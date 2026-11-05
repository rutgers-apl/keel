import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.RuleLib
import Vbcf.Proof.Intern
import Vbcf.Proof.Core1
import Bcf.Soundness

/-!
# Vbcf proofs: the Eval family, part 1 — infrastructure and the arithmetic helpers

* The invariants carried across `CMem.wev` (the C state with only `work`, `err` and
  `val` changed, all that `cval` changes; defined in `Mem.lean`).
* `WP.ck_setVal`: the store `st->val = e;` (the only `u64` field).
* `memoVal` unfolded one level (`cv_memoVal_args`), and the typing of its values.
* `CvRep`: how `cval`'s result word and `st->val` represent a Lean value.
* Specifications of `mask64`, `udiv_w`, `umod_w`, `sdiv_w`, `smod_w` as pure functions
  on 64-bit words (`mask64M`, `udivM`, `umodM`, `sdivM`, `smodM`).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## The state `cval` leaves behind -/

section wev
variable (c : CMem)

/-- The store `st->val = x` as a `wev`. -/
theorem setVal_wev (x : BitVec 64) :
    ({ c with k := { c.k with val := x } } : CMem) = c.wev c.k.work c.k.err x := rfl

end wev

/-! ## `st->val = e;` -/

theorem WP.ck_setVal {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {W : World} {sb : Nat}
    {c : CMem} {p e : Expr}
    (hs : P.findStruct "ck" = some ckS) {m : Mem} (h : Holds W m sb c) (hm : st.mem = m)
    (H : match evalE P env st.mem p, evalE P env st.mem e with
      | some (.ptr b off), some (.u64 x) =>
        b = sb ∧ off = 0 ∧
        ∀ st', Holds W st'.mem sb (c.wev c.k.work c.k.err x) → Q .normal env st'
      | _, _ => False) :
    WP P (.setField p "val" e) Q env st := by
  subst hm
  apply WP.setField
  split at H
  · rename_i b off x hp he
    obtain ⟨rfl, rfl, H⟩ := H
    rw [hp, he]; dsimp only
    refine ⟨rfl, ?_⟩
    rw [Mem.storeField_eq (by rw [ck_slot hs h.ck, fi_val]) (by simp) (by simp [CK.cells])]
    exact H _ (h.setCK (k' := { c.k with val := x }) (by simp [CK.cells]) rfl)
  · exact H.elim

/-! ## `memoVal` one level down -/

theorem cv_memoVal_args {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {n : Node}
    (hn : st.pool[i]? = some n)
    (h1 : ∀ w id, n.op ≠ .bvVar w id) (h2 : ∀ id, n.op ≠ .boolVar id) (h3 : ∀ w, n.op ≠ .bvSize w) :
    memoVal st i = (mapOpt (memoVal st) n.args.toList).map (Op.eval (fun _ => 0) n.op) := by
  have hlt := (hok.2 i n hn).1
  have hm : mapOpt (fun a => if a < i then ((memoBuild st i)[a]?).bind id else none) n.args.toList =
      mapOpt (memoVal st) n.args.toList := by
    apply mapOpt_congr
    intro a ha
    have ha' : a < i := hlt a (by simpa using ha)
    simp [ha', memoBuild_get st i a ha']
  rw [← hm]
  obtain ⟨op, args⟩ := n
  simp only at h1 h2 h3 ⊢
  unfold memoVal memoStep
  rw [hn]
  cases op <;> first
    | exact absurd rfl (h1 _ _) | exact absurd rfl (h2 _) | exact absurd rfl (h3 _)
    | (simp only; cases mapOpt (fun a => if a < i then ((memoBuild st i)[a]?).bind id else none)
        args.toList <;> rfl)

theorem cv_memoVal_bvSize {st : St} {i : Nat} {w a : Nat}
    (hn : st.pool[i]? = some ⟨.bvSize w, #[a]⟩) {k : Nat} (ht : st.tys[a]? = some (.bv k)) :
    memoVal st i = some (Op.eval (fun _ => 0) (.bvSize w) [.bv k 0]) := by
  unfold memoVal memoStep
  rw [hn]
  simp [ht]

/-- Constant values have the type the memo records. -/
theorem cv_memoVal_ty {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {v : Bcf.Val}
    (h : memoVal st i = some v) : v.ty = st.tys[i]? := by
  obtain ⟨n, hn⟩ := node_of_lt (memoVal_lt h)
  rw [← memoVal_eval hok (fun _ => 0) i v h, eval_ty, (hok.2 i n hn).2]

/-! ## Results of `cval` -/

/-- `cval` returned `r` with `st->val = vl` for the Lean value `v`: a boolean is
`CV_BOOL` with 0 or 1, a bit-vector of width `w ≤ 64` is `w` with its value. -/
def CvRep (r : BitVec 32) (vl : BitVec 64) : Bcf.Val → Prop
  | .bool b => r = 100#32 ∧ vl = (if b then 1#64 else 0#64)
  | .bv w x => r.toNat = w ∧ 1 ≤ w ∧ w ≤ 64 ∧ vl.toNat = x.toNat
  | _ => False

/-! ## `mask64` -/

def mask64M (w : BitVec 32) : BitVec 64 :=
  if 64#32 ≤ w then 0xffffffffffffffff#64 else (1#64 <<< w.toNat) - 1#64

theorem mask64_spec (w : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "mask64" (fun vs _ => vs = [.u32 w])
      (fun _ s rv s' => s' = s ∧ rv = some (.u64 (mask64M w))) := by
  apply FnSpec.intro' (fn := mask64) rfl
  rintro vs st rfl
  simp [mask64, bindParams]
  simp only [Stmt.block, initLocals, List.map]
  apply WP.ifRet
  embc_simp
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · simp [retPost, mask64M, hw]
  · apply WP.ret
    have hlt : w.toNat < 64 := by rw [BitVec.lt_def] at hw; simpa using hw
    have hm : w.toNat % 18446744073709551616 = w.toNat := Nat.mod_eq_of_lt (by omega)
    have hw' : ¬ 64#32 ≤ w := by rw [BitVec.le_def]; simp; omega
    embc_simp [retPost, mask64M, hlt, hm, hw']

/-! ## Division helpers -/

def udivM (x y m : BitVec 64) : BitVec 64 := if y = 0#64 then m else x / y
def umodM (x y : BitVec 64) : BitVec 64 := if y = 0#64 then x else x % y

theorem udiv_w_spec (x y m : BitVec 64) :
    FnSpec (State := State) Vbcf.prog "udiv_w" (fun vs _ => vs = [.u64 x, .u64 y, .u64 m])
      (fun _ s rv s' => s' = s ∧ rv = some (.u64 (udivM x y m))) := by
  apply FnSpec.intro' (fn := udivW) rfl
  rintro vs st rfl
  simp [udivW, bindParams]
  simp only [Stmt.block, initLocals, List.map]
  apply WP.ifRet
  embc_simp
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · simp [retPost, udivM, hy]
  · apply WP.ret
    embc_simp [retPost, udivM, hy]

theorem umod_w_spec (x y : BitVec 64) :
    FnSpec (State := State) Vbcf.prog "umod_w" (fun vs _ => vs = [.u64 x, .u64 y])
      (fun _ s rv s' => s' = s ∧ rv = some (.u64 (umodM x y))) := by
  apply FnSpec.intro' (fn := umodW) rfl
  rintro vs st rfl
  simp [umodW, bindParams]
  simp only [Stmt.block, initLocals, List.map]
  apply WP.ifRet
  embc_simp
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · simp [retPost, umodM, hy]
  · apply WP.ret
    embc_simp [retPost, umodM, hy]

/-- `sdiv_w` on words; `k` is the sign-bit position `w - 1`. -/
def sdivM (x y m : BitVec 64) (k : Nat) : BitVec 64 :=
  if x >>> k &&& 1#64 = 0#64 ∧ y >>> k &&& 1#64 = 0#64 then udivM x y m
  else if x >>> k &&& 1#64 = 0#64 then (0#64 - udivM x ((0#64 - y) &&& m) m) &&& m
  else if y >>> k &&& 1#64 = 0#64 then (0#64 - udivM ((0#64 - x) &&& m) y m) &&& m
  else udivM ((0#64 - x) &&& m) ((0#64 - y) &&& m) m

/-- `smod_w` on words. -/
def smodM (x y m : BitVec 64) (k : Nat) : BitVec 64 :=
  if x >>> k &&& 1#64 = 0#64 ∧ y >>> k &&& 1#64 = 0#64 then umodM x y
  else if x >>> k &&& 1#64 = 0#64 then
    (if umodM x ((0#64 - y) &&& m) = 0#64 then 0#64 else (umodM x ((0#64 - y) &&& m) + y) &&& m)
  else if y >>> k &&& 1#64 = 0#64 then
    (if umodM ((0#64 - x) &&& m) y = 0#64 then 0#64 else (y - umodM ((0#64 - x) &&& m) y) &&& m)
  else (0#64 - umodM ((0#64 - x) &&& m) ((0#64 - y) &&& m)) &&& m

theorem cv_sign_pos_eq {w : BitVec 32} (hw1 : 1 ≤ w.toNat) :
    (4294967295 + w.toNat) % 4294967296 % 18446744073709551616 = w.toNat - 1 := by
  have := w.isLt; omega

theorem cv_sign_pos_eq2 {w : BitVec 32} (hw1 : 1 ≤ w.toNat) :
    (4294967295 + w.toNat) % 4294967296 = w.toNat - 1 := by
  have := w.isLt; omega

theorem sdiv_w_spec (x y m : BitVec 64) (w : BitVec 32) (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat ≤ 64) :
    FnSpec (State := State) Vbcf.prog "sdiv_w" (fun vs _ => vs = [.u64 x, .u64 y, .u32 w, .u64 m])
      (fun _ s rv s' => s' = s ∧ rv = some (.u64 (sdivM x y m (w.toNat - 1)))) := by
  have hk := cv_sign_pos_eq hw1
  have hk' := cv_sign_pos_eq2 hw1
  have hlt : w.toNat - 1 < 64 := by omega
  have hk2 : (w.toNat - 1) % 18446744073709551616 = w.toNat - 1 := Nat.mod_eq_of_lt (by omega)
  apply FnSpec.intro' (fn := sdivW) rfl
  rintro vs st rfl
  simp [sdivW, bindParams]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq; apply WP.assign; embc_simp [hk, hk', hk2, hlt]
  apply WP.seq; apply WP.assign; embc_simp [hk, hk', hk2, hlt]
  by_cases h1 : x >>> (w.toNat - 1) &&& 1#64 = 0#64 <;>
  by_cases h2 : y >>> (w.toNat - 1) &&& 1#64 = 0#64
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (udiv_w_spec x y m); embc_simp
    apply WP.ret; embc_simp [LoopQ, retPost, sdivM, h1, h2]
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (udiv_w_spec x ((0#64 - y) &&& m) m); embc_simp
    apply WP.ret; embc_simp [LoopQ, retPost, sdivM, h1, h2]
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (udiv_w_spec ((0#64 - x) &&& m) y m); embc_simp
    apply WP.ret; embc_simp [LoopQ, retPost, sdivM, h1, h2]
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (udiv_w_spec ((0#64 - x) &&& m) ((0#64 - y) &&& m) m); embc_simp
    apply WP.ret; embc_simp [retPost, sdivM, h1, h2]

theorem smod_w_spec (x y m : BitVec 64) (w : BitVec 32) (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat ≤ 64) :
    FnSpec (State := State) Vbcf.prog "smod_w" (fun vs _ => vs = [.u64 x, .u64 y, .u32 w, .u64 m])
      (fun _ s rv s' => s' = s ∧ rv = some (.u64 (smodM x y m (w.toNat - 1)))) := by
  have hk := cv_sign_pos_eq hw1
  have hk' := cv_sign_pos_eq2 hw1
  have hlt : w.toNat - 1 < 64 := by omega
  have hk2 : (w.toNat - 1) % 18446744073709551616 = w.toNat - 1 := Nat.mod_eq_of_lt (by omega)
  apply FnSpec.intro' (fn := smodW) rfl
  rintro vs st rfl
  simp [smodW, bindParams]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq; apply WP.assign; embc_simp [hk, hk', hk2, hlt]
  apply WP.seq; apply WP.assign; embc_simp [hk, hk', hk2, hlt]
  by_cases h1 : x >>> (w.toNat - 1) &&& 1#64 = 0#64 <;>
  by_cases h2 : y >>> (w.toNat - 1) &&& 1#64 = 0#64
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (umod_w_spec x y); embc_simp
    apply WP.ret; embc_simp [LoopQ, retPost, smodM, h1, h2]
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (umod_w_spec x ((0#64 - y) &&& m)); embc_simp
    apply WP.ite_seq; embc_simp
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · apply WP.ret; embc_simp [LoopQ, retPost, smodM, h1, h2, hu]
    · apply WP.ret; embc_simp [LoopQ, retPost, smodM, h1, h2, hu]
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (umod_w_spec ((0#64 - x) &&& m) y); embc_simp
    apply WP.ite_seq; embc_simp
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · apply WP.ret; embc_simp [LoopQ, retPost, smodM, h1, h2, hu]
    · apply WP.ret; embc_simp [LoopQ, retPost, smodM, h1, h2, hu]
  · apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.ite_seq; embc_simp [h1, h2]
    apply WP.seq; apply WP.call (umod_w_spec ((0#64 - x) &&& m) ((0#64 - y) &&& m)); embc_simp
    apply WP.ret; embc_simp [retPost, smodM, h1, h2]

end Vbcf.Proof

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## The specification of `cval` -/

/-- What `cval(st, id, depth)` guarantees when it returns `r` for node `i`: the state
differs only in `work`, `err`, `val`, and a result other than 0 and `NOID` is the
represented constant value of `i`. -/
def CvalPost (W : World) (sb : Nat) (c : CMem) (st : VSt) (i : Nat) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ r wk er vl, rv = some (.u32 r) ∧ Holds W s'.mem sb (c.wev wk er vl) ∧
    (r ≠ 0#32 → r ≠ 4294967295#32 → ∃ v, memoVal st i = some v ∧ CvRep r vl v)

def CvalSpecD (d : BitVec 32) : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : VSt) (i : Nat),
    FnSpec (State := State) Vbcf.prog "cval"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i), .u32 d] ∧ Holds W s.mem sb c ∧
        VInv posOf c st ∧ st.lv i)
      (fun _ _ => CvalPost W sb c st i)

def CvalSpec : Prop := ∀ d, CvalSpecD (State := State) d

/-! ## Pieces of the body of `cval` (verbatim from `Vbcf/Rules/Eval.lean`) -/

def cvU : Stmt := [cstms|
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    if (code == BV_NEG) { x = (0ull - x) & m; }
    else if (code == BV_NOT) { x = (~x) & m; }
    else if (code == BV_EXTRACT) { x = (x >> (u64)lo) & m; }
    else if (code == BV_SEXT) {
      if (((x >> (u64)(cw - 1)) & 1ull) != 0ull) {
        y = mask64(cw);
        x = x | (m & ~y);
      }
    }
    else if (code == BV_REPEAT) {
      if (cw < 64) {
        y = 0ull;
        while (i < hi) {
          y = (y << (u64)cw) | x;
          i = i + 1;
        }
        x = y;
      }
    }
    else if (code == BOOL_NOT) { x = 1ull - x; }
    else if (code == BOOL_BITOF) { x = (x >> (u64)lo) & 1ull; }
    st->val = x;
    return w;
]

def cvB : Stmt := [cstms|
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    if (code == BV_SUB) { z = (x - y) & m; }
    else if (code == BV_SHL) {
      z = 0ull;
      if (y < (u64)w) { z = (x << y) & m; }
    }
    else if (code == BV_LSHR) {
      z = 0ull;
      if (y < (u64)w) { z = x >> y; }
    }
    else if (code == BV_ASHR) {
      sb = (x >> (u64)(w - 1)) & 1ull;
      if (y >= (u64)w) {
        z = 0ull;
        if (sb != 0ull) { z = m; }
      } else {
        z = x >> y;
        if (sb != 0ull) { z = z | (m & ~(m >> y)); }
      }
    }
    else if (code == BV_UDIV) { z = udiv_w(x, y, m); }
    else if (code == BV_UREM) { z = umod_w(x, y); }
    else if (code == BV_SDIV) { z = sdiv_w(x, y, w, m); }
    else if (code == BV_SMOD) { z = smod_w(x, y, w, m); }
    else if (code == BOOL_EQ) { z = (u64)(x == y); }
    else if (code == BOOL_DISTINCT) { z = (u64)(x != y); }
    else if (code == BOOL_IMPLIES) { z = (1ull - x) | y; }
    else if (code == BOOL_ULT) { z = (u64)(x < y); }
    else if (code == BOOL_ULE) { z = (u64)(x <= y); }
    else if (code == BOOL_UGT) { z = (u64)(y < x); }
    else if (code == BOOL_UGE) { z = (u64)(y <= x); }
    else {
      sb = 1ull << (u64)(cw - 1);
      x = x ^ sb;
      y = y ^ sb;
      if (code == BOOL_SLT) { z = (u64)(x < y); }
      else if (code == BOOL_SLE) { z = (u64)(x <= y); }
      else if (code == BOOL_SGT) { z = (u64)(y < x); }
      else { z = (u64)(y <= x); }
    }
    st->val = z;
    return w;
]

def cvI : Stmt := [cstms|
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    cw = cval(st, st->pool[id + 3], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    z = st->val;
    if (x != 0ull) { z = y; }
    st->val = z;
    return w;
]

def cvN : Stmt := [cstms|
    acc = 0ull;
    if (code == BV_MUL || code == BOOL_CONJ) { acc = 1ull; }
    if (code == BV_AND) { acc = m; }
    while (i < n) {
      cw = cval(st, st->pool[id + 1 + i], depth - 1);
      if (cw == 0 || cw == NOID) { return cw; }
      x = st->val;
      if (code == BV_ADD) { acc = (acc + x) & m; }
      else if (code == BV_MUL) { acc = (acc * x) & m; }
      else if (code == BV_OR || code == BOOL_DISJ) { acc = acc | x; }
      else if (code == BV_AND || code == BOOL_CONJ) { acc = acc & x; }
      else if (code == BV_XOR || code == BOOL_XOR) { acc = acc ^ x; }
      else if (code == BV_CONCAT) { acc = (acc << (u64)cw) | x; }
      else { acc = acc | (x << (u64)i); }
      i = i + 1;
    }
    st->val = acc;
    return w;
]

/-- `cvU` after the child's value has been read. -/
def cvUt : Stmt := [cstms|
    if (code == BV_NEG) { x = (0ull - x) & m; }
    else if (code == BV_NOT) { x = (~x) & m; }
    else if (code == BV_EXTRACT) { x = (x >> (u64)lo) & m; }
    else if (code == BV_SEXT) {
      if (((x >> (u64)(cw - 1)) & 1ull) != 0ull) {
        y = mask64(cw);
        x = x | (m & ~y);
      }
    }
    else if (code == BV_REPEAT) {
      if (cw < 64) {
        y = 0ull;
        while (i < hi) {
          y = (y << (u64)cw) | x;
          i = i + 1;
        }
        x = y;
      }
    }
    else if (code == BOOL_NOT) { x = 1ull - x; }
    else if (code == BOOL_BITOF) { x = (x >> (u64)lo) & 1ull; }
    st->val = x;
    return w;
]

/-- `cvB` after both children's values have been read. -/
def cvBt : Stmt := [cstms|
    if (code == BV_SUB) { z = (x - y) & m; }
    else if (code == BV_SHL) {
      z = 0ull;
      if (y < (u64)w) { z = (x << y) & m; }
    }
    else if (code == BV_LSHR) {
      z = 0ull;
      if (y < (u64)w) { z = x >> y; }
    }
    else if (code == BV_ASHR) {
      sb = (x >> (u64)(w - 1)) & 1ull;
      if (y >= (u64)w) {
        z = 0ull;
        if (sb != 0ull) { z = m; }
      } else {
        z = x >> y;
        if (sb != 0ull) { z = z | (m & ~(m >> y)); }
      }
    }
    else if (code == BV_UDIV) { z = udiv_w(x, y, m); }
    else if (code == BV_UREM) { z = umod_w(x, y); }
    else if (code == BV_SDIV) { z = sdiv_w(x, y, w, m); }
    else if (code == BV_SMOD) { z = smod_w(x, y, w, m); }
    else if (code == BOOL_EQ) { z = (u64)(x == y); }
    else if (code == BOOL_DISTINCT) { z = (u64)(x != y); }
    else if (code == BOOL_IMPLIES) { z = (1ull - x) | y; }
    else if (code == BOOL_ULT) { z = (u64)(x < y); }
    else if (code == BOOL_ULE) { z = (u64)(x <= y); }
    else if (code == BOOL_UGT) { z = (u64)(y < x); }
    else if (code == BOOL_UGE) { z = (u64)(y <= x); }
    else {
      sb = 1ull << (u64)(cw - 1);
      x = x ^ sb;
      y = y ^ sb;
      if (code == BOOL_SLT) { z = (u64)(x < y); }
      else if (code == BOOL_SLE) { z = (u64)(x <= y); }
      else if (code == BOOL_SGT) { z = (u64)(y < x); }
      else { z = (u64)(y <= x); }
    }
    st->val = z;
    return w;
]

/-- From the `BV_SIZE` test to the end. -/
def cvT2 : Stmt := [cstms|
  if (code == BV_SIZE) {
    cw = ty_of(st->pool[st->pool[id + 1]]);
    st->val = (u64)cw;
    return w;
  }
  if (code == BV_NEG || code == BV_NOT || code == BV_EXTRACT || code == BV_SEXT
      || code == BV_ZEXT || code == BV_REPEAT || code == BOOL_NOT || code == BOOL_BITOF) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    if (code == BV_NEG) { x = (0ull - x) & m; }
    else if (code == BV_NOT) { x = (~x) & m; }
    else if (code == BV_EXTRACT) { x = (x >> (u64)lo) & m; }
    else if (code == BV_SEXT) {
      if (((x >> (u64)(cw - 1)) & 1ull) != 0ull) {
        y = mask64(cw);
        x = x | (m & ~y);
      }
    }
    else if (code == BV_REPEAT) {
      if (cw < 64) {
        y = 0ull;
        while (i < hi) {
          y = (y << (u64)cw) | x;
          i = i + 1;
        }
        x = y;
      }
    }
    else if (code == BOOL_NOT) { x = 1ull - x; }
    else if (code == BOOL_BITOF) { x = (x >> (u64)lo) & 1ull; }
    st->val = x;
    return w;
  }
  if (code == BV_SUB || code == BV_SHL || code == BV_LSHR || code == BV_ASHR || code == BV_UDIV
      || code == BV_UREM || code == BV_SDIV || code == BV_SMOD || code == BOOL_EQ
      || code == BOOL_DISTINCT || code == BOOL_UGT || code == BOOL_UGE || code == BOOL_SGT
      || code == BOOL_SGE || code == BOOL_ULT || code == BOOL_ULE || code == BOOL_SLT
      || code == BOOL_SLE || code == BOOL_IMPLIES) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    if (code == BV_SUB) { z = (x - y) & m; }
    else if (code == BV_SHL) {
      z = 0ull;
      if (y < (u64)w) { z = (x << y) & m; }
    }
    else if (code == BV_LSHR) {
      z = 0ull;
      if (y < (u64)w) { z = x >> y; }
    }
    else if (code == BV_ASHR) {
      sb = (x >> (u64)(w - 1)) & 1ull;
      if (y >= (u64)w) {
        z = 0ull;
        if (sb != 0ull) { z = m; }
      } else {
        z = x >> y;
        if (sb != 0ull) { z = z | (m & ~(m >> y)); }
      }
    }
    else if (code == BV_UDIV) { z = udiv_w(x, y, m); }
    else if (code == BV_UREM) { z = umod_w(x, y); }
    else if (code == BV_SDIV) { z = sdiv_w(x, y, w, m); }
    else if (code == BV_SMOD) { z = smod_w(x, y, w, m); }
    else if (code == BOOL_EQ) { z = (u64)(x == y); }
    else if (code == BOOL_DISTINCT) { z = (u64)(x != y); }
    else if (code == BOOL_IMPLIES) { z = (1ull - x) | y; }
    else if (code == BOOL_ULT) { z = (u64)(x < y); }
    else if (code == BOOL_ULE) { z = (u64)(x <= y); }
    else if (code == BOOL_UGT) { z = (u64)(y < x); }
    else if (code == BOOL_UGE) { z = (u64)(y <= x); }
    else {
      sb = 1ull << (u64)(cw - 1);
      x = x ^ sb;
      y = y ^ sb;
      if (code == BOOL_SLT) { z = (u64)(x < y); }
      else if (code == BOOL_SLE) { z = (u64)(x <= y); }
      else if (code == BOOL_SGT) { z = (u64)(y < x); }
      else { z = (u64)(y <= x); }
    }
    st->val = z;
    return w;
  }
  if (code == BV_ITE || code == BOOL_ITE) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    cw = cval(st, st->pool[id + 3], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    z = st->val;
    if (x != 0ull) { z = y; }
    st->val = z;
    return w;
  }
  if (code == BV_ADD || code == BV_MUL || code == BV_OR || code == BV_AND || code == BV_XOR
      || code == BV_CONCAT || code == BV_FROM_BOOL || code == BOOL_CONJ || code == BOOL_DISJ
      || code == BOOL_XOR) {
    acc = 0ull;
    if (code == BV_MUL || code == BOOL_CONJ) { acc = 1ull; }
    if (code == BV_AND) { acc = m; }
    while (i < n) {
      cw = cval(st, st->pool[id + 1 + i], depth - 1);
      if (cw == 0 || cw == NOID) { return cw; }
      x = st->val;
      if (code == BV_ADD) { acc = (acc + x) & m; }
      else if (code == BV_MUL) { acc = (acc * x) & m; }
      else if (code == BV_OR || code == BOOL_DISJ) { acc = acc | x; }
      else if (code == BV_AND || code == BOOL_CONJ) { acc = acc & x; }
      else if (code == BV_XOR || code == BOOL_XOR) { acc = acc ^ x; }
      else if (code == BV_CONCAT) { acc = (acc << (u64)cw) | x; }
      else { acc = acc | (x << (u64)i); }
      i = i + 1;
    }
    st->val = acc;
    return w;
  }
  return NOID;
]

/-- From `m = 1ull;` to the end. -/
def cvT : Stmt := [cstms|
  m = 1ull;
  if (w <= 64) { m = mask64(w); }
  if (code == BV_SIZE) {
    cw = ty_of(st->pool[st->pool[id + 1]]);
    st->val = (u64)cw;
    return w;
  }
  if (code == BV_NEG || code == BV_NOT || code == BV_EXTRACT || code == BV_SEXT
      || code == BV_ZEXT || code == BV_REPEAT || code == BOOL_NOT || code == BOOL_BITOF) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    if (code == BV_NEG) { x = (0ull - x) & m; }
    else if (code == BV_NOT) { x = (~x) & m; }
    else if (code == BV_EXTRACT) { x = (x >> (u64)lo) & m; }
    else if (code == BV_SEXT) {
      if (((x >> (u64)(cw - 1)) & 1ull) != 0ull) {
        y = mask64(cw);
        x = x | (m & ~y);
      }
    }
    else if (code == BV_REPEAT) {
      if (cw < 64) {
        y = 0ull;
        while (i < hi) {
          y = (y << (u64)cw) | x;
          i = i + 1;
        }
        x = y;
      }
    }
    else if (code == BOOL_NOT) { x = 1ull - x; }
    else if (code == BOOL_BITOF) { x = (x >> (u64)lo) & 1ull; }
    st->val = x;
    return w;
  }
  if (code == BV_SUB || code == BV_SHL || code == BV_LSHR || code == BV_ASHR || code == BV_UDIV
      || code == BV_UREM || code == BV_SDIV || code == BV_SMOD || code == BOOL_EQ
      || code == BOOL_DISTINCT || code == BOOL_UGT || code == BOOL_UGE || code == BOOL_SGT
      || code == BOOL_SGE || code == BOOL_ULT || code == BOOL_ULE || code == BOOL_SLT
      || code == BOOL_SLE || code == BOOL_IMPLIES) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    if (code == BV_SUB) { z = (x - y) & m; }
    else if (code == BV_SHL) {
      z = 0ull;
      if (y < (u64)w) { z = (x << y) & m; }
    }
    else if (code == BV_LSHR) {
      z = 0ull;
      if (y < (u64)w) { z = x >> y; }
    }
    else if (code == BV_ASHR) {
      sb = (x >> (u64)(w - 1)) & 1ull;
      if (y >= (u64)w) {
        z = 0ull;
        if (sb != 0ull) { z = m; }
      } else {
        z = x >> y;
        if (sb != 0ull) { z = z | (m & ~(m >> y)); }
      }
    }
    else if (code == BV_UDIV) { z = udiv_w(x, y, m); }
    else if (code == BV_UREM) { z = umod_w(x, y); }
    else if (code == BV_SDIV) { z = sdiv_w(x, y, w, m); }
    else if (code == BV_SMOD) { z = smod_w(x, y, w, m); }
    else if (code == BOOL_EQ) { z = (u64)(x == y); }
    else if (code == BOOL_DISTINCT) { z = (u64)(x != y); }
    else if (code == BOOL_IMPLIES) { z = (1ull - x) | y; }
    else if (code == BOOL_ULT) { z = (u64)(x < y); }
    else if (code == BOOL_ULE) { z = (u64)(x <= y); }
    else if (code == BOOL_UGT) { z = (u64)(y < x); }
    else if (code == BOOL_UGE) { z = (u64)(y <= x); }
    else {
      sb = 1ull << (u64)(cw - 1);
      x = x ^ sb;
      y = y ^ sb;
      if (code == BOOL_SLT) { z = (u64)(x < y); }
      else if (code == BOOL_SLE) { z = (u64)(x <= y); }
      else if (code == BOOL_SGT) { z = (u64)(y < x); }
      else { z = (u64)(y <= x); }
    }
    st->val = z;
    return w;
  }
  if (code == BV_ITE || code == BOOL_ITE) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    cw = cval(st, st->pool[id + 3], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    z = st->val;
    if (x != 0ull) { z = y; }
    st->val = z;
    return w;
  }
  if (code == BV_ADD || code == BV_MUL || code == BV_OR || code == BV_AND || code == BV_XOR
      || code == BV_CONCAT || code == BV_FROM_BOOL || code == BOOL_CONJ || code == BOOL_DISJ
      || code == BOOL_XOR) {
    acc = 0ull;
    if (code == BV_MUL || code == BOOL_CONJ) { acc = 1ull; }
    if (code == BV_AND) { acc = m; }
    while (i < n) {
      cw = cval(st, st->pool[id + 1 + i], depth - 1);
      if (cw == 0 || cw == NOID) { return cw; }
      x = st->val;
      if (code == BV_ADD) { acc = (acc + x) & m; }
      else if (code == BV_MUL) { acc = (acc * x) & m; }
      else if (code == BV_OR || code == BOOL_DISJ) { acc = acc | x; }
      else if (code == BV_AND || code == BOOL_CONJ) { acc = acc & x; }
      else if (code == BV_XOR || code == BOOL_XOR) { acc = acc ^ x; }
      else if (code == BV_CONCAT) { acc = (acc << (u64)cw) | x; }
      else { acc = acc | (x << (u64)i); }
      i = i + 1;
    }
    st->val = acc;
    return w;
  }
  return NOID;
]

/-! ## The environment of `cval`'s body -/

/-- The locals of `cval`, in declaration order. -/
def cvEnv (sb : Nat) (id d hdr code n par lo hi w cw i : BitVec 32) (x y z m sbv acc : BitVec 64) :
    Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, .u32 id), ("depth", .u32, .u32 d),
   ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 code), ("n", .u32, .u32 n),
   ("par", .u32, .u32 par), ("lo", .u32, .u32 lo), ("hi", .u32, .u32 hi), ("w", .u32, .u32 w),
   ("cw", .u32, .u32 cw), ("i", .u32, .u32 i), ("x", .u64, .u64 x), ("y", .u64, .u64 y),
   ("z", .u64, .u64 z), ("m", .u64, .u64 m), ("sb", .u64, .u64 sbv), ("acc", .u64, .u64 acc)]

/-- The C type word `w` after `if (w == TY_BOOL) { w = CV_BOOL; }`, for a scalar type of
width at most 64. -/
def CvW (t : Bcf.Ty) (w : BitVec 32) : Prop :=
  (t = .bool ∧ w = 100#32) ∨ (∃ k, t = .bv k ∧ 1 ≤ k ∧ k ≤ 64 ∧ w = BitVec.ofNat 32 k)

/-- The mask `m` after `m = 1ull; if (w <= 64) { m = mask64(w); }`. -/
def mW (w : BitVec 32) : BitVec 64 := if w ≤ 64#32 then mask64M w else 1#64

/-- A postcondition `Q` accepts every `return r;` that `cval` may do for node `i`. -/
def CvQ (W : World) (sb : Nat) (c : CMem) (st : VSt) (i : Nat) (Q : (Post prog State)) : Prop :=
  ∀ (r wk er : BitVec 32) (vl : BitVec 64) (env : Env) (s' : (KernelState prog State)),
    Holds W s'.mem sb (c.wev wk er vl) →
    (r ≠ 0#32 → r ≠ 4294967295#32 → ∃ v, memoVal st i = some v ∧ CvRep r vl v) →
    Q (.ret (some (.u32 r))) env s'

theorem CvQ.loopQ {W : World} {sb : Nat} {c : CMem} {st : VSt} {i : Nat} {Q : (Post prog State)}
    {I : Env → (KernelState prog State) → Prop} (hQ : CvQ W sb c st i Q) : CvQ W sb c st i (LoopQ I Q) :=
  fun r wk er vl env s' h hv => hQ r wk er vl env s' h hv

/-- The body's postcondition is such a `Q`. -/
theorem CvQ.retPost {W : World} {sb : Nat} {c : CMem} {st : VSt} {i : Nat} {vs : List EmbC.Val}
    {s0 : (KernelState prog State)} :
    CvQ (State := State) W sb c st i (retPost (some .u32) (fun rv s' => (fun (_ : List EmbC.Val) (_ : (KernelState prog State)) =>
      CvalPost W sb c st i) vs s0 rv s')) :=
  fun r wk er vl _ _s' h hv => ⟨rfl, r, wk, er, vl, rfl, h, hv⟩

/-- `cw = cval(st, child, depth - 1); rest` -/
theorem WP.cval_child {d' : BitVec 32} (IH : CvalSpecD (State := State) d') {W : World} {sb : Nat} {c : CMem}
    {posOf : Nat → Nat} {st : VSt} {a : Nat} {env : Env} {s : (KernelState prog State)} {args : List Expr}
    {rest : Stmt} {Q : (Post prog State)}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (ha : st.lv a)
    (hargs : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, uv (st.id a), .u32 d'])
    (H : ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) →
      (r ≠ 0#32 → r ≠ 4294967295#32 → ∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      match env.assign s'.mem "cw" (.u32 r) with
      | none => False
      | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some "cw") "cval" args) rest) Q env s := by
  apply WP.call_seq (IH W sb c posOf st a) hargs ⟨rfl, h, hc, ha⟩
  rintro rv s' ⟨r, wk, er, vl, rfl, h', hv⟩
  exact H r wk er vl s' h' hv

/-- `if (cw == 0 || cw == NOID) { return cw; } rest` -/
theorem WP.cw_guard {W : World} {sb : Nat} {c : CMem} {st : VSt} {i : Nat} {Q : (Post prog State)}
    {env : Env} {s : (KernelState prog State)} {rest : Stmt} {r wk er : BitVec 32} {vl : BitVec 64}
    (hQ : CvQ W sb c st i Q) (h : Holds W s.mem sb (c.wev wk er vl))
    (henv : env.get "cw" = some (.u32 r))
    (H : r ≠ 0#32 → r ≠ 4294967295#32 → WP Vbcf.prog rest Q env s) :
    WP Vbcf.prog (.seq (.ite (.lor (.bin .eq (.var "cw") (.lit32 0#32))
        (.bin .eq (.var "cw") NOID)) (.ret (some (.var "cw"))) .skip) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  by_cases h0 : r = 0#32
  · subst h0
    simp only [evalE, henv, evalBin, evalArith]
    simp only [Val.ofBool, decide_true, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h1 => by simp at h1⟩
    apply WP.ret
    simp only [evalE, henv]
    exact hQ _ _ _ _ _ _ h (fun h => absurd rfl h)
  by_cases h1 : r = 4294967295#32
  · subst h1
    simp only [evalE, henv, evalBin, evalArith, Val.ofBool]
    simp
    apply WP.ret
    simp only [evalE, henv]
    exact hQ _ _ _ _ _ _ h (fun _ h => absurd rfl h)
  · simp only [evalE, henv, evalBin, evalArith, Val.ofBool]
    simp [h0, h1]
    apply WP.skip
    exact H h0 h1

end Vbcf.Proof
