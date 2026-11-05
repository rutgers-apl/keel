import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly4

/-!
# Vbcf proofs: the Poly family, part 5 — `lin_f`

`lin_f(st, w, id, depth)` pushes `plEnc (lin pool w i)` (`LinFSpecD`), by strong induction
on the depth argument as for `cval` (`Eval9`).  The body is cut into pieces after the
prologue: `plT0` (from the literal test on), …, `plT5` (the final `lin_atom`).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


def LinFSpecD (d : BitVec 32) : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (w i : Nat),
    FnSpec (State := State) Vbcf.prog "lin_f"
      (fun vs s => vs = [.ptr sb 0, uv w, uv (offs st.cs.pool i), .u32 d] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ i < st.cs.pool.size ∧ 1 ≤ w ∧ w ≤ 64)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        PlRet W sb X c0 prems params st c c.k.sp.toNat (plEnc st.cs.pool (Bcf.lin st.cs.pool w i)) r s')

def LinFSpec : Prop := ∀ d, LinFSpecD (State := State) d

/-- The environment of `lin_f`'s body. -/
def plFEnv (sb w id : Nat) (d hdr code n wn a b base mid i ok : BitVec 32) (m k : BitVec 64) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("w", .u32, uv w), ("id", .u32, uv id),
   ("depth", .u32, .u32 d), ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 code), ("n", .u32, .u32 n),
   ("wn", .u32, .u32 wn), ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("base", .u32, .u32 base),
   ("mid", .u32, .u32 mid), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok), ("m", .u64, .u64 m),
   ("k", .u64, .u64 k)]

theorem PlRet.stk_eq {W : World} {sb : Nat} {X : Ctx} {c0 c c1 : CMem} {prems params : List Nat}
    {st : VSt} (h : c1.stk = c.stk) :
    PlRet (State := State) W sb X c0 prems params st c =
      PlRet (State := State) W sb X c0 prems params st c1 := by
  funext base ws r s
  simp [PlRet, h]

/-! ## The pieces of the body -/

def plT5 : Stmt := [cstms|
  ok = lin_atom(st, id, m);
  return ok;
]

def plFMul : Stmt := [cstms|
    a = st->pool[id + 1];
    b = st->pool[id + 2];
    if (wn == w && a < id && b < id) {
      ok = poly_lit_val(st, w, a);
      if (ok != 0) {
        k = st->val;
        ok = lin_f(st, w, b, depth - 1);
        if (ok == 0) { return 0; }
        if (st->sp < base || st->sp > MAX_POOL) { return 0; }
        ok = spend(st, st->sp - base);
        if (ok == 0) { return 0; }
        lin_scale(st, base, k, m);
        return 1;
      }
      ok = poly_lit_val(st, w, b);
      if (ok != 0) {
        k = st->val;
        ok = lin_f(st, w, a, depth - 1);
        if (ok == 0) { return 0; }
        if (st->sp < base || st->sp > MAX_POOL) { return 0; }
        ok = spend(st, st->sp - base);
        if (ok == 0) { return 0; }
        lin_scale(st, base, k, m);
        return 1;
      }
    }
]

def plT4 : Stmt := .seq (.ite (.land (.bin .eq (.var "code") (.named "BV_MUL" 0x20#32))
    (.bin .eq (.var "n") (.lit32 2#32))) plFMul .skip) plT5

def plFNeg : Stmt := [cstms|
    a = st->pool[id + 1];
    if (wn == w && a < id) {
      ok = lin_f(st, w, a, depth - 1);
      if (ok == 0) { return 0; }
      if (st->sp < base || st->sp > MAX_POOL) { return 0; }
      ok = spend(st, st->sp - base);
      if (ok == 0) { return 0; }
      lin_scale(st, base, m, m);
      return 1;
    }
]

def plT3 : Stmt := .seq (.ite (.land (.bin .eq (.var "code") (.named "BV_NEG" 0x80#32))
    (.bin .eq (.var "n") (.lit32 1#32))) plFNeg .skip) plT4

def plFSub : Stmt := [cstms|
    a = st->pool[id + 1];
    b = st->pool[id + 2];
    if (wn == w && a < id && b < id) {
      ok = lin_f(st, w, b, depth - 1);
      if (ok == 0) { return 0; }
      if (st->sp < base || st->sp > MAX_POOL) { return 0; }
      ok = spend(st, st->sp - base);
      if (ok == 0) { return 0; }
      lin_scale(st, base, m, m);
      mid = st->sp;
      ok = lin_f(st, w, a, depth - 1);
      if (ok == 0) { return 0; }
      ok = lin_add(st, base, mid, m);
      return ok;
    }
]

def plT2 : Stmt := .seq (.ite (.land (.bin .eq (.var "code") (.named "BV_SUB" 0x10#32))
    (.bin .eq (.var "n") (.lit32 2#32))) plFSub .skip) plT3

def plFAdd : Stmt := [cstms|
    ok = lin_push64(st, 0ull);
    if (ok == 0) { return 0; }
    i = n;
    while (i > 0) {
      i = i - 1;
      a = st->pool[id + 1 + i];
      mid = st->sp;
      if (a < id) {
        ok = lin_f(st, w, a, depth - 1);
      } else {
        ok = lin_atom(st, a, m);
      }
      if (ok == 0) { return 0; }
      ok = lin_add(st, base, mid, m);
      if (ok == 0) { return 0; }
    }
    return 1;
]

def plT1 : Stmt := .seq (.ite (.land (.bin .eq (.var "code") (.named "BV_ADD" 0x00#32))
    (.bin .eq (.var "wn") (.var "w"))) plFAdd .skip) plT2

def plFVal : Stmt := [cstms|
    ok = poly_lit_val(st, w, id);
    if (ok != 0) {
      ok = lin_push64(st, st->val);
      return ok;
    }
]

def plT0 : Stmt := .seq (.ite (.bin .eq (.var "code") (.named "BV_VAL" 0x08#32)) plFVal .skip) plT1

/-! ## The final `lin_atom` and the skipped tests -/

section pieces
variable {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {w i : Nat} {d : BitVec 32} {s : (KernelState prog State)} {Q : (Post prog State)}

theorem lfT5_spec (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (_hi : i < st.cs.pool.size)
    (hw1 : 1 ≤ w) (hw64 : w ≤ 64) (hlin : Bcf.lin st.cs.pool w i = Lin.atom i)
    (hdr code nn wn a b base mid i' ok : BitVec 32) (k : BitVec 64) :
    WP Vbcf.prog plT5 (RetQ (PlRet W sb X c0 prems params st c c.k.sp.toNat
        (plEnc st.cs.pool (Bcf.lin st.cs.pool w i))))
      (plFEnv sb w (offs st.cs.pool i) d hdr code nn wn a b base mid i' ok (mask64M (BitVec.ofNat 32 w)) k)
      s := by
  have hs := prog_ck
  unfold plT5
  apply WP.pl_call (lin_atom_spec W sb X c0 c prems params st w i (mask64M (BitVec.ofNat 32 w)))
    (by rule_simp [plFEnv]) ⟨rfl, h, hR, hw1, mask64M_toNat hw1 hw64⟩
  intro s' r hr
  rule_simp [plFEnv]
  apply WP.rule_ret; rule_simp
  rw [hlin]; exact hr

theorem lfT4_skip {cd tl : Nat} (hcd : cd < 4294967296) (htl : tl < 4294967296)
    (hc : ¬ (cd = 0x20 ∧ tl = 2)) {hdr wn a b base mid i' ok : BitVec 32} {m k : BitVec 64}
    (H : WP Vbcf.prog plT5 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) (BitVec.ofNat 32 tl) wn a b base
      mid i' ok m k) s) :
    WP Vbcf.prog plT4 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) (BitVec.ofNat 32 tl) wn a b base
      mid i' ok m k) s := by
  unfold plT4
  apply WP.ite_seq
  simp only [plFEnv, evalE, Env.get, evalBin, evalArith, Val.ofBool]
  by_cases h1 : cd = 0x20
  · subst h1
    have h2 : tl ≠ 2 := fun e => hc ⟨rfl, e⟩
    simp [uv_inj htl (by omega : 2 < 4294967296), h2]
    exact H
  · simp [uv_inj hcd (by omega : 32 < 4294967296), h1]
    exact H

theorem lfT3_skip {cd tl : Nat} (hcd : cd < 4294967296) (htl : tl < 4294967296)
    (hc : ¬ (cd = 0x80 ∧ tl = 1)) {hdr wn a b base mid i' ok : BitVec 32} {m k : BitVec 64}
    (H : WP Vbcf.prog plT4 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) (BitVec.ofNat 32 tl) wn a b base
      mid i' ok m k) s) :
    WP Vbcf.prog plT3 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) (BitVec.ofNat 32 tl) wn a b base
      mid i' ok m k) s := by
  unfold plT3
  apply WP.ite_seq
  simp only [plFEnv, evalE, Env.get, evalBin, evalArith, Val.ofBool]
  by_cases h1 : cd = 0x80
  · subst h1
    have h2 : tl ≠ 1 := fun e => hc ⟨rfl, e⟩
    simp [uv_inj htl (by omega : 1 < 4294967296), h2]
    exact H
  · simp [uv_inj hcd (by omega : 128 < 4294967296), h1]
    exact H

theorem lfT2_skip {cd tl : Nat} (hcd : cd < 4294967296) (htl : tl < 4294967296)
    (hc : ¬ (cd = 0x10 ∧ tl = 2)) {hdr wn a b base mid i' ok : BitVec 32} {m k : BitVec 64}
    (H : WP Vbcf.prog plT3 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) (BitVec.ofNat 32 tl) wn a b base
      mid i' ok m k) s) :
    WP Vbcf.prog plT2 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) (BitVec.ofNat 32 tl) wn a b base
      mid i' ok m k) s := by
  unfold plT2
  apply WP.ite_seq
  simp only [plFEnv, evalE, Env.get, evalBin, evalArith, Val.ofBool]
  by_cases h1 : cd = 0x10
  · subst h1
    have h2 : tl ≠ 2 := fun e => hc ⟨rfl, e⟩
    simp [uv_inj htl (by omega : 2 < 4294967296), h2]
    exact H
  · simp [uv_inj hcd (by omega : 16 < 4294967296), h1]
    exact H

theorem lfT1_skip {cd wv : Nat} (hcd : cd < 4294967296) (hwv : wv < 4294967296) (hw : w < 4294967296)
    (hc : ¬ (cd = 0 ∧ wv = w)) {hdr nn a b base mid i' ok : BitVec 32} {m k : BitVec 64}
    (H : WP Vbcf.prog plT2 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) nn (BitVec.ofNat 32 wv) a b base
      mid i' ok m k) s) :
    WP Vbcf.prog plT1 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) nn (BitVec.ofNat 32 wv) a b base
      mid i' ok m k) s := by
  unfold plT1
  apply WP.ite_seq
  simp only [plFEnv, evalE, Env.get, evalBin, evalArith, Val.ofBool]
  by_cases h1 : cd = 0
  · subst h1
    have h2 : wv ≠ w := fun e => hc ⟨rfl, e⟩
    simp [uv_inj hwv hw, h2]
    exact H
  · simp [uv_inj hcd (by omega : 0 < 4294967296), h1]
    exact H

theorem lfT0_skip {cd : Nat} (hcd : cd < 4294967296) (hc : cd ≠ 8)
    {hdr nn wn a b base mid i' ok : BitVec 32} {m k : BitVec 64}
    (H : WP Vbcf.prog plT1 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) nn wn a b base
      mid i' ok m k) s) :
    WP Vbcf.prog plT0 Q (plFEnv sb w i d hdr (BitVec.ofNat 32 cd) nn wn a b base
      mid i' ok m k) s := by
  unfold plT0
  apply WP.ite_seq
  simp only [plFEnv, evalE, Env.get, evalBin, evalArith, Val.ofBool]
  simp [uv_inj hcd (by omega : 8 < 4294967296), hc]
  exact H

end pieces

/-! ## Calls of `lin_scale` and `lin_add` -/

section calls
variable {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {es : List Expr} {rest : Stmt}

/-- `lin_scale(st, b0, k, m); rest` -/
theorem WP.pl_scale (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) {w b0 : Nat}
    {p : Lin w} {kk : BitVec w} {k m : BitVec 64} (hw1 : 1 ≤ w) (hw64 : w ≤ 64)
    (hm : m.toNat = 2 ^ w - 1) (hk : k.toNat = kk.toNat) (hst : PlStkW c b0 (plEnc st.cs.pool p))
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv b0, .u64 k, .u64 m] ∧
      ∀ s' c', Holds W s'.mem sb c' → RCtx W X c0 prems params c' st →
        (∀ j, j < b0 → c'.stk[j]? = c.stk[j]?) → PlStkW c' b0 (plEnc st.cs.pool (Lin.scale kk p)) →
        WP Vbcf.prog rest Q env s') :
    WP Vbcf.prog (.seq (.call none "lin_scale" es) rest) Q env s := by
  apply WP.seq
  apply WP.call (lin_scale_spec W sb X c0 c prems params st w b0 p kk k m)
  rw [H.1]
  refine ⟨⟨rfl, h, hR, hw1, hw64, hm, hk, hst⟩, ?_⟩
  rintro rv s' ⟨rfl, c', h', hR', hpre, hst'⟩
  exact H.2 s' c' h' hR' hpre hst'

/-- `x = lin_add(st, b0, b1, m); rest` -/
theorem WP.pl_add (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) {x : Var}
    {w b0 : Nat} {p q : Lin w} {m : BitVec 64} (hw1 : 1 ≤ w) (hw64 : w ≤ 64)
    (hm : m.toNat = 2 ^ w - 1) (hp : LinOK st.cs.pool p.terms) (hq : LinOK st.cs.pool q.terms)
    (hst : PlStkW c b0 (plEnc st.cs.pool q ++ plEnc st.cs.pool p))
    (H : evalArgs Vbcf.prog env s.mem es =
        some [.ptr sb 0, uv b0, uv (b0 + (plEnc st.cs.pool q).length), .u64 m] ∧
      ∀ s' r, PlRet W sb X c0 prems params st c b0 (plEnc st.cs.pool (Lin.add p q)) r s' →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "lin_add" es) rest) Q env s :=
  WP.pl_call (lin_add_spec W sb X c0 c prems params st w b0 _ p q m) H.1
    ⟨rfl, h, hR, hw1, hw64, hm, hp, hq, rfl, hst⟩ H.2

end calls

theorem pl_neg_one {w : Nat} (hw : 1 ≤ w) : (-1 : BitVec w).toNat = 2 ^ w - 1 := by
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have h1 : (1 : BitVec w).toNat = 1 := by
    rw [show (1 : BitVec w) = BitVec.ofNat w 1 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_neg, h1, Nat.mod_eq_of_lt (by omega)]

/-- Chaining two prefix facts. -/
theorem pl_pre_trans {c1 c2 c3 : CMem} {b b' : Nat} (hb : b ≤ b')
    (h1 : ∀ j, j < b' → c3.stk[j]? = c2.stk[j]?) (h2 : ∀ j, j < b → c2.stk[j]? = c1.stk[j]?) :
    ∀ j, j < b → c3.stk[j]? = c1.stk[j]? := fun j hj => (h1 j (by omega)).trans (h2 j hj)

/-! ## The node's form, and the cases -/

/-- The environment after the prologue, for node `n` at index `i`. -/
def plFE (sb w : Nat) (st : VSt) (i : Nat) (n : Node) (d a b base mid i' ok : BitVec 32) (k : BitVec 64) :
    Env :=
  plFEnv sb w (offs st.cs.pool i) d (BitVec.ofNat 32 (hdrW n)) (BitVec.ofNat 32 (opC n.op))
    (BitVec.ofNat 32 (tailLen n)) (BitVec.ofNat 32 (opLo n.op + opHi n.op * 256)) a b base mid i' ok
    (mask64M (BitVec.ofNat 32 w)) k

/-- When none of the five tests of `lin_f` passes, the form is an atom. -/
theorem pl_lin_rest {pool : Pool} {w i : Nat} {n : Node} (hn : pool[i]? = some n)
    (h8 : opC n.op ≠ 0x08) (h0 : ¬ (opC n.op = 0 ∧ opLo n.op + opHi n.op * 256 = w))
    (h10 : ¬ (opC n.op = 0x10 ∧ tailLen n = 2)) (h80 : ¬ (opC n.op = 0x80 ∧ tailLen n = 1))
    (h20 : ¬ (opC n.op = 0x20 ∧ tailLen n = 2)) : Bcf.lin pool w i = Lin.atom i := by
  obtain ⟨op, args⟩ := n
  by_cases c0 : opC op = 0
  · obtain ⟨w', rfl⟩ := opC_bvAdd_iff.mp c0
    rw [pl_lin_add hn, ite_eq_right (fun e => h0 ⟨c0, by simp [opLo, opHi, e]⟩)]
  by_cases c10 : opC op = 0x10
  · obtain ⟨w', rfl⟩ := opC_bvSub_iff.mp c10
    exact pl_lin_sub_other hn (fun e => h10 ⟨c10, by simp [tailLen, e]⟩)
  by_cases c80 : opC op = 0x80
  · obtain ⟨w', rfl⟩ := opC_bvNeg_iff.mp c80
    exact pl_lin_neg_other hn (fun e => h80 ⟨c80, by simp [tailLen, e]⟩)
  by_cases c20 : opC op = 0x20
  · obtain ⟨w', rfl⟩ := opC_bvMul_iff.mp c20
    exact pl_lin_mul_other hn (fun e => h20 ⟨c20, by simp [tailLen, e]⟩)
  exact pl_lin_other hn h8 c0 c10 c80 c20

section cases
variable {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {w i : Nat} {d : BitVec 32} {s : (KernelState prog State)}

/-- From `plT1` on, for a node none of whose tests passes. -/
theorem lfT1_atom {n : Node} (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    (hi : i < st.cs.pool.size) (_hn : st.cs.pool[i]? = some n) (hf : Fits X.posOf n)
    (hw1 : 1 ≤ w) (hw64 : w ≤ 64)
    (h0 : ¬ (opC n.op = 0 ∧ opLo n.op + opHi n.op * 256 = w))
    (h10 : ¬ (opC n.op = 0x10 ∧ tailLen n = 2)) (h80 : ¬ (opC n.op = 0x80 ∧ tailLen n = 1))
    (h20 : ¬ (opC n.op = 0x20 ∧ tailLen n = 2))
    (hlin : Bcf.lin st.cs.pool w i = Lin.atom i) (a b base mid i' ok : BitVec 32) (k : BitVec 64) :
    WP Vbcf.prog plT1 (RetQ (PlRet W sb X c0 prems params st c c.k.sp.toNat
        (plEnc st.cs.pool (Bcf.lin st.cs.pool w i)))) (plFE sb w st i n d a b base mid i' ok k) s := by
  have h1 := opC_lt32 n.op
  have h2 := hf.tailLen
  have h3 := hf.lo
  have h4 := hf.hi
  unfold plFE
  apply lfT1_skip (by omega) (by omega) (by omega) h0
  apply lfT2_skip (by omega) (by omega) h10
  apply lfT3_skip (by omega) (by omega) h80
  apply lfT4_skip (by omega) (by omega) h20
  exact lfT5_spec h hR hi hw1 hw64 hlin _ _ _ _ _ _ _ _ _ _ _

/-- A literal. -/
theorem lfT0_val {w' v : Nat} {args : Array Nat} (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (hi : i < st.cs.pool.size)
    (hn : st.cs.pool[i]? = some ⟨.bvVal w' v, args⟩) (hf : Fits X.posOf ⟨.bvVal w' v, args⟩)
    (hw1 : 1 ≤ w) (hw64 : w ≤ 64) (a b mid i' ok : BitVec 32) (k : BitVec 64) :
    WP Vbcf.prog plT0 (RetQ (PlRet W sb X c0 prems params st c c.k.sp.toNat
        (plEnc st.cs.pool (Bcf.lin st.cs.pool w i))))
      (plFE sb w st i ⟨.bvVal w' v, args⟩ d a b c.k.sp mid i' ok k) s := by
  have hs := prog_ck
  unfold plT0
  apply WP.ite_seq
  rule_simp [plFE, plFEnv, opC]
  unfold plFVal
  apply WP.call_seq (poly_lit_val_spec W sb X c0 c prems params st w i)
    (vs := [.ptr sb 0, uv w, uv (offs st.cs.pool i)]) (by rule_simp) ⟨rfl, h, hR, hi, by omega⟩
  rintro rv s' ⟨r, rfl, hr⟩
  rcases hr with ⟨rfl, rfl, hnone⟩ | ⟨rfl, kk, vl, hsome, hvl, h'⟩
  · rule_simp
    apply WP.ite; rule_simp; apply WP.skip; simp only [LoopQ]
    have hww : w' ≠ w := by
      intro e; rw [pl_litVal_val hn, ite_eq_left e] at hnone; cases hnone
    have hlin : Bcf.lin st.cs.pool w i = Lin.atom i := by rw [pl_lin_val hn, ite_eq_right hww]
    exact lfT1_atom (n := ⟨.bvVal w' v, args⟩) h hR hi hn hf hw1 hw64 (by simp [opC])
      (by simp [opC]) (by simp [opC]) (by simp [opC]) hlin _ _ _ _ _ _ _
  · rule_simp
    apply WP.ite; rule_simp
    have hR' := hR.wev (wk := c.k.work) (er := c.k.err) (vl := vl)
    have h := h'
    apply WP.pl_call (lin_push64_spec W sb X c0 _ prems params st vl) (by rule_simp) ⟨rfl, h, hR'⟩
    intro s2 r2 hr2
    rule_simp
    apply WP.rule_ret; rule_simp
    have hww : w' = w := by
      by_cases e : w' = w
      · exact e
      · rw [pl_litVal_val hn, ite_eq_right e] at hsome; cases hsome
    subst hww
    rw [pl_litVal_val hn, ite_eq_left rfl] at hsome
    cases hsome
    rw [pl_lin_val hn, ite_eq_left rfl, PlRet.stk_eq (c := c) (c1 := c.wev c.k.work c.k.err vl) rfl]
    simpa [plEnc, Lin.ofConst, hvl] using hr2

end cases

end Vbcf.Proof
