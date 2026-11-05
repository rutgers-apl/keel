import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Clause1

/-!
# Vbcf proofs: the Clause family, part 2 — stack lemmas, `cl_byte`, `cl_half`, `cl_lits`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## The scratch stack: pointer, stores, `sp` -/

section stk
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {m : Mem}

/-- A non-empty stack is allocated, at offset 0. -/
theorem RCtx.stk_eq (hR : RCtx W X c0 prems params c st) (h : Holds W m sb c)
    (hsp : 0 < c.k.sp.toNat) : c.k.stk = some (stkB c, 0) := by
  have hok := hR.core.stk
  cases hc : c.k.stk with
  | none =>
    have := hok.null hc
    have := hok.cap.1
    simp_all
  | some bo =>
    obtain ⟨b, o⟩ := bo
    have := (h.arr .stk b o hc).1
    subst this
    simp [stkB, hc]

/-- Cells below `sp` are in bounds. -/
theorem RCtx.stk_size (hR : RCtx W X c0 prems params c st) (h : Holds W m sb c)
    (hsp : 0 < c.k.sp.toNat) : c.k.sp.toNat ≤ c.stk.size := by
  have hok := hR.core.stk
  rw [hok.size _ _ (hR.stk_eq h hsp)]
  exact hok.cap.1

theorem RCtx.sp_lt (hR : RCtx W X c0 prems params c st) : c.k.sp.toNat ≤ 2 * maxPool :=
  Nat.le_trans hR.core.stk.cap.1 hR.core.stk.cap.2

/-- A store into the stack keeps the rule context. -/
theorem RCtx.set_stk (hR : RCtx W X c0 prems params c st) (i : Nat) (v : EmbC.Val) :
    RCtx W X c0 prems params { c with stk := c.stk.setIfInBounds i v } st := by
  apply hR.after_push (by constructor <;> rfl)
  have hok := hR.core.stk
  exact ⟨hok.null, fun b o hb => by simpa using hok.size b o hb, hok.cap⟩

/-- Lowering `sp` keeps the rule context. -/
theorem RCtx.set_sp (hR : RCtx W X c0 prems params c st) (x : BitVec 32)
    (hx : x.toNat ≤ c.k.sp.toNat) :
    RCtx W X c0 prems params { c with k := { c.k with sp := x } } st := by
  apply hR.after_push (by constructor <;> rfl)
  have hok := hR.core.stk
  have := hok.cap
  exact ⟨hok.null, hok.size, ⟨by simp only; omega, hok.cap.2⟩⟩

end stk

/-! ## Lists on the stack -/

section stktop
variable {c c' : CMem} {st : VSt}

theorem StkTop.split {base : Nat} {A B : List Nat} (ht : StkTop c st base (A ++ B)) :
    StkTop c st (base + A.length) B :=
  ⟨by have := ht.1; simp at this; omega, ht.2.drop_left⟩

theorem StkIds.frame {base : Nat} {A : List Nat} (hA : StkIds c st base A)
    (hpre : ∀ j, j < base + A.length → c'.stk[j]? = c.stk[j]?) : StkIds c' st base A := by
  intro j i hj
  obtain ⟨hi, hU⟩ := hA j i hj
  have := lt_length_of_getElem? hj
  exact ⟨hi, by unfold U; rw [hpre _ (by omega)]; exact hU⟩

theorem StkTop.join {base : Nat} {A B : List Nat} (hA : StkIds c st base A)
    (hB : StkTop c st (base + A.length) B) : StkTop c st base (A ++ B) := by
  refine ⟨by rw [hB.1]; simp; omega, ?_⟩
  intro j i hj
  rcases Nat.lt_or_ge j A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hj
    exact hA j i hj
  · rw [List.getElem?_append_right hge] at hj
    have := hB.2 _ _ hj
    rwa [show base + A.length + (j - A.length) = base + j by omega] at this

theorem StkTop.lt_size {base : Nat} {A : List Nat} (ht : StkTop c st base A) {j : Nat}
    (hj : j < A.length) : st.lv A[j] :=
  (ht.2 j _ (List.getElem?_eq_getElem hj)).1

theorem StkTop.cell {base : Nat} {A : List Nat} (ht : StkTop c st base A) {j : Nat}
    (hj : j < A.length) : c.stk[base + j]? = some (uv (st.id A[j])) :=
  (ht.2 j _ (List.getElem?_eq_getElem hj)).2

end stktop

/-! ## `cl_byte`, `cl_half` -/

/-- The postcondition of a pure function returning the word `v`. -/
def PureRet (s : (KernelState prog State)) (v : Nat) : Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  s' = s ∧ rv = some (uv v)

def ClByteSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (k : Nat),
    FnSpec (State := State) Vbcf.prog "cl_byte"
      (fun vs s => vs = [.ptr sb 0, uv k] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ k < 4 * params.length)
      (fun _ s => PureRet s (paramByte params k))

theorem cl_byte_spec : ClByteSpec (State := State) := by
  intro W sb X c0 c prems params st k
  have hs := prog_ck
  apply FnSpec.intro' (fn := clByte) rfl
  rintro vs s ⟨rfl, h, hR, hk⟩
  simp [clByte, bindParams, Mem.hasTy_ptr h.ck rfl]
  have hlen := hR.par.1
  have hw := hR.par_lt (j := k / 4) (by omega)
  apply WP.ret
  rule_simp [cw_div, cw_mod, cw_mul, cw_shr hw, (by omega : 8 * (k % 4) < 32)]
  refine ⟨rfl, rfl, ?_⟩
  unfold paramByte
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    Nat.shiftRight_eq_div_pow, show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

def ClHalfSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (t : Nat),
    FnSpec (State := State) Vbcf.prog "cl_half"
      (fun vs s => vs = [.ptr sb 0, uv t] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ t < 2 * params.length)
      (fun _ s => PureRet s (clHalfW params t))

theorem cl_half_spec : ClHalfSpec (State := State) := by
  intro W sb X c0 c prems params st t
  have hs := prog_ck
  apply FnSpec.intro' (fn := clHalf) rfl
  rintro vs s ⟨rfl, h, hR, ht⟩
  simp [clHalf, bindParams, Mem.hasTy_ptr h.ck rfl]
  have hlen := hR.par.1
  have hw := hR.par_lt (j := t / 2) (by omega)
  apply WP.ret
  rule_simp [cw_div, cw_mod, cw_mul, cw_shr hw, cw_andffff, (by omega : 16 * (t % 2) < 32)]
  refine ⟨rfl, rfl, ?_⟩
  unfold clHalfW
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    Nat.shiftRight_eq_div_pow, show (0xffff : Nat) = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ## Helpers that push on the stack -/

/-- A pivot as a word: `NOID` for none, else the id of the node.  A dead node (one the
Lean checker found but the C pool no longer holds, see `FindRes`) is `NOID` too: no
live clause contains it, so erasing it, or comparing a live literal with it, is the
same as for no pivot. -/
def PivW (st : VSt) (po : Option Nat) (w : BitVec 32) : Prop :=
  match po with
  | none => w = 4294967295#32
  | some i => (st.lv i ∧ w = BitVec.ofNat 32 (st.id i)) ∨ (¬ st.lv i ∧ w = 4294967295#32)

theorem PivW.of_find {st : VSt} {n : Node} {r : BitVec 32} (hf : FindRes st n r) :
    PivW st (findNode st n) r := by
  unfold FindRes at hf
  unfold PivW
  split at hf
  · rename_i he; rw [he]; exact hf
  · rename_i i he; rw [he]
    rcases hf with ⟨h1, -, h3⟩ | h
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr h

/-- What a helper that pushes the list `l` returns: `0`, or `1` with `l` pushed. -/
def PushRet (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (is l : List Nat) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (r = 0#32 ∨ (r = 1#32 ∧ StkTop c' st base (is ++ l)))

/-- A postcondition `R r s'` on the returned word, as a body postcondition. -/
def RetQ (R : BitVec 32 → (KernelState prog State) → Prop) : (Post prog State) := fun o _ s' =>
  match o with
  | .ret (some (.u32 r)) => R r s'
  | _ => False

instance {R : BitVec 32 → (KernelState prog State) → Prop} : RetsTo (RetQ R) R := ⟨fun _ _ _ h => h⟩

theorem RetQ.intro {fn : Fn} (hr : fn.ret = some .u32) {R : BitVec 32 → (KernelState prog State) → Prop} {env : Env}
    {s : (KernelState prog State)} (H : WP Vbcf.prog fn.body (RetQ R) env s) :
    WP Vbcf.prog fn.body (retPost fn.ret (fun rv s' => ∃ r, rv = some (.u32 r) ∧ R r s')) env s := by
  rw [hr]
  refine WP.mono H ?_
  intro o env' s' hq
  unfold RetQ at hq
  split at hq
  · rename_i r
    exact ⟨rfl, r, rfl, hq⟩
  · exact hq.elim

theorem cl_litsOf_ne {st : St} {p : Nat} {n : Node} (po : Option Nat) (hn : st.pool[p]? = some n)
    (hop : n.op ≠ .disj) : litsOf st p po = [p] := by
  obtain ⟨op, args⟩ := n
  simp only at hop
  unfold litsOf
  simp only [St.node, hn, Option.bind_some]
  cases op <;> simp_all [isDisjNode]

theorem cl_litsOf_disj {st : St} {p : Nat} {args : Array Nat} {po : Option Nat}
    (hn : st.pool[p]? = some ⟨.disj, args⟩) : litsOf st p po = if some p = po then [p] else args.toList := by
  unfold litsOf
  simp only [St.node, hn, Option.bind_some, isDisjNode]

def ClLitsSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (p : Nat) (po : Option Nat) (pw : BitVec 32) (base : Nat) (is : List Nat),
    FnSpec (State := State) Vbcf.prog "cl_lits"
      (fun vs s => vs = [.ptr sb 0, uv (st.id p), .u32 pw] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv p ∧ PivW st po pw ∧ StkTop c st base is)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        PushRet W sb X c0 prems params st base is (litsOf st p po) r s')

theorem cl_lits_spec : ClLitsSpec (State := State) := by
  intro W sb X c0 c prems params st p po pw base is
  have hs := prog_ck
  apply FnSpec.intro' (fn := clLits) rfl
  rintro vs s ⟨rfl, h, hR, hp, hpw, htop⟩
  simp [clLits, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := clLits) rfl
  simp only [clLits, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨n, hn⟩ := node_of_lv hp
  have hpiv : (BitVec.ofNat 32 (st.id p) = pw) ↔ po = some p := by
    unfold PivW at hpw
    split at hpw
    · subst hpw; rw [hR.core.id_ne_noid hp]; simp
    · rename_i i
      rcases hpw with ⟨hi, rfl⟩ | ⟨hi, rfl⟩
      · rw [hR.core.id_inj hp hi]; simp [eq_comm]
      · rw [hR.core.id_ne_noid hp]; simp only [false_iff, Option.some.injEq]
        intro e; subst e; exact hi hp
  apply WP.ite_seq
  rule_simp [hR.core.rdHdr hn, hpiv]
  refine ⟨fun hop hne => ?_, fun hcond => ?_⟩
  · obtain ⟨args, rfl, -, -, -⟩ := hR.core.argsN hn hop
    apply WP.rule_push_args h hR p hn (show ¬ IsLeaf Op.disj by decide) htop
    refine ⟨by rule_simp, ?_⟩
    intro s' c' ok h' hR' hok
    rule_simp
    rule_ret
    rw [cl_litsOf_disj hn, ite_eq_right (fun e => hne e.symm)]
    exact ⟨c', h', hR', hok⟩
  · have hl : litsOf st p po = [p] := by
      by_cases hop : n.op = .disj
      · have he := hcond hop
        obtain ⟨args, rfl, -, -, -⟩ := hR.core.argsN hn hop
        rw [cl_litsOf_disj hn, ite_eq_left he.symm]
      · exact cl_litsOf_ne po hn hop
    apply WP.rule_push h hR
    rule_simp
    intro s' c' ok h' hP
    rule_ret
    rw [hl]
    refine ⟨c', h', hP.1, ?_⟩
    by_cases h0 : ok = 0#32
    · exact Or.inl h0
    · refine Or.inr ⟨?_, StkTop.push htop hP h0 hp⟩
      rcases hP.2.2 with ⟨e, -⟩ | ⟨e, -⟩
      · exact absurd e h0
      · exact e

theorem PivW.eq_iff {posOf : Nat → Nat} {c : CMem} {st : VSt} {po : Option Nat} {pw : BitVec 32}
    (hc : VInv posOf c st) (hpw : PivW st po pw) {i : Nat} (hi : st.lv i) :
    (BitVec.ofNat 32 (st.id i) = pw) ↔ po = some i := by
  unfold PivW at hpw
  split at hpw
  · subst hpw; rw [hc.id_ne_noid hi]; simp
  · rename_i j
    rcases hpw with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
    · rw [hc.id_inj hi hj]; simp [eq_comm]
    · rw [hc.id_ne_noid hi]; simp only [false_iff, Option.some.injEq]
      intro e; subst e; exact hj hi

/-! ## `cl_erase` -/

/-- What `cl_erase` leaves: the list `l'` from `base` on, the cells below `base` as before. -/
def EraseRet (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (l' : List Nat) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ StkTop c' st base l' ∧
    ∀ j, j < base → c'.stk[j]? = c.stk[j]?

def ClEraseSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (po : Option Nat) (pw : BitVec 32) (l : List Nat),
    FnSpec (State := State) Vbcf.prog "cl_erase"
      (fun vs s => vs = [.ptr sb 0, uv base, .u32 pw] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ PivW st po pw ∧ StkTop c st base l)
      (fun _ _ _ s' => EraseRet W sb X c0 c prems params st base (eraseOpt l po) s')

/-- First loop of `cl_erase`: the first `j` entries are not the pivot. -/
def EraseInv1 (sb : Nat) (s : (KernelState prog State)) (base : Nat) (pw : BitVec 32) (po : Option Nat)
    (l : List Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  s' = s ∧ ∃ j, env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, uv base),
      ("pivot", .u32, .u32 pw), ("i", .u32, uv (base + j))] ∧ j ≤ l.length ∧
    ∀ j', j' < j → po ≠ l[j']?

/-- Second loop of `cl_erase`: entries `k+1..i` have moved down by one. -/
def EraseInv2 (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (pw : BitVec 32) (l : List Nat) (k : Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ c2 i, env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, uv base),
      ("pivot", .u32, .u32 pw), ("i", .u32, uv i)] ∧
    Holds W s'.mem sb c2 ∧ RCtx W X c0 prems params c2 st ∧ c2.k.sp = c.k.sp ∧
    base + k ≤ i ∧ i < base + l.length ∧
    (∀ j, j < base + k → c2.stk[j]? = c.stk[j]?) ∧
    (∀ j, base + k ≤ j → j < i → c2.stk[j]? = c.stk[j + 1]?) ∧
    (∀ j, i < j → j < base + l.length → c2.stk[j]? = c.stk[j]?)

theorem cl_erase_spec : ClEraseSpec (State := State) := by
  intro W sb X c0 c prems params st base po pw l
  have hs := prog_ck
  apply FnSpec.intro' (fn := clErase) rfl
  rintro vs s ⟨rfl, h, hR, hpw, htop⟩
  simp [clErase, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hsp1 := htop.1
  have hspw : c.k.sp = BitVec.ofNat 32 (base + l.length) := by
    rw [← hsp1]; exact (bv_ofNat_toNat _).symm
  rule_assign
  apply WP.loop_seq (EraseInv1 sb s base pw po l)
  · exact ⟨rfl, 0, by simp, by omega, fun j' hj' => by omega⟩
  rintro env s' ⟨rfl, j, rfl, hj, hne⟩
  have hstk := fun (hj : 0 < l.length) => hR.stk_eq h (by omega)
  by_cases hjl : j < l.length
  · have hstk' := hstk (by omega)
    rule_simp [hspw, hstk', rd_u32 (htop.cell hjl),
      PivW.eq_iff hR.core hpw (htop.lt_size hjl)]
    refine ⟨fun hpo => ?_, fun _ hpo => ?_⟩
    rotate_left
    · apply WP.assign_loop
      rule_simp
      refine ⟨rfl, j + 1, by simp [Nat.add_assoc], by omega, fun j' hj' => ?_⟩
      rcases Nat.lt_or_ge j' j with h1 | h1
      · exact hne j' h1
      · rw [show j' = j by omega, List.getElem?_eq_getElem hjl]; exact hpo
    have hpo := hpo hjl
    have herase : eraseOpt l po = l.eraseIdx j := by
      rw [hpo]
      refine cl_erase_at hjl rfl (fun j' hj' e => hne j' hj' ?_)
      rw [hpo, List.getElem?_eq_getElem (by omega), e]
    rw [herase]
    apply WP.ite_seq
    rule_simp [hspw]
    refine ⟨fun e => by omega, fun _ => ?_⟩
    apply WP.loop_seq (EraseInv2 W sb X c0 c prems params st base pw l j)
    · exact ⟨c, base + j, rfl, h, hR, rfl, by omega, by omega, fun _ _ => rfl,
        fun j' h1 h2 => by omega, fun _ _ _ => rfl⟩
    clear h hR
    rintro env s2 ⟨c2, i, rfl, h, hR, hsp2, hki, hil, hlow, hmid, hup⟩
    have hsz := hR.stk_size h (by rw [hsp2]; omega)
    rw [hsp2] at hsz
    rule_simp [hsp2, hspw]
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · -- `st->sp = st->sp - 1;`
      apply WP.ck_setField hs h (by rfl)
      ck_simp [hsp2, hspw]
      intro s3 h3
      have e1 : (BitVec.ofNat 32 (base + l.length) - 1#32) = BitVec.ofNat 32 (base + l.length - 1) :=
        cw_sub (by omega) (by omega)
      rw [e1] at h3
      have hR3 := hR.set_sp (BitVec.ofNat 32 (base + l.length - 1)) (by
        rw [hsp2, hspw, uv_toNat (by omega), uv_toNat (by omega)]; omega)
      refine ⟨_, h3, hR3, ⟨?_, ?_⟩, fun j' hj' => hlow j' (by omega)⟩
      · simp only
        rw [uv_toNat (by omega), List.length_eraseIdx, ite_eq_left hjl]
        omega
      · intro j' x hx
        have hj' := lt_length_of_getElem? hx
        rw [List.length_eraseIdx, ite_eq_left hjl] at hj'
        rw [List.getElem?_eq_getElem (by rw [List.length_eraseIdx, ite_eq_left hjl]; omega),
          List.getElem_eraseIdx] at hx
        simp only [Option.some.injEq] at hx
        subst hx
        split
        · rename_i hlt
          refine ⟨htop.lt_size (by omega), ?_⟩
          show c2.stk[base + j']? = _
          rw [hlow _ (by omega)]
          exact htop.cell (by omega)
        · rename_i hge
          refine ⟨htop.lt_size (by omega), ?_⟩
          show c2.stk[base + j']? = _
          rw [hmid _ (by omega) (by omega)]
          have := htop.cell (j := j' + 1) (by omega)
          rwa [show base + (j' + 1) = base + j' + 1 by omega] at this
    · -- `st->stk[i] = st->stk[i + 1]; i = i + 1;`
      have hstk2 := hR.stk_eq h (by rw [hsp2]; omega)
      have hc1 : c2.stk[i + 1]? = some (uv (st.id (l[i + 1 - base]'(by omega)))) := by
        rw [hup (i + 1) (by omega) (by omega)]
        have := htop.cell (j := i + 1 - base) (by omega)
        rwa [show base + (i + 1 - base) = i + 1 by omega] at this
      apply WP.seq
      apply WP.ck_store .stk h (by rfl) hstk2
      ck_simp [hstk2, h.rd_stk hstk2, rd_u32 hc1, uv_add, uv_toNat (show i < 4294967296 by omega),
        uv_toNat (show i + 1 < 4294967296 by omega)]
      refine ⟨by omega, ?_⟩
      intro s3 h3
      apply WP.assign_loop
      rule_simp
      have hR3 := hR.set_stk i (uv (st.id (l[i + 1 - base]'(by omega))))
      refine ⟨_, i + 1, rfl, h3, hR3, hsp2, by omega, by omega, ?_, ?_, ?_⟩
      · intro j' hj'
        simp only
        rw [Array.getElem?_setIfInBounds_ne (by omega)]
        exact hlow j' hj'
      · intro j' h1 h2
        simp only
        rcases Nat.lt_or_ge j' i with h3 | h3
        · rw [Array.getElem?_setIfInBounds_ne (by omega)]
          exact hmid j' h1 h3
        · rw [show j' = i by omega, Array.getElem?_setIfInBounds_self_of_lt (by omega),
            ← hup (i + 1) (by omega) (by omega), hc1]
      · intro j' h1 h2
        simp only
        rw [Array.getElem?_setIfInBounds_ne (by omega)]
        exact hup j' (by omega) h2
  · have hjl' : j = l.length := by omega
    subst hjl'
    rule_simp [hspw]
    apply WP.ite_seq
    rule_simp [hspw]
    have he : eraseOpt l po = l := by
      cases po with
      | none => rfl
      | some x =>
        apply List.erase_of_not_mem
        intro hx
        obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hx
        exact hne j' hj' (by rw [List.getElem?_eq_getElem hj'])
    rw [he]
    apply WP.retVoid
    simp only [LoopQ, retPost]
    exact ⟨c, h, hR, htop, fun _ _ => rfl⟩

end Vbcf.Proof
