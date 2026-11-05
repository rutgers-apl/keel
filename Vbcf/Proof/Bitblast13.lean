import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast12

/-!
# Vbcf proofs: the Bitblast family, part 13 — `bb_eq_bits`, `bb_atom`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Lean side -/

theorem bb_eqBits_step {st : St} {cs xs ys : List Nat} {k : Nat} {P : Prop}
    (hc : k < cs.length) (hx : k < xs.length) (hy : k < ys.length)
    (H : bbAtom.eqBits st (cs.drop k) (xs.drop k) (ys.drop k) = true → P)
    (he : isEqOf st cs[k] xs[k] ys[k] = true) :
    bbAtom.eqBits st (cs.drop (k + 1)) (xs.drop (k + 1)) (ys.drop (k + 1)) = true → P := fun h' =>
  H (by rw [List.drop_eq_getElem_cons hc, List.drop_eq_getElem_cons hx,
    List.drop_eq_getElem_cons hy]; simp [bbAtom.eqBits, he, h'])

theorem bb_eqBits_end {st : St} {cs xs ys : List Nat} {k : Nat} {P : Prop}
    (hc : cs.length ≤ k) (hx : xs.length ≤ k) (hy : ys.length ≤ k)
    (H : bbAtom.eqBits st (cs.drop k) (xs.drop k) (ys.drop k) = true → P) : P :=
  H (by rw [List.drop_of_length_le hc, List.drop_of_length_le hx, List.drop_of_length_le hy]; rfl)

section atom
variable {st : VSt} {a b x y : Nat} {xa ya : Array Nat}

theorem bbAtom_eq {cs : Array Nat} (hn : st.pool[a]? = some ⟨.eq, #[x, y]⟩)
    (hx : st.pool[x]? = some ⟨.bvFromBool, xa⟩) (hy : st.pool[y]? = some ⟨.bvFromBool, ya⟩)
    (hb : st.pool[b]? = some ⟨.conj, cs⟩) :
    Bcf.bbAtom st a b = bbAtom.eqBits st cs.toList xa.toList ya.toList := by
  simp [Bcf.bbAtom, hn, bitsOf, hx, hy, hb]

theorem bbAtom_ult (hn : st.pool[a]? = some ⟨.ult, #[x, y]⟩)
    (hx : st.pool[x]? = some ⟨.bvFromBool, xa⟩) (hy : st.pool[y]? = some ⟨.bvFromBool, ya⟩) :
    Bcf.bbAtom st a b = ultGo st false xa.toList.reverse ya.toList.reverse b := by
  simp [Bcf.bbAtom, hn, bitsOf, hx, hy]

theorem bbAtom_ule (hn : st.pool[a]? = some ⟨.ule, #[x, y]⟩)
    (hx : st.pool[x]? = some ⟨.bvFromBool, xa⟩) (hy : st.pool[y]? = some ⟨.bvFromBool, ya⟩) :
    Bcf.bbAtom st a b = ultGo st true xa.toList.reverse ya.toList.reverse b := by
  simp [Bcf.bbAtom, hn, bitsOf, hx, hy]

theorem bbAtom_slt (hn : st.pool[a]? = some ⟨.slt, #[x, y]⟩)
    (hx : st.pool[x]? = some ⟨.bvFromBool, xa⟩) (hy : st.pool[y]? = some ⟨.bvFromBool, ya⟩) :
    Bcf.bbAtom st a b = sltChain st false xa.toList.reverse ya.toList.reverse b := by
  simp [Bcf.bbAtom, hn, bitsOf, hx, hy]

theorem bbAtom_sle (hn : st.pool[a]? = some ⟨.sle, #[x, y]⟩)
    (hx : st.pool[x]? = some ⟨.bvFromBool, xa⟩) (hy : st.pool[y]? = some ⟨.bvFromBool, ya⟩) :
    Bcf.bbAtom st a b = sltChain st true xa.toList.reverse ya.toList.reverse b := by
  simp [Bcf.bbAtom, hn, bitsOf, hx, hy]

end atom

/-! ## `bb_eq_bits` -/

def BbEqBitsSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (b x y : Nat) (cs xs ys : Array Nat),
    FnSpec (State := State) Vbcf.prog "bb_eq_bits"
      (fun vs s => vs = [.ptr sb 0, uv (st.id b), uv (st.id x), uv (st.id y)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.pool[b]? = some ⟨.conj, cs⟩ ∧ st.lv b ∧
        st.pool[x]? = some ⟨.bvFromBool, xs⟩ ∧ st.lv x ∧ st.pool[y]? = some ⟨.bvFromBool, ys⟩∧ st.lv y )
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (bbAtom.eqBits st cs.toList xs.toList ys.toList = true) r s')

theorem bb_eq_bits_spec : BbEqBitsSpec (State := State) := by
  intro W sb X c0 c prems params st b x y cs xs ys
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbEqBits) rfl
  rintro vs s ⟨rfl, h, hR, hnb, hbl, hnx, hxl, hny, hyl⟩
  simp [bbEqBits, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbEqBits) rfl
  simp only [bbEqBits, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hszb, hargsb⟩ := hR.core.bb_args hnb (by decide)
  obtain ⟨hszx, hargsx⟩ := hR.core.bb_args hnx (by decide)
  obtain ⟨hszy, hargsy⟩ := hR.core.bb_args hny (by decide)
  rule_assign [(hR.core.rdN hnb).1, (hR.core.rdN hnb).2.1]
  apply WP.guard_lit
  rule_simp [(hR.core.rdN hnx).1, (hR.core.rdN hnx).2.1, (hR.core.rdN hny).1, (hR.core.rdN hny).2.1]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hl1 hl2 => ?_⟩
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" ["ok"] cs.size
    (fun k => bbAtom.eqBits st (cs.toList.drop k) (xs.toList.drop k) (ys.toList.drop k) = true →
      bbAtom.eqBits st cs.toList xs.toList ys.toList = true))
  · exact ⟨rfl, 0, [0#32], rfl, by simp [bbSets, Env.set], by omega, fun h => by simpa using h⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain ⟨ok, rfl⟩ := len_shape 1 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact bb_eqBits_end (by simp; omega) (by simp; omega) (by simp; omega) hres
  have hkx : k < xs.size := by omega
  have hky : k < ys.size := by omega
  refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st cs[k] 529#32 .eq xs[k] ys[k]) ?_
    ⟨rfl, h, hR, hargsb k hlt, hargsx k hkx, hargsy k hky, by decide, by decide, by decide,
      by decide⟩ ?_
  · rule_simp [(hR.core.rdN hnb).2.2 k hlt, (hR.core.rdN hnx).2.2 k hkx, (hR.core.rdN hny).2.2 k hky]
  intro r hr
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hr0 => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, k + 1, [r], rfl, by simp [bbSets, Env.set], by omega, ?_⟩
  exact bb_eqBits_step (by simpa using hlt) (by simpa using hkx) (by simpa using hky) hres
    (by simpa [isEqOf] using hr hr0)

/-! ## `bb_atom` -/

def BbAtomSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b : Nat) (na : Node),
    FnSpec (State := State) Vbcf.prog "bb_atom"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.pool[a]? = some na ∧ st.lv a ∧
        st.lv b)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        BbChk W sb X c0 prems params st c (Bcf.bbAtom st a b = true) r s')

theorem bb_atom_spec : BbAtomSpec (State := State) := by
  intro W sb X c0 c prems params st a b na
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbAtom) rfl
  rintro vs s ⟨rfl, h, hR, hna, hal, hb⟩
  simp [bbAtom, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbAtom) rfl
  simp only [bbAtom, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨op, args⟩ := na
  apply WP.bb_pure (bb_nargs_spec W sb X c0 c prems params st a _) (by rule_simp) ⟨rfl, h, hR, hna, by vlv⟩
  rule_simp
  apply WP.guard_lit
  have hsz := hR.core.bb_size_le hna
  simp only at hsz
  rule_simp
  refine ⟨fun _ => by simp [RetQ]; exact BbChk.zero h hR, fun h2 => ?_⟩
  have h2' : args.size = 2 := h2
  have hnl := hR.core.bb_not_leaf hna (by simp only; omega)
  simp only at hnl
  obtain ⟨x, y, rfl⟩ := array_eq_two h2'
  have hx := hR.core.bb_arg_lt hna (x := x) (by simp)
  have hy := hR.core.bb_arg_lt hna (x := y) (by simp)
  rule_assign [hR.core.rd2 hna hnl]
  rule_assign [hR.core.rd2 hna hnl]
  obtain ⟨nx, hnx⟩ := node_of_lv hx
  obtain ⟨ny, hny⟩ := node_of_lv hy
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnx, hR.core.rdHdr hny]
  refine ⟨fun _ => by simp [RetQ]; exact BbChk.zero h hR, fun hfx hfy => ?_⟩
  obtain ⟨opx, xa⟩ := nx
  obtain ⟨opy, ya⟩ := ny
  simp only at hfx hfy
  subst hfx hfy
  rule_assign [hR.core.rdHdr hna]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hop => ?_, fun hc1 => ?_⟩
  · subst hop
    obtain ⟨nb, hnb⟩ := node_of_lv hb
    apply WP.guard_lit
    rule_simp [hR.core.rdHdr hnb]
    refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun hcb => ?_⟩
    obtain ⟨opb, cs⟩ := nb
    simp only at hcb
    subst hcb
    refine WP.bb_call (bb_eq_bits_spec W sb X c0 c prems params st b x y cs xa ya) ?_
      ⟨rfl, h, hR, hnb, by vlv, hnx, by vlv, hny, by vlv⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbAtom_eq hna hnx hny hnb]; exact hr hn0⟩
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ _ _ _ => by simp [RetQ]; exact BbChk.zero h hR, fun hc2 => ?_⟩
  have h4 : op = .ult ∨ op = .ule ∨ op = .slt ∨ op = .sle := by
    by_cases e1 : op = .ult
    · exact Or.inl e1
    by_cases e2 : op = .ule
    · exact Or.inr (Or.inl e2)
    by_cases e3 : op = .slt
    · exact Or.inr (Or.inr (Or.inl e3))
    exact Or.inr (Or.inr (Or.inr (hc2 e1 e2 e3)))
  clear hc2
  obtain ⟨hszx, -⟩ := hR.core.bb_args hnx (by decide)
  obtain ⟨hszy, -⟩ := hR.core.bb_args hny (by decide)
  rule_assign [(hR.core.rdN hnx).1, (hR.core.rdN hnx).2.1]
  rule_assign [(hR.core.rdN hny).1, (hR.core.rdN hny).2.1]
  rule_assign
  apply WP.bb_push_args h hR x hnx (by simp [IsLeaf, isLeaf])
  refine ⟨by rule_simp [hR.core.rd2 hna hnl], ?_⟩
  intro s1 c1 ok1 h1 hR1 hcase1
  bb_swap h1 hR1
  rule_simp
  apply WP.guard_lit
  rcases hcase1 with rfl | ⟨rfl, hpre1, hsp1, htx⟩
  · rule_simp; simp only [RetQ]; exact BbChk.zero h hR
  rule_simp
  simp only at htx hsp1
  have hsp1' : c.k.sp.toNat ≤ c1.k.sp.toNat := by omega
  rule_assign
  apply WP.bb_push_args h hR y hny (by simp [IsLeaf, isLeaf])
  refine ⟨by rule_simp [hR.core.rd2 hna hnl], ?_⟩
  intro s2 c2 ok2 h2 hR2 hcase2
  bb_swap h2 hR2
  rule_simp
  apply WP.guard_lit
  rcases hcase2 with rfl | ⟨rfl, hpre2, hsp2, hty⟩
  · rule_simp; simp only [RetQ]; exact BbChk.zero h hR
  rule_simp
  simp only at hty hsp2
  have hsp2' : c1.k.sp.toNat ≤ c2.k.sp.toNat := by omega
  have hx2 := htx.bbRange.frame hpre2 hsp2'
  have hy2 := hty.bbRange
  have hfr : ∀ {P : Prop} {s4 : (KernelState prog State)} {r : BitVec 32},
      BbOK s2 P r s4 → BbChk W sb X c0 prems params st c P r s4 :=
    fun H => BbChk.trans hpre1 hsp1' (BbChk.trans hpre2 hsp2' (BbChk.ofOK h hR H))
  apply WP.seq
  apply WP.ite
  rcases h4 with rfl | rfl | rfl | rfl
  · rule_simp
    refine WP.bb_call_last_ok (bb_ult_spec W sb X c0 c2 prems params st false c.k.sp.toNat
      c1.k.sp.toNat b xa.toList ya.toList) ?_ ⟨rfl, h, hR, hx2, hy2, hb⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact hfr ⟨rfl, fun hn0 => by rw [bbAtom_ult hna hnx hny]; exact hr hn0⟩
  · rule_simp
    apply WP.ite
    rule_simp
    refine WP.bb_call_last_ok (bb_ult_spec W sb X c0 c2 prems params st true c.k.sp.toNat
      c1.k.sp.toNat b xa.toList ya.toList) ?_ ⟨rfl, h, hR, hx2, hy2, hb⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact hfr ⟨rfl, fun hn0 => by rw [bbAtom_ule hna hnx hny]; exact hr hn0⟩
  · rule_simp
    apply WP.ite
    rule_simp
    apply WP.ite
    rule_simp
    refine WP.bb_call_last_ok (bb_slt_spec W sb X c0 c2 prems params st false c.k.sp.toNat
      c1.k.sp.toNat b xa.toList ya.toList) ?_ ⟨rfl, h, hR, hx2, hy2, hb⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact hfr ⟨rfl, fun hn0 => by rw [bbAtom_slt hna hnx hny]; exact hr hn0⟩
  · rule_simp
    apply WP.ite
    rule_simp
    apply WP.ite
    rule_simp
    refine WP.bb_call_last_ok (bb_slt_spec W sb X c0 c2 prems params st true c.k.sp.toNat
      c1.k.sp.toNat b xa.toList ya.toList) ?_ ⟨rfl, h, hR, hx2, hy2, hb⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact hfr ⟨rfl, fun hn0 => by rw [bbAtom_sle hna hnx hny]; exact hr hn0⟩

end Vbcf.Proof
