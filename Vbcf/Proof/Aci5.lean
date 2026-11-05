import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Aci4

/-!
# Vbcf proofs: the Aci family, part 5 — `aci_uniq`

`aci_uniq` removes adjacent duplicates from a list on the stack sorted by id.  The result
is strictly sorted by id with the same elements, hence a permutation of
`sortNat (dedupNat l)` when the input was a permutation of `l`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Lean side -/

theorem aci_dedup_nodup (l : List Nat) : (dedupNat l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    simp only [dedupNat]
    split
    · exact ih
    · rename_i hx
      exact List.nodup_cons.mpr ⟨fun h => hx (mem_dedupNat.mp h), ih⟩

/-- A strictly sorted list with the elements of `L` is `sortNat (dedupNat L)`. -/
theorem aci_strict_eq {U L : List Nat} (hs : U.Pairwise (· < ·)) (hm : ∀ x, x ∈ U ↔ x ∈ L) :
    U = sortNat (dedupNat L) := by
  have hp1 := sortNat_perm (dedupNat L)
  have hnd : (sortNat (dedupNat L)).Nodup := hp1.nodup_iff.mpr (aci_dedup_nodup L)
  have hU : U.Nodup := List.nodup_iff_pairwise_ne.mpr (hs.imp (fun h => Nat.ne_of_lt h))
  apply aci_sorted_eq (hs.imp (fun h => Nat.le_of_lt h))
  refine ((List.perm_ext_iff_of_nodup hU hnd).mpr (fun x => ?_)).trans hp1
  rw [hm, hp1.mem_iff, mem_dedupNat]

theorem aci_take_mem_le {S : List Nat} (hs : S.Pairwise (· ≤ ·)) {p u : Nat} (hp : 0 < p)
    (hpl : p ≤ S.length) (hu : u ∈ S.take p) : u ≤ S[p - 1] := by
  obtain ⟨t, ht, htp, rfl⟩ := aci_mem_take hu
  exact aci_sorted_le hs ht (by omega) (by omega)

theorem aci_take_mem_le_by {f : Nat → Nat} {S : List Nat} (hs : S.Pairwise (fun a b => f a ≤ f b))
    {p u : Nat} (hp : 0 < p) (hpl : p ≤ S.length) (hu : u ∈ S.take p) : f u ≤ f S[p - 1] := by
  obtain ⟨t, ht, htp, rfl⟩ := aci_mem_take hu
  exact aci_sorted_le_by hs ht (by omega) (by omega)

theorem aci_take_succ_mem {S : List Nat} {p : Nat} (hp : p < S.length) (x : Nat) :
    x ∈ S.take (p + 1) ↔ x ∈ S.take p ∨ x = S[p] := by
  rw [List.take_succ_eq_append_getElem hp, List.mem_append, List.mem_singleton]

theorem aci_uq_get_i {A U G S : List Nat} {p : Nat} (hl : U.length + G.length = p)
    (hp : p < S.length) :
    (A ++ U ++ G ++ S.drop p)[A.length + p]'(by simp; omega) = S[p] := by
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_append, List.getElem_drop]
  congr 1; omega

theorem aci_uq_get_j {A U G R : List Nat} {q : Nat} (hl : U.length = q) (hq : 0 < q) :
    (A ++ U ++ G ++ R)[A.length + (q - 1)]'(by simp; omega) = U[q - 1] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
    List.getElem_append_right (by simp)]
  simp

theorem aci_uq_noset {A U G S : List Nat} {p : Nat} (hp : p < S.length) :
    A ++ U ++ G ++ S.drop p = A ++ U ++ (G ++ [S[p]]) ++ S.drop (p + 1) := by
  rw [List.drop_eq_getElem_cons hp]
  simp

theorem aci_uq_set {A U G S : List Nat} {p : Nat} (hp : p < S.length) :
    ∃ G' : List Nat, G'.length = G.length ∧
      (A ++ U ++ G ++ S.drop p).set (A.length + U.length) S[p] =
        A ++ (U ++ [S[p]]) ++ G' ++ S.drop (p + 1) := by
  rw [aci_uq_noset hp]
  obtain ⟨g, G', e⟩ : ∃ g G', G ++ [S[p]] = g :: G' := by
    cases G with
    | nil => exact ⟨S[p], [], rfl⟩
    | cons g G => exact ⟨g, G ++ [S[p]], rfl⟩
  have hlen : G'.length = G.length := by
    have := congrArg List.length e
    simp at this; omega
  refine ⟨G', hlen, ?_⟩
  rw [e, List.append_assoc, List.append_assoc, List.set_append_right _ _ (by omega),
    List.set_append_right _ _ (by simp)]
  simp

/-! ## `aci_uniq` -/

/-- What `aci_uniq` leaves: a strictly sorted list with the elements of `S`. -/
def AciUniqRes (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (A S : List Nat) (s' : (KernelState prog State)) : Prop :=
  ∃ c' U, Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    StkTop c' st base (A ++ U) ∧ U.Pairwise (fun a b => st.id a < st.id b) ∧ ∀ x, x ∈ U ↔ x ∈ S

def AciUniqSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (A S : List Nat),
    FnSpec (State := State) Vbcf.prog "aci_uniq"
      (fun vs s => vs = [.ptr sb 0, uv (base + A.length)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ StkTop c st base (A ++ S) ∧
        S.Pairwise (fun a b => st.id a ≤ st.id b))
      (fun _ _ _ s' => AciUniqRes W sb X c0 prems params st base A S s')

/-- Loop invariant of `aci_uniq`: the first `p` elements, without duplicates, are the `q`
elements of `U`; `G` is what is left in the cells between. -/
def AciUniqInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (A S : List Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (p q : Nat) (U G : List Nat),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, uv (base + A.length)),
      ("i", .u32, uv (base + A.length + p)), ("j", .u32, uv (base + A.length + q))] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ 1 ≤ q ∧ q ≤ p ∧ p ≤ S.length ∧
    U.length = q ∧ G.length = p - q ∧ U.Pairwise (fun a b => st.id a < st.id b) ∧
    (∀ x, x ∈ U ↔ x ∈ S.take p) ∧
    U[q - 1]? = S[p - 1]? ∧ StkTop c' st base (A ++ U ++ G ++ S.drop p)

theorem aci_uniq_spec : AciUniqSpec (State := State) := by
  intro W sb X c0 c prems params st base A S
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciUniq) rfl
  rintro vs s ⟨rfl, h, hR, htop, hS⟩
  simp [aciUniq, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hsp1 := htop.1
  simp only [List.length_append] at hsp1
  have hspw : c.k.sp = BitVec.ofNat 32 (base + A.length + S.length) := by
    rw [← bv_ofNat_toNat c.k.sp, hsp1]; congr 1; omega
  apply WP.ite_seq
  rule_simp [hspw]
  refine ⟨fun hne => ?_, fun he => ?_⟩
  · subst hne
    apply WP.retVoid
    exact ⟨c, [], h, hR, by simpa using htop, List.Pairwise.nil, by simp⟩
  have hS0 : 0 < S.length := List.length_pos_iff.mpr he
  rule_assign
  rule_assign
  apply WP.loop_seq (AciUniqInv W sb X c0 prems params st base A S)
  · refine ⟨c, 1, 1, [S[0]], [], by simp, h, hR, by omega, by omega, by omega, by simp, by simp,
      by simp, ?_, by simp, ?_⟩
    · intro x; rw [List.take_one]; simp [List.head?_eq_getElem?, List.getElem?_eq_getElem hS0]
    · have := List.drop_eq_getElem_cons (l := S) hS0
      simp only [List.drop_zero] at this
      rw [List.append_nil, List.append_assoc, List.singleton_append, ← this]
      exact htop
  clear h hR htop
  rintro env s' ⟨c', p, q, U, G, rfl, h, hR, hq1, hqp, hpS, hUl, hGl, hUs, hUm, hUlast, htop⟩
  have hlenL : (A ++ U ++ G ++ S.drop p).length = A.length + S.length := by
    simp [hUl, hGl]; omega
  have hsp2 := htop.1
  rw [hlenL] at hsp2
  have hspmax2 := hR.sp_lt
  simp only [maxPool] at hspmax2
  have hspw2 : c'.k.sp = BitVec.ofNat 32 (base + A.length + S.length) := by
    rw [← bv_ofNat_toNat c'.k.sp, hsp2]; congr 1; omega
  rule_simp [hspw2]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hpS' : p = S.length := by omega
    subst hpS'
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s3 h3
    refine ⟨_, U, h3, hR.set_sp _ (by rw [uv_toNat (by omega)]; omega), ⟨?_, ?_⟩, hUs, ?_⟩
    · simp only; rw [uv_toNat (by omega)]; simp [hUl]; omega
    · exact (htop.2.append_left).append_left
    · intro x; rw [hUm, List.take_of_length_le (Nat.le_refl _)]
  have hpS' : p < S.length := by omega
  have hstk := hR.stk_eq h (by omega)
  have hSp : st.lv S[p] := by
    have := htop.lt_size (j := A.length + p) (by rw [hlenL]; omega)
    rwa [aci_uq_get_i (by omega) hpS'] at this
  have hci : rd c'.stk (base + A.length + p) = some (uv (st.id S[p])) := by
    have := htop.aci_rd (j := A.length + p) (by rw [hlenL]; omega)
    rwa [aci_uq_get_i (by omega) hpS', ← Nat.add_assoc] at this
  have hlastU : U[q - 1]'(by omega) = S[p - 1]'(by omega) := by
    have := hUlast
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have hSp1 : st.lv S[p - 1] := by
    have := htop.lt_size (j := A.length + (q - 1)) (by rw [hlenL]; omega)
    rwa [aci_uq_get_j hUl (by omega), hlastU] at this
  have hcj : rd c'.stk (base + A.length + (q - 1)) = some (uv (st.id S[p - 1])) := by
    have := htop.aci_rd (j := A.length + (q - 1)) (by rw [hlenL]; omega)
    rwa [aci_uq_get_j hUl (by omega), hlastU, ← Nat.add_assoc] at this
  have hj1 : BitVec.ofNat 32 (base + A.length + q) - 1#32 =
      BitVec.ofNat 32 (base + A.length + (q - 1)) := by
    rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl, cw_sub (by omega) (by omega)]
    congr 1; omega
  have hle : st.id S[p - 1] ≤ st.id S[p] := aci_sorted_le_by hS (by omega) hpS' (by omega)
  apply WP.ite_seq
  rule_simp [hstk, hci, hcj, hj1, hR.core.id_inj hSp hSp1]
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · obtain ⟨G', hG', hset⟩ := aci_uq_set (A := A) (U := U) (G := G) hpS'
    apply WP.seq
    apply WP.aci_stk_store h hR htop (p := A.length + q) (y := S[p]) (by rw [hlenL]; omega) hSp
      (by simp [Env.get]) (by simp [evalE, Env.get, Nat.add_assoc])
      (by rule_simp [hstk, hci])
    intro s3 c3 h3 hR3 htop3
    rw [← hUl, hset] at htop3
    apply WP.assign_loop
    rule_simp
    apply WP.assign_loop
    rule_simp
    refine ⟨c3, p + 1, q + 1, U ++ [S[p]], G', by simp [Nat.add_assoc], h3, hR3, by omega, by omega,
      by omega, by simp [hUl], by omega, ?_, ?_, ?_, htop3⟩
    · rw [List.pairwise_append]
      refine ⟨hUs, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      have h1 := aci_take_mem_le_by hS (by omega) (by omega) ((hUm a).mp ha)
      have h2 : st.id S[p - 1] ≠ st.id S[p] := fun e => hne (st.id_inj hSp hSp1 e.symm)
      omega
    · intro x
      rw [aci_take_succ_mem hpS', List.mem_append, List.mem_singleton, hUm]
    · simp [hUl]
  · apply WP.assign_loop
    rule_simp
    refine ⟨c', p + 1, q, U, G ++ [S[p]], by simp [Nat.add_assoc], h, hR, by omega, by omega,
      by omega, hUl, by simp [hGl]; omega, hUs, ?_, ?_, ?_⟩
    · intro x
      rw [aci_take_succ_mem hpS', hUm]
      constructor
      · exact Or.inl
      · rintro (hx | rfl)
        · exact hx
        · rw [heq]
          have := List.getElem_mem (l := S.take p) (n := p - 1) (by simp; omega)
          simpa [List.getElem_take] using this
    · rw [hUlast, show p + 1 - 1 = p by omega, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem hpS', heq]
    · rw [← aci_uq_noset hpS']; exact htop

end Vbcf.Proof
