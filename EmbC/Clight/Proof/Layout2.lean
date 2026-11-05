import EmbC.Clight.Proof.Layout
import EmbC.Clight.Proof.Program

/-!
# Struct fields lie inside the struct's footprint
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem addComposite_get : ∀ (defs : List CC.CompositeDef) (env env' : CC.CompositeEnv),
    CC.addCompositeDefinitions env defs = .OK env' → ∀ id co, env'.get id = some co →
    env.get id = some co ∨ ∃ env0 su ms a, CC.CompositeDef.Composite id su ms a ∈ defs ∧
      CC.compositeOfDef env0 id su ms a = .OK co
  | [], env, env', h, id, co, hg => by
    simp only [CC.addCompositeDefinitions] at h; cases h; exact .inl hg
  | .Composite id' su ms a :: defs, env, env', h, id, co, hg => by
    simp only [CC.addCompositeDefinitions] at h
    split at h
    · rename_i co' hco'
      rcases addComposite_get defs _ _ h id co hg with h1 | ⟨env0, su0, ms0, a0, hm, hc⟩
      · by_cases hid : id' = id
        · subst hid
          rw [CC.PTree.gss] at h1; cases h1
          exact .inr ⟨env, su, ms, a, List.mem_cons_self, hco'⟩
        · rw [CC.PTree.gso _ _ _ _ hid] at h1; exact .inl h1
      · exact .inr ⟨env0, su0, ms0, a0, List.mem_cons_of_mem _ hm, hc⟩
    · cases h

theorem alignofComposite_pos (ce : CC.CompositeEnv) : ∀ (fs : List (String × Ty)),
    Scalars fs → 1 ≤ CC.alignofComposite ce (memList fs)
  | [], _ => by simp [memList, CC.alignofComposite]
  | (g, u) :: rest, hs => by
    simp only [memList_cons, CC.alignofComposite, CC.Member.isPadding, Bool.false_eq_true, ite_false]
    have h1 := alignofComposite_pos ce rest (fun x hx => hs x (.tail _ hx))
    have h2 : CC.alignof ce (type u) = CC.sizeChunk (chunkOf u) :=
      alignof_type ce (hs (g, u) (.head _))
    have := sizeChunk_chunkOf_pos u
    show 1 ≤ max (CC.alignof ce (type u)) _
    rw [h2]
    exact Int.le_trans this (Int.le_max_left _ _)

theorem le_align (n al : Int) (h : 1 ≤ al) : n ≤ CC.align n al := by
  unfold CC.align CC.zdiv
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  have h1 := Int.mul_ediv_add_emod (n + al - 1) al
  have h2 := Int.emod_lt_of_pos (n + al - 1) (by omega : (0 : Int) < al)
  have h3 := Int.emod_nonneg (n + al - 1) (by omega : al ≠ 0)
  rw [Int.mul_comm] at h1
  omega

/-- The footprint of a struct field is inside the struct. -/
theorem field_bounds {P : Prog} (hscal : ∀ d ∈ P.structs, Scalars d.fields)
    (hids : ∀ d ∈ P.structs, (idents d.fields).Nodup)
    (hce : CC.buildCompositeEnv (composites P) = .OK (compositeEnv P))
    {s : String} {d : StructDef} {co : CC.Composite} {i : Nat} {f : String} {t : Ty}
    {off : CC.Z} {bf : CC.Bitfield}
    (hd : P.findStruct s = some d) (hco : (compositeEnv P).get (CC.identOfString s) = some co)
    (hmem : co.co_members = members d) (hi : d.fields[i]? = some (f, t))
    (hoff : CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members = .OK (off, bf)) :
    (0 : Int) ≤ off ∧ off + CC.sizeChunk (chunkOf t) ≤ co.co_sizeof := by
  have hdm : d ∈ P.structs := List.mem_of_find?_eq_some hd
  rcases addComposite_get _ _ _ hce _ _ hco with h | ⟨env0, su, ms, a, hm, hc⟩
  · simp at h
  obtain ⟨d', hd', he⟩ := List.mem_map.mp hm
  simp only [CC.CompositeDef.Composite.injEq] at he
  obtain ⟨-, rfl, rfl, rfl⟩ := he
  unfold CC.compositeOfDef at hc
  split at hc
  · cases hc
  split at hc
  · cases hc
  simp only [CC.Res.OK.injEq] at hc
  subst hc
  simp only at hmem hoff ⊢
  rw [hmem, members_eq] at hoff
  obtain ⟨off', e1, e2, e3⟩ := field_rec (compositeEnv P) d.fields 0 i f t (hscal d hdm)
    (hids d hdm) hi
  unfold CC.fieldOffset at hoff
  rw [e1] at hoff
  cases hoff
  rw [bitsize_indep (compositeEnv P) env0 _ _ (hscal d hdm), ← members_eq, ← hmem] at e3
  have e2' : (0 : Int) ≤ 8 * off := e2
  have e3' : (8 * off + 8 * CC.sizeChunk (chunkOf t) : Int) ≤
      CC.bitsizeofStruct env0 0 (members d') := e3
  have hal : 1 ≤ CC.alignAttr CC.noattr (CC.alignofComposite env0 (members d')) := by
    simp only [CC.alignAttr, CC.noattr]
    rw [hmem, members_eq]
    exact alignofComposite_pos env0 _ (hscal d hdm)
  refine ⟨by omega, ?_⟩
  refine Int.le_trans ?_ (le_align _ _ hal)
  simp only [CC.sizeofComposite, CC.sizeofStruct, CC.bytesOfBits, CC.zdiv]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have := sizeChunk_chunkOf_pos t
  omega

end EmbC.Clight.Proof
