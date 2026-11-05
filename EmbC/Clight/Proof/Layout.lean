import EmbC.Clight.Proof.MemRel

/-!
# Struct layout facts for scalar-field structs
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem alignof_type (ce : CC.CompositeEnv) {t : Ty} (h : t.isStruct = false) :
    CC.alignof ce (type t) = CC.sizeChunk (chunkOf t) := by
  cases t <;> simp [Ty.isStruct] at h <;> rfl

theorem layout_scalar (ce : CC.CompositeEnv) (pos : CC.Z) (id : CC.Ident) {t : Ty}
    (h : t.isStruct = false) :
    ∃ off, CC.layoutField ce pos (.Member_plain id (type t)) = .OK (off, .Full) ∧
      pos ≤ 8 * off ∧
      8 * off + 8 * CC.sizeChunk (chunkOf t) = CC.nextField ce pos (.Member_plain id (type t)) := by
  simp only [CC.layoutField, CC.nextField, CC.bitalignof, CC.bitsizeof, alignof_type ce h,
    sizeof_type ce h, CC.align, CC.zdiv]
  refine ⟨_, rfl, ?_⟩
  have hs : CC.sizeChunk (chunkOf t) = 4 ∨ CC.sizeChunk (chunkOf t) = 8 := by
    cases t <;> simp [chunkOf, CC.sizeChunk]
  rcases hs with hs | hs <;> rw [hs]
  · have e1 : ∀ x : Int, Int.fdiv x (4 * 8) = x / 32 := fun x => Int.fdiv_eq_ediv_of_nonneg _ (by decide)
    have e2 : ∀ x : Int, Int.fdiv x 8 = x / 8 := fun x => Int.fdiv_eq_ediv_of_nonneg _ (by decide)
    rw [e1, e2]
    have key : ∀ p : Int, p ≤ 8 * ((p + 4 * 8 - 1) / 32 * (4 * 8) / 8) ∧
      8 * ((p + 4 * 8 - 1) / 32 * (4 * 8) / 8) + 8 * 4 = (p + 4 * 8 - 1) / 32 * (4 * 8) + 4 * 8 := by
      intro p; omega
    exact key pos
  · have e1 : ∀ x : Int, Int.fdiv x (8 * 8) = x / 64 := fun x => Int.fdiv_eq_ediv_of_nonneg _ (by decide)
    have e2 : ∀ x : Int, Int.fdiv x 8 = x / 8 := fun x => Int.fdiv_eq_ediv_of_nonneg _ (by decide)
    rw [e1, e2]
    have key : ∀ p : Int, p ≤ 8 * ((p + 8 * 8 - 1) / 64 * (8 * 8) / 8) ∧
      8 * ((p + 8 * 8 - 1) / 64 * (8 * 8) / 8) + 8 * 8 = (p + 8 * 8 - 1) / 64 * (8 * 8) + 8 * 8 := by
      intro p; omega
    exact key pos

theorem ite_pos' {α : Type} {p : Prop} {inst : Decidable p} (h : p) (a b : α) :
    @ite α p inst a b = a := @if_pos p inst h α a b

theorem ite_neg' {α : Type} {p : Prop} {inst : Decidable p} (h : ¬p) (a b : α) :
    @ite α p inst a b = b := @if_neg p inst h α a b

def memList (fs : List (String × Ty)) : List CC.Member :=
  fs.map fun (f, t) => .Member_plain (CC.identOfString f) (type t)

theorem memList_cons (x : String × Ty) (rest : List (String × Ty)) :
    memList (x :: rest) = .Member_plain (CC.identOfString x.1) (type x.2) :: memList rest := rfl

theorem members_eq (d : StructDef) : members d = memList d.fields := rfl

def Scalars (fs : List (String × Ty)) : Prop := ∀ x ∈ fs, x.2.isStruct = false

theorem nextField_ge (ce : CC.CompositeEnv) (pos : CC.Z) (id : CC.Ident) {t : Ty}
    (h : t.isStruct = false) : pos ≤ CC.nextField ce pos (.Member_plain id (type t)) := by
  obtain ⟨off, _, h1, h2⟩ := layout_scalar ce pos id h
  have := sizeChunk_chunkOf_pos t
  have key : ∀ a b c d : Int, a ≤ 8 * b → 8 * b + 8 * c = d → 0 < c → a ≤ d := by
    intro a b c d h1 h2 h3; omega
  exact key _ _ _ _ h1 h2 this

theorem bitsize_mono (ce : CC.CompositeEnv) : ∀ (fs : List (String × Ty)) (pos : CC.Z),
    Scalars fs → pos ≤ CC.bitsizeofStruct ce pos (memList fs)
  | [], _, _ => Int.le_refl _
  | (g, u) :: rest, pos, hs => by
    simp only [memList_cons, CC.bitsizeofStruct]
    exact Int.le_trans (nextField_ge ce pos _ (hs (g, u) (.head _)))
      (bitsize_mono ce rest _ fun x hx => hs x (.tail _ hx))

theorem nextField_indep (ce ce' : CC.CompositeEnv) (pos : CC.Z) (id : CC.Ident) {t : Ty}
    (h : t.isStruct = false) :
    CC.nextField ce pos (.Member_plain id (type t)) = CC.nextField ce' pos (.Member_plain id (type t)) := by
  simp only [CC.nextField, CC.bitalignof, CC.bitsizeof, alignof_type _ h, sizeof_type _ h]

theorem bitsize_indep (ce ce' : CC.CompositeEnv) : ∀ (fs : List (String × Ty)) (pos : CC.Z),
    Scalars fs → CC.bitsizeofStruct ce pos (memList fs) = CC.bitsizeofStruct ce' pos (memList fs)
  | [], _, _ => rfl
  | (g, u) :: rest, pos, hs => by
    simp only [memList_cons, CC.bitsizeofStruct]
    rw [nextField_indep ce ce' pos _ (hs (g, u) (.head _))]
    exact bitsize_indep ce ce' rest _ fun x hx => hs x (.tail _ hx)

def idents (fs : List (String × Ty)) : List CC.Ident := fs.map fun x => CC.identOfString x.1

theorem ident_mem_of_get {fs : List (String × Ty)} {i : Nat} {f : String} {t : Ty}
    (h : fs[i]? = some (f, t)) : CC.identOfString f ∈ idents fs := by
  unfold idents
  exact List.mem_map.mpr ⟨(f, t), List.mem_of_getElem? h, rfl⟩

theorem field_rec (ce : CC.CompositeEnv) : ∀ (fs : List (String × Ty)) (pos : CC.Z) (i : Nat)
    (f : String) (t : Ty), Scalars fs → (idents fs).Nodup → fs[i]? = some (f, t) →
    ∃ off, CC.fieldOffsetRec ce (CC.identOfString f) pos (memList fs) = .OK (off, .Full) ∧
      pos ≤ 8 * off ∧
      8 * off + 8 * CC.sizeChunk (chunkOf t) ≤ CC.bitsizeofStruct ce pos (memList fs)
  | [], _, _, _, _, _, _, h => by simp at h
  | (g, u) :: rest, pos, 0, f, t, hs, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    have hu := hs (g, u) (.head _)
    obtain ⟨off, e1, e2, e3⟩ := layout_scalar ce pos (CC.identOfString g) hu
    refine ⟨off, ?_, e2, ?_⟩
    · simp only [memList_cons, CC.fieldOffsetRec, CC.Member.name]; simp only [↓reduceIte]; exact e1
    · simp only [memList_cons, CC.bitsizeofStruct]
      rw [e3]
      exact bitsize_mono ce rest _ fun x hx => hs x (.tail _ hx)
  | (g, u) :: rest, pos, i + 1, f, t, hs, hnd, h => by
    simp only [List.getElem?_cons_succ] at h
    have hne : CC.identOfString f ≠ CC.identOfString g := by
      intro e
      simp only [idents, List.map_cons, List.nodup_cons] at hnd
      exact hnd.1 (e ▸ ident_mem_of_get h)
    have hs' : Scalars rest := fun x hx => hs x (.tail _ hx)
    have hnd' : (idents rest).Nodup := by
      simp only [idents, List.map_cons, List.nodup_cons] at hnd; exact hnd.2
    obtain ⟨off, e1, e2, e3⟩ := field_rec ce rest
      (CC.nextField ce pos (.Member_plain (CC.identOfString g) (type u))) i f t hs' hnd' h
    refine ⟨off, ?_, Int.le_trans (nextField_ge ce pos (CC.identOfString g) (hs (g, u) (.head _))) e2, ?_⟩
    · simp only [memList_cons, CC.fieldOffsetRec, CC.Member.name]; simp only [hne, ↓reduceIte]; exact e1
    · simp only [memList_cons, CC.bitsizeofStruct]; exact e3

theorem field_disj (ce : CC.CompositeEnv) : ∀ (fs : List (String × Ty)) (pos : CC.Z)
    (i i' : Nat) (f f' : String) (t t' : Ty) (off off' : CC.Z) (bf bf' : CC.Bitfield),
    Scalars fs → (idents fs).Nodup → fs[i]? = some (f, t) → fs[i']? = some (f', t') → i < i' →
    CC.fieldOffsetRec ce (CC.identOfString f) pos (memList fs) = .OK (off, bf) →
    CC.fieldOffsetRec ce (CC.identOfString f') pos (memList fs) = .OK (off', bf') →
    off + CC.sizeChunk (chunkOf t) ≤ off'
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _ => by simp at h
  | (g, u) :: rest, pos, 0, i' + 1, f, f', t, t', off, off', bf, bf', hs, hnd, h, h', _, e, e' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    simp only [List.getElem?_cons_succ] at h'
    have hne : CC.identOfString f' ≠ CC.identOfString g := by
      intro eq
      simp only [idents, List.map_cons, List.nodup_cons] at hnd
      exact hnd.1 (eq ▸ ident_mem_of_get h')
    have hs' : Scalars rest := fun x hx => hs x (.tail _ hx)
    have hnd' : (idents rest).Nodup := by
      simp only [idents, List.map_cons, List.nodup_cons] at hnd; exact hnd.2
    have hu := hs (g, u) (.head _)
    obtain ⟨o, e1, _, e3⟩ := layout_scalar ce pos (CC.identOfString g) hu
    simp only [memList_cons, CC.fieldOffsetRec, CC.Member.name] at e; simp only [↓reduceIte] at e
    rw [e1] at e; cases e
    simp only [memList_cons, CC.fieldOffsetRec, CC.Member.name] at e'; simp only [hne, ↓reduceIte] at e'
    obtain ⟨o', e1', e2', _⟩ := field_rec ce rest _ i' f' t' hs' hnd' h'
    rw [e1'] at e'; cases e'
    have key : ∀ a b c d : Int, 8 * a + 8 * b = c → c ≤ 8 * d → a + b ≤ d := by
      intro a b c d h1 h2; omega
    exact key _ _ _ _ e3 e2'
  | (g, u) :: rest, pos, i + 1, i' + 1, f, f', t, t', off, off', bf, bf', hs, hnd, h, h', hlt, e, e' => by
    simp only [List.getElem?_cons_succ] at h h'
    have hs' : Scalars rest := fun x hx => hs x (.tail _ hx)
    have hnd' : (idents rest).Nodup := by
      simp only [idents, List.map_cons, List.nodup_cons] at hnd; exact hnd.2
    have hne : ∀ {f₀ : String} {t₀ : Ty} {k : Nat}, rest[k]? = some (f₀, t₀) →
        CC.identOfString f₀ ≠ CC.identOfString g := by
      intro f₀ t₀ k hk eq
      simp only [idents, List.map_cons, List.nodup_cons] at hnd
      exact hnd.1 (eq ▸ ident_mem_of_get hk)
    simp only [memList_cons, CC.fieldOffsetRec, CC.Member.name] at e; simp only [(hne h), ↓reduceIte] at e
    simp only [memList_cons, CC.fieldOffsetRec, CC.Member.name] at e'; simp only [(hne h'), ↓reduceIte] at e'
    exact field_disj ce rest _ i i' f f' t t' off off' bf bf' hs' hnd' h h' (by omega) e e'
  | (g, u) :: rest, pos, _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, _, hlt, _, _ => by omega
  | (g, u) :: rest, pos, 0, 0, _, _, _, _, _, _, _, _, _, _, _, _, hlt, _, _ => by omega

end EmbC.Clight.Proof
