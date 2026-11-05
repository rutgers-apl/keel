import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rules

/-!
# Vbcf proofs: growing an owned array

`Holds.grow` covers the idiom used by `ck_room` and `push`:

    np = kvrealloc(st->F, array_size(n, sizeof(u32)));
    if (np == NULL) { ... }
    st->F = np;

It describes the memory after a successful `kvrealloc` followed by the store
of the new pointer into the struct, and shows that `Holds` is re-established
with the array's contents carried over.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

/-- Field name and index of an owned array's pointer. -/
def Arr.field : Arr → String × Nat
  | .pool => ("pool", 0)
  | .htab => ("htab", 3)
  | .facts => ("facts", 6)
  | .stk => ("stk", 10)
  | .prem => ("prem", 13)
  | .lr => ("lr", 23)

def CK.setPtr (k : CK) : Arr → Ptr → CK
  | .pool, p => { k with pool := p }
  | .htab, p => { k with htab := p }
  | .facts, p => { k with facts := p }
  | .stk, p => { k with stk := p }
  | .prem, p => { k with prem := p }
  | .lr, p => { k with lr := p }

theorem CK.setPtr_cells (k : CK) (a : Arr) (p : Ptr) :
    (k.setPtr a p).cells = k.cells.setIfInBounds a.field.2 p.val := by
  cases a <;> simp [CK.setPtr, CK.cells, Arr.field]

theorem CK.setPtr_ptr (k : CK) (a a' : Arr) (p : Ptr) :
    (k.setPtr a p).ptr a' = if a' = a then p else k.ptr a' := by
  cases a <;> cases a' <;> simp [CK.setPtr, CK.ptr]

theorem Arr.field_slot (a : Arr) : fieldIn ckS.fields a.field.1 = some (a.field.2, .ptr .u32) := by
  cases a <;> simp [Arr.field, ckS, fieldIn]

/-- The contents an array has before it is reallocated: nothing if the
pointer is still `NULL`. -/
def CMem.old (c : CMem) (a : Arr) : Array Val :=
  match c.k.ptr a with
  | none => #[]
  | some _ => c.arr a

/-- Memory after a successful `kvrealloc` of array `a` to `n` cells. -/
def growMem (m : Mem) (c : CMem) (a : Arr) (n : Nat) : Mem :=
  match c.k.ptr a with
  | none => (m.alloc .u32 (reallocCells #[] n)).2
  | some (b, _) => ((m.free b).alloc .u32 (reallocCells (c.arr a) n)).2

section
variable {P : Prog} {W : World} {m : Mem} {sb : Nat} {c : CMem}

theorem Holds.sb_lt (h : Holds W m sb c) : sb < m.blocks.size := Mem.block?_lt h.ck

/-- No auxiliary block lies past the end of memory. -/
theorem Holds.aux_ge (h : Holds W m sb c) {b : Nat} (hb : m.blocks.size ≤ b) : W.aux b = none := by
  have := h.sb_lt; have := h.sbNew
  rw [← h.exact b (by omega) (by omega) (fun a o hp => by
    have := Mem.block?_lt (h.arr a b o hp).2.2.2; omega)]
  unfold Mem.block?; rw [Array.getElem?_eq_none hb]

/-- An owned array is not an auxiliary block. -/
theorem Holds.aux_owned (h : Holds W m sb c) {a : Arr} {b o : Nat} (hp : c.k.ptr a = some (b, o)) :
    W.aux b = none := by
  cases e : W.aux b with
  | none => rfl
  | some _ => exact absurd hp ((h.auxNew b (by rw [e]; simp)).2.2 a o)

/-- The response selected for this particular reallocation call. -/
def reallocResponse {P : Prog} (ptr : Ptr)
    {n : BitVec 64} (_hn : n ≠ 0) (st : KernelState P State) :
    Option Val × KernelState P State :=
  Ext.answer P (.kvrealloc .u32) [ptr.val, .u64 n] st

/-- `kvrealloc` on an owned array obeys its contract for every compatible oracle. -/
theorem Holds.realloc_run {st : KernelState P State}
    (h : Holds W st.mem sb c) (a : Arr) {n : BitVec 64} (hn : n ≠ 0#64) :
    Ext.run P (.kvrealloc .u32) [(c.k.ptr a).val, .u64 n] st =
      if (reallocResponse (P := P) (c.k.ptr a) hn st).1 ≠ some .null then
        some (some (.ptr st.mem.blocks.size 0),
          ⟨growMem st.mem c a n.toNat, (reallocResponse (P := P) (c.k.ptr a) hn st).2.oracle⟩)
      else some (some .null, ⟨st.mem, (reallocResponse (P := P) (c.k.ptr a) hn st).2.oracle⟩) := by
  have hd : Kernel.Defined P ⟨.kvrealloc .u32, [(c.k.ptr a).val, .u64 n], st.mem⟩ := by
    cases hp : c.k.ptr a with
    | none => exact ⟨hn, rfl, trivial⟩
    | some bo =>
      obtain ⟨b, o⟩ := bo
      obtain ⟨rfl, _, _, harr⟩ := h.arr a b o hp
      exact ⟨hn, rfl, rfl, _, harr, rfl⟩
  rw [Ext.run_answer hd]
  have ha := Ext.answer_spec hd
  have hc : ((Ext.answer P (.kvrealloc .u32) [(c.k.ptr a).val, .u64 n] st).1 = some .null ∧
      (Ext.answer P (.kvrealloc .u32) [(c.k.ptr a).val, .u64 n] st).2.mem = st.mem) ∨
    ((Ext.answer P (.kvrealloc .u32) [(c.k.ptr a).val, .u64 n] st).1 = some (.ptr st.mem.blocks.size 0) ∧
      (Ext.answer P (.kvrealloc .u32) [(c.k.ptr a).val, .u64 n] st).2.mem = growMem st.mem c a n.toNat) := by
    cases hp : c.k.ptr a with
    | none =>
      simp only [hp, Ptr.val] at ha ⊢
      simpa [growMem, hp, reallocCells] using ha.kvrealloc_null
    | some bo =>
      obtain ⟨b, o⟩ := bo
      obtain ⟨rfl, _, _, harr⟩ := h.arr a b o hp
      simp only [hp, Ptr.val] at ha ⊢
      obtain ⟨blk, hb, hc⟩ := ha.kvrealloc_ptr
      have heq : blk = ⟨.u32, c.arr a⟩ := Option.some.inj (hb.symm.trans harr)
      subst blk
      simpa only [growMem, hp] using hc
  change _ = if (Ext.answer P (.kvrealloc .u32) [(c.k.ptr a).val, .u64 n] st).1 ≠ some .null then _ else _
  generalize he : Ext.answer P (.kvrealloc .u32) [(c.k.ptr a).val, .u64 n] st = reply at *
  rcases reply with ⟨rv, ⟨mem, world⟩⟩
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [reallocResponse, he]

/-- In the memory after a successful `kvrealloc`, the new block is a live
`u32` array and the struct is unchanged. -/
theorem Holds.grow_blocks (h : Holds W m sb c) (a : Arr) (n : Nat) :
    (growMem m c a n).block? m.blocks.size = some ⟨.u32, reallocCells (c.old a) n⟩ ∧
    HasCK (growMem m c a n) sb c.k := by
  have hsb := h.sb_lt
  unfold growMem CMem.old
  cases hp : c.k.ptr a with
  | none =>
    refine ⟨by rw [Mem.block?_alloc]; simp, ?_⟩
    show (m.alloc _ _).2.block? sb = _
    rw [Mem.block?_alloc]; simp [Nat.ne_of_lt hsb]; exact h.ck
  | some bo =>
    obtain ⟨b, o⟩ := bo
    obtain ⟨rfl, hbs, _, harr⟩ := h.arr a b o hp
    refine ⟨by rw [Mem.block?_alloc]; simp, ?_⟩
    show ((m.free b).alloc _ _).2.block? sb = _
    rw [Mem.block?_alloc, Mem.block?_free]
    simp [Nat.ne_of_lt hsb, Ne.symm hbs]; exact h.ck

/-- Storing the new pointer re-establishes `Holds`. -/
theorem Holds.grow (hs : P.findStruct "ck" = some ckS) (h : Holds W m sb c) (a : Arr) (n : Nat) :
    let m1 := growMem m c a n
    let v := Val.ptr m.blocks.size 0
    m1.storeField P sb a.field.1 v = some (m1.setCell sb a.field.2 v) ∧
    Holds W (m1.setCell sb a.field.2 v) sb
      ({ c with k := c.k.setPtr a (some (m.blocks.size, 0)) }.setArr a (reallocCells (c.old a) n)) := by
  intro m1 v
  obtain ⟨hnew, hck⟩ := h.grow_blocks a n
  have hsb := h.sb_lt
  have hstore : m1.storeField P sb a.field.1 v = some (m1.setCell sb a.field.2 v) :=
    Mem.storeField_eq (by rw [ck_slot hs hck, a.field_slot]) (Mem.hasTy_ptr hnew rfl)
      (by cases a <;> simp [Arr.field, CK.cells])
  refine ⟨hstore, ?_⟩
  -- blocks of the final memory
  have hb : ∀ b', (m1.setCell sb a.field.2 v).block? b' =
      if b' = sb then some ⟨.struct "ck", c.k.cells.setIfInBounds a.field.2 v⟩
      else m1.block? b' := fun b' => by
    rw [Mem.block?_setCell b' hck]
  have hm1 : ∀ b', b' ≠ m.blocks.size → (∀ o, c.k.ptr a ≠ some (b', o)) →
      m1.block? b' = m.block? b' := by
    intro b' hne hno
    show (growMem m c a n).block? b' = _
    unfold growMem
    cases hp : c.k.ptr a with
    | none => simp only []; rw [Mem.block?_alloc]; simp [hne]
    | some bo =>
      obtain ⟨b, o⟩ := bo
      simp only []
      rw [Mem.block?_alloc, Mem.block?_free]
      have : b' ≠ b := fun e => hno o (by rw [hp, e])
      simp [hne, this]
  have hfreed : ∀ b o, c.k.ptr a = some (b, o) → m1.block? b = none := by
    intro b o hp
    show (growMem m c a n).block? b = _
    unfold growMem
    rw [hp]; simp only []
    have hlt := Mem.block?_lt (h.arr a b o hp).2.2.2
    rw [Mem.block?_alloc, Mem.block?_free]; simp [Nat.ne_of_lt hlt]
  have hptr : ∀ a', ({ c with k := c.k.setPtr a (some (m.blocks.size, 0)) }.setArr a
      (reallocCells (c.old a) n)).k.ptr a' = if a' = a then some (m.blocks.size, 0) else c.k.ptr a' := by
    intro a'
    have : ({ c with k := c.k.setPtr a (some (m.blocks.size, 0)) }.setArr a
        (reallocCells (c.old a) n)).k = c.k.setPtr a (some (m.blocks.size, 0)) := by
      cases a <;> rfl
    rw [this, CK.setPtr_ptr]
  have hbase : W.base.blocks.size ≤ m.blocks.size := by have := h.sbNew; omega
  have howned_lt : ∀ a' b o, c.k.ptr a' = some (b, o) → b < m.blocks.size :=
    fun a' b o hp => Mem.block?_lt (h.arr a' b o hp).2.2.2
  refine ⟨?_, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (m1.setCell sb a.field.2 v).block? sb = _
    rw [hb]; simp only [↓reduceIte]
    have : ({ c with k := c.k.setPtr a (some (m.blocks.size, 0)) }.setArr a
        (reallocCells (c.old a) n)).k = c.k.setPtr a (some (m.blocks.size, 0)) := by
      cases a <;> rfl
    rw [this, CK.setPtr_cells]; rfl
  · show (m1.setCell sb a.field.2 v).block? W.pb = _
    rw [hb]; simp only [h.pb_ne_sb, ↓reduceIte]
    rw [hm1 W.pb (by have := h.pbOld; omega)
      (fun o hp => by have := (h.arr a W.pb o hp).2.2.1; have := h.pbOld; omega)]
    cases a <;> exact h.proof
  · cases a <;> exact h.proofPtr
  · cases a <;> exact h.parPtr
  · intro a' b o hpa
    rw [hptr] at hpa
    by_cases haa : a' = a
    · subst haa
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpa
      obtain ⟨rfl, rfl⟩ := hpa
      refine ⟨rfl, by omega, hbase, ?_⟩
      show (m1.setCell sb a'.field.2 v).block? m.blocks.size = _
      rw [hb]; simp only [Nat.ne_of_gt hsb, ↓reduceIte]
      rw [hnew]; cases a' <;> rfl
    · simp only [haa, ↓reduceIte] at hpa
      obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a' b o hpa
      refine ⟨ho, hbs, hbb, ?_⟩
      show (m1.setCell sb a.field.2 v).block? b = _
      rw [hb]; simp only [hbs, ↓reduceIte]
      rw [hm1 b (Nat.ne_of_lt (howned_lt a' b o hpa))
        (fun o' hp => h.sep a' a b b o o' haa hpa hp rfl)]
      cases a <;> cases a' <;> first | exact absurd rfl haa | exact harr
  · intro a1 a2 b1 b2 o1 o2 hne h1 h2
    rw [hptr] at h1 h2
    by_cases e1 : a1 = a
    · subst e1
      have e2 : a2 ≠ a1 := fun e => hne e.symm
      simp only [↓reduceIte, e2, Option.some.injEq, Prod.mk.injEq] at h1 h2
      have := howned_lt a2 b2 o2 h2
      omega
    · by_cases e2 : a2 = a
      · subst e2
        simp only [↓reduceIte, e1, Option.some.injEq, Prod.mk.injEq] at h1 h2
        have := howned_lt a1 b1 o1 h1
        omega
      · simp only [e1, e2, ↓reduceIte] at h1 h2
        exact h.sep a1 a2 b1 b2 o1 o2 hne h1 h2
  · intro b hlt hne
    rw [hb]
    have h1 : b ≠ sb := by have := h.sbNew; omega
    simp only [h1, ↓reduceIte]
    rw [hm1 b (by omega) (fun o hp => by have := (h.arr a b o hp).2.2.1; omega)]
    exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]; simp only [hne, ↓reduceIte]
    have hbn : b ≠ m.blocks.size := fun e => hno a 0 (by rw [hptr, e]; simp)
    by_cases hold : ∃ o, c.k.ptr a = some (b, o)
    · obtain ⟨o, hp⟩ := hold
      rw [hfreed b o hp, h.aux_owned hp]
    · rw [hm1 b hbn (fun o hp => hold ⟨o, hp⟩)]
      refine h.exact b hge hne (fun a' o hp => ?_)
      by_cases haa : a' = a
      · subst haa; exact hold ⟨o, hp⟩
      · exact hno a' o (by rw [hptr]; simp [haa, hp])
  · intro b hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b hb'
    refine ⟨h1, h2, fun a' o => ?_⟩
    rw [hptr]
    by_cases haa : a' = a
    · simp only [haa, ↓reduceIte, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
      intro e; subst e; exact absurd (h.aux_ge (Nat.le_refl _)) hb'
    · simp only [haa, ↓reduceIte]; exact h3 a' o

end

end Vbcf.Proof
