import EmbC.Kernel
import Vbcf.Prog
import EmbC.Cost
import Vbcf.Proof.Core1

/-!
# Vbcf cost proofs: what a cost proof tracks

A cost proof (`FnCost`, `EmbC/Cost.lean`) may get stuck wherever it likes,
because the partial-correctness proofs already rule that out.  So it needs
none of the representation invariants (`Holds`, `CoreInv`, `RCtx`): only the
few fields of the checker state that bound loops, above all the work counter.

`Fld m sb i v`: cell `i` of the `struct ck` in block `sb` holds `v`.  It
survives every store to another block or another field, every allocation,
and every `kvfree` of another block (`Fld.storeArr`, `Fld.storeField`,
`Fld.ext`).  `wk m sb` is the work counter read from memory, the potential
of the cost bounds.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

/-! ## Struct cells -/

/-- Cell `i` of the struct in block `sb` holds `v`. -/
def Fld (m : Mem) (sb i : Nat) (v : Val) : Prop :=
  ∃ cells, m.block? sb = some ⟨.struct "ck", cells⟩ ∧ cells[i]? = some v

/-- The cells of the fields appended for reclamation (`Mem.lean` lists the first 23). -/
theorem cfi_lr : fieldIn ckS.fields "lr" = some (23, .ptr .u32) := by simp [ckS, fieldIn]
theorem cfi_lo : fieldIn ckS.fields "lo" = some (24, .u32) := by simp [ckS, fieldIn]
theorem cfi_live : fieldIn ckS.fields "live" = some (25, .u32) := by simp [ckS, fieldIn]

/-- The cell index of the work counter. -/
abbrev iWork : Nat := 20

/-- The work counter of the struct in block `sb` (0 if there is none). -/
def wk (m : Mem) (sb : Nat) : Nat :=
  match m.block? sb with
  | some blk => match blk.cells[iWork]? with
    | some (.u32 w) => w.toNat
    | _ => 0
  | none => 0

theorem Fld.wk {m : Mem} {sb : Nat} {w : BitVec 32} (h : Fld m sb iWork (.u32 w)) :
    wk m sb = w.toNat := by
  obtain ⟨cells, hb, hc⟩ := h
  simp [Vbcf.Proof.wk, hb, hc]

theorem HasCK.fld {m : Mem} {sb : Nat} {k : CK} (h : HasCK m sb k) (i : Nat) (v : Val)
    (hv : k.cells[i]? = some v) : Fld m sb i v :=
  ⟨_, h, hv⟩

theorem Holds.fld_work {W : World} {m : Mem} {sb : Nat} {c : CMem} (h : Holds W m sb c) :
    Fld m sb iWork (.u32 c.k.work) :=
  h.ck.fld _ _ (by simp [CK.cells])

theorem fieldIn_get : ∀ (l : List (String × Ty)) (f : String) (i : Nat) (t : Ty),
    fieldIn l f = some (i, t) → l[i]? = some (f, t)
  | [], f, i, t, h => by simp [fieldIn] at h
  | (g, u) :: rest, f, i, t, h => by
    unfold fieldIn at h
    by_cases hg : g = f
    · simp only [hg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hg]
    · simp only [hg, ↓reduceIte] at h
      cases hr : fieldIn rest f with
      | none => rw [hr] at h; simp at h
      | some p =>
        obtain ⟨j, t'⟩ := p
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa using fieldIn_get rest f j t' hr

/-- The field at a given cell index. -/
theorem fieldIn_idx {f : String} {i : Nat} {t : Ty} (h : fieldIn ckS.fields f = some (i, t)) :
    ckS.fields[i]? = some (f, t) := fieldIn_get _ _ _ _ h

theorem Mem.block?_setCell_ne {m : Mem} {b b' j : Nat} {x : Val} (hne : b ≠ b') :
    (m.setCell b j x).block? b' = m.block? b' := by
  unfold Mem.setCell Mem.block?
  simp [Array.getElem?_modify, hne]

theorem Fld.setCell_other {m : Mem} {sb i : Nat} {v : Val} {b j : Nat} {x : Val}
    (h : Fld m sb i v) (hne : b ≠ sb ∨ j ≠ i) : Fld (m.setCell b j x) sb i v := by
  obtain ⟨cells, hb, hc⟩ := h
  by_cases hbs : b = sb
  · subst hbs
    have hj : j ≠ i := by rcases hne with h | h; exact absurd rfl h; exact h
    refine ⟨cells.setIfInBounds j x, ?_, ?_⟩
    · rw [Mem.block?_setCell b hb]; simp
    · rw [Array.getElem?_setIfInBounds]; simp [hj, hc]
  · exact ⟨cells, by rw [Mem.block?_setCell_ne hbs]; exact hb, hc⟩

theorem Fld.setCell_same {m : Mem} {sb i : Nat} {v x : Val} (h : Fld m sb i v) :
    Fld (m.setCell sb i x) sb i x := by
  obtain ⟨cells, hb, hc⟩ := h
  have hi : i < cells.size := by
    rcases Nat.lt_or_ge i cells.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hc; simp at hc
  refine ⟨cells.setIfInBounds i x, ?_, ?_⟩
  · rw [Mem.block?_setCell sb hb]; simp
  · simp [hi]

/-- A store to an array never touches the struct. -/
theorem Fld.storeArr {m m' : Mem} {sb i : Nat} {v : Val} {b j : Nat} {x : Val}
    (h : Fld m sb i v) (hs : m.storeArr b j x = some m') : Fld m' sb i v := by
  unfold Mem.storeArr at hs
  obtain ⟨cells, hb, hc⟩ := h
  cases hblk : m.block? b with
  | none => rw [hblk] at hs; simp at hs
  | some blk =>
    rw [hblk] at hs
    simp only [] at hs
    split at hs
    · simp at hs
    · rename_i hns
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        refine Fld.setCell_other ⟨cells, hb, hc⟩ (Or.inl ?_)
        intro e; subst e
        rw [hb] at hblk; simp only [Option.some.injEq] at hblk; subst hblk
        simp [Ty.isStruct] at hns
      · simp at hs

/-- A store to another field (or another struct) keeps cell `i`. -/
theorem Fld.storeField {m m' : Mem} {sb i : Nat} {v : Val} {b : Nat} {f : String} {x : Val}
    (h : Fld m sb i v) (hs : m.storeField Vbcf.prog b f x = some m')
    (hf : ∀ t, fieldIn ckS.fields f ≠ some (i, t)) : Fld m' sb i v := by
  unfold Mem.storeField at hs
  cases hslot : m.fieldSlot Vbcf.prog b f with
  | none => rw [hslot] at hs; simp at hs
  | some r =>
    obtain ⟨blk, j, t⟩ := r
    rw [hslot] at hs
    simp only [] at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      by_cases hbs : b = sb
      · subst hbs
        obtain ⟨cells, hb, hc⟩ := h
        refine Fld.setCell_other ⟨cells, hb, hc⟩ (Or.inr ?_)
        intro e; subst e
        unfold Mem.fieldSlot at hslot
        rw [hb] at hslot
        simp only [prog_ck, StructDef.field?] at hslot
        cases hfi : fieldIn ckS.fields f with
        | none => rw [hfi] at hslot; simp at hslot
        | some p =>
          rw [hfi] at hslot
          simp only [Option.some.injEq, Prod.mk.injEq] at hslot
          obtain ⟨-, rfl, rfl⟩ := hslot
          exact hf _ hfi
      · exact h.setCell_other (Or.inl hbs)
    · simp at hs

/-- A store to the field at cell `i` itself. -/
theorem Fld.storeField_same {m m' : Mem} {sb i : Nat} {v : Val} {f : String} {t : Ty} {x : Val}
    (h : Fld m sb i v) (hs : m.storeField Vbcf.prog sb f x = some m')
    (hf : fieldIn ckS.fields f = some (i, t)) : Fld m' sb i x := by
  unfold Mem.storeField at hs
  obtain ⟨cells, hb, hc⟩ := h
  have hslot : m.fieldSlot Vbcf.prog sb f = some (⟨.struct "ck", cells⟩, i, t) := by
    unfold Mem.fieldSlot; rw [hb]; simp [prog_ck, StructDef.field?, hf]
  rw [hslot] at hs
  simp only [] at hs
  split at hs
  · simp only [Option.some.injEq] at hs
    subst hs
    exact Fld.setCell_same ⟨cells, hb, hc⟩
  · simp at hs

/-- Reading a field whose cell is known. -/
theorem Fld.load {m : Mem} {sb i : Nat} {v : Val} {f : String} {t : Ty} (h : Fld m sb i v)
    (hf : fieldIn ckS.fields f = some (i, t)) (hv : v ≠ .undef) :
    m.loadField Vbcf.prog sb f = some v := by
  obtain ⟨cells, hb, hc⟩ := h
  apply Mem.loadField_eq (blk := ⟨.struct "ck", cells⟩) (i := i) (t := t) _ hc hv
  unfold Mem.fieldSlot; rw [hb]; simp [prog_ck, StructDef.field?, hf]

theorem Fld.ld_work {m : Mem} {sb : Nat} {w : BitVec 32} (h : Fld m sb iWork (.u32 w)) :
    m.loadField Vbcf.prog sb "work" = some (.u32 w) := h.load fi_work (by simp)

theorem Fld.alloc {m : Mem} {sb i : Nat} {v : Val} {t : Ty} {cells : Array Val}
    (h : Fld m sb i v) : Fld (m.alloc t cells).2 sb i v := by
  obtain ⟨cs, hb, hc⟩ := h
  refine ⟨cs, ?_, hc⟩
  rw [Mem.block?_alloc]
  have := Mem.block?_lt hb
  simp [show sb ≠ m.blocks.size by omega, hb]

theorem Fld.free {m : Mem} {sb i : Nat} {v : Val} {b : Nat} (h : Fld m sb i v) (hne : b ≠ sb) :
    Fld (m.free b) sb i v := by
  obtain ⟨cs, hb, hc⟩ := h
  exact ⟨cs, by rw [Mem.block?_free]; simp [Ne.symm hne, hb], hc⟩

/-- `fill` writes a `u32` block, never the struct. -/
theorem Fld.fill {m : Mem} {sb i : Nat} {v : Val} {b off : Nat} {vs : List Val} (h : Fld m sb i v)
    (hb : ∃ cells, m.block? b = some ⟨.u32, cells⟩) : Fld (m.fill b off vs) sb i v := by
  obtain ⟨cs, hsb, hc⟩ := h
  obtain ⟨cells, hbb⟩ := hb
  have hne : b ≠ sb := by intro e; subst e; rw [hbb] at hsb; simp at hsb
  refine ⟨cs, ?_, hc⟩
  unfold Mem.fill Mem.block?
  simp only [Array.getElem?_modify]
  rw [ite_eq_right hne]
  exact hsb

/-- Every kernel call keeps the struct, except a `kvfree` of the struct itself. -/
theorem Fld.ext {P : Prog} {st st' : (KernelState P State)} {sb i : Nat} {v : Val} {f : Ext} {vs : List Val}
    {rv : Option Val} (h : Fld st.mem sb i v) (hr : Ext.run P f vs st = some (rv, st'))
    (hfree : ∀ b, vs = [.ptr b 0] → f = .kvfree → b ≠ sb) : Fld st'.mem sb i v := by
  have ha := Ext.run_spec hr
  have hd := ha.defined
  unfold Kernel.Defined at hd
  split at hd
  all_goals subst_vars
  all_goals try contradiction
  · rcases ha.kvcalloc with hfail | hsuccess
    · rw [hfail.2]
      exact h
    · rw [hsuccess.2]
      exact h.alloc
  · obtain ⟨d, _, ha⟩ := ha.kzalloc
    rcases ha with hfail | hsuccess
    · rw [hfail.2]
      exact h
    · rw [hsuccess.2]
      exact h.alloc
  · split at hd
    all_goals subst_vars
    all_goals try simp at hd
    all_goals try contradiction
    · rcases ha.kvrealloc_null with hfail | hsuccess
      · rw [hfail.2]
        exact h
      · rw [hsuccess.2]
        exact h.alloc
    · rename_i b off
      obtain ⟨blk, hb, ha⟩ := ha.kvrealloc_ptr
      obtain ⟨_, ht, _, old, hbold, he⟩ := hd
      have heq : old = blk := Option.some.inj (hbold.symm.trans hb)
      subst old
      have hns : blk.elem.isStruct = false := by rw [he]; exact ht
      have hne : b ≠ sb := by
        intro e
        subst b
        obtain ⟨cs, hsb, _⟩ := h
        rw [hsb] at hb
        cases hb
        simp [Ty.isStruct] at hns
      rcases ha with hfail | hsuccess
      · rw [hfail.2]
        exact h
      · rw [hsuccess.2]
        exact (h.free hne).alloc
  · split at hd
    all_goals subst_vars
    all_goals try simp at hd
    all_goals try contradiction
    · rw [ha.kvfree_null.2]
      exact h
    · rename_i b off
      obtain ⟨hoff, _⟩ := hd
      subst off
      rw [ha.kvfree_ptr.2]
      exact h.free (hfree b rfl rfl)
  · rename_i b off n
    obtain ⟨blk, hb, he, _⟩ := hd
    have hblock : ∃ cells, st.mem.block? b = some ⟨.u32, cells⟩ :=
      ⟨blk.cells, by rw [hb, ← he]⟩
    rcases ha.copyFromBpfptr with hfail | ⟨words, _, _, hsuccess⟩
    · rw [hfail.2]
      exact h.fill hblock
    · rw [hsuccess]
      exact h.fill hblock
  · rw [ha.signalPending.2]
    exact h
  · rw [ha.condResched.2]
    exact h

/-! ## The two budget cells -/

/-- The cell index of the memory budget. -/
abbrev iMem : Nat := 22

/-- The memory budget of the struct in block `sb` (0 if there is none). -/
def mk (m : Mem) (sb : Nat) : Nat :=
  match m.block? sb with
  | some blk => match blk.cells[iMem]? with
    | some (.u32 w) => w.toNat
    | _ => 0
  | none => 0

theorem Fld.mk {m : Mem} {sb : Nat} {w : BitVec 32} (h : Fld m sb iMem (.u32 w)) :
    mk m sb = w.toNat := by
  obtain ⟨cells, hb, hc⟩ := h
  simp [Vbcf.Proof.mk, hb, hc]

theorem Fld.ld_mem {m : Mem} {sb : Nat} {w : BitVec 32} (h : Fld m sb iMem (.u32 w)) :
    m.loadField Vbcf.prog sb "mem" = some (.u32 w) := h.load fi_mem (by simp)

theorem Fld.hasTy {m : Mem} {sb i : Nat} {v : Val} (h : Fld m sb i v) :
    m.hasTy (.ptr sb 0) (.ptr (.struct "ck")) = true := by
  obtain ⟨cells, hb, -⟩ := h
  exact Mem.hasTy_ptr hb rfl

/-- A field other than `f` is not at `f`'s cell. -/
theorem fieldIn_ne_of_ne {f g : String} {i : Nat} {t : Ty} (hg : fieldIn ckS.fields g = some (i, t))
    (hne : f ≠ g) (t' : Ty) : fieldIn ckS.fields f ≠ some (i, t') := by
  intro hf
  have h1 := fieldIn_idx hf
  have h2 := fieldIn_idx hg
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact hne h2.1

/-- The struct in block `sb` has work budget `w` and memory budget `mm`. -/
def Budget (m : Mem) (sb : Nat) (w mm : BitVec 32) : Prop :=
  Fld m sb iWork (.u32 w) ∧ Fld m sb iMem (.u32 mm)

namespace Budget
variable {m m' : Mem} {sb : Nat} {w mm : BitVec 32}

theorem work (h : Budget m sb w mm) : Fld m sb iWork (.u32 w) := h.1
theorem mem (h : Budget m sb w mm) : Fld m sb iMem (.u32 mm) := h.2
theorem wk (h : Budget m sb w mm) : Vbcf.Proof.wk m sb = w.toNat := h.1.wk
theorem mk (h : Budget m sb w mm) : Vbcf.Proof.mk m sb = mm.toNat := h.2.mk
theorem hasTy (h : Budget m sb w mm) : m.hasTy (.ptr sb 0) (.ptr (.struct "ck")) = true := h.1.hasTy
theorem ld_work (h : Budget m sb w mm) : m.loadField Vbcf.prog sb "work" = some (.u32 w) := h.1.ld_work
theorem ld_mem (h : Budget m sb w mm) : m.loadField Vbcf.prog sb "mem" = some (.u32 mm) := h.2.ld_mem

theorem storeArr {b j : Nat} {x : Val} (h : Budget m sb w mm) (hs : m.storeArr b j x = some m') :
    Budget m' sb w mm := ⟨h.1.storeArr hs, h.2.storeArr hs⟩

/-- A store to a field other than `work` and `mem`. -/
theorem storeField {b : Nat} {f : String} {x : Val} (h : Budget m sb w mm)
    (hs : m.storeField Vbcf.prog b f x = some m') (h1 : f ≠ "work") (h2 : f ≠ "mem") :
    Budget m' sb w mm :=
  ⟨h.1.storeField hs (fieldIn_ne_of_ne fi_work h1), h.2.storeField hs (fieldIn_ne_of_ne fi_mem h2)⟩

theorem setWork {x : BitVec 32} (h : Budget m sb w mm)
    (hs : m.storeField Vbcf.prog sb "work" (.u32 x) = some m') : Budget m' sb x mm :=
  ⟨h.1.storeField_same hs fi_work, h.2.storeField hs (fieldIn_ne_of_ne fi_mem (by decide))⟩

theorem setMem {x : BitVec 32} (h : Budget m sb w mm)
    (hs : m.storeField Vbcf.prog sb "mem" (.u32 x) = some m') : Budget m' sb w x :=
  ⟨h.1.storeField hs (fieldIn_ne_of_ne fi_work (by decide)), h.2.storeField_same hs fi_mem⟩

theorem ext {P : Prog} {st st' : (KernelState P State)} {f : Ext} {vs : List Val} {rv : Option Val}
    (h : Budget st.mem sb w mm) (hr : Ext.run P f vs st = some (rv, st'))
    (hfree : ∀ b, vs = [.ptr b 0] → f = .kvfree → b ≠ sb) : Budget st'.mem sb w mm :=
  ⟨h.1.ext hr hfree, h.2.ext hr hfree⟩

end Budget

theorem Holds.budget {W : World} {m : Mem} {sb : Nat} {c : CMem} (h : Holds W m sb c) :
    Budget m sb c.k.work c.k.mem :=
  ⟨h.ck.fld _ _ (by simp [CK.cells]), h.ck.fld _ _ (by simp [CK.cells])⟩

/-! ## Statements that keep a struct cell -/

section
variable {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb i : Nat} {v : Val}

/-- Any array store keeps the struct. -/
theorem WPC.store_fld {p j e : Expr} (hfld : Fld st.mem sb i v)
    (h : ∀ m', Fld m' sb i v → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.store p j e) Q env st := by
  apply WPC.store
  split
  · split
    · trivial
    · split
      · trivial
      · rename_i m' hs; exact h m' (hfld.storeArr hs)
  · trivial

/-- A store to another field keeps cell `i`. -/
theorem WPC.setField_fld {p e : Expr} {f : String} (hfld : Fld st.mem sb i v)
    (hf : ∀ t, fieldIn ckS.fields f ≠ some (i, t))
    (h : ∀ m', Fld m' sb i v → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.setField p f e) Q env st := by
  apply WPC.setField
  split
  · intro _
    split
    · trivial
    · rename_i m' hs; exact h m' (hfld.storeField hs hf)
  · trivial

/-- A kernel call other than freeing the struct keeps it.  Its cost depends on
the evaluated arguments. -/
theorem WPC.ecall_fld {dst : Option Var} {f : Ext} {args : List Expr} (hfld : Fld st.mem sb i v)
    (h : ∀ vs, evalArgs Vbcf.prog env st.mem args = some vs →
      (∀ b, vs = [.ptr b 0] → f = .kvfree → b ≠ sb) ∧
      ∀ rv st', Fld st'.mem sb i v →
        match assignDst env st'.mem dst rv with
        | none => True
        | some env' => Q .normal env' st' (Ext.costC Vbcf.prog f vs + 3)) :
    WPC Vbcf.prog (.ecall dst f args) Q env st := by
  apply WPC.ecall
  cases hv : evalArgs Vbcf.prog env st.mem args with
  | none => trivial
  | some vs =>
    obtain ⟨hfree, h⟩ := h vs hv
    simp only []
    cases hr : Ext.run Vbcf.prog f vs st with
    | none => trivial
    | some r =>
      obtain ⟨rv, st'⟩ := r
      exact h rv st' (hfld.ext hr hfree)

end

/-! ## Statements that keep the budget -/

section
variable {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm : BitVec 32}

/-- Any array store keeps the budget. -/
theorem WPC.store_bud {p j e : Expr} (hb : Budget st.mem sb w mm)
    (h : ∀ m', Budget m' sb w mm → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.store p j e) Q env st := by
  apply WPC.store
  split
  · split
    · trivial
    · split
      · trivial
      · rename_i m' hs; exact h m' (hb.storeArr hs)
  · trivial

/-- A store to a field other than `work` and `mem` keeps the budget. -/
theorem WPC.setField_bud {p e : Expr} {f : String} (hb : Budget st.mem sb w mm)
    (h1 : f ≠ "work") (h2 : f ≠ "mem")
    (h : ∀ m', Budget m' sb w mm → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.setField p f e) Q env st := by
  apply WPC.setField
  split
  · intro _
    split
    · trivial
    · rename_i m' hs; exact h m' (hb.storeField hs h1 h2)
  · trivial

/-- `st->work = e;` where `e` evaluates to `x`. -/
theorem WPC.setWork {p e : Expr} {x : BitVec 32} (hb : Budget st.mem sb w mm)
    (hp : evalE Vbcf.prog env st.mem p = some (.ptr sb 0))
    (he : evalE Vbcf.prog env st.mem e = some (.u32 x))
    (h : ∀ m', Budget m' sb x mm → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.setField p "work" e) Q env st := by
  apply WPC.setField
  rw [hp, he]
  intro _
  cases hs : st.mem.storeField Vbcf.prog sb "work" (.u32 x) with
  | none => trivial
  | some m' => exact h m' (hb.setWork hs)

/-- `st->mem = e;` where `e` evaluates to `x`. -/
theorem WPC.setMem {p e : Expr} {x : BitVec 32} (hb : Budget st.mem sb w mm)
    (hp : evalE Vbcf.prog env st.mem p = some (.ptr sb 0))
    (he : evalE Vbcf.prog env st.mem e = some (.u32 x))
    (h : ∀ m', Budget m' sb w x → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.setField p "mem" e) Q env st := by
  apply WPC.setField
  rw [hp, he]
  intro _
  cases hs : st.mem.storeField Vbcf.prog sb "mem" (.u32 x) with
  | none => trivial
  | some m' => exact h m' (hb.setMem hs)

/-- A kernel call other than freeing the struct keeps the budget.  Its cost
depends on the evaluated arguments. -/
theorem WPC.ecall_bud {dst : Option Var} {f : Ext} {args : List Expr} (hb : Budget st.mem sb w mm)
    (h : ∀ vs, evalArgs Vbcf.prog env st.mem args = some vs →
      (∀ b, vs = [.ptr b 0] → f = .kvfree → b ≠ sb) ∧
      ∀ rv st', Budget st'.mem sb w mm →
        match assignDst env st'.mem dst rv with
        | none => True
        | some env' => Q .normal env' st' (Ext.costC Vbcf.prog f vs + 3)) :
    WPC Vbcf.prog (.ecall dst f args) Q env st := by
  apply WPC.ecall
  cases hv : evalArgs Vbcf.prog env st.mem args with
  | none => trivial
  | some vs =>
    obtain ⟨hfree, h⟩ := h vs hv
    simp only []
    cases hr : Ext.run Vbcf.prog f vs st with
    | none => trivial
    | some r =>
      obtain ⟨rv, st'⟩ := r
      exact h rv st' (hb.ext hr hfree)

end

end Vbcf.Proof
