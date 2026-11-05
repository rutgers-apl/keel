import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCompact
import EmbC.Semantics.Correctness

/-!
# Vbcf cost proofs: the `live` cell holds a `u32`

`ck_run`'s trigger for `ck_compact` reads `(u64)st->live`.  A cost proof
knows nothing of the struct's cells beyond the budget, and a `u64` in that
cell would make the trigger (computed in `u64`) say nothing about the pool.
But no run can put one there: `kzalloc` zeroes the cell to a `u32`, a store
to a field checks the field's type, and every other memory operation leaves
struct blocks alone.  `TypedU32 m sb` says so of block `sb`, and
`source_next_typed`/`FnCost.typed` show every statement and every call keeps it (any
function of `prog`: it is a property of the semantics, not of the callee).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

/-- Every `u32` field of the struct in block `sb`, if there is one, holds a `u32` (or is unset). -/
def TypedU32 (m : Mem) (sb : Nat) : Prop :=
  ∀ cells, m.block? sb = some ⟨.struct "ck", cells⟩ → ∀ (i : Nat) (v : Val), (ckS.fields[i]?).map Prod.snd = some Ty.u32 →
    cells[i]? = some v → v = Val.undef ∨ ∃ x, v = Val.u32 x

theorem TypedU32.of_block {m m' : Mem} {sb : Nat}
    (h : ∀ cells, m'.block? sb = some ⟨.struct "ck", cells⟩ → m.block? sb = some ⟨.struct "ck", cells⟩)
    (hl : TypedU32 m sb) : TypedU32 m' sb := fun cells hb => hl cells (h cells hb)

theorem TypedU32.alloc {m : Mem} {sb : Nat} {t : Ty} {cells : Array Val} (hl : TypedU32 m sb)
    (ht : ∀ cs, (⟨t, cells⟩ : Block) = ⟨.struct "ck", cs⟩ → ∀ (i : Nat) (v : Val), (ckS.fields[i]?).map Prod.snd = some Ty.u32 →
      cs[i]? = some v → v = Val.undef ∨ ∃ x, v = Val.u32 x) :
    TypedU32 (m.alloc t cells).2 sb := by
  intro cs hb i v hi hv
  rw [Mem.block?_alloc] at hb
  split at hb
  · exact ht cs (Option.some.inj hb) i v hi hv
  · exact hl cs hb i v hi hv

theorem TypedU32.free {m : Mem} {sb b : Nat} (hl : TypedU32 m sb) : TypedU32 (m.free b) sb := by
  refine TypedU32.of_block (fun cells hb => ?_) hl
  rw [Mem.block?_free] at hb
  split at hb
  · simp at hb
  · exact hb

/-- A cell store into a block that is not a struct. -/
theorem TypedU32.setCell_arr {m : Mem} {sb b i : Nat} {v : Val} {blk : Block} (hl : TypedU32 m sb)
    (hb : m.block? b = some blk) (hs : blk.elem.isStruct = false) : TypedU32 (m.setCell b i v) sb := by
  refine TypedU32.of_block (fun cells h => ?_) hl
  rw [Mem.block?_setCell sb hb] at h
  split at h
  · simp only [Option.some.injEq, Block.mk.injEq] at h
    rw [h.1] at hs; simp [Ty.isStruct] at hs
  · exact h

theorem TypedU32.storeArr {m m' : Mem} {sb b j : Nat} {v : Val} (hl : TypedU32 m sb)
    (h : m.storeArr b j v = some m') : TypedU32 m' sb := by
  unfold Mem.storeArr at h
  cases hb : m.block? b with
  | none => rw [hb] at h; simp at h
  | some blk =>
    rw [hb] at h
    simp only [] at h
    split at h
    · simp at h
    · rename_i hns
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact hl.setCell_arr hb (by simpa using hns)
      · simp at h

theorem ck_field25 : ∀ t, fieldIn ckS.fields "live" = some (25, t) → t = .u32 := by
  intro t h; rw [cfi_live] at h; simp at h; exact h.symm

theorem TypedU32.storeField {m m' : Mem} {sb b : Nat} {f : String} {v : Val} (hl : TypedU32 m sb)
    (h : m.storeField Vbcf.prog b f v = some m') : TypedU32 m' sb := by
  unfold Mem.storeField at h
  cases hslot : m.fieldSlot Vbcf.prog b f with
  | none => rw [hslot] at h; simp at h
  | some r =>
    obtain ⟨blk, i, t⟩ := r
    rw [hslot] at h
    simp only [] at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      unfold Mem.fieldSlot at hslot
      cases hb : m.block? b with
      | none => rw [hb] at hslot; simp at hslot
      | some blk0 =>
        rw [hb] at hslot
        simp only [] at hslot
        intro cells hcs j v' hj hv'
        rw [Mem.block?_setCell sb hb] at hcs
        split at hcs
        · rename_i hsb
          subst hsb
          simp only [Option.some.injEq] at hcs
          -- the block is the struct: its field `f` is at cell `i` with type `t`
          split at hslot
          · rename_i s hs
            have hs' : s = "ck" := by
              have := congrArg Block.elem hcs; simp [hs] at this; exact this
            subst hs'
            simp only [prog_ck, StructDef.field?] at hslot
            split at hslot
            · simp at hslot
            · rename_i i' t' hfi
              simp only [Option.some.injEq, Prod.mk.injEq] at hslot
              obtain ⟨rfl, rfl, rfl⟩ := hslot
              have hcells := congrArg Block.cells hcs
              simp only at hcells
              rw [← hcells] at hv'
              rw [Array.getElem?_setIfInBounds] at hv'
              split at hv'
              · rename_i hij
                subst hij
                split at hv'
                · simp only [Option.some.injEq] at hv'
                  subst hv'
                  have ht := fieldIn_idx hfi
                  rw [ht] at hj
                  simp only [Option.map_some, Option.some.injEq] at hj
                  subst hj
                  obtain ⟨n, rfl⟩ := Mem.hasTy_u32_inv (by simpa using hok.1)
                  exact Or.inr ⟨n, rfl⟩
                · simp at hv'
              · refine hl _ ?_ j v' hj hv'
                rw [hb]; cases blk0; simp only at hs; simp [hs]
          · simp at hslot
        · exact hl cells hcs j v' hj hv'
    · simp at h

theorem ck_zeroU32 {i : Nat} (hi : (ckS.fields[i]?).map Prod.snd = some Ty.u32) :
    ckS.zeroCells[i]? = some (.u32 0) := by
  simp only [StructDef.zeroCells, List.getElem?_toArray, List.getElem?_map]
  cases h : ckS.fields[i]? with
  | none => rw [h] at hi; simp at hi
  | some p => rw [h] at hi; simp only [Option.map_some, Option.some.injEq] at hi; simp [hi, Ty.zero]

theorem TypedU32.ext {st st' : (KernelState prog State)} {sb : Nat} {f : Ext} {vs : List Val} {rv : Option Val}
    (hl : TypedU32 st.mem sb) (hr : Ext.run Vbcf.prog f vs st = some (rv, st')) : TypedU32 st'.mem sb := by
  have ha := Ext.run_spec hr
  have hd := ha.defined
  unfold Kernel.Defined at hd
  split at hd
  all_goals subst_vars
  all_goals try contradiction
  · rcases ha.kvcalloc with hfail | hsuccess
    · rw [hfail.2]
      exact hl
    · rw [hsuccess.2]
      refine hl.alloc (fun cs hblock => ?_)
      simp only [Block.mk.injEq] at hblock
      have ht := hd.2
      rw [hblock.1] at ht
      simp [Ty.isStruct] at ht
  · obtain ⟨d, hfind, ha⟩ := ha.kzalloc
    rcases ha with hfail | hsuccess
    · rw [hfail.2]
      exact hl
    · rw [hsuccess.2]
      refine hl.alloc (fun cs hblock i v hi hv => ?_)
      simp only [Block.mk.injEq, Ty.struct.injEq] at hblock
      obtain ⟨rfl, rfl⟩ := hblock
      rw [prog_ck] at hfind
      simp only [Option.some.injEq] at hfind
      subst d
      rw [ck_zeroU32 hi] at hv
      simp only [Option.some.injEq] at hv
      exact Or.inr ⟨0, hv.symm⟩
  · rename_i t p n
    have hst : ∀ cs (c : Array Val), (⟨t, c⟩ : Block) = ⟨.struct "ck", cs⟩ → False := by
      intro cs c hblock
      simp only [Block.mk.injEq] at hblock
      have ht := hd.2.1
      rw [hblock.1] at ht
      simp [Ty.isStruct] at ht
    split at hd
    all_goals subst_vars
    all_goals try simp at hd
    all_goals try contradiction
    · rcases ha.kvrealloc_null with hfail | hsuccess
      · rw [hfail.2]
        exact hl
      · rw [hsuccess.2]
        exact hl.alloc (fun cs hblock => (hst cs _ hblock).elim)
    · obtain ⟨blk, _, ha⟩ := ha.kvrealloc_ptr
      rcases ha with hfail | hsuccess
      · rw [hfail.2]
        exact hl
      · rw [hsuccess.2]
        exact hl.free.alloc (fun cs hblock => (hst cs _ hblock).elim)
  · split at hd
    all_goals subst_vars
    all_goals try simp at hd
    all_goals try contradiction
    · rw [ha.kvfree_null.2]
      exact hl
    · rw [ha.kvfree_ptr.2]
      exact hl.free
  · rename_i b off n
    obtain ⟨blk, hblk, he, _⟩ := hd
    have hfill : ∀ vs', TypedU32 (st.mem.fill b off vs') sb := by
      intro vs'
      refine TypedU32.of_block (fun cells h => ?_) hl
      unfold Mem.fill Mem.block? at h
      simp only [Array.getElem?_modify] at h
      by_cases hbs : b = sb
      · subst hbs
        rw [Mem.block?_eq] at hblk
        rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)] at h
        rw [hblk] at h
        simp only [Option.map_some, Option.some.injEq, Block.mk.injEq] at h
        rw [he] at h
        simp at h
      · simp only [hbs, ↓reduceIte] at h
        exact h
    rcases ha.copyFromBpfptr with hfail | ⟨words, _, _, hsuccess⟩
    · rw [hfail.2]
      exact hfill _
    · rw [hsuccess]
      exact hfill _
  · rw [ha.signalPending.2]
    exact hl
  · rw [ha.condResched.2]
    exact hl

/-! ## Every run keeps it -/

/-- Every transition preserves the types of the checker's scalar fields. -/
theorem source_next_typed {sb : Nat} {q : (Semantics.ExecState prog State)} {a : (Semantics.ExecAction prog State)}
    (hn : Semantics.nextFor Vbcf.prog q = some a)
    (hl : TypedU32 (Semantics.stateKernelState q).mem sb) :
    TypedU32 (Semantics.stateKernelState a.target).mem sb := by
  cases q with
  | regular s env mem orc k =>
    cases s <;> simp only [Semantics.nextFor, Semantics.nextCore, Semantics.returnTarget] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals simp only [Semantics.Action.target, Semantics.stateKernelState] at *
    all_goals first
      | exact hl
      | exact hl.storeArr (by assumption)
      | exact hl.storeField (by assumption)
  | callstate f vs mem orc k =>
    cases f <;> simp only [Semantics.nextFor, Semantics.nextCore] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals simp only [Semantics.Action.target, Semantics.stateKernelState] at *
    all_goals first
      | exact hl
      | exact hl.ext (by assumption)
  | returnstate rv mem orc k =>
    cases k <;> simp only [Semantics.nextFor, Semantics.nextCore] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals exact hl

theorem source_rawStar_typed {sb : Nat} {q q' : (Semantics.ExecState prog State)}
    (h : Semantics.RawStar (Semantics.rawStepFor Vbcf.prog) q q') :
    TypedU32 (Semantics.stateKernelState q).mem sb →
      TypedU32 (Semantics.stateKernelState q').mem sb := by
  induction h with
  | refl => exact id
  | step _ _ _ hs _ ih =>
    intro hl
    obtain ⟨a, hn, rfl⟩ := hs
    exact ih (source_next_typed hn hl)

/-- Every call keeps `TypedU32`; costs do not affect the operational path. -/
theorem FnCost.typed {f : String} {pre : List Val → (KernelState prog State) → Prop}
    {post : List Val → (KernelState prog State) → Option Val → (KernelState prog State) → Cost → Prop}
    (sb : Nat) (h : FnCost (State := State) Vbcf.prog f pre post) :
    FnCost (State := State) Vbcf.prog f (fun vs st => pre vs st ∧ TypedU32 st.mem sb)
      (fun vs st rv st' c => post vs st rv st' c ∧ TypedU32 st'.mem sb) := by
  intro vs st ⟨hp, hl⟩
  obtain ⟨fuel, hf⟩ := h vs st hp
  refine ⟨fuel, ?_⟩
  revert hf
  cases hr : Vbcf.prog.runC fuel f vs st with
  | timeout => intro hf; exact hf
  | stuck => intro _; trivial
  | ok r =>
    obtain ⟨rv, st', c⟩ := r
    intro hf
    refine ⟨hf, ?_⟩
    have he : Vbcf.prog.run fuel f vs st = .ok (rv, st') := by
      rw [← runC_erase, hr]
      rfl
    exact source_rawStar_typed (Semantics.run_ok_path he) hl

/-- A `u32` field that loads holds a `u32`. -/
theorem TypedU32.load {m : Mem} {sb i : Nat} {w mm : BitVec 32} {f : String} {x : Val}
    (ht : TypedU32 m sb) (hb : Budget m sb w mm) (hf : fieldIn ckS.fields f = some (i, Ty.u32))
    (hl : m.loadField Vbcf.prog sb f = some x) : ∃ X, x = .u32 X ∧ Fld m sb i (.u32 X) := by
  have hfx := hb.fld_of_load hf hl
  obtain ⟨cells, hblk, hc⟩ := hfx
  rcases ht cells hblk i x (by rw [fieldIn_idx hf]; rfl) hc with rfl | ⟨X, rfl⟩
  · have := Fld.load_undef ⟨cells, hblk, hc⟩ hf
    rw [this] at hl; simp at hl
  · exact ⟨X, rfl, cells, hblk, hc⟩

/-- A fresh struct from `kzalloc` has its `u32` fields zero. -/
theorem TypedU32.of_kzalloc {st st' : (KernelState prog State)} {b : Nat}
    (h : Ext.run Vbcf.prog (.kzalloc "ck") [] st = some (some (.ptr b 0), st')) : TypedU32 st'.mem b := by
  obtain ⟨d, hd, ha⟩ := (Ext.run_spec h).kzalloc
  rw [prog_ck] at hd
  simp only [Option.some.injEq] at hd
  subst d
  rcases ha with hnull | hsuccess
  · have he := hnull.1
    simp at he
  · have he := hsuccess
    have hb := he.1
    simp only [Option.some.injEq, Val.ptr.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    rw [he.2]
    intro cells hb i v hi hv
    simp only [Mem.block?_alloc, ↓reduceIte, Option.some.injEq, Block.mk.injEq, true_and] at hb
    subst cells
    rw [ck_zeroU32 hi] at hv
    simp only [Option.some.injEq] at hv
    exact Or.inr ⟨0, hv.symm⟩

end Vbcf.Proof
