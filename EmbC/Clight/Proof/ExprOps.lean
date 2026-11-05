import EmbC.Clight.Proof.Env
import EmbC.Clight.Proof.Ops

/-!
# Clight operations on represented values
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-- Static type of a lowered expression. -/
def tyO : Option Ty → CC.Ty
  | some t => type t
  | none => CC.tptr .Tvoid

/-- Dynamic shape of a value of a lowered expression. -/
def ValTyO (m : Mem) (v : Val) : Option Ty → Prop
  | some t => ValTy m v t
  | none => v = .null

theorem ValTyO.mono {m m' : Mem} (hg : MemGrow m m') {v : Val} {o : Option Ty}
    (h : ValTyO m v o) : ValTyO m' v o := by
  cases o with
  | none => exact h
  | some t => exact ValTy.mono hg h

theorem ptrofs_unsigned_repr {z : CC.Z} (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    CC.Integers.Ptrofs.unsigned (CC.Integers.Ptrofs.repr z) = z := by
  simp only [CC.Integers.Ptrofs.unsigned, CC.Integers.Ptrofs.repr, CC.Integers.MI.unsigned,
    CC.Integers.MI.repr]
  show ((BitVec.ofInt 64 z).toNat : Int) = z
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  exact Int.emod_eq_of_lt h0 (by simpa using h1)

theorem deref_scalar {t : Ty} (h : t.isStruct = false) (cm : CC.Mem) (B : CC.Block)
    (ofs : CC.Integers.Ptrofs) :
    CC.doDerefLoc (type t) cm B ofs .Full =
      CC.Mem.load (chunkOf t) cm B (CC.Integers.Ptrofs.unsigned ofs) := by
  simp only [CC.doDerefLoc, accessMode_type h, CC.Mem.loadv]

/-! ## Casts -/

theorem cast_ptr_ptr (w : CC.Val) (a b : CC.Ty) (cm : CC.Mem)
    (hw : (∃ B o, w = .Vptr B o) ∨ w = .Vlong 0) :
    CC.Cop.semCast w (CC.tptr a) (CC.tptr b) cm = some w := by
  rcases hw with ⟨B, o, rfl⟩ | rfl <;> rfl

theorem valRel_ptr_shape {P : Prog} {m : Mem} {j : MemoryInjection} {v : Val} {w : CC.Val}
    {t : Ty} (hv : valRel P m j v w) (ht : ValTy m v (.ptr t)) :
    (∃ B o, w = .Vptr B o) ∨ w = .Vlong 0 := by
  rcases ht with rfl | ⟨b, off, rfl, _⟩
  · right; simp only [valRel] at hv; rw [hv]; rfl
  · left; obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, _, rfl⟩

/-- A cast to the declared type of a value it already has is the identity. -/
theorem cast_accepts {P : Prog} {m : Mem} {j : MemoryInjection} {v : Val} {w : CC.Val}
    {o : Option Ty} {t : Ty} (hv : valRel P m j v w) (ho : ValTyO m v o)
    (hacc : Priv.accepts t o = true) (hu : v ≠ .undef) (cm : CC.Mem) :
    CC.Cop.semCast w (tyO o) (type t) cm = some w := by
  cases o with
  | none =>
    cases t <;> simp [Priv.accepts] at hacc
    simp only [ValTyO] at ho; subst ho
    simp only [valRel] at hv; subst hv
    exact cast_ptr_ptr _ _ _ _ (.inr rfl)
  | some t' =>
    have : t' = t := by simpa [Priv.accepts] using hacc
    subst this
    simp only [tyO]
    cases t' with
    | u32 => obtain ⟨a, rfl⟩ := ho; simp only [valRel] at hv; subst hv; rfl
    | u64 => obtain ⟨a, rfl⟩ := ho; simp only [valRel] at hv; subst hv; rfl
    | ptr t => exact cast_ptr_ptr _ _ _ _ (valRel_ptr_shape hv ho)
    | bpfptr =>
      rcases ho with rfl | rfl
      · simp only [valRel] at hv; subst hv; rfl
      · exact absurd rfl hu
    | struct s => exact ho.elim


/-! ## Pointer arithmetic -/

/-- An integer index value and its static type. -/
def IdxW (wi : CC.Val) (ti : CC.Ty) (k : Nat) : Prop :=
  (∃ a : BitVec 32, wi = .Vint a ∧ ti = CC.tuint ∧ k = a.toNat) ∨
  (∃ a : BitVec 64, wi = .Vlong a ∧ ti = CC.tulong ∧ k = a.toNat)

theorem add_ptr_idx (ce : CC.CompositeEnv) {T ty : CC.Ty}
    (hT : CC.typeconv T = .Tpointer ty CC.noattr) (B : CC.Block) (o : CC.Integers.Ptrofs)
    {wi : CC.Val} {ti : CC.Ty} {k : Nat} (hidx : IdxW wi ti k) (cm : CC.Mem) :
    CC.Cop.semBinaryOperation ce .Oadd (.Vptr B o) T wi ti cm =
      some (.Vptr B (CC.Integers.Ptrofs.add o (CC.Integers.Ptrofs.repr (CC.sizeof ce ty * k)))) := by
  rcases hidx with ⟨a, rfl, rfl, rfl⟩ | ⟨a, rfl, rfl, rfl⟩
  · simp only [CC.Cop.semBinaryOperation, CC.Cop.semAdd, CC.Cop.classifyAdd, hT]
    show some (CC.Val.Vptr B (CC.Integers.Ptrofs.add o (CC.Integers.Ptrofs.mul _ _))) = _
    congr 3
    simp only [CC.Integers.Ptrofs.mul, CC.Integers.MI.mul,
      CC.Integers.Ptrofs.repr, CC.Integers.MI.repr, CC.Cop.ptrofsOfInt, CC.Integers.Ptrofs.of_intu,
      CC.Integers.Ptrofs.of_int]
    rw [BitVec.ofInt_mul]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp
  · simp only [CC.Cop.semBinaryOperation, CC.Cop.semAdd, CC.Cop.classifyAdd, hT]
    show some (CC.Val.Vptr B (CC.Integers.Ptrofs.add o (CC.Integers.Ptrofs.mul _ _))) = _
    congr 3
    simp only [CC.Integers.Ptrofs.mul, CC.Integers.MI.mul,
      CC.Integers.Ptrofs.repr, CC.Integers.MI.repr, CC.Integers.Ptrofs.of_int64,
      CC.Integers.MI.unsigned]
    rw [BitVec.ofInt_mul]

theorem ptrofs_add_repr (a b : CC.Z) :
    CC.Integers.Ptrofs.add (CC.Integers.Ptrofs.repr a) (CC.Integers.Ptrofs.repr b) =
      CC.Integers.Ptrofs.repr (a + b) := by
  simp only [CC.Integers.Ptrofs.add, CC.Integers.MI.add, CC.Integers.Ptrofs.repr, CC.Integers.MI.repr]
  rw [BitVec.ofInt_add]

theorem idxW_of {P : Prog} {m : Mem} {j : MemoryInjection} {vi : Val} {wi : CC.Val}
    {o : Option Ty} (hv : valRel P m j vi wi) (ho : ValTyO m vi o)
    (hint : o.any Priv.intType = true) :
    ∃ k, vi.toIdx = some k ∧ IdxW wi (tyO o) k := by
  rcases o with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp [Priv.intType] at hint
  · obtain ⟨a, rfl⟩ := ho; simp only [valRel] at hv; subst hv
    exact ⟨_, rfl, .inl ⟨a, rfl, rfl, rfl⟩⟩
  · obtain ⟨a, rfl⟩ := ho; simp only [valRel] at hv; subst hv
    exact ⟨_, rfl, .inr ⟨a, rfl, rfl, rfl⟩⟩

/-! ## Pointer comparisons -/

theorem stride_eq {P : Prog} {j : MemoryInjection} {m : Mem} {cm : CC.Mem}
    (hrel : memoryRel P j m cm) {b : Nat} {blk : Block} (hb : m.block? b = some blk) :
    (j.stride b : CC.Z) = byteSize P blk.elem := (hrel.2.2.1 b blk hb).2.1

theorem weak_valid {P : Prog} {j : MemoryInjection} {m : Mem} {cm : CC.Mem}
    (hrel : memoryRel P j m cm) {b off : Nat} {blk : Block} (hb : m.block? b = some blk)
    (hfit : valueFits P m (.ptr b off)) (hlt : off * j.stride b < 2 ^ 64) :
    CC.Val.weakValidPtr (CC.Mem.validPointer cm) (j.block b)
      (CC.Integers.Ptrofs.unsigned (CC.Integers.Ptrofs.repr ((off * j.stride b : Nat) : CC.Z))) =
        true := by
  obtain ⟨_, hst, hperm, _⟩ := hrel.2.2.1 b blk hb
  have hpos := (hrel.1.2 b blk hb).1
  simp only [valueFits, hb] at hfit
  obtain ⟨hoff, hnn, _⟩ := hfit
  have hX : ((off * j.stride b : Nat) : CC.Z) = (off : CC.Z) * byteSize P blk.elem := by
    rw [Int.natCast_mul, hst]
  have hlt' : ((off * j.stride b : Nat) : CC.Z) < 2 ^ 64 := by
    have : ((off * j.stride b : Nat) : CC.Z) < ((2 ^ 64 : Nat) : CC.Z) := Int.ofNat_lt.mpr hlt
    simpa using this
  rw [ptrofs_unsigned_repr (Int.natCast_nonneg _) hlt']
  have hle : ((off * j.stride b : Nat) : CC.Z) ≤ blockByteSize P blk := by
    rw [hX]
    unfold blockByteSize
    split
    · rename_i hs; simp only [hs, ite_true] at hoff; subst hoff; simpa using hnn
    · rename_i hs; simp only [hs] at hoff
      exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hoff) hnn
  have hperm' := fun z (h1 : 0 ≤ z) (h2 : z < blockByteSize P blk) =>
    CC.Mem.perm_implies (CC.Mem.rangePerm_perm _ _ _ _ _ _ hperm z h1 h2) (by decide)
      (q := .Nonempty)
  have h0 : (0 : CC.Z) ≤ ((off * j.stride b : Nat) : CC.Z) := Int.natCast_nonneg _
  unfold CC.Val.weakValidPtr CC.Mem.validPointer
  rcases Int.lt_or_eq_of_le hle with h | h
  · rw [hperm' _ h0 h]; rfl
  · have hp2 : 0 < ((off * j.stride b : Nat) : CC.Z) := h ▸ hpos
    have q1 : (0 : CC.Z) ≤ ((off * j.stride b : Nat) : CC.Z) - 1 := Int.le_sub_one_of_lt hp2
    have q2 : ((off * j.stride b : Nat) : CC.Z) - 1 < blockByteSize P blk :=
      Int.sub_one_lt_of_le (Int.le_of_eq h)
    rw [hperm' _ q1 q2]; simp

theorem vnullptr_eq : CC.Val.Vnullptr = .Vlong 0 := rfl

theorem cmpPtr_unfold (cm : CC.Mem) (c : CC.Comparison) (X Y : CC.Ty) (w1 w2 : CC.Val) :
    CC.Cop.semCmp c w1 (CC.tptr X) w2 (CC.tptr Y) cm =
      (CC.Val.cmplu_bool (CC.Mem.validPointer cm) c w1 w2).map CC.Val.ofBool := rfl

theorem repr_inj64 {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : CC.Integers.Ptrofs.repr (x : CC.Z) = CC.Integers.Ptrofs.repr (y : CC.Z)) : x = y := by
  have := congrArg CC.Integers.Ptrofs.unsigned h
  rw [ptrofs_unsigned_repr (Int.natCast_nonneg _) (by have := Int.ofNat_lt.mpr hx; simpa using this),
    ptrofs_unsigned_repr (Int.natCast_nonneg _) (by have := Int.ofNat_lt.mpr hy; simpa using this)] at this
  exact Int.ofNat.inj this

theorem cmplu_ne (vp : CC.Block → CC.Z → Bool) (w1 w2 : CC.Val) :
    CC.Val.cmplu_bool vp .Cne w1 w2 = (CC.Val.cmplu_bool vp .Ceq w1 w2).map (!·) := by
  unfold CC.Val.cmplu_bool
  cases w1 <;> cases w2 <;> simp only [Option.map] <;> (repeat' split) <;>
    simp_all [CC.Val.cmpDifferentBlocks, CC.Integers.Int64.cmpu, CC.Integers.Ptrofs.cmpu, CC.Integers.MI.cmpu]

theorem ptr_cmp {P : Prog} {m : Mem} {j : MemoryInjection} {cm : CC.Mem}
    (hrel : memoryRel P j m cm) {op : BinOp} (hop : op = .eq ∨ op = .ne) {va vb : Val} {r : Bool}
    (hr : EmbC.ptrEq m va vb = some r) {wa wb : CC.Val} (ha : valRel P m j va wa)
    (hb : valRel P m j vb wb) (hfa : valueFits P m va) (hfb : valueFits P m vb)
    (X Y : CC.Ty) (ce : CC.CompositeEnv) :
    CC.Cop.semBinaryOperation ce (Priv.binop op) wa (CC.tptr X) wb (CC.tptr Y) cm =
      some (CC.Val.ofBool (if op = .eq then r else !r)) := by
  have key : CC.Val.cmplu_bool (CC.Mem.validPointer cm) .Ceq wa wb = some r := by
    match va, vb, hr with
    | .null, .null, hr =>
      simp only [EmbC.ptrEq, Option.some.injEq] at hr; subst hr
      simp only [valRel] at ha hb; subst ha hb; rfl
    | .ptr b o, .null, hr =>
      simp only [EmbC.ptrEq] at hr
      split at hr
      · rename_i hs
        cases hr
        obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨_, hlt, rfl⟩ := ha
        simp only [valRel] at hb; subst hb
        have := weak_valid hrel hblk hfa hlt
        simp only [CC.Val.cmplu_bool, vnullptr_eq, this]; rfl
      · cases hr
    | .null, .ptr b o, hr =>
      simp only [EmbC.ptrEq] at hr
      split at hr
      · rename_i hs
        cases hr
        obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨_, hlt, rfl⟩ := hb
        simp only [valRel] at ha; subst ha
        have := weak_valid hrel hblk hfb hlt
        simp only [CC.Val.cmplu_bool, vnullptr_eq, this]; rfl
      · cases hr
    | .ptr b o, .ptr b' o', hr =>
      simp only [EmbC.ptrEq] at hr
      split at hr
      · rename_i hs
        obtain ⟨rfl, hs⟩ := hs
        cases hr
        obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨_, hlt, rfl⟩ := ha
        obtain ⟨_, hlt', rfl⟩ := hb
        have h1 := weak_valid hrel hblk hfa hlt
        have h2 := weak_valid hrel hblk hfb hlt'
        simp only [CC.Val.cmplu_bool, h1, h2]
        simp only [show CC.Archi.ptr64 = true from rfl, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, Bool.and_self]
        congr 1
        simp only [CC.Integers.Ptrofs.cmpu, CC.Integers.MI.cmpu, CC.Integers.MI.eq]
        by_cases ho : o = o'
        · subst ho; simp only [decide_true]; exact beq_iff_eq.mpr rfl
        · have hne : CC.Integers.Ptrofs.repr ((o * j.stride b : Nat) : CC.Z) ≠
              CC.Integers.Ptrofs.repr ((o' * j.stride b : Nat) : CC.Z) := fun h =>
            ho (Nat.eq_of_mul_eq_mul_right (j.stride_positive b) (repr_inj64 hlt hlt' h))
          rw [Int.natCast_mul, Int.natCast_mul] at hne
          simp only [ho, decide_false]
          exact beq_false_of_ne hne
      · cases hr
  rcases hop with rfl | rfl
  · simp only [Priv.binop, CC.Cop.semBinaryOperation, cmpPtr_unfold, key]; rfl
  · simp only [Priv.binop, CC.Cop.semBinaryOperation, cmpPtr_unfold, cmplu_ne, key]; rfl


end EmbC.Clight.Proof
