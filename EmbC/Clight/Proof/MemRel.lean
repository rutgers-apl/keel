import EmbC.Clight.Proof.Inv
import CCLib.MemoryLemmas

/-!
# The memory representation: loads, stores, and their effect on `memoryRel`
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-! ## Scalar types -/

def chunkOf : Ty → CC.Chunk
  | .u32 => .Mint32
  | _ => .Mint64

theorem accessMode_type {t : Ty} (h : t.isStruct = false) :
    CC.accessMode (type t) = .By_value (chunkOf t) := by
  cases t <;> simp [Ty.isStruct] at h <;> rfl

theorem sizeof_type (ce : CC.CompositeEnv) {t : Ty} (h : t.isStruct = false) :
    CC.sizeof ce (type t) = CC.sizeChunk (chunkOf t) := by
  cases t <;> simp [Ty.isStruct] at h <;> rfl

theorem byteSize_scalar (P : Prog) {t : Ty} (h : t.isStruct = false) :
    byteSize P t = CC.sizeChunk (chunkOf t) := sizeof_type _ h

theorem sizeChunk_chunkOf_pos (t : Ty) : 0 < CC.sizeChunk (chunkOf t) := by
  cases t <;> simp [chunkOf, CC.sizeChunk]

theorem sizeChunk_chunkOf_le (t : Ty) : CC.sizeChunk (chunkOf t) ≤ 8 := by
  cases t <;> simp [chunkOf, CC.sizeChunk]

theorem alignChunk_chunkOf (t : Ty) : CC.alignChunk (chunkOf t) = CC.sizeChunk (chunkOf t) := by
  cases t <;> rfl

theorem chunk_eq_of_accessMode {t : Ty} {chunk : CC.Chunk} (h : t.isStruct = false)
    (ha : CC.accessMode (type t) = .By_value chunk) : chunk = chunkOf t := by
  rw [accessMode_type h] at ha; cases ha; rfl

/-! ## Representation does not depend on cell contents -/

theorem valRel_size {P : Prog} {m m' : Mem} {j : MemoryInjection}
    (hs : m.blocks.size = m'.blocks.size) {v : Val} {w : CC.Val} (h : valRel P m j v w) :
    valRel P m' j v w := by
  cases v with
  | ptr b off => obtain ⟨hb, h2, h3⟩ := h; exact ⟨hs ▸ hb, h2, h3⟩
  | _ => exact h

theorem loadResult_rel {P : Prog} {m : Mem} {j : MemoryInjection} {v : Val} {w : CC.Val}
    {t : Ty} (hv : valRel P m j v w) (ht : ValTy m v t) :
    CC.Val.loadResult (chunkOf t) w = w := by
  cases t with
  | u32 => obtain ⟨a, rfl⟩ := ht; simp only [valRel] at hv; subst hv; rfl
  | u64 => obtain ⟨a, rfl⟩ := ht; simp only [valRel] at hv; subst hv; rfl
  | ptr t =>
    rcases ht with rfl | ⟨b, off, rfl, _⟩
    · simp only [valRel] at hv; subst hv; rfl
    · obtain ⟨_, _, rfl⟩ := hv; rfl
  | bpfptr =>
    rcases ht with rfl | rfl
    · simp only [valRel] at hv; subst hv; rfl
    · simp only [valRel] at hv; subst hv; rfl
  | struct s => exact ht.elim

/-! ## Generic Clight memory facts -/

theorem load_validAccess {chunk : CC.Chunk} {cm : CC.Mem} {B : CC.Block} {off : CC.Z}
    {w : CC.Val} (h : CC.Mem.load chunk cm B off = some w) :
    CC.Mem.validAccess cm chunk B off .Readable = true := by
  unfold CC.Mem.load at h
  split at h
  · assumption
  · cases h

theorem rangePerm_sub {cm : CC.Mem} {B : CC.Block} {lo hi lo' hi' : Int} {k : CC.PermKind}
    {p : CC.Permission} (h : CC.Mem.rangePerm cm B lo hi k p = true) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : CC.Mem.rangePerm cm B lo' hi' k p = true :=
  CC.Mem.rangePerm_intro _ _ _ _ _ _ fun o a b =>
    CC.Mem.rangePerm_perm _ _ _ _ _ _ h o (Int.le_trans h1 a) (Int.lt_of_lt_of_le b h2)

theorem store_of_load {chunk : CC.Chunk} {cm : CC.Mem} {B : CC.Block} {off N : CC.Z}
    {w₀ : CC.Val} (hl : CC.Mem.load chunk cm B off = some w₀)
    (hp : CC.Mem.rangePerm cm B 0 N .Cur .Freeable = true) (h0 : 0 ≤ off)
    (hN : off + CC.sizeChunk chunk ≤ N) (w : CC.Val) :
    ∃ cm', CC.Mem.store chunk cm B off w = some cm' := by
  have hva := load_validAccess hl
  have hw : CC.Mem.validAccess cm chunk B off .Writable = true := by
    simp only [CC.Mem.validAccess, Bool.and_eq_true] at hva ⊢
    exact ⟨CC.Mem.rangePerm_implies (rangePerm_sub hp h0 hN) (by decide), hva.2⟩
  unfold CC.Mem.store
  simp only [hw, ite_true]
  exact ⟨_, rfl⟩

theorem store_validBlock {chunk : CC.Chunk} {cm cm' : CC.Mem} {B : CC.Block} {off : CC.Z}
    {w : CC.Val} (h : CC.Mem.store chunk cm B off w = some cm') (b : CC.Block) :
    CC.Mem.validBlock cm' b = CC.Mem.validBlock cm b := by
  simp [CC.Mem.validBlock, CC.Mem.store_nextblock h]

/-! ## Stores into source blocks -/

/-- The parts of `memoryRel` that concern blocks other than the stored one, and
the read-only tables, survive a store into a live source block. -/
theorem frame_store {P : Prog} {j : MemoryInjection} {m : Mem} {cm cm' : CC.Mem}
    {ge : CC.CGenv} {b : Nat} {chunk : CC.Chunk} {off : CC.Z} {w : CC.Val}
    (hb : b < m.blocks.size) (hst : CC.Mem.store chunk cm (j.block b) off w = some cm')
    (hc : ConstRel P ge j m cm) : ConstRel P ge j m cm' := by
  intro table ht
  obtain ⟨tb, h1, h2, h3, h4⟩ := hc table ht
  refine ⟨tb, h1, by rw [store_validBlock hst]; exact h2, h3, fun i word hw => ?_⟩
  rw [CC.Mem.load_store_other hst _ _ _ (.inl fun e => h3 b hb e.symm)]
  exact h4 i word hw

theorem constRel_size {P : Prog} {ge : CC.CGenv} {j : MemoryInjection} {m m' : Mem}
    {cm : CC.Mem} (hs : m'.blocks.size ≤ m.blocks.size) (h : ConstRel P ge j m cm) :
    ConstRel P ge j m' cm := by
  intro table ht
  obtain ⟨tb, h1, h2, h3, h4⟩ := h table ht
  exact ⟨tb, h1, h2, fun sb hsb => h3 sb (Nat.lt_of_lt_of_le hsb hs), h4⟩

/-- Loads from a block different from the stored one are unchanged. -/
theorem cellRel_store_other {P : Prog} {j : MemoryInjection} {m m' : Mem} {cm cm' : CC.Mem}
    {b b' : Nat} {chunk : CC.Chunk} {off off' : CC.Z} {w : CC.Val} {t : Ty} {v : Val}
    (hs : m.blocks.size = m'.blocks.size)
    (hst : CC.Mem.store chunk cm (j.block b) off w = some cm')
    (hne : b' ≠ b ∨ off' + CC.sizeChunk (chunkOf t) ≤ off ∨ off + CC.sizeChunk chunk ≤ off')
    (ht : t.isStruct = false)
    (h : cellRel P m j cm b' off' t v) : cellRel P m' j cm' b' off' t v := by
  obtain ⟨chunk', w', ha, hl, hv⟩ := h
  have hc := chunk_eq_of_accessMode ht ha
  subst hc
  refine ⟨_, w', ha, ?_, valRel_size hs hv⟩
  rw [CC.Mem.load_store_other hst]
  · exact hl
  · rcases hne with h | h
    · exact .inl fun e => h (j.injective _ _ e)
    · exact .inr h

/-! ## Accessing `memoryRel` block by block -/

theorem memRel_arr {P : Prog} {j : MemoryInjection} {m : Mem} {cm : CC.Mem} {b : Nat} {blk : Block}
    (hrel : memoryRel P j m cm) (hblk : m.block? b = some blk) (hns : blk.elem.isStruct = false) :
    ∀ (i : Nat) v, blk.cells[i]? = some v → cellRel P m j cm b ((i : CC.Z) * byteSize P blk.elem) blk.elem v := by
  obtain ⟨_, _, _, h⟩ := hrel.2.2.1 b blk hblk
  split at h
  · rename_i s hs; rw [hs] at hns; cases hns
  · exact h
theorem memRel_struct {P : Prog} {j : MemoryInjection} {m : Mem} {cm : CC.Mem} {b : Nat} {blk : Block}
    (hrel : memoryRel P j m cm) (hblk : m.block? b = some blk) {s : String} (he : blk.elem = .struct s) :
    ∃ d co, P.findStruct s = some d ∧
        (compositeEnv P).get (CC.identOfString s) = some co ∧
        co.co_su = .Struct ∧ co.co_members = members d ∧
        ∀ (i : Nat) f t v, d.fields[i]? = some (f, t) → blk.cells[i]? = some v →
          ∃ off, CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members =
            .OK (off, .Full) ∧ cellRel P m j cm b off t v := by
  obtain ⟨_, _, _, h⟩ := hrel.2.2.1 b blk hblk
  split at h
  · rename_i s' hs; rw [hs] at he; cases he; exact h
  · rename_i hn; exact absurd he (hn s)
def BlockRel (P : EmbC.Prog) (j : MemoryInjection)
    (m : EmbC.Mem) (cm : CC.Mem) (b : Nat) (blk : Block) : Prop :=
    CC.Mem.validBlock cm (j.block b) = true ∧
    (j.stride b : CC.Z) = byteSize P blk.elem ∧
    CC.Mem.rangePerm cm (j.block b) 0 (blockByteSize P blk) .Cur .Freeable = true ∧
    match blk.elem with
    | .struct s => ∃ d co, P.findStruct s = some d ∧
        (compositeEnv P).get (CC.identOfString s) = some co ∧
        co.co_su = .Struct ∧ co.co_members = members d ∧
        ∀ (i : Nat) f t v, d.fields[i]? = some (f, t) → blk.cells[i]? = some v →
          ∃ off, CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members =
            .OK (off, .Full) ∧ cellRel P m j cm b off t v
    | t => ∀ (i : Nat) v, blk.cells[i]? = some v →
        cellRel P m j cm b ((i : CC.Z) * byteSize P t) t v
theorem memoryRel_iff {P : Prog} {j : MemoryInjection} {m : Mem} {cm : CC.Mem} :
    memoryRel P j m cm ↔ Representable P m ∧
  (∀ b, b < m.blocks.size → CC.Mem.validBlock cm (j.block b) = true) ∧
  (∀ b blk, m.block? b = some blk → BlockRel P j m cm b blk) ∧
  (∀ b, m.blocks[b]? = some none →
    ∀ off, CC.Mem.perm cm (j.block b) off .Cur .Nonempty = false) := Iff.rfl
theorem blockRel_intro {P : Prog} {j : MemoryInjection} {m : Mem} {cm : CC.Mem} {b : Nat} {blk : Block}
  (h1 : CC.Mem.validBlock cm (j.block b) = true) (h2 : (j.stride b : CC.Z) = byteSize P blk.elem)
  (h3 : CC.Mem.rangePerm cm (j.block b) 0 (blockByteSize P blk) .Cur .Freeable = true)
  (ha : blk.elem.isStruct = false → ∀ (i : Nat) v, blk.cells[i]? = some v →
        cellRel P m j cm b ((i : CC.Z) * byteSize P blk.elem) blk.elem v)
  (hs : ∀ s, blk.elem = .struct s → ∃ d co, P.findStruct s = some d ∧
        (compositeEnv P).get (CC.identOfString s) = some co ∧
        co.co_su = .Struct ∧ co.co_members = members d ∧
        ∀ (i : Nat) f t v, d.fields[i]? = some (f, t) → blk.cells[i]? = some v →
          ∃ off, CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members =
            .OK (off, .Full) ∧ cellRel P m j cm b off t v) : BlockRel P j m cm b blk := by
  refine ⟨h1, h2, h3, ?_⟩
  split
  · rename_i s he; exact hs s he
  · rename_i t hn
    exact ha (by cases h : blk.elem <;> simp_all [Ty.isStruct])

/-! ## Stores -/

theorem cellRel_store_otherblock {P : Prog} {j : MemoryInjection} {m m' : Mem} {cm cm' : CC.Mem}
    {b b' : Nat} {chunk : CC.Chunk} {off off' : CC.Z} {w : CC.Val} {t : Ty} {v : Val}
    (hs : m.blocks.size = m'.blocks.size)
    (hst : CC.Mem.store chunk cm (j.block b) off w = some cm') (hne : b' ≠ b)
    (h : cellRel P m j cm b' off' t v) : cellRel P m' j cm' b' off' t v := by
  obtain ⟨chunk', w', ha, hl, hv⟩ := h
  refine ⟨chunk', w', ha, ?_, valRel_size hs hv⟩
  rw [CC.Mem.load_store_other hst _ _ _ (.inl fun e => hne (j.injective _ _ e))]
  exact hl

theorem blockRel_store_other {P : Prog} {j : MemoryInjection} {m m' : Mem} {cm cm' : CC.Mem}
    {b b' : Nat} {chunk : CC.Chunk} {off : CC.Z} {w : CC.Val} {blk : Block}
    (hrel : memoryRel P j m cm) (hblk : m.block? b' = some blk)
    (hs : m.blocks.size = m'.blocks.size)
    (hst : CC.Mem.store chunk cm (j.block b) off w = some cm') (hne : b' ≠ b) :
    BlockRel P j m' cm' b' blk := by
  obtain ⟨h1, h2, h3, -⟩ := hrel.2.2.1 b' blk hblk
  refine blockRel_intro (by rw [store_validBlock hst]; exact h1) h2
    (CC.Mem.rangePerm_store hst _ _ _ _ _ h3) ?_ ?_
  · intro hns i v hv
    exact cellRel_store_otherblock hs hst hne (memRel_arr hrel hblk hns i v hv)
  · intro s he
    obtain ⟨d, co, e1, e2, e3, e4, e5⟩ := memRel_struct hrel hblk he
    refine ⟨d, co, e1, e2, e3, e4, fun i f t v hf hv => ?_⟩
    obtain ⟨o, ho, hc⟩ := e5 i f t v hf hv
    exact ⟨o, ho, cellRel_store_otherblock hs hst hne hc⟩

theorem memoryRel_setCell {P : Prog} {j : MemoryInjection} {m : Mem} {cm cm' : CC.Mem}
    {b i : Nat} {v : Val} {blk : Block} {chunk : CC.Chunk} {off : CC.Z} {w : CC.Val}
    (hrel : memoryRel P j m cm) (hblk : m.block? b = some blk)
    (hrep : Representable P (m.setCell b i v))
    (hst : CC.Mem.store chunk cm (j.block b) off w = some cm')
    (hself : BlockRel P j (m.setCell b i v) cm' b ⟨blk.elem, blk.cells.setIfInBounds i v⟩) :
    memoryRel P j (m.setCell b i v) cm' := by
  have hs := (setCell_size m b i v).symm
  rw [memoryRel_iff]
  refine ⟨hrep, fun b' hb' => ?_, fun b' blk' hb' => ?_, fun b' hb' o => ?_⟩
  · rw [store_validBlock hst]; exact hrel.2.1 b' (by rwa [setCell_size] at hb')
  · rw [setCell_block?] at hb'
    cases hg : m.block? b' with
    | none => simp [hg] at hb'
    | some blk0 =>
      simp only [hg, Option.map_some, Option.some.injEq] at hb'
      subst hb'
      by_cases hbb : b = b'
      · subst hbb; rw [hblk] at hg; cases hg; simpa using hself
      · simp only [hbb, ite_false]
        exact blockRel_store_other hrel hg hs hst (Ne.symm hbb)
  · rw [setCell_get_none] at hb'
    rw [CC.Mem.perm_store hst]; exact hrel.2.2.2 b' hb' o

theorem storeArr_rel {P : Prog} {j : MemoryInjection} {m : Mem} {cm : CC.Mem} {ge : CC.CGenv}
    {b i : Nat} {v : Val} {blk : Block} {w : CC.Val}
    (hrel : memoryRel P j m cm) (hc : ConstRel P ge j m cm)
    (hblk : m.block? b = some blk) (hns : blk.elem.isStruct = false)
    (hi : i < blk.cells.size) (hty : ValTy m v blk.elem) (hv : valRel P m j v w)
    (hrep : Representable P (m.setCell b i v)) :
    ∃ cm', CC.Mem.store (chunkOf blk.elem) cm (j.block b)
        ((i : CC.Z) * byteSize P blk.elem) w = some cm' ∧
      memoryRel P j (m.setCell b i v) cm' ∧ ConstRel P ge j (m.setCell b i v) cm' := by
  obtain ⟨hvalid, hstride, hperm, -⟩ := hrel.2.2.1 b blk hblk
  have hcells := memRel_arr hrel hblk hns
  obtain ⟨v0, hv0⟩ : ∃ v0, blk.cells[i]? = some v0 := ⟨_, Array.getElem?_eq_getElem hi⟩
  obtain ⟨chunk, w0, ha, hl, _⟩ := hcells i v0 hv0
  have hck := chunk_eq_of_accessMode hns ha; subst hck
  have hsz := byteSize_scalar P hns
  have hpos := sizeChunk_chunkOf_pos blk.elem
  have hbs : blockByteSize P blk = (blk.cells.size : CC.Z) * byteSize P blk.elem := by
    simp [blockByteSize, hns]
  have hnn : (0 : Int) ≤ byteSize P blk.elem := by rw [hsz]; exact Int.le_of_lt hpos
  have hb : b < m.blocks.size := block?_lt hblk
  have hs := (setCell_size m b i v).symm
  obtain ⟨cm', hst⟩ := store_of_load hl hperm
    (Int.mul_nonneg (Int.natCast_nonneg _) hnn) (by
      rw [hbs, ← hsz]
      have : ((i : CC.Z) + 1) * byteSize P blk.elem ≤ (blk.cells.size : CC.Z) * byteSize P blk.elem :=
        Int.mul_le_mul_of_nonneg_right (by omega) hnn
      rw [Int.add_mul, Int.one_mul] at this; exact this) w
  refine ⟨cm', hst, memoryRel_setCell hrel hblk hrep hst ?_,
    constRel_size (Nat.le_of_eq hs.symm) (frame_store hb hst hc)⟩
  refine blockRel_intro (by rw [store_validBlock hst]; exact hvalid) hstride ?_ ?_ ?_
  · have : blockByteSize P ⟨blk.elem, blk.cells.setIfInBounds i v⟩ = blockByteSize P blk := by
      simp [blockByteSize]
    rw [this]; exact CC.Mem.rangePerm_store hst _ _ _ _ _ hperm
  · intro _ i' v' hi'
    simp only [Array.getElem?_setIfInBounds] at hi'
    by_cases hii : i = i'
    · subst hii
      simp only [hi, ite_true, Option.some.injEq] at hi'
      subst hi'
      refine ⟨_, w, ha, ?_, valRel_size hs hv⟩
      rw [CC.Mem.load_store_same hst, loadResult_rel hv hty]
    · simp only [hii, ite_false] at hi'
      obtain ⟨chunk', w', ha', hl', hv'⟩ := hcells i' v' hi'
      refine ⟨chunk', w', ha', ?_, valRel_size hs hv'⟩
      have hck := chunk_eq_of_accessMode hns ha'; subst hck
      rw [CC.Mem.load_store_other hst]
      · exact hl'
      · right
        rw [← hsz]
        rcases Nat.lt_or_gt_of_ne hii with h | h
        · right
          have : ((i : CC.Z) + 1) * byteSize P blk.elem ≤ (i' : CC.Z) * byteSize P blk.elem :=
            Int.mul_le_mul_of_nonneg_right (by omega) hnn
          rw [Int.add_mul, Int.one_mul] at this; exact this
        · left
          have : ((i' : CC.Z) + 1) * byteSize P blk.elem ≤ (i : CC.Z) * byteSize P blk.elem :=
            Int.mul_le_mul_of_nonneg_right (by omega) hnn
          rw [Int.add_mul, Int.one_mul] at this; exact this
  · intro s he; rw [he] at hns; cases hns

end EmbC.Clight.Proof
