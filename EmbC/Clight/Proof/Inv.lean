import EmbC.Clight.Proof.Defs

/-!
# Source-side invariants

Growth of the source memory (live blocks keep their element type, dead blocks
stay dead, new blocks are appended), shape typing of values, and monotonicity
of the value representation along memory growth and injection extension.
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-! ## Block lookup after memory operations -/

theorem block?_def (m : Mem) (b : Nat) :
    m.block? b = (match m.blocks[b]? with | some (some blk) => some blk | _ => none) := rfl

theorem block?_lt {m : Mem} {b : Nat} {blk : Block} (h : m.block? b = some blk) :
    b < m.blocks.size := by
  unfold Mem.block? at h
  split at h
  · rename_i h'; exact (Array.getElem?_eq_some_iff.mp h').1
  · cases h

theorem block?_of_get {m : Mem} {b : Nat} {blk : Block} (h : m.blocks[b]? = some (some blk)) :
    m.block? b = some blk := by
  simp [Mem.block?, h]

theorem setCell_size (m : Mem) (b i : Nat) (v : Val) :
    (m.setCell b i v).blocks.size = m.blocks.size := by
  simp [Mem.setCell]

theorem setCell_block? (m : Mem) (b i : Nat) (v : Val) (b' : Nat) :
    (m.setCell b i v).block? b' =
      (m.block? b').map (fun blk => if b = b' then ⟨blk.elem, blk.cells.setIfInBounds i v⟩ else blk) := by
  simp only [Mem.block?, Mem.setCell, Array.getElem?_modify]
  by_cases h : b = b'
  · subst h; simp only [ite_true]
    cases m.blocks[b]? with
    | none => rfl
    | some o => cases o <;> rfl
  · simp only [h, ite_false]
    cases m.blocks[b']? with
    | none => rfl
    | some o => cases o <;> rfl

theorem setCell_get_none (m : Mem) (b i : Nat) (v : Val) (b' : Nat) :
    (m.setCell b i v).blocks[b']? = some none ↔ m.blocks[b']? = some none := by
  simp only [Mem.setCell, Array.getElem?_modify]
  by_cases h : b = b'
  · subst h; simp only [ite_true]
    cases m.blocks[b]? with
    | none => simp
    | some o => cases o <;> simp
  · simp [h]

theorem fill_size (m : Mem) (b off : Nat) (vs : List Val) :
    (m.fill b off vs).blocks.size = m.blocks.size := by
  simp [Mem.fill]

theorem fill_block?_elem {m : Mem} {b off : Nat} {vs : List Val} {b' : Nat} {blk' : Block}
    (h : (m.fill b off vs).block? b' = some blk') :
    ∃ blk, m.block? b' = some blk ∧ blk.elem = blk'.elem := by
  simp only [Mem.block?, Mem.fill, Array.getElem?_modify] at h ⊢
  by_cases hb : b = b'
  · subst hb; simp only [ite_true] at h
    cases hg : m.blocks[b]? with
    | none => simp [hg] at h
    | some o =>
      cases o with
      | none => simp [hg] at h
      | some blk => simp [hg] at h; subst h; exact ⟨blk, rfl, rfl⟩
  · simp only [hb, ite_false] at h
    cases hg : m.blocks[b']? with
    | none => simp [hg] at h
    | some o =>
      cases o with
      | none => simp [hg] at h
      | some blk => simp [hg] at h; subst h; exact ⟨_, rfl, rfl⟩

theorem free_size (m : Mem) (b : Nat) : (m.free b).blocks.size = m.blocks.size := by
  simp [Mem.free]

theorem free_block? (m : Mem) (b b' : Nat) :
    (m.free b).block? b' = if b = b' then none else m.block? b' := by
  simp only [Mem.block?, Mem.free, Array.getElem?_setIfInBounds]
  by_cases h : b = b'
  · subst h; simp only [ite_true]
    split <;> simp_all
  · simp [h]

theorem alloc_size (m : Mem) (t : Ty) (cells : Array Val) :
    (m.alloc t cells).2.blocks.size = m.blocks.size + 1 := by
  simp [Mem.alloc]

theorem alloc_block? (m : Mem) (t : Ty) (cells : Array Val) (b' : Nat) :
    (m.alloc t cells).2.block? b' =
      if b' < m.blocks.size then m.block? b'
      else if b' = m.blocks.size then some ⟨t, cells⟩ else none := by
  simp only [Mem.block?, Mem.alloc, Array.getElem?_push]
  by_cases h1 : b' < m.blocks.size
  · have : b' ≠ m.blocks.size := by omega
    simp [h1, this]
  · by_cases h2 : b' = m.blocks.size
    · subst h2; simp
    · have : m.blocks[b']? = none := by simp; omega
      simp [h1, h2, this]

/-! ## Memory growth -/

structure MemGrow (m m' : Mem) : Prop where
  size : m.blocks.size ≤ m'.blocks.size
  live : ∀ b blk', m'.block? b = some blk' → b < m.blocks.size →
    ∃ blk, m.block? b = some blk ∧ blk.elem = blk'.elem

theorem MemGrow.refl (m : Mem) : MemGrow m m :=
  ⟨Nat.le_refl _, fun _ blk' h _ => ⟨blk', h, rfl⟩⟩

theorem MemGrow.trans {m₁ m₂ m₃ : Mem} (h₁ : MemGrow m₁ m₂) (h₂ : MemGrow m₂ m₃) :
    MemGrow m₁ m₃ := by
  refine ⟨Nat.le_trans h₁.size h₂.size, fun b blk₃ h hb => ?_⟩
  obtain ⟨blk₂, e₂, t₂⟩ := h₂.live b blk₃ h (Nat.lt_of_lt_of_le hb h₁.size)
  obtain ⟨blk₁, e₁, t₁⟩ := h₁.live b blk₂ e₂ hb
  exact ⟨blk₁, e₁, t₁.trans t₂⟩

theorem MemGrow.setCell (m : Mem) (b i : Nat) (v : Val) : MemGrow m (m.setCell b i v) := by
  refine ⟨Nat.le_of_eq (setCell_size _ _ _ _).symm, fun b' blk' h _ => ?_⟩
  rw [setCell_block?] at h
  cases hg : m.block? b' with
  | none => simp [hg] at h
  | some blk =>
    simp only [hg, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨blk, rfl, ?_⟩
    split <;> rfl

theorem MemGrow.fill (m : Mem) (b off : Nat) (vs : List Val) : MemGrow m (m.fill b off vs) :=
  ⟨Nat.le_of_eq (fill_size _ _ _ _).symm, fun _ _ h _ => fill_block?_elem h⟩

theorem MemGrow.free (m : Mem) (b : Nat) : MemGrow m (m.free b) := by
  refine ⟨Nat.le_of_eq (free_size _ _).symm, fun b' blk' h _ => ?_⟩
  rw [free_block?] at h
  split at h
  · cases h
  · exact ⟨blk', h, rfl⟩

theorem MemGrow.alloc (m : Mem) (t : Ty) (cells : Array Val) : MemGrow m (m.alloc t cells).2 := by
  refine ⟨by rw [alloc_size]; omega, fun b' blk' h hb => ?_⟩
  rw [alloc_block?] at h
  simp only [hb, ite_true] at h
  exact ⟨blk', h, rfl⟩

theorem storeArr_eq {m m' : Mem} {b i : Nat} {v : Val} (h : m.storeArr b i v = some m') :
    ∃ blk, m.block? b = some blk ∧ blk.elem.isStruct = false ∧ m.hasTy v blk.elem = true ∧
      i < blk.cells.size ∧ m' = m.setCell b i v := by
  unfold Mem.storeArr at h
  split at h
  · cases h
  · rename_i blk hblk
    split at h
    · cases h
    · rename_i hs
      split at h
      · rename_i hc
        cases h
        exact ⟨blk, hblk, by simpa using hs, hc.1, hc.2, rfl⟩
      · cases h

theorem storeField_eq {P : Prog} {m m' : Mem} {b : Nat} {f : String} {v : Val}
    (h : m.storeField P b f v = some m') :
    ∃ blk i t, m.fieldSlot P b f = some (blk, i, t) ∧ m.hasTy v t = true ∧
      i < blk.cells.size ∧ m' = m.setCell b i v := by
  unfold Mem.storeField at h
  split at h
  · cases h
  · rename_i blk i t hs
    split at h
    · rename_i hc; cases h; exact ⟨blk, i, t, hs, hc.1, hc.2, rfl⟩
    · cases h

theorem MemGrow.storeArr {m m' : Mem} {b i : Nat} {v : Val} (h : m.storeArr b i v = some m') :
    MemGrow m m' := by
  obtain ⟨_, _, _, _, _, rfl⟩ := storeArr_eq h
  exact MemGrow.setCell _ _ _ _

theorem MemGrow.storeField {P : Prog} {m m' : Mem} {b : Nat} {f : String} {v : Val}
    (h : m.storeField P b f v = some m') : MemGrow m m' := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := storeField_eq h
  exact MemGrow.setCell _ _ _ _

theorem MemGrow.returns {P : Prog} {call : Kernel.Call} {reply : Kernel.Reply}
    (h : Oracle.Returns P call reply) : MemGrow call.before reply.after := by
  rcases call with ⟨ext, args, mem⟩
  rcases reply with ⟨rv, after⟩
  have hd := h.defined
  cases ext with
  | kvcalloc t =>
    match args, hd, h with
    | [.u64 n], hd, h =>
      rcases h.kvcalloc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact MemGrow.refl _
      · exact MemGrow.alloc _ _ _
  | kzalloc name =>
    match args, hd, h with
    | [], hd, h =>
      obtain ⟨d, _, hr⟩ := h.kzalloc
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact MemGrow.refl _
      · exact MemGrow.alloc _ _ _
  | kvrealloc t =>
    match args, hd, h with
    | [.null, .u64 n], hd, h =>
      rcases h.kvrealloc_null with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact MemGrow.refl _
      · exact MemGrow.alloc _ _ _
    | [.ptr b off, .u64 n], hd, h =>
      obtain ⟨blk, _, hr⟩ := h.kvrealloc_ptr
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact MemGrow.refl _
      · exact (MemGrow.free _ _).trans (MemGrow.alloc _ _ _)
    | [.u32 _, .u64 _], ⟨_, _, hf⟩, _ | [.u64 _, .u64 _], ⟨_, _, hf⟩, _ |
      [.uptr, .u64 _], ⟨_, _, hf⟩, _ | [.undef, .u64 _], ⟨_, _, hf⟩, _ => exact hf.elim
  | kvfree =>
    match args, hd, h with
    | [.null], hd, h =>
      obtain ⟨rfl, rfl⟩ := h.kvfree_null
      exact MemGrow.refl _
    | [.ptr b off], hd, h =>
      obtain ⟨rfl, rfl⟩ := h.kvfree_ptr
      exact MemGrow.free _ _
    | [.u32 _], hf, _ | [.u64 _], hf, _ | [.uptr], hf, _ | [.undef], hf, _ => exact hf.elim
  | copyFromBpfptr =>
    match args, hd, h with
    | [.ptr b off, .uptr, .u64 n], hd, h =>
      rcases h.copyFromBpfptr with ⟨rfl, rfl⟩ | ⟨words, _, rfl, rfl⟩
      · exact MemGrow.fill _ _ _ _
      · exact MemGrow.fill _ _ _ _
  | signalPending =>
    match args, hd, h with
    | [], hd, h =>
      obtain ⟨_, rfl⟩ := h.signalPending
      exact MemGrow.refl _
  | condResched =>
    match args, hd, h with
    | [], hd, h =>
      obtain ⟨rfl, rfl⟩ := h.condResched
      exact MemGrow.refl _

/-! ## Shape typing -/

/-- The shape of a value of a declared scalar type.  Pointers are typed by
their block's element type while that block is live. -/
def ValTy (m : Mem) (v : Val) : Ty → Prop
  | .u32 => ∃ a, v = .u32 a
  | .u64 => ∃ a, v = .u64 a
  | .ptr t => v = .null ∨ ∃ b off, v = .ptr b off ∧ b < m.blocks.size ∧
      ∀ blk, m.block? b = some blk → blk.elem = t
  | .bpfptr => v = .uptr ∨ v = .undef
  | .struct _ => False

theorem ValTy.mono {m m' : Mem} (hg : MemGrow m m') {v : Val} {t : Ty} (h : ValTy m v t) :
    ValTy m' v t := by
  cases t with
  | ptr t =>
    rcases h with h | ⟨b, off, rfl, hb, hel⟩
    · exact .inl h
    · refine .inr ⟨b, off, rfl, Nat.lt_of_lt_of_le hb hg.size, fun blk' h' => ?_⟩
      obtain ⟨blk, e, te⟩ := hg.live b blk' h' hb
      rw [← te]; exact hel blk e
  | _ => exact h

theorem hasTy_ptr_ptr (m : Mem) (b off : Nat) (t : Ty) :
    m.hasTy (.ptr b off) (.ptr t) = (match m.block? b with | some blk => blk.elem == t | none => false) :=
  rfl

theorem ValTy.of_hasTy {m : Mem} {v : Val} {t : Ty} (h : m.hasTy v t = true) : ValTy m v t := by
  match v, t, h with
  | .u32 a, .u32, _ => exact ⟨a, rfl⟩
  | .u64 a, .u64, _ => exact ⟨a, rfl⟩
  | .null, .ptr _, _ => exact .inl rfl
  | .uptr, .bpfptr, _ => exact .inl rfl
  | .ptr b off, .ptr t, h =>
    rw [hasTy_ptr_ptr] at h
    split at h
    · rename_i blk hblk
      refine .inr ⟨b, off, rfl, block?_lt hblk, fun blk' h' => ?_⟩
      rw [hblk] at h'; cases h'; simpa using h
    · cases h

theorem ValTy.of_cellTyped {m : Mem} {v : Val} {t : Ty} (h : cellTyped m v t) (hv : v ≠ .undef) :
    ValTy m v t := by
  rcases h with h | h | ⟨b, off, elem, rfl, rfl, hb, hn⟩
  · exact absurd h hv
  · exact ValTy.of_hasTy h
  · exact .inr ⟨b, off, rfl, hb, fun blk h' => by rw [hn] at h'; cases h'⟩

theorem ValTy.zero {m : Mem} {t : Ty} (h : t.isStruct = false) : ValTy m t.zero t := by
  cases t <;> simp [Ty.zero, ValTy, Ty.isStruct] at h ⊢

theorem ValTy.ne_undef_of_not_bpfptr {m : Mem} {v : Val} {t : Ty} (h : ValTy m v t)
    (ht : t ≠ .bpfptr) : v ≠ .undef := by
  intro hv; subst hv
  cases t <;> simp [ValTy] at h ht

/-! ## Representation monotonicity -/

theorem Extends.refl (j : MemoryInjection) (m : Mem) : j.Extends j m :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem Extends.trans {j₁ j₂ j₃ : MemoryInjection} {m₁ m₂ : Mem} (h₁ : j₁.Extends j₂ m₁)
    (h₂ : j₂.Extends j₃ m₂) (hs : m₁.blocks.size ≤ m₂.blocks.size) : j₁.Extends j₃ m₁ := by
  refine ⟨h₂.1.trans h₁.1, fun b hb => ?_⟩
  obtain ⟨a₁, a₂⟩ := h₁.2 b hb
  obtain ⟨c₁, c₂⟩ := h₂.2 b (Nat.lt_of_lt_of_le hb hs)
  exact ⟨c₁.trans a₁, c₂.trans a₂⟩

theorem valRel_mono {P : Prog} {m m' : Mem} {j j' : MemoryInjection} (hg : MemGrow m m')
    (hj : j.Extends j' m) {v : Val} {w : CC.Val} (h : valRel P m j v w) : valRel P m' j' v w := by
  cases v with
  | ptr b off =>
    obtain ⟨hb, hs, rfl⟩ := h
    obtain ⟨e1, e2⟩ := hj.2 b hb
    exact ⟨Nat.lt_of_lt_of_le hb hg.size, by rw [e2]; exact hs, by rw [e1, e2]⟩
  | uptr => simp only [valRel] at h ⊢; rw [h, hj.1]
  | _ => exact h

theorem argsRel_mono {P : Prog} {m m' : Mem} {j j' : MemoryInjection} (hg : MemGrow m m')
    (hj : j.Extends j' m) : ∀ {vs : List Val} {ws : List CC.Val},
    argsRel P m j vs ws → argsRel P m' j' vs ws
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨valRel_mono hg hj h1, argsRel_mono hg hj h2⟩

theorem retRel_mono {P : Prog} {m m' : Mem} {j j' : MemoryInjection} (hg : MemGrow m m')
    (hj : j.Extends j' m) {rv : Option Val} {w : CC.Val} (h : retRel P m j rv w) :
    retRel P m' j' rv w := by
  cases rv with
  | none => exact h
  | some v => exact valRel_mono (P := P) hg hj h

end EmbC.Clight.Proof
