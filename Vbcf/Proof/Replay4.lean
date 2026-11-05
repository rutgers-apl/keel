import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay3
import EmbC.Semantics.Correctness

/-!
# Vbcf proofs: block shapes, and `ck_free`

* `Shape m m'`: no live block changes its size, and a dead block stays dead.
  Every run of every EmbC function preserves it (`source_next_shape`,
  `FnSpec.withShape`): blocks are never resized in place.  This is what gives
  the size clause of `OnlyBlockChanged` without asking the loading-phase
  specifications to track the size of the proof block.
* `Mem.fill` on a zeroed block (what `copy_from_bpfptr` does).
* `ck_free`: frees the five owned arrays (`CkFreeSpec`, `ck_free_spec`).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

/-! ## Shapes -/

/-- From `m` to `m'`: no block disappears from the block table, a dead block
stays dead, and a block live in both has the same number of cells. -/
structure Shape (m m' : Mem) : Prop where
  size : m.blocks.size ≤ m'.blocks.size
  dead : ∀ b, b < m.blocks.size → m.block? b = none → m'.block? b = none
  cells : ∀ b blk blk', m.block? b = some blk → m'.block? b = some blk' →
    blk'.cells.size = blk.cells.size

theorem Shape.refl (m : Mem) : Shape m m :=
  ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ _ h h' => by rw [h] at h'; cases h'; rfl⟩

theorem Shape.trans {m1 m2 m3 : Mem} (h1 : Shape m1 m2) (h2 : Shape m2 m3) : Shape m1 m3 := by
  refine ⟨Nat.le_trans h1.size h2.size, fun b hb hd => h2.dead b (by have := h1.size; omega)
    (h1.dead b hb hd), ?_⟩
  intro b blk blk' hb hb'
  cases hm : m2.block? b with
  | none =>
    have := h2.dead b (by have := Mem.block?_lt hb; have := h1.size; omega) hm
    rw [this] at hb'; cases hb'
  | some blk2 => rw [h2.cells b blk2 blk' hm hb', h1.cells b blk blk2 hb hm]

theorem Shape.modify {m : Mem} (b : Nat) (g : Option Block → Option Block) (hn : g none = none)
    (hs : ∀ blk, ∃ blk', g (some blk) = some blk' ∧ blk'.cells.size = blk.cells.size) :
    Shape m ⟨m.blocks.modify b g⟩ := by
  refine ⟨by simp, ?_, ?_⟩
  · intro b' hb' hd
    have : m.blocks[b']? = some none := by
      unfold Mem.block? at hd
      rw [Array.getElem?_eq_getElem hb'] at hd ⊢
      split at hd
      · cases hd
      · rename_i hne
        cases hx : m.blocks[b'] with
        | none => rfl
        | some blk => exact absurd (by rw [hx]) (hne blk)
    unfold Mem.block?
    rw [Array.getElem?_modify, this]
    by_cases hbb : b = b' <;> simp [hbb, hn]
  · intro b' blk blk' hb hb'
    have h1 := Mem.block?_eq.mp hb
    have h2 := Mem.block?_eq.mp hb'
    rw [Array.getElem?_modify, h1] at h2
    split at h2
    · obtain ⟨blk'', hg, hsz⟩ := hs blk
      simp only [Option.map_some, hg, Option.some.injEq] at h2
      subst h2; exact hsz
    · simp at h2; subst h2; rfl

theorem Shape.setCell (m : Mem) (b i : Nat) (v : Val) : Shape m (m.setCell b i v) :=
  Shape.modify b _ rfl (fun blk => ⟨_, rfl, by simp⟩)

theorem foldl_setIfInBounds_size (l : List (Val × Nat)) (f : Nat → Nat) (cells : Array Val) :
    (l.foldl (fun cells (p : Val × Nat) => cells.setIfInBounds (f p.2) p.1) cells).size = cells.size := by
  induction l generalizing cells with
  | nil => rfl
  | cons p rest ih => simp only [List.foldl_cons]; rw [ih]; simp

theorem Shape.fill (m : Mem) (b off : Nat) (vs : List Val) : Shape m (m.fill b off vs) :=
  Shape.modify b _ rfl (fun _blk => ⟨_, rfl, foldl_setIfInBounds_size _ (off + ·) _⟩)

theorem Shape.alloc (m : Mem) (t : Ty) (cs : Array Val) : Shape m (m.alloc t cs).2 := by
  refine ⟨by simp, ?_, ?_⟩
  · intro b hb hd
    rw [Mem.block?_alloc]; simp [Nat.ne_of_lt hb, hd]
  · intro b blk blk' hb hb'
    rw [Mem.block?_alloc] at hb'
    have := Mem.block?_lt hb
    simp only [Nat.ne_of_lt this, ↓reduceIte, hb, Option.some.injEq] at hb'
    subst hb'; rfl

theorem Shape.free (m : Mem) (b : Nat) : Shape m (m.free b) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro b' _ hd
    rw [Mem.block?_free]; split <;> simp [hd]
  · intro b' _blk blk' hb hb'
    rw [Mem.block?_free] at hb'
    split at hb'
    · cases hb'
    · rw [hb] at hb'; cases hb'; rfl

theorem Mem.storeArr_some {m m' : Mem} {b i : Nat} {v : Val} (h : m.storeArr b i v = some m') :
    m' = m.setCell b i v := by
  unfold Mem.storeArr at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; rfl
      · cases h

theorem Mem.storeField_some {P : Prog} {m m' : Mem} {b : Nat} {f : String} {v : Val}
    (h : m.storeField P b f v = some m') : m' = m.setCell b (m.fieldSlot P b f |>.get! |>.2.1) v := by
  unfold Mem.storeField at h
  split at h
  · cases h
  · rename_i blk i t hslot
    split at h
    · cases h; rw [hslot]; rfl
    · cases h

theorem Shape.storeField {P : Prog} {m m' : Mem} {b : Nat} {f : String} {v : Val}
    (h : m.storeField P b f v = some m') : Shape m m' := by
  rw [Mem.storeField_some h]; exact Shape.setCell _ _ _ _

theorem Shape.storeArr {m m' : Mem} {b i : Nat} {v : Val} (h : m.storeArr b i v = some m') :
    Shape m m' := by
  rw [Mem.storeArr_some h]; exact Shape.setCell _ _ _ _

/-- Every kernel call preserves shapes. -/
theorem Ext.run_shape {P : Prog} {f : Ext} {vs : List Val} {st st' : (KernelState P State)} {rv : Option Val}
    (h : Ext.run P f vs st = some (rv, st')) : Shape st.mem st'.mem := by
  have ha := Ext.run_spec h
  have hd := ha.defined
  unfold Kernel.Defined at hd
  split at hd
  all_goals subst_vars
  all_goals try contradiction
  · rcases ha.kvcalloc with hfail | hsuccess
    · rw [hfail.2]; exact Shape.refl _
    · rw [hsuccess.2]; exact Shape.alloc _ _ _
  · obtain ⟨d, _, hreply⟩ := ha.kzalloc
    rcases hreply with hfail | hsuccess
    · rw [hfail.2]; exact Shape.refl _
    · rw [hsuccess.2]; exact Shape.alloc _ _ _
  · split at hd
    all_goals subst_vars
    all_goals try contradiction
    all_goals try exact hd.2.2.elim
    · rcases ha.kvrealloc_null with hfail | hsuccess
      · rw [hfail.2]; exact Shape.refl _
      · rw [hsuccess.2]; exact Shape.alloc _ _ _
    · obtain ⟨blk, _, hreply⟩ := ha.kvrealloc_ptr
      rcases hreply with hfail | hsuccess
      · rw [hfail.2]; exact Shape.refl _
      · rw [hsuccess.2]
        exact (Shape.free _ _).trans (Shape.alloc _ _ _)
  · split at hd
    all_goals subst_vars
    all_goals try contradiction
    · rw [ha.kvfree_null.2]; exact Shape.refl _
    · rw [ha.kvfree_ptr.2]; exact Shape.free _ _
  · rcases ha.copyFromBpfptr with hfail | ⟨words, _, _, hsuccess⟩
    · rw [hfail.2]; exact Shape.fill _ _ _ _
    · rw [hsuccess]; exact Shape.fill _ _ _ _
  · rw [ha.signalPending.2]; exact Shape.refl _
  · rw [ha.condResched.2]; exact Shape.refl _

/-- Each step of the sole operational machine preserves memory shapes. -/
theorem source_next_shape {P : Prog} {c : (EmbC.Semantics.ExecState P State)} {a : (EmbC.Semantics.ExecAction P State)}
    (h : EmbC.Semantics.nextFor P c = some a) :
    Shape (EmbC.Semantics.stateKernelState c).mem (EmbC.Semantics.stateKernelState a.target).mem := by
  cases c with
  | regular s env mem orc k =>
    cases s <;> simp only [EmbC.Semantics.nextFor, EmbC.Semantics.nextCore,
      EmbC.Semantics.returnTarget] at h
    all_goals repeat' split at h
    all_goals cases h
    all_goals simp only [EmbC.Semantics.Action.target, EmbC.Semantics.stateKernelState]
    all_goals first
      | exact Shape.refl _
      | exact Shape.storeArr (by assumption)
      | exact Shape.storeField (by assumption)
  | callstate f vs mem orc k =>
    cases f <;> simp only [EmbC.Semantics.nextFor, EmbC.Semantics.nextCore] at h
    all_goals repeat' split at h
    all_goals cases h
    all_goals simp only [EmbC.Semantics.Action.target, EmbC.Semantics.stateKernelState]
    all_goals first
      | exact Shape.refl _
      | exact Ext.run_shape (by assumption)
  | returnstate rv mem orc k =>
    cases k <;> simp only [EmbC.Semantics.nextFor, EmbC.Semantics.nextCore] at h
    all_goals repeat' split at h
    all_goals cases h
    all_goals exact Shape.refl _

theorem source_rawStar_shape {P : Prog} {c c' : (EmbC.Semantics.ExecState P State)}
    (h : EmbC.Semantics.RawStar (EmbC.Semantics.rawStepFor P) c c') :
    Shape (EmbC.Semantics.stateKernelState c).mem (EmbC.Semantics.stateKernelState c').mem := by
  induction h with
  | refl => exact Shape.refl _
  | step _ _ _ hs _ ih =>
    obtain ⟨a, hn, rfl⟩ := hs
    exact (source_next_shape hn).trans ih

/-- A whole function run preserves shapes. -/
theorem run_shape {P : Prog} {fuel : Nat} {f : String} {vs : List Val} {st st' : (KernelState P State)}
    {rv : Option Val} (h : P.run fuel f vs st = .ok (rv, st')) : Shape st.mem st'.mem :=
  source_rawStar_shape (EmbC.Semantics.run_ok_path h)

/-- Any specification may be strengthened with `Shape`. -/
theorem FnSpec.withShape {P : Prog} {f : String} {pre : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop} (h : FnSpec (State := State) P f pre post) :
    FnSpec (State := State) P f pre (fun vs s rv s' => post vs s rv s' ∧ Shape s.mem s'.mem) := by
  intro fuel vs st hpre
  have := h fuel vs st hpre
  split at this
  · trivial
  · exact this.elim
  · rename_i rv st' hr
    exact ⟨this, run_shape hr⟩

/-- Weakening a postcondition, using the precondition. -/
theorem FnSpec.mono {P : Prog} {f : String} {pre : List Val → (KernelState P State) → Prop}
    {post post' : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop} (h : FnSpec (State := State) P f pre post)
    (hq : ∀ vs s rv s', pre vs s → post vs s rv s' → post' vs s rv s') :
    FnSpec (State := State) P f pre post' := by
  intro fuel vs st hpre
  have := h fuel vs st hpre
  split at this
  · trivial
  · exact this.elim
  · exact hq _ _ _ _ hpre this

/-! ## `copy_from_bpfptr` fills a whole block -/

theorem fill_fold_get (vs : List Val) : ∀ (k : Nat) (cells : Array Val) (i : Nat),
    k + vs.length ≤ cells.size →
    ((vs.zipIdx k).foldl (fun cells (p : Val × Nat) => cells.setIfInBounds (0 + p.2) p.1) cells)[i]? =
      if k ≤ i ∧ i < k + vs.length then vs[i - k]? else cells[i]? := by
  induction vs with
  | nil => intro k cells i _; simp; intro h1 h2; omega
  | cons v rest ih =>
    intro k cells i hsz
    rw [List.zipIdx_cons, List.foldl_cons]
    rw [ih (k + 1) _ i (by simp at hsz ⊢; omega)]
    simp only [List.length_cons, Nat.zero_add, Array.getElem?_setIfInBounds]
    by_cases hik : i = k
    · subst hik
      have h1 : ¬ (i + 1 ≤ i ∧ i < i + 1 + rest.length) := by omega
      have h2 : i ≤ i ∧ i < i + (rest.length + 1) := by omega
      have h3 : i < cells.size := by simp at hsz; omega
      simp only [h1, h2, h3, ↓reduceIte, Nat.sub_self]
      rfl
    · by_cases h1 : k + 1 ≤ i ∧ i < k + 1 + rest.length
      · have : k ≤ i ∧ i < k + (rest.length + 1) := by omega
        simp only [h1, this, and_self, ↓reduceIte]
        obtain ⟨j, rfl⟩ : ∃ j, i = k + 1 + j := ⟨i - (k + 1), by omega⟩
        rw [show k + 1 + j - k = j + 1 by omega, List.getElem?_cons_succ]
        congr 1; omega
      · have : ¬ (k ≤ i ∧ i < k + (rest.length + 1)) := by omega
        simp only [h1, this, ↓reduceIte, Ne.symm hik]

/-- Filling a block from offset 0 with exactly as many values as it has cells. -/
theorem fill_fold_full (vs : List Val) (cells : Array Val) (h : cells.size = vs.length) :
    (vs.zipIdx).foldl (fun cells (p : Val × Nat) => cells.setIfInBounds (0 + p.2) p.1) cells =
      vs.toArray := by
  apply Array.ext_getElem?
  intro i
  rw [fill_fold_get vs 0 cells i (by omega)]
  by_cases hi : i < vs.length
  · simp [hi]
  · simp only [Nat.zero_le, Nat.zero_add, hi, and_false, ↓reduceIte]
    rw [Array.getElem?_eq_none (by omega)]
    simp; omega

theorem Mem.block?_fill_full {m : Mem} {b : Nat} {t : Ty} {cells : Array Val} {vs : List Val}
    (hb : m.block? b = some ⟨t, cells⟩) (h : cells.size = vs.length) (b' : Nat) :
    (m.fill b 0 vs).block? b' = if b' = b then some ⟨t, vs.toArray⟩ else m.block? b' := by
  have hb2 := Mem.block?_eq.mp hb
  unfold Mem.fill Mem.block?
  rw [Array.getElem?_modify]
  by_cases hbb : b' = b
  · subst hbb
    simp only [↓reduceIte, hb2, Option.map_some]
    have := fill_fold_full vs cells h
    simp only [this]
  · simp only [Ne.symm hbb, ↓reduceIte, hbb]

/-! ## Freeing the checker's arrays -/

/-- While `ck_free` runs: the arrays in `A` have been freed, the others are
still live, nothing else changed. -/
structure Freeing (W : World) (sb : Nat) (c : CMem) (m : Mem) (A : List Arr) : Prop where
  ck : HasCK m sb c.k
  sbNew : W.base.blocks.size ≤ sb
  pbOld : W.pb < W.base.blocks.size
  proof : HasArr m W.pb c.proof
  arr : ∀ a b o, a ∉ A → c.k.ptr a = some (b, o) →
    o = 0 ∧ b ≠ sb ∧ W.base.blocks.size ≤ b ∧ (m.block? b).isSome
  sep : ∀ a a' b b' o o', a ≠ a' → c.k.ptr a = some (b, o) → c.k.ptr a' = some (b', o') → b ≠ b'
  out : ∀ b, b < W.base.blocks.size → b ≠ W.pb → m.block? b = W.base.block? b
  exact : ∀ b, W.base.blocks.size ≤ b → b ≠ sb → (∀ a o, a ∉ A → c.k.ptr a ≠ some (b, o)) →
    m.block? b = W.aux b
  auxOwned : ∀ a b o, c.k.ptr a = some (b, o) → W.aux b = none

theorem Holds.freeing {W : World} {m : Mem} {sb : Nat} {c : CMem} (h : Holds W m sb c) :
    Freeing W sb c m [] where
  ck := h.ck
  sbNew := h.sbNew
  pbOld := h.pbOld
  proof := h.proof
  arr := fun a b o _ hp => by
    obtain ⟨h1, h2, h3, h4⟩ := h.arr a b o hp
    exact ⟨h1, h2, h3, by rw [h4]; rfl⟩
  sep := h.sep
  out := h.out
  exact := fun b h1 h2 h3 => h.exact b h1 h2 (fun a o => h3 a o List.not_mem_nil)
  auxOwned := fun _ _ _ hp => h.aux_owned hp

/-- `kvfree` of one more array. -/
theorem Freeing.step {P : Prog} {W : World} {sb : Nat} {c : CMem} {st : (KernelState P State)} {A : List Arr}
    (h : Freeing W sb c st.mem A) (a : Arr) (ha : a ∉ A) :
    ∃ after : KernelState P State,
      Ext.run P .kvfree [(c.k.ptr a).val] st = some (none, after) ∧
      Freeing W sb c after.mem (a :: A) := by
  cases hp : c.k.ptr a with
  | none =>
    obtain ⟨rv, after, hr⟩ := Ext.run_defined (P := P) (st := st)
      (show Kernel.Defined P ⟨.kvfree, [.null], st.mem⟩ from trivial)
    have ha := Ext.run_spec hr
    have he := ha.kvfree_null
    rcases after with ⟨mem, world⟩
    simp only at he
    rcases he with ⟨rfl, rfl⟩
    refine ⟨⟨st.mem, world⟩, by simpa [Ptr.val] using hr,
      h.ck, h.sbNew, h.pbOld, h.proof, ?_, h.sep, h.out, ?_, h.auxOwned⟩
    · intro a' b o ha' hp'
      exact h.arr a' b o (fun hm => ha' (List.mem_cons_of_mem _ hm)) hp'
    · intro b h1 h2 h3
      refine h.exact b h1 h2 (fun a' o ha' => ?_)
      by_cases e : a' = a
      · subst e; rw [hp]; simp
      · exact h3 a' o (by simp [e, ha'])
  | some bo =>
    obtain ⟨b, o⟩ := bo
    obtain ⟨rfl, hbs, hbb, hlive⟩ := h.arr a b o ha hp
    obtain ⟨blk, hblk⟩ : ∃ blk, st.mem.block? b = some blk := Option.isSome_iff_exists.mp hlive
    have hfree := fun b' => Mem.block?_free (m := st.mem) (b := b) b'
    obtain ⟨rv, after, hr⟩ := Ext.run_defined (P := P) (st := st)
      (show Kernel.Defined P ⟨.kvfree, [.ptr b 0], st.mem⟩ from ⟨rfl, blk, hblk⟩)
    have ha := Ext.run_spec hr
    have he := ha.kvfree_ptr
    rcases after with ⟨mem, world⟩
    simp only at he
    rcases he with ⟨rfl, rfl⟩
    refine ⟨⟨st.mem.free b, world⟩, by simpa [Ptr.val] using hr,
      ?_, h.sbNew, h.pbOld, ?_, ?_, h.sep, ?_, ?_, h.auxOwned⟩
    · show (st.mem.free b).block? sb = _
      rw [hfree]; simp [Ne.symm hbs]; exact h.ck
    · show (st.mem.free b).block? W.pb = _
      have : W.pb ≠ b := by have := h.pbOld; omega
      rw [hfree]; simp [this]; exact h.proof
    · intro a' b' o' ha' hp'
      have ha'' : a' ∉ A := fun hm => ha' (List.mem_cons_of_mem _ hm)
      have hne : a' ≠ a := fun e => ha' (by simp [e])
      obtain ⟨h1, h2, h3, h4⟩ := h.arr a' b' o' ha'' hp'
      have : b' ≠ b := h.sep a' a b' b o' 0 hne hp' hp
      refine ⟨h1, h2, h3, ?_⟩
      rw [hfree]; simp [this, h4]
    · intro b' h1 h2
      have : b' ≠ b := by omega
      rw [hfree]; simp [this]; exact h.out b' h1 h2
    · intro b' h1 h2 h3
      rw [hfree]
      by_cases e : b' = b
      · simp only [e, ↓reduceIte]; exact (h.auxOwned a b 0 hp).symm
      · simp only [e, ↓reduceIte]
        refine h.exact b' h1 h2 (fun a' o' ha' => ?_)
        by_cases e2 : a' = a
        · subst e2; rw [hp]; simp [Ne.symm e]
        · exact h3 a' o' (by simp [e2, ha'])

/-- After `ck_free`: the struct and the proof block as before, every array freed. -/
structure Freed (W : World) (sb : Nat) (c : CMem) (m : Mem) : Prop where
  ck : HasCK m sb c.k
  sbNew : W.base.blocks.size ≤ sb
  pbOld : W.pb < W.base.blocks.size
  proof : HasArr m W.pb c.proof
  out : ∀ b, b < W.base.blocks.size → b ≠ W.pb → m.block? b = W.base.block? b
  exact : ∀ b, W.base.blocks.size ≤ b → b ≠ sb → m.block? b = W.aux b

theorem Freeing.freed {W : World} {sb : Nat} {c : CMem} {m : Mem}
    (h : Freeing W sb c m [.lr, .prem, .stk, .facts, .htab, .pool]) : Freed W sb c m where
  ck := h.ck
  sbNew := h.sbNew
  pbOld := h.pbOld
  proof := h.proof
  out := h.out
  exact := fun b h1 h2 => h.exact b h1 h2 (fun a o ha => by cases a <;> simp at ha)

def CkFreeSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem),
    FnSpec (State := State) Vbcf.prog "ck_free"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c)
      (fun _ _ rv s' => rv = none ∧ Freed W sb c s'.mem)

theorem ck_free_spec : CkFreeSpec (State := State) := by
  intro W sb c
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckFree) rfl
  rintro vs s ⟨rfl, h⟩
  simp [ckFree, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [initLocals, List.map]
  have h0 := h.freeing
  -- one `kvfree(st->F)`
  have step : ∀ (a : Arr) (A : List Arr) (s1 : (KernelState prog State)) (Q : (Post prog State)) (f : String),
      Freeing W sb c s1.mem A → a ∉ A →
      s1.mem.loadField Vbcf.prog sb f = some (c.k.ptr a).val →
      (∀ s2, Freeing W sb c s2.mem (a :: A) → Q .normal [("st", .ptr (.struct "ck"), .ptr sb 0)] s2) →
      WP Vbcf.prog (.ecall none .kvfree [.field (.var "st") f]) Q
        [("st", .ptr (.struct "ck"), .ptr sb 0)] s1 := by
    intro a A s1 Q f hF ha hld hk
    obtain ⟨after, hrun, hF'⟩ := hF.step (P := Vbcf.prog) a ha
    apply WP.ecall
    embc_simp [hld, hrun]
    exact hk _ hF'
  apply WP.seq
  apply step .pool [] s _ _ h0 (by simp) (HasCK.ld_pool hs h0.ck)
  intro s1 h1
  apply WP.seq
  apply step .htab _ s1 _ _ h1 (by simp) (HasCK.ld_htab hs h1.ck)
  intro s2 h2
  apply WP.seq
  apply step .facts _ s2 _ _ h2 (by simp) (HasCK.ld_facts hs h2.ck)
  intro s3 h3
  apply WP.seq
  apply step .stk _ s3 _ _ h3 (by simp) (HasCK.ld_stk hs h3.ck)
  intro s4 h4
  apply WP.seq
  apply step .prem _ s4 _ _ h4 (by simp) (HasCK.ld_prem hs h4.ck)
  intro s5 h5
  apply step .lr _ s5 _ _ h5 (by simp) (HasCK.ld_lr hs h5.ck)
  intro s6 h6
  simp only [retPost]
  exact ⟨by simp, h6.freed⟩

end Vbcf.Proof
