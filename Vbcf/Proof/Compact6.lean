import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact5

/-!
# Vbcf proofs: `ck_compact`, part 6 — marking everything reachable

The worklist loop pops a marked node, and for an inner node marks (and
pushes) each unmarked child at or above `lo`.  When the stack is empty every
marked node has all its children (at or above `nL`) marked.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem leaf_code {op : Op} (h : IsLeaf op) :
    opC op = 0x18 ∨ opC op = 0x19 ∨ opC op = 0x08 ∨ opC op = 0x09 := by
  cases op <;> simp [IsLeaf, isLeaf, opC] at h ⊢

theorem leaf_of_code {op : Op} (h : opC op = 0x18 ∨ opC op = 0x19 ∨ opC op = 0x08 ∨ opC op = 0x09) :
    IsLeaf op := by
  cases op <;> simp [IsLeaf, isLeaf, opC] at h ⊢

/-- A leaf of a `PoolOK` state has no children. -/
theorem PoolOK.leaf_args {cs : St} (hok : PoolOK cs) {y : Nat} {n : Node} (hn : cs.pool[y]? = some n)
    (hl : IsLeaf n.op) : n.args.size = 0 := by
  obtain ⟨argTys, t, -, hrt, -, hlen⟩ := hok.retype hn
  have := resultTy_leaf hl hrt
  subst this
  simp at hlen; omega

theorem ofNat32_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a = BitVec.ofNat 32 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [bv_toNat_ofNat ha, bv_toNat_ofNat hb] at this
  · intro h; rw [h]

section
variable {cs : St} {nL : Nat} {c0 c : CMem} {fw : Array EmbC.Val}

theorem MarkInv.weaken {pend pend' : Nat → Prop} (hM : MarkInv cs nL c0 c fw pend)
    (h : ∀ y, pend y → pend' y) : MarkInv cs nL c0 c fw pend' :=
  ⟨hM.fr, hM.stk, hM.size, hM.cells, hM.onStk, fun y h1 h2 h3 => by
    rcases hM.todo y h1 h2 h3 with a | b | d
    · exact Or.inl a
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (h y d))⟩

theorem MarkInv.finish {pend : Nat → Prop} (hM : MarkInv cs nL c0 c fw pend)
    (h : ∀ y, pend y → Done cs.pool nL fw y) : MarkInv cs nL c0 c fw (fun _ => False) :=
  ⟨hM.fr, hM.stk, hM.size, hM.cells, hM.onStk, fun y h1 h2 h3 => by
    rcases hM.todo y h1 h2 h3 with a | b | d
    · exact Or.inl a
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inl (h y d))⟩

/-- Popping the top of the stack: it becomes the node being expanded. -/
theorem MarkInv.pop (hM : MarkInv cs nL c0 c fw (fun _ => False)) (hsp : 0 < c.k.sp.toNat)
    (hP : offs cs.pool cs.pool.size < 2 ^ 32)
    {y : Nat} (_hy : nL ≤ y) (hys : y < cs.pool.size)
    (hu : U c.stk (c.k.sp.toNat - 1) (offs cs.pool y)) :
    MarkInv cs nL c0 { c with k := { c.k with sp := c.k.sp - 1#32 } } fw (fun z => z = y) := by
  have hsp1 : (c.k.sp - 1#32).toNat = c.k.sp.toNat - 1 := by
    rw [bv_sub_toNat (by simp; omega)]; simp
  refine ⟨hM.fr.trans (by constructor <;> rfl), ⟨hM.stk.null, hM.stk.size, ?_⟩, hM.size, hM.cells,
    ?_, ?_⟩
  · have := hM.stk.cap
    exact ⟨by show (c.k.sp - 1#32).toNat ≤ c.k.scap.toNat; rw [hsp1]; omega, this.2⟩
  · intro p hp
    show ∃ y, _
    simp only [hsp1] at hp
    exact hM.onStk p (by omega)
  · intro z h1 h2 h3
    rcases hM.todo z h1 h2 h3 with ⟨p, hp, hpu⟩ | hd | hf
    · by_cases e : p = c.k.sp.toNat - 1
      · subst e
        right; right
        have hlt := offs_lt_end hys
        have hlt' := offs_lt_end h2
        have := U.inj32 hpu hu (by omega) (by omega)
        exact offs_inj (Nat.le_of_lt h2) (Nat.le_of_lt hys) this
      · left
        exact ⟨p, by show p < (c.k.sp - 1#32).toNat; rw [hsp1]; omega, hpu⟩
    · exact Or.inr (Or.inl hd)
    · exact hf.elim

end

end Vbcf.Proof
