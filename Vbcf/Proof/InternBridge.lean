import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Interned

/-!
# Vbcf proofs: `Interned` and the functional checker's `pushNode`

Used only by the refinement proof (`Vbcf.Proof.Final`): on a well-formed ghost
state, the structural description `Interned` of interning is exactly what the
functional checker's `Bcf.pushNode` computes.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

section
variable {st st' : St} {n : Node} {i : Nat}

/-- `pushNode` interns. -/
theorem Interned.of_pushNode (hok : PoolOK st) (hp : pushNode st n = some (st', i)) :
    Interned st n st' i := by
  obtain ⟨argTys, t, hargs, hmap, ht, ⟨hst, hr⟩ | ⟨hst, hr, hnew⟩⟩ := pushNode_cases' hok hp
  · subst hst; exact Interned.found hok hr
  · refine ⟨⟨hargs, argTys, t, hmap, ht⟩, pushNode_get hp, Or.inr ⟨hr, hnew, argTys, t, hmap, ht, ?_⟩⟩
    subst hst
    simp [St.append_eq]

/-- What `Interned` describes is what `pushNode` computes. -/
theorem Interned.pushNode_eq (hok : PoolOK st) (h : Interned st n st' i) :
    pushNode st n = some (st', i) := by
  rcases h.shape with rfl | ⟨hi, hnew, argTys, t, hmap, ht, hp, htys, hidx, hf⟩
  · exact pushNode_found hok h.get
  · subst hi
    have hst : st' = (st.append n t).1 := by
      rw [St.append_eq]
      cases st'
      simp only at hp htys hidx hf
      subst hp htys hidx hf
      rfl
    subst hst
    have hargs := h.typed.1
    unfold pushNode
    simp only [hargs, ↓reduceIte, hmap, ht]
    split
    · rename_i r _
      have : st.pool[r]? ≠ some n := hnew r
      simp only [this, ↓reduceIte]
      rw [St.append_eq]
    · rw [St.append_eq]

end

end Vbcf.Proof
