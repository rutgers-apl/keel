import Vbcf.Proof.CostAci
import Vbcf.Proof.CostLeaf
import Vbcf.Proof.CostCore2
import Vbcf.Proof.CostBool
import Vbcf.Proof.CostBool2
import Vbcf.Proof.CostMid
import Vbcf.Proof.CostReplay
import Vbcf.Proof.CostCompact
import Vbcf.Proof.CostLive
import Vbcf.Proof.CostCompact2
import Vbcf.Proof.CostTop
import Vbcf.Proof.CostEvalRw
import Vbcf.Proof.CostRules
import Vbcf.Proof.CostRule
import Vbcf.Proof.CostFinal

/-!
# Vbcf cost proofs

The cost of each checker function, as an `EmbC.FnCost` (`EmbC/Cost.lean`):
the call finishes, and its cost — machine transitions plus kernel-call work
(`t`), and words obtained from the allocator (`m`) — is bounded.  Combined
with the partial-correctness specifications by `EmbC.FnCost.run`.

* `CostBase`: what a cost proof tracks (`Fld`, the budget cells `Budget`).
* `CostAuto`: the amortised specification `Amort`, the registry of cost
  lemmas (`fncost_register`) and the automation (`wpc_auto`, `wpc_call`,
  `wpc_finish`).
* `CostCore`: `tick`, `spend`, `words_eq`, `push`.
* `CostAci`: `aci_absorb` and its helpers.
* `CostCompact`, `CostLive`, `CostCompact2`: `ck_compact` (cells beyond the
  budget: frame lemmas for `spend`/`push`, `TypedU32`).
-/
