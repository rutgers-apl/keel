import Vbcf.Proof.Clause1
import Vbcf.Proof.Clause2
import Vbcf.Proof.Clause3
import Vbcf.Proof.Clause4
import Vbcf.Proof.Clause5
import Vbcf.Proof.Clause6

/-!
# Vbcf proofs: the Clause family (`Vbcf/Rules/Clause.lean`)

* `Clause1`: the Lean side — `resolveChain` as a fold (`clRfold`), `parseDupPairs` through its
  loop state (`clPd`, `clPd_ge`/`clPd_zero`/`clPd_step`), `keptLits` on a prefix (`clKept`),
  `applySwaps` as a fold of swaps (`applySwaps_eq_fold`, `clSwaps_perm`); word lemmas `cw_*`.
* `Clause2`: scratch-stack lemmas (`RCtx.stk_eq`, `RCtx.set_stk`, `RCtx.set_sp`, `StkTop.split`,
  `StkTop.join`), `cl_byte_spec`, `cl_half_spec`, `cl_lits_spec`, `cl_erase_spec`.
* `Clause3`: `r_resolution_spec`.
* `Clause4`: `r_reordering_spec`.
* `Clause5`: `cl_dups_spec`.
* `Clause6`: `r_factoring_spec`.
-/
