import Vbcf.Proof.Bitblast1
import Vbcf.Proof.Bitblast2
import Vbcf.Proof.Bitblast3
import Vbcf.Proof.Bitblast4
import Vbcf.Proof.Bitblast5
import Vbcf.Proof.Bitblast6
import Vbcf.Proof.Bitblast7
import Vbcf.Proof.Bitblast8
import Vbcf.Proof.Bitblast9
import Vbcf.Proof.Bitblast10
import Vbcf.Proof.Bitblast11
import Vbcf.Proof.Bitblast12
import Vbcf.Proof.Bitblast13
import Vbcf.Proof.Bitblast14

/-!
# Vbcf proofs: the Bitblast family (`Vbcf/Rules/Bitblast.lean`)

One `FnSpec` per C helper, stated on the Lean checker function it mirrors
(`Bcf/Bitblast.lean`), and **`r_bitblast_spec`**, with exactly the type of the
`bitblast` field of `RuleSpecs`.  No function of the family builds a node, so the
Lean state never changes; bit lists live either in place (the argument words of a
`from_bool` node) or on the scratch stack (`BbRange`, `StkTop`).

* `Bitblast1`: read-only helpers (`BbOK`, `WP.bb_call`, `BbInv`/`bbSets` loop invariants,
  `WP.bb_loop`, header tests `CoreInv.bb_hdr*`), `bb_nargs`, `bb_is1`, `bb_is2`, `bb_var`,
  `bb_val`, `bb_ite_bit`, `bb_ite`.
* `Bitblast2`: stack ranges (`BbRange`), `bb_zip_not`, `bb_list_eq`, pushing helpers
  (`BbPush`, `BbPushInv`), `bb_pre` (`preSum`/`preAdder`), `bb_carry`, `bb_ripple`.
* `Bitblast3`: `BbChk` (checks that use the stack), `bb_neg`, `bb_sub`.
* `Bitblast4`: `WP.bb_push_args`, `bb_add`.  `Bitblast5`: `bb_bitwise`.
* `Bitblast6`: `bb_concat`, `bb_extract`, `bb_sext`.
* `Bitblast7`: `bb_ult_base`, `bb_ult`, `bb_slt`.
* `Bitblast8`: `bb_is_fill`, `bb_shift_limit`, `bb_log2`.
* `Bitblast9`: `bb_lsh_stage`, `bb_rsh_stage`.  `Bitblast10`: `bb_shift`.
* `Bitblast11`: `bbTerm` per operator.  `Bitblast12`: `bb_term`.
* `Bitblast13`: `bb_eq_bits`, `bb_atom`.  `Bitblast14`: **`r_bitblast_spec`**.
-/
