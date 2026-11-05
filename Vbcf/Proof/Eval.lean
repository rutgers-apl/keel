import Vbcf.Proof.Eval1
import Vbcf.Proof.Eval2
import Vbcf.Proof.Eval3
import Vbcf.Proof.Eval4
import Vbcf.Proof.Eval5
import Vbcf.Proof.Eval6
import Vbcf.Proof.Eval7
import Vbcf.Proof.Eval8
import Vbcf.Proof.Eval9
import Vbcf.Proof.Eval10

/-!
# Vbcf proofs: the Eval family (`Vbcf/Rules/Eval.lean`)

* `Eval1`: infrastructure — `CMem.wev` (the state with only `work`/`err`/`val` changed),
  `WP.ck_setVal` (the `u64` store `st->val = e`), `memoVal` one level down, `CvRep`
  (result word and `st->val` represent a Lean value), the specs of `mask64`, `udiv_w`,
  `umod_w`, `sdiv_w`, `smod_w`, `CvalSpecD`/`CvalSpec`, and the pieces of `cval`'s body.
* `Eval2`: semantics of `ite`.  `Eval3`: `cv_simp`, `WP.cv_finish`, the `ite` group.
* `Eval4`: the one-argument group (semantics and `grpU_spec`).
* `Eval5`/`Eval6`: the two-argument group (semantics, `grpB_spec`).
* `Eval7`/`Eval8`: the n-ary group (the loop `grpN_loop`, folds, `grpN_spec`).
* `Eval9`: the body of `cval` (`cval_specD`) and **`cval_spec : CvalSpec`** by induction on
  the depth argument.
* `Eval10`: **`r_evaluate_spec`**, **`r_distinct_values_spec`**.
-/
