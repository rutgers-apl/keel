import Vbcf.Proof.Poly1
import Vbcf.Proof.Poly2
import Vbcf.Proof.Poly3
import Vbcf.Proof.Poly4
import Vbcf.Proof.Poly5
import Vbcf.Proof.Poly6
import Vbcf.Proof.Poly7
import Vbcf.Proof.Poly8
import Vbcf.Proof.Poly9
import Vbcf.Proof.Poly10

/-!
# Vbcf proofs: the Poly family (`Vbcf/Rules/Poly.lean`)

* `Poly1`: the Lean side — `plEnc` (a `Lin w` as stack words) and its injectivity
  (`plEnc_inj`), `LinOK` (atoms are nodes; `lin_ok`), `mergeTerms` one step at a time,
  `lin` unfolded per operator (`pl_lin_*`).
* `Poly2`: `PlStkW`, `PlRet` (what a pushing helper leaves; `PlRet.trans`),
  `lin_push64_spec`, `lin_get64_spec`, `lin_term_spec`, `lin_atom_spec`,
  `poly_lit_val_spec` (exact: fails iff `litVal` is `none`).
* `Poly3`: `lin_scale_spec` (`Lin.scale`, in place).
* `Poly4`: `lin_add_spec` (`Lin.add`, the merge of `mergeTerms`, then the move down).
* `Poly5`–`Poly8`: `lin_f`: the body cut into `plT0`…`plT5`, one lemma per operator,
  and **`lin_f_spec : LinFSpec`** by induction on the depth argument.
* `Poly9`: **`r_poly_norm_spec`**.
* `Poly10`: `odd_mul_sub_spec`, **`r_poly_norm_eq_spec`**.
-/
