import Vbcf.Proof.Rewrite1
import Vbcf.Proof.Rewrite2
import Vbcf.Proof.Rewrite3
import Vbcf.Proof.Rewrite4
import Vbcf.Proof.Rewrite5
import Vbcf.Proof.Rewrite6
import Vbcf.Proof.Rewrite7
import Vbcf.Proof.Rewrite8
import Vbcf.Proof.Rewrite9
import Vbcf.Proof.Rewrite10
import Vbcf.Proof.Rewrite11
import Vbcf.Proof.Rewrite12

/-!
# Vbcf proofs: the Rewrite family

`r_rewrite_spec : RuleSpec "r_rewrite" (fun X st pr pa => ruleRewrite rwTable X.bi X.ei st pr pa)`
(`Rewrite12`), the `rewrite` field of `RuleSpecs`.

* `Rewrite1`: the constant table on the Lean side — `RwAt` (words at an offset), the generic
  decoding of `RwEnc.encTable` (`rw_tbl_index`, `rw_rec`, `rw_head`), the two table facts proved
  by evaluation (`rw_words_len`: fewer than `2^16` words; `rw_tbl_wf_all`: variable numbers below
  256, literals below `2^32`, `BV(w)` widths below `2^16`), reading `@rw_tbl[i]` in C
  (`rw_findConst`, `rw_tbl_get`), and `cval = memoVal` (`rw_cval_eq`).
* `Rewrite2`: `rw_const`, `rw_lit`, `rw_ty_ok`, `rw_cond_match`, `rw_splice`.
* `Rewrite3`: `rw_app` (`pushApp`; the width comes from the typing of the built node).
* `Rewrite4`: `rw_sym`, `rw_max`, `rw_ext`, `rw_ite`, `rw_extract` (the ends of `instE`).
* `Rewrite5`-`Rewrite8`: `rw_inst` (`instE`/`instA`), by strong induction on the depth:
  infrastructure and statement (`RwInstSpecD`, `RwB`), leaf cases, cases with sub-patterns,
  the `RW_APP` case and **`rw_inst_spec`**.
* `Rewrite9`: `rw_params` (`paramsOK`), `rw_cond_one`, `rw_check_cond` (`checkCond`).
* `Rewrite10`: `rw0_and_half`, `rw0_and_split`, `rw0_repeat`, `rw0_distinct`, `rw_zero`.
* `Rewrite11`, `Rewrite12`: `r_rewrite`.
-/
