import Vbcf.Proof.Tyck1
import Vbcf.Proof.Tyck2
import Vbcf.Proof.Tyck3

/-!
# Vbcf proofs: the type checker (`ty_of`, `ck_all_ty`, `ck_sum_bv`, `ck_tyck`)

* `Tyck1.lean`: `ty_of_spec`, `ck_all_ty_spec`, `ck_sum_bv_spec`; the truth-value
  normal form `bw` and the tactic `tk_simp`; `WP.ifRet`.
* `Tyck2.lean`: the pure part of `ck_tyck`: for each accepting `return`, the candidate
  is the encoding of a typed node (`TCtx.bvVar` … `TCtx.listBv`).
* `Tyck3.lean`: the symbolic execution, `ck_tyck_spec : TyckSpecT`.

`TyckSpecT` is `TyckSpec` with `CandRaw` strengthened to `CandRawT`: the identity word
of a variable candidate must be a position below `2^32` (otherwise `Fits` cannot hold).
-/
