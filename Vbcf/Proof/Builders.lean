import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Builders1
import Vbcf.Proof.Builders2
import Vbcf.Proof.Builders3
import Vbcf.Proof.Builders4

/-!
# Vbcf proofs: pool growth, the node builders, and two accessors

* `Builders1`: pure lemmas — frames (`PoolFrame.trans`, `StkFrame.trans`, `CoreInv.stkFrame`),
  changes above `plen` (`TailEq`, `wr`, `CoreInv.tailEq`), candidates (`Written`, `cand_boolVal`,
  `cand_bvVal`), and carrying facts across a call (`RInv.push`, `RInv.stkFrame`, `StkIds.*`, …).
* `Builders2`: `wp_intern_ret`, `mk1_spec`, `mk2_spec`, `mk3_spec`, `mk0_bool_spec`,
  `mk_eq_spec`, `mk_not_spec`.
* `Builders3`: `mkn_spec`, `mkval_spec'` (`MkvalSpec'`), `mkval_spec_lt` (`MkvalSpecLt`).
* `Builders4`: `expr_at_spec'` (`ExprAtSpec'`), `push_args_spec` (`PushArgsSpec`),
  `ck_room_spec`.

Below: with `ck_room` proved, every builder depends on `ck_intern` (`InternSpec`) only.
-/

namespace Vbcf.Proof

variable {State : Type}

theorem mk0_bool_of_intern (hI : InternSpec (State := State)) : Mk0BoolSpec (State := State) := mk0_bool_spec hI ck_room_spec
theorem mk1_of_intern (hI : InternSpec (State := State)) : Mk1Spec (State := State) := mk1_spec hI ck_room_spec
theorem mk2_of_intern (hI : InternSpec (State := State)) : Mk2Spec (State := State) := mk2_spec hI ck_room_spec
theorem mk3_of_intern (hI : InternSpec (State := State)) : Mk3Spec (State := State) := mk3_spec hI ck_room_spec
theorem mkn_of_intern (hI : InternSpec (State := State)) : MknSpec (State := State) := mkn_spec hI ck_room_spec
theorem mkval_of_intern (hI : InternSpec (State := State)) : MkvalSpec' (State := State) := mkval_spec' hI ck_room_spec
theorem mkval_lt_of_intern (hI : InternSpec (State := State)) : MkvalSpecLt (State := State) := mkval_spec_lt hI ck_room_spec
theorem mk_eq_of_intern (hI : InternSpec (State := State)) : MkEqSpec (State := State) := mk_eq_spec (mk2_of_intern hI)
theorem mk_not_of_intern (hI : InternSpec (State := State)) : MkNotSpec (State := State) := mk_not_spec (mk1_of_intern hI)

end Vbcf.Proof
