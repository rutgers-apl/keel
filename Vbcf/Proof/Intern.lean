import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Hash
import Vbcf.Proof.Builders

/-!
# Vbcf proofs: the unconditional interning and builder specifications

`Hash6` proves `ck_intern` against `CoreInv'` (`CoreInv` plus the slot
count); since `HtabOK.nz` now carries the slot count, `CoreInv` itself is
enough, and every builder specification follows without hypotheses.

* `ck_intern_dspec`, `mk*_dspec`, … — the structural contracts (`InternSpecD`,
  `DMk1Spec`, …: the effect on the ghost pool is described by `Interned`), used by
  the direct proof;
* `ck_intern_specT`, `mk*_specT`, … — the refinement proof's contracts (`pushNode`).
-/

namespace Vbcf.Proof

variable {State : Type}

/-- **`ck_intern` meets its structural contract**, proved against the C body
(`ck_intern_spec` in `Hash6`). -/
theorem ck_intern_dspec : InternSpecD (State := State) := by
  intro W sb c posOf st
  refine FnSpec.of_post (FnSpec.of_pre (ck_intern_spec W sb c posOf st) ?_) ?_
  · rintro vs s ⟨hv, h, hinv, hraw⟩
    exact ⟨hv, h, ⟨hinv, hinv.htab.nz⟩, hraw⟩
  · rintro vs s rv s' ⟨c', r, hrv, h, hf, hres⟩
    refine ⟨c', r, hrv, h, hf, ?_⟩
    rcases hres with ⟨hr, hinv⟩ | ⟨n, st', i, hc, hp, hinv, hr, hne⟩
    · exact Or.inl ⟨hr, hinv.core⟩
    · exact Or.inr ⟨st', i, ⟨n, hc, hp⟩, hinv.core, hr, hne⟩

theorem mk0_bool_dspec : DMk0BoolSpec (State := State) := mk0_bool_spec_d ck_intern_dspec ck_room_spec
theorem mk1_dspec : DMk1Spec (State := State) := mk1_spec_d ck_intern_dspec ck_room_spec
theorem mk2_dspec : DMk2Spec (State := State) := mk2_spec_d ck_intern_dspec ck_room_spec
theorem mk3_dspec : DMk3Spec (State := State) := mk3_spec_d ck_intern_dspec ck_room_spec
theorem mkn_dspec : DMknSpec (State := State) := mkn_spec_d ck_intern_dspec ck_room_spec
theorem mkval_dspec' : DMkvalSpec' (State := State) := mkval_spec_d' ck_intern_dspec ck_room_spec
theorem mkval_lt_dspec : DMkvalSpec (State := State) := mkval_spec_lt_d ck_intern_dspec ck_room_spec

theorem ck_intern_specT : InternSpec (State := State) :=
  ck_intern_specT_of_nz (fun _ _ _ h => h.htab.nz)

theorem mk0_bool_specT : Mk0BoolSpec (State := State) := mk0_bool_of_intern ck_intern_specT
theorem mk1_specT : Mk1Spec (State := State) := mk1_of_intern ck_intern_specT
theorem mk2_specT : Mk2Spec (State := State) := mk2_of_intern ck_intern_specT
theorem mk3_specT : Mk3Spec (State := State) := mk3_of_intern ck_intern_specT
theorem mkn_specT : MknSpec (State := State) := mkn_of_intern ck_intern_specT
theorem mkval_specT : MkvalSpec' (State := State) := mkval_of_intern ck_intern_specT
theorem mkval_lt_specT : MkvalSpecLt (State := State) := mkval_lt_of_intern ck_intern_specT
theorem mk_eq_specT : MkEqSpec (State := State) := mk_eq_of_intern ck_intern_specT
theorem mk_not_specT : MkNotSpec (State := State) := mk_not_of_intern ck_intern_specT

end Vbcf.Proof
