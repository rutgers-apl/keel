import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Tyck

/-!
# Vbcf proofs: corrected interning specification

`CandRaw` in `Specs.lean` originally omitted that a variable's identity word is below
`2^32` (found while proving `ck_tyck`; see `CandRawT` in `Tyck2.lean`).
`InternSpecT` is `InternSpec` with the corrected precondition.  Proofs of
`ck_intern` and of its callers should use this version; `CandRaw.toT_nonvar`
converts for every non-variable candidate.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-- Historical name: `InternSpec` now carries the corrected `CandRaw`. -/
abbrev InternSpecT : Prop := InternSpec (State := State)

end Vbcf.Proof
