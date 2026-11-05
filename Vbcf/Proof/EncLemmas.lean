import Vbcf.Proof.EncLemmas1
import Vbcf.Proof.EncLemmas2
import Vbcf.Proof.EncLemmas3

/-!
# Vbcf proofs: lemmas about the encoding of the pool

Pure Lean facts about the definitions of `Vbcf/Enc.lean` and `Vbcf/Proof/Spec.lean`,
used to verify the C checker.  No C semantics here.

* `EncLemmas1`: offsets (`offs`), node words (`nodeW`, `tailW`, `IsLeaf`), `PoolRep`
  (reads, push, prefix stability), and `posOfRaw`.
* `EncLemmas2`: header arithmetic (`hdrW`), the `BitVec 32` bridge, and one
  characterisation `opC_<ctor>_iff` per operator.
* `EncLemmas3`: inversion of the typing combinators, arities (`minArity`, `fixedArity`),
  `Typed`, the type encoding (`tyOfM`, `tyOfB`, `tyW`, `TyFits`), and injectivity of the
  node encoding (`nodeW_inj`).
-/
