import EmbC.Kernel
import Vbcf.Prog
import Lean

/-!
# Vbcf cost proofs: the registry of cost lemmas

An environment extension (it must live in a module imported by its users).
-/

namespace Vbcf.Proof

variable {State : Type}
open Lean

/-- The registered cost lemmas: the function's name, the `rfl` facts
`prog.findFn name = some fn` and `fn.params = …`, and the cost lemma. -/
initialize fncostRegistry : SimplePersistentEnvExtension (String × Name × Name × Name)
    (List (String × Name × Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun l e => e :: l
    addImportedFn := fun as => (as.toList.map (·.toList)).flatten }

end Vbcf.Proof
