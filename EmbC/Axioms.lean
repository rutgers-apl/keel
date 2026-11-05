import EmbC.Examples.Vec
import EmbC.Semantics.Correctness
import EmbC.Cost

/-! Axiom audit of the EmbC stage-1 and operational cost theorems. Expect only
`propext`, `Classical.choice` and `Quot.sound`. -/
#print axioms EmbC.Examples.prog_wordsEq
#print axioms EmbC.Examples.vecPush_spec
#print axioms EmbC.Examples.prog_vecPush2

#print axioms EmbC.Semantics.runnerCorrect
#print axioms EmbC.Semantics.ValidFor.append_call
#print axioms EmbC.WP.while
#print axioms EmbC.WP.call
#print axioms EmbC.FnSpec.intro

#print axioms EmbC.runC_erase
#print axioms EmbC.MachineValidC.append_call
#print axioms EmbC.WPC.while
#print axioms EmbC.WPC.call
#print axioms EmbC.FnCost.intro
#print axioms EmbC.FnCost.run
