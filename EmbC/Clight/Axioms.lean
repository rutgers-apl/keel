import EmbC.Clight
import EmbC.Clight.World
import EmbC.Clight.Replay

/-! Axiom audit for the simulation-based Clight results. Generic simulation
lemmas use only Lean's standard axioms; concrete results additionally mention
CompCert's existing uninterpreted external-call relations. No `sorryAx`, external
determinism axiom, or new semantic assumption is introduced. -/

#print axioms EmbC.Clight.Behaviors.Seg.progress
#print axioms EmbC.Clight.Behaviors.Seg.match_final
#print axioms EmbC.Clight.Behaviors.Seg.simulation
#print axioms EmbC.Clight.Behaviors.backwardSimulation_of_segments
#print axioms EmbC.Clight.Behaviors.ForwardSimulation.behaves
#print axioms EmbC.Clight.Behaviors.BackwardSimulation.behaves
#print axioms EmbC.Clight.embc_clight_forward_simulation
#print axioms EmbC.Clight.embc_clight_backward_simulation
#print axioms EmbC.Clight.embc_clight_behavior_equivalence
#print axioms EmbC.Clight.clight_ub_modeled_in_embc
#print axioms EmbC.Kernel.Defined.exists_reply
#print axioms EmbC.Clight.WorldSource.step_contract
#print axioms EmbC.Clight.WorldProof.behavior_to_contract
#print axioms EmbC.Clight.WorldProof.publicBehavior_contractBehavior
#print axioms EmbC.Clight.world_safe_of_contract_safe
#print axioms EmbC.Clight.embc_clight_world_forward
#print axioms EmbC.Clight.contract_safe_of_oracle_safe
#print axioms EmbC.Clight.clight_of_fnSpec
