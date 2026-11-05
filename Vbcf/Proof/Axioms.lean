import Bcf.Final
import EmbC.Clight
import Vbcf.Proof.ClightFinal
import Vbcf.Proof.CostFinal

/-! Axiom audit of Keel's main theorems. -/

#print axioms Bcf.checkBcf_sound
#print axioms Vbcf.Proof.vbcf_check_proof_sound'
#print axioms Vbcf.Proof.vbcf_check_proof_sound_bounded
#print axioms EmbC.Clight.embc_clight_behavior_equivalence
#print axioms EmbC.Clight.clight_ub_modeled_in_embc
#print axioms Vbcf.Proof.vbcf_check_proof_clight
