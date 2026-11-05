import Vbcf.Proof.Final
import EmbC.Clight.Replay

/-!
# Vbcf proofs: the entry point in Clight

`vbcf_check_proof_sound'` holds for every certified oracle. With `clight_of_fnSpec` it carries
over to the Clight translation of the checker, under the assumptions of the Clight
correspondence: the kernel functions behave as their contracts say, and every state the program
reaches fits Clight's 64-bit representation.
-/

namespace Vbcf.Proof

open EmbC EmbC.Clight

/-- **`vbcf_check_proof` in Clight.** No Clight execution goes wrong. If one returns, it
corresponds to an EmbC execution under a certified oracle that leaves every memory block as it
found it, and a result of 0 means that the words copied from the caller decode to a proof whose
goal holds under no assignment, and so does the verifier's goal if one was passed. -/
theorem vbcf_check_proof_clight (obs : EmbC.Semantics.Observations)
    (hObservations : EmbC.Semantics.ObservationsTotal obs)
    (hKernel : KernelCompatible obs) (hKernelBackward : KernelBackwardCompatible obs)
    (cp : CC.Program) (hWellFormed : wellFormed Vbcf.prog)
    (hTranslation : Vbcf.prog.toClight = .ok cp)
    (ga : GArg) (goal size : BitVec 32) (m : Mem) (harena : ArenaIn m goal.toNat ga)
    (hadm : Admissible Vbcf.prog "vbcf_check_proof" [gxVal ga, .u32 goal, .uptr, .u32 size]
      ⟨m, ()⟩)
    (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val)
    (hmem : memoryRel Vbcf.prog j m cm) (hconst : ConstRel Vbcf.prog cp.globalenv j m cm)
    (hargs : argsRel Vbcf.prog m j [gxVal ga, .u32 goal, .uptr, .u32 size] cargs) :
    ∃ (b : CC.Block) (cf : CC.Function),
      CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString "vbcf_check_proof") = some b ∧
      CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
      (∀ trace, ¬ Behaviors.Behaves (targetSemantics cp)
        (.Callstate (.Internal cf) cargs .Kstop cm) (.goesWrong trace)) ∧
      (∀ trace value cm', Behaviors.Behaves (targetSemantics cp)
          (.Callstate (.Internal cf) cargs .Kstop cm) (.terminates trace value cm') →
        ∃ (o : Oracle Vbcf.prog (List Kernel.Reply)) (rv : Option Val) (m' : Mem),
          (∀ b, m'.block? b = m.block? b) ∧
          (∃ r, rv = some (.u32 r) ∧
            (r = 0#32 → (∃ P g,
              Bcf.decode (wordsToBytes (copiedWords ⟨m, o⟩ (size.toNat / 4))) = .ok P ∧
              ∀ ρ, ¬ Bcf.holds P.pool ρ g) ∧ GoalRefuted goal.toNat ga)) ∧
          ∃ j', j.Extends j' m ∧ retRel Vbcf.prog m' j' rv value ∧
            memoryRel Vbcf.prog j' m' cm' ∧ ConstRel Vbcf.prog cp.globalenv j' m' cm') := by
  obtain ⟨b, cf, hb, hcf, hsafe, hterm⟩ :=
    clight_of_fnSpec obs hObservations hKernel hKernelBackward Vbcf.prog cp hWellFormed
      hTranslation "vbcf_check_proof" [gxVal ga, .u32 goal, .uptr, .u32 size] m (by rfl) hadm
      j cm cargs hmem hconst hargs (vbcf_check_proof_sound' (State := List Kernel.Reply) ga goal size)
      (fun _ => ⟨rfl, harena⟩)
  refine ⟨b, cf, hb, hcf, hsafe, ?_⟩
  intro trace value cm' ht
  obtain ⟨o, _, rv, m', ⟨hm, r, hr, hacc⟩, j', hext, hret, hmem', hconst'⟩ := hterm trace value cm' ht
  exact ⟨o, rv, m', hm, ⟨r, hr, hacc⟩, j', hext, hret, hmem', hconst'⟩

end Vbcf.Proof
