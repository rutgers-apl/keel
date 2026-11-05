import EmbC.Clight
import EmbC.Clight.Proof.World

/-! Clight correspondence for executable intrinsic oracles.

The headline equivalence and undefined-behavior reflection concern the
public responses realizable by certified oracles. Each executable state carries
its intrinsic oracle; an individual oracle can select a subset of these outcomes.
-/

namespace EmbC.Clight

open Behaviors

abbrev PublicSourceBehavior := Behavior (Option Val) Mem

/-- Compare observations and represented final memory after forgetting private
external state. -/
def PublicBehaviorMatches (P : Prog) (cp : CC.Program) (initialMem : Mem)
    (j : MemoryInjection) : PublicSourceBehavior → TargetBehavior → Prop
  | .terminates trace result mem, .terminates trace' value cm =>
    trace = trace' ∧ ∃ j', j.Extends j' initialMem ∧ retRel P mem j' result value ∧
      memoryRel P j' mem cm ∧ ConstRel P cp.globalenv j' mem cm
  | .diverges trace, .diverges trace' => trace = trace'
  | .reacts trace, .reacts trace' => trace = trace'
  | _, _ => False

theorem behaviorMatches_erase_iff {P : Prog} {cp : CC.Program} {initialMem : Mem}
    {j : MemoryInjection} (source : SourceBehavior) (target : TargetBehavior) :
    PublicBehaviorMatches P cp initialMem j
      (WorldProof.erasePrivate (fun st : MachineStore => st.mem) source) target ↔
      BehaviorMatches P cp initialMem j source target := by
  cases source <;> cases target <;> rfl

/-- Safety for every realizable response applies to every intrinsic oracle,
without a separate conformance premise. -/
theorem world_safe_of_contract_safe {P : Prog} {obs : WorldSource.Observations}
    (ht : WorldSource.ObservationsTotal obs) {entry : String} {args : List Val} {mem : Mem}
    (hs : SourceSafe P (WorldSource.contractObservations obs) entry args mem)
    {State : Type} (oracle : Oracle P State) :
    ∀ trace, ¬ Behaves (WorldSource.semantics P obs)
      (Semantics.initial entry args ⟨mem, oracle⟩) (.goesWrong trace) := by
  intro trace hb
  obtain ⟨B, hB, heq⟩ := WorldProof.behavior_to_contract ht hb
  have hwrong : B = .goesWrong trace := by
    cases B <;> simp_all [WorldProof.erasePrivate]
  subst B
  exact hs trace hB

/-- Every execution with a certified intrinsic oracle has a matching Clight
execution under the comparison semantics' source-safety premise. -/
theorem embc_clight_world_forward (obs : WorldSource.Observations)
    (hObservations : WorldSource.ObservationsTotal obs)
    (hKernel : KernelCompatible (WorldSource.contractObservations obs))
    (hKernelBackward : KernelBackwardCompatible (WorldSource.contractObservations obs))
    (P : Prog) (cp : CC.Program) (hWellFormed : wellFormed P)
    (hTranslation : P.toClight = .ok cp) (entry : String) (args : List Val) (mem : Mem)
    (hentry : (P.findFn entry).isSome = true)
    (hadm : Admissible P entry args ⟨mem, ()⟩)
    (hsafe : SourceSafe P (WorldSource.contractObservations obs) entry args mem)
    (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val)
    (hmem : memoryRel P j mem cm) (hconst : ConstRel P cp.globalenv j mem cm)
    (hargs : argsRel P mem j args cargs) :
    ∃ (block : CC.Block) (fn : CC.Function),
      CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString entry) = some block ∧
      CC.Genv.findFunctPtr cp.globalenv.genv_genv block = some (.Internal fn) ∧
      ∀ {State : Type} (oracle : Oracle P State)
        (source : Behavior (Option Val) (KernelState P State)),
        Behaves (WorldSource.semantics P obs) (Semantics.initial entry args ⟨mem, oracle⟩) source →
        ∃ target, Behaves (targetSemantics cp) (.Callstate (.Internal fn) cargs .Kstop cm) target ∧
          PublicBehaviorMatches P cp mem j
            (WorldProof.erasePrivate (fun st : KernelState P State => st.mem) source) target := by
  obtain ⟨block, fn, hblock, hfn, hforward, _⟩ :=
    embc_clight_behavior_equivalence (WorldSource.contractObservations obs)
      (WorldProof.contractObservations_total hObservations) hKernel hKernelBackward
      P cp hWellFormed hTranslation entry args mem hentry hadm hsafe j cm cargs
      hmem hconst hargs
  refine ⟨block, fn, hblock, hfn, ?_⟩
  intro State oracle source hs
  obtain ⟨contract, hcontract, heq⟩ := WorldProof.behavior_to_contract hObservations hs
  obtain ⟨target, ht, hm⟩ := hforward contract hcontract
  refine ⟨target, ht, ?_⟩
  rw [heq]
  exact (behaviorMatches_erase_iff contract target).mpr hm

end EmbC.Clight
