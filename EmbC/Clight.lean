import EmbC.Clight.Admissible
import EmbC.Clight.Kernel
import EmbC.Clight.Source
import EmbC.Clight.Behaviors
import EmbC.Clight.Lowering
import EmbC.Clight.Proof.Main
import EmbC.Clight.Proof.BackStep
import EmbC.Clight.Proof.ForwardSimulation
import EmbC.Clight.Proof.BackwardSimulation
import EmbC.Clight.Proof.BackwardSimulationBehaviors

/-!
# Semantic soundness of EmbC's direct Clight embedding

The standard forward and backward simulations use the public response relation
derived from EmbC's intrinsically certified stateful oracles. Both diagrams have initial and final matching;
the backward relation also covers intermediate target states. Behavior
equivalence on safe inputs and reflection of target undefined behavior follow
from these records. Executable states carry their complete oracle; the
comparison semantics forgets this component and retains its public responses.
-/

namespace EmbC.Clight

abbrev SourceBehavior := Behaviors.Behavior (Option Val) MachineStore
abbrev TargetBehavior := Behaviors.Behavior CC.Val CC.Mem

def sourceSemantics (P : Prog) (obs : Semantics.Observations) :
    Behaviors.Semantics Semantics.State (Option Val) MachineStore :=
  { step := Semantics.Step P obs
    final := fun config rv st => config = .returned rv st .stop }

def targetSemantics (cp : CC.Program) :
    Behaviors.Semantics CC.State CC.Val CC.Mem :=
  { step := CC.Step2 cp.globalenv
    final := fun config rv cm => config = .Returnstate rv .Kstop cm }

/-- The source entry has the specified memory and arguments. -/
def sourceInitial (f : String) (args : List Val) (m : Mem) (c : Semantics.State) : Prop :=
  c = Semantics.initial f args ⟨m, ()⟩

/-- The inductive segment relation includes the intermediate Clight states of
generated preludes and control-flow segments. The index is the number of remaining
deterministic silent target steps, not the forward simulation's index. -/
abbrev BackwardMatchStates (P : Prog) (cp : CC.Program) (obs : Semantics.Observations)
    (m : Mem) (j : MemoryInjection) :=
  Behaviors.Seg (sourceSemantics P obs) (targetSemantics cp)
    (Proof.BInv P cp j m) (Proof.FinalRel P cp m j)

/-- CompCert-style stepwise simulation for one declared entry and represented
target initial state. Final values and memories are compared by `FinalRel`.
There is no global no-UB premise; the record's standard local `Safe` guard
appears on its progress, final-state, and step obligations. -/
abbrev EntryBackwardSimulation (P : Prog) (cp : CC.Program) (obs : Semantics.Observations)
    (f : String) (args : List Val) (m : Mem) (j : MemoryInjection)
    (cf : CC.Function) (cargs : List CC.Val) (cm : CC.Mem) :=
  Behaviors.BackwardSimulation (sourceSemantics P obs) (targetSemantics cp)
    (sourceInitial f args m) (fun X => X = .Callstate (.Internal cf) cargs .Kstop cm)
    (Proof.FinalRel P cp m j) Nat

/-- Forward simulation for a represented source and target entry. Its record includes initial and final matching, as well as the
well-founded step diagram inherited from `FwdSim`. -/
abbrev EntryForwardSimulation (P : Prog) (cp : CC.Program) (obs : Semantics.Observations)
    (f : String) (args : List Val) (st : MachineStore) (j : MemoryInjection)
    (cf : CC.Function) (cargs : List CC.Val) (cm : CC.Mem) :=
  Behaviors.ForwardSimulation (sourceSemantics P obs) (targetSemantics cp)
    (fun c => c = Semantics.initial f args st)
    (fun X => X = .Callstate (.Internal cf) cargs .Kstop cm)
    (Proof.FinalRel P cp st.mem j)

/-- The concrete matching relation of the standalone forward simulation. -/
abbrev ForwardMatchStates (P : Prog) (cp : CC.Program) (st : MachineStore) (j : MemoryInjection) :=
  Proof.Rel P cp.globalenv j st.mem

/-- Read-only tables have their declared contents and cannot alias the source
heap. The kernel compatibility condition preserves this global frame. -/
def ConstRel (P : Prog) (ge : CC.CGenv) (j : MemoryInjection)
    (m : Mem) (cm : CC.Mem) : Prop :=
  ∀ table ∈ P.consts, ∃ b,
    CC.Genv.findSymbol ge.genv_genv (CC.identOfString table.name) = some b ∧
    CC.Mem.validBlock cm b = true ∧
    (∀ sourceBlock, sourceBlock < m.blocks.size → j.block sourceBlock ≠ b) ∧
    ∀ (i : Nat) word, table.words[i]? = some word →
      CC.Mem.load .Mint32 cm b ((i : CC.Z) * 4) = some (.Vint word)

/-- Every observed, representable EmbC kernel outcome has a matching Clight
external call with the same trace, preserving existing block identities,
historical strides, and the source's read-only tables. -/
def KernelCompatible (obs : Semantics.Observations) : Prop :=
  ∀ (P : Prog) (ge : CC.CGenv), ge.genv_cenv = compositeEnv P →
    ∀ (ext : Ext) (args : List Val) (st : MachineStore) (rv : Option Val) (st' : MachineStore)
      (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val) (trace : CC.Trace),
      memoryRel P j st.mem cm →
      ConstRel P ge j st.mem cm →
      argsRel P st.mem j args cargs →
      Oracle.Returns P ⟨ext, args, st.mem⟩ ⟨rv, st'.mem⟩ →
      memoryFits P st'.mem →
      obs ext args st rv st' trace →
      ∃ (j' : MemoryInjection) (cm' : CC.Mem) (crv : CC.Val),
        j.Extends j' st.mem ∧
        CC.externalCall (kernelExternal ext) ge.genv_genv.toSenv cargs cm trace crv cm' ∧
        retRel P st'.mem j' rv crv ∧
        memoryRel P j' st'.mem cm' ∧
        ConstRel P ge j' st'.mem cm'

/-- Every target outcome is either an invalid source call or a matching
permitted source reply. No representation of external choices is involved. -/
def KernelBackwardCompatible (obs : Semantics.Observations) : Prop :=
  ∀ (P : Prog) (ge : CC.CGenv), ge.genv_cenv = compositeEnv P →
    ∀ (ext : Ext) (args : List Val) (m : Mem)
      (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val)
      (trace : CC.Trace) (crv : CC.Val) (cm' : CC.Mem),
      memoryRel P j m cm → ConstRel P ge j m cm → argsRel P m j args cargs →
      CC.externalCall (kernelExternal ext) ge.genv_genv.toSenv cargs cm trace crv cm' →
      (¬ Kernel.Defined P ⟨ext, args, m⟩) ∨
      ∃ (rv : Option Val) (m' : Mem) (j' : MemoryInjection),
        Oracle.Returns P ⟨ext, args, m⟩ ⟨rv, m'⟩ ∧ memoryFits P m' ∧
        obs ext args ⟨m, ()⟩ rv ⟨m', ()⟩ trace ∧ j.Extends j' m ∧
        retRel P m' j' rv crv ∧ memoryRel P j' m' cm' ∧ ConstRel P ge j' m' cm'

/-- The direct embedding preserves source struct layouts and function signatures. -/
def ProgramRel (P : Prog) (cp : CC.Program) : Prop :=
  cp.prog_types = composites P ∧
  cp.prog_comp_env = compositeEnv P ∧
  CC.compositesWellFormed cp = true ∧
  ∀ fn ∈ P.fns, ∃ (b : CC.Block) (cf : CC.Function),
    CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString fn.name) = some b ∧
    CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
    CC.typeOfFunction cf =
      .Tfunction (fn.params.map (fun p => type p.2))
        ((fn.ret.map type).getD .Tvoid) CC.cc_default

/-- Configurations fit the target machine; source errors are still observable. -/
def stateFits (P : Prog) (config : Semantics.State) : Prop :=
  memoryFits P (Semantics.stateKernelState config).mem ∧
  match config with
  | .regular _ env mem _ _ => envFits P mem env
  | .callstate _ args mem _ _ => argsFits P mem args
  | .returnstate rv mem _ _ => argsFits P mem rv.toList

/-- Check every reachable source configuration, including every finite prefix
of an infinite execution. This is independent of fuel and observation labels. -/
def Admissible (P : Prog) (f : String) (args : List Val) (st : MachineStore) : Prop :=
  ∀ config,
    Semantics.RawStar (Semantics.rawStep P) (Semantics.initial f args st) config →
      stateFits P config

/-- Source-defined observations are preserved exactly. A source failure allows
any target behavior extending the failure's trace, as in behavior improvement. -/
def Improves (P : Prog) (cp : CC.Program) (initialMem : Mem) (j : MemoryInjection) :
    SourceBehavior → TargetBehavior → Prop
  | .terminates trace rv st', .terminates targetTrace crv cm' =>
    trace = targetTrace ∧
    ∃ j', j.Extends j' initialMem ∧ retRel P st'.mem j' rv crv ∧
      memoryRel P j' st'.mem cm' ∧ ConstRel P cp.globalenv j' st'.mem cm'
  | .diverges trace, .diverges targetTrace => trace = targetTrace
  | .reacts trace, .reacts targetTrace => trace = targetTrace
  | .goesWrong trace, target => Behaviors.Prefix trace target
  | _, _ => False

/-- A standalone forward simulation for every represented source entry.
The concrete relation and initial/final matching are included in the record. -/
def StepwiseForwardSimulation (P : Prog) (cp : CC.Program)
    (obs : Semantics.Observations) : Prop :=
  ∀ (f : String) (args : List Val) (st : MachineStore),
    (P.findFn f).isSome = true → Admissible P f args st →
    ∀ (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val),
      memoryRel P j st.mem cm → ConstRel P cp.globalenv j st.mem cm →
      argsRel P st.mem j args cargs →
      ∃ (b : CC.Block) (cf : CC.Function),
        CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString f) = some b ∧
        CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
        ∃ sim : EntryForwardSimulation P cp obs f args st j cf cargs cm,
          sim.rel = ForwardMatchStates P cp st j

/-- A standard stepwise backward simulation for every represented entry. Its
matching relation is explicitly `BackwardMatchStates`, covering intermediate
target states, and its well-founded order is natural-number decrease. -/
def StepwiseBackwardSimulation (P : Prog) (cp : CC.Program)
    (obs : Semantics.Observations) : Prop :=
  ∀ (f : String) (args : List Val) (m : Mem),
    (P.findFn f).isSome = true →
    Admissible P f args ⟨m, ()⟩ →
    ∀ (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val),
      memoryRel P j m cm →
      ConstRel P cp.globalenv j m cm →
      argsRel P m j args cargs →
      ∃ (b : CC.Block) (cf : CC.Function),
        CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString f) = some b ∧
        CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
        ∃ sim : EntryBackwardSimulation P cp obs f args m j cf cargs cm,
          sim.matchStates = BackwardMatchStates P cp obs m j ∧ sim.order = Nat.lt

/-- Every Clight execution that goes wrong is reflected by a source execution
that goes wrong after a prefix of the target's observations. Initial arguments
and memory agree through the representation relation. Source safety is not assumed. This reflects
semantic stuckness; the source may fail earlier for an EmbC restriction. -/
def ReflectsUndefinedBehavior (P : Prog) (cp : CC.Program)
    (obs : Semantics.Observations) : Prop :=
  ∀ (f : String) (args : List Val) (m : Mem),
    (P.findFn f).isSome = true →
    Admissible P f args ⟨m, ()⟩ →
    ∀ (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val),
      memoryRel P j m cm →
      ConstRel P cp.globalenv j m cm →
      argsRel P m j args cargs →
      ∃ (b : CC.Block) (cf : CC.Function),
        CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString f) = some b ∧
        CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
        ∀ targetTrace, Behaviors.Behaves (targetSemantics cp)
          (.Callstate (.Internal cf) cargs .Kstop cm) (.goesWrong targetTrace) →
          ∃ sourceTrace : CC.Trace,
            Behaviors.Behaves (sourceSemantics P obs)
              (Semantics.initial f args ⟨m, ()⟩) (.goesWrong sourceTrace) ∧
            List.IsPrefix sourceTrace targetTrace

/-- No contract execution goes wrong, for any permitted external outcome. -/
def SourceSafe (P : Prog) (obs : Semantics.Observations) (f : String)
    (args : List Val) (m : Mem) : Prop :=
  ∀ trace : CC.Trace, ¬ Behaviors.Behaves (sourceSemantics P obs)
      (Semantics.initial f args ⟨m, ()⟩) (.goesWrong trace)

/-- Exact matching of defined observations and represented outcomes.
A source failure cannot supply a match through behavior improvement. -/
def BehaviorMatches (P : Prog) (cp : CC.Program) (initialMem : Mem)
    (j : MemoryInjection) : SourceBehavior → TargetBehavior → Prop
  | .goesWrong _, _ => False
  | source, target => Improves P cp initialMem j source target

/-- Equality of the source and target behavior sets modulo representation,
on admissible, source-safe inputs. The two directions use the same target
entry function and initial target memory. Source behaviors range over all
permitted kernel outcomes. Neither target safety nor termination is assumed. -/
def BehaviorEquivalent (P : Prog) (cp : CC.Program) (obs : Semantics.Observations) : Prop :=
  ∀ (f : String) (args : List Val) (m : Mem),
    (P.findFn f).isSome = true →
    Admissible P f args ⟨m, ()⟩ →
    SourceSafe P obs f args m →
    ∀ (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val),
      memoryRel P j m cm →
      ConstRel P cp.globalenv j m cm →
      argsRel P m j args cargs →
      ∃ (b : CC.Block) (cf : CC.Function),
        CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString f) = some b ∧
        CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
        (∀ source : SourceBehavior,
          Behaviors.Behaves (sourceSemantics P obs)
            (Semantics.initial f args ⟨m, ()⟩) source →
          ∃ target, Behaviors.Behaves (targetSemantics cp)
              (.Callstate (.Internal cf) cargs .Kstop cm) target ∧
            BehaviorMatches P cp m j source target) ∧
        (∀ target, Behaviors.Behaves (targetSemantics cp)
            (.Callstate (.Internal cf) cargs .Kstop cm) target →
          ∃ source : SourceBehavior,
            Behaviors.Behaves (sourceSemantics P obs)
              (Semantics.initial f args ⟨m, ()⟩) source ∧
            BehaviorMatches P cp m j source target)

/-- Source safety removes the failure-improvement case from any matched run. -/
theorem behavior_matches_of_source_safe {P : Prog} {cp : CC.Program}
    {obs : Semantics.Observations} {f : String} {args : List Val} {m : Mem}
    {j : MemoryInjection} {source : SourceBehavior} {target : TargetBehavior}
    (hSafe : SourceSafe P obs f args m)
    (hSource : Behaviors.Behaves (sourceSemantics P obs)
      (Semantics.initial f args ⟨m, ()⟩) source)
    (hImproves : Improves P cp m j source target) :
    BehaviorMatches P cp m j source target := by
  cases source with
  | terminates trace rv st => exact hImproves
  | diverges trace => exact hImproves
  | reacts trace => exact hImproves
  | goesWrong trace => exact (hSafe trace hSource).elim

/-- Standalone forward simulation for the direct embedding, with initial and
final matching and the well-founded step diagram. Program representation is
proved alongside the simulation. -/
theorem embc_clight_forward_simulation (obs : Semantics.Observations)
    (hKernel : KernelCompatible obs) (P : Prog) (cp : CC.Program)
    (hWellFormed : wellFormed P) (hTranslation : P.toClight = .ok cp) :
    ProgramRel P cp ∧ StepwiseForwardSimulation P cp obs := by
  refine ⟨Proof.programRel_of hWellFormed hTranslation, ?_⟩
  intro f args st hf hadm j cm cargs hmem hconst hargs
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp hf
  obtain ⟨hmemfn, hname⟩ := Proof.findFn_mem hfn
  obtain ⟨b, cf, hb, hcf, hlow⟩ :=
    Proof.genv_find_fn hWellFormed (Proof.lowerProgram_inv hTranslation) hmemfn
  refine ⟨b, cf, hname ▸ hb, hcf, ?_⟩
  let core : Behaviors.FwdSim (sourceSemantics P obs) (targetSemantics cp) :=
    ⟨Proof.Rel P cp.globalenv j st.mem, fun _ _ _ _ _ h1 h2 => by
      rcases Proof.sim_step hKernel hWellFormed hTranslation h1 h2 with
        ⟨i', X', hr, hp | hp⟩ | ⟨_, i', X', hr, hp⟩
      · exact ⟨i', X', hr, .inl (Proof.plus_of_tplus hp)⟩
      · exact ⟨i', X', hr, .inr hp⟩
      · exact ⟨i', X', hr, .inl (Proof.plus_of_text hp)⟩⟩
  have hrel0 : core.rel 1 (Semantics.initial f args st)
      (.Callstate (.Internal cf) cargs .Kstop cm) := by
    refine ⟨hadm, .inl ⟨rfl, j, cm,
      ⟨Proof.Extends.refl j st.mem, Proof.MemGrow.refl _, hmem, hconst⟩, ?_⟩⟩
    exact ⟨fn, cf, cargs, .Kstop, hfn, ⟨hmemfn, hlow⟩, hargs, .stop, rfl⟩
  let sim : EntryForwardSimulation P cp obs f args st j cf cargs cm :=
    { toFwdSim := core
      match_initial_states := by
        intro c hc
        subst c
        exact ⟨1, _, rfl, hrel0⟩
      match_final_states := by
        intro i c X rv st' hr hf
        obtain ⟨w, cm', hX, hfr⟩ := Proof.rel_final rfl hr hf
        exact ⟨w, cm', hX, hfr⟩ }
  exact ⟨sim, rfl⟩

/-- A CompCert-style backward simulation over the same contract semantics as
 the forward simulation. Its decreasing rank excludes infinite target stuttering. -/
theorem embc_clight_backward_simulation (obs : Semantics.Observations)
    (hObservations : Semantics.ObservationsTotal obs)
    (hKernel : KernelCompatible obs) (hKernelBackward : KernelBackwardCompatible obs)
    (P : Prog) (cp : CC.Program) (hWellFormed : wellFormed P)
    (hTranslation : P.toClight = .ok cp) :
    ProgramRel P cp ∧ StepwiseBackwardSimulation P cp obs := by
  refine ⟨Proof.programRel_of hWellFormed hTranslation, ?_⟩
  intro f args m hf hadm j cm cargs hmem hconst hargs
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp hf
  obtain ⟨hmemfn, hname⟩ := Proof.findFn_mem hfn
  obtain ⟨b, cf, hb, hcf, hlow⟩ :=
    Proof.genv_find_fn hWellFormed (Proof.lowerProgram_inv hTranslation) hmemfn
  refine ⟨b, cf, hname ▸ hb, hcf, ?_⟩
  have hinit : ∀ c X, sourceInitial f args m c →
      X = .Callstate (.Internal cf) cargs .Kstop cm →
      ∃ c', sourceInitial f args m c' ∧ Proof.BInv P cp j m c' X := by
    intro c X hc hX
    subst X
    subst c
    refine ⟨_, rfl, 1, hadm, .inl ⟨rfl, j, cm,
      ⟨Proof.Extends.refl j m, Proof.MemGrow.refl _, hmem, hconst⟩, ?_⟩⟩
    exact ⟨fn, cf, cargs, .Kstop, hfn, ⟨hmemfn, hlow⟩, hargs, .stop, rfl⟩
  let sim : EntryBackwardSimulation P cp obs f args m j cf cargs cm :=
    Behaviors.backwardSimulation_of_segments
      (S := sourceSemantics P obs) (T := targetSemantics cp)
      (Inv := Proof.BInv P cp j m) (FR := Proof.FinalRel P cp m j)
      (fun c X ⟨i, hr⟩ => Proof.seg_of_rel hObservations hKernel hKernelBackward
        hWellFormed hTranslation i c X hr)
      (fun X r m' hfin t Y hst => by
        simp only [targetSemantics] at hfin
        subst hfin
        unfold targetSemantics CC.Step2 at hst
        cases hst)
      (sourceInitial f args m)
      (fun X => X = .Callstate (.Internal cf) cargs .Kstop cm)
      (fun _ _ => ⟨_, rfl⟩) hinit
  exact ⟨sim, rfl, rfl⟩

/-- The two simulations imply equality of defined observable behaviors. -/
theorem behavior_equivalence_of_simulations {P : Prog} {cp : CC.Program}
    {obs : Semantics.Observations} (hForward : StepwiseForwardSimulation P cp obs)
    (hBackward : StepwiseBackwardSimulation P cp obs) : BehaviorEquivalent P cp obs := by
  intro f args m hf hadm hSafe j cm cargs hmem hconst hargs
  obtain ⟨b, cf, hb, hcf, back, _, _⟩ :=
    hBackward f args m hf hadm j cm cargs hmem hconst hargs
  refine ⟨b, cf, hb, hcf, ?_, ?_⟩
  · intro source hSource
    obtain ⟨b', cf', hb', hcf', front, _⟩ :=
      hForward f args ⟨m, ()⟩ hf hadm j cm cargs hmem hconst hargs
    have hbEq : b' = b := Option.some.inj (hb'.symm.trans hb)
    subst b'
    have hcfEq : cf' = cf := CC.FunDef.Internal.inj (Option.some.inj (hcf'.symm.trans hcf))
    subst cf'
    obtain ⟨i, X, hX, hr⟩ := front.match_initial_states _ rfl
    subst X
    obtain ⟨target, hTarget, hm⟩ := front.behaves hr hSource
    exact ⟨target, hTarget,
      behavior_matches_of_source_safe hSafe hSource (Proof.matches_improves hm)⟩
  · intro target hTarget
    obtain ⟨i, c, hc, hr⟩ := back.match_initial_states
      (Semantics.initial f args ⟨m, ()⟩) _ rfl rfl
    subst c
    obtain ⟨source, hSource, hm⟩ := back.behaves hr hTarget
    exact ⟨source, hSource,
      behavior_matches_of_source_safe hSafe hSource (Proof.matches_improves hm)⟩

/-- The backward simulation reflects every target failure, without a global
source-safety premise. -/
theorem undefined_behavior_reflection_of_backward_simulation {P : Prog} {cp : CC.Program}
    {obs : Semantics.Observations}
    (hBackward : StepwiseBackwardSimulation P cp obs) : ReflectsUndefinedBehavior P cp obs := by
  intro f args m hf hadm j cm cargs hmem hconst hargs
  obtain ⟨b, cf, hb, hcf, back, _, _⟩ :=
    hBackward f args m hf hadm j cm cargs hmem hconst hargs
  refine ⟨b, cf, hb, hcf, ?_⟩
  intro targetTrace hTarget
  obtain ⟨i, c, hc, hr⟩ := back.match_initial_states
    (Semantics.initial f args ⟨m, ()⟩) _ rfl rfl
  subst c
  obtain ⟨source, hSource, hm⟩ := back.behaves hr hTarget
  cases source with
  | terminates trace rv st => exact hm.elim
  | diverges trace => exact hm.elim
  | reacts stream => exact hm.elim
  | goesWrong trace => exact ⟨trace, hSource, hm⟩

/-- Every undefined Clight execution has a source failure at a trace prefix. -/
theorem clight_ub_modeled_in_embc (obs : Semantics.Observations)
    (hObservations : Semantics.ObservationsTotal obs)
    (hKernel : KernelCompatible obs) (hKernelBackward : KernelBackwardCompatible obs)
    (P : Prog) (cp : CC.Program) (hWellFormed : wellFormed P)
    (hTranslation : P.toClight = .ok cp) : ReflectsUndefinedBehavior P cp obs :=
  undefined_behavior_reflection_of_backward_simulation
    (embc_clight_backward_simulation obs hObservations hKernel hKernelBackward
      P cp hWellFormed hTranslation).2

/-- Observable behavior equivalence on admissible, source-safe inputs. -/
theorem embc_clight_behavior_equivalence (obs : Semantics.Observations)
    (hObservations : Semantics.ObservationsTotal obs)
    (hKernel : KernelCompatible obs) (hKernelBackward : KernelBackwardCompatible obs)
    (P : Prog) (cp : CC.Program) (hWellFormed : wellFormed P)
    (hTranslation : P.toClight = .ok cp) : BehaviorEquivalent P cp obs :=
  behavior_equivalence_of_simulations
    (embc_clight_forward_simulation obs hKernel P cp hWellFormed hTranslation).2
    (embc_clight_backward_simulation obs hObservations hKernel hKernelBackward
      P cp hWellFormed hTranslation).2

end EmbC.Clight
