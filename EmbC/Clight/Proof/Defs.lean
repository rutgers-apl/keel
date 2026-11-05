import EmbC.Clight.Admissible
import EmbC.Clight.Kernel
import EmbC.Clight.Source
import EmbC.Clight.Behaviors
import EmbC.Clight.Lowering

/-!
# Verbatim copies of the statement's definitions

The proof modules cannot import `EmbC.Clight` (which imports them), so the
definitions used by the main statement are restated here, word for word.
They are definitionally equal to the originals.
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

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

end EmbC.Clight.Proof
