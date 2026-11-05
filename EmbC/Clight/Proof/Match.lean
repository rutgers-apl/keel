import EmbC.Clight.Proof.Env

/-!
# The simulation relation between source configurations and Clight states
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-- `s` is lowered to `s'` somewhere in the body of `fn`. -/
def LSb (P : Prog) (fn : Fn) (s : Stmt) (s' : CC.Stmt) : Prop :=
  ∃ d σ σ', LS (fnContext P fn) d σ s s' σ'

/-- `cf` is the lowering of the source function `fn` of `P`. -/
structure FnOK (P : Prog) (fn : Fn) (cf : CC.Function) : Prop where
  mem : fn ∈ P.fns
  low : Priv.lowerFunction P fn = .ok cf

/-- Continuations.  The index is the current function (or `none` at call-continuation level). -/
inductive KR (P : Prog) (m : Mem) (j : MemoryInjection) :
    Option (Fn × CC.Function) → Semantics.Cont → CC.Cont → Prop
  | seq {fn cf b k b' K} : LSb P fn b b' → KR P m j (some (fn, cf)) k K →
      KR P m j (some (fn, cf)) (.seq b k) (.Kseq b' K)
  | seqSkip {fn cf b k K} : LSb P fn b .Sskip → KR P m j (some (fn, cf)) k K →
      KR P m j (some (fn, cf)) (.seq b k) K
  | loop {fn cf c body k s1 K} : LSb P fn (.while c body) (.Sloop s1 .Sskip) →
      KR P m j (some (fn, cf)) k K → KR P m j (some (fn, cf)) (.loop c body k) (.Kloop1 s1 .Sskip K)
  | fn {fn cf k K} : KR P m j none k K → KR P m j (some (fn, cf)) (.function fn.ret k) K
  | stop : KR P m j none .stop .Kstop
  | call {fn cf dst env k le K} : FnOK P fn cf → EnvRel (fnContext P fn) m j env le →
      KR P m j (some (fn, cf)) k K →
      KR P m j none (.call dst env k) (.Kcall (dst.map CC.identOfString) cf CC.emptyEnv le K)

/-- Source positions inside a function body. -/
abbrev SPos := Stmt × Semantics.Cont

def SPos.exec (s : Stmt) (k : Semantics.Cont) : SPos := (s, k)
def SPos.normal (k : Semantics.Cont) : SPos := (.skip, k)
def SPos.brk (k : Semantics.Cont) : SPos := (.brk, k)

/-- Matching positions; the target may be ahead over statements lowered to `Sskip`. -/
inductive Pos (P : Prog) (m : Mem) (j : MemoryInjection) (fn : Fn) (cf : CC.Function) :
    SPos → CC.Stmt → CC.Cont → Prop
  | exec {s k s' K} : LSb P fn s s' → KR P m j (some (fn, cf)) k K → Pos P m j fn cf (.exec s k) s' K
  | execSkip {s k s' K} : LSb P fn s .Sskip → Pos P m j fn cf (.normal k) s' K →
      Pos P m j fn cf (.exec s k) s' K
  | normal {k K} : KR P m j (some (fn, cf)) k K → Pos P m j fn cf (.normal k) .Sskip K
  | normalSeq {b k s' K} : Pos P m j fn cf (.exec b k) s' K → Pos P m j fn cf (.normal (.seq b k)) s' K
  | brk {k K} : KR P m j (some (fn, cf)) k K → Pos P m j fn cf (.brk k) .Sbreak K

/-- Matching configurations, for a given memory, injection and target memory. -/
def MatchC (P : Prog) (ge : CC.CGenv) (m : Mem) (j : MemoryInjection) (cm : CC.Mem) :
    Semantics.State → CC.State → Prop
  | .regular s env _ _ k, T => ∃ fn cf s' K le, FnOK P fn cf ∧ Pos P m j fn cf (.exec s k) s' K ∧
      EnvRel (fnContext P fn) m j env le ∧ T = .State cf s' K CC.emptyEnv le cm
  | .callstate (.internal f) vs _ _ k, T => ∃ fn cf cargs K, P.findFn f = some fn ∧ FnOK P fn cf ∧
      argsRel P m j vs cargs ∧ KR P m j none k K ∧ T = .Callstate (.Internal cf) cargs K cm
  | .callstate (.external ext) vs _ _ k, T => ∃ fn cf dst env k' K le ces types cargs,
      k = .call dst env k' ∧ FnOK P fn cf ∧ KR P m j (some (fn, cf)) k' K ∧
      EnvRel (fnContext P fn) m j env le ∧ argsRel P m j vs cargs ∧
      CC.EvalExprlist ge CC.emptyEnv le cm ces types cargs ∧
      T = .State cf (.Sbuiltin (dst.map CC.identOfString) (kernelExternal ext) types ces)
        K CC.emptyEnv le cm
  | .returnstate rv _ _ k, T =>
      (∃ w K, retRel P m j rv w ∧ KR P m j none k K ∧ T = .Returnstate w K cm) ∨
      (∃ fn cf dst env k' K le w, k = .call dst env k' ∧ FnOK P fn cf ∧
        KR P m j (some (fn, cf)) k' K ∧ EnvRel (fnContext P fn) m j env le ∧
        retRel P m j rv w ∧
        T = .State cf .Sskip K CC.emptyEnv (CC.setOpttemp (dst.map CC.identOfString) w le) cm)

/-- Global invariant relative to the initial injection and memory. -/
def GInv (P : Prog) (ge : CC.CGenv) (j0 : MemoryInjection) (m0 : Mem)
    (j : MemoryInjection) (m : Mem) (cm : CC.Mem) : Prop :=
  j0.Extends j m0 ∧ MemGrow m0 m ∧ memoryRel P j m cm ∧ ConstRel P ge j m cm

/-! ## Measure -/

def W : Stmt → Nat
  | .seq a b => W a + W b + 2
  | _ => 1

def M : Semantics.Cont → Nat
  | .seq b k => W b + 1 + M k
  | .loop _ _ k => 1 + M k
  | .function _ _ => 2
  | _ => 1

def mu : Semantics.State → Nat
  | .regular s _ _ _ k => W s + M k
  | .returnstate _ _ _ (.call _ _ k) => M k + 3
  | _ => 1

theorem W_pos (s : Stmt) : 0 < W s := by cases s <;> simp [W]

/-- Configurations that silently and deterministically reach a stuck state. -/
inductive Doom (P : Prog) : Nat → Semantics.State → Prop
  | stuck {n c} : Semantics.Failed P c → Doom P n c
  | step {n c c'} : Semantics.next P c = some (.silent c') → Doom P n c' → Doom P (n + 1) c

/-- Every configuration reachable from `c` fits the target machine. -/
def AdmFrom (P : Prog) (c : Semantics.State) : Prop :=
  ∀ c', Semantics.RawStar (Semantics.rawStep P) c c' → stateFits P c'

/-- The simulation relation. -/
def Rel (P : Prog) (ge : CC.CGenv) (j0 : MemoryInjection) (m0 : Mem)
    (i : Nat) (c : Semantics.State) (T : CC.State) : Prop :=
  AdmFrom P c ∧
    ((i = mu c ∧ ∃ j cm, GInv P ge j0 m0 j (Semantics.stateKernelState c).mem cm ∧
      MatchC P ge (Semantics.stateKernelState c).mem j cm c T) ∨ Doom P i c)

end EmbC.Clight.Proof
