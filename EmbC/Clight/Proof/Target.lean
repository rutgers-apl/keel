import EmbC.Clight.Proof.BehaviorsLemmas
import EmbC.Clight.Proof.Priv
import CCLib.ClightExecSound

/-!
# Target-side execution helpers

Executions of the straight-line "preludes" produced by the lowering.
-/

namespace EmbC.Clight.Proof

open CC
open EmbC.Clight.Behaviors

/-- States whose step may perform an external call (and is therefore the only
source of nondeterminism in Clight). -/
def isExtState : CC.State → Bool
  | .State _ (.Sbuiltin ..) _ _ _ _ => true
  | .Callstate (.External ..) _ _ _ => true
  | _ => false

def NotExt (s : CC.State) : Prop := isExtState s = false

/-- Steps that do not perform an external call. -/
def DStep (ge : CGenv) (s : CC.State) (t : Trace) (s' : CC.State) : Prop :=
  CC.Step2 ge s t s' ∧ NotExt s

abbrev TStar (ge : CGenv) := Behaviors.Star (DStep ge)
abbrev TPlus (ge : CGenv) := Behaviors.Plus (DStep ge)

/-- A run of non-external steps followed by a single (external) step. -/
def TExt (ge : CGenv) (s : CC.State) (t : Trace) (s' : CC.State) : Prop :=
  ∃ sb, TStar ge s [] sb ∧ CC.Step2 ge sb t s'

theorem step_of_doStep {ge : CGenv} {s s' : CC.State} {t : Trace}
    (h : CC.doStep ge s = some (t, s')) : CC.Step2 ge s t s' :=
  CC.doStep_sound ge s t s' h

theorem tstar_one {ge : CGenv} {s s' : CC.State} {t : Trace}
    (h : CC.doStep ge s = some (t, s')) (hs : NotExt s := by rfl) : TStar ge s t s' :=
  Behaviors.Star.one ⟨step_of_doStep h, hs⟩

theorem tplus_one {ge : CGenv} {s s' : CC.State} {t : Trace}
    (h : CC.doStep ge s = some (t, s')) (hs : NotExt s := by rfl) : TPlus ge s t s' :=
  Behaviors.Plus.one ⟨step_of_doStep h, hs⟩

theorem DStep.step {ge : CGenv} {s s' : CC.State} {t : Trace} (h : DStep ge s t s') :
    CC.Step2 ge s t s' := h.1

theorem star_of_tstar {ge : CGenv} {s s' : CC.State} {t : Trace} (h : TStar ge s t s') :
    Behaviors.Star (CC.Step2 ge) s t s' := by
  induction h with
  | refl => exact Behaviors.Star.refl _
  | step a _ ih => exact Behaviors.Star.step a.1 ih

theorem plus_of_tplus {ge : CGenv} {s s' : CC.State} {t : Trace} (h : TPlus ge s t s') :
    Behaviors.Plus (CC.Step2 ge) s t s' := by
  cases h with
  | intro a b => exact Behaviors.Plus.intro a.1 (star_of_tstar b)

theorem plus_of_text {ge : CGenv} {s s' : CC.State} {t : Trace} (h : TExt ge s t s') :
    Behaviors.Plus (CC.Step2 ge) s t s' := by
  obtain ⟨sb, h1, h2⟩ := h
  simpa using Behaviors.Star.trans_plus (star_of_tstar h1) (Behaviors.Plus.one h2)

theorem tstar_refl {ge : CGenv} (s : CC.State) : TStar ge s [] s := Behaviors.Star.refl s

theorem tstar_trans {ge : CGenv} {s₁ s₂ s₃ : CC.State} {t₁ t₂ : Trace}
    (h₁ : TStar ge s₁ t₁ s₂) (h₂ : TStar ge s₂ t₂ s₃) : TStar ge s₁ (t₁ ++ t₂) s₃ :=
  Behaviors.Star.trans h₁ h₂

theorem tstar_trans0 {ge : CGenv} {s₁ s₂ s₃ : CC.State} {t : Trace}
    (h₁ : TStar ge s₁ [] s₂) (h₂ : TStar ge s₂ t s₃) : TStar ge s₁ t s₃ := by
  simpa using Behaviors.Star.trans h₁ h₂

theorem tplus_of_star_plus {ge : CGenv} {s₁ s₂ s₃ : CC.State} {t : Trace}
    (h₁ : TStar ge s₁ [] s₂) (h₂ : TPlus ge s₂ t s₃) : TPlus ge s₁ t s₃ := by
  simpa using Behaviors.Star.trans_plus h₁ h₂

theorem tplus_of_plus_star {ge : CGenv} {s₁ s₂ s₃ : CC.State} {t : Trace}
    (h₁ : TPlus ge s₁ t s₂) (h₂ : TStar ge s₂ [] s₃) : TPlus ge s₁ t s₃ := by
  simpa using Behaviors.Plus.trans_star h₁ h₂

/-- Straight-line code made of temporaries assignments and conditionals. -/
inductive PRun (ge : CGenv) (m : CC.Mem) : CC.Stmt → CC.TempEnv → CC.TempEnv → Prop
  | skip (le) : PRun ge m .Sskip le le
  | set {le id a v} : doEvalExpr ge emptyEnv le m a = some v →
      PRun ge m (.Sset id a) le (le.set id v)
  | seq {a b le le₁ le₂} : PRun ge m a le le₁ → PRun ge m b le₁ le₂ →
      PRun ge m (.Ssequence a b) le le₂
  | ite {c s₁ s₂ le le' v} {bb : Bool} : doEvalExpr ge emptyEnv le m c = some v →
      Cop.boolVal v (typeof c) m = some bb →
      PRun ge m (if bb then s₁ else s₂) le le' → PRun ge m (.Sifthenelse c s₁ s₂) le le'

theorem PRun.star {ge : CGenv} {m : CC.Mem} {f : CC.Function} {a : CC.Stmt} {le le' : CC.TempEnv}
    (h : PRun ge m a le le') : ∀ K, TStar ge (.State f a K emptyEnv le m) []
      (.State f .Sskip K emptyEnv le' m) := by
  induction h with
  | skip le => intro K; exact tstar_refl _
  | set hv => intro K; exact tstar_one (by simp only [doStep, hv]; rfl)
  | @seq a b le le₁ le₂ _ _ iha ihb =>
    intro K
    refine tstar_trans0 (tstar_one (s' := .State f a (.Kseq b K) emptyEnv le m) rfl) ?_
    refine tstar_trans0 (iha _) ?_
    refine tstar_trans0 (tstar_one (s' := .State f b K emptyEnv le₁ m) rfl) ?_
    exact ihb K
  | @ite c s₁ s₂ le le' v bb hv hb _ ih =>
    intro K
    refine tstar_trans0 (tstar_one (s' := .State f (if bb then s₁ else s₂) K emptyEnv le m)
      (by simp only [doStep, hv, hb]; rfl)) ?_
    exact ih K

theorem PRun.skip_inv {ge : CGenv} {m : CC.Mem} {le le' : CC.TempEnv} (h : PRun ge m .Sskip le le') :
    le' = le := by
  cases h; rfl

theorem PRun.sequence {ge : CGenv} {m : CC.Mem} {a b : CC.Stmt} {le le₁ le₂ : CC.TempEnv}
    (ha : PRun ge m a le le₁) (hb : PRun ge m b le₁ le₂) :
    PRun ge m (Priv.sequence a b) le le₂ := by
  unfold Priv.sequence
  split
  · rw [ha.skip_inv] at hb; exact hb
  · rw [hb.skip_inv]; exact ha
  · exact .seq ha hb

/-- Running a prelude in front of a statement. -/
theorem PRun.seq_star {ge : CGenv} {m : CC.Mem} {f : CC.Function} {a b : CC.Stmt} {le le₁ : CC.TempEnv}
    (ha : PRun ge m a le le₁) (K : CC.Cont) :
    TStar ge (.State f (Priv.sequence a b) K emptyEnv le m) [] (.State f b K emptyEnv le₁ m) := by
  unfold Priv.sequence
  split
  · rw [ha.skip_inv]; exact tstar_refl _
  · exact ha.star K
  · refine tstar_trans0 (tstar_one (s' := .State f a (.Kseq b K) emptyEnv le m) rfl) ?_
    refine tstar_trans0 (ha.star _) ?_
    exact tstar_one rfl

theorem sequence_skip_left (b : CC.Stmt) : Priv.sequence .Sskip b = b := by
  simp [Priv.sequence]

theorem sequence_ne_skip_right {a : CC.Stmt} (b : CC.Stmt) (ha : a ≠ .Sskip) :
    Priv.sequence a b = .Sskip → b = .Sskip ∧ a = .Sskip := by
  unfold Priv.sequence
  split <;> simp_all

theorem sequence_eq_skip {a b : CC.Stmt} (h : Priv.sequence a b = .Sskip) : a = .Sskip ∧ b = .Sskip := by
  unfold Priv.sequence at h
  split at h <;> simp_all

end EmbC.Clight.Proof
