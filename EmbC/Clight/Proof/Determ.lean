import EmbC.Clight.Proof.Target
import CCLib.Determinism

/-!
# Determinism of non-external Clight steps

A copy of Clean's `step_determ` restricted to states that do not perform an
external call.  It therefore needs neither external-call determinism axiom.
-/

namespace EmbC.Clight.Proof

open CC

set_option maxHeartbeats 2000000 in
theorem step2_determ_notExt {ge : CGenv} {s t1 s1 t2 s2} (hs : NotExt s)
    (h1 : Step2 ge s t1 s1) (h2 : Step2 ge s t2 s2) : t1 = t2 ∧ s1 = s2 := by
  have hfe := entryDeterm_functionEntry2 ge
  unfold Step2 at h1 h2
  cases h1 <;> cases h2 <;>
    try (first
          | exact ⟨rfl, rfl⟩
          | (exfalso; simp_all [isCallCont]; done)
          | (exfalso; simp [NotExt, isExtState] at hs; done))
  case assign.assign =>
    rename_i hlv1 he1 hc1 hal1 _ _ _ _ _ _ hal2 hc2 hlv2 he2
    refine ⟨rfl, ?_⟩
    obtain ⟨hb, ho, hbf⟩ := evalLvalue_determ hlv1 hlv2
    subst hb; subst ho; subst hbf
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hc1] at hc2
    simp only [Option.some.injEq] at hc2
    subst hc2
    rw [assignLoc_determ hal1 hal2]
  case set.set =>
    rename_i _ he1 _ he2
    refine ⟨rfl, ?_⟩
    rw [evalExpr_determ he1 he2]
  case call.call =>
    rename_i hcf1 he1 hel1 hff1 _ _ _ _ _ _ _ hff2 _ hcf2 he2 hel2
    refine ⟨rfl, ?_⟩
    rw [hcf1] at hcf2
    simp only [Cop.FunCase.f.injEq] at hcf2
    obtain ⟨e1, e2, e3⟩ := hcf2
    subst e1; subst e2; subst e3
    have hvf := evalExpr_determ he1 he2
    subst hvf
    have hva := evalExprlist_determ hel1 _ hel2
    subst hva
    rw [hff1] at hff2
    simp only [Option.some.injEq] at hff2
    subst hff2
    rfl
  case ifthenelse.ifthenelse =>
    rename_i he1 hb1 _ _ hb2 he2
    refine ⟨rfl, ?_⟩
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hb1] at hb2
    simp_all
  case return_0.return_0 =>
    rename_i hf1 _ hf2
    refine ⟨rfl, ?_⟩
    rw [hf1] at hf2
    simp_all
  case return_1.return_1 =>
    rename_i he1 hc1 hf1 _ _ _ hc2 hf2 he2
    refine ⟨rfl, ?_⟩
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hc1] at hc2
    rw [hf1] at hf2
    simp_all
  case skip_call.skip_call =>
    rename_i _ hf1 _ _ hf2
    refine ⟨rfl, ?_⟩
    rw [hf1] at hf2
    simp_all
  case switch.switch =>
    rename_i he1 hn1 _ _ hn2 he2
    refine ⟨rfl, ?_⟩
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hn1] at hn2
    simp_all
  case goto.goto =>
    rename_i hfl1 _ _ hfl2
    refine ⟨rfl, ?_⟩
    rw [hfl1] at hfl2
    simp_all
  case internal_function.internal_function =>
    rename_i hfe1 _ _ _ hfe2
    obtain ⟨he, hle, hm⟩ := hfe _ _ _ _ _ _ _ _ _ hfe1 hfe2
    subst he; subst hle; subst hm
    exact ⟨rfl, rfl⟩

end EmbC.Clight.Proof
