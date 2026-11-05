import EmbC.Kernel.Conformance
import EmbC.Clight.Proof.Main
import EmbC.Clight.Proof.Determ
import EmbC.Clight.Proof.Backward

/-! The segment argument for the direct, nondeterministic kernel contracts.
Each target external outcome is matched by one permitted source outcome.
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight Behaviors

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

/-! ## Deterministic target segments -/

theorem tstar_detpath {ge : CC.CGenv} {X Y : CC.State} {t : CC.Trace} (h : TStar ge X t Y) :
    t = [] → DetPath (CC.Step2 ge) X Y := by
  induction h with
  | refl => intro _; exact .refl _
  | @step s₁ s₂ s₃ t₁ t₂ a _ ih =>
    intro ht
    have h1 : t₁ = [] := (List.append_eq_nil_iff.mp ht).1
    have h2 : t₂ = [] := (List.append_eq_nil_iff.mp ht).2
    subst h1
    refine .step ⟨a.1, fun t z hz => ?_⟩ (ih h2)
    obtain ⟨h3, h4⟩ := step2_determ_notExt a.2 a.1 hz
    exact ⟨h3.symm, h4.symm⟩

theorem dstar_detpath_last {ge : CC.CGenv} {Y : CC.State} :
    ∀ {s₂ : CC.State} {u : CC.Trace}, Star (DStep ge) s₂ u Y → u = [] →
      ∀ X, DStep ge X [] s₂ → ∃ Tb, DetPath (CC.Step2 ge) X Tb ∧ DStep ge Tb [] Y := by
  intro s₂ u b
  induction b with
  | refl => intro _ X a; exact ⟨X, .refl _, a⟩
  | @step s₂ s₃ s₄ t₃ t₄ a' _ ih =>
    intro hnil X a
    have h3 : t₃ = [] := (List.append_eq_nil_iff.mp hnil).1
    have h4 : t₄ = [] := (List.append_eq_nil_iff.mp hnil).2
    subst h3
    obtain ⟨Tb, hp, hl⟩ := ih h4 s₂ a'
    refine ⟨Tb, .step ⟨a.1, fun t z hz => ?_⟩ hp, hl⟩
    obtain ⟨h5, h6⟩ := step2_determ_notExt a.2 a.1 hz
    exact ⟨h5.symm, h6.symm⟩

theorem tplus_detpath {ge : CC.CGenv} {X Y : CC.State} {t : CC.Trace} (h : TPlus ge X t Y)
    (ht : t = []) : ∃ Tb, DetPath (CC.Step2 ge) X Tb ∧ DStep ge Tb [] Y := by
  obtain ⟨s₂, t₁, t₂, a, b, rfl⟩ := h.inv
  have h1 : t₁ = [] := (List.append_eq_nil_iff.mp ht).1
  have h2 : t₂ = [] := (List.append_eq_nil_iff.mp ht).2
  subst h1
  exact dstar_detpath_last b h2 X a

/-! ## The invariant -/

/-- The ordinary forward invariant at segment boundaries. -/
def BInv (P : Prog) (cp : CC.Program) (j0 : MemoryInjection) (m0 : Mem)
    (c : Semantics.State) (X : CC.State) : Prop :=
  ∃ i, Rel P cp.globalenv j0 m0 i c X

abbrev BSeg (P : Prog) (obs : Semantics.Observations) (cp : CC.Program) (j0 : MemoryInjection)
    (m0 : Mem) := Seg (sourceSemantics P obs) (targetSemantics cp)
      (BInv P cp j0 m0) (FinalRel P cp m0 j0)

theorem seg_prepend {P : Prog} {obs : Semantics.Observations} {cp : CC.Program}
    {j0 : MemoryInjection} {m0 : Mem} {n : Nat} {c c₁ : Semantics.State} {X : CC.State}
    (hs : Semantics.Step P obs c [] c₁) (h : BSeg P obs cp j0 m0 n c₁ X) :
    BSeg P obs cp j0 m0 n c X := by
  cases h with
  | error hs' hst =>
    exact .error (by simpa [sourceSemantics, CC.Eapp, CC.E0] using Star.step hs hs') hst
  | final hs' hf hno hex hfr =>
    exact .final (by simpa [sourceSemantics, CC.Eapp, CC.E0] using Star.step hs hs') hf hno hex hfr
  | pending hp hex hall =>
    refine .pending hp hex (fun t X' hst => ?_)
    obtain ⟨c', hplus, hinv⟩ := hall t X' hst
    exact ⟨c', by simpa [sourceSemantics] using Plus.intro hs hplus.star, hinv⟩

theorem ecall_not_silent {P : Prog} {c c₁ : Semantics.State} (he : IsECall c)
    (hn : Semantics.next P c = some (.silent c₁)) : False := by
  cases c with
  | callstate callee vs mem world k =>
    cases callee with
    | external ext => simp [Semantics.next, Semantics.nextCore] at hn
    | internal => exact he.elim
  | _ => exact he.elim

section ECall

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {k : Semantics.Cont} {K : CC.Cont}

theorem ecall_backward (hObs : Semantics.ObservationsTotal obs)
    (hKernel : KernelCompatible obs) (hKB : KernelBackwardCompatible obs)
    (hs : SCtx P cp) {dst : Option Var} {ext : Ext} {vs : List Val} {m : Mem}
    {ces : List CC.Expr} {types : List CC.Ty} {cargs : List CC.Val}
    (had : AdmFrom P (.call (.external ext) vs ⟨m, ()⟩ (.call dst env k)))
    (hg : GInv P cp.globalenv j0 m0 j m cm)
    (hfn : FnOK P fn cf) (hk : KR P m j (some (fn, cf)) k K)
    (henv : EnvRel (fnContext P fn) m j env le)
    (hargs : argsRel P m j vs cargs)
    (hev : CC.EvalExprlist cp.globalenv CC.emptyEnv le cm ces types cargs)
    (hdefined : Kernel.Defined P ⟨ext, vs, m⟩) :
    ∃ Tb, DetPath (CC.Step2 cp.globalenv)
        (.State cf (.Sbuiltin (dst.map CC.identOfString) (kernelExternal ext) types ces)
          K CC.emptyEnv le cm) Tb ∧
      (∃ t X', CC.Step2 cp.globalenv Tb t X') ∧
      ∀ t X', CC.Step2 cp.globalenv Tb t X' →
        ∃ c', Plus (Semantics.Step P obs)
          (.call (.external ext) vs ⟨m, ()⟩ (.call dst env k)) t c' ∧
          BInv P cp j0 m0 c' X' := by
  refine ⟨_, .refl _, ?_, ?_⟩
  · obtain ⟨reply, hallowed⟩ := Kernel.Defined.exists_reply hdefined
    obtain ⟨t0, hobs0⟩ := hObs P ext vs ⟨m, ()⟩ reply.result ⟨reply.after, ()⟩ hallowed
    have hfits0 : memoryFits P reply.after := (had.external (after := ⟨reply.after, ()⟩) hallowed).here.1
    obtain ⟨j', cm', crv, -, hcall, -⟩ :=
      hKernel P cp.globalenv hs.cenv ext vs ⟨m, ()⟩ reply.result ⟨reply.after, ()⟩
        j cm cargs t0 hg.2.2.1 hg.2.2.2 hargs hallowed hfits0 hobs0
    exact ⟨t0, _, CC.Step.builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hev hcall⟩
  · intro t X' hst
    unfold CC.Step2 at hst
    cases hst with
    | builtin _ _ _ _ _ _ _ _ _ vargs _ vres cm'' hev' hcall' =>
      have hva' := CC.evalExprlist_determ hev _ hev'
      subst hva'
      rcases hKB P cp.globalenv hs.cenv ext vs m j cm cargs t vres cm'' hg.2.2.1 hg.2.2.2
          hargs hcall' with hbad | ⟨rv, m', j', hallowed, hfits', hobs', hext, hret, hmem', hconst'⟩
      · exact (hbad hdefined).elim
      have hgrow : MemGrow m m' := MemGrow.returns hallowed
      have hstep : Semantics.Step P obs
          (.call (.external ext) vs ⟨m, ()⟩ (.call dst env k)) t
          (.returned rv ⟨m', ()⟩ (.call dst env k)) :=
        .external _ _ ext vs ⟨m, ()⟩ rv ⟨m', ()⟩ t ⟨_, rfl, hallowed, rfl⟩ hobs'
      have had' := had.external (after := ⟨m', ()⟩) hallowed
      refine ⟨_, Plus.one hstep, _, had', .inl ⟨rfl, j', cm'', ?_, ?_⟩⟩
      · exact hg.update hgrow hext hmem' hconst'
      · exact .inr ⟨fn, cf, dst, env, k, K, le, vres, rfl, hfn,
          hk.mono hgrow hext, henv.mono hgrow hext, hret, rfl⟩
    | skip_or_continue_loop1 _ _ _ _ _ _ _ _ h => rcases h with h | h <;> cases h
    | skip_break_switch _ _ _ _ _ _ h => rcases h with h | h <;> cases h

end ECall

/-! ## The segment property -/

theorem seg_of_rel {obs : Semantics.Observations} (hObs : Semantics.ObservationsTotal obs)
    (hKernel : KernelCompatible obs) (hKB : KernelBackwardCompatible obs)
    {P : Prog} {cp : CC.Program} (hwf : wellFormed P) (hl : P.toClight = .ok cp)
    {j0 : MemoryInjection} {m0 : Mem} :
    ∀ i c X, Rel P cp.globalenv j0 m0 i c X →
      ∃ n, BSeg P obs cp j0 m0 n c X := by
  classical
  have hs := sctx_of hwf hl
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro c X hrel
    by_cases hready : Semantics.KernelReady P c
    · obtain ⟨ext, vs, m, k, rfl, hdefined⟩ := hready
      obtain ⟨had, ⟨rfl, j, cm, hg, hm⟩ | hd⟩ := hrel
      · obtain ⟨fn, cf, dst, env, k', K, le, ces, types, cargs, rfl,
          hfn, hk, henv, hargs, hev, rfl⟩ := hm
        obtain ⟨Tb, hp, hex, hall⟩ :=
          ecall_backward hObs hKernel hKB hs had hg hfn hk henv hargs hev hdefined
        obtain ⟨n, hn⟩ := hp.counted
        exact ⟨n, .pending hn hex hall⟩
      · cases hd with
        | stuck hf => exact (hf.2.2 ⟨ext, vs, m, k, rfl, hdefined⟩).elim
        | step hn _ => simp [Semantics.next, Semantics.nextCore] at hn
    · cases hn : Semantics.next P c with
      | none =>
        by_cases hf : Semantics.final c
        · obtain ⟨rv, st, rfl⟩ := hf
          obtain ⟨w, cm, rfl, hfr⟩ := rel_final rfl hrel rfl
          refine ⟨0, .final (Star.refl _) rfl (fun t X' h => ?_) ⟨w, cm, rfl⟩
            (fun r' m' h => ?_)⟩
          · unfold targetSemantics CC.Step2 at h; cases h
          · simp only [targetSemantics, CC.State.Returnstate.injEq] at h
            obtain ⟨rfl, -, rfl⟩ := h
            exact hfr
        · have hfailed : Semantics.Failed P c := ⟨hn, hf, hready⟩
          exact ⟨0, .error (Star.refl _) ⟨fun _ _ ht => step_failed hfailed ht,
            fun _ _ hfin => hf ⟨_, _, hfin⟩⟩⟩
      | some a =>
        cases a with
        | silent c₁ =>
          have hstep : Semantics.Step P obs c CC.E0 c₁ := .silent _ _ hn
          rcases sim_step hKernel hwf hl hrel hstep with
              ⟨i', T', hr, hp | ⟨-, rfl, hlt⟩⟩ | ⟨he, -⟩
          · obtain ⟨Tb, hdp, hlast⟩ := tplus_detpath hp rfl
            obtain ⟨n, hn'⟩ := hdp.counted
            refine ⟨n, .pending hn' ⟨[], T', hlast.1⟩ (fun t X' hst => ?_)⟩
            obtain ⟨rfl, rfl⟩ := step2_determ_notExt hlast.2 hlast.1 hst
            exact ⟨c₁, Plus.one hstep, i', hr⟩
          · obtain ⟨n, hn'⟩ := ih i' hlt c₁ _ hr
            exact ⟨n, seg_prepend hstep hn'⟩
          · exact (ecall_not_silent he hn).elim
        | external ext args before rv after target =>
          exact (Semantics.next_ne_external hn).elim

end EmbC.Clight.Proof
