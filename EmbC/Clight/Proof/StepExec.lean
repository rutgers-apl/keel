import EmbC.Clight.Proof.StepBase

/-!
# Simulation of statement execution (memory-preserving statements)
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem step_silent {P : Prog} {obs : Semantics.Observations} {c c0 c' : Semantics.State} {t : CC.Trace}
    (hn : Semantics.next P c = some (.silent c0)) (h : Semantics.Step P obs c t c') :
    t = CC.E0 ∧ c' = c0 := by
  cases h with
  | silent _ hn' => rw [hn] at hn'; cases hn'; exact ⟨rfl, rfl⟩
  | external _ _ _ _ _ _ _ he _ =>
    obtain ⟨k, rfl, _, _⟩ := he
    simp [Semantics.next, Semantics.nextCore] at hn

theorem step_none {P : Prog} {obs : Semantics.Observations} {c c' : Semantics.State} {t : CC.Trace}
    (hn : Semantics.next P c = none) (h : Semantics.Step P obs c t c')
    (hnot : ¬ Semantics.KernelReady P c := by simp [Semantics.KernelReady]) : False := by
  cases h with
  | silent _ hn' => rw [hn] at hn'; cases hn'
  | external _ ext args st rv st' _ he _ =>
    obtain ⟨k, rfl, ha, _⟩ := he
    exact hnot ⟨ext, args, st.mem, k, by cases st; rfl, ha.defined⟩

theorem step_failed {P : Prog} {obs : Semantics.Observations} {c c' : Semantics.State}
    {t : CC.Trace} (hf : Semantics.Failed P c) (h : Semantics.Step P obs c t c') : False :=
  step_none hf.1 h hf.2.2

/-- Undefined values cannot pass the source return-type check. -/
theorem hasTy_undef_value (m : Mem) (t : Ty) : m.hasTy .undef t = false := by
  cases t <;> rfl

theorem hasTy_ne_undef {m : Mem} {v : Val} {t : Ty}
    (h : m.hasTy v t = true) : v ≠ .undef := by
  intro he
  have h' : m.hasTy .undef t = true := he ▸ h
  rw [hasTy_undef_value] at h'
  cases h'

theorem match_normal {ge : CC.CGenv} {P : Prog} {m : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn}
    {cf : CC.Function} {env : Env} {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont}
    (hfn : FnOK P fn cf) (hk : KR P m j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) m j env le) :
    MatchC P ge m j cm (.exec .skip env st k) (.State cf .Sskip K CC.emptyEnv le cm) :=
  ⟨fn, cf, .Sskip, K, le, hfn, .normal hk, henv, rfl⟩

theorem match_exec {ge : CC.CGenv} {P : Prog} {m : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn}
    {cf : CC.Function} {env : Env} {le : CC.TempEnv} {st : MachineStore} {s : Stmt} {k : Semantics.Cont}
    {s' : CC.Stmt} {K : CC.Cont}
    (hfn : FnOK P fn cf) (hp : Pos P m j fn cf (.exec s k) s' K)
    (henv : EnvRel (fnContext P fn) m j env le) :
    MatchC P ge m j cm (.exec s env st k) (.State cf s' K CC.emptyEnv le cm) :=
  ⟨fn, cf, s', K, le, hfn, hp, henv, rfl⟩

theorem sequence_cases (a b : CC.Stmt) :
    (a = .Sskip ∧ Priv.sequence a b = b) ∨ (a ≠ .Sskip ∧ b = .Sskip ∧ Priv.sequence a b = a) ∨
      (a ≠ .Sskip ∧ b ≠ .Sskip ∧ Priv.sequence a b = .Ssequence a b) := by
  unfold Priv.sequence
  split
  · exact .inl ⟨rfl, rfl⟩
  · rename_i h; exact .inr (.inl ⟨by simpa using h, rfl, rfl⟩)
  · rename_i h1 h2
    exact .inr (.inr ⟨by rintro rfl; simp_all, by rintro rfl; simp_all, rfl⟩)

theorem Doom.mono {P : Prog} {n n' : Nat} {c : Semantics.State} (h : Doom P n c) (hn : n ≤ n') :
    Doom P n' c := by
  induction h generalizing n' with
  | stuck hf => exact .stuck hf
  | step hs _ ih =>
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
    exact .step hs (ih (by omega))

theorem KR_none_callCont {P : Prog} {m : Mem} {j : MemoryInjection} {k : Semantics.Cont} {K : CC.Cont}
    (h : KR P m j none k K) : CC.callCont K = K ∧ CC.isCallCont K = true := by
  cases h <;> exact ⟨rfl, rfl⟩

/-- Return discards the current function's statement and loop continuations. -/
theorem KR.returnCont {P : Prog} {m : Mem} {j : MemoryInjection}
    {fn : Fn} {cf : CC.Function} {k : Semantics.Cont} {K : CC.Cont}
    (h : KR P m j (some (fn, cf)) k K) :
    ∃ k', k.returnCont = some (fn.ret, k') ∧ KR P m j none k' (CC.callCont K) := by
  induction k generalizing K with
  | stop => cases h
  | call => cases h
  | seq b k ih =>
    cases h with
    | seq hb hk =>
      obtain ⟨k', hc, hk'⟩ := ih hk
      exact ⟨k', hc, hk'⟩
    | seqSkip hb hk =>
      obtain ⟨k', hc, hk'⟩ := ih hk
      exact ⟨k', hc, hk'⟩
  | loop c body k ih =>
    cases h with
    | loop hb hk =>
      obtain ⟨k', hc, hk'⟩ := ih hk
      exact ⟨k', hc, hk'⟩
  | function rt k =>
    cases h with
    | fn hk =>
      refine ⟨k, rfl, ?_⟩
      simpa only [(KR_none_callCont hk).1] using hk

section Exec

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont} {d : Nat} {σ σ' : LSt}
  {s' : CC.Stmt}

theorem exec_seq_inner {a b : Stmt}
    (had : AdmFrom P (.exec (.seq a b) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hpos : Pos P st.mem j fn cf (.exec a (.seq b k)) s' K)
    (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.exec (.seq a b) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.seq a b) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  have hn : Semantics.next P (.exec (.seq a b) env st k) = some (.silent (.exec a env st (.seq b k))) := rfl
  obtain ⟨rfl, rfl⟩ := step_silent hn hstep
  exact goal_stutter (had.silent hn) hg (match_exec hfn hpos henv) (by simp only [mu, W, M]; omega)

/-- `seq` reached through its lowering (not through a skipped prefix). -/
theorem exec_seq {a b : Stmt}
    (had : AdmFrom P (.exec (.seq a b) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.seq a b) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.exec (.seq a b) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.seq a b) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @seq _ _ _ _ a' σ1 b' _ ha hb =>
    rcases sequence_cases a' b' with ⟨ha0, he⟩ | ⟨_, hb0, he⟩ | ⟨_, _, he⟩
    · rw [he]
      subst ha0
      exact exec_seq_inner had hg hfn (.execSkip ⟨_, _, _, ha⟩ (.normalSeq (.exec ⟨_, _, _, hb⟩ hk)))
        henv hstep
    · rw [he]
      subst hb0
      exact exec_seq_inner had hg hfn (.exec ⟨_, _, _, ha⟩ (.seqSkip ⟨_, _, _, hb⟩ hk)) henv hstep
    · rw [he]
      have hn : Semantics.next P (.exec (.seq a b) env st k) =
          some (.silent (.exec a env st (.seq b k))) := rfl
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      exact goal_plus (had.silent hn) hg
        (match_exec hfn (.exec ⟨_, _, _, ha⟩ (.seq ⟨_, _, _, hb⟩ hk)) henv) (tplus_one rfl)

theorem exec_assign (hs : SCtx P cp) {x : Var} {e : EmbC.Expr}
    (had : AdmFrom P (.exec (.assign x e) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.assign x e) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.assign x e) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.assign x e) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @assign _ _ _ _ ty r _ hty hle hacc =>
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    generalize hv : evalE P env st.mem e = ov
    rcases ov with _ | v
    · have hn : Semantics.next P (.exec (.assign x e) env st k) = none := by
        simp [Semantics.next, Semantics.nextCore, hv]
      exact (step_none hn hstep).elim
    generalize ha : env.assign st.mem x v = oa
    rcases oa with _ | env'
    · have hn : Semantics.next P (.exec (.assign x e) env st k) = none := by
        simp [Semantics.next, Semantics.nextCore, hv, ha]
      exact (step_none hn hstep).elim
    have hn : Semantics.next P (.exec (.assign x e) env st k) =
        some (.silent (.exec .skip env' st k)) := by
      simp [Semantics.next, Semantics.nextCore, hv, ha]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    obtain ⟨-, -, w, hw, le1, prun, fr, ev⟩ := expr_sim hx hfits.2 hle le v henv hv
    obtain ⟨t', ht', hhas, rfl⟩ := env_assign_inv ha
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    refine goal_plus (had.silent hn) hg
      (match_normal hfn hk ((henv.frame hc fr).set hc ht' (ValTy.of_hasTy hhas) hw)) ?_
    refine tplus_of_star_plus (prun.seq_star K) (tplus_one ?_)
    simp only [CC.doStep, ev le1 (Agree.refl _ _ _)]

theorem exec_ite (hs : SCtx P cp) {cnd : EmbC.Expr} {a b : Stmt}
    (had : AdmFrom P (.exec (.ite cnd a b) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.ite cnd a b) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.ite cnd a b) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.ite cnd a b) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @ite _ _ _ _ _ rc σ1 a' σ2 b' _ hle hacc ha hb =>
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    by_cases hvu : ¬ ∃ v, evalE P env st.mem cnd = some (.u32 v)
    · have hn : Semantics.next P (.exec (.ite cnd a b) env st k) = none := by
        simp only [Semantics.next, Semantics.nextCore]; split
        · exact absurd ⟨_, ‹_›⟩ hvu
        · rfl
      exact (step_none hn hstep).elim
    obtain ⟨v, hv⟩ := Classical.not_not.mp hvu
    have hn : Semantics.next P (.exec (.ite cnd a b) env st k) =
        some (.silent (.exec (if v = 0 then b else a) env st k)) := by
      simp [Semantics.next, Semantics.nextCore, hv]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    obtain ⟨-, -, w, hw, le1, prun, fr, ev⟩ := expr_sim hx hfits.2 hle le _ henv hv
    simp only [valRel] at hw; subst hw
    have hty : CC.typeof rc.ex = CC.tuint := by rw [(LE_static hle).2, accepts_u32 hacc]; rfl
    have henv1 := henv.frame hc fr
    have hif : TPlus cp.globalenv (.State cf (.Sifthenelse rc.ex a' b') K CC.emptyEnv le1 cm) CC.E0
        (.State cf (if decide (v ≠ 0) then a' else b') K CC.emptyEnv le1 cm) := by
      refine tplus_one ?_
      simp only [CC.doStep, ev le1 (Agree.refl _ _ _), hty, boolVal32]
    refine goal_plus (had.silent hn) hg ?_ (tplus_of_star_plus (prun.seq_star K) hif)
    by_cases h0 : v = 0
    · simp only [h0, ite_true, ne_eq, not_true_eq_false, decide_false]
      exact match_exec hfn (.exec ⟨_, _, _, hb⟩ hk) henv1
    · simp only [h0, ite_false, ne_eq, not_false_eq_true, decide_true, ite_true]
      exact match_exec hfn (.exec ⟨_, _, _, ha⟩ hk) henv1

theorem exec_while (hs : SCtx P cp) {cnd : EmbC.Expr} {body : Stmt}
    (had : AdmFrom P (.exec (.while cnd body) env st k))
    (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.while cnd body) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.while cnd body) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.while cnd body) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  have hlsw := hls
  cases hls with
  | @«while» _ _ _ _ rc σ1 b' _ hle hacc hb =>
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    by_cases hvu : ¬ ∃ v, evalE P env st.mem cnd = some (.u32 v)
    · have hn : Semantics.next P (.exec (.while cnd body) env st k) = none := by
        simp only [Semantics.next, Semantics.nextCore]; split
        · exact absurd ⟨_, ‹_›⟩ hvu
        · rfl
      exact (step_none hn hstep).elim
    obtain ⟨v, hv⟩ := Classical.not_not.mp hvu
    obtain ⟨-, -, w, hw, le1, prun, fr, ev⟩ := expr_sim hx hfits.2 hle le _ henv hv
    simp only [valRel] at hw; subst hw
    have hty : CC.typeof rc.ex = CC.tuint := by rw [(LE_static hle).2, accepts_u32 hacc]; rfl
    have henv1 := henv.frame hc fr
    generalize hs1 : Priv.sequence rc.pre (.Ssequence (.Sifthenelse rc.ex .Sskip .Sbreak) b') = s1
      at hlsw
    have hpre : TPlus cp.globalenv (.State cf (.Sloop s1 .Sskip) K CC.emptyEnv le cm) CC.E0
        (.State cf (if decide (v ≠ 0) then .Sskip else .Sbreak)
          (.Kseq b' (.Kloop1 s1 .Sskip K)) CC.emptyEnv le1 cm) := by
      refine tplus_of_plus_star (tplus_one (s' := .State cf s1 (.Kloop1 s1 .Sskip K) CC.emptyEnv le cm) rfl) ?_
      rw [← hs1]
      refine tstar_trans0 (prun.seq_star _) ?_
      refine tstar_trans0 (tstar_one rfl) ?_
      rw [hs1]
      refine tstar_one ?_
      simp only [CC.doStep, ev le1 (Agree.refl _ _ _), hty, boolVal32]; rfl
    by_cases h0 : v = 0
    · have hn : Semantics.next P (.exec (.while cnd body) env st k) =
          some (.silent (.exec .skip env st k)) := by
        simp [Semantics.next, Semantics.nextCore, hv, h0]
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      simp only [h0, ne_eq, not_true_eq_false, decide_false] at hpre
      refine goal_plus (had.silent hn) hg (match_normal hfn hk henv1) ?_
      refine tplus_of_plus_star hpre ?_
      exact tstar_trans0 (tstar_one rfl) (tstar_one rfl)
    · have hn : Semantics.next P (.exec (.while cnd body) env st k) =
          some (.silent (.exec body env st (.loop cnd body k))) := by
        simp only [Semantics.next, Semantics.nextCore, hv]
        split
        · rename_i hz
          exact (h0 hz).elim
        · rfl
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      simp only [h0, ne_eq, not_false_eq_true, decide_true, ite_true] at hpre
      refine goal_plus (had.silent hn) hg
        (match_exec hfn (.exec ⟨_, _, _, hb⟩ (.loop ⟨_, _, _, hlsw⟩ hk)) henv1) ?_
      exact tplus_of_plus_star hpre (tstar_one rfl)

theorem exec_ret0
    (had : AdmFrom P (.exec (.ret none) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (_hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.ret none) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.ret none) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.ret none) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls
  obtain ⟨k', hcont, hk'⟩ := hk.returnCont
  cases hr : fn.ret with
  | none =>
    have hn : Semantics.next P (.exec (.ret none) env st k) =
        some (.silent (.returned none st k')) := by
      simp [Semantics.next, Semantics.nextCore, Semantics.returnTarget, hcont, hr]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    exact goal_plus (had.silent hn) hg (.inl ⟨.Vundef, _, rfl, hk', rfl⟩) (tplus_one rfl)
  | some ty =>
    have hn : Semantics.next P (.exec (.ret none) env st k) = none := by
      simp [Semantics.next, Semantics.nextCore, Semantics.returnTarget, hcont, hr]
    exact (step_none hn hstep).elim

theorem exec_ret1 (hs : SCtx P cp) {e : EmbC.Expr}
    (had : AdmFrom P (.exec (.ret (some e)) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.ret (some e)) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.ret (some e)) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.ret (some e)) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @ret1 _ _ _ ty r _ hres hle hacc =>
    have hres' : fn.ret = some ty := hres
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    generalize hv : evalE P env st.mem e = ov
    rcases ov with _ | v
    · have hn : Semantics.next P (.exec (.ret (some e)) env st k) = none := by
        simp [Semantics.next, Semantics.nextCore, hv]
      exact (step_none hn hstep).elim
    obtain ⟨k', hcont, hk'⟩ := hk.returnCont
    by_cases hhas : st.mem.hasTy v ty = true
    · have hn : Semantics.next P (.exec (.ret (some e)) env st k) =
          some (.silent (.returned (some v) st k')) := by
        simp [Semantics.next, Semantics.nextCore, hv, Semantics.returnTarget, hcont, hres', hhas]
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      have hu : v ≠ .undef := hasTy_ne_undef hhas
      obtain ⟨hty, -, w, hw, le1, prun, fr, ev⟩ := expr_sim hx hfits.2 hle le v henv hv
      have hret : cf.fn_return = type ty := by
        obtain ⟨_, _, _, rfl⟩ := (lowerFunction_inv hfn.low).body
        show (fn.ret.map type).getD .Tvoid = _
        rw [hres']; rfl
      have hcast := cast_accepts hw hty hacc hu cm
      refine goal_plus (had.silent hn) hg (.inl ⟨w, _, hw, hk', rfl⟩) ?_
      refine tplus_of_star_plus (prun.seq_star K) (tplus_one ?_)
      simp only [CC.doStep, ev le1 (Agree.refl _ _ _), (LE_static hle).2, hret, hcast]
      rfl
    · have hn : Semantics.next P (.exec (.ret (some e)) env st k) = none := by
        simp [Semantics.next, Semantics.nextCore, hv, Semantics.returnTarget, hcont, hres', hhas]
      exact (step_none hn hstep).elim

end Exec

end EmbC.Clight.Proof
