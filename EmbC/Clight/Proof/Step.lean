import EmbC.Clight.Proof.StepMem
import EmbC.Clight.Proof.StepECall
import EmbC.Clight.Proof.StepEntry

/-!
# The simulation step
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-- Only `skip` and sequences of skipped statements lower to `Sskip`. -/
theorem lowers_skip {ctx : LCtx} {d : Nat} {σ σ' : LSt} {s : Stmt} {s0 : CC.Stmt}
    (h : LS ctx d σ s s0 σ') (hz : s0 = .Sskip) :
    s = .skip ∨ ∃ a b, s = .seq a b ∧ (∃ d σ σ', LS ctx d σ a .Sskip σ') ∧
      (∃ d σ σ', LS ctx d σ b .Sskip σ') := by
  cases h with
  | skip => exact .inl rfl
  | seq ha hb =>
    obtain ⟨rfl, rfl⟩ := sequence_eq_skip hz
    exact .inr ⟨_, _, rfl, ⟨_, _, _, ha⟩, ⟨_, _, _, hb⟩⟩
  | assign => cases (sequence_eq_skip hz).2
  | store => cases (sequence_eq_skip (sequence_eq_skip (sequence_eq_skip hz).2).2).2
  | setField => cases (sequence_eq_skip (sequence_eq_skip hz).2).2
  | ite => cases (sequence_eq_skip hz).2
  | «while» => cases hz
  | call => cases (sequence_eq_skip hz).2
  | ecall => cases (sequence_eq_skip hz).2
  | ret0 => cases hz
  | ret1 => cases (sequence_eq_skip hz).2
  | brk => cases hz

/-- Configurations about to perform a kernel call. -/
def IsECall : Semantics.State → Prop
  | .callstate (.external _) _ _ _ _ => True
  | _ => False

section Assemble

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont} {s' : CC.Stmt}

theorem exec_case (hs : SCtx P cp) {s : Stmt}
    (had : AdmFrom P (.exec s env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hpos : Pos P st.mem j fn cf (.exec s k) s' K)
    (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.exec s env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec s env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hpos with
  | exec hls hk =>
    obtain ⟨d, σ, σ', hls⟩ := hls
    cases s with
    | skip => cases hls; exact normal_skip had hg hfn hk henv hstep
    | assign => exact exec_assign hs had hg hfn hls hk henv hstep
    | store => exact exec_store hs had hg hfn hls hk henv hstep
    | setField => exact exec_setField hs had hg hfn hls hk henv hstep
    | seq => exact exec_seq had hg hfn hls hk henv hstep
    | ite => exact exec_ite hs had hg hfn hls hk henv hstep
    | «while» => exact exec_while hs had hg hfn hls hk henv hstep
    | call => exact exec_call hs had hg hfn hls hk henv hstep
    | ecall => exact exec_ecall hs had hg hfn hls hk henv hstep
    | ret e =>
      cases e with
      | none => exact exec_ret0 had hg hfn hls hk hstep
      | some => exact exec_ret1 hs had hg hfn hls hk henv hstep
    | brk => cases hls; exact outcome_brk had hg hfn (.brk hk) henv hstep
  | execSkip hsk hp =>
    obtain ⟨d, σ, σ', hsk⟩ := hsk
    rcases lowers_skip hsk rfl with rfl | ⟨a, b, rfl, ha, hb⟩
    · exact outcome_normal had hg hfn hp henv hstep
    · exact exec_seq_inner had hg hfn (.execSkip ha (.normalSeq (.execSkip hb hp))) henv hstep
  | normal hk => exact normal_skip had hg hfn hk henv hstep
  | normalSeq hp => exact outcome_normal had hg hfn (.normalSeq hp) henv hstep
  | brk hk => exact outcome_brk had hg hfn (.brk hk) henv hstep

end Assemble

theorem sim_step {obs : Semantics.Observations} (hKernel : KernelCompatible obs) {P : Prog}
    {cp : CC.Program} (hwf : wellFormed P) (hl : P.toClight = .ok cp)
    {j0 : MemoryInjection} {m0 : Mem} {i : Nat} {c : Semantics.State} {T : CC.State}
    {t : CC.Trace} {c' : Semantics.State}
    (hrel : Rel P cp.globalenv j0 m0 i c T) (hstep : Semantics.Step P obs c t c') :
    (∃ i' T', Rel P cp.globalenv j0 m0 i' c' T' ∧
      (TPlus cp.globalenv T t T' ∨ (t = CC.E0 ∧ T' = T ∧ i' < i))) ∨
    (IsECall c ∧ ∃ i' T', Rel P cp.globalenv j0 m0 i' c' T' ∧ TExt cp.globalenv T t T') := by
  have hs := sctx_of hwf hl
  obtain ⟨had, ⟨rfl, j, cm, hg, hm⟩ | hd⟩ := hrel
  · show SimGoal P cp.globalenv j0 m0 (mu c) c' T t ∨ (IsECall c ∧ _)
    cases c with
    | regular s env mem orc k =>
      obtain ⟨fn, cf, s', K, le, hfn, hpos, henv, rfl⟩ := hm
      exact .inl (exec_case (st := ⟨mem, orc⟩) hs had hg hfn hpos henv hstep)
    | callstate callee vs mem orc k =>
      cases callee with
      | internal f =>
        obtain ⟨fn, cf, cargs, K, hfind, hfn, hargs, hk, rfl⟩ := hm
        exact .inl (call_step (st := ⟨mem, orc⟩) hs had hg hfind hfn hargs hk hstep)
      | external ext =>
        obtain ⟨fn, cf, dst, env, k', K, le, ces, types, cargs, rfl, hfn, hk, henv, hargs, hev, rfl⟩ := hm
        exact .inr ⟨trivial, external_step (st := ⟨mem, orc⟩) hKernel hs had hg hfn hk henv hargs hev hstep⟩
    | returnstate rv mem orc k =>
      exact .inl (returned_step (st := ⟨mem, orc⟩) had hg hm hstep)
  · cases hd with
    | stuck hf => exact (step_failed hf hstep).elim
    | step hn hd' =>
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      exact .inl ⟨_, T, ⟨had.silent hn, .inr hd'⟩, .inr ⟨rfl, rfl, Nat.lt_succ_self _⟩⟩

end EmbC.Clight.Proof
