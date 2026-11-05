import EmbC.Clight.Proof.Match
import EmbC.Clight.Proof.ExprSim

/-!
# Infrastructure for the simulation step

Static program facts, monotonicity of the matching relations along memory
growth, and the shapes of simulation-step conclusions.
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-! ## Static facts about the program -/

structure SCtx (P : Prog) (cp : CC.Program) : Prop where
  wf : wellFormed P
  low : ProgLowered P cp
  toClight : P.toClight = .ok cp
  cenv : cp.globalenv.genv_cenv = compositeEnv P
  scal : ∀ d ∈ P.structs, Scalars d.fields
  ids : ∀ d ∈ P.structs, (idents d.fields).Nodup

theorem sctx_of {P : Prog} {cp : CC.Program} (hwf : wellFormed P) (hl : P.toClight = .ok cp) :
    SCtx P cp := by
  refine ⟨hwf, lowerProgram_inv hl, hl, (programRel_of hwf hl).2.1, ?_, ?_⟩
  · intro d hd x hx
    exact ((hwf.2.2.2.1 d hd).2 x hx).1
  · intro d hd
    have hasc := lowerProgram_fieldNames hl d hd
    have hnd := (hwf.2.2.2.1 d hd).1
    have : idents d.fields = (d.fields.map (·.1)).map CC.identOfString := by
      simp [idents, List.map_map]
    rw [this]
    refine nodup_map_on (fun x hx y hy he => ?_) hnd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact identOfString_inj_ascii (hasc a ha) (hasc b hb) he

theorem xctx_of {P : Prog} {cp : CC.Program} (hs : SCtx P cp) {fn : Fn} {cf : CC.Function}
    (hfn : FnOK P fn cf) {m : Mem} {j : MemoryInjection} {cm : CC.Mem}
    (hmem : memoryRel P j m cm) (hc : ConstRel P cp.globalenv j m cm) (hfit : memoryFits P m) :
    XCtx P cp.globalenv (fnContext P fn) m j cm :=
  { prog := rfl
    ok := ctxOK_fnContext (lowerFunction_inv hfn.low)
    cenv := hs.cenv
    scal := hs.scal
    ids := hs.ids
    consts := hs.wf.2.2.1
    mem := hmem
    const := hc
    fits := hfit }

/-! ## Monotonicity of the matching relations -/

theorem KR.mono {P : Prog} {m m' : Mem} {j j' : MemoryInjection} (hg : MemGrow m m')
    (hj : j.Extends j' m) {idx : Option (Fn × CC.Function)} {k : Semantics.Cont} {K : CC.Cont}
    (h : KR P m j idx k K) : KR P m' j' idx k K := by
  induction h with
  | seq hb _ ih => exact .seq hb ih
  | seqSkip hb _ ih => exact .seqSkip hb ih
  | loop hb _ ih => exact .loop hb ih
  | fn _ ih => exact .fn ih
  | stop => exact .stop
  | call hfn henv _ ih => exact .call hfn (henv.mono hg hj) ih

theorem Pos.mono {P : Prog} {m m' : Mem} {j j' : MemoryInjection} (hg : MemGrow m m')
    (hj : j.Extends j' m) {fn : Fn} {cf : CC.Function} {sp : SPos} {s' : CC.Stmt} {K : CC.Cont}
    (h : Pos P m j fn cf sp s' K) : Pos P m' j' fn cf sp s' K := by
  induction h with
  | exec hs hk => exact .exec hs (hk.mono hg hj)
  | execSkip hs _ ih => exact .execSkip hs ih
  | normal hk => exact .normal (hk.mono hg hj)
  | normalSeq _ ih => exact .normalSeq ih
  | brk hk => exact .brk (hk.mono hg hj)

theorem GInv.update {P : Prog} {ge : CC.CGenv} {j0 : MemoryInjection} {m0 : Mem}
    {j j' : MemoryInjection} {m m' : Mem} {cm cm' : CC.Mem} (h : GInv P ge j0 m0 j m cm)
    (hg : MemGrow m m') (hj : j.Extends j' m) (hmem : memoryRel P j' m' cm')
    (hc : ConstRel P ge j' m' cm') : GInv P ge j0 m0 j' m' cm' :=
  ⟨Extends.trans h.1 hj h.2.1.size, h.2.1.trans hg, hmem, hc⟩

/-! ## Admissibility along steps -/

theorem AdmFrom.here {P : Prog} {c : Semantics.State} (h : AdmFrom P c) : stateFits P c :=
  h c (.refl c)

theorem AdmFrom.next {P : Prog} {c c' : Semantics.State} (h : AdmFrom P c) {a : Semantics.Action}
    (hn : Semantics.next P c = some a) (ht : a.target = c') : AdmFrom P c' :=
  fun c'' h'' => h c'' (.step c c' c'' (.inl ⟨a, hn, ht⟩) h'')

theorem AdmFrom.silent {P : Prog} {c c' : Semantics.State} (h : AdmFrom P c)
    (hn : Semantics.next P c = some (.silent c')) : AdmFrom P c' :=
  h.next hn rfl

theorem AdmFrom.external {P : Prog} {ext : Ext} {args : List Val}
    {before after : MachineStore} {k : Semantics.Cont} {result : Option Val}
    (h : AdmFrom P (.call (.external ext) args before k))
    (ha : Oracle.Returns P ⟨ext, args, before.mem⟩ ⟨result, after.mem⟩) :
    AdmFrom P (.returned result after k) := by
  intro c'' h''
  apply h c''
  refine .step _ _ _ ?_ h''
  cases before with
  | mk mem world =>
    cases after with
    | mk mem' world' =>
      cases world
      cases world'
      exact .inr ⟨ext, args, mem, k, result, mem', rfl, ha, rfl⟩

/-! ## Shapes of the conclusion -/

/-- The conclusion of the simulation step. -/
def SimGoal (P : Prog) (ge : CC.CGenv) (j0 : MemoryInjection) (m0 : Mem) (i : Nat)
    (c' : Semantics.State) (T : CC.State) (t : CC.Trace) : Prop :=
  ∃ i' T', Rel P ge j0 m0 i' c' T' ∧ (TPlus ge T t T' ∨ (t = CC.E0 ∧ T' = T ∧ i' < i))

/-- The conclusion of the simulation step for a kernel call, whose target
execution ends with an external step. -/
def SimGoalX (P : Prog) (ge : CC.CGenv) (j0 : MemoryInjection) (m0 : Mem) (i : Nat)
    (c' : Semantics.State) (T : CC.State) (t : CC.Trace) : Prop :=
  SimGoal P ge j0 m0 i c' T t ∨ ∃ i' T', Rel P ge j0 m0 i' c' T' ∧ TExt ge T t T'

section Goals

variable {P : Prog} {ge : CC.CGenv} {j0 : MemoryInjection} {m0 : Mem} {i : Nat}
  {c' : Semantics.State} {T : CC.State}

theorem goal_doom {n : Nat} (had : AdmFrom P c') (hd : Doom P n c') (hn : n < i) :
    SimGoal P ge j0 m0 i c' T CC.E0 :=
  ⟨n, T, ⟨had, .inr hd⟩, .inr ⟨rfl, rfl, hn⟩⟩

theorem goal_stuck {c : Semantics.State} (had : AdmFrom P c) (hf : Semantics.Failed P c) (hi : 0 < i) :
    SimGoal P ge j0 m0 i c T CC.E0 :=
  goal_doom had (.stuck hf) hi

theorem goal_plus {t : CC.Trace} {T' : CC.State} {j : MemoryInjection} {cm : CC.Mem}
    (had : AdmFrom P c') (hg : GInv P ge j0 m0 j (Semantics.stateKernelState c').mem cm)
    (hm : MatchC P ge (Semantics.stateKernelState c').mem j cm c' T') (hp : TPlus ge T t T') :
    SimGoal P ge j0 m0 i c' T t :=
  ⟨mu c', T', ⟨had, .inl ⟨rfl, j, cm, hg, hm⟩⟩, .inl hp⟩

theorem goal_stutter {j : MemoryInjection} {cm : CC.Mem}
    (had : AdmFrom P c') (hg : GInv P ge j0 m0 j (Semantics.stateKernelState c').mem cm)
    (hm : MatchC P ge (Semantics.stateKernelState c').mem j cm c' T) (hlt : mu c' < i) :
    SimGoal P ge j0 m0 i c' T CC.E0 :=
  ⟨mu c', T, ⟨had, .inl ⟨rfl, j, cm, hg, hm⟩⟩, .inr ⟨rfl, rfl, hlt⟩⟩

end Goals

/-! ## The measure -/

theorem M_pos (k : Semantics.Cont) : 0 < M k := by
  cases k <;> simp [M] <;> omega

theorem mu_exec_pos {s : Stmt} {env : Env} {st : MachineStore} {k : Semantics.Cont} :
    0 < mu (.exec s env st k) := by
  have := W_pos s; simp only [mu]; omega

end EmbC.Clight.Proof
