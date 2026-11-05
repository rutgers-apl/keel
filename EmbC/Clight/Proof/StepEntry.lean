import EmbC.Clight.Proof.StepCont

/-!
# Function entry
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-! ## Temporaries introduced by the lowering are fresh -/

def TempsFresh (ctx : LCtx) (σ : LSt) : Prop := ∀ p ∈ σ.temps, ∃ n, p.1 = freshId ctx n

theorem TempsFresh.cap {ctx : LCtx} {σ : LSt} (e : LX) (h : TempsFresh ctx σ) :
    TempsFresh ctx (capState ctx σ e) := by
  intro p hp
  simp only [capState, LSt.temps_mk, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact h p hp
  · exact ⟨_, rfl⟩

theorem TempsFresh.fresh {ctx : LCtx} {σ : LSt} (t : CC.Ty) (h : TempsFresh ctx σ) :
    TempsFresh ctx (freshState ctx σ t) := by
  intro p hp
  simp only [freshState, LSt.temps_mk, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact h p hp
  · exact ⟨_, rfl⟩

theorem LE_fresh {ctx : LCtx} {σ : LSt} {e : EmbC.Expr} {r : LX} {σ' : LSt}
    (h : LE ctx σ e r σ') : TempsFresh ctx σ → TempsFresh ctx σ' := by
  induction h with
  | var _ => exact id
  | lit32 => exact id
  | named => exact id
  | lit64 => exact id
  | null => exact id
  | cload _ _ _ ih => exact fun h => (ih h).cap _
  | bin _ _ _ iha ihb => exact fun h => (ihb ((iha h).cap _)).cap _
  | lnot _ _ ih => exact ih
  | bnot _ _ ih => exact ih
  | land _ _ _ _ iha ihb => exact fun h => (ihb ((iha h).cap _)).fresh _
  | lor _ _ _ _ iha ihb => exact fun h => (ihb ((iha h).cap _)).fresh _
  | cast _ _ _ ih => exact ih
  | index _ _ _ _ _ ihp ihi => exact fun h => (ihi ((ihp h).cap _)).cap _
  | field _ _ _ ih => exact ih
  | padd _ _ _ _ _ ihp ihi => exact fun h => (ihi ((ihp h).cap _)).cap _

theorem LA_fresh {ctx : LCtx} {σ : LSt} {es : List EmbC.Expr} {pre : CC.Stmt} {rs : List LX}
    {σ' : LSt} (h : LA ctx σ es pre rs σ') : TempsFresh ctx σ → TempsFresh ctx σ' := by
  induction h with
  | nil => exact id
  | cons he _ ih => exact fun h => ih ((LE_fresh he h).cap _)

theorem LS_fresh {ctx : LCtx} {d : Nat} {σ : LSt} {s : Stmt} {s' : CC.Stmt} {σ' : LSt}
    (h : LS ctx d σ s s' σ') : TempsFresh ctx σ → TempsFresh ctx σ' := by
  induction h with
  | skip => exact id
  | assign _ he _ => exact LE_fresh he
  | store hp _ _ hi _ he _ =>
    exact fun h => LE_fresh he ((LE_fresh hi ((LE_fresh hp h).cap _)).cap _)
  | setField hp _ _ he _ => exact fun h => LE_fresh he ((LE_fresh hp h).cap _)
  | seq _ _ iha ihb => exact fun h => ihb (iha h)
  | ite hc _ _ _ iha ihb => exact fun h => ihb (iha (LE_fresh hc h))
  | «while» hc _ _ ih => exact fun h => ih (LE_fresh hc h)
  | call _ ha _ _ => exact LA_fresh ha
  | ecall ha _ _ => exact LA_fresh ha
  | ret0 _ => exact id
  | ret1 _ he _ => exact LE_fresh he
  | brk _ => exact id

/-! ## Parameters -/

theorem bindParams_shape {m : Mem} : ∀ {ps : List (Var × Ty)} {vs : List Val} {penv : Env},
    bindParams m ps vs = some penv →
    penv.map (fun b => (b.1, b.2.1)) = ps ∧ ∀ b ∈ penv, m.hasTy b.2.2 b.2.1 = true
  | [], [], penv, h => by simp only [bindParams, Option.some.injEq] at h; subst h; simp
  | (x, t) :: ps, v :: vs, penv, h => by
    simp only [bindParams] at h
    split at h
    · rename_i hhas
      generalize hb : bindParams m ps vs = ob at h
      rcases ob with _ | penv'
      · cases h
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := bindParams_shape hb
      refine ⟨by simp [h1], fun b hb' => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hhas
      · exact h2 b hb'
    · cases h
  | [], _ :: _, penv, h => by simp [bindParams] at h
  | _ :: _, [], penv, h => by simp [bindParams] at h

theorem bindTemps {P : Prog} {m : Mem} {j : MemoryInjection} :
    ∀ (ps : List (Var × Ty)) (vs : List Val) (ws : List CC.Val) (penv : Env) (le0 : CC.TempEnv),
    bindParams m ps vs = some penv → argsRel P m j vs ws →
    (ps.map (fun p => CC.identOfString p.1)).Nodup →
    ∃ le', CC.bindParameterTemps (ps.map fun (x, t) => (CC.identOfString x, type t)) ws le0 =
        some le' ∧
      (∀ id, id ∉ ps.map (fun p => CC.identOfString p.1) → le'.get id = le0.get id) ∧
      ∀ b ∈ penv, ∃ w, le'.get (CC.identOfString b.1) = some w ∧ valRel P m j b.2.2 w
  | [], [], [], penv, le0, h, _, _ => by
    simp only [bindParams, Option.some.injEq] at h; subst h
    exact ⟨le0, rfl, fun _ _ => rfl, fun b hb => by cases hb⟩
  | (x, t) :: ps, v :: vs, w :: ws, penv, le0, h, ha, hnd => by
    simp only [bindParams] at h
    split at h
    · generalize hb : bindParams m ps vs = ob at h
      rcases ob with _ | penv'
      · cases h
      simp only [Option.some.injEq] at h; subst h
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨le', h1, h2, h3⟩ := bindTemps ps vs ws penv' (le0.set (CC.identOfString x) w) hb
        ha.2 hnd.2
      refine ⟨le', h1, fun id hid => ?_, fun b hb' => ?_⟩
      · simp only [List.map_cons, List.mem_cons, not_or] at hid
        rw [h2 id hid.2, CC.PTree.gso _ _ _ _ (Ne.symm hid.1)]
      · rcases List.mem_cons.mp hb' with rfl | hb'
        · refine ⟨w, ?_, ha.1⟩
          rw [h2 _ hnd.1, CC.PTree.gss]
        · exact h3 b hb'
    · cases h
  | [], _ :: _, _, _, _, h, _, _ => by simp [bindParams] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [bindParams] at h
  | [], [], _ :: _, _, _, _, ha, _ => ha.elim
  | _ :: _, _ :: _, [], _, _, _, ha, _ => ha.elim

theorem createUndef_get : ∀ (temps : List (CC.Ident × CC.Ty)) (id : CC.Ident),
    id ∈ temps.map (·.1) → (CC.createUndefTemps temps).get id = some .Vundef
  | [], _, h => by cases h
  | (id', _) :: temps, id, h => by
    simp only [CC.createUndefTemps]
    by_cases he : id' = id
    · subst he; exact CC.PTree.gss _ _ _
    · rw [CC.PTree.gso _ _ _ _ he]
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm he
      · exact createUndef_get temps id h

/-! ## Initialisation of locals -/

theorem init_one {P : Prog} {m : Mem} {j : MemoryInjection} {ge : CC.CGenv} {cm : CC.Mem}
    {le : CC.TempEnv} (x : Var) {t : Ty} (hs : t.isStruct = false)
    (h : le.get (CC.identOfString x) = some .Vundef) :
    ∃ le1, PRun ge cm (Priv.initializeLocal x t) le le1 ∧
      (∀ id, id ≠ CC.identOfString x → le1.get id = le.get id) ∧
      ∃ w, le1.get (CC.identOfString x) = some w ∧ valRel P m j t.zero w := by
  cases t with
  | u32 =>
    exact ⟨_, .set rfl, fun id hid => CC.PTree.gso _ _ _ _ (Ne.symm hid), _, CC.PTree.gss _ _ _, rfl⟩
  | u64 =>
    exact ⟨_, .set rfl, fun id hid => CC.PTree.gso _ _ _ _ (Ne.symm hid), _, CC.PTree.gss _ _ _, rfl⟩
  | ptr t =>
    exact ⟨_, .set rfl, fun id hid => CC.PTree.gso _ _ _ _ (Ne.symm hid), _, CC.PTree.gss _ _ _, rfl⟩
  | bpfptr => exact ⟨le, .skip le, fun _ _ => rfl, _, h, rfl⟩
  | struct s => cases hs

theorem init_run {P : Prog} {m : Mem} {j : MemoryInjection} {ge : CC.CGenv} {cm : CC.Mem} :
    ∀ (ls : List (Var × Ty)) (le : CC.TempEnv), (∀ d ∈ ls, d.2.isStruct = false) →
    (ls.map (fun p => CC.identOfString p.1)).Nodup →
    (∀ d ∈ ls, le.get (CC.identOfString d.1) = some .Vundef) →
    ∃ le', PRun ge cm (ls.foldr (fun (x, t) rest => Priv.sequence (Priv.initializeLocal x t) rest)
        .Sskip) le le' ∧
      (∀ id, id ∉ ls.map (fun p => CC.identOfString p.1) → le'.get id = le.get id) ∧
      ∀ d ∈ ls, ∃ w, le'.get (CC.identOfString d.1) = some w ∧ valRel P m j d.2.zero w
  | [], le, _, _, _ => ⟨le, .skip le, fun _ _ => rfl, fun d hd => by cases hd⟩
  | (x, t) :: ls, le, hs, hnd, hu => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨le1, p1, f1, w, hw, hrel⟩ :=
      init_one (P := P) (m := m) (j := j) (ge := ge) (cm := cm) x (hs (x, t) (.head _))
        (hu (x, t) (.head _))
    obtain ⟨le', p2, f2, h2⟩ := init_run ls le1 (fun d hd => hs d (.tail _ hd)) hnd.2
      (fun d hd => by
        rw [f1 _ (fun he => hnd.1 (he ▸ List.mem_map_of_mem hd))]
        exact hu d (.tail _ hd))
    refine ⟨le', PRun.sequence p1 p2, fun id hid => ?_, fun d hd => ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at hid
      rw [f2 id hid.2, f1 id hid.1]
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨w, by rw [f2 _ hnd.1]; exact hw, hrel⟩
      · exact h2 d hd

theorem varNames_lower : ∀ (l : List (Var × Ty)),
    CC.varNames (l.map fun (x, t) => (CC.identOfString x, type t)) =
      l.map (fun p => CC.identOfString p.1)
  | [] => rfl
  | (x, t) :: l => by
    simp only [CC.varNames, List.map_cons] at *
    rw [← varNames_lower l]; rfl

theorem initLocals_shape : ∀ (l : List (Var × Ty)),
    (initLocals l).map (fun b => (b.1, b.2.1)) = l
  | [] => rfl
  | (x, t) :: l => by
    have ih := initLocals_shape l
    simp only [initLocals] at ih ⊢
    simp only [List.map_cons, ih]

section Entry

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function}
  {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont}

theorem call_step (hs : SCtx P cp) {f : String} {vs : List Val} {cargs : List CC.Val}
    (had : AdmFrom P (.call (.internal f) vs st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfind : P.findFn f = some fn) (hfn : FnOK P fn cf) (hargs : argsRel P st.mem j vs cargs)
    (hk : KR P st.mem j none k K)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.call (.internal f) vs st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.call (.internal f) vs st k)) c'
      (.Callstate (.Internal cf) cargs K cm) t := by
  generalize hb : bindParams st.mem fn.params vs = ob
  rcases ob with _ | penv
  · have hn : Semantics.next P (.call (.internal f) vs st k) = none := by
      simp [Semantics.next, Semantics.nextCore, hfind, hb]
    exact (step_none hn hstep).elim
  have hn : Semantics.next P (.call (.internal f) vs st k) =
      some (.silent (.exec fn.body (penv ++ initLocals fn.locals) st (.function fn.ret k))) := by
    simp [Semantics.next, Semantics.nextCore, hfind, hb]
  obtain ⟨rfl, rfl⟩ := step_silent hn hstep
  have hlow := lowerFunction_inv hfn.low
  have hc := ctxOK_fnContext hlow
  obtain ⟨body, σ, hbody, hcf⟩ := hlow.body
  have hls := lowerStmt_LS _ _ _ _ _ _ hbody
  have hfr : TempsFresh (fnContext P fn) σ := LS_fresh hls (fun p hp => by cases hp)
  have hids : ((fn.params ++ fn.locals).map (fun p => CC.identOfString p.1)).Nodup := by
    have : (fn.params ++ fn.locals).map (fun p => CC.identOfString p.1) =
        ((fn.params ++ fn.locals).map (·.1)).map CC.identOfString := by
      rw [List.map_map]; rfl
    rw [this]
    refine nodup_map_on (fun x hx y hy he => ?_) hlow.nodup
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact identOfString_inj_ascii (hlow.names a ha) (hlow.names b hb) he
  rw [List.map_append, List.nodup_append] at hids
  obtain ⟨hpnd, hlnd, hdisj⟩ := hids
  have hscal : ∀ d ∈ fn.locals, d.2.isStruct = false := fun d hd =>
    ((hs.wf.2.2.2.2.1 fn hfn.mem).2.1 d (List.mem_append_right _ hd)).1
  obtain ⟨le1, hbind, hf1, hp1⟩ := bindTemps (P := P) (m := st.mem) (j := j) fn.params vs cargs
    penv (CC.createUndefTemps ((fn.locals.map fun (x, t) => (CC.identOfString x, type t)) ++
      Priv.LowerState.temps σ)) hb hargs hpnd
  have hnotp : ∀ d ∈ fn.locals, CC.identOfString d.1 ∉ fn.params.map (fun p => CC.identOfString p.1) :=
    fun d hd hm => hdisj _ hm _ (List.mem_map_of_mem hd) rfl
  obtain ⟨le2, hrun, hf2, hl2⟩ := init_run (P := P) (m := st.mem) (j := j) (ge := cp.globalenv)
    (cm := cm) fn.locals le1 hscal hlnd (fun d hd => by
      rw [hf1 _ (hnotp d hd)]
      apply createUndef_get
      rw [List.map_append, List.mem_append]
      left
      obtain ⟨x, t⟩ := d
      exact List.mem_map.mpr ⟨_, List.mem_map_of_mem hd, rfl⟩)
  have hentry : CC.doFunctionEntry2 cp.globalenv cf cargs cm = some (CC.emptyEnv, le1, cm) := by
    subst hcf
    unfold CC.doFunctionEntry2
    refine (ite_eq_left ⟨List.nodup_nil, ?_, ?_⟩).trans ?_
    · simp only [CC.doAllocVariables, hbind]
    · show (CC.varNames _).Nodup
      rw [varNames_lower]; exact hpnd
    · intro x hx hx'
      simp only [CC.varNames, List.map_append, List.mem_append] at hx hx'
      have hx2 : x ∈ fn.params.map (fun p => CC.identOfString p.1) := by
        rw [← varNames_lower]; exact hx
      rcases hx' with hx' | hx'
      · have hx3 : x ∈ fn.locals.map (fun p => CC.identOfString p.1) := by
          rw [← varNames_lower]; exact hx'
        exact hdisj _ hx2 _ hx3 rfl
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'
        obtain ⟨n, hn⟩ := hfr p hp
        obtain ⟨a, ha, he⟩ := List.mem_map.mp hx2
        exact hc.fresh.ne_decl n a (List.mem_append_left _ ha) (hn ▸ he.symm)
  have hstep1 : CC.doStep cp.globalenv (.Callstate (.Internal cf) cargs K cm) =
      some (CC.E0, .State cf cf.fn_body K CC.emptyEnv le1 cm) := by
    simp only [CC.doStep, hentry]
  have henv : EnvRel (fnContext P fn) st.mem j (penv ++ initLocals fn.locals) le2 := by
    refine ⟨?_, fun b hb' => ?_⟩
    · show (penv ++ initLocals fn.locals).map (fun b => (b.1, b.2.1)) = fn.params ++ fn.locals
      rw [List.map_append, (bindParams_shape hb).1, initLocals_shape]
    · rcases List.mem_append.mp hb' with hb' | hb'
      · refine ⟨ValTy.of_hasTy ((bindParams_shape hb).2 b hb'), ?_⟩
        obtain ⟨w, hw, hrel⟩ := hp1 b hb'
        refine ⟨w, ?_, hrel⟩
        rw [hf2]
        · exact hw
        · intro hm
          have : (b.1, b.2.1) ∈ fn.params := by
            rw [← (bindParams_shape hb).1]; exact List.mem_map_of_mem hb'
          exact hdisj _ (List.mem_map_of_mem this) _ hm rfl
      · obtain ⟨⟨x, t⟩, hd, rfl⟩ := List.mem_map.mp hb'
        exact ⟨ValTy.zero (hscal _ hd), hl2 _ hd⟩
  subst hcf
  exact goal_plus (had.silent hn) hg ⟨fn, _, body, K, le2, hfn, .exec ⟨0, _, _, hls⟩ (.fn hk), henv, rfl⟩
    (tplus_of_plus_star (tplus_one hstep1) (hrun.seq_star K))

end Entry

end EmbC.Clight.Proof
