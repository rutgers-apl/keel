import EmbC.Clight.Proof.Lower

/-! # Inversion of statement lowering -/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem lowerArgs_LA (ctx : LCtx) : ∀ (es : List EmbC.Expr) (σ : LSt) (pre : CC.Stmt)
    (rs : List LX) (σ' : LSt), Priv.lowerArgs ctx es σ = .ok ((pre, rs), σ') →
    LA ctx σ es pre rs σ'
  | [], σ, pre, rs, σ', h => by
    simp only [Priv.lowerArgs] at h
    obtain ⟨h1, rfl⟩ := pure_ok h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact .nil
  | e :: es, σ, pre, rs, σ', h => by
    simp only [Priv.lowerArgs] at h
    lsimp at h
    obtain ⟨_, _, ⟨r, σ1, he, rfl, rfl⟩, ⟨pre', rs'⟩, σ2, ha, ⟨rfl, rfl⟩, rfl⟩ := h
    exact LA.cons (lowerExpr_LE ctx _ _ _ _ he) (lowerArgs_LA ctx es _ _ _ _ ha)

theorem checkArgs_ok : ∀ (ts : List Ty) (as : List LX) (σ σ' : LSt) (u : Unit),
    Priv.checkArgs ts as σ = .ok (u, σ') → ArgsOK ts as ∧ σ' = σ
  | [], [], σ, σ', u, h => by
    simp only [Priv.checkArgs] at h; exact ⟨.nil, (pure_ok h).2⟩
  | t :: ts, a :: as, σ, σ', u, h => by
    simp only [Priv.checkArgs] at h
    obtain ⟨_, σ1, h1, h2⟩ := bind_ok h
    obtain ⟨hacc, rfl⟩ := requireType_ok h1
    obtain ⟨hr, rfl⟩ := checkArgs_ok ts as _ _ _ h2
    exact ⟨.cons hacc hr, rfl⟩
  | [], _ :: _, σ, σ', u, h => by simp only [Priv.checkArgs] at h; exact (throw_ok h).elim
  | _ :: _, [], σ, σ', u, h => by simp only [Priv.checkArgs] at h; exact (throw_ok h).elim

theorem lowerDestination_ok {ctx : LCtx} {dst : Option Var} {ret : Option Ty}
    {dst' : Option CC.Ident} {σ σ' : LSt}
    (h : Priv.lowerDestination ctx dst ret σ = .ok (dst', σ')) : DstOK ctx dst ret dst' ∧ σ' = σ := by
  unfold Priv.lowerDestination at h
  rcases dst with _ | x
  · obtain ⟨rfl, rfl⟩ := pure_ok h; exact ⟨.inl ⟨rfl, rfl⟩, rfl⟩
  · obtain ⟨t, σ1, h1, h2⟩ := bind_ok h
    obtain ⟨ht, rfl⟩ := lookupVariable_ok h1
    lsimp at h2
    obtain ⟨hne, rfl, rfl⟩ := h2
    refine ⟨.inr ⟨x, t, rfl, ht, ?_, rfl⟩, rfl⟩
    simpa using hne


theorem liftM_ok {α : Type} {x : Except String α} {σ σ' : LSt} {a : α}
    (h : (liftM x : Priv.LowerM α) σ = .ok (a, σ')) : x = .ok a ∧ σ' = σ := by
  cases x with
  | error e =>
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, Except.bind] at h
  | ok v =>
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, Except.bind, pure,
      Except.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem checkScalar_ok {P : Prog} {t : Ty} {u : Unit} (h : Priv.checkScalar P t = .ok u) :
    t.isStruct = false := by
  unfold Priv.checkScalar at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · cases hs : t.isStruct
    · rfl
    · simp [hs, throw, throwThe, MonadExceptOf.throw] at h

theorem kernelTypes_ok {ctx : LCtx} {ext : Ext} {args : List LX} {types : List CC.Ty}
    {ret : Option Ty} {σ σ' : LSt}
    (h : Priv.kernelTypes ctx ext args σ = .ok ((types, ret), σ')) :
    KT ctx.prog ext args types ret ∧ σ' = σ := by
  cases ext with
  | kvcalloc t =>
    simp only [Priv.kernelTypes] at h
    lsimp at h
    obtain ⟨_, _, h1, _, _, h2, ⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hS, rfl⟩ := liftM_ok h1
    obtain ⟨hA, rfl⟩ := checkArgs_ok _ _ _ _ _ h2
    cases hA with
    | cons ha h0 => cases h0; exact ⟨.kvcalloc (checkScalar_ok hS) ha, rfl⟩
  | kzalloc s =>
    simp only [Priv.kernelTypes] at h
    lsimp at h
    obtain ⟨_, _, h1, _, _, h2, ⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hS, rfl⟩ := liftM_ok h1
    obtain ⟨hA, rfl⟩ := checkArgs_ok _ _ _ _ _ h2
    cases hA; exact ⟨.kzalloc, rfl⟩
  | kvrealloc t =>
    simp only [Priv.kernelTypes] at h
    lsimp at h
    obtain ⟨_, _, h1, _, _, h2, ⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hS, rfl⟩ := liftM_ok h1
    obtain ⟨hA, rfl⟩ := checkArgs_ok _ _ _ _ _ h2
    cases hA with
    | cons ha h0 =>
      cases h0 with
      | cons hb h00 => cases h00; exact ⟨.kvrealloc (checkScalar_ok hS) ha hb, rfl⟩
  | kvfree =>
    simp only [Priv.kernelTypes] at h
    rcases args with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · lsimp at h
    · lsimp at h
      obtain ⟨hp, ⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨.kvfree (by simpa [LX.ty] using hp), rfl⟩
    · lsimp at h
  | copyFromBpfptr =>
    simp only [Priv.kernelTypes] at h
    lsimp at h
    obtain ⟨_, _, h2, ⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hA, rfl⟩ := checkArgs_ok _ _ _ _ _ h2
    cases hA with
    | cons ha h0 =>
      cases h0 with
      | cons hb h00 =>
        cases h00 with
        | cons hc h000 => cases h000; exact ⟨.copyFromBpfptr ha hb hc, rfl⟩
  | signalPending =>
    simp only [Priv.kernelTypes] at h
    lsimp at h
    obtain ⟨_, _, h2, ⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hA, rfl⟩ := checkArgs_ok _ _ _ _ _ h2
    cases hA; exact ⟨.signalPending, rfl⟩
  | condResched =>
    simp only [Priv.kernelTypes] at h
    lsimp at h
    obtain ⟨_, _, h2, ⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hA, rfl⟩ := checkArgs_ok _ _ _ _ _ h2
    cases hA; exact ⟨.condResched, rfl⟩


theorem lowerStmt_LS (ctx : LCtx) : ∀ (s : Stmt) (d : Nat) (σ : LSt) (cs : CC.Stmt) (σ' : LSt),
    Priv.lowerStmt ctx d s σ = .ok (cs, σ') → LS ctx d σ s cs σ' := by
  intro s
  induction s with
  | skip => intro d σ cs σ' h; obtain ⟨rfl, rfl⟩ := pure_ok h; exact .skip
  | assign x e =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨t, _, hx, re, σe, he, _, _, hr, rfl, rfl⟩ := h
    obtain ⟨hx', rfl⟩ := lookupVariable_ok hx
    obtain ⟨hr', rfl⟩ := requireType_ok hr
    exact .assign hx' (lowerExpr_LE ctx _ _ _ _ he) hr'
  | store p i e =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨_, _, ⟨rp, σp, hp, rfl, rfl⟩, t, _, hae, _, _, ⟨ri, σi, hi, rfl, rfl⟩, _, _, hreq,
      re, σe, he, _, _, hrt, rfl, rfl⟩ := h
    obtain ⟨hpt, hns, rfl⟩ := arrayElement_ok hae
    obtain ⟨hint, rfl⟩ := requireInteger_ok hreq
    obtain ⟨hrt', rfl⟩ := requireType_ok hrt
    exact .store (lowerExpr_LE ctx _ _ _ _ hp) hpt hns (lowerExpr_LE ctx _ _ _ _ hi) hint
      (lowerExpr_LE ctx _ _ _ _ he) hrt'
  | setField p f e =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨_, _, ⟨rp, σp, hp, rfl, rfl⟩, t, _, hft, re, σe, he, _, _, hrt, rfl, rfl⟩ := h
    obtain ⟨⟨s, hs⟩, hf, rfl⟩ := fieldType_ok hft
    obtain ⟨hrt', rfl⟩ := requireType_ok hrt
    have := LS.setField (d := d) (lowerExpr_LE ctx _ _ _ _ hp) hs hf (lowerExpr_LE ctx _ _ _ _ he) hrt'
    have hs' : Priv.LowerExpr.sourceType (capExpr ctx σp rp) = some (.ptr (.struct s)) := hs
    simp only [Priv.fieldExpr, hs']
    exact this
  | seq a b iha ihb =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨a', σ1, ha, b', σ2, hb, rfl, rfl⟩ := h
    exact .seq (iha _ _ _ _ ha) (ihb _ _ _ _ hb)
  | ite c a b iha ihb =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨rc, σc, hc, _, _, hrt, a', σa, ha, b', σb, hb, rfl, rfl⟩ := h
    obtain ⟨hrt', rfl⟩ := requireType_ok hrt
    exact .ite (lowerExpr_LE ctx _ _ _ _ hc) hrt' (iha _ _ _ _ ha) (ihb _ _ _ _ hb)
  | «while» c body ih =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨rc, σc, hc, _, _, hrt, b', σb, hb, rfl, rfl⟩ := h
    obtain ⟨hrt', rfl⟩ := requireType_ok hrt
    exact .while (lowerExpr_LE ctx _ _ _ _ hc) hrt' (ih _ _ _ _ hb)
  | call dst f args =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    generalize hfn : (Priv.LowerContext.program ctx).findFn f = ofn at h
    rcases ofn with _ | fn
    · lsimp at h
    lsimp at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, ⟨pre, rs⟩, σa, ha, _, _, hc, dst', σd, hd, rfl, rfl⟩ := h
    obtain ⟨hc', rfl⟩ := checkArgs_ok _ _ _ _ _ hc
    obtain ⟨hd', rfl⟩ := lowerDestination_ok hd
    exact .call hfn (lowerArgs_LA ctx _ _ _ _ _ ha) hc' hd'
  | ecall dst ext args =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨⟨pre, rs⟩, σa, ha, ⟨types, ret⟩, σk, hk, dst', σd, hd, rfl, rfl⟩ := h
    obtain ⟨hk', rfl⟩ := kernelTypes_ok hk
    obtain ⟨hd', rfl⟩ := lowerDestination_ok hd
    exact .ecall (lowerArgs_LA ctx _ _ _ _ _ ha) hk' hd'
  | ret e =>
    intro d σ cs σ' h
    rcases e with _ | e
    · simp only [Priv.lowerStmt] at h
      lsimp at h
      obtain ⟨hr, rfl, rfl⟩ := h
      exact .ret0 (by simpa [LCtx.res] using hr)
    · unfold Priv.lowerStmt at h
      generalize hres : Priv.LowerContext.result ctx = ores at h
      rcases ores with _ | t
      · lsimp at h
      lsimp at h
      obtain ⟨_, _, ⟨rfl, rfl⟩, r, σr, he, _, _, hrt, rfl, rfl⟩ := h
      obtain ⟨hrt', rfl⟩ := requireType_ok hrt
      exact .ret1 hres (lowerExpr_LE ctx _ _ _ _ he) hrt'
  | brk =>
    intro d σ cs σ' h
    simp only [Priv.lowerStmt] at h
    lsimp at h
    obtain ⟨hd, rfl, rfl⟩ := h
    exact .brk (by simpa using hd)

end EmbC.Clight.Proof
