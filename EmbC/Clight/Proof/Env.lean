import EmbC.Clight.Proof.Fresh
import EmbC.Clight.Proof.MemRel

/-!
# Source frames versus Clight temporaries
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-- Static facts about a lowering context. -/
structure CtxOK (ctx : LCtx) : Prop where
  fresh : FreshOK ctx
  ascii : ∀ d ∈ ctx.vars, Ascii d.1
  nodup : (ctx.vars.map (·.1)).Nodup

theorem ctxOK_fnContext {P : Prog} {fn : Fn} {cf : CC.Function} (h : FnLowered P fn cf) :
    CtxOK (fnContext P fn) :=
  ⟨freshOK_fnContext h.names, h.names, h.nodup⟩

def EnvShape (vars : List (Var × Ty)) (env : Env) : Prop :=
  env.map (fun b => (b.1, b.2.1)) = vars

def EnvRel (ctx : LCtx) (m : Mem) (j : MemoryInjection) (env : Env) (le : CC.TempEnv) : Prop :=
  EnvShape ctx.vars env ∧ ∀ b ∈ env, ValTy m b.2.2 b.2.1 ∧
    ∃ w, le.get (CC.identOfString b.1) = some w ∧ valRel ctx.prog m j b.2.2 w

def InRange (ctx : LCtx) (lo hi : Nat) (id : CC.Ident) : Prop :=
  ∃ n, lo ≤ n ∧ n < hi ∧ id = freshId ctx n

def IsDecl (ctx : LCtx) (id : CC.Ident) : Prop :=
  ∃ d ∈ ctx.vars, id = CC.identOfString d.1

/-- `le'` differs from `le` only at fresh temporaries numbered in `[lo, hi)`. -/
def Frame (ctx : LCtx) (lo hi : Nat) (le le' : CC.TempEnv) : Prop :=
  ∀ id, ¬ InRange ctx lo hi id → le'.get id = le.get id

/-- `le'` agrees with `le` on declared variables and on fresh temporaries in `[lo, hi)`. -/
def Agree (ctx : LCtx) (lo hi : Nat) (le le' : CC.TempEnv) : Prop :=
  ∀ id, IsDecl ctx id ∨ InRange ctx lo hi id → le'.get id = le.get id

section Frames

variable {ctx : LCtx}

theorem Frame.refl (lo hi : Nat) (le : CC.TempEnv) : Frame ctx lo hi le le := fun _ _ => rfl

theorem Frame.mono {lo hi lo' hi' : Nat} {le le' : CC.TempEnv} (h : Frame ctx lo hi le le')
    (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : Frame ctx lo' hi' le le' := by
  intro id hid
  apply h
  rintro ⟨n, hn1, hn2, rfl⟩
  exact hid ⟨n, by omega, by omega, rfl⟩

theorem Frame.trans {a b c : Nat} {le₁ le₂ le₃ : CC.TempEnv} (h₁ : Frame ctx a b le₁ le₂)
    (h₂ : Frame ctx b c le₂ le₃) (hab : a ≤ b) (hbc : b ≤ c) : Frame ctx a c le₁ le₃ := by
  intro id hid
  rw [h₂ id (fun ⟨n, h1, h2, h3⟩ => hid ⟨n, by omega, h2, h3⟩),
    h₁ id (fun ⟨n, h1, h2, h3⟩ => hid ⟨n, h1, by omega, h3⟩)]

theorem Frame.set_fresh (n : Nat) (le : CC.TempEnv) (v : CC.Val) :
    Frame ctx n (n + 1) le (le.set (freshId ctx n) v) := by
  intro id hid
  apply CC.PTree.gso
  rintro rfl
  exact hid ⟨n, Nat.le_refl _, by omega, rfl⟩

theorem Agree.refl (lo hi : Nat) (le : CC.TempEnv) : Agree ctx lo hi le le := fun _ _ => rfl

theorem Agree.mono {lo hi lo' hi' : Nat} {le le' : CC.TempEnv} (h : Agree ctx lo hi le le')
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : Agree ctx lo' hi' le le' := by
  intro id hid
  apply h
  rcases hid with hid | ⟨n, hn1, hn2, rfl⟩
  · exact .inl hid
  · exact .inr ⟨n, by omega, by omega, rfl⟩

theorem Agree.trans {lo hi : Nat} {le₁ le₂ le₃ : CC.TempEnv} (h₁ : Agree ctx lo hi le₁ le₂)
    (h₂ : Agree ctx lo hi le₂ le₃) : Agree ctx lo hi le₁ le₃ := fun id hid =>
  (h₂ id hid).trans (h₁ id hid)

theorem not_inRange_decl (hc : CtxOK ctx) {lo hi : Nat} {id : CC.Ident} (h : IsDecl ctx id) :
    ¬ InRange ctx lo hi id := by
  rintro ⟨n, _, _, rfl⟩
  obtain ⟨d, hd, he⟩ := h
  exact hc.fresh.ne_decl n d hd he

theorem not_inRange_disjoint (hc : CtxOK ctx) {a b c d : Nat} {id : CC.Ident}
    (h : InRange ctx a b id) (hbc : b ≤ c) : ¬ InRange ctx c d id := by
  rintro ⟨n, h1, _, rfl⟩
  obtain ⟨n', _, h2, he⟩ := h
  have := hc.fresh.inj _ _ he
  omega

/-- A frame change at later temporaries preserves agreement on earlier ones. -/
theorem Agree.of_frame (hc : CtxOK ctx) {a b c d : Nat} {le₁ le₂ le₃ : CC.TempEnv}
    (hA : Agree ctx a b le₂ le₃) (hF : Frame ctx c d le₁ le₂) (hbc : b ≤ c) :
    Agree ctx a b le₁ le₃ := by
  intro id hid
  rw [hA id hid]
  apply hF
  rcases hid with hid | hid
  · exact not_inRange_decl hc hid
  · exact not_inRange_disjoint hc hid hbc

/-- Agreement with a frame-changed environment, on the earlier range. -/
theorem Agree.frame_left (hc : CtxOK ctx) {a b c d : Nat} {le₁ le₂ : CC.TempEnv}
    (hF : Frame ctx c d le₁ le₂) (hbc : b ≤ c) : Agree ctx a b le₁ le₂ := by
  intro id hid
  apply hF
  rcases hid with hid | hid
  · exact not_inRange_decl hc hid
  · exact not_inRange_disjoint hc hid hbc

end Frames

/-! ## Source frames -/

theorem envShape_names {vars : List (Var × Ty)} {env : Env} (h : EnvShape vars env) :
    env.map (·.1) = vars.map (·.1) := by
  rw [← h, List.map_map]; rfl

theorem env_get_mem : ∀ {vars : List (Var × Ty)} {env : Env} {x : Var} {v : Val},
    EnvShape vars env → Env.get env x = some v →
    ∃ t, (vars.find? (·.1 == x)).map (·.2) = some t ∧ (x, t, v) ∈ env
  | _, [], _, _, _, h => by cases h
  | vars, (y, t, w) :: rest, x, v, hs, h => by
    subst hs
    simp only [Env.get] at h
    by_cases hy : y = x
    · subst hy
      simp only [ite_true, Option.some.injEq] at h
      subst h
      exact ⟨t, by simp, by simp⟩
    · simp only [hy, ite_false] at h
      obtain ⟨t', h1, h2⟩ := env_get_mem rfl h
      refine ⟨t', ?_, List.mem_cons_of_mem _ h2⟩
      simpa [hy] using h1

theorem env_ty_eq : ∀ {vars : List (Var × Ty)} {env : Env} {x : Var},
    EnvShape vars env → Env.ty env x = (vars.find? (·.1 == x)).map (·.2)
  | _, [], _, h => by subst h; rfl
  | vars, (y, t, w) :: rest, x, hs => by
    subst hs
    simp only [Env.ty]
    by_cases hy : y = x
    · subst hy; simp
    · simp only [hy, ite_false]
      rw [env_ty_eq rfl]
      simp [hy]

theorem env_set_shape : ∀ (env : Env) (x : Var) (v : Val),
    (env.set x v).map (fun b => (b.1, b.2.1)) = env.map (fun b => (b.1, b.2.1))
  | [], _, _ => rfl
  | (y, t, w) :: rest, x, v => by
    simp only [Env.set]
    split
    · rfl
    · simp [env_set_shape rest x v]

theorem env_set_mem : ∀ {env : Env} {x : Var} {v : Val} {b : Var × Ty × Val},
    (env.map (·.1)).Nodup → b ∈ env.set x v →
    (b.1 = x ∧ b.2.2 = v ∧ Env.ty env x = some b.2.1) ∨ (b.1 ≠ x ∧ b ∈ env)
  | [], _, _, _, _, h => by cases h
  | (y, t, w) :: rest, x, v, b, hnd, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Env.set] at h
    by_cases hy : y = x
    · subst hy
      simp only [ite_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl ⟨rfl, rfl, by simp [Env.ty]⟩
      · right
        refine ⟨fun he => hnd.1 ?_, List.mem_cons_of_mem _ h⟩
        rw [← he]; exact List.mem_map_of_mem h
    · simp only [hy, ite_false, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr ⟨hy, by simp⟩
      · rcases env_set_mem hnd.2 h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact .inl ⟨h1, h2, by simp [Env.ty, hy, h3]⟩
        · exact .inr ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem env_assign_inv {env env' : Env} {m : Mem} {x : Var} {v : Val}
    (h : env.assign m x v = some env') :
    ∃ t, Env.ty env x = some t ∧ m.hasTy v t = true ∧ env' = env.set x v := by
  unfold Env.assign at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h; exact ⟨t, ht, by assumption, rfl⟩
    · cases h

section EnvRel

variable {ctx : LCtx} {m : Mem} {j : MemoryInjection} {env : Env} {le : CC.TempEnv}

theorem EnvRel.mem_decl (h : EnvRel ctx m j env le) {b : Var × Ty × Val} (hb : b ∈ env) :
    (b.1, b.2.1) ∈ ctx.vars := by
  rw [← h.1]; exact List.mem_map_of_mem hb

theorem EnvRel.frame {lo hi : Nat} {le' : CC.TempEnv} (hc : CtxOK ctx) (h : EnvRel ctx m j env le)
    (hF : Frame ctx lo hi le le') : EnvRel ctx m j env le' := by
  refine ⟨h.1, fun b hb => ?_⟩
  obtain ⟨h1, w, h2, h3⟩ := h.2 b hb
  refine ⟨h1, w, ?_, h3⟩
  rw [hF _ (not_inRange_decl hc ⟨_, h.mem_decl hb, rfl⟩)]; exact h2

theorem EnvRel.agree {lo hi : Nat} {le' : CC.TempEnv} (h : EnvRel ctx m j env le)
    (hA : Agree ctx lo hi le le') : EnvRel ctx m j env le' := by
  refine ⟨h.1, fun b hb => ?_⟩
  obtain ⟨h1, w, h2, h3⟩ := h.2 b hb
  refine ⟨h1, w, ?_, h3⟩
  rw [hA _ (.inl ⟨_, h.mem_decl hb, rfl⟩)]; exact h2

theorem EnvRel.mono {m' : Mem} {j' : MemoryInjection} (h : EnvRel ctx m j env le)
    (hg : MemGrow m m') (hj : j.Extends j' m) : EnvRel ctx m' j' env le := by
  refine ⟨h.1, fun b hb => ?_⟩
  obtain ⟨h1, w, h2, h3⟩ := h.2 b hb
  exact ⟨h1.mono hg, w, h2, valRel_mono hg hj h3⟩

theorem EnvRel.get {x : Var} {v : Val} {t : Ty} (h : EnvRel ctx m j env le)
    (hx : Env.get env x = some v) (ht : lookupVar ctx x = some t) :
    ValTy m v t ∧ ∃ w, le.get (CC.identOfString x) = some w ∧ valRel ctx.prog m j v w := by
  obtain ⟨t', h1, h2⟩ := env_get_mem h.1 hx
  have : t' = t := by
    unfold lookupVar at ht; rw [h1] at ht; cases ht; rfl
  subst this
  exact h.2 _ h2

theorem EnvRel.set (hc : CtxOK ctx) (h : EnvRel ctx m j env le) {x : Var} {t : Ty} {v : Val}
    {w : CC.Val} (ht : Env.ty env x = some t) (hv : ValTy m v t)
    (hw : valRel ctx.prog m j v w) :
    EnvRel ctx m j (env.set x v) (le.set (CC.identOfString x) w) := by
  have hnd : (env.map (·.1)).Nodup := by rw [envShape_names h.1]; exact hc.nodup
  have hx : (x, t) ∈ ctx.vars := by
    rw [env_ty_eq h.1] at ht
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ht
    have := List.find?_some hd
    have hdx : d.1 = x := by simpa using this
    rw [← hdx]; exact List.mem_of_find?_eq_some hd
  refine ⟨?_, fun b hb => ?_⟩
  · unfold EnvShape; rw [env_set_shape]; exact h.1
  rcases env_set_mem hnd hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · rw [ht] at h3; cases h3
    rw [h1, h2]
    exact ⟨hv, w, CC.PTree.gss _ _ _, hw⟩
  · obtain ⟨h3, w', h4, h5⟩ := h.2 b h2
    refine ⟨h3, w', ?_, h5⟩
    rw [CC.PTree.gso]
    · exact h4
    · intro he
      exact h1 (identOfString_inj_ascii (hc.ascii _ hx) (hc.ascii _ (h.mem_decl h2)) he).symm
end EnvRel

end EmbC.Clight.Proof
