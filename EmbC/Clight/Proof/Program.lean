import EmbC.Clight.Proof.Ident
import EmbC.Clight.Proof.Defs

/-!
# Inverting the program embedding
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem forIn_ok_all {α ε : Type} {l : List α} {g : α → PUnit → Except ε (ForInStep PUnit)}
    (hg : ∀ a x, g a PUnit.unit = .ok x → x = .yield PUnit.unit) {u : PUnit}
    (h : forIn l PUnit.unit g = .ok u) : ∀ a ∈ l, g a PUnit.unit = .ok (.yield PUnit.unit) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.forIn_cons] at h
    cases hga : g a PUnit.unit with
    | error e => simp [hga, bind, Except.bind] at h
    | ok x =>
      have := hg a x hga
      subst this
      simp only [hga, bind, Except.bind] at h
      intro b hb
      cases hb with
      | head => exact hga
      | tail _ hb => exact ih h b hb

/-- ASCII strings. -/
def Ascii (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 128

theorem Ascii.byte {s : String} (h : Ascii s) : ByteString s := fun c hc => by
  have := h c hc; omega

theorem checkName_ok {s : String} {u : Unit} (h : Priv.checkName s = .ok u) : Ascii s := by
  unfold Priv.checkName at h
  simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp at h
  rename_i c cs hv
  intro x hx
  rw [hv] at hx
  split at h
  · simp at h
  rename_i hb
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hb
  cases hx with
  | head => exact hb.1.1
  | tail _ hx => exact (hb.2 x hx).1

theorem checkName_ok' {s : String} {α : Type} {f : Unit → Except String α} {r : α}
    (h : (match Priv.checkName s with
      | .error e => .error e
      | .ok v => f v) = Except.ok r) : Ascii s ∧ ∃ u, f u = .ok r := by
  split at h
  · simp at h
  · rename_i v hv
    exact ⟨checkName_ok hv, v, h⟩

inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a b l r} : R a b → Forall2 R l r → Forall2 R (a :: l) (b :: r)

theorem Forall2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l r}, Forall2 R l r → Forall2 S l r
  | _, _, .nil => .nil
  | _, _, .cons hab hr => .cons (h _ _ hab) (Forall2.imp h hr)

theorem mapM_forall₂ {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → Forall2 (fun a b => f a = .ok b) l r
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    rename_i b hb
    split at h
    · simp at h
    rename_i bs hbs
    simp only [Except.ok.injEq] at h
    subst h
    exact .cons hb (mapM_forall₂ hbs)

def fnContext (P : Prog) (fn : Fn) : Priv.LowerContext :=
  Priv.LowerContext.mk P (fn.params ++ fn.locals) fn.ret
    (String.ofList (List.replicate
      ((fn.params ++ fn.locals).foldl (fun n d => max n d.1.length) 0 + 1) '_'))

def initialization (fn : Fn) : CC.Stmt :=
  fn.locals.foldr (fun (x, t) rest => Priv.sequence (Priv.initializeLocal x t) rest) .Sskip

/-- What a successfully lowered function looks like. -/
structure FnLowered (P : Prog) (fn : Fn) (cf : CC.Function) : Prop where
  names : ∀ d ∈ fn.params ++ fn.locals, Ascii d.1
  nodup : ((fn.params ++ fn.locals).map (·.1)).Nodup
  body : ∃ body σ, Priv.lowerStmt (fnContext P fn) 0 fn.body (Priv.LowerState.mk 0 []) =
      .ok (body, σ) ∧
    cf = { fn_return := (fn.ret.map type).getD .Tvoid, fn_callconv := CC.cc_default,
           fn_params := fn.params.map fun (x, t) => (CC.identOfString x, type t),
           fn_vars := [],
           fn_temps := (fn.locals.map fun (x, t) => (CC.identOfString x, type t)) ++
             Priv.LowerState.temps σ,
           fn_body := Priv.sequence (initialization fn) body }

theorem lowerFunction_inv {P : Prog} {fn : Fn} {cf : CC.Function}
    (h : Priv.lowerFunction P fn = .ok cf) : FnLowered P fn cf := by
  unfold Priv.lowerFunction at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    StateT.run] at h
  split at h
  · simp at h
  rename_i hnd
  split at h
  · simp at h
  rename_i u1 hs
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i r hr
  simp only [Except.ok.injEq] at h
  refine ⟨?_, ?_, ⟨r.1, r.2, hr, h.symm⟩⟩
  · intro d hd
    have := forIn_ok_all (fun a x hx => by
      split at hx
      · simp at hx
      split at hx
      · simp at hx
      simp at hx; exact hx.symm) hs d hd
    split at this
    · simp at this
    · rename_i v hv; exact checkName_ok hv
  · simpa using hnd

/-- What a successfully lowered program looks like. -/
structure ProgLowered (P : Prog) (cp : CC.Program) : Prop where
  fnNames : ∀ fn ∈ P.fns, Ascii fn.name
  constNames : ∀ c ∈ P.consts, Ascii c.name
  composite : (CC.buildCompositeEnv (composites P)).isOK = true
  defs : ∃ fs main, Forall2 (fun fn d => ∃ cf, Priv.lowerFunction P fn = .ok cf ∧
      d = (CC.identOfString fn.name, CC.GlobDef.Gfun (CC.FunDef.Internal cf))) P.fns fs ∧
    cp = CC.mkprogram (composites P) (fs ++ P.consts.map Priv.lowerConstant)
      (P.fns.map fun fn => CC.identOfString fn.name) main

theorem lowerProgram_inv {P : Prog} {cp : CC.Program} (h : lowerProgram P = .ok cp) :
    ProgLowered P cp := by
  unfold lowerProgram at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i u2 hf
  split at h
  · simp at h
  rename_i u3 hc
  split at h
  · simp at h
  rename_i hcomp
  have hfn : ∀ fn ∈ P.fns, Ascii fn.name := by
    intro fn hm
    have := forIn_ok_all (fun a x hx => by
      split at hx
      · simp at hx
      simp at hx; exact hx.symm) hf fn hm
    split at this
    · simp at this
    · rename_i v hv; exact checkName_ok hv
  have hcn : ∀ c ∈ P.consts, Ascii c.name := by
    intro c hm
    have := forIn_ok_all (fun a x hx => by
      split at hx
      · simp at hx
      simp at hx; exact hx.symm) hc c hm
    split at this
    · simp at this
    · rename_i v hv; exact checkName_ok hv
  refine ⟨hfn, hcn, by simpa using hcomp, ?_⟩
  split at h
  · simp at h
  rename_i fn0 tl hfns
  split at h
  · simp at h
  rename_i fs hfs
  simp only [Except.ok.injEq] at h
  refine ⟨fs, _, ?_, h.symm⟩
  refine (mapM_forall₂ hfs).imp ?_
  intro fn d hd
  split at hd
  · simp at hd
  rename_i cf hcf
  exact ⟨cf, hcf, by simp at hd; exact hd.symm⟩


theorem lowerProgram_fieldNames {P : Prog} {cp : CC.Program} (h : lowerProgram P = .ok cp) :
    ∀ d ∈ P.structs, ∀ x ∈ d.fields, Ascii x.1 := by
  unfold lowerProgram at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i u1 hs
  intro d hd x hx
  have := forIn_ok_all (fun a x hx => by
      split at hx
      · simp at hx
      split at hx
      · simp at hx
      split at hx
      · simp at hx
      simp at hx; exact hx.symm) hs d hd
  split at this
  · simp at this
  split at this
  · simp at this
  split at this
  · simp at this
  rename_i u2 hf
  have := forIn_ok_all (fun a x hx => by
      split at hx
      · simp at hx
      split at hx
      · simp at hx
      simp at hx; exact hx.symm) hf x hx
  split at this
  · simp at this
  · rename_i v hv; exact checkName_ok hv

/-! ## Global environment lookups -/

theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_on (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])) hnd.2⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have := hinj b (by simp [hb]) a (by simp) hfb
    subst this
    exact hnd.1 hb

section Genv

variable {F V : Type}

theorem addGlobals_symb_notin (id : CC.Ident) :
    ∀ (gl : List (CC.Ident × CC.GlobDef F V)) (ge : CC.Genv F V), id ∉ gl.map Prod.fst →
      CC.Genv.findSymbol (CC.Genv.addGlobals ge gl) id = CC.Genv.findSymbol ge id
  | [], _, _ => rfl
  | g :: gl, ge, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show CC.Genv.findSymbol (CC.Genv.addGlobals (CC.Genv.addGlobal ge g) gl) id = _
    rw [addGlobals_symb_notin id gl _ h.2]
    simp only [CC.Genv.findSymbol, CC.Genv.addGlobal]
    exact CC.PTree.gso _ _ _ _ (Ne.symm h.1)

theorem addGlobals_defs_below (b : CC.Block) :
    ∀ (gl : List (CC.Ident × CC.GlobDef F V)) (ge : CC.Genv F V), b.toNat < ge.genv_next.toNat →
      CC.Genv.findDef (CC.Genv.addGlobals ge gl) b = CC.Genv.findDef ge b
  | [], _, _ => rfl
  | g :: gl, ge, h => by
    show CC.Genv.findDef (CC.Genv.addGlobals (CC.Genv.addGlobal ge g) gl) b = _
    rw [addGlobals_defs_below b gl _ (by simp [CC.Genv.addGlobal]; omega)]
    simp only [CC.Genv.findDef, CC.Genv.addGlobal]
    exact CC.PTree.gso _ _ _ _ (fun he => by subst he; omega)

theorem addGlobals_find (id : CC.Ident) (g : CC.GlobDef F V) :
    ∀ (gl : List (CC.Ident × CC.GlobDef F V)) (ge : CC.Genv F V), (gl.map Prod.fst).Nodup →
      (id, g) ∈ gl → ∃ b, CC.Genv.findSymbol (CC.Genv.addGlobals ge gl) id = some b ∧
        CC.Genv.findDef (CC.Genv.addGlobals ge gl) b = some g
  | [], _, _, h => by cases h
  | g' :: gl, ge, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show ∃ b, CC.Genv.findSymbol (CC.Genv.addGlobals (CC.Genv.addGlobal ge g') gl) id = some b ∧
      CC.Genv.findDef (CC.Genv.addGlobals (CC.Genv.addGlobal ge g') gl) b = some g
    cases hm with
    | head =>
      refine ⟨ge.genv_next, ?_, ?_⟩
      · rw [addGlobals_symb_notin id gl _ hnd.1]
        simp [CC.Genv.findSymbol, CC.Genv.addGlobal]
      · rw [addGlobals_defs_below _ gl _ (by simp [CC.Genv.addGlobal])]
        simp [CC.Genv.findDef, CC.Genv.addGlobal]
    | tail _ hm => exact addGlobals_find id g gl _ hnd.2 hm

end Genv

theorem forall2_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, Forall2 R l r → ∀ a ∈ l, ∃ b ∈ r, R a b
  | _, _, .nil, a, h => by cases h
  | _, _, .cons hab hr, a, h => by
    cases h with
    | head => exact ⟨_, List.mem_cons_self, hab⟩
    | tail _ h =>
      obtain ⟨b, hb, h⟩ := forall2_mem hr a h
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem forall2_map {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {r : List β}, Forall2 R l r → l.map f = r.map g
  | _, _, .nil => rfl
  | _, _, .cons hab hr => by simp [hfg _ _ hab, forall2_map hfg hr]

theorem findFn_mem {P : Prog} {f : String} {fn : Fn} (h : P.findFn f = some fn) :
    fn ∈ P.fns ∧ fn.name = f := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem identOfString_inj_ascii {s t : String} (hs : Ascii s) (ht : Ascii t)
    (h : CC.identOfString s = CC.identOfString t) : s = t :=
  identOfString_inj hs.byte ht.byte h

/-- Every source function is found in the target global environment. -/
theorem genv_find_fn {P : Prog} {cp : CC.Program} (hwf : wellFormed P) (hl : ProgLowered P cp)
    {fn : Fn} (hfn : fn ∈ P.fns) :
    ∃ b cf, CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString fn.name) = some b ∧
      CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
      Priv.lowerFunction P fn = .ok cf := by
  obtain ⟨fs, main, hfs, rfl⟩ := hl.defs
  obtain ⟨d, hd, cf, hcf, rfl⟩ := forall2_mem hfs fn hfn
  have hnd : ((fs ++ P.consts.map Priv.lowerConstant).map Prod.fst).Nodup := by
    have heq : (fs ++ P.consts.map Priv.lowerConstant).map Prod.fst =
        (P.fns.map (·.name) ++ P.consts.map (·.name)).map CC.identOfString := by
      rw [List.map_append, ← forall2_map (f := fun fn => CC.identOfString fn.name)
        (fun a b ⟨cf, _, hb⟩ => by rw [hb]) hfs]
      simp [List.map_map, Function.comp_def, Priv.lowerConstant]
    rw [heq]
    · refine nodup_map_on ?_ hwf.2.1
      intro x hx y hy hxy
      have hall : ∀ z ∈ P.fns.map (·.name) ++ P.consts.map (·.name), Ascii z := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hz; exact hl.fnNames fn hfn
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz; exact hl.constNames c hc
      exact identOfString_inj_ascii (hall x hx) (hall y hy) hxy
  obtain ⟨b, hb, hdef⟩ := addGlobals_find _ _ _ _ hnd (List.mem_append_left _ hd)
  exact ⟨b, cf, hb, by simp [CC.Genv.findFunctPtr, CC.Program.globalenv, CC.mkprogram] at hdef ⊢; rw [hdef], hcf⟩

theorem programRel_of {P : Prog} {cp : CC.Program} (hwf : wellFormed P)
    (h : P.toClight = .ok cp) : ProgramRel P cp := by
  have hl := lowerProgram_inv h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨fs, main, _, rfl⟩ := hl.defs; rfl
  · obtain ⟨fs, main, _, rfl⟩ := hl.defs
    simp only [CC.mkprogram, compositeEnv]
    cases CC.buildCompositeEnv (composites P) <;> rfl
  · have hc := hl.composite
    obtain ⟨fs, main, _, rfl⟩ := hl.defs
    exact hc
  · intro fn hfn
    obtain ⟨b, cf, hb, hf, hcf⟩ := genv_find_fn hwf hl hfn
    refine ⟨b, cf, hb, hf, ?_⟩
    obtain ⟨_, _, ⟨body, σ, _, rfl⟩⟩ := lowerFunction_inv hcf
    simp [CC.typeOfFunction, CC.typeOfParams]

end EmbC.Clight.Proof
