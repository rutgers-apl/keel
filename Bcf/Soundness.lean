import Bcf.Check

/-!
# Soundness of the BCF checker

`check_sound`: if the checker accepts a proof, the assumed goal is
unsatisfiable in the proof's own expression pool.

The invariant `Inv` is carried through replay: the type memo is
correct, the built-in `true`/`false` nodes are in place, every fact is
a node of the pool, and every fact is entailed by the goal.  Each rule
preserves it; the final fact is `false`, which holds in no state.
-/

namespace Bcf

theorem subsetB_eq (l m : List Nat) : subsetB l m = l.all (fun a => decide (a ∈ m)) := by
  simp only [subsetB, Std.HashSet.contains_ofList]
  congr 1
  funext a
  exact Bool.eq_iff_iff.mpr (by simp)


theorem mapOpt_length {f : α → Option β} {l : List α} {l' : List β}
    (h : mapOpt f l = some l') : l'.length = l.length := by
  induction l generalizing l' with
  | nil => simp [mapOpt] at h; subst h; rfl
  | cons a rest ih =>
    simp only [mapOpt] at h
    split at h
    · rename_i b bs _ hrest
      simp at h; subst h
      simp [ih hrest]
    · simp at h

/-! ## Semantic facts about nodes of a well-formed pool -/

theorem eqv_self_of_scalar {v : Val} {t : Ty} (ht : v.ty = some t) (hs : t.isScalar = true) :
    Val.eqv v v = .bool true := by
  cases v with
  | bv w x => simp [Val.eqv]
  | bool b => simp [Val.eqv]
  | list e vs => simp at ht; subst ht; simp [Ty.isScalar] at hs
  | bad => simp at ht

theorem eqv_true_iff {x y : Val} :
    Val.eqv x y = .bool true ↔ x = y ∧ ∃ t, x.ty = some t ∧ t.isScalar = true := by
  cases x with
  | bv n a =>
    cases y with
    | bv m b =>
      by_cases h : m = n
      · subst h; simp [Val.eqv, Ty.isScalar]
      · have h' : ¬n = m := fun e => h e.symm
        simp [Val.eqv, h, h']
    | bool _ => simp [Val.eqv]
    | list _ _ => simp [Val.eqv]
    | bad => simp [Val.eqv]
  | bool a => cases y <;> simp [Val.eqv, Ty.isScalar]
  | list e vs => cases y <;> simp [Val.eqv, Ty.isScalar]
  | bad => cases y <;> simp [Val.eqv]

theorem eqv_symm {x y : Val} {r : Bool} (h : Val.eqv x y = .bool r) : Val.eqv y x = .bool r := by
  cases x with
  | bv n a =>
    cases y with
    | bv m b =>
      by_cases hw : m = n
      · subst hw; simp [Val.eqv] at h ⊢; rw [← h]; simp [eq_comm]
      · simp [Val.eqv, hw] at h
    | bool _ => simp [Val.eqv] at h
    | list _ _ => simp [Val.eqv] at h
    | bad => simp [Val.eqv] at h
  | bool a => cases y <;> simp [Val.eqv] at h ⊢; rw [← h]; simp [eq_comm]
  | list _ _ => cases y <;> simp [Val.eqv] at h
  | bad => cases y <;> simp [Val.eqv] at h

/-- A node `eq a b` holds iff the two sides evaluate equally to a scalar. -/
theorem holds_eq_node {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.eq, #[a, b]⟩) (ρ : Assign) :
    holds pool ρ e ↔ eval pool ρ a = eval pool ρ b ∧
      ∃ t, (eval pool ρ a).ty = some t ∧ t.isScalar = true := by
  unfold holds
  rw [eval_node hwf ρ he]
  simp only [Op.eval, List.map, eqEval]
  constructor
  · intro h
    cases hq : Val.eqv (eval pool ρ a) (eval pool ρ b) with
    | bool r => rw [hq] at h; simp at h; subst h; exact eqv_true_iff.mp hq
    | bv _ _ => rw [hq] at h; simp at h
    | list _ _ => rw [hq] at h; simp at h
    | bad => rw [hq] at h; simp at h
  · intro h
    rw [eqv_true_iff.mpr h]; rfl

/-- The value of a node `eq a b` is the comparison of its sides. -/
theorem eval_eq_node {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.eq, #[a, b]⟩) (ρ : Assign) {r : Bool}
    (h : eval pool ρ e = .bool r) : Val.eqv (eval pool ρ a) (eval pool ρ b) = .bool r := by
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, List.map, eqEval] at h
  cases hq : Val.eqv (eval pool ρ a) (eval pool ρ b) with
  | bool r' => rw [hq] at h; simp at h; rw [h]
  | bv _ _ => rw [hq] at h; simp at h
  | list _ _ => rw [hq] at h; simp at h
  | bad => rw [hq] at h; simp at h

/-- A node `not a` holds iff `a` is false. -/
theorem holds_not_node {pool : Pool} (hwf : WF pool) {e a : Nat}
    (he : pool[e]? = some ⟨.boolNot, #[a]⟩) (ρ : Assign) :
    holds pool ρ e ↔ eval pool ρ a = .bool false := by
  unfold holds
  rw [eval_node hwf ρ he]
  simp only [Op.eval, List.map]
  cases eval pool ρ a with
  | bool b => cases b <;> simp [boolNotEval]
  | bv _ _ => simp [boolNotEval]
  | list _ _ => simp [boolNotEval]
  | bad => simp [boolNotEval]

theorem eval_not_node_false {pool : Pool} (hwf : WF pool) {e a : Nat}
    (he : pool[e]? = some ⟨.boolNot, #[a]⟩) (ρ : Assign)
    (h : eval pool ρ e = .bool false) : eval pool ρ a = .bool true := by
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, List.map] at h
  cases hv : eval pool ρ a with
  | bool b => rw [hv] at h; cases b <;> simp [boolNotEval] at h ⊢
  | bv _ _ => rw [hv] at h; simp [boolNotEval] at h
  | list _ _ => rw [hv] at h; simp [boolNotEval] at h
  | bad => rw [hv] at h; simp [boolNotEval] at h

theorem bools_all_true {vs : List Val} {bs : List Bool}
    (h : Val.bools vs = some bs) (hall : bs.all id = true) : ∀ v ∈ vs, v = .bool true := by
  induction vs generalizing bs with
  | nil => simp
  | cons v rest ih =>
    simp only [Val.bools] at h
    split at h
    · rename_i x xs hx hrest
      simp at h; subst h
      rw [List.all_cons, Bool.and_eq_true] at hall
      intro v' hv'
      simp at hv'
      rcases hv' with rfl | hv'
      · rw [Val.asBool_some_iff.mp hx]; have := hall.1; simp at this; rw [this]
      · exact ih hrest hall.2 v' hv'
    · simp at h

theorem bools_any_false {vs : List Val} {bs : List Bool}
    (h : Val.bools vs = some bs) (hany : bs.any id = false) : ∀ v ∈ vs, v = .bool false := by
  induction vs generalizing bs with
  | nil => simp
  | cons v rest ih =>
    simp only [Val.bools] at h
    split at h
    · rename_i x xs hx hrest
      simp at h; subst h
      rw [List.any_cons, Bool.or_eq_false_iff] at hany
      intro v' hv'
      simp at hv'
      rcases hv' with rfl | hv'
      · rw [Val.asBool_some_iff.mp hx]; have := hany.1; simp at this; rw [this]
      · exact ih hrest hany.2 v' hv'
    · simp at h

theorem bools_of_all_true {vs : List Val} (h : ∀ v ∈ vs, v = .bool true) :
    Val.bools vs = some (vs.map fun _ => true) := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
    have hv := h v (by simp)
    subst hv
    simp only [Val.bools, Val.asBool_bool, ih (fun v' hv' => h v' (by simp [hv']))]
    rfl

/-- A conjunction holds iff every conjunct does (given at least two). -/
theorem holds_conj_node {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.conj, args⟩) (ρ : Assign) (h : holds pool ρ e) :
    ∀ a ∈ args, holds pool ρ a := by
  unfold holds at h ⊢
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, boolN] at h
  cases hb : Val.bools (args.toList.map (eval pool ρ)) with
  | none => rw [hb] at h; simp at h
  | some bs =>
    rw [hb] at h
    dsimp only at h
    split at h
    · have h' : bs.all id = true := by simpa using h
      intro a ha
      exact bools_all_true hb h' (eval pool ρ a) (List.mem_map_of_mem (by simpa using ha))
    · simp at h

theorem holds_conj_intro {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.conj, args⟩) (ρ : Assign) (hlen : 2 ≤ args.size)
    (h : ∀ a ∈ args, holds pool ρ a) : holds pool ρ e := by
  unfold holds at h ⊢
  rw [eval_node hwf ρ he]
  simp only [Op.eval, boolN]
  rw [bools_of_all_true (fun v hv => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact h a (by simpa using ha))]
  simp [hlen] <;> (induction args.toList <;> simp_all)

/-- Under a negated disjunction every disjunct is false. -/
theorem holds_not_disj_node {pool : Pool} (hwf : WF pool) {e q : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.boolNot, #[q]⟩) (hq : pool[q]? = some ⟨.disj, args⟩) (ρ : Assign)
    (h : holds pool ρ e) : ∀ a ∈ args, eval pool ρ a = .bool false := by
  have hqf := (holds_not_node hwf he ρ).mp h
  rw [eval_node hwf ρ hq] at hqf
  simp only [Op.eval, boolN] at hqf
  cases hb : Val.bools (args.toList.map (eval pool ρ)) with
  | none => rw [hb] at hqf; simp at hqf
  | some bs =>
    rw [hb] at hqf
    dsimp only at hqf
    split at hqf
    · have h' : bs.any id = false := by simpa using hqf
      intro a ha
      exact bools_any_false hb h' (eval pool ρ a) (List.mem_map_of_mem (by simpa using ha))
    · simp at hqf

/-- Modus ponens at the value level. -/
theorem holds_implies_node {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.implies, #[a, b]⟩) (ρ : Assign)
    (h : holds pool ρ e) (ha : holds pool ρ a) : holds pool ρ b := by
  unfold holds at h ha ⊢
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, List.map, ha] at h
  cases hv : eval pool ρ b with
  | bool bb => rw [hv] at h; cases bb <;> simp [impliesEval] at h ⊢
  | bv _ _ => rw [hv] at h; simp [impliesEval] at h
  | list _ _ => rw [hv] at h; simp [impliesEval] at h
  | bad => rw [hv] at h; simp [impliesEval] at h

/-! ## The invariant -/

structure Inv (base : Pool) (g : Nat) (bi : Builtins) (st : St) : Prop where
  tys   : TysOK st.pool st.tys
  ext   : ∀ j, j < base.size → st.pool[j]? = base[j]?
  size  : base.size ≤ st.pool.size
  goal  : g < st.pool.size
  tt    : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩
  ff    : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩
  facts : ∀ (k f : Nat), st.facts[k]? = some f → f < st.pool.size
  sound : ∀ ρ, holds st.pool ρ g → ∀ (k f : Nat), st.facts[k]? = some f → holds st.pool ρ f

/-- "`f` is a node entailed by the goal." -/
def Entails (st : St) (g f : Nat) : Prop :=
  f < st.pool.size ∧ ∀ ρ, holds st.pool ρ g → holds st.pool ρ f

theorem Inv.wf {base g bi st} (h : Inv base g bi st) : WF st.pool := h.tys.wf

theorem idx_lt_of_get {pool : Pool} {i : Nat} {n : Node} (h : pool[i]? = some n) : i < pool.size := by
  rcases Nat.lt_or_ge i pool.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; cases h

/-- Pushing a node preserves the invariant. -/
theorem Inv.push {base g bi st st' n r} (hinv : Inv base g bi st) (h : pushNode st n = some (st', r)) :
    Inv base g bi st' where
  tys := pushNode_tysOK h hinv.tys
  ext := fun j hj => by rw [pushNode_prefix h j (Nat.lt_of_lt_of_le hj hinv.size)]; exact hinv.ext j hj
  size := Nat.le_trans hinv.size (pushNode_size h).1
  goal := Nat.lt_of_lt_of_le hinv.goal (pushNode_size h).1
  tt := by rw [pushNode_prefix h _ (idx_lt_of_get hinv.tt)]; exact hinv.tt
  ff := by rw [pushNode_prefix h _ (idx_lt_of_get hinv.ff)]; exact hinv.ff
  facts := by
    intro k f hf
    rw [pushNode_facts h] at hf
    exact Nat.lt_of_lt_of_le (hinv.facts k f hf) (pushNode_size h).1
  sound := by
    intro ρ hg k f hf
    rw [pushNode_facts h] at hf
    rw [pushNode_holds h ρ (hinv.facts k f hf)]
    rw [pushNode_holds h ρ hinv.goal] at hg
    exact hinv.sound ρ hg k f hf

theorem Entails.push {base g st st' n r f} (hinv : Inv base g bi st) (h : pushNode st n = some (st', r))
    (he : Entails st g f) : Entails st' g f := by
  refine ⟨Nat.lt_of_lt_of_le he.1 (pushNode_size h).1, ?_⟩
  intro ρ hg
  rw [pushNode_holds h ρ he.1]
  rw [pushNode_holds h ρ hinv.goal] at hg
  exact he.2 ρ hg

theorem Inv.addFact {base g bi st f} (hinv : Inv base g bi st) (he : Entails st g f) :
    Inv base g bi { st with facts := st.facts.push f } where
  tys := hinv.tys
  ext := hinv.ext
  size := hinv.size
  goal := hinv.goal
  tt := hinv.tt
  ff := hinv.ff
  facts := by
    intro k f' hf
    simp only [Array.getElem?_push] at hf
    split at hf
    · simp at hf; subst hf; exact he.1
    · exact hinv.facts k f' hf
  sound := by
    intro ρ hg k f' hf
    simp only [Array.getElem?_push] at hf
    split at hf
    · simp at hf; subst hf; exact he.2 ρ hg
    · exact hinv.sound ρ hg k f' hf

/-! ## Builders are sound -/

/-- The argument types recorded for a successfully pushed node. -/
theorem pushNode_argTys {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r))
    (hok : TysOK st.pool st.tys) :
    ∃ argTys t, mapOpt (fun a => typeOf st'.pool a) n.args.toList = some argTys ∧
      n.op.resultTy argTys = some t := by
  obtain ⟨argTys, t, hargs, hmap, ht, _⟩ := pushNode_cases h
  refine ⟨argTys, t, ?_, ht⟩
  rw [← hmap]
  apply mapOpt_congr
  intro a ha
  simp only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] at hargs
  have ha' := hargs a (by simpa using ha)
  rw [typeOf_extend (pushNode_prefix h) a ha']
  rcases hn : st.pool[a]? with _ | m
  · rw [Array.getElem?_eq_none_iff] at hn; omega
  · exact (hok.2 a m hn).2

/-- The type of a node, from its operator and children (no fuel guards). -/
theorem typeOf_node {pool : Pool} (hwf : WF pool) {e : Nat} {n : Node} (he : pool[e]? = some n) :
    typeOf pool e = (mapOpt (typeOf pool) n.args.toList).bind n.op.resultTy := by
  rw [typeOf_unfold, he]
  simp only
  have h1 := (hwf e n he).1
  rw [mapOpt_congr (g := typeOf pool) (fun x hx => by simp [h1 x (by simpa using hx)])]
  cases mapOpt (typeOf pool) n.args.toList <;> rfl

theorem boolNotTy_some {tys : List Ty} {t : Ty} (h : boolNotTy tys = some t) : tys = [.bool] := by
  unfold boolNotTy at h
  split at h
  · rename_i a; simp [tyGuard] at h; rw [h.1]
  · simp at h


/-- The argument of a successfully built `not` is boolean. -/
theorem mkNot_arg_bool {st st' : St} {a e : Nat} (h : mkNot st a = some (st', e)) (hok : TysOK st.pool st.tys) :
    typeOf st'.pool a = some .bool := by
  obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hok
  simp only [Op.resultTy] at ht
  have := boolNotTy_some ht; subst this
  simp only [mapOpt] at hmap
  cases hta : typeOf st'.pool a <;> rw [hta] at hmap <;> simp at hmap
  rw [hmap]

theorem mkEq_holds {st st' : St} {a b e : Nat} (h : mkEq st a b = some (st', e))
    (hok : TysOK st.pool st.tys) (ρ : Assign) (hab : eval st'.pool ρ a = eval st'.pool ρ b) :
    holds st'.pool ρ e := by
  have hwf := (pushNode_tysOK h hok).wf
  obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hok
  simp only [mapOpt] at hmap
  rw [holds_eq_node hwf (pushNode_get h) ρ]
  refine ⟨hab, ?_⟩
  cases hta : typeOf st'.pool a with
  | none => rw [hta] at hmap; simp at hmap
  | some ta =>
    cases htb : typeOf st'.pool b with
    | none => rw [hta, htb] at hmap; simp at hmap
    | some tb =>
      rw [hta, htb] at hmap; simp at hmap; subst hmap
      simp [Op.resultTy, eqTy, tyGuard] at ht
      refine ⟨ta, ?_, ht.1.2⟩
      rw [eval_ty, hta]

theorem mkEq_entails {g bi st st' a b e} (hinv : Inv base g bi st) (h : mkEq st a b = some (st', e))
    (hab : ∀ ρ, holds st.pool ρ g → eval st.pool ρ a = eval st.pool ρ b)
    (ha : a < st.pool.size) (hb : b < st.pool.size) :
    Inv base g bi st' ∧ Entails st' g e := by
  refine ⟨hinv.push h, (pushNode_size h).2, ?_⟩
  intro ρ hg
  rw [pushNode_holds h ρ hinv.goal] at hg
  apply mkEq_holds h hinv.tys ρ
  rw [pushNode_eval h ρ ha, pushNode_eval h ρ hb]
  exact hab ρ hg

theorem mkNot_holds {st st' : St} {a e : Nat} (h : mkNot st a = some (st', e)) (hok : TysOK st.pool st.tys)
    (ρ : Assign) (ha : eval st'.pool ρ a = .bool false) : holds st'.pool ρ e :=
  (holds_not_node (pushNode_tysOK h hok).wf (pushNode_get h) ρ).mpr ha

theorem mkNot_entails {g bi st st' a e} (hinv : Inv base g bi st) (h : mkNot st a = some (st', e))
    (ha : ∀ ρ, holds st.pool ρ g → eval st.pool ρ a = .bool false) (hlt : a < st.pool.size) :
    Inv base g bi st' ∧ Entails st' g e := by
  refine ⟨hinv.push h, (pushNode_size h).2, ?_⟩
  intro ρ hg
  rw [pushNode_holds h ρ hinv.goal] at hg
  apply mkNot_holds h hinv.tys ρ
  rw [pushNode_eval h ρ hlt]
  exact ha ρ hg

/-- The value of a built-in constant. -/
theorem eval_boolVal {pool : Pool} (hwf : WF pool) {i : Nat} {b : Bool}
    (h : pool[i]? = some ⟨.boolVal b, #[]⟩) (ρ : Assign) : eval pool ρ i = .bool b := by
  rw [eval_node hwf ρ h]; rfl

/-! ## Rule lemmas -/

section Rules
variable {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat}

theorem premise_entails {prems : List Nat} (hp : ∀ p ∈ prems, Entails st g p) {p : Nat}
    (hmem : p ∈ prems) (ρ : Assign) (hg : holds st.pool ρ g) : holds st.pool ρ p :=
  (hp p hmem).2 ρ hg

theorem node_eq_of_isEq {n : Node} {a b : Nat} (h : isEqNode n = some (a, b)) :
    n = ⟨.eq, #[a, b]⟩ := by
  unfold isEqNode at h
  split at h
  · rename_i args
    obtain ⟨l⟩ := args
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, rest⟩⟩⟩⟩ <;> simp at h
    first
      | (obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (subst h; rfl)
  · simp at h

theorem node_eq_of_isNot {n : Node} {a : Nat} (h : isNotNode n = some a) :
    n = ⟨.boolNot, #[a]⟩ := by
  unfold isNotNode at h
  split at h
  · rename_i args
    obtain ⟨l⟩ := args
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, rest⟩⟩⟩⟩ <;> simp at h
    first
      | (obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (subst h; rfl)
  · simp at h

theorem node_eq_of_isImplies {n : Node} {a b : Nat} (h : isImpliesNode n = some (a, b)) :
    n = ⟨.implies, #[a, b]⟩ := by
  unfold isImpliesNode at h
  split at h
  · rename_i args
    obtain ⟨l⟩ := args
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, rest⟩⟩⟩⟩ <;> simp at h
    first
      | (obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (subst h; rfl)
  · simp at h

theorem node_eq_of_isConj {n : Node} {args : Array Nat} (h : isConjNode n = some args) :
    n = ⟨.conj, args⟩ := by
  unfold isConjNode at h; split at h <;> simp at h; subst h; rfl

theorem node_eq_of_isDisj {n : Node} {args : Array Nat} (h : isDisjNode n = some args) :
    n = ⟨.disj, args⟩ := by
  unfold isDisjNode at h; split at h <;> simp at h; subst h; rfl

theorem node_bind_eq {p a b : Nat} (h : (st.node p).bind isEqNode = some (a, b)) :
    st.pool[p]? = some ⟨.eq, #[a, b]⟩ := by
  simp only [St.node, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hn'⟩ := h
  rw [hn, node_eq_of_isEq hn']

theorem node_bind_not {p a : Nat} (h : (st.node p).bind isNotNode = some a) :
    st.pool[p]? = some ⟨.boolNot, #[a]⟩ := by
  simp only [St.node, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hn'⟩ := h
  rw [hn, node_eq_of_isNot hn']

theorem node_bind_implies {p a b : Nat} (h : (st.node p).bind isImpliesNode = some (a, b)) :
    st.pool[p]? = some ⟨.implies, #[a, b]⟩ := by
  simp only [St.node, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hn'⟩ := h
  rw [hn, node_eq_of_isImplies hn']

theorem node_bind_conj {p : Nat} {args : Array Nat} (h : (st.node p).bind isConjNode = some args) :
    st.pool[p]? = some ⟨.conj, args⟩ := by
  simp only [St.node, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hn'⟩ := h
  rw [hn, node_eq_of_isConj hn']

theorem node_bind_disj {p : Nat} {args : Array Nat} (h : (st.node p).bind isDisjNode = some args) :
    st.pool[p]? = some ⟨.disj, args⟩ := by
  simp only [St.node, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hn'⟩ := h
  rw [hn, node_eq_of_isDisj hn']

/-- Children of a well-formed node are nodes. -/
theorem child_lt {pool : Pool} (hwf : WF pool) {i : Nat} {n : Node} (h : pool[i]? = some n)
    {a : Nat} (ha : a ∈ n.args) : a < pool.size :=
  Nat.lt_trans ((hwf i n h).1 a ha) (idx_lt_of_get h)

theorem ruleAssume_sound {ei : EI} {prems params : List Nat} (h : ruleAssume g ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleAssume at h
  split at h
  · rename_i p
    split at h
    · rename_i g' hg'
      split at h
      · rename_i hc; simp at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨hinv, hc.2.1, fun ρ hg => by rw [hc.1]; exact hg⟩
      · simp at h
    · simp at h
  · simp at h

theorem ruleRefl_sound {ei : EI} {prems params : List Nat} (h : ruleRefl ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleRefl at h
  split at h
  · rename_i p
    split at h
    · rename_i a _
      split at h
      · rename_i t ht
        split at h
        · rename_i hs
          have ha : a < st.pool.size := by
            have := hinv.tys.1
            rcases Nat.lt_or_ge a st.tys.size with h' | h'
            · omega
            · rw [Array.getElem?_eq_none h'] at ht; cases ht
          exact mkEq_entails hinv h (fun ρ _ => rfl) ha ha
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleSymm_sound {prems params : List Nat} (h : ruleSymm st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleSymm at h
  split at h
  · rename_i p
    have hpe := premise_entails hp (p := p) (by simp)
    split at h
    · rename_i n hn
      split at h
      · rename_i a b hab
        have hpn : st.pool[p]? = some ⟨.eq, #[a, b]⟩ := by rw [St.node] at hn; rw [hn, node_eq_of_isEq hab]
        have ha := child_lt hinv.wf hpn (a := a) (by simp)
        have hb := child_lt hinv.wf hpn (a := b) (by simp)
        apply mkEq_entails hinv h _ hb ha
        intro ρ hg
        exact ((holds_eq_node hinv.wf hpn ρ).mp (hpe ρ hg)).1.symm
      · split at h
        · rename_i q hq
          split at h
          · rename_i a b hab
            have hpn : st.pool[p]? = some ⟨.boolNot, #[q]⟩ := by rw [St.node] at hn; rw [hn, node_eq_of_isNot hq]
            have hqn := node_bind_eq hab
            have ha := child_lt hinv.wf hqn (a := a) (by simp)
            have hb := child_lt hinv.wf hqn (a := b) (by simp)
            split at h
            · rename_i st1 e he
              have hinv1 := hinv.push he
              apply mkNot_entails hinv1 h _ (pushNode_size he).2
              intro ρ hg
              rw [pushNode_holds he ρ hinv.goal] at hg
              have hq' := (holds_not_node hinv.wf hpn ρ).mp (hpe ρ hg)
              have hqv := eval_eq_node hinv.wf hqn ρ hq'
              have hwf1 := hinv1.wf
              rw [eval_node hwf1 ρ (pushNode_get he)]
              simp only [Op.eval, List.map, eqEval]
              rw [pushNode_eval he ρ ha, pushNode_eval he ρ hb, eqv_symm hqv]
              rfl
            · simp at h
          · simp at h
        · simp at h
    · simp at h
  · simp at h

theorem transChain_sound {rest : List Nat} (hwf : WF st.pool) :
    ∀ {lhs rhs lhs' rhs'}, transChain st rest lhs rhs = some (lhs', rhs') →
    (∀ p ∈ rest, ∀ ρ, holds st.pool ρ g → holds st.pool ρ p) →
    (∀ ρ, holds st.pool ρ g → eval st.pool ρ lhs = eval st.pool ρ rhs) →
    lhs' = lhs ∧ (rhs' = rhs ∨ rhs' < st.pool.size) ∧
      ∀ ρ, holds st.pool ρ g → eval st.pool ρ lhs = eval st.pool ρ rhs' := by
  induction rest with
  | nil =>
    intro lhs rhs lhs' rhs' h _ hlr
    simp [transChain] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Or.inl rfl, hlr⟩
  | cons p rest ih =>
    intro lhs rhs lhs' rhs' h hp hlr
    unfold transChain at h
    split at h
    · rename_i a b hab
      split at h
      · rename_i hae; subst hae
        have hpn := node_bind_eq hab
        have hb := child_lt hwf hpn (a := b) (by simp)
        have := ih h (fun p' hp' => hp p' (by simp [hp'])) (fun ρ hg => by
          rw [hlr ρ hg]
          exact ((holds_eq_node hwf hpn ρ).mp (hp p (by simp) ρ hg)).1)
        exact ⟨this.1, Or.inr (this.2.1.elim (fun e => e ▸ hb) id), this.2.2⟩
      · simp at h
    · simp at h

theorem ruleTrans_sound {prems params : List Nat} (h : ruleTrans st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleTrans at h
  split at h
  · rename_i p rest
    split at h
    · rename_i a b hab
      split at h
      · rename_i lhs rhs hchain
        have hpn := node_bind_eq hab
        have ha := child_lt hinv.wf hpn (a := a) (by simp)
        have hb := child_lt hinv.wf hpn (a := b) (by simp)
        have hpe := premise_entails hp (p := p) (by simp)
        obtain ⟨rfl, hr, hlr⟩ := transChain_sound hinv.wf hchain
          (fun p' hp' ρ hg => premise_entails hp (by simp [hp']) ρ hg)
          (fun ρ hg => ((holds_eq_node hinv.wf hpn ρ).mp (hpe ρ hg)).1)
        have hrhs : rhs < st.pool.size := hr.elim (fun e => e ▸ hb) id
        exact mkEq_entails hinv h hlr ha hrhs
      · simp at h
    · simp at h
  · simp at h

theorem eqSides_sound {prems : List Nat} (hwf : WF st.pool) :
    ∀ {as bs}, eqSides st prems = some (as, bs) →
    (∀ p ∈ prems, ∀ ρ, holds st.pool ρ g → holds st.pool ρ p) →
    as.length = prems.length ∧ bs.length = prems.length ∧
    (∀ a ∈ as, a < st.pool.size) ∧ (∀ b ∈ bs, b < st.pool.size) ∧
    ∀ ρ, holds st.pool ρ g → as.map (eval st.pool ρ) = bs.map (eval st.pool ρ) := by
  induction prems with
  | nil =>
    intro as bs h _
    simp [eqSides] at h; obtain ⟨rfl, rfl⟩ := h
    simp
  | cons p rest ih =>
    intro as bs h hp
    unfold eqSides at h
    split at h
    · rename_i a b as' bs' hab hrest
      simp at h; obtain ⟨rfl, rfl⟩ := h
      have hpn := node_bind_eq hab
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih hrest (fun p' hp' => hp p' (by simp [hp']))
      refine ⟨by simp [h1], by simp [h2], ?_, ?_, ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | hx
        · exact child_lt hwf hpn (by simp)
        · exact h3 x hx
      · intro x hx; simp at hx; rcases hx with rfl | hx
        · exact child_lt hwf hpn (by simp)
        · exact h4 x hx
      · intro ρ hg
        simp only [List.map_cons]
        rw [((holds_eq_node hwf hpn ρ).mp (hp p (by simp) ρ hg)).1, h5 ρ hg]
    · simp at h

theorem ruleCong_sound {prems params : List Nat} (h : ruleCong st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCong at h
  split at h
  · rename_i hdr
    split at h
    · rename_i as bs hsides
      split at h
      · rename_i op hop
        split at h
        · rename_i st1 l hl
          split at h
          · rename_i st2 r hr
            obtain ⟨_, _, has, hbs, hab⟩ := eqSides_sound hinv.wf hsides
              (fun p hp' ρ hg => premise_entails hp hp' ρ hg)
            have hinv1 := hinv.push hl
            have hinv2 := hinv1.push hr
            have hl2 : l < st2.pool.size := Nat.lt_of_lt_of_le (pushNode_size hl).2 (pushNode_size hr).1
            have hr2 : r < st2.pool.size := (pushNode_size hr).2
            apply mkEq_entails hinv2 h _ hl2 hr2
            intro ρ hg
            have hg1 : holds st1.pool ρ g := by rw [← pushNode_holds hr ρ hinv1.goal]; exact hg
            have hg0 : holds st.pool ρ g := by rw [← pushNode_holds hl ρ hinv.goal]; exact hg1
            have hln : st2.pool[l]? = some ⟨op, as.toArray⟩ := by
              rw [pushNode_prefix hr l (pushNode_size hl).2]; exact pushNode_get hl
            rw [eval_node hinv2.wf ρ hln, eval_node hinv2.wf ρ (pushNode_get hr)]
            simp only
            congr 1
            have e1 : as.map (eval st2.pool ρ) = as.map (eval st.pool ρ) := by
              apply List.map_congr_left; intro a ha
              rw [pushNode_eval hr ρ (Nat.lt_of_lt_of_le (has a ha) (pushNode_size hl).1),
                  pushNode_eval hl ρ (has a ha)]
            have e2 : bs.map (eval st2.pool ρ) = bs.map (eval st.pool ρ) := by
              apply List.map_congr_left; intro b hb
              rw [pushNode_eval hr ρ (Nat.lt_of_lt_of_le (hbs b hb) (pushNode_size hl).1),
                  pushNode_eval hl ρ (hbs b hb)]
            rw [e1, e2, hab ρ hg0]
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleTrueIntro_sound {prems params : List Nat} (h : ruleTrueIntro bi st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleTrueIntro at h
  split at h
  · rename_i p
    have hpe := hp p (by simp)
    apply mkEq_entails hinv h _ hpe.1 (idx_lt_of_get hinv.tt)
    intro ρ hg
    rw [eval_boolVal hinv.wf hinv.tt ρ]
    exact hpe.2 ρ hg
  · simp at h

theorem ruleTrueElim_sound {prems params : List Nat} (h : ruleTrueElim bi st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleTrueElim at h
  split at h
  · rename_i p
    split at h
    · rename_i a t hat
      split at h
      · rename_i ht; subst ht
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hpn := node_bind_eq hat
        refine ⟨hinv, child_lt hinv.wf hpn (by simp), ?_⟩
        intro ρ hg
        have := ((holds_eq_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)).1
        unfold holds; rw [this]; exact eval_boolVal hinv.wf hinv.tt ρ
      · simp at h
    · simp at h
  · simp at h

theorem ruleFalseIntro_sound {prems params : List Nat} (h : ruleFalseIntro bi st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleFalseIntro at h
  split at h
  · rename_i p
    split at h
    · rename_i a ha
      have hpn := node_bind_not ha
      apply mkEq_entails hinv h _ (child_lt hinv.wf hpn (by simp)) (idx_lt_of_get hinv.ff)
      intro ρ hg
      rw [eval_boolVal hinv.wf hinv.ff ρ]
      exact (holds_not_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)
    · simp at h
  · simp at h

theorem ruleFalseElim_sound {prems params : List Nat} (h : ruleFalseElim bi st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleFalseElim at h
  split at h
  · rename_i p
    split at h
    · rename_i a t hat
      split at h
      · rename_i ht; subst ht
        have hpn := node_bind_eq hat
        apply mkNot_entails hinv h _ (child_lt hinv.wf hpn (by simp))
        intro ρ hg
        have := ((holds_eq_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)).1
        rw [this]; exact eval_boolVal hinv.wf hinv.ff ρ
      · simp at h
    · simp at h
  · simp at h

theorem ruleEqResolve_sound {prems params : List Nat} (h : ruleEqResolve st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleEqResolve at h
  split at h
  · rename_i p q
    split at h
    · rename_i a b hab
      split at h
      · rename_i hap; subst hap
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hqn := node_bind_eq hab
        refine ⟨hinv, child_lt hinv.wf hqn (by simp), ?_⟩
        intro ρ hg
        have := ((holds_eq_node hinv.wf hqn ρ).mp (premise_entails hp (p := q) (by simp) ρ hg)).1
        unfold holds; rw [← this]; exact premise_entails hp (p := a) (by simp) ρ hg
      · simp at h
    · simp at h
  · simp at h

theorem ruleModusPonens_sound {prems params : List Nat}
    (h : ruleModusPonens st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleModusPonens at h
  split at h
  · rename_i p q
    split at h
    · rename_i a b hab
      split at h
      · rename_i hap; subst hap
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hqn := node_bind_implies hab
        refine ⟨hinv, child_lt hinv.wf hqn (by simp), ?_⟩
        intro ρ hg
        exact holds_implies_node hinv.wf hqn ρ (premise_entails hp (p := q) (by simp) ρ hg)
          (premise_entails hp (p := a) (by simp) ρ hg)
      · simp at h
    · simp at h
  · simp at h

theorem ruleNotNotElim_sound {prems params : List Nat}
    (h : ruleNotNotElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleNotNotElim at h
  split at h
  · rename_i p
    split at h
    · rename_i q hq
      split at h
      · rename_i a ha
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hpn := node_bind_not hq
        have hqn := node_bind_not ha
        refine ⟨hinv, child_lt hinv.wf hqn (by simp), ?_⟩
        intro ρ hg
        have hqf := (holds_not_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)
        exact eval_not_node_false hinv.wf hqn ρ hqf
      · simp at h
    · simp at h
  · simp at h

theorem ruleContra_sound {prems params : List Nat} (h : ruleContra bi st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleContra at h
  split at h
  · rename_i p q
    split at h
    · rename_i a ha
      split at h
      · rename_i hc
        simp at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, hff⟩ := hc
        refine ⟨hinv, hff, ?_⟩
        intro ρ hg
        have h1 := premise_entails hp (p := a) (by simp) ρ hg
        have h2 := (holds_not_node hinv.wf (node_bind_not ha) ρ).mp (premise_entails hp (p := q) (by simp) ρ hg)
        unfold holds at h1; rw [h1] at h2; cases h2
      · simp at h
    · simp at h
  · simp at h

theorem ruleAndElim_sound {prems params : List Nat} (h : ruleAndElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleAndElim at h
  split at h
  · rename_i p k
    split at h
    · rename_i args hargs
      split at h
      · rename_i a hak
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hpn := node_bind_conj hargs
        have hmem : a ∈ args := by
          rw [Array.getElem?_eq_some_iff] at hak
          obtain ⟨hk, rfl⟩ := hak
          exact Array.getElem_mem hk
        refine ⟨hinv, child_lt hinv.wf hpn hmem, ?_⟩
        intro ρ hg
        exact holds_conj_node hinv.wf hpn ρ (premise_entails hp (p := p) (by simp) ρ hg) a hmem
      · simp at h
    · simp at h
  · simp at h

theorem ruleAndIntro_sound {prems params : List Nat} (h : ruleAndIntro st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleAndIntro at h
  split at h
  · rename_i p
    simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hinv, hp p (by simp)⟩
  · rename_i prems' _
    split at h
    · rename_i hlen
      refine ⟨hinv.push h, (pushNode_size h).2, ?_⟩
      intro ρ hg
      rw [pushNode_holds h ρ hinv.goal] at hg
      apply holds_conj_intro (hinv.push h).wf (pushNode_get h) ρ (by simpa using hlen)
      intro a ha
      have ha' := hp a (by simpa using ha)
      rw [pushNode_holds h ρ ha'.1]
      exact ha'.2 ρ hg
    · simp at h
  · simp at h

theorem ruleNotOrElim_sound {prems params : List Nat}
    (h : ruleNotOrElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleNotOrElim at h
  split at h
  · rename_i p k
    split at h
    · rename_i q hq
      split at h
      · rename_i args hargs
        split at h
        · rename_i a hak
          have hpn := node_bind_not hq
          have hqn := node_bind_disj hargs
          have hmem : a ∈ args := by
            rw [Array.getElem?_eq_some_iff] at hak
            obtain ⟨hk, rfl⟩ := hak
            exact Array.getElem_mem hk
          apply mkNot_entails hinv h _ (child_lt hinv.wf hqn hmem)
          intro ρ hg
          exact holds_not_disj_node hinv.wf hpn hqn ρ (premise_entails hp (p := p) (by simp) ρ hg) a hmem
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleSplit_sound {ei : EI} {prems params : List Nat} (h : ruleSplit ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleSplit at h
  split at h
  · rename_i p
    split at h
    · rename_i a _
      split at h
      · rename_i st1 na hna
        have hinv1 := hinv.push hna
        have hta := mkNot_arg_bool hna hinv.tys
        have ha1 : a < st1.pool.size := by
          rcases hn : st1.pool[a]? with _ | n
          · rw [typeOf_unfold, hn] at hta; simp at hta
          · exact idx_lt_of_get hn
        refine ⟨hinv1.push h, (pushNode_size h).2, ?_⟩
        intro ρ _
        have hinv2 := hinv1.push h
        unfold holds
        rw [eval_node hinv2.wf ρ (pushNode_get h)]
        simp only [Op.eval, boolN, List.map]
        obtain ⟨b, hb⟩ := eval_bool (ρ := ρ) hta
        have hna' : eval st1.pool ρ na = .bool (!b) := by
          rw [eval_node hinv1.wf ρ (pushNode_get hna)]
          simp only [Op.eval, List.map, hb, boolNotEval]
        rw [pushNode_eval h ρ ha1, pushNode_eval h ρ (pushNode_size hna).2, hb, hna']
        simp [Val.bools] <;> cases b <;> simp
      · simp at h
    · simp at h
  · simp at h

/-! ### EVALUATE -/

theorem noVarsF_stable (pool : Pool) (i : Nat) :
    ∀ f f', i < f → i < f' → noVarsF pool f i = noVarsF pool f' i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f f' hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [noVarsF]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      split <;> try rfl
      congr 1
      funext a
      by_cases ha : a < i
      · simp only [ha, decide_true, Bool.true_and]
        exact ih a ha g g' (by omega) (by omega)
      · simp [ha]

theorem Op.eval_noVar {op : Op} (h1 : ∀ w id, op ≠ .bvVar w id) (h2 : ∀ id, op ≠ .boolVar id)
    (ρ ρ' : Assign) (vs : List Val) : op.eval ρ vs = op.eval ρ' vs := by
  cases op <;> first | rfl | exact absurd rfl (h1 _ _) | exact absurd rfl (h2 _)

/-- `bvsize` depends only on the type of its argument. -/
theorem bvSizeEval_tydep (w : Nat) {vs vs' : List Val} (h : vs.map Val.ty = vs'.map Val.ty) :
    bvSizeEval w vs = bvSizeEval w vs' := by
  match vs, vs', h with
  | [], [], _ => rfl
  | [a], [a'], h =>
    simp at h
    cases a <;> cases a' <;> simp at h <;> simp [bvSizeEval] <;> simp [h]
  | _ :: _ :: _, _ :: _ :: _, _ => simp [bvSizeEval]
  | [], _ :: _, h => simp at h
  | _ :: _, [], h => simp at h
  | [_], _ :: _ :: _, h => simp at h
  | _ :: _ :: _, [_], h => simp at h

/-- A variable-free node has the same value in every state. -/
theorem eval_noVars {pool : Pool} (ρ ρ' : Assign) :
    ∀ i, noVars pool i = true → eval pool ρ i = eval pool ρ' i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro h
    unfold noVars at h
    simp only [noVarsF] at h
    rw [eval_unfold, eval_unfold]
    cases hn : pool[i]? with
    | none => rfl
    | some n =>
      rw [hn] at h
      simp only at h ⊢
      split at h
      · simp at h
      · simp at h
      · rename_i w hw
        rw [hw]
        simp only [Op.eval]
        apply bvSizeEval_tydep
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro a _
        simp only [Function.comp]
        split <;> simp [eval_ty]
      · rename_i hv1 hv2 hv3
        have hargs : ∀ a ∈ n.args, a < i ∧ noVarsF pool i a = true := by
          intro a ha
          simp only [Array.all_eq_true_iff_forall_mem, Bool.and_eq_true, decide_eq_true_eq] at h
          exact h a ha
        rw [Op.eval_noVar (fun w id e => hv1 w id e) (fun id e => hv2 id e) ρ ρ']
        congr 1
        apply List.map_congr_left
        intro a ha
        obtain ⟨hlt, hnv⟩ := hargs a (by simpa using ha)
        simp only [hlt, ite_true]
        apply ih a hlt
        unfold noVars
        rw [noVarsF_stable pool a _ _ (by omega) hlt]
        exact hnv

theorem litOf_eval {st st' : St} {v : Val} {lit : Node} {l : Nat}
    (hl : litOf v = some lit) (h : pushNode st lit = some (st', l)) (hok : TysOK st.pool st.tys)
    (ρ : Assign) : eval st'.pool ρ l = v := by
  have hwf := (pushNode_tysOK h hok).wf
  obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hok
  rw [eval_node hwf ρ (pushNode_get h)]
  cases v with
  | bv w x =>
    simp [litOf] at hl; subst hl
    simp only [mapOpt] at hmap
    simp at hmap; subst hmap
    simp only [Op.resultTy, bvValTy, tyGuard] at ht
    split at ht
    · rename_i hc
      simp only [Op.eval, List.map]
      simp [bvValEval, hc.1, hc.2.1, hc.2.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp at ht
  | bool b =>
    simp [litOf] at hl; subst hl
    rfl
  | list _ _ => simp [litOf] at hl
  | bad => simp [litOf] at hl

theorem Op.eval_indep (op : Op) (hv : ∀ w id, op ≠ .bvVar w id) (hb : ∀ id, op ≠ .boolVar id)
    (ρ ρ' : Assign) (vs : List Val) : Op.eval ρ op vs = Op.eval ρ' op vs := by
  cases op <;> first | rfl | exact absurd rfl (hv _ _) | exact absurd rfl (hb _)

theorem mapOpt_eq_map {f : α → Option β} {g : α → β} {l : List α} {l' : List β}
    (h : mapOpt f l = some l') (hfg : ∀ a ∈ l, ∀ v, f a = some v → g a = v) : l.map g = l' := by
  induction l generalizing l' with
  | nil => simp [mapOpt] at h; subst h; rfl
  | cons a rest ih =>
    simp only [mapOpt] at h
    split at h
    · rename_i b bs hb hbs
      simp at h; subst h
      simp only [List.map_cons]
      rw [hfg a (by simp) b hb, ih hbs (fun a' ha' => hfg a' (by simp [ha']))]
    · simp at h

theorem node_of_lt' {pool : Pool} {a : Nat} (ha : a < pool.size) : ∃ m, pool[a]? = some m := by
  cases hm : pool[a]? with
  | none => rw [Array.getElem?_eq_none_iff] at hm; omega
  | some m => exact ⟨m, rfl⟩

theorem memoBuild_size (st : St) : ∀ k, (memoBuild st k).size = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [memoBuild, memoPush, ih]

theorem memoBuild_get (st : St) : ∀ k j, j < k → (memoBuild st k)[j]? = some (memoVal st j) := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    simp only [memoBuild, memoPush, Array.getElem?_push, memoBuild_size]
    by_cases h : j = k
    · subst h; simp [memoVal]
    · rw [ite_eq_right h]; exact ih j (by omega)

/-- Memoised constant values are the values under every assignment. -/
theorem memoVal_eval {st : St} (hok : TysOK st.pool st.tys) (ρ : Assign) :
    ∀ i v, memoVal st i = some v → eval st.pool ρ i = v := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro v h
    unfold memoVal memoStep at h
    split at h
    · simp at h
    · rename_i n hn
      have hwf := hok.wf
      have hlt := (hok.2 i n hn).1
      split at h
      · simp at h
      · simp at h
      · rename_i w hop
        split at h
        · rename_i a hargs
          split at h
          · rename_i m hm
            simp at h; subst h
            obtain ⟨op, args⟩ := n
            simp only at hop hargs; subst hop
            have : args = #[a] := Array.ext' hargs
            subst this
            rw [eval_node hwf ρ hn]
            have ha : a < st.pool.size := by
              rw [← hok.1]; exact (Array.getElem?_eq_some_iff.mp hm).1
            obtain ⟨m', hm'⟩ := node_of_lt' ha
            rw [← (hok.2 a m' hm').2] at hm
            obtain ⟨x, hx⟩ := eval_bv (ρ := ρ) hm
            simp only [List.map, hx]
            rfl
          · simp at h
        · simp at h
      · rename_i hnv hnb hns
        split at h
        · rename_i vs hvs
          simp at h; subst h
          rw [eval_node hwf ρ hn]
          have hmap : n.args.toList.map (eval st.pool ρ) = vs := by
            apply mapOpt_eq_map hvs
            intro a ha v' hv'
            have ha' : a < i := hlt a (by simpa using ha)
            simp only [ha', ite_true, memoBuild_get st i a ha', Option.bind_some] at hv'
            exact ih a ha' v' hv'
          rw [hmap]
          exact Op.eval_indep n.op (fun w id hh => hnv w id hh) (fun id hh => hnb id hh) ρ _ vs
        · simp at h

theorem memoVal_lt {st : St} {i : Nat} {v : Val} (h : memoVal st i = some v) : i < st.pool.size := by
  unfold memoVal memoStep at h
  split at h
  · simp at h
  · rename_i n hn; exact idx_lt_of_get hn

theorem ruleEvaluate_sound {ei : EI} {prems params : List Nat} (h : ruleEvaluate ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleEvaluate at h
  split at h
  · rename_i p
    split at h
    · simp at h
    · rename_i e _
      split at h
      · rename_i v hv
        split at h
        · rename_i lit hlit
          split at h
          · rename_i st1 l hl
            have hinv1 := hinv.push hl
            have he : e < st.pool.size := memoVal_lt hv
            apply mkEq_entails hinv1 h _ (Nat.lt_of_lt_of_le he (pushNode_size hl).1) (pushNode_size hl).2
            intro ρ _
            rw [litOf_eval hlit hl hinv.tys ρ, pushNode_eval hl ρ he]
            exact memoVal_eval hinv.tys ρ e v hv
          · simp at h
        · simp at h
      · simp at h
  · simp at h

/-! ### Extension of the pool through several pushes -/

def Extends (st st' : St) : Prop :=
  st.pool.size ≤ st'.pool.size ∧ ∀ j, j < st.pool.size → st'.pool[j]? = st.pool[j]?

theorem Extends.refl (st : St) : Extends st st := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Extends.trans {a b c : St} (h1 : Extends a b) (h2 : Extends b c) : Extends a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun j hj => by rw [h2.2 j (Nat.lt_of_lt_of_le hj h1.1), h1.2 j hj]⟩

theorem pushNode_extends {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r)) :
    Extends st st' := ⟨(pushNode_size h).1, pushNode_prefix h⟩

theorem holds_ext {st st' : St} (h : Extends st st') (ρ : Assign) {i : Nat} (hi : i < st.pool.size) :
    holds st'.pool ρ i ↔ holds st.pool ρ i := by
  unfold holds; rw [eval_extend ρ h.2 i hi]

theorem eval_ext {st st' : St} (h : Extends st st') (ρ : Assign) {i : Nat} (hi : i < st.pool.size) :
    eval st'.pool ρ i = eval st.pool ρ i := eval_extend ρ h.2 i hi

theorem get_ext {st st' : St} (h : Extends st st') {i : Nat} {n : Node} (hi : st.pool[i]? = some n) :
    st'.pool[i]? = some n := by rw [h.2 i (idx_lt_of_get hi)]; exact hi

/-! ### Disjunctions -/

theorem bools_exists {vs : List Val} (h : ∀ v ∈ vs, ∃ b, v = .bool b) : ∃ bs, Val.bools vs = some bs := by
  induction vs with
  | nil => exact ⟨[], rfl⟩
  | cons v rest ih =>
    obtain ⟨b, rfl⟩ := h v (by simp)
    obtain ⟨bs, hbs⟩ := ih (fun v' hv' => h v' (by simp [hv']))
    exact ⟨b :: bs, by simp [Val.bools, hbs]⟩

theorem bools_any_iff {vs : List Val} {bs : List Bool} (h : Val.bools vs = some bs) :
    bs.any id = true ↔ ∃ v ∈ vs, v = .bool true := by
  induction vs generalizing bs with
  | nil => simp [Val.bools] at h; subst h; simp
  | cons v rest ih =>
    simp only [Val.bools] at h
    split at h
    · rename_i x xs hx hrest
      simp at h; subst h
      rw [Val.asBool_some_iff] at hx; subst hx
      simp [ih hrest] <;> cases x <;> simp
    · simp at h

theorem mapOpt_mem {f : α → Option β} {l : List α} {l' : List β} (h : mapOpt f l = some l')
    {x : α} (hx : x ∈ l) : ∃ y ∈ l', f x = some y := by
  induction l generalizing l' with
  | nil => simp at hx
  | cons a rest ih =>
    simp only [mapOpt] at h
    split at h
    · rename_i b bs hb hrest
      simp at h; subst h
      simp at hx
      rcases hx with rfl | hx
      · exact ⟨b, by simp, hb⟩
      · obtain ⟨y, hy, hfy⟩ := ih hrest hx
        exact ⟨y, by simp [hy], hfy⟩
    · simp at h

theorem allBool_mem {tys : List Ty} (h : allBool tys = true) {t : Ty} (ht : t ∈ tys) : t = .bool := by
  induction tys with
  | nil => simp at ht
  | cons a rest ih =>
    cases a with
    | bool =>
      simp at ht
      rcases ht with rfl | ht
      · rfl
      · exact ih (by simpa [allBool] using h) ht
    | bv _ => simp [allBool] at h
    | list _ _ => simp [allBool] at h

/-- Every argument of a well-typed `disj`/`conj` node is boolean. -/
theorem boolN_args_bool {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.disj, args⟩ ∨ pool[e]? = some ⟨.conj, args⟩) :
    ∀ a ∈ args, typeOf pool a = some .bool := by
  have key : ∀ op, pool[e]? = some ⟨op, args⟩ → op.resultTy = boolNTy → ∀ a ∈ args, typeOf pool a = some .bool := by
    intro op hop hres a ha
    have h2 := (hwf e _ hop).2
    rw [typeOf_node hwf hop] at h2
    simp only [hres] at h2
    cases hm : mapOpt (typeOf pool) args.toList with
    | none => rw [hm] at h2; simp at h2
    | some tys =>
      rw [hm] at h2
      simp only [Option.bind_some, boolNTy, tyGuard] at h2
      split at h2
      · rename_i hc
        obtain ⟨y, hy, hfy⟩ := mapOpt_mem hm (by simpa using ha)
        rw [hfy]; congr; exact allBool_mem hc.1 hy
      · simp at h2
  rcases he with he | he
  · exact key _ he rfl
  · exact key _ he rfl

theorem holds_disj_elim {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.disj, args⟩) (ρ : Assign) (h : holds pool ρ e) :
    ∃ a ∈ args, holds pool ρ a := by
  unfold holds at h ⊢
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, boolN] at h
  cases hb : Val.bools (args.toList.map (eval pool ρ)) with
  | none => rw [hb] at h; simp at h
  | some bs =>
    rw [hb] at h
    dsimp only at h
    split at h
    · have h' : bs.any id = true := by simpa using h
      obtain ⟨v, hv, hvt⟩ := (bools_any_iff hb).mp h'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact ⟨a, by simpa using ha, hvt⟩
    · simp at h

theorem holds_disj_intro {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.disj, args⟩) (ρ : Assign) (hlen : 2 ≤ args.size)
    (h : ∃ a ∈ args, holds pool ρ a) : holds pool ρ e := by
  have hargs := boolN_args_bool hwf (Or.inl he)
  unfold holds
  rw [eval_node hwf ρ he]
  simp only [Op.eval, boolN]
  obtain ⟨bs, hbs⟩ := bools_exists (vs := args.toList.map (eval pool ρ)) (by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact eval_bool (hargs a (by simpa using ha)))
  rw [hbs]
  have hl : bs.length = args.size := by have := Val.tys_length (Val.bools_some_tys hbs); simp at this; omega
  simp only [hl, hlen, ite_true]
  congr 1
  rw [bools_any_iff hbs]
  obtain ⟨a, ha, hat⟩ := h
  exact ⟨eval pool ρ a, List.mem_map_of_mem (by simpa using ha), hat⟩

theorem mkDisj_holds {st st' : St} {lits : Array Nat} {d : Nat} (h : mkDisj st lits = some (st', d))
    (hok : TysOK st.pool st.tys) (ρ : Assign) (hl : ∃ l ∈ lits, holds st'.pool ρ l) :
    holds st'.pool ρ d := by
  have hwf := (pushNode_tysOK h hok).wf
  obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hok
  simp only [Op.resultTy, boolNTy, tyGuard] at ht
  split at ht
  · rename_i hc
    have hlen : 2 ≤ lits.size := by have := mapOpt_length hmap; simp at this; omega
    exact holds_disj_intro hwf (pushNode_get h) ρ hlen hl
  · simp at ht

theorem mkDisj_entails {lits : Array Nat} {d : Nat} (hinv : Inv base g bi st)
    (h : mkDisj st lits = some (st', d)) (hl : ∀ l ∈ lits, l < st.pool.size)
    (hc : ∀ ρ, holds st.pool ρ g → ∃ l ∈ lits, holds st.pool ρ l) :
    Inv base g bi st' ∧ Entails st' g d := by
  refine ⟨hinv.push h, (pushNode_size h).2, ?_⟩
  intro ρ hg
  rw [pushNode_holds h ρ hinv.goal] at hg
  apply mkDisj_holds h hinv.tys ρ
  obtain ⟨l, hl', hlt⟩ := hc ρ hg
  exact ⟨l, hl', by rw [pushNode_holds h ρ (hl l hl')]; exact hlt⟩

/-! ### Value-level facts for the boolean connectives -/

theorem eval_not_node {pool : Pool} (hwf : WF pool) {e a : Nat}
    (he : pool[e]? = some ⟨.boolNot, #[a]⟩) (ρ : Assign) {r : Bool}
    (h : eval pool ρ e = .bool r) : eval pool ρ a = .bool (!r) := by
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, List.map] at h
  cases hv : eval pool ρ a with
  | bool b => rw [hv] at h; simp [boolNotEval] at h; rw [← h] <;> simp
  | bv _ _ => rw [hv] at h; simp [boolNotEval] at h
  | list _ _ => rw [hv] at h; simp [boolNotEval] at h
  | bad => rw [hv] at h; simp [boolNotEval] at h

theorem impliesEval_inv {vs : List Val} {r : Bool} (h : impliesEval vs = .bool r) :
    ∃ x y, vs = [.bool x, .bool y] ∧ r = (!x || y) := by
  unfold impliesEval at h
  split at h
  · rename_i x y; simp at h; exact ⟨x, y, rfl, h.symm⟩
  · simp at h

theorem boolIteEval_inv {vs : List Val} {r : Bool} (h : boolIteEval vs = .bool r) :
    ∃ c x y, vs = [.bool c, .bool x, .bool y] ∧ r = (if c then x else y) := by
  unfold boolIteEval at h
  split at h
  · rename_i c x y; simp at h; exact ⟨c, x, y, rfl, h.symm⟩
  · simp at h

theorem boolN2_inv {f : List Bool → Bool} {v1 v2 : Val} {r : Bool} (h : boolN f [v1, v2] = .bool r) :
    ∃ x y, v1 = .bool x ∧ v2 = .bool y ∧ r = f [x, y] := by
  cases v1 <;> cases v2 <;> simp [boolN, Val.bools] at h <;> exact ⟨_, _, rfl, rfl, by simp_all⟩

theorem eval_implies_node {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.implies, #[a, b]⟩) (ρ : Assign) {r : Bool}
    (h : eval pool ρ e = .bool r) :
    ∃ x y, eval pool ρ a = .bool x ∧ eval pool ρ b = .bool y ∧ r = (!x || y) := by
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, List.map] at h
  obtain ⟨x, y, hvs, hr⟩ := impliesEval_inv h
  simp at hvs
  exact ⟨x, y, hvs.1, hvs.2, hr⟩

theorem eqv_bool_left {x : Bool} {v : Val} {r : Bool} (h : Val.eqv (.bool x) v = .bool r) :
    ∃ y, v = .bool y ∧ r = decide (x = y) := by
  cases v <;> simp [Val.eqv] at h
  exact ⟨_, rfl, h.symm⟩

theorem eval_xor2_node {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.boolXor, #[a, b]⟩) (ρ : Assign) {r : Bool}
    (h : eval pool ρ e = .bool r) :
    ∃ x y, eval pool ρ a = .bool x ∧ eval pool ρ b = .bool y ∧ r = (x ^^ y) := by
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, List.map] at h
  obtain ⟨x, y, hx, hy, hr⟩ := boolN2_inv h
  exact ⟨x, y, hx, hy, by rw [hr]; simp⟩

theorem eval_boolIte_node {pool : Pool} (hwf : WF pool) {e c a b : Nat}
    (he : pool[e]? = some ⟨.boolIte, #[c, a, b]⟩) (ρ : Assign) {r : Bool}
    (h : eval pool ρ e = .bool r) :
    ∃ cv av bv, eval pool ρ c = .bool cv ∧ eval pool ρ a = .bool av ∧ eval pool ρ b = .bool bv ∧
      r = (if cv then av else bv) := by
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, List.map] at h
  obtain ⟨cv, x, y, hvs, hr⟩ := boolIteEval_inv h
  simp at hvs
  exact ⟨cv, x, y, hvs.1, hvs.2.1, hvs.2.2, hr⟩

/-- A well-typed ite selects a branch. -/
theorem eval_ite_sel {pool : Pool} (hwf : WF pool) {e c a b : Nat}
    (he : pool[e]? = some ⟨.boolIte, #[c, a, b]⟩ ∨ ∃ w, pool[e]? = some ⟨.bvIte w, #[c, a, b]⟩)
    (ρ : Assign) {cv : Bool} (hc : eval pool ρ c = .bool cv) :
    eval pool ρ e = if cv then eval pool ρ a else eval pool ρ b := by
  rcases he with he | ⟨w, he⟩
  · have hty := (hwf e _ he).2
    rw [typeOf_node hwf he] at hty
    simp only [mapOpt, Op.resultTy] at hty
    cases htc : typeOf pool c <;> rw [htc] at hty <;> cases hta : typeOf pool a <;> rw [hta] at hty <;>
      cases htb : typeOf pool b <;> rw [htb] at hty <;> simp [boolIteTy, tyGuard] at hty
    obtain ⟨-, rfl, rfl⟩ := hty
    obtain ⟨av, hav⟩ := eval_bool (ρ := ρ) hta
    obtain ⟨bv, hbv⟩ := eval_bool (ρ := ρ) htb
    rw [eval_node hwf ρ he]
    simp only [Op.eval, List.map, hc, hav, hbv, boolIteEval]
    cases cv <;> simp
  · have hty := (hwf e _ he).2
    rw [typeOf_node hwf he] at hty
    simp only [mapOpt, Op.resultTy] at hty
    cases htc : typeOf pool c <;> rw [htc] at hty <;> cases hta : typeOf pool a <;> rw [hta] at hty <;>
      cases htb : typeOf pool b <;> rw [htb] at hty <;> simp [bvIteTy, tyGuard] at hty
    obtain ⟨hw, -, rfl, rfl⟩ := hty
    obtain ⟨av, hav⟩ := eval_bv (ρ := ρ) hta
    obtain ⟨bv, hbv⟩ := eval_bv (ρ := ρ) htb
    rw [eval_node hwf ρ he]
    simp only [Op.eval, List.map, hc, hav, hbv]
    simp [bvIteEval, Val.asCond, hw]
    cases cv <;> simp

theorem bools_all_false {vs : List Val} {bs : List Bool}
    (h : Val.bools vs = some bs) (hall : bs.all id = false) : ∃ v ∈ vs, v = .bool false := by
  induction vs generalizing bs with
  | nil => simp [Val.bools] at h; subst h; simp at hall
  | cons v rest ih =>
    simp only [Val.bools] at h
    split at h
    · rename_i x xs hx hrest
      simp at h; subst h
      rw [Val.asBool_some_iff] at hx; subst hx
      rw [List.all_cons, Bool.and_eq_false_iff] at hall
      rcases hall with hx | hxs
      · exact ⟨.bool x, by simp, by simp at hx; rw [hx]⟩
      · obtain ⟨v', hv', hvf⟩ := ih hrest hxs
        exact ⟨v', by simp [hv'], hvf⟩
    · simp at h

theorem eval_conj_node_false {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.conj, args⟩) (ρ : Assign) (h : eval pool ρ e = .bool false) :
    ∃ a ∈ args, eval pool ρ a = .bool false := by
  rw [eval_node hwf ρ he] at h
  simp only [Op.eval, boolN] at h
  cases hb : Val.bools (args.toList.map (eval pool ρ)) with
  | none => rw [hb] at h; simp at h
  | some bs =>
    rw [hb] at h
    dsimp only at h
    split at h
    · have h' : bs.all id = false := by simpa using h
      obtain ⟨v, hv, hvf⟩ := bools_all_false hb h'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact ⟨a, by simpa using ha, hvf⟩
    · simp at h

theorem boolNotTy_bool {tys : List Ty} {t : Ty} (h : boolNotTy tys = some t) : t = .bool := by
  unfold boolNotTy at h; split at h <;> simp [tyGuard] at h; exact h.2.symm
theorem eqTy_bool {tys : List Ty} {t : Ty} (h : eqTy tys = some t) : t = .bool := by
  unfold eqTy at h; split at h <;> simp [tyGuard] at h; exact h.2.symm
theorem impliesTy_bool {tys : List Ty} {t : Ty} (h : impliesTy tys = some t) : t = .bool := by
  unfold impliesTy at h; split at h <;> simp [tyGuard] at h; exact h.2.symm
theorem boolNTy_bool {tys : List Ty} {t : Ty} (h : boolNTy tys = some t) : t = .bool := by
  simp [boolNTy, tyGuard] at h; exact h.2.symm
theorem boolIteTy_bool {tys : List Ty} {t : Ty} (h : boolIteTy tys = some t) : t = .bool := by
  unfold boolIteTy at h; split at h <;> simp [tyGuard] at h; exact h.2.symm

/-- Types of `not`, `eq`, `implies`, `xor`, `ite`, `disj`, `conj` nodes are boolean. -/
theorem typeOf_bool_node {pool : Pool} (hwf : WF pool) {e : Nat} {n : Node} (he : pool[e]? = some n)
    (hop : n.op.resultTy = boolNotTy ∨ n.op.resultTy = eqTy ∨ n.op.resultTy = impliesTy ∨
      n.op.resultTy = boolNTy ∨ n.op.resultTy = boolIteTy) :
    typeOf pool e = some .bool := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf e n he).2
  rw [ht]
  rw [typeOf_node hwf he] at ht
  cases hm : mapOpt (typeOf pool) n.args.toList with
  | none => rw [hm] at ht; simp at ht
  | some tys =>
    rw [hm] at ht
    simp only [Option.bind_some] at ht
    congr
    rcases hop with h | h | h | h | h <;> rw [h] at ht
    · exact boolNotTy_bool ht
    · exact eqTy_bool ht
    · exact impliesTy_bool ht
    · exact boolNTy_bool ht
    · exact boolIteTy_bool ht

theorem typeOf_conj_bool {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.conj, args⟩) : typeOf pool e = some .bool :=
  typeOf_bool_node hwf he (by simp [Op.resultTy])
theorem typeOf_disj_bool {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.disj, args⟩) : typeOf pool e = some .bool :=
  typeOf_bool_node hwf he (by simp [Op.resultTy])
theorem typeOf_implies_bool {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.implies, #[a, b]⟩) : typeOf pool e = some .bool :=
  typeOf_bool_node hwf he (by simp [Op.resultTy])
theorem typeOf_eq_bool {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.eq, #[a, b]⟩) : typeOf pool e = some .bool :=
  typeOf_bool_node hwf he (by simp [Op.resultTy])
theorem typeOf_xor_bool {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.boolXor, args⟩) : typeOf pool e = some .bool :=
  typeOf_bool_node hwf he (by simp [Op.resultTy])
theorem typeOf_boolIte_bool {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.boolIte, args⟩) : typeOf pool e = some .bool :=
  typeOf_bool_node hwf he (by simp [Op.resultTy])
theorem typeOf_not_bool {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.boolNot, args⟩) : typeOf pool e = some .bool :=
  typeOf_bool_node hwf he (by simp [Op.resultTy])

theorem node_eq_of_isXor2 {n : Node} {a b : Nat} (h : isXor2Node n = some (a, b)) :
    n = ⟨.boolXor, #[a, b]⟩ := by
  unfold isXor2Node at h
  split at h
  · rename_i args
    obtain ⟨l⟩ := args
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, rest⟩⟩⟩⟩ <;> simp at h
    first
      | (obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (subst h; rfl)
  · simp at h

theorem node_bind_xor2 {p a b : Nat} (h : (st.node p).bind isXor2Node = some (a, b)) :
    st.pool[p]? = some ⟨.boolXor, #[a, b]⟩ := by
  simp only [St.node, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hn'⟩ := h
  rw [hn, node_eq_of_isXor2 hn']

theorem node_eq_of_isBoolIte {n : Node} {c a b : Nat} (h : isBoolIteNode n = some (c, a, b)) :
    n = ⟨.boolIte, #[c, a, b]⟩ := by
  unfold isBoolIteNode at h
  split at h
  · rename_i args
    obtain ⟨l⟩ := args
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, rest⟩⟩⟩⟩ <;> simp at h
    first
      | (obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (subst h; rfl)
  · simp at h

theorem node_bind_boolIte {p c a b : Nat} (h : (st.node p).bind isBoolIteNode = some (c, a, b)) :
    st.pool[p]? = some ⟨.boolIte, #[c, a, b]⟩ := by
  simp only [St.node, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, hn'⟩ := h
  rw [hn, node_eq_of_isBoolIte hn']

/-- Two-push clause builder: `¬x ∨ y`-style clauses. -/
theorem notDisj_entails {x y na d : Nat} {st1 : St} (hinv : Inv base g bi st)
    (hn : mkNot st x = some (st1, na)) (hd : mkDisj st1 #[na, y] = some (st', d))
    (hx : x < st.pool.size) (hy : y < st.pool.size)
    (hc : ∀ ρ, holds st.pool ρ g → eval st.pool ρ x = .bool false ∨ holds st.pool ρ y) :
    Inv base g bi st' ∧ Entails st' g d := by
  have hinv1 := hinv.push hn
  apply mkDisj_entails hinv1 hd
  · intro l hl; simp at hl; rcases hl with rfl | rfl
    · exact (pushNode_size hn).2
    · exact Nat.lt_of_lt_of_le hy (pushNode_size hn).1
  · intro ρ hg
    rw [pushNode_holds hn ρ hinv.goal] at hg
    rcases hc ρ hg with hxf | hyt
    · exact ⟨na, by simp, mkNot_holds hn hinv.tys ρ (by rw [pushNode_eval hn ρ hx]; exact hxf)⟩
    · exact ⟨y, by simp, by rw [pushNode_holds hn ρ hy]; exact hyt⟩

theorem ruleImpliesElim_sound {prems params : List Nat} (h : ruleImpliesElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleImpliesElim at h
  split at h
  · rename_i p
    split at h
    · rename_i a b hab
      split at h
      · rename_i st1 na hna
        have hpn := node_bind_implies hab
        apply notDisj_entails hinv hna h (child_lt hinv.wf hpn (by simp)) (child_lt hinv.wf hpn (by simp))
        intro ρ hg
        have := premise_entails hp (p := p) (by simp) ρ hg
        obtain ⟨x, y, hx, hy, hr⟩ := eval_implies_node hinv.wf hpn ρ this
        cases x
        · left; exact hx
        · right; simp at hr; unfold holds; rw [hy, ← hr]
      · simp at h
    · simp at h
  · simp at h

theorem ruleNotImpliesElim_sound {prems params : List Nat}
    (h : ruleNotImpliesElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleNotImpliesElim at h
  split at h
  · rename_i p idx
    split at h
    · rename_i q hq
      split at h
      · rename_i a b hab
        have hpn := node_bind_not hq
        have hqn := node_bind_implies hab
        have key : ∀ ρ, holds st.pool ρ g → holds st.pool ρ a ∧ eval st.pool ρ b = .bool false := by
          intro ρ hg
          have hqf := (holds_not_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)
          obtain ⟨x, y, hx, hy, hr⟩ := eval_implies_node hinv.wf hqn ρ hqf
          cases x <;> cases y <;> simp at hr
          exact ⟨hx, hy⟩
        split at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨hinv, child_lt hinv.wf hqn (by simp), fun ρ hg => (key ρ hg).1⟩
        · split at h
          · exact mkNot_entails hinv h (fun ρ hg => (key ρ hg).2) (child_lt hinv.wf hqn (by simp))
          · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- `a = b` on booleans, at the value level. -/
theorem eval_eq_bools {pool : Pool} (hwf : WF pool) {e a b : Nat}
    (he : pool[e]? = some ⟨.eq, #[a, b]⟩) (ρ : Assign) {r x : Bool}
    (h : eval pool ρ e = .bool r) (hx : eval pool ρ a = .bool x) :
    ∃ y, eval pool ρ b = .bool y ∧ r = decide (x = y) := by
  have := eval_eq_node hwf he ρ h
  rw [hx] at this
  exact eqv_bool_left this

theorem equivElimClause_sound {a b form : Nat} (hinv : Inv base g bi st)
    (h : equivElimClause st a b form = some (st', f)) (ha : a < st.pool.size) (hb : b < st.pool.size)
    (hc : ∀ ρ, holds st.pool ρ g → ∀ x y, eval st.pool ρ a = .bool x → eval st.pool ρ b = .bool y → x = y) :
    Inv base g bi st' ∧ Entails st' g f := by
  unfold equivElimClause at h
  split at h
  · split at h
    · rename_i st1 na hna
      apply notDisj_entails hinv hna h ha hb
      intro ρ hg
      have hta := mkNot_arg_bool hna hinv.tys
      rw [typeOf_extend (pushNode_prefix hna) a ha] at hta
      obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
      cases x
      · left; exact hx
      · right; unfold holds
        -- b is boolean because the disjunction type-checked
        have htb : typeOf st'.pool b = some .bool := by
          obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h (pushNode_tysOK hna hinv.tys)
          simp only [Op.resultTy, boolNTy, tyGuard] at ht
          split at ht
          · rename_i hc'
            obtain ⟨y, hy, hfy⟩ := mapOpt_mem hmap (x := b) (by simp)
            rw [hfy]; congr; exact allBool_mem hc'.1 hy
          · simp at ht
        rw [typeOf_extend (pushNode_prefix h) b (Nat.lt_of_lt_of_le hb (pushNode_size hna).1),
            typeOf_extend (pushNode_prefix hna) b hb] at htb
        obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
        rw [hy, hc ρ hg true y hx hy]
    · simp at h
  · split at h
    · split at h
      · rename_i st1 nb hnb
        have hinv1 := hinv.push hnb
        apply mkDisj_entails hinv1 h
        · intro l hl; simp at hl; rcases hl with rfl | rfl
          · exact Nat.lt_of_lt_of_le ha (pushNode_size hnb).1
          · exact (pushNode_size hnb).2
        · intro ρ hg
          rw [pushNode_holds hnb ρ hinv.goal] at hg
          have htb := mkNot_arg_bool hnb hinv.tys
          rw [typeOf_extend (pushNode_prefix hnb) b hb] at htb
          obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
          cases y
          · exact ⟨nb, by simp, mkNot_holds hnb hinv.tys ρ (by rw [pushNode_eval hnb ρ hb]; exact hy)⟩
          · refine ⟨a, by simp, ?_⟩
            rw [pushNode_holds hnb ρ ha]
            have hta : typeOf st'.pool a = some .bool := by
              obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hinv1.tys
              simp only [Op.resultTy, boolNTy, tyGuard] at ht
              split at ht
              · rename_i hc'
                obtain ⟨y', hy', hfy⟩ := mapOpt_mem hmap (x := a) (by simp)
                rw [hfy]; congr; exact allBool_mem hc'.1 hy'
              · simp at ht
            rw [typeOf_extend (pushNode_prefix h) a (Nat.lt_of_lt_of_le ha (pushNode_size hnb).1),
                typeOf_extend (pushNode_prefix hnb) a ha] at hta
            obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
            unfold holds; rw [hx, hc ρ hg x true hx hy]
      · simp at h
    · simp at h

theorem notEquivElimClause_sound {a b form : Nat} (hinv : Inv base g bi st)
    (h : notEquivElimClause st a b form = some (st', f)) (ha : a < st.pool.size) (hb : b < st.pool.size)
    (hc : ∀ ρ, holds st.pool ρ g → ∀ x y, eval st.pool ρ a = .bool x → eval st.pool ρ b = .bool y → x ≠ y) :
    Inv base g bi st' ∧ Entails st' g f := by
  unfold notEquivElimClause at h
  split at h
  · apply mkDisj_entails hinv h
    · intro l hl; simp at hl; rcases hl with rfl | rfl <;> assumption
    · intro ρ hg
      obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hinv.tys
      simp only [Op.resultTy, boolNTy, tyGuard] at ht
      split at ht
      · rename_i hc'
        have hta : typeOf st.pool a = some .bool := by
          obtain ⟨y, hy, hfy⟩ := mapOpt_mem hmap (x := a) (by simp)
          rw [← typeOf_extend (pushNode_prefix h) a ha, hfy]; congr; exact allBool_mem hc'.1 hy
        have htb : typeOf st.pool b = some .bool := by
          obtain ⟨y, hy, hfy⟩ := mapOpt_mem hmap (x := b) (by simp)
          rw [← typeOf_extend (pushNode_prefix h) b hb, hfy]; congr; exact allBool_mem hc'.1 hy
        obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
        obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
        have hne := hc ρ hg x y hx hy
        cases x
        · cases y
          · exact absurd rfl hne
          · exact ⟨b, by simp, hy⟩
        · exact ⟨a, by simp, hx⟩
      · simp at ht
  · split at h
    · split at h
      · rename_i st1 na hna
        split at h
        · rename_i st2 nb hnb
          have hinv1 := hinv.push hna
          have hinv2 := hinv1.push hnb
          apply mkDisj_entails hinv2 h
          · intro l hl; simp at hl; rcases hl with rfl | rfl
            · exact Nat.lt_of_lt_of_le (pushNode_size hna).2 (pushNode_size hnb).1
            · exact (pushNode_size hnb).2
          · intro ρ hg
            rw [pushNode_holds hnb ρ hinv1.goal, pushNode_holds hna ρ hinv.goal] at hg
            have hta := mkNot_arg_bool hna hinv.tys
            rw [typeOf_extend (pushNode_prefix hna) a ha] at hta
            have htb := mkNot_arg_bool hnb hinv1.tys
            rw [typeOf_extend (pushNode_prefix hnb) b (Nat.lt_of_lt_of_le hb (pushNode_size hna).1),
                typeOf_extend (pushNode_prefix hna) b hb] at htb
            obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
            obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
            have hne := hc ρ hg x y hx hy
            have hna' : holds st2.pool ρ na ↔ eval st.pool ρ a = .bool false := by
              rw [holds_not_node hinv2.wf (get_ext (pushNode_extends hnb) (pushNode_get hna)) ρ,
                  eval_ext (pushNode_extends hnb) ρ (Nat.lt_of_lt_of_le ha (pushNode_size hna).1),
                  pushNode_eval hna ρ ha]
            have hnb' : holds st2.pool ρ nb ↔ eval st.pool ρ b = .bool false := by
              rw [holds_not_node hinv2.wf (pushNode_get hnb) ρ,
                  eval_ext (pushNode_extends hnb) ρ (Nat.lt_of_lt_of_le hb (pushNode_size hna).1),
                  pushNode_eval hna ρ hb]
            cases x
            · exact ⟨na, by simp, hna'.mpr hx⟩
            · cases y
              · exact ⟨nb, by simp, hnb'.mpr hy⟩
              · exact absurd rfl hne
        · simp at h
      · simp at h
    · simp at h

theorem ruleEquivElim_sound {prems params : List Nat} (h : ruleEquivElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleEquivElim at h
  split at h
  · rename_i p form
    split at h
    · rename_i a b hab
      have hpn := node_bind_eq hab
      apply equivElimClause_sound hinv h (child_lt hinv.wf hpn (by simp)) (child_lt hinv.wf hpn (by simp))
      intro ρ hg x y hx hy
      have := ((holds_eq_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)).1
      rw [hx, hy] at this; simpa using this
    · simp at h
  · simp at h

theorem ruleNotEquivElim_sound {prems params : List Nat} (h : ruleNotEquivElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleNotEquivElim at h
  split at h
  · rename_i p form
    split at h
    · rename_i q hq
      split at h
      · rename_i a b hab
        have hpn := node_bind_not hq
        have hqn := node_bind_eq hab
        apply notEquivElimClause_sound hinv h (child_lt hinv.wf hqn (by simp)) (child_lt hinv.wf hqn (by simp))
        intro ρ hg x y hx hy
        have hqf := (holds_not_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)
        obtain ⟨y', hy', hr⟩ := eval_eq_bools hinv.wf hqn ρ hqf hx
        rw [hy] at hy'
        have hyy : y = y' := by simpa using hy'
        subst y'
        simpa using hr

      · simp at h
    · simp at h
  · simp at h

theorem ruleXorElim_sound {prems params : List Nat} (h : ruleXorElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleXorElim at h
  split at h
  · rename_i p form
    split at h
    · rename_i a b hab
      have hpn := node_bind_xor2 hab
      apply notEquivElimClause_sound hinv h (child_lt hinv.wf hpn (by simp)) (child_lt hinv.wf hpn (by simp))
      intro ρ hg x y hx hy
      obtain ⟨x', y', hx', hy', hr⟩ := eval_xor2_node hinv.wf hpn ρ (premise_entails hp (p := p) (by simp) ρ hg)
      rw [hx] at hx'; rw [hy] at hy'
      have hxx : x = x' := by simpa using hx'
      have hyy : y = y' := by simpa using hy'
      subst x'; subst y'
      cases x <;> cases y <;> simp at hr ⊢
    · simp at h
  · simp at h

theorem ruleNotXorElim_sound {prems params : List Nat} (h : ruleNotXorElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleNotXorElim at h
  split at h
  · rename_i p lit
    split at h
    · rename_i q hq
      split at h
      · rename_i a b hab
        have hpn := node_bind_not hq
        have hqn := node_bind_xor2 hab
        apply equivElimClause_sound hinv h (child_lt hinv.wf hqn (by simp)) (child_lt hinv.wf hqn (by simp))
        intro ρ hg x y hx hy
        have hqf := (holds_not_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)
        obtain ⟨x', y', hx', hy', hr⟩ := eval_xor2_node hinv.wf hqn ρ hqf
        rw [hx] at hx'; rw [hy] at hy'
        have hxx : x = x' := by simpa using hx'
        have hyy : y = y' := by simpa using hy'
        subst x'; subst y'
        cases x <;> cases y <;> simp at hr ⊢
      · simp at h
    · simp at h
  · simp at h

theorem ruleIteElim_sound {prems params : List Nat} (h : ruleIteElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleIteElim at h
  split at h
  · rename_i p lit
    split at h
    · rename_i c a b hcab
      have hpn := node_bind_boolIte hcab
      have hc' := child_lt hinv.wf hpn (a := c) (by simp)
      have ha' := child_lt hinv.wf hpn (a := a) (by simp)
      have hb' := child_lt hinv.wf hpn (a := b) (by simp)
      have key : ∀ ρ, holds st.pool ρ g → ∃ cv av bv, eval st.pool ρ c = .bool cv ∧ eval st.pool ρ a = .bool av ∧
          eval st.pool ρ b = .bool bv ∧ (if cv then av else bv) = true := by
        intro ρ hg
        obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := eval_boolIte_node hinv.wf hpn ρ (premise_entails hp (p := p) (by simp) ρ hg)
        exact ⟨cv, av, bv, h1, h2, h3, h4.symm⟩
      split at h
      · apply mkDisj_entails hinv h
        · intro l hl; simp at hl; rcases hl with rfl | rfl <;> assumption
        · intro ρ hg
          obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := key ρ hg
          cases cv
          · exact ⟨b, by simp, by unfold holds; rw [h3]; simpa using h4⟩
          · exact ⟨c, by simp, h1⟩
      · split at h
        · split at h
          · rename_i st1 nc hnc
            apply notDisj_entails hinv hnc h hc' ha'
            intro ρ hg
            obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := key ρ hg
            cases cv
            · left; exact h1
            · right; unfold holds; rw [h2]; simpa using h4
          · simp at h
        · simp at h
    · simp at h
  · simp at h

theorem ruleNotIteElim_sound {prems params : List Nat} (h : ruleNotIteElim st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleNotIteElim at h
  split at h
  · rename_i p lit
    split at h
    · rename_i q hq
      split at h
      · rename_i c a b hcab
        have hpn := node_bind_not hq
        have hqn := node_bind_boolIte hcab
        have hc' := child_lt hinv.wf hqn (a := c) (by simp)
        have ha' := child_lt hinv.wf hqn (a := a) (by simp)
        have hb' := child_lt hinv.wf hqn (a := b) (by simp)
        have key : ∀ ρ, holds st.pool ρ g → ∃ cv av bv, eval st.pool ρ c = .bool cv ∧ eval st.pool ρ a = .bool av ∧
            eval st.pool ρ b = .bool bv ∧ (if cv then av else bv) = false := by
          intro ρ hg
          have hqf := (holds_not_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)
          obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := eval_boolIte_node hinv.wf hqn ρ hqf
          exact ⟨cv, av, bv, h1, h2, h3, h4.symm⟩
        split at h
        · split at h
          · rename_i st1 nb hnb
            have hinv1 := hinv.push hnb
            apply mkDisj_entails hinv1 h
            · intro l hl; simp at hl; rcases hl with rfl | rfl
              · exact Nat.lt_of_lt_of_le hc' (pushNode_size hnb).1
              · exact (pushNode_size hnb).2
            · intro ρ hg
              rw [pushNode_holds hnb ρ hinv.goal] at hg
              obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := key ρ hg
              cases cv
              · refine ⟨nb, by simp, mkNot_holds hnb hinv.tys ρ ?_⟩
                rw [pushNode_eval hnb ρ hb', h3]; simpa using h4
              · exact ⟨c, by simp, by rw [pushNode_holds hnb ρ hc']; exact h1⟩
          · simp at h
        · split at h
          · split at h
            · rename_i st1 nc hnc
              split at h
              · rename_i st2 na hna
                have hinv1 := hinv.push hnc
                have hinv2 := hinv1.push hna
                apply mkDisj_entails hinv2 h
                · intro l hl; simp at hl; rcases hl with rfl | rfl
                  · exact Nat.lt_of_lt_of_le (pushNode_size hnc).2 (pushNode_size hna).1
                  · exact (pushNode_size hna).2
                · intro ρ hg
                  rw [pushNode_holds hna ρ hinv1.goal, pushNode_holds hnc ρ hinv.goal] at hg
                  obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := key ρ hg
                  cases cv
                  · refine ⟨nc, by simp, ?_⟩
                    rw [holds_not_node hinv2.wf (get_ext (pushNode_extends hna) (pushNode_get hnc)) ρ,
                        eval_ext (pushNode_extends hna) ρ (Nat.lt_of_lt_of_le hc' (pushNode_size hnc).1),
                        pushNode_eval hnc ρ hc']
                    exact h1
                  · refine ⟨na, by simp, ?_⟩
                    rw [holds_not_node hinv2.wf (pushNode_get hna) ρ,
                        eval_ext (pushNode_extends hna) ρ (Nat.lt_of_lt_of_le ha' (pushNode_size hnc).1),
                        pushNode_eval hnc ρ ha', h2]
                    simpa using h4
              · simp at h
            · simp at h
          · simp at h
      · simp at h
    · simp at h
  · simp at h

/-! ### `mkNots` -/

theorem mkNots_sound {l : List Nat} :
    ∀ {st st' : St} {nl : List Nat}, mkNots st l = some (st', nl) → Inv base g bi st →
    (∀ x ∈ l, x < st.pool.size) →
    Inv base g bi st' ∧ Extends st st' ∧
    (∀ nx ∈ nl, nx < st'.pool.size) ∧
    (∀ x ∈ l, ∃ nx ∈ nl, st'.pool[nx]? = some ⟨.boolNot, #[x]⟩) ∧
    (∀ nx ∈ nl, ∃ x ∈ l, st'.pool[nx]? = some ⟨.boolNot, #[x]⟩) := by
  induction l with
  | nil =>
    intro st st' nl h hinv _
    simp [mkNots] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hinv, Extends.refl st, by simp, by simp, by simp⟩
  | cons a rest ih =>
    intro st st' nl h hinv hl
    unfold mkNots at h
    split at h
    · rename_i st1 na hna
      split at h
      · rename_i st2 nas hrest
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hinv1 := hinv.push hna
        obtain ⟨hinv2, hext, hlt, h1, h2⟩ := ih hrest hinv1 (fun x hx => Nat.lt_of_lt_of_le (hl x (by simp [hx])) (pushNode_size hna).1)
        refine ⟨hinv2, (pushNode_extends hna).trans hext, ?_, ?_, ?_⟩
        · intro nx hnx; simp at hnx; rcases hnx with rfl | hnx
          · exact Nat.lt_of_lt_of_le (pushNode_size hna).2 hext.1
          · exact hlt nx hnx
        · intro x hx; simp at hx; rcases hx with rfl | hx
          · exact ⟨na, by simp, get_ext hext (pushNode_get hna)⟩
          · obtain ⟨nx, hnx, hp⟩ := h1 x hx; exact ⟨nx, by simp [hnx], hp⟩
        · intro nx hnx; simp at hnx; rcases hnx with rfl | hnx
          · exact ⟨a, by simp, get_ext hext (pushNode_get hna)⟩
          · obtain ⟨x, hx, hp⟩ := h2 nx hnx; exact ⟨x, by simp [hx], hp⟩
      · simp at h
    · simp at h

theorem ruleNotAnd_sound {prems params : List Nat} (h : ruleNotAnd st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleNotAnd at h
  split at h
  · rename_i p
    split at h
    · rename_i q hq
      split at h
      · rename_i args hargs
        split at h
        · rename_i st1 nas hnas
          have hpn := node_bind_not hq
          have hqn := node_bind_conj hargs
          obtain ⟨hinv1, hext, hlt, h1, h2⟩ := mkNots_sound hnas hinv (fun x hx => child_lt hinv.wf hqn (by simpa using hx))
          apply mkDisj_entails hinv1 h (fun l hl => hlt l (by simpa using hl))
          intro ρ hg
          rw [holds_ext hext ρ hinv.goal] at hg
          have hqf := (holds_not_node hinv.wf hpn ρ).mp (premise_entails hp (p := p) (by simp) ρ hg)
          obtain ⟨a, ha, haf⟩ := eval_conj_node_false hinv.wf hqn ρ hqf
          obtain ⟨na, hna, hnap⟩ := h1 a (by simpa using ha)
          refine ⟨na, by simpa using hna, ?_⟩
          rw [holds_not_node hinv1.wf hnap ρ, eval_ext hext ρ (child_lt hinv.wf hqn ha)]
          exact haf
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-! ### CNF tautologies -/

theorem ruleCnfAndPos_sound {ei : EI} {prems params : List Nat} (h : ruleCnfAndPos ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfAndPos at h
  split at h
  · rename_i pe lit
    split at h
    · rename_i e _
      split at h
      · rename_i args hargs
        split at h
        · rename_i a hak
          split at h
          · rename_i st1 ne hne
            have hen := node_bind_conj hargs
            have hmem : a ∈ args := by
              rw [Array.getElem?_eq_some_iff] at hak; obtain ⟨hk, rfl⟩ := hak; exact Array.getElem_mem hk
            apply notDisj_entails hinv hne h (idx_lt_of_get hen) (child_lt hinv.wf hen hmem)
            intro ρ _
            obtain ⟨b, hb⟩ := eval_bool (ρ := ρ) (typeOf_conj_bool hinv.wf hen)
            cases b
            · left; exact hb
            · right; exact holds_conj_node hinv.wf hen ρ hb a hmem
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfAndNeg_sound {ei : EI} {prems params : List Nat} (h : ruleCnfAndNeg ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfAndNeg at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i args hargs
        split at h
        · rename_i st1 nas hnas
          have hen := node_bind_conj hargs
          obtain ⟨hinv1, hext, hlt, h1, h2⟩ := mkNots_sound hnas hinv (fun x hx => child_lt hinv.wf hen (by simpa using hx))
          apply mkDisj_entails hinv1 h
          · intro l hl; simp at hl; rcases hl with rfl | hl
            · exact Nat.lt_of_lt_of_le (idx_lt_of_get hen) hext.1
            · exact hlt l hl
          · intro ρ _
            obtain ⟨b, hb⟩ := eval_bool (ρ := ρ) (typeOf_conj_bool hinv.wf hen)
            cases b
            · obtain ⟨a, ha, haf⟩ := eval_conj_node_false hinv.wf hen ρ hb
              obtain ⟨na, hna, hnap⟩ := h1 a (by simpa using ha)
              refine ⟨na, by simp [hna], ?_⟩
              rw [holds_not_node hinv1.wf hnap ρ, eval_ext hext ρ (child_lt hinv.wf hen ha)]
              exact haf
            · exact ⟨e, by simp, by rw [holds_ext hext ρ (idx_lt_of_get hen)]; exact hb⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfOrPos_sound {ei : EI} {prems params : List Nat} (h : ruleCnfOrPos ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfOrPos at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i args hargs
        split at h
        · rename_i st1 ne hne
          have hen := node_bind_disj hargs
          have hinv1 := hinv.push hne
          apply mkDisj_entails hinv1 h
          · intro l hl; simp at hl; rcases hl with rfl | hl
            · exact (pushNode_size hne).2
            · exact Nat.lt_of_lt_of_le (child_lt hinv.wf hen hl) (pushNode_size hne).1
          · intro ρ _
            obtain ⟨b, hb⟩ := eval_bool (ρ := ρ) (typeOf_disj_bool hinv.wf hen)
            cases b
            · exact ⟨ne, by simp, mkNot_holds hne hinv.tys ρ (by rw [pushNode_eval hne ρ (idx_lt_of_get hen)]; exact hb)⟩
            · obtain ⟨a, ha, hat⟩ := holds_disj_elim hinv.wf hen ρ hb
              exact ⟨a, by simp [ha], by rw [pushNode_holds hne ρ (child_lt hinv.wf hen ha)]; exact hat⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfOrNeg_sound {ei : EI} {prems params : List Nat} (h : ruleCnfOrNeg ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfOrNeg at h
  split at h
  · rename_i pe lit
    split at h
    · rename_i e _
      split at h
      · rename_i args hargs
        split at h
        · rename_i a hak
          split at h
          · rename_i st1 na hna
            have hen := node_bind_disj hargs
            have hmem : a ∈ args := by
              rw [Array.getElem?_eq_some_iff] at hak; obtain ⟨hk, rfl⟩ := hak; exact Array.getElem_mem hk
            have hinv1 := hinv.push hna
            apply mkDisj_entails hinv1 h
            · intro l hl; simp at hl; rcases hl with rfl | rfl
              · exact Nat.lt_of_lt_of_le (idx_lt_of_get hen) (pushNode_size hna).1
              · exact (pushNode_size hna).2
            · intro ρ _
              have hta := boolN_args_bool hinv.wf (Or.inl hen) a hmem
              obtain ⟨b, hb⟩ := eval_bool (ρ := ρ) hta
              cases b
              · exact ⟨na, by simp, mkNot_holds hna hinv.tys ρ (by rw [pushNode_eval hna ρ (child_lt hinv.wf hen hmem)]; exact hb)⟩
              · refine ⟨e, by simp, ?_⟩
                rw [pushNode_holds hna ρ (idx_lt_of_get hen)]
                exact holds_disj_intro hinv.wf hen ρ (by
                  have h2 := (hinv.wf e _ hen).2
                  rw [typeOf_node hinv.wf hen] at h2
                  cases hm : mapOpt (typeOf st.pool) args.toList with
                  | none => rw [hm] at h2; simp at h2
                  | some tys =>
                    rw [hm] at h2; simp [Op.resultTy, boolNTy, tyGuard] at h2
                    have := mapOpt_length hm; simp at this; omega) ⟨a, hmem, hb⟩
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfImpliesPos_sound {ei : EI} {prems params : List Nat} (h : ruleCnfImpliesPos ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfImpliesPos at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        split at h
        · rename_i st1 ne hne
          split at h
          · rename_i st2 na hna
            have hen := node_bind_implies hab
            have ha' := child_lt hinv.wf hen (a := a) (by simp)
            have hb' := child_lt hinv.wf hen (a := b) (by simp)
            have hinv1 := hinv.push hne
            have hinv2 := hinv1.push hna
            apply mkDisj_entails hinv2 h
            · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
              · exact Nat.lt_of_lt_of_le (pushNode_size hne).2 (pushNode_size hna).1
              · exact (pushNode_size hna).2
              · exact Nat.lt_of_lt_of_le hb' (Nat.le_trans (pushNode_size hne).1 (pushNode_size hna).1)
            · intro ρ _
              obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_implies_bool hinv.wf hen)
              have hext : Extends st st2 := (pushNode_extends hne).trans (pushNode_extends hna)
              cases r
              · refine ⟨ne, by simp, ?_⟩
                rw [holds_not_node hinv2.wf (get_ext (pushNode_extends hna) (pushNode_get hne)) ρ,
                    eval_ext hext ρ (idx_lt_of_get hen)]
                exact hr
              · obtain ⟨x, y, hx, hy, hxy⟩ := eval_implies_node hinv.wf hen ρ hr
                cases x
                · refine ⟨na, by simp, ?_⟩
                  rw [holds_not_node hinv2.wf (pushNode_get hna) ρ, eval_ext hext ρ ha']
                  exact hx
                · refine ⟨b, by simp, ?_⟩
                  rw [holds_ext hext ρ hb']
                  unfold holds; rw [hy]; simpa using hxy.symm
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfImpliesNeg_sound {ei : EI} {prems params : List Nat} (h : ruleCnfImpliesNeg ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfImpliesNeg at h
  split at h
  · rename_i pe lit
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        have hen := node_bind_implies hab
        have ha' := child_lt hinv.wf hen (a := a) (by simp)
        have hb' := child_lt hinv.wf hen (a := b) (by simp)
        split at h
        · apply mkDisj_entails hinv h
          · intro l hl; simp at hl; rcases hl with rfl | rfl
            · exact idx_lt_of_get hen
            · exact ha'
          · intro ρ _
            obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_implies_bool hinv.wf hen)
            cases r
            · obtain ⟨x, y, hx, hy, hxy⟩ := eval_implies_node hinv.wf hen ρ hr
              cases x <;> simp at hxy
              exact ⟨a, by simp, hx⟩
            · exact ⟨e, by simp, hr⟩
        · split at h
          · split at h
            · rename_i st1 nb hnb
              have hinv1 := hinv.push hnb
              apply mkDisj_entails hinv1 h
              · intro l hl; simp at hl; rcases hl with rfl | rfl
                · exact Nat.lt_of_lt_of_le (idx_lt_of_get hen) (pushNode_size hnb).1
                · exact (pushNode_size hnb).2
              · intro ρ _
                obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_implies_bool hinv.wf hen)
                cases r
                · obtain ⟨x, y, hx, hy, hxy⟩ := eval_implies_node hinv.wf hen ρ hr
                  cases x <;> cases y <;> simp at hxy
                  exact ⟨nb, by simp, mkNot_holds hnb hinv.tys ρ (by rw [pushNode_eval hnb ρ hb']; exact hy)⟩
                · exact ⟨e, by simp, by rw [pushNode_holds hnb ρ (idx_lt_of_get hen)]; exact hr⟩
            · simp at h
          · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- Three-literal clause with a head `h` (either `e` or `¬e`), for the
equivalence and xor CNF rules. -/
theorem cnfPosClause_sound {e a b form : Nat} {negE : Bool} (hinv : Inv base g bi st)
    (h : cnfPosClause st e a b form negE = some (st', f))
    (he : e < st.pool.size) (ha : a < st.pool.size) (hb : b < st.pool.size)
    (hc : ∀ ρ, ∀ x y : Bool, eval st.pool ρ a = .bool x → eval st.pool ρ b = .bool y →
      (∃ r, eval st.pool ρ e = .bool r ∧ ((negE ∧ r = false) ∨ (¬negE ∧ r = true))) ∨
      (form = 0 → x = false ∨ y = true) ∧ (form = 1 → x = true ∨ y = false)) :
    Inv base g bi st' ∧ Entails st' g f := by
  unfold cnfPosClause at h
  -- head
  have hhead : ∀ {st1 : St} {hd : Nat}, headOf st e negE = some (st1, hd) →
      Inv base g bi st1 ∧ Extends st st1 ∧ hd < st1.pool.size ∧
      ∀ ρ, (∃ r, eval st.pool ρ e = .bool r ∧ ((negE ∧ r = false) ∨ (¬negE ∧ r = true))) → holds st1.pool ρ hd := by
    intro st1 hd hh
    unfold headOf at hh
    cases negE
    · simp at hh; obtain ⟨rfl, rfl⟩ := hh
      refine ⟨hinv, Extends.refl _, he, ?_⟩
      intro ρ ⟨r, hr, hr'⟩; simp at hr'; subst hr'; exact hr
    · simp at hh
      refine ⟨hinv.push hh, pushNode_extends hh, (pushNode_size hh).2, ?_⟩
      intro ρ ⟨r, hr, hr'⟩; simp at hr'; subst hr'
      exact mkNot_holds hh hinv.tys ρ (by rw [pushNode_eval hh ρ he]; exact hr)
  split at h
  · rename_i st1 hd hh
    obtain ⟨hinv1, hext1, hhd, hhold⟩ := hhead hh
    split at h
    · split at h
      · rename_i st2 na hna
        have hinv2 := hinv1.push hna
        apply mkDisj_entails hinv2 h
        · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
          · exact Nat.lt_of_lt_of_le hhd (pushNode_size hna).1
          · exact (pushNode_size hna).2
          · exact Nat.lt_of_lt_of_le hb (Nat.le_trans hext1.1 (pushNode_size hna).1)
        · intro ρ _
          have hta := mkNot_arg_bool hna hinv1.tys
          rw [typeOf_extend (pushNode_prefix hna) a (Nat.lt_of_lt_of_le ha hext1.1), typeOf_extend hext1.2 a ha] at hta
          obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
          have htb : typeOf st'.pool b = some .bool := by
            obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hinv2.tys
            simp only [Op.resultTy, boolNTy, tyGuard] at ht
            split at ht
            · rename_i hc'
              obtain ⟨y, hy, hfy⟩ := mapOpt_mem hmap (x := b) (by simp)
              rw [hfy]; congr; exact allBool_mem hc'.1 hy
            · simp at ht
          have hext2 : Extends st st2 := hext1.trans (pushNode_extends hna)
          rw [typeOf_extend (pushNode_prefix h) b (Nat.lt_of_lt_of_le hb hext2.1), typeOf_extend hext2.2 b hb] at htb
          obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
          rcases hc ρ x y hx hy with hh' | ⟨h0, _⟩
          · exact ⟨hd, by simp, by rw [holds_ext (pushNode_extends hna) ρ hhd]; exact hhold ρ hh'⟩
          · rcases h0 (by assumption) with rfl | rfl
            · exact ⟨na, by simp, mkNot_holds hna hinv1.tys ρ (by rw [pushNode_eval hna ρ (Nat.lt_of_lt_of_le ha hext1.1), eval_ext hext1 ρ ha]; exact hx)⟩
            · exact ⟨b, by simp, by rw [holds_ext hext2 ρ hb]; unfold holds; exact hy⟩
      · simp at h
    · split at h
      · split at h
        · rename_i st2 nb hnb
          have hinv2 := hinv1.push hnb
          apply mkDisj_entails hinv2 h
          · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
            · exact Nat.lt_of_lt_of_le hhd (pushNode_size hnb).1
            · exact Nat.lt_of_lt_of_le ha (Nat.le_trans hext1.1 (pushNode_size hnb).1)
            · exact (pushNode_size hnb).2
          · intro ρ _
            have htb := mkNot_arg_bool hnb hinv1.tys
            rw [typeOf_extend (pushNode_prefix hnb) b (Nat.lt_of_lt_of_le hb hext1.1), typeOf_extend hext1.2 b hb] at htb
            obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
            have hta : typeOf st'.pool a = some .bool := by
              obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hinv2.tys
              simp only [Op.resultTy, boolNTy, tyGuard] at ht
              split at ht
              · rename_i hc'
                obtain ⟨y', hy', hfy⟩ := mapOpt_mem hmap (x := a) (by simp)
                rw [hfy]; congr; exact allBool_mem hc'.1 hy'
              · simp at ht
            have hext2 : Extends st st2 := hext1.trans (pushNode_extends hnb)
            rw [typeOf_extend (pushNode_prefix h) a (Nat.lt_of_lt_of_le ha hext2.1), typeOf_extend hext2.2 a ha] at hta
            obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
            rcases hc ρ x y hx hy with hh' | ⟨_, h1⟩
            · exact ⟨hd, by simp, by rw [holds_ext (pushNode_extends hnb) ρ hhd]; exact hhold ρ hh'⟩
            · rcases h1 (by assumption) with rfl | rfl
              · exact ⟨a, by simp, by rw [holds_ext hext2 ρ ha]; unfold holds; exact hx⟩
              · exact ⟨nb, by simp, mkNot_holds hnb hinv1.tys ρ (by rw [pushNode_eval hnb ρ (Nat.lt_of_lt_of_le hb hext1.1), eval_ext hext1 ρ hb]; exact hy)⟩
        · simp at h
      · simp at h
  · simp at h

theorem cnfNegClause_sound {e a b lit : Nat} {negE : Bool} (hinv : Inv base g bi st)
    (h : cnfNegClause st e a b lit negE = some (st', f))
    (he : e < st.pool.size) (ha : a < st.pool.size) (hb : b < st.pool.size)
    (hc : ∀ ρ, ∀ x y : Bool, eval st.pool ρ a = .bool x → eval st.pool ρ b = .bool y →
      (∃ r, eval st.pool ρ e = .bool r ∧ ((negE ∧ r = false) ∨ (¬negE ∧ r = true))) ∨
      (lit = 0 → x = true ∨ y = true) ∧ (lit = 1 → x = false ∨ y = false)) :
    Inv base g bi st' ∧ Entails st' g f := by
  unfold cnfNegClause at h
  have hhead : ∀ {st1 : St} {hd : Nat}, headOf st e negE = some (st1, hd) →
      Inv base g bi st1 ∧ Extends st st1 ∧ hd < st1.pool.size ∧
      ∀ ρ, (∃ r, eval st.pool ρ e = .bool r ∧ ((negE ∧ r = false) ∨ (¬negE ∧ r = true))) → holds st1.pool ρ hd := by
    intro st1 hd hh
    unfold headOf at hh
    cases negE
    · simp at hh; obtain ⟨rfl, rfl⟩ := hh
      refine ⟨hinv, Extends.refl _, he, ?_⟩
      intro ρ ⟨r, hr, hr'⟩; simp at hr'; subst hr'; exact hr
    · simp at hh
      refine ⟨hinv.push hh, pushNode_extends hh, (pushNode_size hh).2, ?_⟩
      intro ρ ⟨r, hr, hr'⟩; simp at hr'; subst hr'
      exact mkNot_holds hh hinv.tys ρ (by rw [pushNode_eval hh ρ he]; exact hr)
  split at h
  · rename_i st1 hd hh
    obtain ⟨hinv1, hext1, hhd, hhold⟩ := hhead hh
    split at h
    · apply mkDisj_entails hinv1 h
      · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
        · exact hhd
        · exact Nat.lt_of_lt_of_le ha hext1.1
        · exact Nat.lt_of_lt_of_le hb hext1.1
      · intro ρ _
        obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys h hinv1.tys
        simp only [Op.resultTy, boolNTy, tyGuard] at ht
        split at ht
        · rename_i hc'
          have hta : typeOf st.pool a = some .bool := by
            obtain ⟨y, hy, hfy⟩ := mapOpt_mem hmap (x := a) (by simp)
            rw [← typeOf_extend hext1.2 a ha, ← typeOf_extend (pushNode_prefix h) a (Nat.lt_of_lt_of_le ha hext1.1), hfy]
            congr; exact allBool_mem hc'.1 hy
          have htb : typeOf st.pool b = some .bool := by
            obtain ⟨y, hy, hfy⟩ := mapOpt_mem hmap (x := b) (by simp)
            rw [← typeOf_extend hext1.2 b hb, ← typeOf_extend (pushNode_prefix h) b (Nat.lt_of_lt_of_le hb hext1.1), hfy]
            congr; exact allBool_mem hc'.1 hy
          obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
          obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
          rcases hc ρ x y hx hy with hh' | ⟨h0, _⟩
          · exact ⟨hd, by simp, hhold ρ hh'⟩
          · rcases h0 (by assumption) with rfl | rfl
            · exact ⟨a, by simp, by rw [holds_ext hext1 ρ ha]; exact hx⟩
            · exact ⟨b, by simp, by rw [holds_ext hext1 ρ hb]; exact hy⟩
        · simp at ht
    · split at h
      · split at h
        · rename_i st2 na hna
          split at h
          · rename_i st3 nb hnb
            have hinv2 := hinv1.push hna
            have hinv3 := hinv2.push hnb
            have hext2 : Extends st st2 := hext1.trans (pushNode_extends hna)
            have hext3 : Extends st st3 := hext2.trans (pushNode_extends hnb)
            apply mkDisj_entails hinv3 h
            · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
              · exact Nat.lt_of_lt_of_le hhd (Nat.le_trans (pushNode_size hna).1 (pushNode_size hnb).1)
              · exact Nat.lt_of_lt_of_le (pushNode_size hna).2 (pushNode_size hnb).1
              · exact (pushNode_size hnb).2
            · intro ρ _
              have hta := mkNot_arg_bool hna hinv1.tys
              rw [typeOf_extend (pushNode_prefix hna) a (Nat.lt_of_lt_of_le ha hext1.1), typeOf_extend hext1.2 a ha] at hta
              have htb := mkNot_arg_bool hnb hinv2.tys
              rw [typeOf_extend (pushNode_prefix hnb) b (Nat.lt_of_lt_of_le hb hext2.1), typeOf_extend hext2.2 b hb] at htb
              obtain ⟨x, hx⟩ := eval_bool (ρ := ρ) hta
              obtain ⟨y, hy⟩ := eval_bool (ρ := ρ) htb
              rcases hc ρ x y hx hy with hh' | ⟨_, h1⟩
              · exact ⟨hd, by simp, by rw [holds_ext ((pushNode_extends hna).trans (pushNode_extends hnb)) ρ hhd]; exact hhold ρ hh'⟩
              · rcases h1 (by assumption) with rfl | rfl
                · refine ⟨na, by simp, ?_⟩
                  rw [holds_not_node hinv3.wf (get_ext (pushNode_extends hnb) (pushNode_get hna)) ρ, eval_ext hext3 ρ ha]
                  exact hx
                · refine ⟨nb, by simp, ?_⟩
                  rw [holds_not_node hinv3.wf (pushNode_get hnb) ρ, eval_ext hext3 ρ hb]
                  exact hy
          · simp at h
        · simp at h
      · simp at h
  · simp at h

theorem ruleCnfEquivPos_sound {ei : EI} {prems params : List Nat} (h : ruleCnfEquivPos ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfEquivPos at h
  split at h
  · rename_i pe form
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        have hen := node_bind_eq hab
        apply cnfPosClause_sound hinv h (idx_lt_of_get hen) (child_lt hinv.wf hen (by simp)) (child_lt hinv.wf hen (by simp))
        intro ρ x y hx hy
        obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_eq_bool hinv.wf hen)
        cases r
        · left; exact ⟨false, hr, Or.inl ⟨rfl, rfl⟩⟩
        · right
          obtain ⟨y', hy', hxy⟩ := eval_eq_bools hinv.wf hen ρ hr hx
          rw [hy] at hy'
          have hyy : y = y' := by simpa using hy'
          subst y'
          simp at hxy; subst y
          cases x <;> simp
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfEquivNeg_sound {ei : EI} {prems params : List Nat} (h : ruleCnfEquivNeg ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfEquivNeg at h
  split at h
  · rename_i pe lit
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        have hen := node_bind_eq hab
        apply cnfNegClause_sound hinv h (idx_lt_of_get hen) (child_lt hinv.wf hen (by simp)) (child_lt hinv.wf hen (by simp))
        intro ρ x y hx hy
        obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_eq_bool hinv.wf hen)
        cases r
        · right
          obtain ⟨y', hy', hxy⟩ := eval_eq_bools hinv.wf hen ρ hr hx
          rw [hy] at hy'
          have hyy : y = y' := by simpa using hy'
          subst y'
          simp at hxy
          cases x <;> cases y <;> simp at hxy ⊢
        · left; exact ⟨true, hr, Or.inr ⟨by simp, rfl⟩⟩
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfXorPos_sound {ei : EI} {prems params : List Nat} (h : ruleCnfXorPos ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfXorPos at h
  split at h
  · rename_i pe lit
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        have hen := node_bind_xor2 hab
        apply cnfNegClause_sound hinv h (idx_lt_of_get hen) (child_lt hinv.wf hen (by simp)) (child_lt hinv.wf hen (by simp))
        intro ρ x y hx hy
        obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_xor_bool hinv.wf hen)
        cases r
        · left; exact ⟨false, hr, Or.inl ⟨rfl, rfl⟩⟩
        · right
          obtain ⟨x', y', hx', hy', hxy⟩ := eval_xor2_node hinv.wf hen ρ hr
          rw [hx] at hx'; rw [hy] at hy'
          have hxx : x = x' := by simpa using hx'
          have hyy : y = y' := by simpa using hy'
          subst x'; subst y'
          cases x <;> cases y <;> simp at hxy ⊢
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfXorNeg_sound {ei : EI} {prems params : List Nat} (h : ruleCnfXorNeg ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfXorNeg at h
  split at h
  · rename_i pe form
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        have hen := node_bind_xor2 hab
        apply cnfPosClause_sound hinv h (idx_lt_of_get hen) (child_lt hinv.wf hen (by simp)) (child_lt hinv.wf hen (by simp))
        intro ρ x y hx hy
        obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_xor_bool hinv.wf hen)
        cases r
        · right
          obtain ⟨x', y', hx', hy', hxy⟩ := eval_xor2_node hinv.wf hen ρ hr
          rw [hx] at hx'; rw [hy] at hy'
          have hxx : x = x' := by simpa using hx'
          have hyy : y = y' := by simpa using hy'
          subst x'; subst y'
          cases x <;> cases y <;> simp at hxy ⊢
        · left; exact ⟨true, hr, Or.inr ⟨by simp, rfl⟩⟩
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfItePos_sound {ei : EI} {prems params : List Nat} (h : ruleCnfItePos ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfItePos at h
  split at h
  · rename_i pe lit
    split at h
    · rename_i e _
      split at h
      · rename_i c a b hcab
        have hen := node_bind_boolIte hcab
        have hc' := child_lt hinv.wf hen (a := c) (by simp)
        have ha' := child_lt hinv.wf hen (a := a) (by simp)
        have hb' := child_lt hinv.wf hen (a := b) (by simp)
        have key : ∀ ρ, (eval st.pool ρ e = .bool false) ∨ ∃ cv av bv, eval st.pool ρ c = .bool cv ∧
            eval st.pool ρ a = .bool av ∧ eval st.pool ρ b = .bool bv ∧ (if cv then av else bv) = true := by
          intro ρ
          obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_boolIte_bool hinv.wf hen)
          cases r
          · exact Or.inl hr
          · obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := eval_boolIte_node hinv.wf hen ρ hr
            exact Or.inr ⟨cv, av, bv, h1, h2, h3, h4.symm⟩
        split at h
        · rename_i st1 ne hne
          have hinv1 := hinv.push hne
          have hne' : ∀ ρ, eval st.pool ρ e = .bool false → holds st1.pool ρ ne := fun ρ hr =>
            mkNot_holds hne hinv.tys ρ (by rw [pushNode_eval hne ρ (idx_lt_of_get hen)]; exact hr)
          split at h
          · split at h
            · rename_i st2 nc hnc
              have hinv2 := hinv1.push hnc
              have hext : Extends st st2 := (pushNode_extends hne).trans (pushNode_extends hnc)
              apply mkDisj_entails hinv2 h
              · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
                · exact Nat.lt_of_lt_of_le (pushNode_size hne).2 (pushNode_size hnc).1
                · exact (pushNode_size hnc).2
                · exact Nat.lt_of_lt_of_le ha' hext.1
              · intro ρ _
                rcases key ρ with hr | ⟨cv, av, bv, h1, h2, h3, h4⟩
                · exact ⟨ne, by simp, by rw [pushNode_holds hnc ρ (pushNode_size hne).2]; exact hne' ρ hr⟩
                · cases cv
                  · refine ⟨nc, by simp, ?_⟩
                    rw [holds_not_node hinv2.wf (pushNode_get hnc) ρ, eval_ext hext ρ hc']; exact h1
                  · refine ⟨a, by simp, ?_⟩
                    rw [holds_ext hext ρ ha']; unfold holds; rw [h2]; simpa using h4
            · simp at h
          · split at h
            · apply mkDisj_entails hinv1 h
              · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
                · exact (pushNode_size hne).2
                · exact Nat.lt_of_lt_of_le hc' (pushNode_size hne).1
                · exact Nat.lt_of_lt_of_le hb' (pushNode_size hne).1
              · intro ρ _
                rcases key ρ with hr | ⟨cv, av, bv, h1, h2, h3, h4⟩
                · exact ⟨ne, by simp, hne' ρ hr⟩
                · cases cv
                  · exact ⟨b, by simp, by rw [pushNode_holds hne ρ hb']; unfold holds; rw [h3]; simpa using h4⟩
                  · exact ⟨c, by simp, by rw [pushNode_holds hne ρ hc']; exact h1⟩
            · split at h
              · apply mkDisj_entails hinv1 h
                · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
                  · exact (pushNode_size hne).2
                  · exact Nat.lt_of_lt_of_le ha' (pushNode_size hne).1
                  · exact Nat.lt_of_lt_of_le hb' (pushNode_size hne).1
                · intro ρ _
                  rcases key ρ with hr | ⟨cv, av, bv, h1, h2, h3, h4⟩
                  · exact ⟨ne, by simp, hne' ρ hr⟩
                  · cases cv
                    · exact ⟨b, by simp, by rw [pushNode_holds hne ρ hb']; unfold holds; rw [h3]; simpa using h4⟩
                    · exact ⟨a, by simp, by rw [pushNode_holds hne ρ ha']; unfold holds; rw [h2]; simpa using h4⟩
              · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem ruleCnfIteNeg_sound {ei : EI} {prems params : List Nat} (h : ruleCnfIteNeg ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleCnfIteNeg at h
  split at h
  · rename_i pe lit
    split at h
    · rename_i e _
      split at h
      · rename_i c a b hcab
        have hen := node_bind_boolIte hcab
        have he' := idx_lt_of_get hen
        have hc' := child_lt hinv.wf hen (a := c) (by simp)
        have ha' := child_lt hinv.wf hen (a := a) (by simp)
        have hb' := child_lt hinv.wf hen (a := b) (by simp)
        have key : ∀ ρ, (eval st.pool ρ e = .bool true) ∨ ∃ cv av bv, eval st.pool ρ c = .bool cv ∧
            eval st.pool ρ a = .bool av ∧ eval st.pool ρ b = .bool bv ∧ (if cv then av else bv) = false := by
          intro ρ
          obtain ⟨r, hr⟩ := eval_bool (ρ := ρ) (typeOf_boolIte_bool hinv.wf hen)
          cases r
          · obtain ⟨cv, av, bv, h1, h2, h3, h4⟩ := eval_boolIte_node hinv.wf hen ρ hr
            exact Or.inr ⟨cv, av, bv, h1, h2, h3, h4.symm⟩
          · exact Or.inl hr
        split at h
        · split at h
          · rename_i st1 nc hnc
            split at h
            · rename_i st2 na hna
              have hinv1 := hinv.push hnc
              have hinv2 := hinv1.push hna
              have hext : Extends st st2 := (pushNode_extends hnc).trans (pushNode_extends hna)
              apply mkDisj_entails hinv2 h
              · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
                · exact Nat.lt_of_lt_of_le he' hext.1
                · exact Nat.lt_of_lt_of_le (pushNode_size hnc).2 (pushNode_size hna).1
                · exact (pushNode_size hna).2
              · intro ρ _
                rcases key ρ with hr | ⟨cv, av, bv, h1, h2, h3, h4⟩
                · exact ⟨e, by simp, by rw [holds_ext hext ρ he']; exact hr⟩
                · cases cv
                  · refine ⟨nc, by simp, ?_⟩
                    rw [holds_not_node hinv2.wf (get_ext (pushNode_extends hna) (pushNode_get hnc)) ρ, eval_ext hext ρ hc']
                    exact h1
                  · refine ⟨na, by simp, ?_⟩
                    rw [holds_not_node hinv2.wf (pushNode_get hna) ρ, eval_ext hext ρ ha', h2]; simpa using h4
            · simp at h
          · simp at h
        · split at h
          · split at h
            · rename_i st1 nb hnb
              have hinv1 := hinv.push hnb
              apply mkDisj_entails hinv1 h
              · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
                · exact Nat.lt_of_lt_of_le he' (pushNode_size hnb).1
                · exact Nat.lt_of_lt_of_le hc' (pushNode_size hnb).1
                · exact (pushNode_size hnb).2
              · intro ρ _
                rcases key ρ with hr | ⟨cv, av, bv, h1, h2, h3, h4⟩
                · exact ⟨e, by simp, by rw [pushNode_holds hnb ρ he']; exact hr⟩
                · cases cv
                  · exact ⟨nb, by simp, mkNot_holds hnb hinv.tys ρ (by rw [pushNode_eval hnb ρ hb', h3]; simpa using h4)⟩
                  · exact ⟨c, by simp, by rw [pushNode_holds hnb ρ hc']; exact h1⟩
            · simp at h
          · split at h
            · split at h
              · rename_i st1 na hna
                split at h
                · rename_i st2 nb hnb
                  have hinv1 := hinv.push hna
                  have hinv2 := hinv1.push hnb
                  have hext : Extends st st2 := (pushNode_extends hna).trans (pushNode_extends hnb)
                  apply mkDisj_entails hinv2 h
                  · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl
                    · exact Nat.lt_of_lt_of_le he' hext.1
                    · exact Nat.lt_of_lt_of_le (pushNode_size hna).2 (pushNode_size hnb).1
                    · exact (pushNode_size hnb).2
                  · intro ρ _
                    rcases key ρ with hr | ⟨cv, av, bv, h1, h2, h3, h4⟩
                    · exact ⟨e, by simp, by rw [holds_ext hext ρ he']; exact hr⟩
                    · cases cv
                      · refine ⟨nb, by simp, ?_⟩
                        rw [holds_not_node hinv2.wf (pushNode_get hnb) ρ, eval_ext hext ρ hb', h3]; simpa using h4
                      · refine ⟨na, by simp, ?_⟩
                        rw [holds_not_node hinv2.wf (get_ext (pushNode_extends hnb) (pushNode_get hna)) ρ, eval_ext hext ρ ha', h2]
                        simpa using h4
                · simp at h
              · simp at h
            · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem iteEqBody_sound {e c a b : Nat} {op : Op} (hinv : Inv base g bi st)
    (hmk : st.pool[e]? = some ⟨op, #[c, a, b]⟩) (hop : op = .boolIte ∨ ∃ w, op = .bvIte w)
    (hh : iteEqBody st e c a b = some (st', f)) : Inv base g bi st' ∧ Entails st' g f := by
  unfold iteEqBody at hh
  split at hh
  · rename_i st1 e1 he1
    split at hh
    · rename_i st2 e2 he2
      have he' := idx_lt_of_get hmk
      have hc' : c < st.pool.size := child_lt hinv.wf hmk (by simp)
      have ha' : a < st.pool.size := child_lt hinv.wf hmk (by simp)
      have hb' : b < st.pool.size := child_lt hinv.wf hmk (by simp)
      have hinv1 := hinv.push he1
      have hinv2 := hinv1.push he2
      have hinv3 := hinv2.push hh
      have hext2 : Extends st st2 := (pushNode_extends he1).trans (pushNode_extends he2)
      have hext3 : Extends st st' := hext2.trans (pushNode_extends hh)
      refine ⟨hinv3, (pushNode_size hh).2, ?_⟩
      intro ρ _
      have hmk3 : st'.pool[e]? = some ⟨op, #[c, a, b]⟩ := get_ext hext3 hmk
      -- condition is boolean: the outer ite type-checked
      have hcb : typeOf st'.pool c = some .bool := by
        obtain ⟨argTys, t, hmap, ht⟩ := pushNode_argTys hh hinv2.tys
        simp only [mapOpt] at hmap
        cases h0 : typeOf st'.pool c <;> rw [h0] at hmap
        · simp at hmap
        · cases h1 : typeOf st'.pool e1 <;> rw [h1] at hmap <;> cases h2 : typeOf st'.pool e2 <;> rw [h2] at hmap <;>
            simp at hmap
          subst hmap
          simp [Op.resultTy, boolIteTy, tyGuard] at ht
          rw [ht.1.1]
      obtain ⟨cv, hcv⟩ := eval_bool (ρ := ρ) hcb
      have hsel : eval st'.pool ρ e = if cv then eval st'.pool ρ a else eval st'.pool ρ b := by
        apply eval_ite_sel hinv3.wf _ ρ hcv
        rcases hop with hop | ⟨w, hop⟩
        · left; rw [hmk3, hop]
        · right; exact ⟨w, by rw [hmk3, hop]⟩
      -- the scalar type of e
      have hescalar : ∃ t, (eval st'.pool ρ e).ty = some t ∧ t.isScalar = true := by
        rw [eval_ty]
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hinv3.wf e _ hmk3).2
        refine ⟨t, ht, ?_⟩
        rw [typeOf_node hinv3.wf hmk3] at ht
        simp only at ht
        cases hm : mapOpt (typeOf st'.pool) [c, a, b] with
        | none => rw [hm] at ht; cases ht
        | some tys =>
          rw [hm] at ht
          simp only [Option.bind_some] at ht
          rcases hop with hop | ⟨w, hop⟩ <;> subst hop
          · have := boolIteTy_bool (tys := tys) (t := t) (by simpa [Op.resultTy] using ht)
            rw [this]; rfl
          · simp only [Op.resultTy, bvIteTy] at ht
            split at ht <;> simp [tyGuard] at ht
            rw [← ht.2]; rfl
      unfold holds
      rw [eval_node hinv3.wf ρ (pushNode_get hh)]
      simp only [Op.eval, List.map, hcv, boolIteEval]
      have he1' : st'.pool[e1]? = some ⟨.eq, #[e, a]⟩ :=
        get_ext ((pushNode_extends he2).trans (pushNode_extends hh)) (pushNode_get he1)
      have he2' : st'.pool[e2]? = some ⟨.eq, #[e, b]⟩ := get_ext (pushNode_extends hh) (pushNode_get he2)
      cases cv
      · have : holds st'.pool ρ e2 := by
          rw [holds_eq_node hinv3.wf he2' ρ]
          exact ⟨by rw [hsel]; simp, hescalar⟩
        obtain ⟨b1, hb1⟩ := eval_bool (ρ := ρ) (typeOf_eq_bool hinv3.wf he1')
        unfold holds at this; rw [this, hb1]; simp
      · have : holds st'.pool ρ e1 := by
          rw [holds_eq_node hinv3.wf he1' ρ]
          exact ⟨by rw [hsel]; simp, hescalar⟩
        obtain ⟨b2, hb2⟩ := eval_bool (ρ := ρ) (typeOf_eq_bool hinv3.wf he2')
        unfold holds at this; rw [this, hb2]; simp
    · simp at hh
  · simp at hh

theorem three_eq {args : Array Nat} {c a b : Nat} (h : three args = some (c, a, b)) : args = #[c, a, b] := by
  unfold three at h
  split at h
  · rename_i c' a' b' h0 h1 h2
    split at h
    · rename_i hs
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      rw [Array.getElem?_eq_some_iff] at h0 h1 h2
      obtain ⟨_, h0⟩ := h0; obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
      apply Array.ext
      · simp [hs]
      · intro i hi _
        rcases i with _ | _ | _ | i
        · exact h0
        · exact h1
        · exact h2
        · omega
    · simp at h
  · simp at h

theorem ruleIteEq_sound {ei : EI} {prems params : List Nat} (h : ruleIteEq ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleIteEq at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i args hmk
        split at h
        · rename_i c a b h3
          have hmk' : st.pool[e]? = some ⟨.boolIte, #[c, a, b]⟩ := by
            rw [St.node] at hmk; rw [hmk, three_eq h3]
          exact iteEqBody_sound hinv hmk' (Or.inl rfl) h
        · simp at h
      · rename_i w args hmk
        split at h
        · rename_i c a b h3
          have hmk' : st.pool[e]? = some ⟨.bvIte w, #[c, a, b]⟩ := by
            rw [St.node] at hmk; rw [hmk, three_eq h3]
          exact iteEqBody_sound hinv hmk' (Or.inr ⟨w, rfl⟩) h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A well-typed bit-vector literal has no children and an in-range value. -/
theorem bvVal_typing {pool : Pool} (hwf : WF pool) {i w v : Nat} {args : Array Nat}
    (h : pool[i]? = some ⟨.bvVal w v, args⟩) : args = #[] ∧ w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w := by
  have h2 := (hwf i _ h).2
  rw [typeOf_node hwf h] at h2
  obtain ⟨l⟩ := args
  cases l with
  | nil => simp [mapOpt, Op.resultTy, bvValTy, tyGuard] at h2; exact ⟨rfl, h2⟩
  | cons x rest =>
    simp only [mapOpt] at h2
    cases hx : typeOf pool x <;> cases hr : mapOpt (typeOf pool) rest <;> rw [hx, hr] at h2 <;>
      simp [Op.resultTy, bvValTy] at h2

theorem boolVal_typing {pool : Pool} (hwf : WF pool) {i : Nat} {b : Bool} {args : Array Nat}
    (h : pool[i]? = some ⟨.boolVal b, args⟩) : args = #[] := by
  have h2 := (hwf i _ h).2
  rw [typeOf_node hwf h] at h2
  obtain ⟨l⟩ := args
  cases l with
  | nil => rfl
  | cons x rest =>
    simp only [mapOpt] at h2
    cases hx : typeOf pool x <;> cases hr : mapOpt (typeOf pool) rest <;> rw [hx, hr] at h2 <;>
      simp [Op.resultTy, boolNullTy] at h2

theorem ruleDistinctValues_sound {ei : EI} {prems params : List Nat}
    (h : ruleDistinctValues ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleDistinctValues at h
  split at h
  · rename_i p0 p1
    split at h
    · rename_i v0 v1 _ _
      split at h
      · rename_i w a args0 w' b args1 hv0 hv1
        split at h
        · rename_i hc
          obtain ⟨rfl, hab⟩ := hc
          split at h
          · rename_i st1 e he
            rw [St.node] at hv0 hv1
            obtain ⟨rfl, hw, hw64, ha⟩ := bvVal_typing hinv.wf hv0
            obtain ⟨rfl, -, -, hb⟩ := bvVal_typing hinv.wf hv1
            have hinv1 := hinv.push he
            apply mkNot_entails hinv1 h _ (pushNode_size he).2
            intro ρ _
            rw [eval_node hinv1.wf ρ (pushNode_get he)]
            simp only [Op.eval, List.map, eqEval]
            rw [pushNode_eval he ρ (idx_lt_of_get hv0), pushNode_eval he ρ (idx_lt_of_get hv1),
                eval_node hinv.wf ρ hv0, eval_node hinv.wf ρ hv1]
            simp only [Op.eval, List.map]
            simp [bvValEval, hw, hw64, ha, hb, Val.eqv]
            intro heq
            have := congrArg BitVec.toNat heq
            simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
            exact hab this
          · simp at h
        · simp at h
      · rename_i a args0 b args1 hv0 hv1
        split at h
        · rename_i hab
          split at h
          · rename_i st1 e he
            rw [St.node] at hv0 hv1
            obtain rfl := boolVal_typing hinv.wf hv0
            obtain rfl := boolVal_typing hinv.wf hv1
            have hinv1 := hinv.push he
            apply mkNot_entails hinv1 h _ (pushNode_size he).2
            intro ρ _
            rw [eval_node hinv1.wf ρ (pushNode_get he)]
            simp only [Op.eval, List.map, eqEval]
            rw [pushNode_eval he ρ (idx_lt_of_get hv0), pushNode_eval he ρ (idx_lt_of_get hv1),
                eval_boolVal hinv.wf hv0 ρ, eval_boolVal hinv.wf hv1 ρ]
            simp [Val.eqv]
            exact hab
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-! ### Clauses, resolution, factoring, reordering -/

/-- Some literal of the list is true. -/
def ClauseTrue (pool : Pool) (ρ : Assign) (lits : List Nat) : Prop := ∃ l ∈ lits, holds pool ρ l

theorem clauseTrue_litsOf (hwf : WF st.pool) {p : Nat} (piv : Option Nat) (ρ : Assign)
    (h : holds st.pool ρ p) : ClauseTrue st.pool ρ (litsOf st p piv) := by
  unfold litsOf
  split
  · rename_i args hargs
    split
    · exact ⟨p, by simp, h⟩
    · have hpn := node_bind_disj hargs
      obtain ⟨a, ha, hat⟩ := holds_disj_elim hwf hpn ρ h
      exact ⟨a, by simpa using ha, hat⟩
  · exact ⟨p, by simp, h⟩

theorem litsOf_lt (hwf : WF st.pool) {p : Nat} (piv : Option Nat) (hp : p < st.pool.size) :
    ∀ l ∈ litsOf st p piv, l < st.pool.size := by
  unfold litsOf
  split
  · rename_i args hargs
    split
    · intro l hl; simp at hl; subst hl; exact hp
    · intro l hl; exact child_lt hwf (node_bind_disj hargs) (by simpa using hl)
  · intro l hl; simp at hl; subst hl; exact hp

theorem clauseTrue_erase {pool : Pool} {ρ : Assign} {lits : List Nat} (h : ClauseTrue pool ρ lits) (o : Option Nat) :
    ClauseTrue pool ρ (eraseOpt lits o) ∨ ∃ x, o = some x ∧ holds pool ρ x := by
  cases o with
  | none => exact Or.inl h
  | some x =>
    obtain ⟨l, hl, hlt⟩ := h
    by_cases hlx : l = x
    · subst hlx; exact Or.inr ⟨l, rfl, hlt⟩
    · left; exact ⟨l, List.mem_erase_of_ne hlx |>.mpr hl, hlt⟩

theorem eraseOpt_sub {lits : List Nat} (o : Option Nat) : ∀ l ∈ eraseOpt lits o, l ∈ lits := by
  cases o with
  | none => intro l hl; exact hl
  | some x => intro l hl; exact List.mem_of_mem_erase hl

theorem findNode_get {n : Node} {r : Nat} (h : findNode st n = some r) : st.pool[r]? = some n := by
  unfold findNode at h
  split at h
  · split at h
    · simp at h; subst h; assumption
    · simp at h
  · simp at h

/-- A pivot and its negation cannot both hold. -/
theorem pivot_contra (hwf : WF st.pool) {lit nl : Nat} (hnl : findNode st ⟨.boolNot, #[lit]⟩ = some nl)
    (ρ : Assign) (h1 : holds st.pool ρ lit) (h2 : holds st.pool ρ nl) : False := by
  have := (holds_not_node hwf (findNode_get hnl) ρ).mp h2
  unfold holds at h1; rw [h1] at this; cases this

theorem resolveChain_sound (hwf : WF st.pool) {pols : List Nat} :
    ∀ {rhsPms lits : List Nat} {i : Nat} {lhs res : List Nat},
    resolveChain st pols rhsPms lits i lhs = some res →
    (∀ ρ, holds st.pool ρ g → ClauseTrue st.pool ρ lhs) →
    (∀ p ∈ rhsPms, p < st.pool.size ∧ ∀ ρ, holds st.pool ρ g → holds st.pool ρ p) →
    (∀ l ∈ lhs, l < st.pool.size) →
    (∀ ρ, holds st.pool ρ g → ClauseTrue st.pool ρ res) ∧ ∀ l ∈ res, l < st.pool.size := by
  intro rhsPms
  induction rhsPms with
  | nil =>
    intro lits i lhs res h hl _ hlt
    cases lits with
    | nil => simp [resolveChain] at h; subst h; exact ⟨hl, hlt⟩
    | cons _ _ => simp [resolveChain] at h
  | cons rhsPm rest ih =>
    intro lits i lhs res h hl hp hlt
    cases lits with
    | nil => simp [resolveChain] at h
    | cons lit lits' =>
      simp only [resolveChain] at h
      have hrhs := hp rhsPm (by simp)
      apply ih h
      · intro ρ hg
        have hcl := hl ρ hg
        have hcr := clauseTrue_litsOf hwf (if testPol pols i then findNode st ⟨.boolNot, #[lit]⟩ else some lit) ρ (hrhs.2 ρ hg)
        rcases clauseTrue_erase hcl (if testPol pols i then some lit else findNode st ⟨.boolNot, #[lit]⟩) with h1 | ⟨x, hx, hxt⟩
        · obtain ⟨l, hl', hlt'⟩ := h1; exact ⟨l, List.mem_append_left _ hl', hlt'⟩
        · rcases clauseTrue_erase hcr (if testPol pols i then findNode st ⟨.boolNot, #[lit]⟩ else some lit) with h2 | ⟨y, hy, hyt⟩
          · obtain ⟨l, hl', hlt'⟩ := h2; exact ⟨l, List.mem_append_right _ hl', hlt'⟩
          · exfalso
            cases hpol : testPol pols i <;> simp [hpol] at hx hy
            · subst hy; exact pivot_contra hwf hx ρ hyt hxt
            · subst hx; exact pivot_contra hwf hy ρ hxt hyt
      · intro p hp'; exact hp p (by simp [hp'])
      · intro l hl'
        rcases List.mem_append.mp hl' with h1 | h1
        · exact hlt l (eraseOpt_sub _ l h1)
        · exact litsOf_lt hwf _ hrhs.1 l (eraseOpt_sub _ l h1)

theorem mkClause_entails {lits : List Nat} {c : Nat} (hinv : Inv base g bi st)
    (h : mkClause bi st lits = some (st', c)) (hlt : ∀ l ∈ lits, l < st.pool.size)
    (hc : ∀ ρ, holds st.pool ρ g → ClauseTrue st.pool ρ lits) :
    Inv base g bi st' ∧ Entails st' g c := by
  unfold mkClause at h
  split at h
  · split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨hinv, by assumption, ?_⟩
      intro ρ hg; obtain ⟨l, hl, _⟩ := hc ρ hg; simp at hl
    · simp at h
  · rename_i l
    simp at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨hinv, hlt l (by simp), ?_⟩
    intro ρ hg; obtain ⟨l', hl', hlt'⟩ := hc ρ hg; simp at hl'; subst hl'; exact hlt'
  · apply mkDisj_entails hinv h (fun l hl => hlt l (by simpa using hl))
    intro ρ hg; obtain ⟨l, hl, hlt'⟩ := hc ρ hg; exact ⟨l, by simpa using hl, hlt'⟩

theorem ruleResolution_sound {ei : EI} {prems params : List Nat}
    (h : ruleResolution bi ei st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleResolution at h
  split at h
  · rename_i p0 rest
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i lit0 lits _
          split at h
          · rename_i res hres
            have hp0 := hp p0 (by simp)
            obtain ⟨hct, hlt⟩ := resolveChain_sound hinv.wf hres
              (fun ρ hg => clauseTrue_litsOf hinv.wf _ ρ (hp0.2 ρ hg))
              (fun p hp' => ⟨(hp p (by simp [hp'])).1, (hp p (by simp [hp'])).2⟩)
              (litsOf_lt hinv.wf _ hp0.1)
            exact mkClause_entails hinv h hlt hct
          · simp at h
        · simp at h
  · simp at h

theorem ruleFactoring_sound {prems params : List Nat} (h : ruleFactoring st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleFactoring at h
  split at h
  · rename_i p
    split at h
    · rename_i args hargs
      split at h
      · simp at h
      · split at h
        · rename_i dups _
          split at h
          · rename_i hall
            have hpn := node_bind_disj hargs
            simp only [subsetB_eq, List.all_eq_true, decide_eq_true_eq] at hall
            have hkept : ∀ l ∈ keptLits args dups, l ∈ args := by
              intro l hl
              obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hl
              rw [Array.getElem?_eq_some_iff] at hi; obtain ⟨hk, rfl⟩ := hi; exact Array.getElem_mem hk
            have hclause : ∀ ρ, holds st.pool ρ g → ∃ l ∈ keptLits args dups, holds st.pool ρ l := by
              intro ρ hg
              obtain ⟨a, ha, hat⟩ := holds_disj_elim hinv.wf hpn ρ ((hp p (by simp)).2 ρ hg)
              exact ⟨a, hall a (by simpa using ha), hat⟩
            split at h
            · rename_i l hl
              simp at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨hinv, child_lt hinv.wf hpn (hkept l (by rw [hl]; simp)), ?_⟩
              intro ρ hg
              obtain ⟨l', hl', hlt⟩ := hclause ρ hg
              rw [hl] at hl'; simp at hl'; subst hl'; exact hlt
            · apply mkDisj_entails hinv h
              · intro l hl; exact child_lt hinv.wf hpn (hkept l (by simpa using hl))
              · intro ρ hg; obtain ⟨l, hl, hlt⟩ := hclause ρ hg; exact ⟨l, by simpa using hl, hlt⟩
          · simp at h
        · simp at h
    · simp at h
  · simp at h

theorem ruleReordering_sound {prems params : List Nat} (h : ruleReordering st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleReordering at h
  split at h
  · rename_i p
    split at h
    · rename_i args hargs
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hinv, hp p (by simp)⟩
      · split at h
        · rename_i args' _
          split at h
          · rename_i hall
            have hpn := node_bind_disj hargs
            simp only [subsetB_eq, List.all_eq_true, decide_eq_true_eq] at hall
            obtain ⟨hall1, hall2⟩ := hall
            apply mkDisj_entails hinv h
            · intro l hl; exact child_lt hinv.wf hpn (by simpa using hall2 l (by simpa using hl))
            · intro ρ hg
              obtain ⟨a, ha, hat⟩ := holds_disj_elim hinv.wf hpn ρ ((hp p (by simp)).2 ρ hg)
              exact ⟨a, by simpa using hall1 a (by simpa using ha), hat⟩
          · simp at h
        · simp at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hinv, hp p (by simp)⟩
  · simp at h

end Rules

end Bcf
