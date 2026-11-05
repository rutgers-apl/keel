import Bcf.Rw.Bv

/-!
# Boolean, `ite` and equality rewrites

The `ITE_*`, `EQ_*`, `BOOL_*` rewrites not already covered in `Rw/Core.lean`,
including the four with `Bools` list parameters (`BOOL_AND_CONF*`, `BOOL_OR_TAUT*`).
-/
namespace Bcf

open RwExpr

/-! ## Helpers -/

theorem bool_appVal_eq_ne_list (l : List Val) (e : Bool) (vs : List Val) : appVal .eq l ≠ .list e vs := by
  rcases l with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp only [appVal, RwOp.reducible, RwOp.node, Op.eval, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact eqEval_ne_list _ _ _ _ | simp

theorem bool_appVal_not_ne_list (l : List Val) (e : Bool) (vs : List Val) : appVal .not l ≠ .list e vs := by
  rcases l with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp only [appVal, RwOp.reducible, RwOp.node, Op.eval, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact boolNotEval_ne_list _ _ _ | simp

theorem bool_splice_eq (l : List Val) : spliceVal (appVal .eq l) = [appVal .eq l] :=
  spliceVal_of_ne (fun _ _ => bool_appVal_eq_ne_list l _ _)
theorem bool_splice_not (l : List Val) : spliceVal (appVal .not l) = [appVal .not l] :=
  spliceVal_of_ne (fun _ _ => bool_appVal_not_ne_list l _ _)

theorem bool_eqv_bb (a b : Bool) : Val.eqv (.bool a) (.bool b) = .bool (decide (a = b)) := rfl
theorem bool_eqv_vv {n m : Nat} (x : BitVec n) (y : BitVec m) :
    Val.eqv (.bv n x) (.bv m y) = if h : m = n then .bool (decide (x = y.cast h)) else .bad := rfl
theorem bool_eqv_bad_l (x : Val) : Val.eqv .bad x = .bad := by cases x <;> rfl
theorem bool_eqv_bad_r (x : Val) : Val.eqv x .bad = .bad := by cases x <;> rfl
theorem bool_eqv_list_l (e : Bool) (vs : List Val) (x : Val) : Val.eqv (.list e vs) x = .bad := by cases x <;> rfl
theorem bool_eqv_list_r (e : Bool) (vs : List Val) (x : Val) : Val.eqv x (.list e vs) = .bad := by cases x <;> rfl
theorem bool_eqv_bool_bv (a : Bool) {n : Nat} (x : BitVec n) : Val.eqv (.bool a) (.bv n x) = .bad := rfl
theorem bool_eqv_bv_bool (a : Bool) {n : Nat} (x : BitVec n) : Val.eqv (.bv n x) (.bool a) = .bad := rfl

syntax "bool_unfold" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| bool_unfold $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.xor', RwExpr.conj',
      RwExpr.implies', RwExpr.disj', RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, appVal, RwOp.reducible,
      RwOp.node, Op.eval, eqEval, bool_eqv_bb, bool_eqv_vv, bool_eqv_bad_l, bool_eqv_bad_r, bool_eqv_list_l,
      bool_eqv_list_r, bool_eqv_bool_bv, bool_eqv_bv_bool, boolNotEval, boolN, Val.bools, Val.asBool, impliesEval,
      boolIteEval, bvIteEval, Val.asCond, Val.asBv, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, dite_true,
      dite_false, ne_eq, not_false_eq_true, not_true_eq_false, BitVec.cast_eq] $[$loc]?)

syntax "bool_open" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| bool_open $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.xor', RwExpr.conj',
      RwExpr.implies', RwExpr.disj', RwExpr.mk, RwArgs.ofList, denoteE, denoteA, bool_splice_eq, bool_splice_not,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append] $[$loc]?)


/-- Full `simp` with the evaluator unfoldings and the `Val.eqv` case lemmas; extra facts in brackets. -/
syntax "bool_simp" ("[" Lean.Parser.Tactic.simpArg,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| bool_simp [$ts,*] $[$loc]?) => `(tactic| simp [bool_eqv_bb, bool_eqv_vv, bool_eqv_bad_l, bool_eqv_bad_r,
      bool_eqv_list_l, bool_eqv_list_r, bool_eqv_bool_bv, bool_eqv_bv_bool, spliceVal, appVal, RwOp.reducible, RwOp.node,
      Op.eval, eqEval, boolNotEval, boolN, Val.bools, Val.asBool, impliesEval, boolIteEval, bvIteEval, Val.asCond,
      Val.asBv, $ts,*] $[$loc]?)
  | `(tactic| bool_simp $[$loc]?) => `(tactic| simp [bool_eqv_bb, bool_eqv_vv, bool_eqv_bad_l, bool_eqv_bad_r,
      bool_eqv_list_l, bool_eqv_list_r, bool_eqv_bool_bv, bool_eqv_bv_bool, spliceVal, appVal, RwOp.reducible, RwOp.node,
      Op.eval, eqEval, boolNotEval, boolN, Val.bools, Val.asBool, impliesEval, boolIteEval, bvIteEval, Val.asCond,
      Val.asBv] $[$loc]?)

/-- Close a goal that is either ill-typed (`hl`/`hr` is `.bad`) or a truth table over `b`. -/
macro "bool_done" hl:ident hr:ident b:ident : tactic => `(tactic|
  first | exact absurd rfl $hl | exact absurd rfl $hr | (bool_simp at $hl:ident; done) | (bool_simp at $hr:ident; done)
        | (cases $b:ident <;> bool_simp; done))


/-! ## Rules -/

-- rewrite id 1
theorem sound_EQ_REFL :
    (RwRule.mk [.any]
      (none)
      (eq' (var 0) (var 0))
      (tt)).Sound := by
  intro env _ _ hl hr
  bool_open at hl hr ⊢
  generalize spliceVal (env 0) = s0 at *
  rcases s0 with _ | ⟨a, _ | ⟨b, _ | ⟨c, r0⟩⟩⟩ <;> bool_unfold at hl ⊢ <;> try exact absurd rfl hl
  cases a <;> bool_simp at hl ⊢

-- rewrite id 3
theorem sound_EQ_COND_DEQ :
    (RwRule.mk [.any, .any, .any]
      (some (eq' (eq' (var 1) (var 2)) (ff)))
      (eq' (eq' (var 0) (var 1)) (eq' (var 0) (var 2)))
      (conj' [not' (eq' (var 0) (var 1)), not' (eq' (var 0) (var 2))])).Sound := by
  intro env _ hc hl hr
  have hc := hc _ rfl
  bool_open at hc hl hr ⊢
  generalize spliceVal (env 0) = s0 at *
  generalize spliceVal (env 1) = s1 at *
  generalize spliceVal (env 2) = s2 at *
  rcases s0 with _ | ⟨a, _ | ⟨a', _ | ⟨a'', r0⟩⟩⟩ <;> rcases s1 with _ | ⟨b, _ | ⟨b', _ | ⟨b'', r1⟩⟩⟩ <;>
    rcases s2 with _ | ⟨c, _ | ⟨c', _ | ⟨c'', r2⟩⟩⟩ <;> bool_unfold at hc hl hr ⊢
  all_goals first | exact absurd rfl hl | exact Val.noConfusion hc | skip
  generalize h1 : Val.eqv a b = q1 at *
  generalize h2 : Val.eqv a c = q2 at *
  generalize h3 : Val.eqv b c = q3 at *
  cases q3 <;> simp only [bool_eqv_bad_l, bool_eqv_bb] at hc <;> try exact Val.noConfusion hc
  rename_i r3
  cases r3
  · cases q1 <;> cases q2 <;> simp only [bool_eqv_bad_l, bool_eqv_bad_r, bool_eqv_bb] at hl ⊢ <;>
      try exact absurd rfl hl
    rename_i r1 r2
    cases r1 <;> cases r2 <;> simp
    have := (eqv_true_iff.mp h1).1; subst this
    have := (eqv_true_iff.mp h2).1; subst this
    rw [h1] at h3; simp at h3
  · simp at hc

-- rewrite id 4
theorem sound_EQ_ITE_LIFT :
    (RwRule.mk [.bool, .any, .any, .any]
      (none)
      (eq' (ite (var 0) (var 1) (var 2)) (var 3))
      (ite (var 0) (eq' (var 1) (var 3)) (eq' (var 2) (var 3)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, eb⟩ := henv 0 .bool rfl
  bool_open at hl hr ⊢
  simp only [eb] at hl hr ⊢
  generalize spliceVal (env 3) = s3 at *
  generalize env 1 = v1 at *
  generalize env 2 = v2 at *
  cases v1 with
  | bool c =>
    cases v2 with
    | bool c' =>
      rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl hr ⊢ <;> try bool_done hl hr b
      cases d <;> bool_unfold at hl hr ⊢ <;> bool_done hl hr b
    | _ => rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl <;> bool_done hl hr b
  | bv w x =>
    cases v2 with
    | bv w' y =>
      by_cases h : w' = w
      · subst w'
        by_cases hw : w = 0
        · rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl <;> bool_simp [hw] at hl
        · rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl hr ⊢ <;>
            simp only [hw, not_false_eq_true, ↓reduceIte] at hl hr ⊢ <;> try bool_done hl hr b
          cases d with
          | bv m z =>
            by_cases hm : m = w
            · subst m; bool_unfold at hl hr ⊢; bool_done hl hr b
            · bool_simp [hm] at hl
          | _ => bool_simp at hl
      · rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl <;> bool_simp [h] at hl
    | _ => rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl <;> bool_done hl hr b
  | list e vs => rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl <;> bool_done hl hr b
  | bad => rcases s3 with _ | ⟨d, _ | ⟨d', _ | ⟨d'', r3⟩⟩⟩ <;> bool_unfold at hl <;> bool_done hl hr b

-- rewrite id 6
theorem sound_ITE_TRUE_COND :
    (RwRule.mk [.any, .any]
      (none)
      (ite (tt) (var 0) (var 1))
      (var 0)).Sound := by
  intro env _ _ hl hr
  bool_unfold at hl hr ⊢
  generalize env 0 = v0 at *
  generalize env 1 = v1 at *
  cases v0 with
  | bool b => cases v1 <;> bool_simp at hl ⊢
  | bv w x =>
    cases v1 with
    | bv w' y =>
      by_cases h : w' = w
      · subst w'; bool_simp at hl ⊢; try exact hl
      · bool_simp [h] at hl
    | _ => bool_simp at hl
  | _ => bool_simp at hl

-- rewrite id 7
theorem sound_ITE_FALSE_COND :
    (RwRule.mk [.any, .any]
      (none)
      (ite (ff) (var 0) (var 1))
      (var 1)).Sound := by
  intro env _ _ hl hr
  bool_unfold at hl hr ⊢
  generalize env 0 = v0 at *
  generalize env 1 = v1 at *
  cases v0 with
  | bool b => cases v1 <;> bool_simp at hl ⊢
  | bv w x =>
    cases v1 with
    | bv w' y =>
      by_cases h : w' = w
      · subst w'; bool_simp at hl ⊢; try exact hl
      · bool_simp [h] at hl
    | _ => bool_simp at hl
  | _ => bool_simp at hl

-- rewrite id 8
theorem sound_ITE_NOT_COND :
    (RwRule.mk [.bool, .any, .any]
      (none)
      (ite (not' (var 0)) (var 1) (var 2))
      (ite (var 0) (var 2) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, eb⟩ := henv 0 .bool rfl
  bool_unfold at hl hr ⊢
  simp only [eb] at hl hr ⊢
  try bool_unfold at hl hr ⊢
  generalize env 1 = v1 at *
  generalize env 2 = v2 at *
  cases v1 with
  | bool c => cases v2 <;> bool_done hl hr b
  | bv w x =>
    cases v2 with
    | bv w' y =>
      by_cases h : w' = w
      · subst w'; bool_done hl hr b
      · bool_simp [h] at hl
    | _ => bool_simp at hl
  | _ => bool_simp at hl

-- rewrite id 9
theorem sound_ITE_EQ_BRANCH :
    (RwRule.mk [.bool, .any]
      (none)
      (ite (var 0) (var 1) (var 1))
      (var 1)).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, eb⟩ := henv 0 .bool rfl
  bool_unfold at hl hr ⊢
  simp only [eb] at hl hr ⊢
  try bool_unfold at hl hr ⊢
  generalize env 1 = v1 at *
  cases v1 with
  | bool c => cases b <;> simp
  | bv w x =>
    by_cases hw : w = 0
    · simp [hw] at hl
    · cases b <;> simp [hw]
  | _ => simp at hl

-- rewrite id 10
theorem sound_ITE_THEN_LOOKAHEAD :
    (RwRule.mk [.bool, .any, .any, .any]
      (none)
      (ite (var 0) (ite (var 0) (var 1) (var 2)) (var 3))
      (ite (var 0) (var 1) (var 3))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, eb⟩ := henv 0 .bool rfl
  bool_unfold at hl hr ⊢
  simp only [eb] at hl hr ⊢
  try bool_unfold at hl hr ⊢
  generalize env 1 = v1 at *
  generalize env 2 = v2 at *
  generalize env 3 = v3 at *
  cases v1 with
  | bool c =>
    cases v2 with
    | bool c' => cases v3 <;> bool_done hl hr b
    | _ => bool_simp at hl
  | bv w x =>
    cases v2 with
    | bv w' y =>
      by_cases h : w' = w
      · subst w'
        by_cases hw : w = 0
        · bool_simp [hw] at hl
        · bool_unfold at hl hr ⊢
          simp only [hw, not_false_eq_true, ↓reduceIte] at hl hr ⊢
          cases v3 with
          | bv m z =>
            by_cases hm : m = w
            · subst m; bool_unfold at hl hr ⊢; bool_done hl hr b
            · bool_simp [hm] at hl
          | _ => bool_simp at hl
      · bool_simp [h] at hl
    | _ => bool_simp at hl
  | _ => bool_simp at hl

-- rewrite id 11
theorem sound_ITE_ELSE_LOOKAHEAD :
    (RwRule.mk [.bool, .any, .any, .any]
      (none)
      (ite (var 0) (var 1) (ite (var 0) (var 2) (var 3)))
      (ite (var 0) (var 1) (var 3))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, eb⟩ := henv 0 .bool rfl
  bool_unfold at hl hr ⊢
  simp only [eb] at hl hr ⊢
  try bool_unfold at hl hr ⊢
  generalize env 1 = v1 at *
  generalize env 2 = v2 at *
  generalize env 3 = v3 at *
  cases v1 with
  | bool c =>
    cases v2 with
    | bool c' => cases v3 <;> bool_done hl hr b
    | bv w y =>
      cases v3 with
      | bv m z =>
        by_cases hm : m = w
        · subst m; by_cases hw : w = 0
          · bool_simp [hw] at hl
          · bool_simp [hw] at hl
        · bool_simp [hm] at hl
      | _ => bool_simp at hl
    | _ => bool_simp at hl
  | bv w x =>
    cases v2 with
    | bv w' y =>
      cases v3 with
      | bv m z =>
        by_cases h : w' = w
        · subst w'
          by_cases hm : m = w
          · subst m
            by_cases hw : w = 0
            · bool_simp [hw] at hl
            · bool_unfold at hl hr ⊢
              simp only [hw, not_false_eq_true, ↓reduceIte] at hl hr ⊢
              bool_done hl hr b
          · bool_simp [hm] at hl
        · by_cases hm : m = w'
          · subst m
            by_cases hw : w' = 0
            · bool_simp [hw] at hl
            · bool_simp [hw, h] at hl
          · bool_simp [hm] at hl
      | _ => bool_simp at hl
    | _ => cases v3 <;> bool_simp at hl
  | _ => bool_simp at hl

-- rewrite id 12
theorem sound_ITE_THEN_NEG_LOOKAHEAD :
    (RwRule.mk [.bool, .any, .any, .any]
      (none)
      (ite (var 0) (ite (not' (var 0)) (var 1) (var 2)) (var 3))
      (ite (var 0) (var 2) (var 3))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, eb⟩ := henv 0 .bool rfl
  bool_unfold at hl hr ⊢
  simp only [eb] at hl hr ⊢
  try bool_unfold at hl hr ⊢
  generalize env 1 = v1 at *
  generalize env 2 = v2 at *
  generalize env 3 = v3 at *
  cases v1 with
  | bool c =>
    cases v2 with
    | bool c' => cases v3 <;> bool_done hl hr b
    | _ => bool_simp at hl
  | bv w x =>
    cases v2 with
    | bv w' y =>
      by_cases h : w' = w
      · subst w'
        by_cases hw : w = 0
        · bool_simp [hw] at hl
        · bool_unfold at hl hr ⊢
          simp only [hw, not_false_eq_true, ↓reduceIte] at hl hr ⊢
          cases v3 with
          | bv m z =>
            by_cases hm : m = w
            · subst m; bool_unfold at hl hr ⊢; bool_done hl hr b
            · bool_simp [hm] at hl
          | _ => bool_simp at hl
      · bool_simp [h] at hl
    | _ => bool_simp at hl
  | _ => bool_simp at hl

-- rewrite id 13
theorem sound_ITE_ELSE_NEG_LOOKAHEAD :
    (RwRule.mk [.bool, .any, .any, .any]
      (none)
      (ite (var 0) (var 1) (ite (not' (var 0)) (var 2) (var 3)))
      (ite (var 0) (var 1) (var 2))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, eb⟩ := henv 0 .bool rfl
  bool_unfold at hl hr ⊢
  simp only [eb] at hl hr ⊢
  try bool_unfold at hl hr ⊢
  generalize env 1 = v1 at *
  generalize env 2 = v2 at *
  generalize env 3 = v3 at *
  cases v1 with
  | bool c =>
    cases v2 with
    | bool c' => cases v3 <;> bool_done hl hr b
    | bv w y =>
      cases v3 with
      | bv m z =>
        by_cases hm : m = w
        · subst m; by_cases hw : w = 0
          · bool_simp [hw] at hl
          · bool_simp [hw] at hl
        · bool_simp [hm] at hl
      | _ => bool_simp at hl
    | _ => bool_simp at hl
  | bv w x =>
    cases v2 with
    | bv w' y =>
      cases v3 with
      | bv m z =>
        by_cases h : w' = w
        · subst w'
          by_cases hm : m = w
          · subst m
            by_cases hw : w = 0
            · bool_simp [hw] at hl
            · bool_unfold at hl hr ⊢
              simp only [hw, not_false_eq_true, ↓reduceIte] at hl hr ⊢
              bool_done hl hr b
          · bool_simp [hm] at hl
        · by_cases hm : m = w'
          · subst m
            by_cases hw : w' = 0
            · bool_simp [hw] at hl
            · bool_simp [hw, h] at hl
          · bool_simp [hm] at hl
      | _ => bool_simp at hl
    | _ => cases v3 <;> bool_simp at hl
  | _ => bool_simp at hl

-- rewrite id 15
theorem sound_BOOL_NOT_TRUE :
    (RwRule.mk [.bool]
      (some (eq' (var 0) (ff)))
      (not' (var 0))
      (tt)).Sound := by
  intro env henv hc hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  have hc := hc _ rfl
  bool_unfold at hc ⊢
  simp only [ea] at hc ⊢
  try bool_unfold at hc ⊢
  cases a <;> simp_all

-- rewrite id 16
theorem sound_BOOL_NOT_FALSE :
    (RwRule.mk [.bool]
      (some (eq' (var 0) (tt)))
      (not' (var 0))
      (ff)).Sound := by
  intro env henv hc hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  have hc := hc _ rfl
  bool_unfold at hc ⊢
  simp only [ea] at hc ⊢
  try bool_unfold at hc ⊢
  cases a <;> simp_all

-- rewrite id 20
theorem sound_BOOL_IMPL_FALSE1 :
    (RwRule.mk [.bool]
      (none)
      (implies' (var 0) (ff))
      (not' (var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  bool_unfold
  simp only [ea]
  try bool_unfold
  cases a <;> rfl

-- rewrite id 21
theorem sound_BOOL_IMPL_FALSE2 :
    (RwRule.mk [.bool]
      (none)
      (implies' (ff) (var 0))
      (tt)).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  bool_unfold
  simp only [ea]
  try bool_unfold
  cases a <;> rfl

-- rewrite id 22
theorem sound_BOOL_IMPL_TRUE1 :
    (RwRule.mk [.bool]
      (none)
      (implies' (var 0) (tt))
      (tt)).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  bool_unfold
  simp only [ea]
  try bool_unfold
  cases a <;> rfl

-- rewrite id 23
theorem sound_BOOL_IMPL_TRUE2 :
    (RwRule.mk [.bool]
      (none)
      (implies' (tt) (var 0))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  bool_unfold
  simp only [ea]
  try bool_unfold
  cases a <;> rfl

-- rewrite id 24
theorem sound_BOOL_IMPL_ELIM :
    (RwRule.mk [.bool, .bool]
      (none)
      (implies' (var 0) (var 1))
      (disj' [not' (var 0), var 1])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 25
theorem sound_BOOL_DUAL_IMPL_EQ :
    (RwRule.mk [.bool, .bool]
      (none)
      (conj' [implies' (var 0) (var 1), implies' (var 1) (var 0)])
      (eq' (var 0) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 30
theorem sound_BOOL_IMPLIES_DE_MORGAN :
    (RwRule.mk [.bool, .bool]
      (none)
      (not' (implies' (var 0) (var 1)))
      (conj' [var 0, not' (var 1)])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 31
theorem sound_BOOL_XOR_REFL :
    (RwRule.mk [.bool]
      (none)
      (xor' [var 0, var 0])
      (ff)).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  bool_unfold
  simp only [ea]
  try bool_unfold
  cases a <;> rfl

-- rewrite id 36
theorem sound_BOOL_XOR_ELIM :
    (RwRule.mk [.bool, .bool]
      (none)
      (xor' [var 0, var 1])
      (eq' (not' (var 0)) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 37
theorem sound_BOOL_NOT_XOR_ELIM :
    (RwRule.mk [.bool, .bool]
      (none)
      (not' (xor' [var 0, var 1]))
      (eq' (var 0) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 38
theorem sound_BOOL_NOT_EQ_ELIM1 :
    (RwRule.mk [.bool, .bool]
      (none)
      (not' (eq' (var 0) (var 1)))
      (eq' (not' (var 0)) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 39
theorem sound_BOOL_NOT_EQ_ELIM2 :
    (RwRule.mk [.bool, .bool]
      (none)
      (not' (eq' (var 0) (var 1)))
      (eq' (var 0) (not' (var 1)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 40
theorem sound_ITE_NEG_BRANCH :
    (RwRule.mk [.bool, .bool, .bool]
      (some (eq' (not' (var 2)) (var 1)))
      (ite (var 0) (var 1) (var 2))
      (eq' (var 0) (var 1))).Sound := by
  intro env henv hc hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  obtain ⟨c, ec⟩ := henv 2 .bool rfl
  have hc := hc _ rfl
  bool_unfold at hc ⊢
  simp only [ea, eb, ec] at hc ⊢
  try bool_unfold at hc ⊢
  cases a <;> cases b <;> cases c <;> simp_all

-- rewrite id 41
theorem sound_ITE_THEN_TRUE :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (tt) (var 1))
      (disj' [var 0, var 1])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 42
theorem sound_ITE_ELSE_FALSE :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (var 1) (ff))
      (conj' [var 0, var 1])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 43
theorem sound_ITE_THEN_FALSE :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (ff) (var 1))
      (conj' [not' (var 0), var 1])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 44
theorem sound_ITE_ELSE_TRUE :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (var 1) (tt))
      (disj' [not' (var 0), var 1])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 45
theorem sound_ITE_THEN_LOOKAHEAD_SELF :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (var 0) (var 1))
      (ite (var 0) (tt) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 46
theorem sound_ITE_ELSE_LOOKAHEAD_SELF :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (var 1) (var 0))
      (ite (var 0) (var 1) (ff))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 47
theorem sound_ITE_THEN_LOOKAHEAD_NOT_SELF :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (not' (var 0)) (var 1))
      (ite (var 0) (ff) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 48
theorem sound_ITE_ELSE_LOOKAHEAD_NOT_SELF :
    (RwRule.mk [.bool, .bool]
      (none)
      (ite (var 0) (var 1) (not' (var 0)))
      (ite (var 0) (var 1) (tt))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  bool_unfold
  simp only [ea, eb]
  try bool_unfold
  cases a <;> cases b <;> rfl

-- rewrite id 49
theorem sound_ITE_EXPAND :
    (RwRule.mk [.bool, .bool, .bool]
      (none)
      (ite (var 0) (var 1) (var 2))
      (conj' [disj' [not' (var 0), var 1], disj' [var 0, var 2]])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  obtain ⟨c, ec⟩ := henv 2 .bool rfl
  bool_unfold
  simp only [ea, eb, ec]
  try bool_unfold
  cases a <;> cases b <;> cases c <;> rfl

-- rewrite id 50
theorem sound_BOOL_NOT_ITE_ELIM :
    (RwRule.mk [.bool, .bool, .bool]
      (none)
      (not' (ite (var 0) (var 1) (var 2)))
      (ite (var 0) (not' (var 1)) (not' (var 2)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  obtain ⟨c, ec⟩ := henv 2 .bool rfl
  bool_unfold
  simp only [ea, eb, ec]
  try bool_unfold
  cases a <;> cases b <;> cases c <;> rfl

/-! ## Helpers -/

/-- A boolean element of an argument list ends up in `Val.bools` of that list. -/
theorem bool_bools_mem {vs : List Val} {bs : List Bool} (h : Val.bools vs = some bs) {b : Bool}
    (hm : Val.bool b ∈ vs) : b ∈ bs := by
  induction vs generalizing bs with
  | nil => simp at hm
  | cons v rest ih =>
    simp only [Val.bools] at h
    generalize hr : Val.bools rest = r at h
    cases v <;> simp only [Val.asBool] at h <;> cases r <;> simp at h
    subst h
    simp only [List.mem_cons, Val.bool.injEq] at hm
    rcases hm with rfl | hm
    · simp
    · exact List.mem_cons_of_mem _ (ih hr hm)

theorem bool_appVal_not (v : Val) : appVal .not [v] = boolNotEval [v] := rfl

theorem bool_appVal_conj {vs : List Val} (h : 2 ≤ vs.length) :
    appVal .conj vs = boolN (List.all · id) vs := by
  match vs with
  | [] => simp at h
  | [_] => simp at h
  | _ :: _ :: _ => rfl

theorem bool_appVal_disj {vs : List Val} (h : 2 ≤ vs.length) :
    appVal .disj vs = boolN (List.any · id) vs := by
  match vs with
  | [] => simp at h
  | [_] => simp at h
  | _ :: _ :: _ => rfl

/-- A conjunction containing both `b` and `!b` is false (when it is well typed). -/
theorem bool_conj_conf {l : List Val} {b : Bool} (hb : Val.bool b ∈ l) (hnb : Val.bool (!b) ∈ l)
    (h2 : 2 ≤ l.length) (hl : appVal .conj l ≠ .bad) : appVal .conj l = .bool false := by
  rw [bool_appVal_conj h2] at hl ⊢
  unfold boolN at hl ⊢
  generalize hbs : Val.bools l = obs at hl ⊢
  cases obs with
  | none => exact absurd rfl hl
  | some bs =>
    have hall : bs.all id = false := by
      rw [List.all_eq_false]
      cases b
      · exact ⟨false, bool_bools_mem hbs hb, by simp⟩
      · exact ⟨false, bool_bools_mem hbs hnb, by simp⟩
    by_cases hlen : 2 ≤ bs.length
    · simp only [hlen, ↓reduceIte, hall]
    · simp only [hlen, ↓reduceIte] at hl; exact absurd rfl hl

/-- A disjunction containing both `b` and `!b` is true (when it is well typed). -/
theorem bool_disj_taut {l : List Val} {b : Bool} (hb : Val.bool b ∈ l) (hnb : Val.bool (!b) ∈ l)
    (h2 : 2 ≤ l.length) (hl : appVal .disj l ≠ .bad) : appVal .disj l = .bool true := by
  rw [bool_appVal_disj h2] at hl ⊢
  unfold boolN at hl ⊢
  generalize hbs : Val.bools l = obs at hl ⊢
  cases obs with
  | none => exact absurd rfl hl
  | some bs =>
    have hany : bs.any id = true := by
      rw [List.any_eq_true]
      cases b
      · exact ⟨true, bool_bools_mem hbs hnb, rfl⟩
      · exact ⟨true, bool_bools_mem hbs hb, rfl⟩
    by_cases hlen : 2 ≤ bs.length
    · simp only [hlen, ↓reduceIte, hany]
    · simp only [hlen, ↓reduceIte] at hl; exact absurd rfl hl

-- Unfold the denotation of the G2 patterns down to `appVal` on the spliced argument list
-- (uses the fixed hypothesis names of the `Sound` proofs below).
set_option hygiene false in
macro "bool_unfold" : tactic => `(tactic| (
  obtain ⟨vs0, h0⟩ := henv 0 .bools rfl
  obtain ⟨b, h1⟩ := henv 1 .bool rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bools rfl
  obtain ⟨vs3, h3⟩ := henv 3 .bools rfl
  simp only [RwExpr.conj', RwExpr.disj', RwExpr.not', RwExpr.mk, RwArgs.ofList, denoteE, denoteA,
    spliceVal, List.append_nil, List.singleton_append, List.cons_append, List.nil_append] at hl ⊢
  simp only [h0, h1, h2, h3, bool_appVal_not, boolNotEval, List.cons_append, List.nil_append] at hl ⊢))

/-! ## Rules -/

-- rewrite id 26
theorem sound_BOOL_AND_CONF :
    (RwRule.mk [.bools, .bool, .bools, .bools]
      (none)
      (conj' [var 0, var 1, var 2, not' (var 1), var 3])
      (ff)).Sound := by
  intro env henv _ hl hr
  bool_unfold
  exact bool_conj_conf (b := b) (by simp) (by simp) (by simp; omega) hl

-- rewrite id 27
theorem sound_BOOL_AND_CONF2 :
    (RwRule.mk [.bools, .bool, .bools, .bools]
      (none)
      (conj' [var 0, not' (var 1), var 2, var 1, var 3])
      (ff)).Sound := by
  intro env henv _ hl hr
  bool_unfold
  exact bool_conj_conf (b := b) (by simp) (by simp) (by simp; omega) hl

-- rewrite id 28
theorem sound_BOOL_OR_TAUT :
    (RwRule.mk [.bools, .bool, .bools, .bools]
      (none)
      (disj' [var 0, var 1, var 2, not' (var 1), var 3])
      (tt)).Sound := by
  intro env henv _ hl hr
  bool_unfold
  exact bool_disj_taut (b := b) (by simp) (by simp) (by simp; omega) hl

-- rewrite id 29
theorem sound_BOOL_OR_TAUT2 :
    (RwRule.mk [.bools, .bool, .bools, .bools]
      (none)
      (disj' [var 0, not' (var 1), var 2, var 1, var 3])
      (tt)).Sound := by
  intro env henv _ hl hr
  bool_unfold
  exact bool_disj_taut (b := b) (by simp) (by simp) (by simp; omega) hl

/-- A list whose `Val.bools` succeeds is a list of booleans. -/
theorem bool_bools_map {vs : List Val} {bs : List Bool} (h : Val.bools vs = some bs) :
    vs = bs.map Val.bool := by
  induction vs generalizing bs with
  | nil => simp [Val.bools] at h; simp [h]
  | cons v rest ih =>
    simp only [Val.bools] at h
    generalize hr : Val.bools rest = r at h
    cases v <;> simp only [Val.asBool] at h <;> cases r <;> simp at h
    subst h
    simp [ih hr]

theorem bool_bools_map_bool (bs : List Bool) : Val.bools (bs.map Val.bool) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [Val.bools, Val.asBool, ih]

-- rewrite id 153 (cvc5 `bool-and-de-morgan`, not in BCF's table; one step of the `define-rule*`)
theorem sound_BOOL_AND_DE_MORGAN :
    (RwRule.mk [.bool, .bool, .bools]
      (none)
      (not' (conj' [var 0, var 1, var 2]))
      (disj' [not' (var 0), not' (conj' [var 1, var 2])])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  obtain ⟨vs, ec⟩ := henv 2 .bools rfl
  bool_open at hl ⊢
  simp only [ea, eb, ec, spliceVal, List.cons_append, List.nil_append] at hl ⊢
  rcases hc : Val.bools vs with _ | bs
  · exfalso; apply hl; bool_simp [hc]
  · obtain rfl := bool_bools_map hc
    rcases bs with _ | ⟨c, bs⟩ <;> cases a <;> cases b <;> bool_simp [bool_bools_map_bool]

-- rewrite id 154 (cvc5 `bool-or-de-morgan`, not in BCF's table; one step of the `define-rule*`)
theorem sound_BOOL_OR_DE_MORGAN :
    (RwRule.mk [.bool, .bool, .bools]
      (none)
      (not' (disj' [var 0, var 1, var 2]))
      (conj' [not' (var 0), not' (disj' [var 1, var 2])])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  obtain ⟨vs, ec⟩ := henv 2 .bools rfl
  bool_open at hl ⊢
  simp only [ea, eb, ec, spliceVal, List.cons_append, List.nil_append] at hl ⊢
  rcases hc : Val.bools vs with _ | bs
  · exfalso; apply hl; bool_simp [hc]
  · obtain rfl := bool_bools_map hc
    rcases bs with _ | ⟨c, bs⟩ <;> cases a <;> cases b <;> bool_simp [bool_bools_map_bool]

-- rewrite id 155 (cvc5 `bool-implies-or-distrib`, not in BCF's table; one step of the `define-rule*`)
theorem sound_BOOL_IMPLIES_OR_DISTRIB :
    (RwRule.mk [.bool, .bool, .bools, .bool]
      (none)
      (implies' (disj' [var 0, var 1, var 2]) (var 3))
      (conj' [implies' (var 0) (var 3), implies' (disj' [var 1, var 2]) (var 3)])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  obtain ⟨vs, ec⟩ := henv 2 .bools rfl
  obtain ⟨d, ed⟩ := henv 3 .bool rfl
  bool_open at hl ⊢
  simp only [ea, eb, ec, ed, spliceVal, List.cons_append, List.nil_append] at hl ⊢
  rcases hc : Val.bools vs with _ | bs
  · exfalso; apply hl; bool_simp [hc]
  · obtain rfl := bool_bools_map hc
    rcases bs with _ | ⟨c, bs⟩ <;> cases a <;> cases b <;> cases d <;> bool_simp [bool_bools_map_bool]

-- rewrite id 156 (cvc5 `bool-or-and-distrib`, not in BCF's table; one step of the `define-rule*`)
theorem sound_BOOL_OR_AND_DISTRIB :
    (RwRule.mk [.bool, .bool, .bools, .bool, .bools]
      (none)
      (disj' [conj' [var 0, var 1, var 2], var 3, var 4])
      (conj' [disj' [var 0, var 3, var 4], disj' [conj' [var 1, var 2], var 3, var 4]])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ea⟩ := henv 0 .bool rfl
  obtain ⟨b, eb⟩ := henv 1 .bool rfl
  obtain ⟨vs, ec⟩ := henv 2 .bools rfl
  obtain ⟨d, ed⟩ := henv 3 .bool rfl
  obtain ⟨ws, ee⟩ := henv 4 .bools rfl
  bool_open at hl ⊢
  simp only [ea, eb, ec, ed, ee, spliceVal, List.cons_append, List.nil_append] at hl ⊢
  rcases hc : Val.bools vs with _ | bs
  · exfalso; apply hl; bool_simp [hc]
  obtain rfl := bool_bools_map hc
  rcases he : Val.bools ws with _ | cs
  · exfalso; apply hl; rcases bs with _ | ⟨c, bs⟩ <;> bool_simp [he, bool_bools_map_bool]
  obtain rfl := bool_bools_map he
  rcases bs with _ | ⟨c, bs⟩ <;> cases a <;> cases b <;> cases d <;>
    bool_simp [bool_bools_map_bool] <;> exact fun h => Or.inr h

end Bcf
