import Bcf.Rw.Table
import Bcf.Rw.Instantiate
import Bcf.BvLemmas

/-!
# Soundness of each supported rewrite

Each lemma states `RwRule.Sound` for one table entry: under the declared
parameter types and the proved condition, both sides denote the same value.
-/

namespace Bcf

theorem eqv_comm (a b : Val) : Val.eqv a b = Val.eqv b a := by
  cases a <;> cases b <;> simp only [Val.eqv]
  · rename_i n x m y
    by_cases h : m = n
    · subst h; simp [eq_comm]
    · simp [h, Ne.symm h]
  · simp [eq_comm]

/-! ## Boolean rewrites -/

theorem sound_EQ_SYMM :
    (RwRule.mk [.any, .any] none (RwExpr.eq' (.var 0) (.var 1)) (RwExpr.eq' (.var 1) (.var 0))).Sound := by
  intro env _ _ hl hr
  simp only [RwExpr.eq', RwExpr.mk, RwArgs.ofList, denoteE, denoteA, List.append_nil] at hl hr ⊢
  generalize spliceVal (env 0) = s0 at *
  generalize spliceVal (env 1) = s1 at *
  rcases s0 with _ | ⟨a, _ | ⟨b, _ | ⟨e, r0⟩⟩⟩ <;> rcases s1 with _ | ⟨c, _ | ⟨d, _ | ⟨f, r1⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, List.append_nil, appVal, RwOp.reducible,
      RwOp.node, Op.eval, eqEval] at hl ⊢
  all_goals first | rfl | exact absurd rfl hl | skip
  rw [eqv_comm]

theorem sound_DISTINCT_BINARY_ELIM :
    (RwRule.mk [.any, .any] none (RwExpr.neq' (.var 0) (.var 1)) (RwExpr.not' (RwExpr.eq' (.var 0) (.var 1)))).Sound := by
  intro env _ _ hl hr
  simp only [RwExpr.eq', RwExpr.neq', RwExpr.not', RwExpr.mk, RwArgs.ofList, denoteE, denoteA,
    List.append_nil] at hl hr ⊢
  generalize spliceVal (env 0) = s0 at *
  generalize spliceVal (env 1) = s1 at *
  rcases s0 with _ | ⟨a, _ | ⟨b, _ | ⟨e, r0⟩⟩⟩ <;> rcases s1 with _ | ⟨c, _ | ⟨d, _ | ⟨f, r1⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, List.append_nil, appVal, RwOp.reducible,
      RwOp.node, Op.eval, eqEval, spliceVal, boolNotEval] at hl ⊢
  all_goals first | exact absurd rfl hl | skip
  all_goals first
    | generalize hq : Val.eqv a c = q at hl ⊢
    | generalize hq : Val.eqv c d = q at hl ⊢
    | generalize hq : Val.eqv a b = q at hl ⊢
  all_goals (cases q <;> simp at hl ⊢)

/-- Unfold a pattern with boolean parameters. -/
macro "rw_bool" : tactic => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.xor', RwExpr.mk,
  RwArgs.ofList, denoteE, denoteA, spliceVal, List.append_nil, List.singleton_append, List.cons_append,
  List.nil_append, appVal, RwOp.reducible, RwOp.node, Op.eval, eqEval, Val.eqv, boolNotEval, boolN,
  Val.bools, Val.asBool, Bool.false_eq_true, ↓reduceIte])

theorem sound_BOOL_DOUBLE_NOT_ELIM :
    (RwRule.mk [.bool] none (RwExpr.not' (RwExpr.not' (.var 0))) (.var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, hb⟩ := henv 0 .bool rfl
  rw_bool
  simp only [hb]
  try rw_bool
  cases b <;> rfl

theorem sound_BOOL_EQ_TRUE :
    (RwRule.mk [.bool] none (RwExpr.eq' (.var 0) .tt) (.var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, hb⟩ := henv 0 .bool rfl
  rw_bool
  simp only [hb]
  try rw_bool
  cases b <;> rfl

theorem sound_BOOL_EQ_FALSE :
    (RwRule.mk [.bool] none (RwExpr.eq' (.var 0) .ff) (RwExpr.not' (.var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, hb⟩ := henv 0 .bool rfl
  rw_bool
  simp only [hb]
  try rw_bool
  cases b <;> rfl

theorem sound_BOOL_EQ_NREFL :
    (RwRule.mk [.bool] none (RwExpr.eq' (.var 0) (RwExpr.not' (.var 0))) .ff).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, hb⟩ := henv 0 .bool rfl
  rw_bool
  simp only [hb]
  try rw_bool
  cases b <;> rfl

theorem sound_BOOL_XOR_NREFL :
    (RwRule.mk [.bool] none (RwExpr.xor' [.var 0, RwExpr.not' (.var 0)]) .tt).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, hb⟩ := henv 0 .bool rfl
  rw_bool
  simp only [hb]
  try rw_bool
  cases b <;> rfl

theorem sound_BOOL_XOR_FALSE :
    (RwRule.mk [.bool] none (RwExpr.xor' [.var 0, .ff]) (.var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, hb⟩ := henv 0 .bool rfl
  rw_bool
  simp only [hb]
  try rw_bool
  cases b <;> rfl

theorem sound_BOOL_XOR_TRUE :
    (RwRule.mk [.bool] none (RwExpr.xor' [.var 0, .tt]) (RwExpr.not' (.var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨b, hb⟩ := henv 0 .bool rfl
  rw_bool
  simp only [hb]
  try rw_bool
  cases b <;> rfl

theorem sound_BOOL_XOR_COMM :
    (RwRule.mk [.bool, .bool] none (RwExpr.xor' [.var 0, .var 1]) (RwExpr.xor' [.var 1, .var 0])).Sound := by
  intro env henv _ hl hr
  obtain ⟨a, ha⟩ := henv 0 .bool rfl
  obtain ⟨b, hb⟩ := henv 1 .bool rfl
  rw_bool
  simp only [ha, hb]
  try rw_bool
  cases a <;> cases b <;> rfl

/-! ## Bit-vector rewrites: helpers -/

theorem bvValEval_width {w v n : Nat} {x : BitVec n} (h : bvValEval w v [] = .bv n x) : n = w := by
  simp only [bvValEval] at h
  split at h
  · injection h with hn _; exact hn.symm
  · simp at h

theorem bvValEval_val {w v : Nat} {x : BitVec w} (h : bvValEval w v [] = .bv w x) :
    x = BitVec.ofNat w v ∧ w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w := by
  simp only [bvValEval] at h
  split at h
  · rename_i hc; injection h with _ hx; exact ⟨hx.symm, hc⟩
  · simp at h

theorem bvValEval_not_list {w v : Nat} {e : Bool} {vs : List Val} : bvValEval w v [] ≠ .list e vs := by
  simp only [bvValEval]; split <;> simp

theorem bvValEval_not_bool {w v : Nat} {b : Bool} : bvValEval w v [] ≠ .bool b := by
  simp only [bvValEval]; split <;> simp

theorem l0_val : bvValEval 32 0 [] = .bv 32 (BitVec.ofNat 32 0) := by simp [bvValEval]
theorem l1_val : bvValEval 32 1 [] = .bv 32 (BitVec.ofNat 32 1) := by simp [bvValEval]

/-- A true conjunction of two values. -/
theorem conj2_true {a b : Val} (h : appVal .conj [a, b] = .bool true) : a = .bool true ∧ b = .bool true := by
  simp only [appVal, RwOp.node, Op.eval, boolN] at h
  cases a <;> cases b <;> simp [Val.bools] at h
  rename_i x y
  cases x <;> cases y <;> simp_all

/-- Every member of a true conjunction is true. -/
theorem conjN_true {l : List Val} (h : appVal .conj l = .bool true) : ∀ v ∈ l, v = .bool true := by
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · intro v hv; simp at hv
  · simp only [appVal, RwOp.reducible, ↓reduceIte] at h
    intro v hv; simp at hv; subst hv; exact h
  · simp only [appVal, RwOp.node, Op.eval, boolN] at h
    cases hb : Val.bools (a :: b :: rest) with
    | none => rw [hb] at h; simp at h
    | some bs =>
      rw [hb] at h
      by_cases hlen : 2 ≤ bs.length
      · simp only [hlen, ↓reduceIte, Val.bool.injEq] at h
        exact bools_all_true hb h
      · simp only [hlen, ↓reduceIte] at h
        exact Val.noConfusion h

/-- A true equality. -/
theorem eq_true {a b : Val} (h : appVal .eq [a, b] = .bool true) : a = b := by
  simp only [appVal, RwOp.node, Op.eval, eqEval] at h
  split at h
  · rename_i r hr
    simp at h; subst h
    exact (eqv_true_iff.mp hr).1
  · simp at h

/-- `bvsize` of a bit-vector value. -/
theorem bvsize_val {w : Nat} (x : BitVec w) :
    appVal .bvsize [.bv w x] = if w < 2 ^ 32 then .bv 32 (BitVec.ofNat 32 w) else .bad := by
  simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvSizeEval]

/-- Splicing leaves non-list values alone. -/
theorem spliceVal_of_ne {v : Val} (h : ∀ e vs, v ≠ .list e vs) : spliceVal v = [v] := by
  cases v <;> simp_all [spliceVal]

theorem eqEval_ne_list (n : Bool) (vs : List Val) (e : Bool) (l : List Val) : eqEval n vs ≠ .list e l := by
  unfold eqEval; split <;> (try split) <;> simp
theorem bvCmp_ne_list (f : {w : Nat} → BitVec w → BitVec w → Bool) (vs : List Val) (e : Bool) (l : List Val) :
    bvCmp f vs ≠ .list e l := by
  unfold bvCmp; split <;> (try split) <;> simp
theorem bvSizeEval_ne_list (w : Nat) (vs : List Val) (e : Bool) (l : List Val) : bvSizeEval w vs ≠ .list e l := by
  unfold bvSizeEval; split <;> (try split) <;> simp
theorem bvExtractEval_ne_list (hi lo : Nat) (vs : List Val) (e : Bool) (l : List Val) :
    bvExtractEval hi lo vs ≠ .list e l := by
  unfold bvExtractEval; split <;> (try split) <;> simp
theorem bvExtEval_ne_list (s : Bool) (w k : Nat) (vs : List Val) (e : Bool) (l : List Val) :
    bvExtEval s w k vs ≠ .list e l := by
  unfold bvExtEval; split <;> (try split) <;> simp
theorem bvRepeatEval_ne_list (w k : Nat) (vs : List Val) (e : Bool) (l : List Val) :
    bvRepeatEval w k vs ≠ .list e l := by
  unfold bvRepeatEval; split <;> (try split) <;> simp
theorem bvBin_ne_list (w : Nat) (f : BitVec w → BitVec w → BitVec w) (vs : List Val) (e : Bool) (l : List Val) :
    bvBin w f vs ≠ .list e l := by
  unfold bvBin; split <;> (try split) <;> (try split) <;> simp
theorem bvN_ne_list (w : Nat) (f : List (BitVec w) → BitVec w) (vs : List Val) (e : Bool) (l : List Val) :
    bvN w f vs ≠ .list e l := by
  unfold bvN; split <;> (try split) <;> simp
theorem bvConcatEval_ne_list (w : Nat) (vs : List Val) (e : Bool) (l : List Val) : bvConcatEval w vs ≠ .list e l := by
  unfold bvConcatEval; split <;> (try split) <;> simp
theorem bvValEval_ne_list (w v : Nat) (vs : List Val) (e : Bool) (l : List Val) : bvValEval w v vs ≠ .list e l := by
  unfold bvValEval; split <;> (try split) <;> simp
theorem boolNotEval_ne_list (vs : List Val) (e : Bool) (l : List Val) : boolNotEval vs ≠ .list e l := by
  unfold boolNotEval; split <;> simp
theorem boolN_ne_list (f : List Bool → Bool) (vs : List Val) (e : Bool) (l : List Val) : boolN f vs ≠ .list e l := by
  unfold boolN; split <;> (try split) <;> simp

theorem spliceVal_eqEval (n : Bool) (vs : List Val) : spliceVal (eqEval n vs) = [eqEval n vs] :=
  spliceVal_of_ne (fun _ _ => eqEval_ne_list n vs _ _)
theorem spliceVal_bvCmp (f : {w : Nat} → BitVec w → BitVec w → Bool) (vs : List Val) :
    spliceVal (bvCmp f vs) = [bvCmp f vs] := spliceVal_of_ne (fun _ _ => bvCmp_ne_list f vs _ _)
theorem spliceVal_bvSizeEval (w : Nat) (vs : List Val) : spliceVal (bvSizeEval w vs) = [bvSizeEval w vs] :=
  spliceVal_of_ne (fun _ _ => bvSizeEval_ne_list w vs _ _)
theorem spliceVal_bvExtractEval (hi lo : Nat) (vs : List Val) :
    spliceVal (bvExtractEval hi lo vs) = [bvExtractEval hi lo vs] :=
  spliceVal_of_ne (fun _ _ => bvExtractEval_ne_list hi lo vs _ _)
theorem spliceVal_bvExtEval (s : Bool) (w k : Nat) (vs : List Val) :
    spliceVal (bvExtEval s w k vs) = [bvExtEval s w k vs] := spliceVal_of_ne (fun _ _ => bvExtEval_ne_list s w k vs _ _)
theorem spliceVal_bvRepeatEval (w k : Nat) (vs : List Val) :
    spliceVal (bvRepeatEval w k vs) = [bvRepeatEval w k vs] := spliceVal_of_ne (fun _ _ => bvRepeatEval_ne_list w k vs _ _)
theorem spliceVal_bvBin (w : Nat) (f : BitVec w → BitVec w → BitVec w) (vs : List Val) :
    spliceVal (bvBin w f vs) = [bvBin w f vs] := spliceVal_of_ne (fun _ _ => bvBin_ne_list w f vs _ _)
theorem spliceVal_bvN (w : Nat) (f : List (BitVec w) → BitVec w) (vs : List Val) :
    spliceVal (bvN w f vs) = [bvN w f vs] := spliceVal_of_ne (fun _ _ => bvN_ne_list w f vs _ _)
theorem spliceVal_bvConcatEval (w : Nat) (vs : List Val) : spliceVal (bvConcatEval w vs) = [bvConcatEval w vs] :=
  spliceVal_of_ne (fun _ _ => bvConcatEval_ne_list w vs _ _)
theorem spliceVal_bvValEval (w v : Nat) (vs : List Val) : spliceVal (bvValEval w v vs) = [bvValEval w v vs] :=
  spliceVal_of_ne (fun _ _ => bvValEval_ne_list w v vs _ _)
theorem spliceVal_boolNotEval (vs : List Val) : spliceVal (boolNotEval vs) = [boolNotEval vs] :=
  spliceVal_of_ne (fun _ _ => boolNotEval_ne_list vs _ _)
theorem spliceVal_boolN (f : List Bool → Bool) (vs : List Val) : spliceVal (boolN f vs) = [boolN f vs] :=
  spliceVal_of_ne (fun _ _ => boolN_ne_list f vs _ _)

syntax "rw_bv" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rw_bv $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.ult', RwExpr.ule', RwExpr.slt',
      RwExpr.sle', RwExpr.sge', RwExpr.conj', RwExpr.bvsub', RwExpr.bvadd', RwExpr.bvmul', RwExpr.bvshl',
      RwExpr.bvashr', RwExpr.bvand', RwExpr.bvor', RwExpr.concat', RwExpr.bvsize', RwExpr.l0, RwExpr.l1,
      RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, appVal, RwOp.reducible, RwOp.node,
      RwOp.widthV, RwOp.width, firstBv, sumBv, Val.tys, Val.ty, mapOpt, Op.eval, eqEval, Val.eqv, boolNotEval, bvCmp,
      Bool.false_eq_true, ↓reduceIte, l0_val, l1_val, BitVec.toNat_ofNat, Nat.zero_mod, Nat.one_mod_eq_one,
      spliceVal_eqEval, spliceVal_bvCmp, spliceVal_bvSizeEval, spliceVal_bvExtractEval, spliceVal_bvExtEval,
      spliceVal_bvRepeatEval, spliceVal_bvBin, spliceVal_bvN, spliceVal_bvConcatEval, spliceVal_bvValEval,
      spliceVal_boolNotEval, spliceVal_boolN] $[$loc]?)

/-- Case analysis on a literal built by `symVal`/`bvmax`: leaves the `bv` goal, then the `bad` goal. -/
macro "lit_cases" hlit:ident ":" e:term : tactic => `(tactic|
  (cases $hlit:ident : $e
   case bool => exact absurd $hlit bvValEval_not_bool
   case list => exact absurd $hlit bvValEval_not_list))

/-! ## Comparison rewrites -/

theorem sound_BV_SLE_ELIMINATE :
    (RwRule.mk [.bvq, .bvq] none (RwExpr.sle' (.var 0) (.var 1)) (RwExpr.not' (RwExpr.slt' (.var 1) (.var 0)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  rw_bv at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  rw_bv at hl hr ⊢
  by_cases h : w' = w
  · subst h; simp [BitVec.sle_eq_not_slt]
  · simp [h] at hl

theorem sound_BV_ULE_ELIMINATE :
    (RwRule.mk [.bvq, .bvq] none (RwExpr.ule' (.var 0) (.var 1)) (RwExpr.not' (RwExpr.ult' (.var 1) (.var 0)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  rw_bv at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  rw_bv at hl hr ⊢
  by_cases h : w' = w
  · subst h; simp [BitVec.ule_eq_not_ult]
  · simp [h] at hl

theorem sound_BV_NOT_ULT :
    (RwRule.mk [.bvq, .bvq] none (RwExpr.not' (RwExpr.ult' (.var 0) (.var 1))) (RwExpr.ule' (.var 1) (.var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  rw_bv at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  rw_bv at hl hr ⊢
  by_cases h : w' = w
  · subst h; simp [BitVec.ule_eq_not_ult]
  · simp [h] at hl

theorem sound_BV_ULT_ZERO_2 :
    (RwRule.mk [.bvq, .bv 32] none (RwExpr.ult' (.var 0) (RwExpr.symVal RwExpr.l0 (.var 1))) .ff).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  rw_bv at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  rw_bv at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, hw64, hv⟩ := bvValEval_val hlit
    by_cases h : k.toNat = w
    · subst h; simp [ult_zero]
    · simp [h] at hl
  · simp [hlit] at hl

theorem sound_BV_ULT_ZERO_1 :
    (RwRule.mk [.bvq, .bv 32] none (RwExpr.ult' (RwExpr.symVal RwExpr.l0 (.var 1)) (.var 0))
      (RwExpr.not' (RwExpr.eq' (.var 0) (RwExpr.symVal RwExpr.l0 (.var 1))))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  rw_bv at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  rw_bv at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl hr ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, hw64, hv⟩ := bvValEval_val hlit
    by_cases h : k.toNat = w
    · subst h; simp [zero_ult]
    · simp [Ne.symm h] at hl
  · simp [hlit] at hl

theorem sound_BV_ULE_ZERO :
    (RwRule.mk [.bvq, .bv 32] none (RwExpr.ule' (.var 0) (RwExpr.symVal RwExpr.l0 (.var 1)))
      (RwExpr.eq' (.var 0) (RwExpr.symVal RwExpr.l0 (.var 1)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  rw_bv at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  rw_bv at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl hr ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, hw64, hv⟩ := bvValEval_val hlit
    by_cases h : k.toNat = w
    · subst h; simp [ule_zero]
    · simp [h] at hl
  · simp [hlit] at hl

theorem sound_BV_ULT_ONE :
    (RwRule.mk [.bvq, .bv 32] none (RwExpr.ult' (.var 0) (RwExpr.symVal RwExpr.l1 (.var 1)))
      (RwExpr.eq' (.var 0) (RwExpr.symVal RwExpr.l0 (.var 1)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  rw_bv at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  rw_bv at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 1 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, hw64, hv⟩ := bvValEval_val hlit
    lit_cases hlit0 : bvValEval k.toNat 0 []
    · simp only [hlit0] at hr ⊢
      obtain rfl := bvValEval_width hlit0
      obtain ⟨rfl, _, _, _⟩ := bvValEval_val hlit0
      by_cases h : k.toNat = w
      · subst h; simp only [↓reduceDIte, BitVec.cast_eq]; congr 1; exact ult_one (by omega) x
      · simp [h] at hl
    · simp [hlit0] at hr
  · simp [hlit] at hl

/-! ## Extract, extend, size rewrites -/

theorem conj2_true' {a b : Val} (h : boolN (fun l => l.all id) [a, b] = .bool true) : a = .bool true ∧ b = .bool true := by
  cases a <;> cases b <;> simp [boolN, Val.bools] at h
  rename_i x y; cases x <;> cases y <;> simp_all

theorem eq_true' {a b : Val} (h : eqEval false [a, b] = .bool true) : a = b := by
  simp only [eqEval] at h
  split at h
  · rename_i r hr; simp at h; subst h; exact (eqv_true_iff.mp hr).1
  · simp at h

theorem two32 : (2 : Nat) ^ 32 = 4294967296 := by decide
theorem two31 : (2 : Nat) ^ 31 = 2147483648 := by decide

/-- Signed comparisons of small non-negative 32-bit values are unsigned. -/
theorem sle_small {a b : BitVec 32} (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) :
    a.sle b = decide (a.toNat ≤ b.toNat) := by
  have hma : a.msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  have hmb : b.msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  simp only [BitVec.sle, BitVec.toInt_eq_msb_cond, hma, hmb, Bool.false_eq_true, ↓reduceIte]
  simp

theorem slt_small {a b : BitVec 32} (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) :
    a.slt b = decide (a.toNat < b.toNat) := by
  have hma : a.msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  have hmb : b.msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  simp only [BitVec.slt, BitVec.toInt_eq_msb_cond, hma, hmb, Bool.false_eq_true, ↓reduceIte]
  simp

theorem bvsize_reduce {w : Nat} (x : BitVec w) (hw : w < 2 ^ 32) :
    bvSizeEval 32 [.bv w x] = .bv 32 (BitVec.ofNat 32 w) := by
  simp [bvSizeEval, hw]

theorem sub32 (a b : BitVec 32) : bvBin 32 (· - ·) [.bv 32 a, .bv 32 b] = .bv 32 (a - b) := by
  simp [bvBin]

theorem add32 (a b : BitVec 32) : bvN 32 (List.foldl (· + ·) 0) [.bv 32 a, .bv 32 b] = .bv 32 (a + b) := by
  simp [bvN, Val.bvs, BitVec.zero_add]

theorem toNat_ofNat32 {w : Nat} (hw : w < 2 ^ 32) : (BitVec.ofNat 32 w).toNat = w := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hw

theorem spliceVal_bv (w : Nat) (x : BitVec w) : spliceVal (.bv w x) = [.bv w x] := rfl
theorem spliceVal_bool (b : Bool) : spliceVal (.bool b) = [.bool b] := rfl
theorem spliceVal_bad : spliceVal .bad = [.bad] := rfl
theorem spliceVal_list (e : Bool) (vs : List Val) : spliceVal (.list e vs) = vs := rfl

/-- Structural unfolding: evaluators stay folded. -/
syntax "rw_bvs" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rw_bvs $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.ult', RwExpr.ule', RwExpr.slt',
      RwExpr.sle', RwExpr.sge', RwExpr.conj', RwExpr.bvsub', RwExpr.bvadd', RwExpr.bvmul', RwExpr.bvshl',
      RwExpr.bvashr', RwExpr.bvand', RwExpr.bvor', RwExpr.concat', RwExpr.bvsize', RwExpr.l0, RwExpr.l1,
      RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal_bv, spliceVal_bool, spliceVal_bad, spliceVal_list,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, appVal, RwOp.reducible, RwOp.node,
      RwOp.widthV, RwOp.width, firstBv, sumBv, Val.tys, Val.ty, mapOpt, Op.eval,
      Bool.false_eq_true, ↓reduceIte, l0_val, l1_val, BitVec.toNat_ofNat, Nat.zero_mod, Nat.one_mod_eq_one,
      spliceVal_eqEval, spliceVal_bvCmp, spliceVal_bvSizeEval, spliceVal_bvExtractEval, spliceVal_bvExtEval,
      spliceVal_bvRepeatEval, spliceVal_bvBin, spliceVal_bvN, spliceVal_bvConcatEval, spliceVal_bvValEval,
      spliceVal_boolNotEval, spliceVal_boolN] $[$loc]?)

theorem sound_BV_ULE_MAX : (RwRule.mk [.bvq, .bv 32, .bv 32]
    (some (RwExpr.conj' [RwExpr.eq' (.var 2) (RwExpr.bvsize' (.var 0)),
                         RwExpr.eq' (.var 1) (RwExpr.bvmax (RwExpr.bvsize' (.var 0)))]))
    (RwExpr.ule' (.var 0) (RwExpr.symVal (.var 1) (.var 2))) .tt).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, hk2⟩ := henv 2 (.bv 32) rfl
  have hc := hcond _ rfl
  have h32 : w < 2 ^ 32 := Nat.lt_of_le_of_lt hwb (by decide)
  rw_bvs at hc hl hr ⊢
  simp only [hx, hk1, hk2] at hc hl hr ⊢
  rw_bvs at hc hl hr ⊢
  simp only [bvsize_reduce x h32, toNat_ofNat32 h32] at hc
  rw_bvs at hc
  obtain ⟨hc1, hc2⟩ := conj2_true' hc
  have e1 := eq_true' hc1
  have e2 := eq_true' hc2
  injection e1 with _ e1
  lit_cases hlit : bvValEval w (2 ^ w - 1) []
  · obtain rfl := bvValEval_width hlit
    rw [hlit] at e2
    injection e2 with hw32 e2
    subst hw32
    obtain ⟨rfl, _, _, _⟩ := bvValEval_val hlit
    subst e1; subst e2
    simp only [toNat_ofNat32 (by decide : 32 < 2 ^ 32)]
    rw [toNat_ofNat32 (by rw [two32]; decide)]
    simp only [bvValEval, show (32 : Nat) ≤ 64 by decide,
      show 2 ^ 32 - 1 < 2 ^ 32 by rw [two32]; decide, and_self, bvCmp]
    rw [ite_eq_left ⟨by decide, trivial⟩]
    simp only [↓reduceDIte, BitVec.cast_eq]
    rw [ule_allOnes']
  · rw [hlit] at e2; exact absurd e2 (by simp)

theorem sound_BV_ZERO_EXTEND_ELIMINATE : (RwRule.mk [.bvq, .bv 32] none (RwExpr.zext (.var 1) (.var 0))
    (RwExpr.concat' [RwExpr.symVal RwExpr.l0 (.var 1), .var 0])).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  rw_bv at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  rw_bv at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hr ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, hw64, hv⟩ := bvValEval_val hlit
    rw_bv at hl hr ⊢
    simp only [bvExtEval, bvConcatEval, Val.concatVals, List.length_cons, List.length_nil, Nat.add_zero,
      and_true, Bool.false_eq_true, ↓reduceIte] at hl hr ⊢
    have hw : w + k.toNat ≠ 0 := by omega
    rw [ite_eq_left hw, dite_eq_left ⟨by omega, trivial, by omega⟩]
    rw [bv_cast_eq (show w + k.toNat = k.toNat + w by omega)]
    congr 1
    apply bv_ext
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_zero]
    by_cases hiw : i < w
    · simp [hiw, show i < w + k.toNat by omega]
    · simp [hiw, BitVec.getLsbD_of_ge x i (by omega)]
  · simp [hlit, bvConcatEval, Val.concatVals] at hr

/-- Structural unfolding without `Op.eval` (widths are resolved first). -/
syntax "rw_bvn" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rw_bvn $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.ult', RwExpr.ule', RwExpr.slt',
      RwExpr.sle', RwExpr.sge', RwExpr.conj', RwExpr.bvsub', RwExpr.bvadd', RwExpr.bvmul', RwExpr.bvshl',
      RwExpr.bvashr', RwExpr.bvand', RwExpr.bvor', RwExpr.concat', RwExpr.bvsize', RwExpr.l0, RwExpr.l1,
      RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal_bv, spliceVal_bool, spliceVal_bad, spliceVal_list,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, appVal, RwOp.reducible, RwOp.node,
      RwOp.widthV, RwOp.width, firstBv, sumBv, Val.tys, Val.ty, mapOpt,
      Bool.false_eq_true, ↓reduceIte, l0_val, l1_val, BitVec.toNat_ofNat, Nat.zero_mod, Nat.one_mod_eq_one,
      spliceVal_eqEval, spliceVal_bvCmp, spliceVal_bvSizeEval, spliceVal_bvExtractEval, spliceVal_bvExtEval,
      spliceVal_bvRepeatEval, spliceVal_bvBin, spliceVal_bvN, spliceVal_bvConcatEval, spliceVal_bvValEval,
      spliceVal_boolNotEval, spliceVal_boolN] $[$loc]?)

theorem bvsize_reduce' {w : Nat} (x : BitVec w) (hw : w < 2 ^ 32) (ρ : Assign) :
    Op.eval ρ (.bvSize 32) [.bv w x] = .bv 32 (BitVec.ofNat 32 w) := by
  simp [Op.eval, bvSizeEval, hw]

theorem toNat_sub_one32 {w : Nat} (hw1 : 1 ≤ w) (hw : w < 2 ^ 32) :
    (BitVec.ofNat 32 w - BitVec.ofNat 32 1).toNat = w - 1 := by
  rw [BitVec.toNat_sub_of_le]
  · rw [toNat_ofNat32 hw, toNat_ofNat32 (by rw [two32]; decide)]
  · rw [BitVec.le_def, toNat_ofNat32 hw, toNat_ofNat32 (by rw [two32]; decide)]; exact hw1

theorem toNat_add32 (a b : BitVec 32) (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem sound_BV_EXTRACT_WHOLE : (RwRule.mk [.bvq, .bv 32] (some (RwExpr.sge' (.var 1) (RwExpr.bvsub' (RwExpr.bvsize' (.var 0)) RwExpr.l1)))
    (RwExpr.extract (.var 1) RwExpr.l0 (.var 0)) (.var 0)).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  have hc := hcond _ rfl
  have h32 : w < 2 ^ 32 := Nat.lt_of_le_of_lt hwb (by decide)
  rw_bvn at hc hl hr ⊢
  simp only [hx, hk] at hc hl hr ⊢
  rw_bvn at hc hl hr ⊢
  simp only [bvsize_reduce' x h32] at hc
  rw_bvn at hc
  simp only [Op.eval, sub32, spliceVal_bv, bvCmp, ↓reduceDIte, BitVec.cast_eq, Val.bool.injEq] at hc
  simp only [bvExtractEval] at hl ⊢
  have hkw : k.toNat < w := by
    cases Nat.lt_or_ge k.toNat w with
    | inl h => exact h
    | inr h => simp [Nat.not_lt.mpr h] at hl
  have hw1 : 1 ≤ w := by omega
  rw [sle_small (by rw [toNat_sub_one32 hw1 h32]; omega) (by omega)] at hc
  rw [toNat_sub_one32 hw1 h32] at hc
  simp only [decide_eq_true_eq] at hc
  rw [ite_eq_left ⟨Nat.zero_le _, hkw⟩]
  rw [bv_cast_eq (show k.toNat - 0 + 1 = w by omega)]
  congr 1
  apply bv_ext
  intro i hi
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb]
  simp only [Nat.zero_add]
  rw [decide_eq_true (show i < k.toNat - 0 + 1 by omega), Bool.true_and]

theorem sound_BV_EXTRACT_SIGN_EXTEND_1 : (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32] (some (RwExpr.slt' (.var 2) (RwExpr.bvsize' (.var 0))))
    (RwExpr.extract (.var 2) (.var 1) (RwExpr.sext (.var 3) (.var 0))) (RwExpr.extract (.var 2) (.var 1) (.var 0))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, hk2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, hk3⟩ := henv 3 (.bv 32) rfl
  rw_bvn at hl hr ⊢
  simp only [hx, hk1, hk2, hk3] at hl hr ⊢
  try rw_bvn at hl hr ⊢
  simp only [bvExtractEval] at hr
  have hr' : k1.toNat ≤ k2.toNat ∧ k2.toNat < w := by
    by_cases hh : k1.toNat ≤ k2.toNat ∧ k2.toNat < w
    · exact hh
    · simp [hh] at hr
  have hw : w + k3.toNat ≠ 0 := by omega
  simp only [bvExtEval, hw, ne_eq, not_false_eq_true, true_and, ↓reduceIte] at hl ⊢
  simp only [bvExtractEval] at hl ⊢
  rw [ite_eq_left ⟨hr'.1, by omega⟩, ite_eq_left hr']
  congr 1
  apply bv_ext
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend]
  by_cases hi' : i < k2.toNat - k1.toNat + 1
  · simp [hi', show k1.toNat + i < w + k3.toNat by omega, show k1.toNat + i < w by omega]
  · simp [hi']

theorem sound_BV_EXTRACT_EXTRACT : (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
    (some (RwExpr.conj' [RwExpr.eq' (.var 5) (RwExpr.bvadd' [.var 1, .var 4]), RwExpr.eq' (.var 6) (RwExpr.bvadd' [.var 1, .var 3])]))
    (RwExpr.extract (.var 4) (.var 3) (RwExpr.extract (.var 2) (.var 1) (.var 0)))
    (RwExpr.extract (.var 5) (.var 6) (.var 0))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, hk2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, hk3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, hk4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, hk5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, hk6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_bvn at hc hl hr ⊢
  simp only [hx, hk1, hk2, hk3, hk4, hk5, hk6] at hc hl hr ⊢
  rw_bvn at hc hl hr ⊢
  simp only [Op.eval, add32] at hc
  obtain ⟨hc1, hc2⟩ := conj2_true' hc
  have e5 := eq_true' hc1
  have e6 := eq_true' hc2
  injection e5 with _ e5
  injection e6 with _ e6
  subst e5; subst e6
  simp only [bvExtractEval] at hl hr ⊢
  have hin : k1.toNat ≤ k2.toNat ∧ k2.toNat < w := by
    by_cases hh : k1.toNat ≤ k2.toNat ∧ k2.toNat < w
    · exact hh
    · simp [hh] at hl
  simp only [hin, and_self, ↓reduceIte] at hl ⊢
  have hout : k3.toNat ≤ k4.toNat ∧ k4.toNat < k2.toNat - k1.toNat + 1 := by
    by_cases hh : k3.toNat ≤ k4.toNat ∧ k4.toNat < k2.toNat - k1.toNat + 1
    · exact hh
    · simp [hh] at hl
  have h14 : (k1 + k4).toNat = k1.toNat + k4.toNat := toNat_add32 _ _ (by rw [two32]; omega)
  have h13 : (k1 + k3).toNat = k1.toNat + k3.toNat := toNat_add32 _ _ (by rw [two32]; omega)
  rw [ite_eq_left hout, h14, h13, ite_eq_left ⟨by omega, by omega⟩]
  rw [bv_cast_eq (show k4.toNat - k3.toNat + 1 = k1.toNat + k4.toNat - (k1.toNat + k3.toNat) + 1 by omega)]
  congr 1
  apply bv_ext
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb]
  by_cases hi' : i < k4.toNat - k3.toNat + 1
  · simp [hi', show k3.toNat + i < k2.toNat - k1.toNat + 1 by omega,
      show i < k1.toNat + k4.toNat - (k1.toNat + k3.toNat) + 1 by omega, Nat.add_assoc]
  · simp [hi', show ¬ i < k1.toNat + k4.toNat - (k1.toNat + k3.toNat) + 1 by omega]

end Bcf
