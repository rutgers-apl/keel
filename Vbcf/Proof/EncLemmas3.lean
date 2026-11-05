import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.EncLemmas2

/-!
# Vbcf proofs: typing facts, the type encoding, and injectivity of the node encoding

Part 3 of `Vbcf/Proof/EncLemmas.lean`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ## F. Typing facts

### Inversion of the typing combinators -/

theorem tyGuard_eq_some {p : Prop} [Decidable p] {t t' : Ty} :
    tyGuard p t = some t' ↔ p ∧ t' = t := by
  unfold tyGuard
  by_cases h : p <;> simp [h, eq_comm]

theorem bvVarTy_eq_some {w : Nat} {a : List Ty} {t : Ty} :
    bvVarTy w a = some t ↔ a = [] ∧ w ≠ 0 ∧ t = .bv w := by
  rcases a with _ | ⟨x, r⟩ <;> simp [bvVarTy, tyGuard_eq_some]

theorem bvValTy_eq_some {w v : Nat} {a : List Ty} {t : Ty} :
    bvValTy w v a = some t ↔ a = [] ∧ (w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w) ∧ t = .bv w := by
  rcases a with _ | ⟨x, r⟩ <;> simp [bvValTy, tyGuard_eq_some]

theorem bvIteTy_eq_some {w : Nat} {a : List Ty} {t : Ty} :
    bvIteTy w a = some t ↔
      ∃ c, a = [c, .bv w, .bv w] ∧ w ≠ 0 ∧ (c = .bool ∨ c = .bv 1) ∧ t = .bv w := by
  rcases a with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, r⟩⟩⟩⟩ <;>
    simp [bvIteTy, tyGuard_eq_some, and_assoc, and_left_comm, and_comm]

theorem bvUnTy_eq_some {w : Nat} {a : List Ty} {t : Ty} :
    bvUnTy w a = some t ↔ a = [.bv w] ∧ w ≠ 0 ∧ t = .bv w := by
  rcases a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;>
    simp [bvUnTy, tyGuard_eq_some, and_assoc, and_left_comm, and_comm]

theorem bvExtractTy_eq_some {hi lo : Nat} {a : List Ty} {t : Ty} :
    bvExtractTy hi lo a = some t ↔
      ∃ m, a = [.bv m] ∧ lo ≤ hi ∧ hi < m ∧ t = .bv (hi - lo + 1) := by
  rcases a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> try cases x
  all_goals simp [bvExtractTy, tyGuard_eq_some, and_assoc]

theorem bvExtTy_eq_some {w e : Nat} {a : List Ty} {t : Ty} :
    bvExtTy w e a = some t ↔ ∃ m, a = [.bv m] ∧ w ≠ 0 ∧ m + e = w ∧ t = .bv w := by
  rcases a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> try cases x
  all_goals simp [bvExtTy, tyGuard_eq_some, and_assoc]

theorem bvSizeTy_eq_some {w : Nat} {a : List Ty} {t : Ty} :
    bvSizeTy w a = some t ↔ ∃ m, a = [.bv m] ∧ w ≠ 0 ∧ m < 2 ^ w ∧ t = .bv w := by
  rcases a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> try cases x
  all_goals simp [bvSizeTy, tyGuard_eq_some, and_assoc]

theorem bvRepeatTy_eq_some {w k : Nat} {a : List Ty} {t : Ty} :
    bvRepeatTy w k a = some t ↔ ∃ m, a = [.bv m] ∧ w ≠ 0 ∧ m * k = w ∧ t = .bv w := by
  rcases a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> try cases x
  all_goals simp [bvRepeatTy, tyGuard_eq_some, and_assoc]

theorem bvBinTy_eq_some {w : Nat} {a : List Ty} {t : Ty} :
    bvBinTy w a = some t ↔ a = [.bv w, .bv w] ∧ w ≠ 0 ∧ t = .bv w := by
  rcases a with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;>
    simp [bvBinTy, tyGuard_eq_some, and_assoc, and_left_comm, and_comm]

theorem bvNTy_eq_some {w : Nat} {a : List Ty} {t : Ty} :
    bvNTy w a = some t ↔ w ≠ 0 ∧ allBv w a = true ∧ 2 ≤ a.length ∧ t = .bv w := by
  simp [bvNTy, tyGuard_eq_some, and_assoc]

theorem bvConcatTy_eq_some {w : Nat} {a : List Ty} {t : Ty} :
    bvConcatTy w a = some t ↔ w ≠ 0 ∧ bvWidths a = some w ∧ 2 ≤ a.length ∧ t = .bv w := by
  simp [bvConcatTy, tyGuard_eq_some, and_assoc]

theorem bvFromBoolTy_eq_some {a : List Ty} {t : Ty} :
    bvFromBoolTy a = some t ↔ allBool a = true ∧ 1 ≤ a.length ∧ t = .bv a.length := by
  simp [bvFromBoolTy, tyGuard_eq_some, and_assoc]

theorem boolNullTy_eq_some {a : List Ty} {t : Ty} :
    boolNullTy a = some t ↔ a = [] ∧ t = .bool := by
  rcases a with _ | ⟨x, r⟩ <;> simp [boolNullTy, eq_comm]

theorem boolNotTy_eq_some {a : List Ty} {t : Ty} :
    boolNotTy a = some t ↔ a = [.bool] ∧ t = .bool := by
  rcases a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [boolNotTy, tyGuard_eq_some]

theorem bitofTy_eq_some {i : Nat} {a : List Ty} {t : Ty} :
    bitofTy i a = some t ↔ ∃ m, a = [.bv m] ∧ i < m ∧ t = .bool := by
  rcases a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> try cases x
  all_goals simp [bitofTy, tyGuard_eq_some]

theorem eqTy_eq_some {a : List Ty} {t : Ty} :
    eqTy a = some t ↔ ∃ x, a = [x, x] ∧ x.isScalar = true ∧ t = .bool := by
  rcases a with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;>
    simp [eqTy, tyGuard_eq_some, and_assoc]
  intro _ _; exact eq_comm

theorem cmpTy_eq_some {a : List Ty} {t : Ty} :
    cmpTy a = some t ↔ ∃ m, a = [.bv m, .bv m] ∧ t = .bool := by
  rcases a with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> try (cases x <;> cases y)
  all_goals simp [cmpTy, tyGuard_eq_some, Ty.sameBv]
  intro _; exact eq_comm

theorem impliesTy_eq_some {a : List Ty} {t : Ty} :
    impliesTy a = some t ↔ a = [.bool, .bool] ∧ t = .bool := by
  rcases a with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> simp [impliesTy, tyGuard_eq_some]

theorem boolIteTy_eq_some {a : List Ty} {t : Ty} :
    boolIteTy a = some t ↔ a = [.bool, .bool, .bool] ∧ t = .bool := by
  rcases a with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, r⟩⟩⟩⟩ <;> simp [boolIteTy, tyGuard_eq_some]

theorem boolNTy_eq_some {a : List Ty} {t : Ty} :
    boolNTy a = some t ↔ allBool a = true ∧ 2 ≤ a.length ∧ t = .bool := by
  simp [boolNTy, tyGuard_eq_some, and_assoc]

theorem listTy_eq_some {e : Bool} {a : List Ty} {t : Ty} :
    listTy e a = some t ↔ a.all (Ty.inClass e) = true ∧ t = .list e a.length := by
  simp only [listTy, tyGuard_eq_some]


/-! ### Result type and arity of an operator -/

/-- The result type of a well-typed application of `op` to `k` arguments. -/
def opTy (op : Op) (k : Nat) : Ty :=
  if isBoolOp op then .bool else
  match op with
  | .listVal e => .list e k
  | .bvExtract hi lo => .bv (hi - lo + 1)
  | .bvFromBool => .bv k
  | _ => .bv (opLo op)

/-- The least number of arguments of a well-typed application. -/
def minArity : Op → Nat
  | .bvVar _ _ => 0
  | .bvVal _ _ => 0
  | .boolVal _ => 0
  | .boolVar _ => 0
  | .listVal _ => 0
  | .bvNeg _ => 1
  | .bvNot _ => 1
  | .bvExtract _ _ => 1
  | .bvSignExtend _ _ => 1
  | .bvZeroExtend _ _ => 1
  | .bvSize _ => 1
  | .bvRepeat _ _ => 1
  | .boolNot => 1
  | .boolBitof _ => 1
  | .bvFromBool => 1
  | .bvIte _ => 3
  | .boolIte => 3
  | _ => 2

/-- A well-typed application has exactly `minArity` arguments. -/
def fixedArity : Op → Bool
  | .bvAdd _ => false
  | .bvMul _ => false
  | .bvOr _ => false
  | .bvAnd _ => false
  | .bvXor _ => false
  | .bvConcat _ => false
  | .conj => false
  | .disj => false
  | .boolXor => false
  | .bvFromBool => false
  | .listVal _ => false
  | _ => true

/-- What a typing combinator says about the result type and the number of arguments. -/
def TySpec (f : List Ty → Option Ty) (ty : Nat → Ty) (min : Nat) (fixed : Bool) : Prop :=
  ∀ a t, f a = some t →
    t = ty a.length ∧ min ≤ a.length ∧ (fixed = true → a.length = min) ∧ ∀ w, t = .bv w → 1 ≤ w

theorem bvVarTy_spec (w : Nat) : TySpec (bvVarTy w) (fun _ => .bv w) 0 true := by
  intro a t h
  obtain ⟨rfl, hw, rfl⟩ := bvVarTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvValTy_spec (w v : Nat) : TySpec (bvValTy w v) (fun _ => .bv w) 0 true := by
  intro a t h
  obtain ⟨rfl, hw, rfl⟩ := bvValTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvIteTy_spec (w : Nat) : TySpec (bvIteTy w) (fun _ => .bv w) 3 true := by
  intro a t h
  obtain ⟨c, rfl, hw, _, rfl⟩ := bvIteTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvUnTy_spec (w : Nat) : TySpec (bvUnTy w) (fun _ => .bv w) 1 true := by
  intro a t h
  obtain ⟨rfl, hw, rfl⟩ := bvUnTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvExtractTy_spec (hi lo : Nat) :
    TySpec (bvExtractTy hi lo) (fun _ => .bv (hi - lo + 1)) 1 true := by
  intro a t h
  obtain ⟨m, rfl, _, _, rfl⟩ := bvExtractTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvExtTy_spec (w e : Nat) : TySpec (bvExtTy w e) (fun _ => .bv w) 1 true := by
  intro a t h
  obtain ⟨m, rfl, hw, _, rfl⟩ := bvExtTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvSizeTy_spec (w : Nat) : TySpec (bvSizeTy w) (fun _ => .bv w) 1 true := by
  intro a t h
  obtain ⟨m, rfl, hw, _, rfl⟩ := bvSizeTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvRepeatTy_spec (w k : Nat) : TySpec (bvRepeatTy w k) (fun _ => .bv w) 1 true := by
  intro a t h
  obtain ⟨m, rfl, hw, _, rfl⟩ := bvRepeatTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvBinTy_spec (w : Nat) : TySpec (bvBinTy w) (fun _ => .bv w) 2 true := by
  intro a t h
  obtain ⟨rfl, hw, rfl⟩ := bvBinTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e; omega⟩

theorem bvNTy_spec (w : Nat) : TySpec (bvNTy w) (fun _ => .bv w) 2 false := by
  intro a t h
  obtain ⟨hw, _, hl, rfl⟩ := bvNTy_eq_some.mp h
  exact ⟨rfl, hl, (fun h => by cases h), fun w' e => by cases e; omega⟩

theorem bvConcatTy_spec (w : Nat) : TySpec (bvConcatTy w) (fun _ => .bv w) 2 false := by
  intro a t h
  obtain ⟨hw, _, hl, rfl⟩ := bvConcatTy_eq_some.mp h
  exact ⟨rfl, hl, (fun h => by cases h), fun w' e => by cases e; omega⟩

theorem bvFromBoolTy_spec : TySpec bvFromBoolTy (fun k => .bv k) 1 false := by
  intro a t h
  obtain ⟨_, hl, rfl⟩ := bvFromBoolTy_eq_some.mp h
  exact ⟨rfl, hl, (fun h => by cases h), fun w' e => by cases e; omega⟩

theorem boolNullTy_spec : TySpec boolNullTy (fun _ => .bool) 0 true := by
  intro a t h
  obtain ⟨rfl, rfl⟩ := boolNullTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e⟩

theorem boolNotTy_spec : TySpec boolNotTy (fun _ => .bool) 1 true := by
  intro a t h
  obtain ⟨rfl, rfl⟩ := boolNotTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e⟩

theorem bitofTy_spec (i : Nat) : TySpec (bitofTy i) (fun _ => .bool) 1 true := by
  intro a t h
  obtain ⟨m, rfl, _, rfl⟩ := bitofTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e⟩

theorem eqTy_spec : TySpec eqTy (fun _ => .bool) 2 true := by
  intro a t h
  obtain ⟨x, rfl, _, rfl⟩ := eqTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e⟩

theorem cmpTy_spec : TySpec cmpTy (fun _ => .bool) 2 true := by
  intro a t h
  obtain ⟨m, rfl, rfl⟩ := cmpTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e⟩

theorem impliesTy_spec : TySpec impliesTy (fun _ => .bool) 2 true := by
  intro a t h
  obtain ⟨rfl, rfl⟩ := impliesTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e⟩

theorem boolIteTy_spec : TySpec boolIteTy (fun _ => .bool) 3 true := by
  intro a t h
  obtain ⟨rfl, rfl⟩ := boolIteTy_eq_some.mp h
  exact ⟨rfl, Nat.le_refl _, fun _ => rfl, fun w' e => by cases e⟩

theorem boolNTy_spec : TySpec boolNTy (fun _ => .bool) 2 false := by
  intro a t h
  obtain ⟨_, hl, rfl⟩ := boolNTy_eq_some.mp h
  exact ⟨rfl, hl, (fun h => by cases h), fun w' e => by cases e⟩

theorem listTy_spec (e : Bool) : TySpec (listTy e) (fun k => .list e k) 0 false := by
  intro a t h
  obtain ⟨_, rfl⟩ := listTy_eq_some.mp h
  exact ⟨rfl, Nat.zero_le _, (fun h => by cases h), fun w' e => by cases e⟩

theorem resultTy_spec (op : Op) :
    TySpec op.resultTy (opTy op) (minArity op) (fixedArity op) := by
  cases op <;> first
    | exact bvVarTy_spec _ | exact bvValTy_spec _ _ | exact bvIteTy_spec _ | exact bvUnTy_spec _
    | exact bvExtractTy_spec _ _ | exact bvExtTy_spec _ _ | exact bvSizeTy_spec _
    | exact bvRepeatTy_spec _ _ | exact bvBinTy_spec _ | exact bvNTy_spec _
    | exact bvConcatTy_spec _ | exact bvFromBoolTy_spec | exact boolNullTy_spec
    | exact boolNotTy_spec | exact bitofTy_spec _ | exact eqTy_spec | exact cmpTy_spec
    | exact impliesTy_spec | exact boolIteTy_spec | exact boolNTy_spec | exact listTy_spec _

theorem resultTy_eq_opTy {op : Op} {a : List Ty} {t : Ty} (h : op.resultTy a = some t) :
    t = opTy op a.length := (resultTy_spec op a t h).1

/-- 15 (lower bound): every operator has at least `minArity` arguments. -/
theorem resultTy_minArity {op : Op} {a : List Ty} {t : Ty} (h : op.resultTy a = some t) :
    minArity op ≤ a.length := (resultTy_spec op a t h).2.1

/-- 15 (exact): a fixed-arity operator has exactly `minArity` arguments.  For a specific
operator, `resultTy_fixedArity h rfl : a.length = 2` (say) type-checks directly. -/
theorem resultTy_fixedArity {op : Op} {a : List Ty} {t : Ty} (h : op.resultTy a = some t)
    (hf : fixedArity op = true) : a.length = minArity op := (resultTy_spec op a t h).2.2.1 hf

theorem resultTy_bv_pos {op : Op} {a : List Ty} {w : Nat} (h : op.resultTy a = some (.bv w)) :
    1 ≤ w := (resultTy_spec op a _ h).2.2.2 w rfl

theorem resultTy_leaf {op : Op} {a : List Ty} {t : Ty} (hl : IsLeaf op)
    (h : op.resultTy a = some t) : a = [] := by
  have hf : fixedArity op = true ∧ minArity op = 0 := by
    cases op <;> first | exact ⟨rfl, rfl⟩ | cases hl
  have := resultTy_fixedArity h hf.1
  rw [hf.2] at this
  exact List.eq_nil_of_length_eq_zero this

theorem resultTy_bvVal {w v : Nat} {a : List Ty} {t : Ty}
    (h : (Op.bvVal w v).resultTy a = some t) : w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w :=
  (bvValTy_eq_some.mp h).2.1

theorem resultTy_bvExtract {hi lo : Nat} {a : List Ty} {t : Ty}
    (h : (Op.bvExtract hi lo).resultTy a = some t) : lo ≤ hi := by
  obtain ⟨_, _, h, _⟩ := bvExtractTy_eq_some.mp h
  exact h

/-- The class of the result type, read off the code. -/
theorem resultTy_bool_iff {op : Op} {a : List Ty} {t : Ty} (h : op.resultTy a = some t) :
    t = .bool ↔ opC op % 8 = 1 := by
  rw [resultTy_eq_opTy h]
  cases op <;> simp [opTy, isBoolOp, opC]

theorem resultTy_bv_iff {op : Op} {a : List Ty} {t : Ty} (h : op.resultTy a = some t) :
    (∃ w, t = .bv w) ↔ opC op % 8 = 0 := by
  rw [resultTy_eq_opTy h]
  cases op <;> simp [opTy, isBoolOp, opC]

theorem resultTy_list_iff {op : Op} {a : List Ty} {t : Ty} (h : op.resultTy a = some t) :
    (∃ e k, t = .list e k) ↔ opC op % 8 = 2 := by
  rw [resultTy_eq_opTy h]
  cases op <;> simp [opTy, isBoolOp, opC]

/-! ### `mapOpt` -/

theorem mapOpt_cons_eq_some {α β : Type} {f : α → Option β} {x : α} {l : List α} {l' : List β}
    (h : mapOpt f (x :: l) = some l') :
    ∃ y ys, f x = some y ∧ mapOpt f l = some ys ∧ l' = y :: ys := by
  simp only [mapOpt] at h
  split at h
  · rename_i y ys hy hys
    simp only [Option.some.injEq] at h
    exact ⟨y, ys, hy, hys, h.symm⟩
  · cases h

theorem mapOpt_length {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : mapOpt f l = some l') : l'.length = l.length := by
  induction l generalizing l' with
  | nil => simp only [mapOpt, Option.some.injEq] at h; subst h; rfl
  | cons x l ih =>
    obtain ⟨y, ys, _, hys, rfl⟩ := mapOpt_cons_eq_some h
    simp [ih hys]

/-- The `k`-th result of a successful `mapOpt`. -/
theorem mapOpt_getElem? {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : mapOpt f l = some l') {k : Nat} (hk : k < l.length) : f l[k] = l'[k]? := by
  induction l generalizing l' k with
  | nil => cases hk
  | cons x l ih =>
    obtain ⟨y, ys, hy, hys, rfl⟩ := mapOpt_cons_eq_some h
    cases k with
    | zero => simpa using hy
    | succ k => simpa using ih hys (by simpa using hk)

/-! ### Typed nodes -/

/-- `n` type-checks against the state: what `pushNode` requires of it. -/
def Typed (st : St) (n : Node) : Prop :=
  n.args.all (· < st.pool.size) = true ∧
  ∃ argTys t, mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧
    n.op.resultTy argTys = some t

theorem typed_iff_pushNode {st : St} {n : Node} : Typed st n ↔ (pushNode st n).isSome :=
  pushNode_isSome_iff.symm

theorem Typed.args_lt {st : St} {n : Node} (h : Typed st n) : ∀ a ∈ n.args, a < st.pool.size := by
  have := h.1
  simpa only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] using this

/-- The pool-independent part of typing, the form `nodeW_inj` and `tyOfM_hdrW` take. -/
theorem Typed.shape {st : St} {n : Node} (h : Typed st n) :
    ∃ argTys t, n.op.resultTy argTys = some t ∧ argTys.length = n.args.size := by
  obtain ⟨_, argTys, t, hm, ht⟩ := h
  exact ⟨argTys, t, ht, by simpa using mapOpt_length hm⟩

theorem Typed.minArity {st : St} {n : Node} (h : Typed st n) : minArity n.op ≤ n.args.size := by
  obtain ⟨_, _, ht, hl⟩ := h.shape
  rw [← hl]; exact resultTy_minArity ht

theorem Typed.fixedArity {st : St} {n : Node} (h : Typed st n) (hf : fixedArity n.op = true) :
    n.args.size = Vbcf.Proof.minArity n.op := by
  obtain ⟨_, _, ht, hl⟩ := h.shape
  rw [← hl]; exact resultTy_fixedArity ht hf

/-- The type of argument `k`, as the memo records it. -/
theorem Typed.argTy {st : St} {n : Node} {argTys : List Ty}
    (hm : mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys) {k : Nat}
    (hk : k < n.args.size) : st.tys[n.args[k]]? = argTys[k]? := by
  have := mapOpt_getElem? hm (k := k) (by simpa using hk)
  simpa using this

/-! ### 17. Nodes of the pool -/

theorem PoolOK.typed {st : St} (h : PoolOK st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n) :
    Typed st n := by
  obtain ⟨hargs, argTys, t, hm, ht, _⟩ := tysOK_retype h.tys hn
  exact ⟨hargs, argTys, t, hm, ht⟩

/-- A pool node type-checks against the memo, with the type the memo records for it. -/
theorem PoolOK.retype {st : St} (h : PoolOK st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n) :
    ∃ argTys t, mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧
      n.op.resultTy argTys = some t ∧ st.tys[i]? = some t ∧ argTys.length = n.args.size := by
  obtain ⟨_, argTys, t, hm, ht, hty⟩ := tysOK_retype h.tys hn
  exact ⟨argTys, t, hm, ht, hty, by simpa using mapOpt_length hm⟩

/-- Every node's arguments are earlier nodes. -/
theorem PoolOK.args_lt {st : St} (h : PoolOK st) {i : Nat} {n : Node}
    (hn : st.pool[i]? = some n) : ∀ a ∈ n.args, a < i :=
  (h.tys.2 i n hn).1

/-- The well-formedness hypothesis of `PoolRep.push`. -/
theorem PoolOK.args_lt_size {st : St} (h : PoolOK st) :
    ∀ (i : Nat) (n : Node), st.pool[i]? = some n → ∀ a ∈ n.args, a < st.pool.size :=
  fun _ _ hn a ha => Nat.lt_trans (h.args_lt hn a ha) (lt_size_of_getElem? hn)

/-- Every index below the pool size has a memoised type. -/
theorem PoolOK.tys_size {st : St} (h : PoolOK st) : st.tys.size = st.pool.size := h.tys.1

/-! ### 16. The type encoding -/

/-- The natural-number model of the C function `ty_of` on header `h`.  The `BV_EXTRACT`
case is `hi - lo + 1` in 32-bit arithmetic (it equals `hi - lo + 1` when `lo ≤ hi`, see
`tyOfM_extract`), so that the model is exact for every header (`tyOfB_eq`). -/
def tyOfM (h : Nat) : Nat :=
  if h % 256 % 8 = 1 then 0x1000
  else if h % 256 % 8 = 2 then 0x2000 + (h / 65536 % 2) * 256 + h / 256 % 256
  else if h % 256 = 0x38 then
    (h / 16777216 % 256 + 4294967296 - h / 65536 % 256 + 1) % 4294967296
  else if h % 256 = 0x88 then h / 256 % 256
  else h / 65536 % 256

theorem tyOfM_lt (h : Nat) : tyOfM h < 2 ^ 32 := by
  unfold tyOfM
  repeat' split
  all_goals omega

theorem tyOfM_extract {h : Nat} (hc : h % 256 = 0x38)
    (hle : h / 65536 % 256 ≤ h / 16777216 % 256) :
    tyOfM h = h / 16777216 % 256 - h / 65536 % 256 + 1 := by
  unfold tyOfM
  split
  · omega
  split
  · omega
  first | omega | (split <;> omega)

/-- The types that the header of a fitting node can describe. -/
def TyFits : Ty → Prop
  | .bv w => 1 ≤ w ∧ w ≤ 256
  | .bool => True
  | .list _ k => k < 256

@[simp] theorem tyW_bool : tyW .bool = 0x1000 := rfl
@[simp] theorem tyW_bv (w : Nat) : tyW (.bv w) = w := rfl
theorem tyW_list (e : Bool) (k : Nat) :
    tyW (.list e k) = 0x2000 + (if e then 1 else 0) * 256 + k := rfl

theorem tyW_list_ge (e : Bool) (k : Nat) : 0x2000 ≤ tyW (.list e k) := by
  rw [tyW_list]; omega

theorem tyW_lt {t : Ty} (h : TyFits t) : tyW t < 0x2200 := by
  cases t with
  | bool => simp
  | bv w => simp only [TyFits] at h; simp only [tyW_bv]; omega
  | list e k => simp only [TyFits] at h; rw [tyW_list]; split <;> omega

theorem tyW_lt_two_pow {t : Ty} (h : TyFits t) : tyW t < 2 ^ 32 := by
  have := tyW_lt h; omega

theorem tyW_inj {t t' : Ty} (h : TyFits t) (h' : TyFits t') (e : tyW t = tyW t') : t = t' := by
  cases t <;> cases t' <;> simp only [TyFits] at h h' <;> simp only [tyW] at e <;>
    first
    | rfl
    | (rename_i e1 k1 e2 k2; cases e1 <;> cases e2 <;> simp at e <;> first | omega | (subst e; rfl))
    | (subst e; rfl)
    | (exfalso; split at e <;> omega)
    | (exfalso; omega)

theorem tyW_eq_bool_iff {t : Ty} (h : TyFits t) : tyW t = 0x1000 ↔ t = .bool :=
  ⟨fun e => tyW_inj h trivial e, fun e => e ▸ rfl⟩

theorem tyW_lt_bool_iff {t : Ty} (h : TyFits t) : tyW t < 0x1000 ↔ ∃ w, t = .bv w := by
  cases t with
  | bool => simp
  | bv w => simp only [TyFits] at h; simp; omega
  | list e k => have := tyW_list_ge e k; simp; omega

theorem tyW_lt_list_iff {t : Ty} (h : TyFits t) : tyW t < 0x2000 ↔ t.isScalar = true := by
  cases t with
  | bool => simp [Ty.isScalar]
  | bv w => simp only [TyFits] at h; simp [Ty.isScalar]; omega
  | list e k => have := tyW_list_ge e k; simp [Ty.isScalar]; omega

theorem tyW_eq_bv_iff {t : Ty} (h : TyFits t) {w : Nat} (hw : w < 0x1000) :
    tyW t = w ↔ t = .bv w := by
  cases t with
  | bool => simp; omega
  | bv w' => simp
  | list e k => have := tyW_list_ge e k; simp; omega

/-- The result type of a fitting node fits. -/
theorem tyFits_of_resultTy {posOf : Nat → Nat} {n : Node} {argTys : List Ty} {t : Ty}
    (hf : Fits posOf n) (ht : n.op.resultTy argTys = some t)
    (hl : argTys.length = n.args.size) : TyFits t := by
  have hlo := hf.lo; have hhi := hf.hi; have htl := hf.tailLen
  cases t with
  | bool => trivial
  | bv w =>
    have hpos := resultTy_bv_pos ht
    have e := resultTy_eq_opTy ht
    rw [hl] at e
    refine ⟨hpos, ?_⟩
    rcases n with ⟨op, args⟩
    cases op <;> simp [opTy, isBoolOp, opLo, opHi, tailLen] at e hlo hhi htl <;> omega
  | list e k =>
    have e := resultTy_eq_opTy ht
    rw [hl] at e
    rcases n with ⟨op, args⟩
    cases op <;> simp [opTy, isBoolOp, tailLen] at e htl
    simp only [TyFits]; omega

/-- 16: `ty_of` applied to the header of a fitting, typed node is the encoding of its type. -/
theorem tyOfM_hdrW {posOf : Nat → Nat} {n : Node} {argTys : List Ty} {t : Ty}
    (hf : Fits posOf n) (ht : n.op.resultTy argTys = some t)
    (hl : argTys.length = n.args.size) : tyOfM (hdrW n) = tyW t := by
  have hlo := hf.lo; have hhi := hf.hi; have htl := hf.tailLen
  have e := resultTy_eq_opTy ht
  rw [hl] at e; subst e
  have h4 : hdrW n / 16777216 % 256 = opHi n.op := by rw [hdrW_hi hf]; omega
  have h5 : hdrW n / 65536 % 2 = opLo n.op % 2 := by rw [hdrW_params hf]; omega
  unfold tyOfM
  rw [hdrW_code hf, hdrW_len hf, hdrW_lo hf, h4, h5]
  rcases n with ⟨op, args⟩
  cases op
  case bvExtract hi lo =>
    have := resultTy_bvExtract ht
    simp [opC, opLo, opHi, opTy, isBoolOp] at hhi ⊢
    omega
  case listVal e =>
    cases e <;> simp [opC, opLo, opTy, isBoolOp, tailLen, tyW_list]
  all_goals simp [opC, opLo, opTy, isBoolOp, tailLen]

theorem bv_width_le {posOf : Nat → Nat} {n : Node} {argTys : List Ty} {w : Nat}
    (hf : Fits posOf n) (ht : n.op.resultTy argTys = some (.bv w))
    (hl : argTys.length = n.args.size) : 1 ≤ w ∧ w ≤ 256 :=
  tyFits_of_resultTy hf ht hl

/-- 16 + 17: the header of pool node `i` encodes the memoised type of `i`. -/
theorem PoolOK.tyOfM_hdrW {posOf : Nat → Nat} {st : St} (h : PoolOK st) {i : Nat} {n : Node}
    (hn : st.pool[i]? = some n) (hf : Fits posOf n) :
    ∃ t, st.tys[i]? = some t ∧ tyOfM (hdrW n) = tyW t ∧ TyFits t := by
  obtain ⟨argTys, t, _, ht, hty, hl⟩ := h.retype hn
  exact ⟨t, hty, Vbcf.Proof.tyOfM_hdrW hf ht hl, tyFits_of_resultTy hf ht hl⟩

/-! ### `ty_of` on machine words -/

/-- `ty_of` as the C code computes it. -/
def tyOfB (h : BitVec 32) : BitVec 32 :=
  if (h &&& 0xff#32) &&& 7#32 = 1#32 then 0x1000#32
  else if (h &&& 0xff#32) &&& 7#32 = 2#32 then
    0x2000#32 ||| (((h >>> 16) &&& 1#32) <<< 8) ||| ((h >>> 8) &&& 0xff#32)
  else if h &&& 0xff#32 = 0x38#32 then ((h >>> 24) &&& 0xff#32) - ((h >>> 16) &&& 0xff#32) + 1#32
  else if h &&& 0xff#32 = 0x88#32 then (h >>> 8) &&& 0xff#32
  else (h >>> 16) &&& 0xff#32

theorem bv_eq_lit_iff {x : BitVec 32} {n : Nat} (h : n < 2 ^ 32) :
    x = BitVec.ofNat 32 n ↔ x.toNat = n := bv_eq_ofNat_iff h

theorem tyOfB_toNat (h : BitVec 32) : (tyOfB h).toNat = tyOfM h.toNat := by
  have c1 : ((h &&& 0xff#32) &&& 7#32 = 1#32) ↔ h.toNat % 256 % 8 = 1 := by
    rw [← BitVec.toNat_inj, bv_and_7, bv_and_ff]; rfl
  have c2 : ((h &&& 0xff#32) &&& 7#32 = 2#32) ↔ h.toNat % 256 % 8 = 2 := by
    rw [← BitVec.toNat_inj, bv_and_7, bv_and_ff]; rfl
  have c3 : (h &&& 0xff#32 = 0x38#32) ↔ h.toNat % 256 = 0x38 := by
    rw [← BitVec.toNat_inj, bv_and_ff]; rfl
  have c4 : (h &&& 0xff#32 = 0x88#32) ↔ h.toNat % 256 = 0x88 := by
    rw [← BitVec.toNat_inj, bv_and_ff]; rfl
  unfold tyOfB tyOfM
  simp only [c1, c2, c3, c4]
  split
  · rfl
  split
  · rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_shiftLeft, bv_and_1, bv_and_ff,
      bv_shr_16, bv_shr_8]
    show 8192 ||| (h.toNat / 65536 % 2) <<< 8 % 4294967296 ||| h.toNat / 256 % 256 = _
    have hb : h.toNat / 65536 % 2 = 0 ∨ h.toNat / 65536 % 2 = 1 := by omega
    have hn : h.toNat / 256 % 256 < 2 ^ 8 := by omega
    rcases hb with hb | hb <;> rw [hb]
    · show 32 <<< 8 ||| h.toNat / 256 % 256 = _
      rw [← Nat.shiftLeft_add_eq_or_of_lt hn]; rfl
    · show 33 <<< 8 ||| h.toNat / 256 % 256 = _
      rw [← Nat.shiftLeft_add_eq_or_of_lt hn]; rfl
  split
  · rw [BitVec.toNat_add, BitVec.toNat_sub, bv_and_ff, bv_and_ff, bv_shr_24, bv_shr_16]
    show ((4294967296 - h.toNat / 65536 % 256 + h.toNat / 16777216 % 256) % 4294967296 + 1)
      % 4294967296 = _
    omega
  split
  · rw [bv_and_ff, bv_shr_8]
  · rw [bv_and_ff, bv_shr_16]

/-- The C `ty_of` is the model `tyOfM`, for every header word. -/
theorem tyOfB_eq (h : BitVec 32) : tyOfB h = BitVec.ofNat 32 (tyOfM h.toNat) := by
  rw [bv_eq_ofNat_iff (tyOfM_lt _)]; exact tyOfB_toNat h

/-! ## G. Injectivity of the encoding -/

/-- The datum of a leaf that is stored in the tail rather than in the header. -/
def opData : Op → Nat
  | .bvVar _ id => id
  | .boolVar id => id
  | .bvVal _ v => v
  | _ => 0

/-- Decoder: the operator with the given code, parameter bytes and leaf datum. -/
def decOp (c lo hi d : Nat) : Op :=
  if c = 0x18 then .bvVar lo d else
  if c = 0x08 then .bvVal lo d else
  if c = 0x28 then .bvIte lo else
  if c = 0x80 then .bvNeg lo else
  if c = 0x78 then .bvNot lo else
  if c = 0x38 then .bvExtract hi lo else
  if c = 0x48 then .bvSignExtend lo hi else
  if c = 0x58 then .bvZeroExtend lo hi else
  if c = 0x68 then .bvSize lo else
  if c = 0xa8 then .bvRepeat lo hi else
  if c = 0x10 then .bvSub lo else
  if c = 0x60 then .bvShl lo else
  if c = 0x70 then .bvLshr lo else
  if c = 0xc0 then .bvAshr lo else
  if c = 0x30 then .bvUdiv lo else
  if c = 0x90 then .bvUrem lo else
  if c = 0xb0 then .bvSdiv lo else
  if c = 0xd0 then .bvSmod lo else
  if c = 0x00 then .bvAdd lo else
  if c = 0x20 then .bvMul lo else
  if c = 0x40 then .bvOr lo else
  if c = 0x50 then .bvAnd lo else
  if c = 0xa0 then .bvXor lo else
  if c = 0x98 then .bvConcat lo else
  if c = 0x88 then .bvFromBool else
  if c = 0x09 then .boolVal (lo != 0) else
  if c = 0x19 then .boolVar d else
  if c = 0x81 then .boolNot else
  if c = 0x49 then .boolBitof lo else
  if c = 0x11 then .eq else
  if c = 0x51 then .distinct else
  if c = 0x21 then .ugt else
  if c = 0x31 then .uge else
  if c = 0x61 then .sgt else
  if c = 0x71 then .sge else
  if c = 0xa1 then .ult else
  if c = 0xb1 then .ule else
  if c = 0xc1 then .slt else
  if c = 0xd1 then .sle else
  if c = 0x91 then .implies else
  if c = 0x29 then .boolIte else
  if c = 0x01 then .conj else
  if c = 0x41 then .disj else
  if c = 0x39 then .boolXor else
  .listVal (lo != 0)

theorem decOp_enc (op : Op) : decOp (opC op) (opLo op) (opHi op) (opData op) = op := by
  cases op <;> first | rfl | (rename_i b; cases b <;> rfl)

/-- An operator is determined by its code, its two parameter bytes and its leaf datum. -/
theorem op_eq_of_enc {a b : Op} (hc : opC a = opC b) (hlo : opLo a = opLo b)
    (hhi : opHi a = opHi b) (hd : opData a = opData b) : a = b := by
  rw [← decOp_enc a, ← decOp_enc b, hc, hlo, hhi, hd]

theorem opData_eq_zero {op : Op} (h1 : opC op ≠ 0x18) (h2 : opC op ≠ 0x19) (h3 : opC op ≠ 0x08) :
    opData op = 0 := by
  cases op <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3

theorem map_inj_of_inj_on {α β : Type} {f : α → β} {l l' : List α}
    (hf : ∀ a ∈ l, ∀ b ∈ l', f a = f b → a = b) (h : l.map f = l'.map f) : l = l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons y l' => cases h
  | cons x l ih =>
    cases l' with
    | nil => cases h
    | cons y l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hxy := hf x (by simp) y (by simp) h.1
      subst hxy
      rw [ih (fun a ha b hb => hf a (by simp [ha]) b (by simp [hb])) h.2]

theorem nodeW_inj {posOf : Nat → Nat} {pool : Pool} {n n' : Node}
    (hf : Fits posOf n) (hf' : Fits posOf n')
    (ht : ∃ argTys t, n.op.resultTy argTys = some t ∧ argTys.length = n.args.size)
    (ht' : ∃ argTys t, n'.op.resultTy argTys = some t ∧ argTys.length = n'.args.size)
    (ha : ∀ a ∈ n.args, a < pool.size) (ha' : ∀ a ∈ n'.args, a < pool.size)
    (hpos : ∀ a b, posOf a = posOf b → a = b)
    (h : nodeW posOf pool n = nodeW posOf pool n') : n = n' := by
  simp only [nodeW, List.cons.injEq] at h
  obtain ⟨hh, htl⟩ := h
  obtain ⟨hc, _, hlo, hhi⟩ := hdrW_inj hf hf' hh
  obtain ⟨argTys, t, ht, hl⟩ := ht
  obtain ⟨argTys', t', ht', hl'⟩ := ht'
  rcases n with ⟨op, args⟩
  rcases n' with ⟨op', args'⟩
  simp only at hc hlo hhi ht ht' hl hl' ha ha'
  -- the operators agree
  have hop : op = op' := by
    apply op_eq_of_enc hc hlo hhi
    by_cases h18 : opC op = 0x18
    · obtain ⟨w, id, rfl⟩ := opC_bvVar_iff.mp h18
      obtain ⟨w', id', rfl⟩ := opC_bvVar_iff.mp (hc ▸ h18)
      simp only [tailW, List.cons.injEq, and_true] at htl
      exact hpos _ _ htl
    by_cases h19 : opC op = 0x19
    · obtain ⟨id, rfl⟩ := opC_boolVar_iff.mp h19
      obtain ⟨id', rfl⟩ := opC_boolVar_iff.mp (hc ▸ h19)
      simp only [tailW, List.cons.injEq, and_true] at htl
      exact hpos _ _ htl
    by_cases h08 : opC op = 0x08
    · obtain ⟨w, v, rfl⟩ := opC_bvVal_iff.mp h08
      obtain ⟨w', v', rfl⟩ := opC_bvVal_iff.mp (hc ▸ h08)
      obtain ⟨_, _, hv⟩ := resultTy_bvVal ht
      obtain ⟨_, _, hv'⟩ := resultTy_bvVal ht'
      simp only [opLo] at hlo
      subst hlo
      simp only [tailW, opData] at htl ⊢
      by_cases hw : w ≤ 32
      · simp only [hw, ↓reduceIte, List.cons.injEq, and_true] at htl
        have h32 : 2 ^ w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hw
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htl
        exact htl
      · simp only [hw, ↓reduceIte, List.cons.injEq, and_true] at htl
        have e1 := Nat.div_add_mod v (2 ^ 32)
        have e2 := Nat.div_add_mod v' (2 ^ 32)
        rw [htl.1, htl.2] at e1
        omega
    · rw [opData_eq_zero h18 h19 h08,
        opData_eq_zero (hc ▸ h18) (hc ▸ h19) (hc ▸ h08)]
  subst hop
  -- the arguments agree
  have hargs : args = args' := by
    by_cases hleaf : IsLeaf op
    · have e := resultTy_leaf hleaf ht
      have e' := resultTy_leaf hleaf ht'
      subst e; subst e'
      simp only [List.length_nil] at hl hl'
      rw [Array.eq_empty_of_size_eq_zero hl.symm, Array.eq_empty_of_size_eq_zero hl'.symm]
    · rw [tailW_of_not_leaf (n := ⟨op, args⟩) hleaf,
        tailW_of_not_leaf (n := ⟨op, args'⟩) hleaf] at htl
      have := map_inj_of_inj_on (f := offs pool) (l := args.toList) (l' := args'.toList)
        (fun a ha0 b hb0 e => offs_inj (Nat.le_of_lt (ha a (by simpa using ha0)))
          (Nat.le_of_lt (ha' b (by simpa using hb0))) e) htl
      exact Array.toList_inj.mp this
  rw [hargs]

/-- `nodeW_inj` for a node of a `PoolOK` pool and a typed candidate. -/
theorem nodeW_inj_typed {posOf : Nat → Nat} {st : St} {n n' : Node}
    (hf : Fits posOf n) (hf' : Fits posOf n') (ht : Typed st n) (ht' : Typed st n')
    (hpos : ∀ a b, posOf a = posOf b → a = b)
    (h : nodeW posOf st.pool n = nodeW posOf st.pool n') : n = n' :=
  nodeW_inj hf hf' ht.shape ht'.shape ht.args_lt ht'.args_lt hpos h

/-! ### From machine words back to nodes -/

theorem tailW_of_leaf {posOf off off' : Nat → Nat} {n : Node} (h : IsLeaf n.op) :
    tailW posOf off n = tailW posOf off' n := by
  rcases n with ⟨op, args⟩
  cases op <;> first | rfl | cases h

/-- The leaf words fit 32 bits if all tail words do, for any choice of child images. -/
theorem tailW_zero_lt {posOf off : Nat → Nat} {n : Node} (h : ∀ w ∈ tailW posOf off n, w < 2 ^ 32) :
    ∀ w ∈ tailW posOf (fun _ => 0) n, w < 2 ^ 32 := by
  by_cases hl : IsLeaf n.op
  · rw [tailW_of_leaf (off' := off) hl]; exact h
  · rw [tailW_of_not_leaf hl]
    intro w hw
    simp only [List.mem_map, Array.mem_toList_iff] at hw
    obtain ⟨a, _, rfl⟩ := hw
    decide

/-- Every tail word fits 32 bits, provided the images of the arguments do. -/
theorem tailW_lt {posOf off : Nat → Nat} {n : Node} (hf : Fits posOf n)
    (ha : ∀ a ∈ n.args, off a < 2 ^ 32) : ∀ w ∈ tailW posOf off n, w < 2 ^ 32 := by
  by_cases hl : IsLeaf n.op
  · rw [tailW_of_leaf (off' := fun _ => 0) hl]; exact hf.tail
  · rw [tailW_of_not_leaf hl]
    intro w hw
    simp only [List.mem_map, Array.mem_toList_iff] at hw
    obtain ⟨a, ha', rfl⟩ := hw
    exact ha a ha'

/-- Every word of a fitting node with arguments in the pool fits 32 bits. -/
theorem nodeW_lt {posOf : Nat → Nat} {pool : Pool} {n : Node} (hf : Fits posOf n)
    (ha : ∀ a ∈ n.args, a < pool.size) (hp : offs pool pool.size ≤ 2 ^ 32) :
    ∀ w ∈ nodeW posOf pool n, w < 2 ^ 32 := by
  intro w hw
  simp only [nodeW, List.mem_cons] at hw
  rcases hw with rfl | hw
  · exact hdrW_lt hf
  · exact tailW_lt hf (fun a ha' => Nat.lt_of_lt_of_le (offs_lt_end (ha a ha')) hp) w hw

/-- Word lists that fit 32 bits are equal if their machine words are. -/
theorem map_ofNat_inj {l l' : List Nat} (h : ∀ w ∈ l, w < 2 ^ 32) (h' : ∀ w ∈ l', w < 2 ^ 32)
    (e : l.map (BitVec.ofNat 32) = l'.map (BitVec.ofNat 32)) : l = l' :=
  map_inj_of_inj_on (fun a ha b hb e => (bv_ofNat_inj (h a ha) (h' b hb)).mp e) e

/-- `nodeW_inj` on machine words: what a successful `words_eq` gives. -/
theorem nodeW_inj_bv {posOf : Nat → Nat} {pool : Pool} {n n' : Node}
    (hf : Fits posOf n) (hf' : Fits posOf n')
    (ht : ∃ argTys t, n.op.resultTy argTys = some t ∧ argTys.length = n.args.size)
    (ht' : ∃ argTys t, n'.op.resultTy argTys = some t ∧ argTys.length = n'.args.size)
    (ha : ∀ a ∈ n.args, a < pool.size) (ha' : ∀ a ∈ n'.args, a < pool.size)
    (hpos : ∀ a b, posOf a = posOf b → a = b) (hp : offs pool pool.size ≤ 2 ^ 32)
    (h : (nodeW posOf pool n).map (BitVec.ofNat 32) =
      (nodeW posOf pool n').map (BitVec.ofNat 32)) : n = n' :=
  nodeW_inj hf hf' ht ht' ha ha' hpos
    (map_ofNat_inj (nodeW_lt hf ha hp) (nodeW_lt hf' ha' hp) h)

end Vbcf.Proof
