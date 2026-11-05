import EmbC.Clight.Proof.Program

/-!
# Clight operator semantics on the values produced by the lowering
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem beq_dec {α : Type} [DecidableEq α] (a b : α) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem not_lt_dec (x y : Nat) : (!decide (x < y)) = decide (y ≤ x) := by
  by_cases h : x < y <;> simp [h] <;> omega

section
open CC.Integers

theorem arith32 (op : BinOp) (a b : BitVec 32) (v : Val) (ce : CC.CompositeEnv) (m : CC.Mem)
    (h : evalArith Val.u32 op a b = some v) (hc : Priv.comparison op = false) :
    ∃ r, v = .u32 r ∧
      CC.Cop.semBinaryOperation ce (Priv.binop op) (.Vint a) CC.tuint (.Vint b) CC.tuint m =
        some (.Vint r) := by
  cases op <;> simp [Priv.comparison] at hc
  all_goals simp only [evalArith] at h
  case add => cases h; exact ⟨_, rfl, rfl⟩
  case sub => cases h; exact ⟨_, rfl, rfl⟩
  case mul => cases h; exact ⟨_, rfl, rfl⟩
  case band => cases h; exact ⟨_, rfl, rfl⟩
  case bor => cases h; exact ⟨_, rfl, rfl⟩
  case bxor => cases h; exact ⟨_, rfl, rfl⟩
  case div =>
    split at h
    · cases h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int.eq b Int.zero then none else some (CC.Val.Vint (Int.divu a b))) = _
      simp_all [Int.eq, Int.zero, Int.divu, MI.eq, MI.zero, MI.divu]
  case mod =>
    split at h
    · cases h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int.eq b Int.zero then none else some (CC.Val.Vint (Int.modu a b))) = _
      simp_all [Int.eq, Int.zero, Int.modu, MI.eq, MI.zero, MI.modu]
  case shl =>
    split at h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int.ltu b Int.iwordsize then some (CC.Val.Vint (Int.shl a b)) else none) = _
      simp_all [Int.ltu, MI.ltu, Int.iwordsize, MI.iwordsize, Int.shl, MI.shl, BitVec.ult]
    · cases h
  case shr =>
    split at h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int.ltu b Int.iwordsize then some (CC.Val.Vint (Int.shru a b)) else none) = _
      simp_all [Int.ltu, MI.ltu, Int.iwordsize, MI.iwordsize, Int.shru, MI.shru, BitVec.ult]
    · cases h

theorem arith64 (op : BinOp) (a b : BitVec 64) (v : Val) (ce : CC.CompositeEnv) (m : CC.Mem)
    (h : evalArith Val.u64 op a b = some v) (hc : Priv.comparison op = false) :
    ∃ r, v = .u64 r ∧
      CC.Cop.semBinaryOperation ce (Priv.binop op) (.Vlong a) CC.tulong (.Vlong b) CC.tulong m =
        some (.Vlong r) := by
  cases op <;> simp [Priv.comparison] at hc
  all_goals simp only [evalArith] at h
  case add => cases h; exact ⟨_, rfl, rfl⟩
  case sub => cases h; exact ⟨_, rfl, rfl⟩
  case mul => cases h; exact ⟨_, rfl, rfl⟩
  case band => cases h; exact ⟨_, rfl, rfl⟩
  case bor => cases h; exact ⟨_, rfl, rfl⟩
  case bxor => cases h; exact ⟨_, rfl, rfl⟩
  case div =>
    split at h
    · cases h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int64.eq b Int64.zero then none else some (CC.Val.Vlong (Int64.divu a b))) = _
      simp_all [Int64.eq, Int64.zero, Int64.divu, MI.eq, MI.zero, MI.divu]
  case mod =>
    split at h
    · cases h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int64.eq b Int64.zero then none else some (CC.Val.Vlong (Int64.modu a b))) = _
      simp_all [Int64.eq, Int64.zero, Int64.modu, MI.eq, MI.zero, MI.modu]
  case shl =>
    split at h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int64.ltu b Int64.iwordsize then some (CC.Val.Vlong (Int64.shl a b)) else none) = _
      simp_all [Int64.ltu, MI.ltu, Int64.iwordsize, MI.iwordsize, Int64.shl, MI.shl, BitVec.ult]
    · cases h
  case shr =>
    split at h
    · cases h
      refine ⟨_, rfl, ?_⟩
      show (if Int64.ltu b Int64.iwordsize then some (CC.Val.Vlong (Int64.shru a b)) else none) = _
      simp_all [Int64.ltu, MI.ltu, Int64.iwordsize, MI.iwordsize, Int64.shru, MI.shru, BitVec.ult]
    · cases h

theorem cmp32 (op : BinOp) (a b : BitVec 32) (v : Val) (ce : CC.CompositeEnv) (m : CC.Mem)
    (h : evalArith Val.u32 op a b = some v) (hc : Priv.comparison op = true) :
    ∃ c, v = Val.ofBool c ∧
      CC.Cop.semBinaryOperation ce (Priv.binop op) (.Vint a) CC.tuint (.Vint b) CC.tuint m =
        some (CC.Val.ofBool c) := by
  cases op <;> simp [Priv.comparison] at hc
  all_goals simp only [evalArith] at h; cases h; refine ⟨_, rfl, ?_⟩
  case eq =>
    show some (CC.Val.ofBool (Int.cmpu .Ceq a b)) = _
    simp [Int.cmpu, MI.cmpu, MI.eq, beq_dec]
  case ne =>
    show some (CC.Val.ofBool (Int.cmpu .Cne a b)) = _
    simp [Int.cmpu, MI.cmpu, MI.eq, beq_dec]
  case lt =>
    show some (CC.Val.ofBool (Int.cmpu .Clt a b)) = _
    simp [Int.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.lt_def]
  case le =>
    show some (CC.Val.ofBool (Int.cmpu .Cle a b)) = _
    simp [Int.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.le_def, not_lt_dec]
  case gt =>
    show some (CC.Val.ofBool (Int.cmpu .Cgt a b)) = _
    simp [Int.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.lt_def]
  case ge =>
    show some (CC.Val.ofBool (Int.cmpu .Cge a b)) = _
    simp [Int.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.le_def, not_lt_dec]

theorem cmp64 (op : BinOp) (a b : BitVec 64) (v : Val) (ce : CC.CompositeEnv) (m : CC.Mem)
    (h : evalArith Val.u64 op a b = some v) (hc : Priv.comparison op = true) :
    ∃ c, v = Val.ofBool c ∧
      CC.Cop.semBinaryOperation ce (Priv.binop op) (.Vlong a) CC.tulong (.Vlong b) CC.tulong m =
        some (CC.Val.ofBool c) := by
  cases op <;> simp [Priv.comparison] at hc
  all_goals simp only [evalArith] at h; cases h; refine ⟨_, rfl, ?_⟩
  case eq =>
    show some (CC.Val.ofBool (Int64.cmpu .Ceq a b)) = _
    simp [Int64.cmpu, MI.cmpu, MI.eq, beq_dec]
  case ne =>
    show some (CC.Val.ofBool (Int64.cmpu .Cne a b)) = _
    simp [Int64.cmpu, MI.cmpu, MI.eq, beq_dec]
  case lt =>
    show some (CC.Val.ofBool (Int64.cmpu .Clt a b)) = _
    simp [Int64.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.lt_def]
  case le =>
    show some (CC.Val.ofBool (Int64.cmpu .Cle a b)) = _
    simp [Int64.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.le_def, not_lt_dec]
  case gt =>
    show some (CC.Val.ofBool (Int64.cmpu .Cgt a b)) = _
    simp [Int64.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.lt_def]
  case ge =>
    show some (CC.Val.ofBool (Int64.cmpu .Cge a b)) = _
    simp [Int64.cmpu, MI.cmpu, MI.ltu, BitVec.ult, BitVec.le_def, not_lt_dec]

theorem cast_bool_tint_tuint (c : Bool) (m : CC.Mem) :
    CC.Cop.semCast (CC.Val.ofBool c) CC.tint CC.tuint m = some (CC.Val.ofBool c) := by
  cases c <;> rfl

theorem ofBool_rel (c : Bool) : CC.Val.ofBool c = .Vint (if c then 1 else 0) := by
  cases c <;> rfl

theorem src_ofBool (c : Bool) : Val.ofBool c = .u32 (if c then 1 else 0) := rfl

theorem notbool32 (a : BitVec 32) (m : CC.Mem) :
    CC.Cop.semUnaryOperation .Onotbool (.Vint a) CC.tuint m =
      some (CC.Val.ofBool (decide (a = 0))) := by
  show some (CC.Val.ofBool (!(!Int.eq a Int.zero))) = _
  simp [Int.eq, Int.zero, MI.eq, MI.zero, beq_dec]

theorem notint32 (a : BitVec 32) (m : CC.Mem) :
    CC.Cop.semUnaryOperation .Onotint (.Vint a) CC.tuint m = some (.Vint (~~~a)) := rfl

theorem notint64 (a : BitVec 64) (m : CC.Mem) :
    CC.Cop.semUnaryOperation .Onotint (.Vlong a) CC.tulong m = some (.Vlong (~~~a)) := rfl

theorem cast32_32 (a : BitVec 32) (m : CC.Mem) :
    CC.Cop.semCast (.Vint a) CC.tuint CC.tuint m = some (.Vint a) := rfl

theorem cast64_64 (a : BitVec 64) (m : CC.Mem) :
    CC.Cop.semCast (.Vlong a) CC.tulong CC.tulong m = some (.Vlong a) := rfl

theorem cast32_64 (a : BitVec 32) (m : CC.Mem) :
    CC.Cop.semCast (.Vint a) CC.tuint CC.tulong m = some (.Vlong (a.setWidth 64)) := by
  show some (CC.Val.Vlong (CC.Cop.castIntLong .Unsigned a)) = _
  simp only [CC.Cop.castIntLong, Int64.repr, Int.unsigned, MI.repr, MI.unsigned, Option.some.injEq,
    CC.Val.Vlong.injEq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  have := a.isLt
  omega

theorem cast64_32 (a : BitVec 64) (m : CC.Mem) :
    CC.Cop.semCast (.Vlong a) CC.tulong CC.tuint m = some (.Vint (a.setWidth 32)) := by
  show some (CC.Val.Vint (CC.Cop.castIntInt .I32 .Unsigned (CC.Integers.Int.repr (Int64.unsigned a)))) = _
  simp only [CC.Cop.castIntInt, Int64.unsigned, CC.Integers.Int.repr, MI.repr, MI.unsigned, Option.some.injEq,
    CC.Val.Vint.injEq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  omega

theorem boolVal32 (a : BitVec 32) (m : CC.Mem) :
    CC.Cop.boolVal (.Vint a) CC.tuint m = some (decide (a ≠ 0)) := by
  show some (!Int.eq a Int.zero) = _
  simp [Int.eq, Int.zero, MI.eq, MI.zero, beq_dec]

end

end EmbC.Clight.Proof
