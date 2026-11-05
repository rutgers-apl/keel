import Bcf.Rw.Pattern

/-!
# The rewrite table

Transcribed from `bcf_rewrites.h` (`tools/conv.py`): all 151 rewrites, by id.
Each has a soundness proof in the `Bcf.Rw.*` modules, dispatched in `Rw/All.lean`.
The conditions of entries 73, 74, 80, 140 and 141 have a conjunct that BCF's table lacks;
the checker evaluates such a conjunct itself when the proof
supplies no premise for it.
-/

namespace Bcf

open RwExpr in
/-- The rewrites of `bcf_rewrites.h`, by id, that this checker supports. -/
def rwTable : Nat → Option RwRule
  | 1 => some ⟨[.any], none,
      eq' (var 0) (var 0),
      tt⟩  -- EQ_REFL
  | 2 => some ⟨[.any, .any], none, eq' (V 0) (V 1), eq' (V 1) (V 0)⟩                      -- EQ_SYMM
  | 3 => some ⟨[.any, .any, .any], some (eq' (eq' (var 1) (var 2)) (ff)),
      eq' (eq' (var 0) (var 1)) (eq' (var 0) (var 2)),
      conj' [not' (eq' (var 0) (var 1)), not' (eq' (var 0) (var 2))]⟩  -- EQ_COND_DEQ
  | 4 => some ⟨[.bool, .any, .any, .any], none,
      eq' (ite (var 0) (var 1) (var 2)) (var 3),
      ite (var 0) (eq' (var 1) (var 3)) (eq' (var 2) (var 3))⟩  -- EQ_ITE_LIFT
  | 5 => some ⟨[.any, .any], none, neq' (V 0) (V 1), not' (eq' (V 0) (V 1))⟩              -- DISTINCT_BINARY_ELIM
  | 6 => some ⟨[.any, .any], none,
      ite (tt) (var 0) (var 1),
      var 0⟩  -- ITE_TRUE_COND
  | 7 => some ⟨[.any, .any], none,
      ite (ff) (var 0) (var 1),
      var 1⟩  -- ITE_FALSE_COND
  | 8 => some ⟨[.bool, .any, .any], none,
      ite (not' (var 0)) (var 1) (var 2),
      ite (var 0) (var 2) (var 1)⟩  -- ITE_NOT_COND
  | 9 => some ⟨[.bool, .any], none,
      ite (var 0) (var 1) (var 1),
      var 1⟩  -- ITE_EQ_BRANCH
  | 10 => some ⟨[.bool, .any, .any, .any], none,
      ite (var 0) (ite (var 0) (var 1) (var 2)) (var 3),
      ite (var 0) (var 1) (var 3)⟩  -- ITE_THEN_LOOKAHEAD
  | 11 => some ⟨[.bool, .any, .any, .any], none,
      ite (var 0) (var 1) (ite (var 0) (var 2) (var 3)),
      ite (var 0) (var 1) (var 3)⟩  -- ITE_ELSE_LOOKAHEAD
  | 12 => some ⟨[.bool, .any, .any, .any], none,
      ite (var 0) (ite (not' (var 0)) (var 1) (var 2)) (var 3),
      ite (var 0) (var 2) (var 3)⟩  -- ITE_THEN_NEG_LOOKAHEAD
  | 13 => some ⟨[.bool, .any, .any, .any], none,
      ite (var 0) (var 1) (ite (not' (var 0)) (var 2) (var 3)),
      ite (var 0) (var 1) (var 2)⟩  -- ITE_ELSE_NEG_LOOKAHEAD
  | 14 => some ⟨[.bool], none, not' (not' (V 0)), V 0⟩                                    -- BOOL_DOUBLE_NOT_ELIM
  | 15 => some ⟨[.bool], some (eq' (var 0) (ff)),
      not' (var 0),
      tt⟩  -- BOOL_NOT_TRUE
  | 16 => some ⟨[.bool], some (eq' (var 0) (tt)),
      not' (var 0),
      ff⟩  -- BOOL_NOT_FALSE
  | 17 => some ⟨[.bool], none, eq' (V 0) tt, V 0⟩                                          -- BOOL_EQ_TRUE
  | 18 => some ⟨[.bool], none, eq' (V 0) ff, not' (V 0)⟩                                   -- BOOL_EQ_FALSE
  | 19 => some ⟨[.bool], none, eq' (V 0) (not' (V 0)), ff⟩                                 -- BOOL_EQ_NREFL
  | 20 => some ⟨[.bool], none,
      implies' (var 0) (ff),
      not' (var 0)⟩  -- BOOL_IMPL_FALSE1
  | 21 => some ⟨[.bool], none,
      implies' (ff) (var 0),
      tt⟩  -- BOOL_IMPL_FALSE2
  | 22 => some ⟨[.bool], none,
      implies' (var 0) (tt),
      tt⟩  -- BOOL_IMPL_TRUE1
  | 23 => some ⟨[.bool], none,
      implies' (tt) (var 0),
      var 0⟩  -- BOOL_IMPL_TRUE2
  | 24 => some ⟨[.bool, .bool], none,
      implies' (var 0) (var 1),
      disj' [not' (var 0), var 1]⟩  -- BOOL_IMPL_ELIM
  | 25 => some ⟨[.bool, .bool], none,
      conj' [implies' (var 0) (var 1), implies' (var 1) (var 0)],
      eq' (var 0) (var 1)⟩  -- BOOL_DUAL_IMPL_EQ
  | 26 => some ⟨[.bools, .bool, .bools, .bools], none,
      conj' [var 0, var 1, var 2, not' (var 1), var 3],
      ff⟩  -- BOOL_AND_CONF
  | 27 => some ⟨[.bools, .bool, .bools, .bools], none,
      conj' [var 0, not' (var 1), var 2, var 1, var 3],
      ff⟩  -- BOOL_AND_CONF2
  | 28 => some ⟨[.bools, .bool, .bools, .bools], none,
      disj' [var 0, var 1, var 2, not' (var 1), var 3],
      tt⟩  -- BOOL_OR_TAUT
  | 29 => some ⟨[.bools, .bool, .bools, .bools], none,
      disj' [var 0, not' (var 1), var 2, var 1, var 3],
      tt⟩  -- BOOL_OR_TAUT2
  | 30 => some ⟨[.bool, .bool], none,
      not' (implies' (var 0) (var 1)),
      conj' [var 0, not' (var 1)]⟩  -- BOOL_IMPLIES_DE_MORGAN
  | 31 => some ⟨[.bool], none,
      xor' [var 0, var 0],
      ff⟩  -- BOOL_XOR_REFL
  | 32 => some ⟨[.bool], none, xor' [V 0, not' (V 0)], tt⟩                                 -- BOOL_XOR_NREFL
  | 33 => some ⟨[.bool], none, xor' [V 0, ff], V 0⟩                                        -- BOOL_XOR_FALSE
  | 34 => some ⟨[.bool], none, xor' [V 0, tt], not' (V 0)⟩                                 -- BOOL_XOR_TRUE
  | 35 => some ⟨[.bool, .bool], none, xor' [V 0, V 1], xor' [V 1, V 0]⟩                   -- BOOL_XOR_COMM
  | 36 => some ⟨[.bool, .bool], none,
      xor' [var 0, var 1],
      eq' (not' (var 0)) (var 1)⟩  -- BOOL_XOR_ELIM
  | 37 => some ⟨[.bool, .bool], none,
      not' (xor' [var 0, var 1]),
      eq' (var 0) (var 1)⟩  -- BOOL_NOT_XOR_ELIM
  | 38 => some ⟨[.bool, .bool], none,
      not' (eq' (var 0) (var 1)),
      eq' (not' (var 0)) (var 1)⟩  -- BOOL_NOT_EQ_ELIM1
  | 39 => some ⟨[.bool, .bool], none,
      not' (eq' (var 0) (var 1)),
      eq' (var 0) (not' (var 1))⟩  -- BOOL_NOT_EQ_ELIM2
  | 40 => some ⟨[.bool, .bool, .bool], some (eq' (not' (var 2)) (var 1)),
      ite (var 0) (var 1) (var 2),
      eq' (var 0) (var 1)⟩  -- ITE_NEG_BRANCH
  | 41 => some ⟨[.bool, .bool], none,
      ite (var 0) (tt) (var 1),
      disj' [var 0, var 1]⟩  -- ITE_THEN_TRUE
  | 42 => some ⟨[.bool, .bool], none,
      ite (var 0) (var 1) (ff),
      conj' [var 0, var 1]⟩  -- ITE_ELSE_FALSE
  | 43 => some ⟨[.bool, .bool], none,
      ite (var 0) (ff) (var 1),
      conj' [not' (var 0), var 1]⟩  -- ITE_THEN_FALSE
  | 44 => some ⟨[.bool, .bool], none,
      ite (var 0) (var 1) (tt),
      disj' [not' (var 0), var 1]⟩  -- ITE_ELSE_TRUE
  | 45 => some ⟨[.bool, .bool], none,
      ite (var 0) (var 0) (var 1),
      ite (var 0) (tt) (var 1)⟩  -- ITE_THEN_LOOKAHEAD_SELF
  | 46 => some ⟨[.bool, .bool], none,
      ite (var 0) (var 1) (var 0),
      ite (var 0) (var 1) (ff)⟩  -- ITE_ELSE_LOOKAHEAD_SELF
  | 47 => some ⟨[.bool, .bool], none,
      ite (var 0) (not' (var 0)) (var 1),
      ite (var 0) (ff) (var 1)⟩  -- ITE_THEN_LOOKAHEAD_NOT_SELF
  | 48 => some ⟨[.bool, .bool], none,
      ite (var 0) (var 1) (not' (var 0)),
      ite (var 0) (var 1) (tt)⟩  -- ITE_ELSE_LOOKAHEAD_NOT_SELF
  | 49 => some ⟨[.bool, .bool, .bool], none,
      ite (var 0) (var 1) (var 2),
      conj' [disj' [not' (var 0), var 1], disj' [var 0, var 2]]⟩  -- ITE_EXPAND
  | 50 => some ⟨[.bool, .bool, .bool], none,
      not' (ite (var 0) (var 1) (var 2)),
      ite (var 0) (not' (var 1)) (not' (var 2))⟩  -- BOOL_NOT_ITE_ELIM
  | 51 => some ⟨[.bvqs, .bvq, .bvqs, .bv 32, .bv 32, .bv 32, .bv 32], some (eq' (var 5) (bvadd' [var 4, l1])),
      concat' [var 0, extract (var 6) (var 5) (var 1), extract (var 4) (var 3) (var 1), var 2],
      concat' [var 0, extract (var 6) (var 3) (var 1), var 2]⟩  -- BV_CONCAT_EXTRACT_MERGE
  | 52 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32],                   -- BV_EXTRACT_EXTRACT
      some (conj' [eq' (V 5) (bvadd' [V 1, V 4]), eq' (V 6) (bvadd' [V 1, V 3])]),
      extract (V 4) (V 3) (extract (V 2) (V 1) (V 0)), extract (V 5) (V 6) (V 0)⟩
  | 53 => some ⟨[.bvq, .bv 32], some (sge' (V 1) (bvsub' (bvsize' (V 0)) l1)),           -- BV_EXTRACT_WHOLE
      extract (V 1) l0 (V 0), V 0⟩
  | 54 => some ⟨[.bvq, .bvqs, .bvq, .bv 32, .bv 32], some (sle' (V 4) (bvsize' (V 0))),  -- BV_EXTRACT_CONCAT_1
      extract (V 4) (V 3) (concat' [V 1, V 2, V 0]), extract (V 4) (V 3) (V 0)⟩
  | 55 => some ⟨[.bvq, .bvqs, .bvq, .bv 32, .bv 32, .bv 32, .bv 32],                      -- BV_EXTRACT_CONCAT_2
      some (conj' [slt' (V 3) (bvsize' (V 0)), sge' (V 4) (bvsize' (V 0)),
                   eq' (V 5) (bvsub' (V 4) (bvsize' (V 0))), eq' (V 6) (bvsub' (bvsize' (V 0)) l1)]),
      extract (V 4) (V 3) (concat' [V 1, V 2, V 0]),
      concat' [extract (V 5) l0 (concat' [V 1, V 2]), extract (V 6) (V 3) (V 0)]⟩
  | 56 => some ⟨[.bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32, .bv 32],                      -- BV_EXTRACT_CONCAT_3
      some (conj' [sge' (V 3) (bvsize' (V 0)), eq' (V 5) (bvsub' (V 4) (bvsize' (V 0))),
                   eq' (V 6) (bvsub' (V 3) (bvsize' (V 0)))]),
      extract (V 4) (V 3) (concat' [V 2, V 1, V 0]), extract (V 5) (V 6) (concat' [V 2, V 1])⟩
  | 57 => some ⟨[.bvq, .bvq, .bvqs, .bv 32, .bv 32],                                       -- BV_EXTRACT_CONCAT_4
      some (slt' (V 4) (bvsub' (bvsize' (concat' [V 0, V 2, V 1])) (bvsize' (V 0)))),
      extract (V 4) (V 3) (concat' [V 0, V 2, V 1]), extract (V 4) (V 3) (concat' [V 2, V 1])⟩
  | 58 => some ⟨[.bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvadd' [var 3, l1]), eq' (var 6) (bvsub' (var 2) (l1)), sgt' (var 4) (var 3), sgt' (var 2) (l0)]),
      eq' (extract (var 3) (var 2) (var 0)) (var 1),
      eq' (var 0) (concat' [extract (var 4) (var 5) (var 0), var 1, extract (var 6) (l0) (var 0)])⟩  -- BV_EQ_EXTRACT_ELIM1
  | 59 => some ⟨[.bvq, .bvq, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 3) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 4) (bvadd' [var 2, l1]), sgt' (var 3) (var 2)]),
      eq' (extract (var 2) (l0) (var 0)) (var 1),
      eq' (var 0) (concat' [extract (var 3) (var 4) (var 0), var 1])⟩  -- BV_EQ_EXTRACT_ELIM2
  | 60 => some ⟨[.bvq, .bvq, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 3) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 4) (bvsub' (var 2) (l1)), sgt' (var 2) (l0)]),
      eq' (extract (var 3) (var 2) (var 0)) (var 1),
      eq' (var 0) (concat' [var 1, extract (var 4) (l0) (var 0)])⟩  -- BV_EQ_EXTRACT_ELIM3
  | 61 => some ⟨[.bvq, .bv 32, .bv 32], none,
      extract (var 2) (var 1) (bvnot' (var 0)),
      bvnot' (extract (var 2) (var 1) (var 0))⟩  -- BV_EXTRACT_NOT
  | 62 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32], some (slt' (V 2) (bvsize' (V 0))),       -- BV_EXTRACT_SIGN_EXTEND_1
      extract (V 2) (V 1) (sext (V 3) (V 0)), extract (V 2) (V 1) (V 0)⟩
  | 63 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [slt' (var 1) (bvsize' (var 0)), sge' (var 2) (bvsize' (var 0)), eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvadd' [l1, bvsub' (var 2) (bvsize' (var 0))])]),
      extract (var 2) (var 1) (sext (var 3) (var 0)),
      sext (var 5) (extract (var 4) (var 1) (var 0))⟩  -- BV_EXTRACT_SIGN_EXTEND_2
  | 64 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32],                            -- BV_EXTRACT_SIGN_EXTEND_3
      some (conj' [sge' (V 1) (bvsize' (V 0)), eq' (V 4) (bvadd' [l1, bvsub' (V 2) (V 1)]),
                   eq' (V 5) (bvsub' (bvsize' (V 0)) l1)]),
      extract (V 2) (V 1) (sext (V 3) (V 0)), «repeat» (V 4) (extract (V 5) (V 5) (V 0))⟩
  | 65 => some ⟨[.bvq, .bvq, .bvqs], none,
      bvnot' (bvxor' [var 0, var 1, var 2]),
      bvxor' [bvnot' (var 0), var 1, var 2]⟩  -- BV_NOT_XOR
  | 66 => some ⟨[.bvqs, .bvqs, .bvqs, .bvq, .bv 32], some (eq' (var 4) (bvsize' (var 3))),
      bvand' [var 0, bvnot' (var 3), var 1, var 3, var 2],
      symVal (l0) (var 4)⟩  -- BV_AND_SIMPLIFY_1
  | 67 => some ⟨[.bvqs, .bvqs, .bvqs, .bvq, .bv 32], some (eq' (var 4) (bvsize' (var 3))),
      bvand' [var 0, var 3, var 1, bvnot' (var 3), var 2],
      symVal (l0) (var 4)⟩  -- BV_AND_SIMPLIFY_2
  | 68 => some ⟨[.bvqs, .bvqs, .bvqs, .bvq, .bv 32], some (eq' (var 4) (bvsize' (var 3))),
      bvor' [var 0, bvnot' (var 3), var 1, var 3, var 2],
      bvnot' (symVal (l0) (var 4))⟩  -- BV_OR_SIMPLIFY_1
  | 69 => some ⟨[.bvqs, .bvqs, .bvqs, .bvq, .bv 32], some (eq' (var 4) (bvsize' (var 3))),
      bvor' [var 0, var 3, var 1, bvnot' (var 3), var 2],
      bvnot' (symVal (l0) (var 4))⟩  -- BV_OR_SIMPLIFY_2
  | 70 => some ⟨[.bvqs, .bvqs, .bvqs, .bvq], none,
      bvxor' [var 0, var 3, var 1, bvnot' (var 3), var 2],
      bvnot' (bvxor' [var 0, var 1, var 2])⟩  -- BV_XOR_SIMPLIFY_2
  | 71 => some ⟨[.bvqs, .bvqs, .bvqs, .bvq], none,
      bvxor' [var 0, bvnot' (var 3), var 1, var 3, var 2],
      bvnot' (bvxor' [var 0, var 1, var 2])⟩  -- BV_XOR_SIMPLIFY_3
  | 72 => some ⟨[.bvq, .bvqs, .bvqs, .bvq, .bv 32], some (conj' [eq' (var 3) (symVal (l1) (var 4)), eq' (var 4) (bvsize' (var 0))]),
      ult' (var 0) (bvadd' [var 1, var 3, var 2]),
      conj' [not' (eq' (bvadd' [var 1, var 2]) (bvnot' (symVal (l0) (var 4)))), not' (ult' (bvadd' [var 1, var 2]) (var 0))]⟩  -- BV_ULT_ADD_ONE
  | 73 => some ⟨[.bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 5) (bvsize' (var 0)), eq' (var 6) (bvsize' (var 2)), ule' (var 6) (var 3)]),
      slt' (bvmul' [sext (var 3) (var 1), sext (var 4) (var 2)]) (bvmul' [sext (var 3) (var 0), sext (var 4) (var 2)]),
      conj' [not' (eq' (bvsub' (var 1) (var 0)) (symVal (l0) (var 5))), not' (eq' (var 2) (symVal (l0) (var 6))), eq' (slt' (var 1) (var 0)) (sgt' (var 2) (symVal (l0) (var 6)))]⟩  -- BV_MULT_SLT_MULT_1 (condition extended, see docs)
  | 74 => some ⟨[.bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 5) (bvsize' (var 0)), eq' (var 6) (bvsize' (var 2)), ule' (var 6) (var 3)]),
      slt' (bvmul' [zext (var 3) (var 1), sext (var 4) (var 2)]) (bvmul' [zext (var 3) (var 0), sext (var 4) (var 2)]),
      conj' [not' (eq' (bvsub' (var 1) (var 0)) (symVal (l0) (var 5))), not' (eq' (var 2) (symVal (l0) (var 6))), eq' (ult' (var 1) (var 0)) (sgt' (var 2) (symVal (l0) (var 6)))]⟩  -- BV_MULT_SLT_MULT_2 (condition extended, see docs)
  | 75 => some ⟨[.bvq, .bvq], none,
      bvxor' [var 0, var 1],
      bvxor' [var 1, var 0]⟩  -- BV_COMMUTATIVE_XOR
  | 76 => some ⟨[.bvq], none,
      zext (l0) (var 0),
      var 0⟩  -- BV_ZERO_EXTEND_ELIMINATE_0
  | 77 => some ⟨[.bvq], none,
      sext (l0) (var 0),
      var 0⟩  -- BV_SIGN_EXTEND_ELIMINATE_0
  | 78 => some ⟨[.bvq], some (sgt' (bvsize' (var 0)) (l0)),
      eq' (var 0) (bvnot' (var 0)),
      ff⟩  -- BV_NOT_NEQ
  | 79 => some ⟨[.bvq, .bv 32, .bv 32], some (eq' (var 1) (bvmax (var 2))),
      ult' (var 0) (symVal (var 1) (var 2)),
      neq' (var 0) (symVal (var 1) (var 2))⟩  -- BV_ULT_ONES
  | 80 => some ⟨[.bvqs, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32, .bvqs],                   -- BV_CONCAT_MERGE_CONST
      -- second conjunct added: BCF computes the merged value in 32 bits, so the
      -- rule is only valid when that computation does not overflow, i.e. when
      -- the high literal shifted left by the low width still fits in 32 bits
      some (conj' [eq' (V 5) (bvadd' [V 2, V 4]), ule' (V 1) (bvlshr' (lit 0xFFFFFFFF) (V 4))]),
      concat' [V 0, symVal (V 1) (V 2), symVal (V 3) (V 4), V 6],
      concat' [V 0, symVal (bvadd' [bvmul' [V 1, bvshl' l1 (V 4)], V 3]) (V 5), V 6]⟩
  | 81 => some ⟨[.bvq, .bvq], none,
      bvadd' [var 0, var 1],
      bvadd' [var 1, var 0]⟩  -- BV_COMMUTATIVE_ADD
  | 82 => some ⟨[.bvq, .bvq], none,
      bvsub' (var 0) (var 1),
      bvadd' [var 0, bvneg' (var 1)]⟩  -- BV_SUB_ELIMINATE
  | 83 => some ⟨[.bvq], none,
      ite (eq' (var 0) (symVal (l1) (l1))) (symVal (l1) (l1)) (symVal (l0) (l1)),
      var 0⟩  -- BV_ITE_WIDTH_ONE
  | 84 => some ⟨[.bvq], none,
      ite (eq' (var 0) (symVal (l0) (l1))) (symVal (l1) (l1)) (symVal (l0) (l1)),
      bvnot' (var 0)⟩  -- BV_ITE_WIDTH_ONE_NOT
  | 85 => some ⟨[.bvq, .bvq, .bvq], none,
      eq' (eq' (bvxor' [var 0, var 1]) (var 2)) (eq' (var 0) (bvxor' [var 2, var 1])),
      tt⟩  -- BV_EQ_XOR_SOLVE
  | 86 => some ⟨[.bvq, .bvq], none,
      eq' (eq' (bvnot' (var 0)) (var 1)) (eq' (var 0) (bvnot' (var 1))),
      tt⟩  -- BV_EQ_NOT_SOLVE
  | 87 => some ⟨[.bvq, .bvq], none,
      ugt' (var 0) (var 1),
      ult' (var 1) (var 0)⟩  -- BV_UGT_ELIMINATE
  | 88 => some ⟨[.bvq, .bvq], none,
      uge' (var 0) (var 1),
      ule' (var 1) (var 0)⟩  -- BV_UGE_ELIMINATE
  | 89 => some ⟨[.bvq, .bvq], none,
      sgt' (var 0) (var 1),
      slt' (var 1) (var 0)⟩  -- BV_SGT_ELIMINATE
  | 90 => some ⟨[.bvq, .bvq], none,
      sge' (var 0) (var 1),
      sle' (var 1) (var 0)⟩  -- BV_SGE_ELIMINATE
  | 91 => some ⟨[.bvq, .bvq], none, sle' (V 0) (V 1), not' (slt' (V 1) (V 0))⟩           -- BV_SLE_ELIMINATE
  | 92 => some ⟨[.bvq, .bvq], none, ule' (V 0) (V 1), not' (ult' (V 1) (V 0))⟩           -- BV_ULE_ELIMINATE
  | 93 => some ⟨[.bvq, .bv 32], none, zext (V 1) (V 0), concat' [symVal l0 (V 1), V 0]⟩  -- BV_ZERO_EXTEND_ELIMINATE
  | 94 => some ⟨[.bv 1, .bvq], none,
      ite (var 0) (var 1) (var 1),
      var 1⟩  -- BV_ITE_EQUAL_CHILDREN
  | 95 => some ⟨[.bv 1], none,
      ite (var 0) (symVal (l0) (l1)) (symVal (l1) (l1)),
      bvnot' (var 0)⟩  -- BV_ITE_CONST_CHILDREN_1
  | 96 => some ⟨[.bv 1], none,
      ite (var 0) (symVal (l1) (l1)) (symVal (l0) (l1)),
      var 0⟩  -- BV_ITE_CONST_CHILDREN_2
  | 97 => some ⟨[.bv 1, .bvq, .bvq, .bvq], none,
      ite (var 0) (ite (var 0) (var 1) (var 2)) (var 3),
      ite (var 0) (var 1) (var 3)⟩  -- BV_ITE_EQUAL_COND_1
  | 98 => some ⟨[.bv 1, .bvq, .bvq, .bvq], none,
      ite (var 0) (var 1) (ite (var 0) (var 2) (var 3)),
      ite (var 0) (var 1) (var 3)⟩  -- BV_ITE_EQUAL_COND_2
  | 99 => some ⟨[.bv 1, .bvq, .bvq, .bvq, .bvq], none,
      ite (var 0) (ite (var 0) (var 1) (var 2)) (ite (var 0) (var 3) (var 4)),
      ite (var 0) (var 1) (var 4)⟩  -- BV_ITE_EQUAL_COND_3
  | 100 => some ⟨[.bv 1, .bv 1, .bvq, .bvq], none,
      ite (var 0) (ite (var 1) (var 2) (var 3)) (var 2),
      ite (bvand' [var 0, bvnot' (var 1)]) (var 3) (var 2)⟩  -- BV_ITE_MERGE_THEN_IF
  | 101 => some ⟨[.bv 1, .bv 1, .bvq, .bvq], none,
      ite (var 0) (ite (var 1) (var 2) (var 3)) (var 3),
      ite (bvand' [var 0, var 1]) (var 2) (var 3)⟩  -- BV_ITE_MERGE_ELSE_IF
  | 102 => some ⟨[.bv 1, .bv 1, .bvq, .bvq], none,
      ite (var 0) (var 2) (ite (var 1) (var 2) (var 3)),
      ite (bvand' [bvnot' (var 0), bvnot' (var 1)]) (var 3) (var 2)⟩  -- BV_ITE_MERGE_THEN_ELSE
  | 103 => some ⟨[.bv 1, .bv 1, .bvq, .bvq], none,
      ite (var 0) (var 3) (ite (var 1) (var 2) (var 3)),
      ite (bvand' [bvnot' (var 0), var 1]) (var 2) (var 3)⟩  -- BV_ITE_MERGE_ELSE_ELSE
  | 104 => some ⟨[.bvq, .bv 32], none,
      bvshl' (var 0) (symVal (l0) (var 1)),
      var 0⟩  -- BV_SHL_BY_CONST_0
  | 105 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32],                                           -- BV_SHL_BY_CONST_1
      some (conj' [slt' (V 1) (bvsize' (V 0)), eq' (V 3) (bvsub' (bvsize' (V 0)) (bvadd' [l1, V 1]))]),
      bvshl' (V 0) (symVal (V 1) (V 2)), concat' [extract (V 3) l0 (V 0), symVal l0 (V 1)]⟩
  | 106 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32], some (conj' [sge' (var 1) (bvsize' (var 0)), eq' (var 3) (bvsize' (var 0))]),
      bvshl' (var 0) (symVal (var 1) (var 2)),
      symVal (l0) (var 3)⟩  -- BV_SHL_BY_CONST_2
  | 107 => some ⟨[.bvq, .bv 32], none,
      bvlshr' (var 0) (symVal (l0) (var 1)),
      var 0⟩  -- BV_LSHR_BY_CONST_0
  | 108 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32], some (conj' [slt' (var 1) (bvsize' (var 0)), eq' (var 3) (bvsub' (bvsize' (var 0)) (l1))]),
      bvlshr' (var 0) (symVal (var 1) (var 2)),
      concat' [symVal (l0) (var 1), extract (var 3) (var 1) (var 0)]⟩  -- BV_LSHR_BY_CONST_1
  | 109 => some ⟨[.bvq, .bv 32, .bv 32], some (sge' (var 1) (bvsize' (var 0))),
      bvlshr' (var 0) (symVal (var 1) (var 2)),
      symVal (l0) (var 2)⟩  -- BV_LSHR_BY_CONST_2
  | 110 => some ⟨[.bvq, .bv 32], none,
      bvashr' (var 0) (symVal (l0) (var 1)),
      var 0⟩  -- BV_ASHR_BY_CONST_0
  | 111 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32],                                           -- BV_ASHR_BY_CONST_1
      some (conj' [slt' (V 1) (bvsize' (V 0)), eq' (V 3) (bvsub' (bvsize' (V 0)) l1)]),
      bvashr' (V 0) (symVal (V 1) (V 2)),
      concat' [«repeat» (V 1) (extract (V 3) (V 3) (V 0)), extract (V 3) (V 1) (V 0)]⟩
  | 112 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [sge' (var 1) (bvsize' (var 0)), eq' (var 3) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 4) (bvsize' (var 0))]),
      bvashr' (var 0) (symVal (var 1) (var 2)),
      «repeat» (var 4) (extract (var 3) (var 3) (var 0))⟩  -- BV_ASHR_BY_CONST_2
  | 113 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32],              -- BV_AND_CONCAT_PULLUP
      some (conj' [eq' (V 6) (bvsize' (V 2)), eq' (V 5) (bvsub' (bvsize' (bvand' [V 0, V 1])) l1),
                   eq' (V 7) (bvsub' (bvsize' (V 2)) l1)]),
      bvand' [V 0, concat' [V 4, V 3, V 2], V 1],
      concat' [bvand' [extract (V 5) (V 6) (bvand' [V 0, V 1]), concat' [V 4, V 3]],
               bvand' [extract (V 7) l0 (bvand' [V 0, V 1]), V 2]]⟩
  | 114 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32],              -- BV_OR_CONCAT_PULLUP
      some (conj' [eq' (V 6) (bvsize' (V 2)), eq' (V 5) (bvsub' (bvsize' (bvor' [V 0, V 1])) l1),
                   eq' (V 7) (bvsub' (bvsize' (V 2)) l1)]),
      bvor' [V 0, concat' [V 4, V 3, V 2], V 1],
      concat' [bvor' [extract (V 5) (V 6) (bvor' [V 0, V 1]), concat' [V 4, V 3]],
               bvor' [extract (V 7) l0 (bvor' [V 0, V 1]), V 2]]⟩
  | 115 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 6) (bvsize' (var 2)), eq' (var 5) (bvsub' (bvsize' (bvxor' [var 0, var 1])) (l1)), eq' (var 7) (bvsub' (bvsize' (var 2)) (l1))]),
      bvxor' [var 0, concat' [var 4, var 3, var 2], var 1],
      concat' [bvxor' [extract (var 5) (var 6) (bvxor' [var 0, var 1]), concat' [var 4, var 3]], bvxor' [extract (var 7) (l0) (bvxor' [var 0, var 1]), var 2]]⟩  -- BV_XOR_CONCAT_PULLUP
  | 116 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32],              -- BV_AND_CONCAT_PULLUP2
      some (conj' [eq' (V 6) (bvsize' (concat' [V 2, V 4])),
                   eq' (V 5) (bvsub' (bvsize' (bvand' [V 0, V 1])) l1),
                   eq' (V 7) (bvsub' (bvsize' (concat' [V 2, V 4])) l1)]),
      bvand' [V 0, concat' [V 3, V 2, V 4], V 1],
      concat' [bvand' [extract (V 5) (V 6) (bvand' [V 0, V 1]), V 3],
               bvand' [extract (V 7) l0 (bvand' [V 0, V 1]), concat' [V 2, V 4]]]⟩
  | 117 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32],              -- BV_OR_CONCAT_PULLUP2
      some (conj' [eq' (V 6) (bvsize' (concat' [V 2, V 4])),
                   eq' (V 5) (bvsub' (bvsize' (bvor' [V 0, V 1])) l1),
                   eq' (V 7) (bvsub' (bvsize' (concat' [V 2, V 4])) l1)]),
      bvor' [V 0, concat' [V 3, V 2, V 4], V 1],
      concat' [bvor' [extract (V 5) (V 6) (bvor' [V 0, V 1]), V 3],
               bvor' [extract (V 7) l0 (bvor' [V 0, V 1]), concat' [V 2, V 4]]]⟩
  | 118 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 6) (bvsize' (concat' [var 2, var 4])), eq' (var 5) (bvsub' (bvsize' (bvxor' [var 0, var 1])) (l1)), eq' (var 7) (bvsub' (bvsize' (concat' [var 2, var 4])) (l1))]),
      bvxor' [var 0, concat' [var 3, var 2, var 4], var 1],
      concat' [bvxor' [extract (var 5) (var 6) (bvxor' [var 0, var 1]), var 3], bvxor' [extract (var 7) (l0) (bvxor' [var 0, var 1]), concat' [var 2, var 4]]]⟩  -- BV_XOR_CONCAT_PULLUP2
  | 119 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 5) (bvsub' (bvsize' (bvand' [var 0, var 1])) (l1)), eq' (var 6) (bvadd' [bvsize' (var 2), bvsize' (var 4)]), eq' (var 7) (bvsub' (bvadd' [bvsize' (var 2), bvsize' (var 4)]) (l1)), eq' (var 8) (bvsize' (var 4)), eq' (var 9) (bvsub' (bvsize' (var 4)) (l1))]),
      bvand' [var 0, concat' [var 3, var 2, var 4], var 1],
      concat' [bvand' [extract (var 5) (var 6) (bvand' [var 0, var 1]), var 3], bvand' [extract (var 7) (var 8) (bvand' [var 0, var 1]), var 2], bvand' [extract (var 9) (l0) (bvand' [var 0, var 1]), var 4]]⟩  -- BV_AND_CONCAT_PULLUP3
  | 120 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 5) (bvsub' (bvsize' (bvor' [var 0, var 1])) (l1)), eq' (var 6) (bvadd' [bvsize' (var 2), bvsize' (var 4)]), eq' (var 7) (bvsub' (bvadd' [bvsize' (var 2), bvsize' (var 4)]) (l1)), eq' (var 8) (bvsize' (var 4)), eq' (var 9) (bvsub' (bvsize' (var 4)) (l1))]),
      bvor' [var 0, concat' [var 3, var 2, var 4], var 1],
      concat' [bvor' [extract (var 5) (var 6) (bvor' [var 0, var 1]), var 3], bvor' [extract (var 7) (var 8) (bvor' [var 0, var 1]), var 2], bvor' [extract (var 9) (l0) (bvor' [var 0, var 1]), var 4]]⟩  -- BV_OR_CONCAT_PULLUP3
  | 121 => some ⟨[.bvqs, .bvqs, .bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 5) (bvsub' (bvsize' (bvxor' [var 0, var 1])) (l1)), eq' (var 6) (bvadd' [bvsize' (var 2), bvsize' (var 4)]), eq' (var 7) (bvsub' (bvadd' [bvsize' (var 2), bvsize' (var 4)]) (l1)), eq' (var 8) (bvsize' (var 4)), eq' (var 9) (bvsub' (bvsize' (var 4)) (l1))]),
      bvxor' [var 0, concat' [var 3, var 2, var 4], var 1],
      concat' [bvxor' [extract (var 5) (var 6) (bvxor' [var 0, var 1]), var 3], bvxor' [extract (var 7) (var 8) (bvxor' [var 0, var 1]), var 2], bvxor' [extract (var 9) (l0) (bvxor' [var 0, var 1]), var 4]]⟩  -- BV_XOR_CONCAT_PULLUP3
  | 122 => some ⟨[.bvq, .bv 32], some (eq' (var 1) (bvsize' (var 0))),
      bvxor' [var 0, var 0],
      symVal (l0) (var 1)⟩  -- BV_XOR_DUPLICATE
  | 123 => some ⟨[.bvqs, .bvqs, .bv 32, .bv 32], some (eq' (var 2) (bvmax (var 3))),
      bvxor' [var 0, symVal (var 2) (var 3), var 1],
      bvnot' (bvxor' [var 0, var 1])⟩  -- BV_XOR_ONES
  | 124 => some ⟨[.bvq, .bv 32, .bv 32],                                                   -- BV_ULE_MAX
      some (conj' [eq' (V 2) (bvsize' (V 0)), eq' (V 1) (bvmax (bvsize' (V 0)))]),
      ule' (V 0) (symVal (V 1) (V 2)), tt⟩
  | 125 => some ⟨[.bvq, .bvq], none,
      bvxor' [bvnot' (var 0), bvnot' (var 1)],
      bvxor' [var 0, var 1]⟩  -- BV_XOR_NOT
  | 126 => some ⟨[.bvq], none,
      bvnot' (bvnot' (var 0)),
      var 0⟩  -- BV_NOT_IDEMP
  | 127 => some ⟨[.bvq, .bv 32], none, ult' (symVal l0 (V 1)) (V 0), not' (eq' (V 0) (symVal l0 (V 1)))⟩ -- BV_ULT_ZERO_1
  | 128 => some ⟨[.bvq, .bv 32], none, ult' (V 0) (symVal l0 (V 1)), ff⟩                -- BV_ULT_ZERO_2
  | 129 => some ⟨[.bvq], none,
      ult' (var 0) (var 0),
      ff⟩  -- BV_ULT_SELF
  | 130 => some ⟨[.bvq], none,
      slt' (var 0) (var 0),
      ff⟩  -- BV_LT_SELF
  | 131 => some ⟨[.bvq], none,
      ule' (var 0) (var 0),
      tt⟩  -- BV_ULE_SELF
  | 132 => some ⟨[.bvq, .bv 32], none, ule' (V 0) (symVal l0 (V 1)), eq' (V 0) (symVal l0 (V 1))⟩ -- BV_ULE_ZERO
  | 133 => some ⟨[.bvq, .bv 32], none,
      ule' (symVal (l0) (var 1)) (var 0),
      tt⟩  -- BV_ZERO_ULE
  | 134 => some ⟨[.bvq], none,
      sle' (var 0) (var 0),
      tt⟩  -- BV_SLE_SELF
  | 135 => some ⟨[.bvq, .bvq], none, not' (ult' (V 0) (V 1)), ule' (V 1) (V 0)⟩          -- BV_NOT_ULT
  | 136 => some ⟨[.bvq, .bv 32], none,
      bvshl' (symVal (l0) (var 1)) (var 0),
      symVal (l0) (var 1)⟩  -- BV_SHL_ZERO
  | 137 => some ⟨[.bvq, .bv 32], none,
      bvlshr' (symVal (l0) (var 1)) (var 0),
      symVal (l0) (var 1)⟩  -- BV_LSHR_ZERO
  | 138 => some ⟨[.bvq, .bv 32], none,
      bvashr' (symVal (l0) (var 1)) (var 0),
      symVal (l0) (var 1)⟩  -- BV_ASHR_ZERO
  | 139 => some ⟨[.bvq, .bv 32], none, ult' (V 0) (symVal l1 (V 1)), eq' (V 0) (symVal l0 (V 1))⟩ -- BV_ULT_ONE
  | 140 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 3) (bvadd' [var 1, var 2]), ule' (var 1) (var 3)]),
      sext (var 1) (sext (var 2) (var 0)),
      sext (var 3) (var 0)⟩  -- BV_MERGE_SIGN_EXTEND_1 (condition extended, see docs)
  | 141 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32], some (conj' [sgt' (var 2) (l0), eq' (var 3) (bvadd' [var 1, var 2]), ule' (var 1) (var 3)]),
      sext (var 1) (zext (var 2) (var 0)),
      zext (var 3) (var 0)⟩  -- BV_MERGE_SIGN_EXTEND_2 (condition extended, see docs)
  | 142 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 4) (bvadd' [var 1, l1]), eq' (var 5) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 6) (bvsub' (var 3) (l1))]),
      eq' (sext (var 1) (var 0)) (symVal (var 2) (var 3)),
      conj' [disj' [eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (symVal (l0) (var 4)), eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (bvnot' (symVal (l0) (var 4)))], eq' (var 0) (extract (var 5) (l0) (symVal (var 2) (var 3)))]⟩  -- BV_SIGN_EXTEND_EQ_CONST_1
  | 143 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 4) (bvadd' [var 1, l1]), eq' (var 5) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 6) (bvsub' (var 3) (l1))]),
      eq' (symVal (var 2) (var 3)) (sext (var 1) (var 0)),
      conj' [disj' [eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (symVal (l0) (var 4)), eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (bvnot' (symVal (l0) (var 4)))], eq' (var 0) (extract (var 5) (l0) (symVal (var 2) (var 3)))]⟩  -- BV_SIGN_EXTEND_EQ_CONST_2
  | 144 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvsub' (var 3) (l1))]),
      eq' (zext (var 1) (var 0)) (symVal (var 2) (var 3)),
      conj' [eq' (extract (var 5) (var 4) (symVal (var 2) (var 3))) (symVal (l0) (var 1)), eq' (var 0) (extract (var 4) (l0) (symVal (var 2) (var 3)))]⟩  -- BV_ZERO_EXTEND_EQ_CONST_1
  | 145 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvsub' (var 3) (l1))]),
      eq' (symVal (var 2) (var 3)) (zext (var 1) (var 0)),
      conj' [eq' (extract (var 5) (var 4) (symVal (var 2) (var 3))) (symVal (l0) (var 1)), eq' (var 0) (extract (var 4) (l0) (symVal (var 2) (var 3)))]⟩  -- BV_ZERO_EXTEND_EQ_CONST_2
  | 146 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32],                                   -- BV_ZERO_EXTEND_ULT_CONST_1
      some (conj' [eq' (V 4) (bvsub' (bvsize' (V 0)) l1),
                   eq' (symVal (V 2) (V 3)) (zext (V 1) (extract (V 4) l0 (symVal (V 2) (V 3))))]),
      ult' (zext (V 1) (V 0)) (symVal (V 2) (V 3)), ult' (V 0) (extract (V 4) l0 (symVal (V 2) (V 3)))⟩
  | 147 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32],                                   -- BV_ZERO_EXTEND_ULT_CONST_2
      some (conj' [eq' (V 4) (bvsub' (bvsize' (V 0)) l1),
                   eq' (symVal (V 2) (V 3)) (zext (V 1) (extract (V 4) l0 (symVal (V 2) (V 3))))]),
      ult' (symVal (V 2) (V 3)) (zext (V 1) (V 0)), ult' (extract (V 4) l0 (symVal (V 2) (V 3))) (V 0)⟩
  | 148 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [disj' [ule' (symVal (var 2) (var 3)) (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))), uge' (symVal (var 2) (var 3)) (bvshl' (bvnot' (symVal (l0) (var 3))) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3)))], eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]),
      ult' (sext (var 1) (var 0)) (symVal (var 2) (var 3)),
      ult' (var 0) (extract (var 4) (l0) (symVal (var 2) (var 3)))⟩  -- BV_SIGN_EXTEND_ULT_CONST_1
  | 149 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [ult' (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))) (symVal (var 2) (var 3)), ule' (symVal (var 2) (var 3)) (bvshl' (bvnot' (symVal (l0) (var 3))) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))), eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]),
      ult' (sext (var 1) (var 0)) (symVal (var 2) (var 3)),
      eq' (extract (var 4) (var 4) (var 0)) (symVal (l0) (l1))⟩  -- BV_SIGN_EXTEND_ULT_CONST_2
  | 150 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [disj' [ult' (symVal (var 2) (var 3)) (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))), uge' (symVal (var 2) (var 3)) (bvnot' (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))))], eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]),
      ult' (symVal (var 2) (var 3)) (sext (var 1) (var 0)),
      ult' (extract (var 4) (l0) (symVal (var 2) (var 3))) (var 0)⟩  -- BV_SIGN_EXTEND_ULT_CONST_3
  | 151 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32], some (conj' [ule' (bvnot' (bvshl' (bvnot' (symVal (l0) (var 3))) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3)))) (symVal (var 2) (var 3)), ule' (symVal (var 2) (var 3)) (bvnot' (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3)))), eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]),
      ult' (symVal (var 2) (var 3)) (sext (var 1) (var 0)),
      eq' (extract (var 4) (var 4) (var 0)) (symVal (l1) (l1))⟩  -- BV_SIGN_EXTEND_ULT_CONST_4
  | 152 => some ⟨[.bvqs, .bvqs, .bvqs, .bvq], none,
      bvxor' [var 0, var 3, var 1, var 3, var 2],
      bvxor' [var 0, var 1, var 2]⟩  -- BV_XOR_SIMPLIFY_1 (cvc5 rule, not in BCF's table)
  | 153 => some ⟨[.bool, .bool, .bools], none,
      not' (conj' [var 0, var 1, var 2]),
      disj' [not' (var 0), not' (conj' [var 1, var 2])]⟩  -- BOOL_AND_DE_MORGAN (cvc5 rule, not in BCF's table)
  | 154 => some ⟨[.bool, .bool, .bools], none,
      not' (disj' [var 0, var 1, var 2]),
      conj' [not' (var 0), not' (disj' [var 1, var 2])]⟩  -- BOOL_OR_DE_MORGAN (cvc5 rule, not in BCF's table)
  | 155 => some ⟨[.bool, .bool, .bools, .bool], none,
      implies' (disj' [var 0, var 1, var 2]) (var 3),
      conj' [implies' (var 0) (var 3), implies' (disj' [var 1, var 2]) (var 3)]⟩  -- BOOL_IMPLIES_OR_DISTRIB (cvc5 rule, not in BCF's table)
  | 156 => some ⟨[.bool, .bool, .bools, .bool, .bools], none,
      disj' [conj' [var 0, var 1, var 2], var 3, var 4],
      conj' [disj' [var 0, var 3, var 4], disj' [conj' [var 1, var 2], var 3, var 4]]⟩  -- BOOL_OR_AND_DISTRIB (cvc5 rule, not in BCF's table)
  -- cvc5's condition `(int.ispow2 n) ∧ exponent = (int.log2 n)` is written `n ≠ 0 ∧ n = 1 << exponent` (32-bit)
  | 157 => some ⟨[.bvqs, .bvqs, .bvq, .bv 32, .bv 32, .bv 32, .bv 32],
      some (conj' [not' (eq' (var 4) l0), eq' (var 4) (bvshl' l1 (var 5)), eq' (var 6) (bvsub' (bvsub' (var 3) (var 5)) l1)]),
      bvmul' [var 0, var 2, symVal (var 4) (var 3), var 1],
      concat' [extract (var 6) l0 (bvmul' [var 0, var 2, var 1]), symVal l0 (var 5)]⟩  -- BV_MULT_POW2_1 (cvc5 rule, not in BCF's table)
  -- cvc5's condition `int.ispow2 (2^size - n)` with `exponent = int.log2 (2^size - n)` is written
  -- `(@bv n size) = -(1 << exponent)` at width `size`
  | 158 => some ⟨[.bvqs, .bvqs, .bvq, .bv 32, .bv 32, .bv 32, .bv 32],
      some (conj' [eq' (symVal (var 4) (var 3)) (bvneg' (bvshl' (symVal l1 (var 3)) (symVal (var 5) (var 3)))),
        eq' (var 6) (bvsub' (bvsub' (var 3) (var 5)) l1)]),
      bvmul' [var 0, var 2, symVal (var 4) (var 3), var 1],
      concat' [extract (var 6) l0 (bvneg' (bvmul' [var 0, var 2, var 1])), symVal l0 (var 5)]⟩  -- BV_MULT_POW2_2 (cvc5 rule, not in BCF's table)
  -- condition encoded as for 158
  | 159 => some ⟨[.bvq, .bv 32, .bv 32, .bv 32, .bv 32],
      some (conj' [eq' (symVal (var 2) (var 1)) (bvneg' (bvshl' (symVal l1 (var 1)) (symVal (var 3) (var 1)))),
        eq' (var 4) (bvsub' (bvsub' (var 1) (var 3)) l1)]),
      bvmul' [var 0, symVal (var 2) (var 1)],
      concat' [extract (var 4) l0 (bvneg' (var 0)), symVal l0 (var 3)]⟩  -- BV_MULT_POW2_2B (cvc5 rule, not in BCF's table)
  | 161 => some ⟨[.bvq, .bv 32], none,
      bvudiv' (var 0) (symVal (l1) (var 1)),
      var 0⟩  -- BV_UDIV_ONE (cvc5 rule, not in BCF's table)
  | 162 => some ⟨[.bvq, .bv 32], none,
      bvudiv' (var 0) (symVal (l0) (var 1)),
      bvnot' (symVal (l0) (var 1))⟩  -- BV_UDIV_ZERO (cvc5 rule, not in BCF's table)
  | 163 => some ⟨[.bvq, .bv 32], none,
      bvurem' (var 0) (symVal (l1) (var 1)),
      symVal (l0) (var 1)⟩  -- BV_UREM_ONE (cvc5 rule, not in BCF's table)
  | 164 => some ⟨[.bvq, .bv 32], some (eq' (var 1) (bvsize' (var 0))),
      bvurem' (var 0) (var 0),
      symVal (l0) (var 1)⟩  -- BV_UREM_SELF (cvc5 rule, not in BCF's table)
  | 165 => some ⟨[.bvq, .bvq, .bv 32], some (eq' (var 2) (bvsize' (var 0))),
      ugt' (bvurem' (var 0) (var 1)) (var 1),
      conj' [eq' (var 1) (symVal (l0) (var 2)), ugt' (var 0) (symVal (l0) (var 2))]⟩  -- BV_UGT_UREM (cvc5 rule, not in BCF's table)
  | _ => none

end Bcf
