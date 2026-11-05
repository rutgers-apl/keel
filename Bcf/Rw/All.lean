import Bcf.Rw.Bv
import Bcf.Rw.Bool
import Bcf.Rw.BvBasic
import Bcf.Rw.BvIte
import Bcf.Rw.BvExtract
import Bcf.Rw.BvExtendConst
import Bcf.Rw.BvLists
import Bcf.Rw.BvMul

/-!
# Soundness of the whole rewrite table

`rwTable_sound` dispatches on the rewrite id to the per-rule lemma.
-/

namespace Bcf

/-- **Every rewrite in the table is sound.** -/
theorem rwTable_sound : ∀ rid r, rwTable rid = some r → r.Sound := by
  intro rid r h
  unfold rwTable at h
  split at h
  · injection h with h; subst h; exact sound_EQ_REFL  -- 1
  · injection h with h; subst h; exact sound_EQ_SYMM  -- 2
  · injection h with h; subst h; exact sound_EQ_COND_DEQ  -- 3
  · injection h with h; subst h; exact sound_EQ_ITE_LIFT  -- 4
  · injection h with h; subst h; exact sound_DISTINCT_BINARY_ELIM  -- 5
  · injection h with h; subst h; exact sound_ITE_TRUE_COND  -- 6
  · injection h with h; subst h; exact sound_ITE_FALSE_COND  -- 7
  · injection h with h; subst h; exact sound_ITE_NOT_COND  -- 8
  · injection h with h; subst h; exact sound_ITE_EQ_BRANCH  -- 9
  · injection h with h; subst h; exact sound_ITE_THEN_LOOKAHEAD  -- 10
  · injection h with h; subst h; exact sound_ITE_ELSE_LOOKAHEAD  -- 11
  · injection h with h; subst h; exact sound_ITE_THEN_NEG_LOOKAHEAD  -- 12
  · injection h with h; subst h; exact sound_ITE_ELSE_NEG_LOOKAHEAD  -- 13
  · injection h with h; subst h; exact sound_BOOL_DOUBLE_NOT_ELIM  -- 14
  · injection h with h; subst h; exact sound_BOOL_NOT_TRUE  -- 15
  · injection h with h; subst h; exact sound_BOOL_NOT_FALSE  -- 16
  · injection h with h; subst h; exact sound_BOOL_EQ_TRUE  -- 17
  · injection h with h; subst h; exact sound_BOOL_EQ_FALSE  -- 18
  · injection h with h; subst h; exact sound_BOOL_EQ_NREFL  -- 19
  · injection h with h; subst h; exact sound_BOOL_IMPL_FALSE1  -- 20
  · injection h with h; subst h; exact sound_BOOL_IMPL_FALSE2  -- 21
  · injection h with h; subst h; exact sound_BOOL_IMPL_TRUE1  -- 22
  · injection h with h; subst h; exact sound_BOOL_IMPL_TRUE2  -- 23
  · injection h with h; subst h; exact sound_BOOL_IMPL_ELIM  -- 24
  · injection h with h; subst h; exact sound_BOOL_DUAL_IMPL_EQ  -- 25
  · injection h with h; subst h; exact sound_BOOL_AND_CONF  -- 26
  · injection h with h; subst h; exact sound_BOOL_AND_CONF2  -- 27
  · injection h with h; subst h; exact sound_BOOL_OR_TAUT  -- 28
  · injection h with h; subst h; exact sound_BOOL_OR_TAUT2  -- 29
  · injection h with h; subst h; exact sound_BOOL_IMPLIES_DE_MORGAN  -- 30
  · injection h with h; subst h; exact sound_BOOL_XOR_REFL  -- 31
  · injection h with h; subst h; exact sound_BOOL_XOR_NREFL  -- 32
  · injection h with h; subst h; exact sound_BOOL_XOR_FALSE  -- 33
  · injection h with h; subst h; exact sound_BOOL_XOR_TRUE  -- 34
  · injection h with h; subst h; exact sound_BOOL_XOR_COMM  -- 35
  · injection h with h; subst h; exact sound_BOOL_XOR_ELIM  -- 36
  · injection h with h; subst h; exact sound_BOOL_NOT_XOR_ELIM  -- 37
  · injection h with h; subst h; exact sound_BOOL_NOT_EQ_ELIM1  -- 38
  · injection h with h; subst h; exact sound_BOOL_NOT_EQ_ELIM2  -- 39
  · injection h with h; subst h; exact sound_ITE_NEG_BRANCH  -- 40
  · injection h with h; subst h; exact sound_ITE_THEN_TRUE  -- 41
  · injection h with h; subst h; exact sound_ITE_ELSE_FALSE  -- 42
  · injection h with h; subst h; exact sound_ITE_THEN_FALSE  -- 43
  · injection h with h; subst h; exact sound_ITE_ELSE_TRUE  -- 44
  · injection h with h; subst h; exact sound_ITE_THEN_LOOKAHEAD_SELF  -- 45
  · injection h with h; subst h; exact sound_ITE_ELSE_LOOKAHEAD_SELF  -- 46
  · injection h with h; subst h; exact sound_ITE_THEN_LOOKAHEAD_NOT_SELF  -- 47
  · injection h with h; subst h; exact sound_ITE_ELSE_LOOKAHEAD_NOT_SELF  -- 48
  · injection h with h; subst h; exact sound_ITE_EXPAND  -- 49
  · injection h with h; subst h; exact sound_BOOL_NOT_ITE_ELIM  -- 50
  · injection h with h; subst h; exact sound_BV_CONCAT_EXTRACT_MERGE  -- 51
  · injection h with h; subst h; exact sound_BV_EXTRACT_EXTRACT  -- 52
  · injection h with h; subst h; exact sound_BV_EXTRACT_WHOLE  -- 53
  · exact sound_BV_EXTRACT_CONCAT_1 _ (h ▸ rfl)  -- 54
  · exact sound_BV_EXTRACT_CONCAT_2 _ (h ▸ rfl)  -- 55
  · exact sound_BV_EXTRACT_CONCAT_3 _ (h ▸ rfl)  -- 56
  · exact sound_BV_EXTRACT_CONCAT_4 _ (h ▸ rfl)  -- 57
  · injection h with h; subst h; exact sound_BV_EQ_EXTRACT_ELIM1  -- 58
  · injection h with h; subst h; exact sound_BV_EQ_EXTRACT_ELIM2  -- 59
  · injection h with h; subst h; exact sound_BV_EQ_EXTRACT_ELIM3  -- 60
  · injection h with h; subst h; exact sound_BV_EXTRACT_NOT  -- 61
  · injection h with h; subst h; exact sound_BV_EXTRACT_SIGN_EXTEND_1  -- 62
  · injection h with h; subst h; exact sound_BV_EXTRACT_SIGN_EXTEND_2  -- 63
  · exact sound_BV_EXTRACT_SIGN_EXTEND_3 _ (h ▸ rfl)  -- 64
  · injection h with h; subst h; exact sound_BV_NOT_XOR  -- 65
  · injection h with h; subst h; exact sound_BV_AND_SIMPLIFY_1  -- 66
  · injection h with h; subst h; exact sound_BV_AND_SIMPLIFY_2  -- 67
  · injection h with h; subst h; exact sound_BV_OR_SIMPLIFY_1  -- 68
  · injection h with h; subst h; exact sound_BV_OR_SIMPLIFY_2  -- 69
  · injection h with h; subst h; exact sound_BV_XOR_SIMPLIFY_2  -- 70
  · injection h with h; subst h; exact sound_BV_XOR_SIMPLIFY_3  -- 71
  · injection h with h; subst h; exact sound_BV_ULT_ADD_ONE  -- 72
  · injection h with h; subst h; exact sound_BV_MULT_SLT_MULT_1  -- 73
  · injection h with h; subst h; exact sound_BV_MULT_SLT_MULT_2  -- 74
  · injection h with h; subst h; exact sound_BV_COMMUTATIVE_XOR  -- 75
  · injection h with h; subst h; exact sound_BV_ZERO_EXTEND_ELIMINATE_0  -- 76
  · injection h with h; subst h; exact sound_BV_SIGN_EXTEND_ELIMINATE_0  -- 77
  · injection h with h; subst h; exact sound_BV_NOT_NEQ  -- 78
  · injection h with h; subst h; exact sound_BV_ULT_ONES  -- 79
  · exact sound_BV_CONCAT_MERGE_CONST _ (h ▸ rfl)  -- 80
  · injection h with h; subst h; exact sound_BV_COMMUTATIVE_ADD  -- 81
  · injection h with h; subst h; exact sound_BV_SUB_ELIMINATE  -- 82
  · injection h with h; subst h; exact sound_BV_ITE_WIDTH_ONE  -- 83
  · injection h with h; subst h; exact sound_BV_ITE_WIDTH_ONE_NOT  -- 84
  · injection h with h; subst h; exact sound_BV_EQ_XOR_SOLVE  -- 85
  · injection h with h; subst h; exact sound_BV_EQ_NOT_SOLVE  -- 86
  · injection h with h; subst h; exact sound_BV_UGT_ELIMINATE  -- 87
  · injection h with h; subst h; exact sound_BV_UGE_ELIMINATE  -- 88
  · injection h with h; subst h; exact sound_BV_SGT_ELIMINATE  -- 89
  · injection h with h; subst h; exact sound_BV_SGE_ELIMINATE  -- 90
  · injection h with h; subst h; exact sound_BV_SLE_ELIMINATE  -- 91
  · injection h with h; subst h; exact sound_BV_ULE_ELIMINATE  -- 92
  · injection h with h; subst h; exact sound_BV_ZERO_EXTEND_ELIMINATE  -- 93
  · injection h with h; subst h; exact sound_BV_ITE_EQUAL_CHILDREN  -- 94
  · injection h with h; subst h; exact sound_BV_ITE_CONST_CHILDREN_1  -- 95
  · injection h with h; subst h; exact sound_BV_ITE_CONST_CHILDREN_2  -- 96
  · injection h with h; subst h; exact sound_BV_ITE_EQUAL_COND_1  -- 97
  · injection h with h; subst h; exact sound_BV_ITE_EQUAL_COND_2  -- 98
  · injection h with h; subst h; exact sound_BV_ITE_EQUAL_COND_3  -- 99
  · injection h with h; subst h; exact sound_BV_ITE_MERGE_THEN_IF  -- 100
  · injection h with h; subst h; exact sound_BV_ITE_MERGE_ELSE_IF  -- 101
  · injection h with h; subst h; exact sound_BV_ITE_MERGE_THEN_ELSE  -- 102
  · injection h with h; subst h; exact sound_BV_ITE_MERGE_ELSE_ELSE  -- 103
  · injection h with h; subst h; exact sound_BV_SHL_BY_CONST_0  -- 104
  · exact sound_BV_SHL_BY_CONST_1 _ (h ▸ rfl)  -- 105
  · injection h with h; subst h; exact sound_BV_SHL_BY_CONST_2  -- 106
  · injection h with h; subst h; exact sound_BV_LSHR_BY_CONST_0  -- 107
  · injection h with h; subst h; exact sound_BV_LSHR_BY_CONST_1  -- 108
  · injection h with h; subst h; exact sound_BV_LSHR_BY_CONST_2  -- 109
  · injection h with h; subst h; exact sound_BV_ASHR_BY_CONST_0  -- 110
  · exact sound_BV_ASHR_BY_CONST_1 _ (h ▸ rfl)  -- 111
  · injection h with h; subst h; exact sound_BV_ASHR_BY_CONST_2  -- 112
  · exact sound_BV_AND_CONCAT_PULLUP _ (h ▸ rfl)  -- 113
  · exact sound_BV_OR_CONCAT_PULLUP _ (h ▸ rfl)  -- 114
  · injection h with h; subst h; exact sound_BV_XOR_CONCAT_PULLUP  -- 115
  · exact sound_BV_AND_CONCAT_PULLUP2 _ (h ▸ rfl)  -- 116
  · exact sound_BV_OR_CONCAT_PULLUP2 _ (h ▸ rfl)  -- 117
  · injection h with h; subst h; exact sound_BV_XOR_CONCAT_PULLUP2  -- 118
  · injection h with h; subst h; exact sound_BV_AND_CONCAT_PULLUP3  -- 119
  · injection h with h; subst h; exact sound_BV_OR_CONCAT_PULLUP3  -- 120
  · injection h with h; subst h; exact sound_BV_XOR_CONCAT_PULLUP3  -- 121
  · injection h with h; subst h; exact sound_BV_XOR_DUPLICATE  -- 122
  · injection h with h; subst h; exact sound_BV_XOR_ONES  -- 123
  · injection h with h; subst h; exact sound_BV_ULE_MAX  -- 124
  · injection h with h; subst h; exact sound_BV_XOR_NOT  -- 125
  · injection h with h; subst h; exact sound_BV_NOT_IDEMP  -- 126
  · injection h with h; subst h; exact sound_BV_ULT_ZERO_1  -- 127
  · injection h with h; subst h; exact sound_BV_ULT_ZERO_2  -- 128
  · injection h with h; subst h; exact sound_BV_ULT_SELF  -- 129
  · injection h with h; subst h; exact sound_BV_LT_SELF  -- 130
  · injection h with h; subst h; exact sound_BV_ULE_SELF  -- 131
  · injection h with h; subst h; exact sound_BV_ULE_ZERO  -- 132
  · injection h with h; subst h; exact sound_BV_ZERO_ULE  -- 133
  · injection h with h; subst h; exact sound_BV_SLE_SELF  -- 134
  · injection h with h; subst h; exact sound_BV_NOT_ULT  -- 135
  · injection h with h; subst h; exact sound_BV_SHL_ZERO  -- 136
  · injection h with h; subst h; exact sound_BV_LSHR_ZERO  -- 137
  · injection h with h; subst h; exact sound_BV_ASHR_ZERO  -- 138
  · injection h with h; subst h; exact sound_BV_ULT_ONE  -- 139
  · injection h with h; subst h; exact sound_BV_MERGE_SIGN_EXTEND_1  -- 140
  · injection h with h; subst h; exact sound_BV_MERGE_SIGN_EXTEND_2  -- 141
  · injection h with h; subst h; exact sound_BV_SIGN_EXTEND_EQ_CONST_1  -- 142
  · injection h with h; subst h; exact sound_BV_SIGN_EXTEND_EQ_CONST_2  -- 143
  · injection h with h; subst h; exact sound_BV_ZERO_EXTEND_EQ_CONST_1  -- 144
  · injection h with h; subst h; exact sound_BV_ZERO_EXTEND_EQ_CONST_2  -- 145
  · exact sound_BV_ZERO_EXTEND_ULT_CONST_1 _ (h ▸ rfl)  -- 146
  · exact sound_BV_ZERO_EXTEND_ULT_CONST_2 _ (h ▸ rfl)  -- 147
  · injection h with h; subst h; exact sound_BV_SIGN_EXTEND_ULT_CONST_1  -- 148
  · injection h with h; subst h; exact sound_BV_SIGN_EXTEND_ULT_CONST_2  -- 149
  · injection h with h; subst h; exact sound_BV_SIGN_EXTEND_ULT_CONST_3  -- 150
  · injection h with h; subst h; exact sound_BV_SIGN_EXTEND_ULT_CONST_4  -- 151
  · injection h with h; subst h; exact sound_BV_XOR_SIMPLIFY_1  -- 152
  · injection h with h; subst h; exact sound_BOOL_AND_DE_MORGAN  -- 153
  · injection h with h; subst h; exact sound_BOOL_OR_DE_MORGAN  -- 154
  · injection h with h; subst h; exact sound_BOOL_IMPLIES_OR_DISTRIB  -- 155
  · injection h with h; subst h; exact sound_BOOL_OR_AND_DISTRIB  -- 156
  · injection h with h; subst h; exact sound_BV_MULT_POW2_1  -- 157
  · injection h with h; subst h; exact sound_BV_MULT_POW2_2  -- 158
  · injection h with h; subst h; exact sound_BV_MULT_POW2_2B  -- 159
  · injection h with h; subst h; exact sound_BV_UDIV_ONE  -- 161
  · injection h with h; subst h; exact sound_BV_UDIV_ZERO  -- 162
  · injection h with h; subst h; exact sound_BV_UREM_ONE  -- 163
  · injection h with h; subst h; exact sound_BV_UREM_SELF  -- 164
  · injection h with h; subst h; exact sound_BV_UGT_UREM  -- 165
  · exact absurd h (by simp)

end Bcf
