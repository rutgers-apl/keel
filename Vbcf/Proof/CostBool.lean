import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCore2
import Vbcf.Proof.CostLeaf

/-!
# Vbcf cost proofs: the basic and boolean rules

Cost lemmas for the rule functions of `Vbcf/Rules/Basic.lean` and
`Vbcf/Rules/Bool.lean` (and the `bl_*` helpers they share).  Every lemma has
slack `noSlack` and `Bm = 0`.  Per function: `(A ≥, B)`, lines of proof, and
how it was proved (`auto2`: `fncost_body; wpc_auto; wpc_done` alone; `loop`:
by hand around the loop(s)).

| function                   | A ≥ | B                  | lines | how |
|----------------------------|-----|--------------------|-------|-----|
| `r_assume`                 | –   | 100                | 5     | auto2 |
| `r_refl`, `r_true_intro`, `r_false_intro`, `r_false_elim`, `r_not_or_elim`, `r_not_implies_elim`, `bl_head_of` | 100 | 8600 | 6 | auto2 |
| `r_symm`, `r_split`, `bl_equiv_elim_clause`, `r_implies_elim`, `r_ite_elim`, `r_cnf_and_pos`, `r_cnf_or_neg`, `r_cnf_implies_neg` | 100 | 17200 | 6 | auto2 |
| `bl_not_equiv_elim_clause`, `bl_ite_eq_body`, `r_not_ite_elim`, `r_cnf_implies_pos`, `r_cnf_ite_pos`, `r_cnf_ite_neg` | 100 | 25800 | 6 | auto2 |
| `r_cnf_or_pos`             | 100 | 20000              | 6     | auto2 (calls `push`, `push_args`, `mkn`) |
| `r_and_intro`              | 100 | 10200               | 35    | loop paid by `push`'s slack, then `mkn` |
| `r_trans`                  | 100 | 25·np + 8600       | 25    | loop over `np` premises, no spending (`ck_hash` style) |
| `bl_mk_nots`               | 100 | 2200000            | 43    | loop over `n ≤ 255` args: `mk_not` (8600 each) + `push` (paid by its slack) |
| `r_cong`                   | 100 | 29000              | 78    | two loops paid by `push`'s slack, then 2×`mkn` + `mk_eq` |

`B` is a sum of the callees' allowances (`mk_*` 8500/8510, `mkn` 10100) plus a
margin.  No helpers were added.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000

theorem r_assume_cost (sb A : Nat) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_assume" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 100) 0 noSlack) := by
  apply FnCost.intro (fn := rAssume) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rAssume
  wpc_auto
  wpc_done

fncost_register "r_assume" rAssume r_assume_cost

theorem r_refl_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_refl" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 8600) 0 noSlack) := by
  apply FnCost.intro (fn := rRefl) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rRefl
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_refl" rRefl r_refl_cost

theorem r_symm_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_symm" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := rSymm) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rSymm
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_symm" rSymm r_symm_cost

theorem r_true_intro_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_true_intro" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 8600) 0 noSlack) := by
  apply FnCost.intro (fn := rTrueIntro) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rTrueIntro
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_true_intro" rTrueIntro r_true_intro_cost

theorem r_false_intro_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_false_intro" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 8600) 0 noSlack) := by
  apply FnCost.intro (fn := rFalseIntro) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rFalseIntro
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_false_intro" rFalseIntro r_false_intro_cost

theorem r_false_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_false_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 8600) 0 noSlack) := by
  apply FnCost.intro (fn := rFalseElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rFalseElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_false_elim" rFalseElim r_false_elim_cost

theorem r_not_or_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_not_or_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 8600) 0 noSlack) := by
  apply FnCost.intro (fn := rNotOrElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rNotOrElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_not_or_elim" rNotOrElim r_not_or_elim_cost

theorem r_split_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_split" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := rSplit) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rSplit
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_split" rSplit r_split_cost

theorem bl_equiv_elim_clause_cost (sb A : Nat) (hA : 100 ≤ A) (a b form : BitVec 32) :
    FnCost (State := State) Vbcf.prog "bl_equiv_elim_clause" (BudPre sb [.ptr sb 0, .u32 a, .u32 b, .u32 form])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := blEquivElimClause) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body blEquivElimClause
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "bl_equiv_elim_clause" blEquivElimClause bl_equiv_elim_clause_cost

theorem bl_not_equiv_elim_clause_cost (sb A : Nat) (hA : 100 ≤ A) (a b form : BitVec 32) :
    FnCost (State := State) Vbcf.prog "bl_not_equiv_elim_clause" (BudPre sb [.ptr sb 0, .u32 a, .u32 b, .u32 form])
      (Amort sb A (allow 25800) 0 noSlack) := by
  apply FnCost.intro (fn := blNotEquivElimClause) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body blNotEquivElimClause
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "bl_not_equiv_elim_clause" blNotEquivElimClause bl_not_equiv_elim_clause_cost

theorem bl_head_of_cost (sb A : Nat) (hA : 100 ≤ A) (e neg : BitVec 32) :
    FnCost (State := State) Vbcf.prog "bl_head_of" (BudPre sb [.ptr sb 0, .u32 e, .u32 neg])
      (Amort sb A (allow 8600) 0 noSlack) := by
  apply FnCost.intro (fn := blHeadOf) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body blHeadOf
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "bl_head_of" blHeadOf bl_head_of_cost

theorem bl_ite_eq_body_cost (sb A : Nat) (hA : 100 ≤ A) (e c a b : BitVec 32) :
    FnCost (State := State) Vbcf.prog "bl_ite_eq_body" (BudPre sb [.ptr sb 0, .u32 e, .u32 c, .u32 a, .u32 b])
      (Amort sb A (allow 25800) 0 noSlack) := by
  apply FnCost.intro (fn := blIteEqBody) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body blIteEqBody
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "bl_ite_eq_body" blIteEqBody bl_ite_eq_body_cost

theorem r_implies_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_implies_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := rImpliesElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rImpliesElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_implies_elim" rImpliesElim r_implies_elim_cost

theorem r_not_implies_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_not_implies_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 8600) 0 noSlack) := by
  apply FnCost.intro (fn := rNotImpliesElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rNotImpliesElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_not_implies_elim" rNotImpliesElim r_not_implies_elim_cost

theorem r_ite_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_ite_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := rIteElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rIteElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_ite_elim" rIteElim r_ite_elim_cost

theorem r_not_ite_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_not_ite_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 25800) 0 noSlack) := by
  apply FnCost.intro (fn := rNotIteElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rNotIteElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_not_ite_elim" rNotIteElim r_not_ite_elim_cost

theorem r_cnf_and_pos_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_and_pos" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfAndPos) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfAndPos
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_and_pos" rCnfAndPos r_cnf_and_pos_cost

theorem r_cnf_or_pos_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_or_pos" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 20000) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfOrPos) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfOrPos
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_or_pos" rCnfOrPos r_cnf_or_pos_cost

theorem r_cnf_or_neg_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_or_neg" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfOrNeg) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfOrNeg
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_or_neg" rCnfOrNeg r_cnf_or_neg_cost

theorem r_cnf_implies_pos_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_implies_pos" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 25800) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfImpliesPos) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfImpliesPos
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_implies_pos" rCnfImpliesPos r_cnf_implies_pos_cost

theorem r_cnf_implies_neg_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_implies_neg" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17200) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfImpliesNeg) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfImpliesNeg
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_implies_neg" rCnfImpliesNeg r_cnf_implies_neg_cost

theorem r_cnf_ite_pos_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_ite_pos" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 25800) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfItePos) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfItePos
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_ite_pos" rCnfItePos r_cnf_ite_pos_cost

theorem r_cnf_ite_neg_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_ite_neg" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 25800) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfIteNeg) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfIteNeg
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_ite_neg" rCnfIteNeg r_cnf_ite_neg_cost
theorem r_and_intro_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_and_intro" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 10200) 0 noSlack) := by
  apply FnCost.intro (fn := rAndIntro) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rAndIntro
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done
  rename_i base
  apply WPC.while
    (I := fun env' st' k => ∃ i ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("i", .u32, .u32 i), ("ok", .u32, .u32 ok), ("r", .u32, .u32 0), ("base", .u32, .u32 base)] ∧
      i.toNat ≤ np.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => np.toNat - envU32 env' "i")
  · exact ⟨_, _, rfl, by simp, w, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < np.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq
  wpc_call
  name_bud st5 w5 mm5 hb5
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.assign
  embc_simp
  simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
  refine ⟨by omega, by omega, _, _, hb5, ?_, ?_⟩ <;> cost_arith

fncost_register "r_and_intro" rAndIntro r_and_intro_cost

theorem r_trans_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_trans" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow (25 * np.toNat + 8600)) 0 noSlack) := by
  apply FnCost.intro (fn := rTrans) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rTrans
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done
  rename_i p0 lhs rhs0
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ p rhs i : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("p", .u32, .u32 p), ("lhs", .u32, .u32 lhs), ("rhs", .u32, .u32 rhs), ("i", .u32, .u32 i),
        ("r", .u32, .u32 0)] ∧
      i.toNat ≤ np.toNat + 1 ∧ k.t ≤ 25 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => np.toNat - envU32 env' "i")
  · exact ⟨rfl, _, _, _, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, p, rhs, i, rfl, hin, hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < np.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals loop_next hi1

fncost_register "r_trans" rTrans r_trans_cost

theorem bl_mk_nots_cost (sb A : Nat) (hA : 100 ≤ A) (id : BitVec 32) :
    FnCost (State := State) Vbcf.prog "bl_mk_nots" (BudPre sb [.ptr sb 0, .u32 id])
      (Amort sb A (allow 2200000) 0 noSlack) := by
  apply FnCost.intro (fn := blMkNots) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body blMkNots
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  rename_i n hn
  apply WPC.while
    (I := fun env' st' k => ∃ i r ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, .u32 id), ("n", .u32, .u32 n),
        ("i", .u32, .u32 i), ("r", .u32, .u32 r), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat + 8600 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨_, _, _, rfl, by simp, w, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, r, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq
  wpc_call
  name_bud st5 w5 mm5 hb5
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  wpc_call
  name_bud st6 w6 mm6 hb6
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.assign
  embc_simp
  simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
  refine ⟨by omega, by omega, _, _, hb6, ?_, ?_⟩ <;> cost_arith

fncost_register "bl_mk_nots" blMkNots bl_mk_nots_cost

theorem r_cong_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cong" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 29000) 0 noSlack) := by
  apply FnCost.intro (fn := rCong) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCong
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done
  rename_i hdr base
  -- first loop: push the left sides, each iteration paid by `push`'s slack
  apply WPC.while
    (I := fun env' st' k => ∃ i p ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 (hdr &&& 255#32)), ("i", .u32, .u32 i),
        ("p", .u32, .u32 p), ("ok", .u32, .u32 ok), ("l", .u32, .u32 0), ("r", .u32, .u32 0),
        ("base", .u32, .u32 base)] ∧
      i.toNat ≤ np.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => np.toNat - envU32 env' "i")
  · exact ⟨_, _, _, rfl, by simp, w, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, p, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- second loop: push the right sides
    wpc_auto
    apply WPC.while
      (I := fun env'' st'' k2 => ∃ i2 p2 ok2 : BitVec 32,
        env'' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
          ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 (hdr &&& 255#32)), ("i", .u32, .u32 i2),
          ("p", .u32, .u32 p2), ("ok", .u32, .u32 ok2), ("l", .u32, .u32 0), ("r", .u32, .u32 0),
          ("base", .u32, .u32 base)] ∧
        i2.toNat ≤ np.toNat ∧ ∃ w'' mm'' : BitVec 32, Budget st''.mem sb w'' mm'' ∧
          k2.t + A * w''.toNat ≤ A * w'.toNat ∧ k2.m + mm''.toNat ≤ mm'.toNat)
      (μ := fun env'' _ => np.toNat - envU32 env'' "i")
    · exact ⟨_, _, _, rfl, by simp, w', mm', hb', by simp, by simp⟩
    rintro env'' st'' k2 ⟨i2, p2, ok2, rfl, hin2, w'', mm'', hb'', hk2, hkm2⟩
    embc_simp
    refine ⟨fun hge2 => ?_, fun hlt2 => ?_⟩
    · wpc_auto
      wpc_done
    have hlt2' : i2.toNat < np.toNat := by simpa [BitVec.lt_def] using hlt2
    have hi21 : (i2 + 1#32).toNat = i2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq
    wpc_step
    apply WPC.seq
    wpc_call
    name_bud st6 w6 mm6 hb6
    apply WPC.seq
    wpc_ite_case
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    apply WPC.assign
    embc_simp
    simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi21]
    refine ⟨by omega, by omega, _, _, hb6, ?_, ?_⟩ <;> cost_arith
  have hlt' : i.toNat < np.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq
  wpc_step
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  wpc_call
  name_bud st5 w5 mm5 hb5
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.assign
  embc_simp
  simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
  refine ⟨by omega, by omega, _, _, hb5, ?_, ?_⟩ <;> cost_arith

fncost_register "r_cong" rCong r_cong_cost

end Vbcf.Proof
