import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostBool

/-!
# Vbcf cost proofs: the boolean CNF and elimination rules

Cost lemmas for the remaining rule functions of `Vbcf/Rules/Bool.lean`.
Every lemma has `A ≥ 100`, slack `noSlack`, `Bm = 0`, 6 lines of proof, and
was proved by `fncost_body; wpc_auto; wpc_done` alone (auto).  `B` is the sum
of the callees' allowances (`bl_head_of` 8600, `mk_not` 8510, `mk3` 8500,
`mkn` 10100, `bl_mk_nots` 2200000, `bl_equiv_elim_clause` 17200,
`bl_not_equiv_elim_clause`/`bl_ite_eq_body` 25800) plus a margin.

| function                                   | B       |
|--------------------------------------------|---------|
| `bl_cnf_neg_clause`                        | 36000   |
| `bl_cnf_pos_clause`                        | 26600   |
| `r_cnf_and_neg`, `r_not_and`               | 2220000 |
| `r_cnf_equiv_neg`, `r_cnf_xor_pos`         | 37000   |
| `r_cnf_equiv_pos`, `r_cnf_xor_neg`         | 28000   |
| `r_equiv_elim`, `r_not_xor_elim`           | 18500   |
| `r_not_equiv_elim`, `r_xor_elim`, `r_ite_eq` | 27200 |

No helpers were added.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000

theorem bl_cnf_neg_clause_cost (sb A : Nat) (hA : 100 ≤ A) (e a b lit neg : BitVec 32) :
    FnCost (State := State) Vbcf.prog "bl_cnf_neg_clause" (BudPre sb [.ptr sb 0, .u32 e, .u32 a, .u32 b, .u32 lit, .u32 neg])
      (Amort sb A (allow 36000) 0 noSlack) := by
  apply FnCost.intro (fn := blCnfNegClause) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body blCnfNegClause
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "bl_cnf_neg_clause" blCnfNegClause bl_cnf_neg_clause_cost

theorem bl_cnf_pos_clause_cost (sb A : Nat) (hA : 100 ≤ A) (e a b form neg : BitVec 32) :
    FnCost (State := State) Vbcf.prog "bl_cnf_pos_clause" (BudPre sb [.ptr sb 0, .u32 e, .u32 a, .u32 b, .u32 form, .u32 neg])
      (Amort sb A (allow 26600) 0 noSlack) := by
  apply FnCost.intro (fn := blCnfPosClause) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body blCnfPosClause
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "bl_cnf_pos_clause" blCnfPosClause bl_cnf_pos_clause_cost

theorem r_cnf_and_neg_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_and_neg" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 2220000) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfAndNeg) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfAndNeg
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_and_neg" rCnfAndNeg r_cnf_and_neg_cost

theorem r_cnf_equiv_neg_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_equiv_neg" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 37000) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfEquivNeg) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfEquivNeg
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_equiv_neg" rCnfEquivNeg r_cnf_equiv_neg_cost

theorem r_cnf_equiv_pos_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_equiv_pos" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 28000) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfEquivPos) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfEquivPos
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_equiv_pos" rCnfEquivPos r_cnf_equiv_pos_cost

theorem r_cnf_xor_neg_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_xor_neg" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 28000) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfXorNeg) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfXorNeg
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_xor_neg" rCnfXorNeg r_cnf_xor_neg_cost

theorem r_cnf_xor_pos_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_cnf_xor_pos" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 37000) 0 noSlack) := by
  apply FnCost.intro (fn := rCnfXorPos) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rCnfXorPos
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_cnf_xor_pos" rCnfXorPos r_cnf_xor_pos_cost

theorem r_equiv_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_equiv_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 18500) 0 noSlack) := by
  apply FnCost.intro (fn := rEquivElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rEquivElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_equiv_elim" rEquivElim r_equiv_elim_cost

theorem r_ite_eq_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_ite_eq" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 27200) 0 noSlack) := by
  apply FnCost.intro (fn := rIteEq) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rIteEq
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_ite_eq" rIteEq r_ite_eq_cost

theorem r_not_and_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_not_and" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 2220000) 0 noSlack) := by
  apply FnCost.intro (fn := rNotAnd) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rNotAnd
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_not_and" rNotAnd r_not_and_cost

theorem r_not_equiv_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_not_equiv_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 27200) 0 noSlack) := by
  apply FnCost.intro (fn := rNotEquivElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rNotEquivElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_not_equiv_elim" rNotEquivElim r_not_equiv_elim_cost

theorem r_not_xor_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_not_xor_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 18500) 0 noSlack) := by
  apply FnCost.intro (fn := rNotXorElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rNotXorElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_not_xor_elim" rNotXorElim r_not_xor_elim_cost

theorem r_xor_elim_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) Vbcf.prog "r_xor_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 27200) 0 noSlack) := by
  apply FnCost.intro (fn := rXorElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rXorElim
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "r_xor_elim" rXorElim r_xor_elim_cost

end Vbcf.Proof
