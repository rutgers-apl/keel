import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostBool2
import Vbcf.Proof.CostMid
import Vbcf.Proof.CostEvalRw
import Vbcf.Proof.CostRules

/-!
# Vbcf cost proofs: the rule dispatcher `ck_rule`

`ck_rule` is `r = NOID;` followed by a 50-way `if`/`else if` costChain, one call
per rule, and `return r;`.  Proving the costChain branch by branch (`wpc_auto`)
takes too long (51 leaves, each with a 50-deep cost sum), so the costChain is
described as `costChain costRuleTable` and proved once by induction on the table
(`WPC.costRuleChain`): each level costs the test, and a taken branch costs its
rule.  The allowance is the largest rule allowance (`r_bitblast`, 5410000)
plus the parts that grow with the premise and argument counts (`r_resolution`
`500 * np`, `r_factoring` `80 * na`, `r_trans` `25 * np`), plus 1000 for the
dispatch itself; `ruleAllowC` is its value for byte-sized counts, as
`ck_step` passes them.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

/-- Weaken the allowance of an `Amort` cost lemma. -/
theorem FnCost.allowLe {f : String} {pre : List Val → (KernelState prog State) → Prop} {sb A B B' : Nat}
    (h : FnCost (State := State) prog f pre (Amort sb A (allow B) 0 noSlack)) (hB : B ≤ B') :
    FnCost (State := State) prog f pre (Amort sb A (allow B') 0 noSlack) :=
  FnCost.mono h (fun _ _ h => h) (fun _ _ _ _ _ _ h =>
    Amort.mono h (by simp only [allow_apply]; exact hB) (Nat.le_refl _) (Nat.le_refl _))

/-- The rule codes and the functions they dispatch to, in the order of the C. -/
def costRuleTable : List (BitVec 32 × String) := [
  (0x0001#32, "r_assume"),
  (0x0002#32, "r_evaluate"),
  (0x0003#32, "r_distinct_values"),
  (0x0004#32, "r_aci_norm"),
  (0x0005#32, "r_absorb"),
  (0x0006#32, "r_rewrite"),
  (0x0007#32, "r_refl"),
  (0x0008#32, "r_symm"),
  (0x0009#32, "r_trans"),
  (0x000a#32, "r_cong"),
  (0x000b#32, "r_true_intro"),
  (0x000c#32, "r_true_elim"),
  (0x000d#32, "r_false_intro"),
  (0x000e#32, "r_false_elim"),
  (0x2001#32, "r_resolution"),
  (0x2002#32, "r_factoring"),
  (0x2003#32, "r_reordering"),
  (0x2004#32, "r_split"),
  (0x2005#32, "r_eq_resolve"),
  (0x2006#32, "r_modus_ponens"),
  (0x2007#32, "r_not_not_elim"),
  (0x2008#32, "r_contra"),
  (0x2009#32, "r_and_elim"),
  (0x200a#32, "r_and_intro"),
  (0x200b#32, "r_not_or_elim"),
  (0x200c#32, "r_implies_elim"),
  (0x200d#32, "r_not_implies_elim"),
  (0x200e#32, "r_equiv_elim"),
  (0x200f#32, "r_not_equiv_elim"),
  (0x2010#32, "r_xor_elim"),
  (0x2011#32, "r_not_xor_elim"),
  (0x2012#32, "r_ite_elim"),
  (0x2013#32, "r_not_ite_elim"),
  (0x2014#32, "r_not_and"),
  (0x2015#32, "r_cnf_and_pos"),
  (0x2016#32, "r_cnf_and_neg"),
  (0x2017#32, "r_cnf_or_pos"),
  (0x2018#32, "r_cnf_or_neg"),
  (0x2019#32, "r_cnf_implies_pos"),
  (0x201a#32, "r_cnf_implies_neg"),
  (0x201b#32, "r_cnf_equiv_pos"),
  (0x201c#32, "r_cnf_equiv_neg"),
  (0x201d#32, "r_cnf_xor_pos"),
  (0x201e#32, "r_cnf_xor_neg"),
  (0x201f#32, "r_cnf_ite_pos"),
  (0x2020#32, "r_cnf_ite_neg"),
  (0x2021#32, "r_ite_eq"),
  (0x4001#32, "r_bitblast"),
  (0x4002#32, "r_poly_norm"),
  (0x4003#32, "r_poly_norm_eq")]

/-- The `if`/`else if` costChain of `ck_rule` over a table. -/
def costChain : List (BitVec 32 × String) → Stmt
  | [] => .skip
  | (k, f) :: rest =>
    .ite (.bin .eq (.var "rule") (.lit32 k)) (.call (some "r") f [.var "st", .var "np", .var "na"]) (costChain rest)

/-- The cost of a dispatch costChain: one level per test, plus the taken rule's cost. -/
theorem WPC.costRuleChain (sb A B : Nat) (np na : BitVec 32) (l : List (BitVec 32 × String))
    (hall : ∀ p ∈ l, FnCost (State := State) prog p.2 (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow B) 0 noSlack))
    {env : Env} {st : (KernelState prog State)} {w mm : BitVec 32} (hb : Budget st.mem sb w mm)
    (hst : env.get "st" = some (.ptr sb 0)) (hnp : env.get "np" = some (.u32 np))
    (hna : env.get "na" = some (.u32 na)) :
    WPC prog (costChain l) (fun o _ st' c => o = .normal ∧ ∃ w' mm' : BitVec 32,
      Budget st'.mem sb w' mm' ∧ c.t + A * w'.toNat ≤ A * w.toNat + B + 3 * l.length + 1 ∧
      c.m + mm'.toNat ≤ mm.toNat) env st := by
  induction l with
  | nil =>
    apply WPC.skip
    refine ⟨rfl, w, mm, hb, ?_, ?_⟩
    · cost_arith
    · simp
  | cons p rest ih =>
    obtain ⟨k, f⟩ := p
    apply WPC.ite_any
    · apply WPC.call (hall (k, f) (List.mem_cons_self ..))
      simp only [evalArgs, evalE, hst, hnp, hna]
      refine ⟨⟨rfl, w, mm, hb⟩, ?_⟩
      rintro rv st' c ⟨w', mm', hb', ht, hm⟩
      rw [Budget.wk hb] at ht
      rw [Budget.mk hb] at hm
      split
      · trivial
      refine ⟨rfl, w', mm', hb', ?_, ?_⟩ <;> cost_simp <;> (try simp only [List.length_cons]) <;> omega
    · apply WPC.mono (ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)))
      rintro o env' st' c ⟨rfl, w', mm', hb', ht, hm⟩
      refine ⟨rfl, w', mm', hb', ?_, ?_⟩ <;> cost_simp <;> (try simp only [List.length_cons]) <;> omega

/-- Every rule's lemma, weakened to the common allowance. -/
theorem ruleTable_all (sb A : Nat) (hA : 2000 ≤ A) (np na : BitVec 32) :
    ∀ p ∈ costRuleTable, FnCost (State := State) prog p.2 (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow (5410000 + 500 * np.toNat + 80 * na.toNat)) 0 noSlack) := by
  have h100 : 100 ≤ A := by omega
  have h150 : 150 ≤ A := by omega
  have h400 : 400 ≤ A := by omega
  have h300 : 300 ≤ A := by omega
  intro p hp
  simp only [costRuleTable, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact FnCost.allowLe (r_assume_cost sb A np na) (by omega)
  · exact FnCost.allowLe (r_evaluate_cost sb A hA np na) (by omega)
  · exact FnCost.allowLe (r_distinct_values_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_aci_norm_cost sb A h150 np na) (by omega)
  · exact FnCost.allowLe (r_absorb_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_rewrite_cost sb A hA np na) (by omega)
  · exact FnCost.allowLe (r_refl_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_symm_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_trans_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cong_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_true_intro_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_true_elim_cost sb A np na) (by omega)
  · exact FnCost.allowLe (r_false_intro_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_false_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_resolution_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_factoring_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_reordering_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_split_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_eq_resolve_cost sb A np na) (by omega)
  · exact FnCost.allowLe (r_modus_ponens_cost sb A np na) (by omega)
  · exact FnCost.allowLe (r_not_not_elim_cost sb A np na) (by omega)
  · exact FnCost.allowLe (r_contra_cost sb A np na) (by omega)
  · exact FnCost.allowLe (r_and_elim_cost sb A np na) (by omega)
  · exact FnCost.allowLe (r_and_intro_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_not_or_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_implies_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_not_implies_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_equiv_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_not_equiv_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_xor_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_not_xor_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_ite_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_not_ite_elim_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_not_and_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_and_pos_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_and_neg_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_or_pos_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_or_neg_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_implies_pos_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_implies_neg_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_equiv_pos_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_equiv_neg_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_xor_pos_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_xor_neg_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_ite_pos_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_cnf_ite_neg_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_ite_eq_cost sb A h100 np na) (by omega)
  · exact FnCost.allowLe (r_bitblast_cost sb A h300 np na) (by omega)
  · exact FnCost.allowLe (r_poly_norm_cost sb A h400 np na) (by omega)
  · exact FnCost.allowLe (r_poly_norm_eq_cost sb A h100 np na) (by omega)

/-- The dispatcher's allowance when the counts are bytes (as `ck_step` passes them). -/
def ruleAllowC : Nat := 5411000 + 500 * 255 + 80 * 255

theorem ck_rule_cost (sb A : Nat) (hA : 2000 ≤ A) (rule np na : BitVec 32) :
    FnCost (State := State) prog "ck_rule" (BudPre sb [.ptr sb 0, .u32 rule, .u32 np, .u32 na])
      (Amort sb A (allow (5411000 + 500 * np.toNat + 80 * na.toNat)) 0 noSlack) := by
  apply FnCost.intro (fn := ckRule) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckRule
  -- r = NOID;
  apply WPC.seq
  wpc_step
  -- the costChain, then `return r;`
  apply WPC.seq
  apply WPC.mono (WPC.costRuleChain sb A _ np na costRuleTable (ruleTable_all sb A hA np na) ‹Budget _ _ _ _› rfl rfl rfl)
  rintro o env' st' c ⟨rfl, w', mm', hb', ht, hm⟩
  apply WPC.ret_val
  intro v _
  have hlen : costRuleTable.length = 50 := rfl
  wpc_finish

-- Not registered: `ck_rule` is only called by `ck_step`, whose lemma takes this one as a
-- hypothesis (`CostTop.lean`).

end Vbcf.Proof
