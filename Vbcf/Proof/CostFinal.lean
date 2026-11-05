import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostRule
import Vbcf.Proof.CostTop
import Vbcf.Proof.Final

/-!
# Vbcf: the cost bound of `vbcf_check_proof`

The per-function cost lemmas assembled: `vbcf_check_proof` on a proof of `n`
words (`n = proof_size / 4`) with a goal of `g` words runs within

* time `rateA * (128 * (n + g) + 2^20) + 16003 n + 7850 g + stepAllow + 28960` machine transitions and kernel-call work,
* memory `33 * n + 32 * g + 2^18 + 1306` words obtained from the allocator,

where `rateA` is the time paid per unit of the checker's own work budget and
`K` the fixed allowance of the driver (`costK`).  `vbcf_check_proof_sound_bounded`
combines this with the soundness theorem: every run finishes, with the cost
above, and its verdict is covered by `vbcf_check_proof_sound'`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

/-- The allowance of one proof step: the largest rule allowance plus the step's own work. -/
abbrev stepAllow : Nat := ruleAllowC + 4000

/-- Time paid per unit of work: enough to pay a whole proof step from the one unit it spends. -/
def rateA : Nat := stepAllow + 40

theorem rateA_ge : stepAllow + 40 ≤ rateA ∧ 6000 ≤ rateA ∧ 2000 ≤ rateA :=
  ⟨Nat.le_refl _, by decide, by decide⟩

/-- The fixed allowance of the driver, beyond `rateA * workBudget`:
`ck_init` (20000), `ck_load` and `ck_goal` (linear in the input), `ck_scan` (200), one proof
step left unpaid (`stepAllow`), and the drivers' own transitions (`ck_run`'s 400 include a
failing `ck_compact`, 200). -/
abbrev costK (n g : BitVec 32) : Nat :=
  20000 + (16000 * n.toNat + 100) + 200 + (7850 * g.toNat + 8100) + stepAllow + 400 + 120

theorem vbcf_check_proof_cost_final (gb : Nat) (g size : BitVec 32) (gx : Val)
    (hgx : gx = .null ∨ gx = .ptr gb 0) :
    FnCost (State := State) prog "vbcf_check_proof" (fun vs _ => vs = [gx, .u32 g, .uptr, .u32 size])
      (fun _ _ _ _ c =>
        c.t ≤ rateA * workBudget (size / 4#32) g + costK (size / 4#32) g + 3 * (size / 4#32).toNat + 40 ∧
        c.m ≤ memBudget (size / 4#32) g + 1306 + (size / 4#32).toNat) := by
  have ⟨hAs, hA6000, hA2000⟩ := rateA_ge
  have hA100 : 100 ≤ rateA := by omega
  apply vbcf_check_proof_cost rateA (fun n => costK n g) gb g size gx hgx
  intro pb n hn
  refine vbcf_check_cost rateA (20000 + (16000 * n.toNat + 100) + 200 + (7850 * g.toNat + 8100) + stepAllow + 400)
    pb gb n g hn gx hgx ?_
  intro sb
  have hL := ck_load_cost (State := State) sb rateA hA100 pb n
  have hS := ck_scan_cost (State := State) sb rateA hA100
  have hG := ck_goal_cost (State := State) sb rateA hA100 gb g
  have hRule : ∀ rule np na : BitVec 32, np.toNat ≤ 255 → na.toNat ≤ 255 → FnCost (State := State) prog "ck_rule"
      (BudPre sb [.ptr sb 0, .u32 rule, .u32 np, .u32 na]) (Amort sb rateA (allow ruleAllowC) 0 noSlack) :=
    fun rule np na hnp hna =>
      FnCost.allowLe (ck_rule_cost sb rateA hA2000 rule np na) (by simp only [ruleAllowC]; omega)
  have hStep := fun off => ck_step_cost (State := State) sb rateA ruleAllowC hA100 hRule off
  exact ck_run_cost sb rateA _ _ _ _ hAs hA6000 pb gb n g hn hL hS hG hStep gx hgx

/-- The bound with the budgets unfolded: linear in the input, with explicit constants. -/
theorem vbcf_check_proof_bounded (gb : Nat) (g size : BitVec 32) (gx : Val)
    (hgx : gx = .null ∨ gx = .ptr gb 0) :
    FnCost (State := State) prog "vbcf_check_proof" (fun vs _ => vs = [gx, .u32 g, .uptr, .u32 size])
      (fun _ _ _ _ c =>
        c.t ≤ rateA * (128 * (size.toNat / 4 + g.toNat) + 1048576) +
          (16003 * (size.toNat / 4) + 7850 * g.toNat + stepAllow + 28960) ∧
        c.m ≤ 33 * (size.toNat / 4) + 32 * g.toNat + 262144 + 1306) := by
  refine FnCost.mono (vbcf_check_proof_cost_final gb g size gx hgx) (fun _ _ h => h) ?_
  rintro vs st rv st' c - ⟨ht, hm⟩
  have h4 : (size / 4#32).toNat = size.toNat / 4 := by simp [BitVec.toNat_udiv]
  simp only [workBudget, memBudget, costK, h4, Nat.reducePow] at ht hm
  generalize rateA * (128 * (size.toNat / 4 + g.toNat) + 1048576) = T at ht ⊢
  exact ⟨by omega, by omega⟩

/-- The rate per unit of the checker's work budget once the driver's fixed and linear
allowances are folded in: `R * W(n, g)` bounds the time (`R ≤ 2^23`). -/
def costRate : Nat := rateA + 128

-- Administrative transitions must fit the established public rate.
#guard costRate = 5563068

theorem costRate_le : costRate ≤ 2 ^ 23 := by decide

/-- The tidy form: time at most `costRate` per unit of the work budget, memory at most the
memory budget plus the input buffer (`n` words) plus the fixed tables and struct (1306 words:
the hash table 1024, the premise array 256, the struct 26). -/
theorem vbcf_check_proof_bounded' (gb : Nat) (g size : BitVec 32) (gx : Val)
    (hgx : gx = .null ∨ gx = .ptr gb 0) :
    FnCost (State := State) prog "vbcf_check_proof" (fun vs _ => vs = [gx, .u32 g, .uptr, .u32 size])
      (fun _ _ _ _ c =>
        c.t ≤ costRate * workBudget (size / 4#32) g ∧
        c.m ≤ memBudget (size / 4#32) g + (size / 4#32).toNat + 1306) := by
  refine FnCost.mono (vbcf_check_proof_bounded gb g size gx hgx) (fun _ _ h => h) ?_
  rintro vs st rv st' c - ⟨ht, hm⟩
  have h4 : (size / 4#32).toNat = size.toNat / 4 := by simp [BitVec.toNat_udiv]
  have hW : costRate * workBudget (size / 4#32) g =
      rateA * (128 * (size.toNat / 4 + g.toNat) + 1048576) +
        128 * (128 * (size.toNat / 4 + g.toNat) + 1048576) := by
    simp only [costRate, workBudget, h4, Nat.add_mul, Nat.reducePow]
  have hK : 16003 * (size.toNat / 4) + 7850 * g.toNat + stepAllow + 28960 ≤
      128 * (128 * (size.toNat / 4 + g.toNat) + 1048576) := by
    have : stepAllow = 5411000 + 500 * 255 + 80 * 255 + 4000 := rfl
    omega
  constructor
  · rw [hW]
    exact Nat.le_trans ht (Nat.add_le_add_left hK _)
  · simp only [memBudget, h4, Nat.reducePow]
    omega

/-- The one-variable form.  With `N = n + g`, the proof's words plus the goal's arena
prefix (the two inputs the checker reads), time is at most `costRate * (128 * N + 2^20)`
machine transitions plus kernel work and memory at most `33 * N + 2^18 + 1306` words. -/
theorem vbcf_check_proof_bounded_N (gb : Nat) (g size : BitVec 32) (gx : Val)
    (hgx : gx = .null ∨ gx = .ptr gb 0) :
    FnCost (State := State) prog "vbcf_check_proof" (fun vs _ => vs = [gx, .u32 g, .uptr, .u32 size])
      (fun _ _ _ _ c =>
        c.t ≤ costRate * (128 * (size.toNat / 4 + g.toNat) + 2 ^ 20) ∧
        c.m ≤ 33 * (size.toNat / 4 + g.toNat) + 2 ^ 18 + 1306) := by
  refine FnCost.mono (vbcf_check_proof_bounded' gb g size gx hgx) (fun _ _ h => h) ?_
  rintro vs st rv st' c - ⟨ht, hm⟩
  have h4 : (size / 4#32).toNat = size.toNat / 4 := by simp [BitVec.toNat_udiv]
  simp only [workBudget, memBudget, h4, Nat.reducePow] at ht hm ⊢
  generalize costRate * (128 * (size.toNat / 4 + g.toNat) + 1048576) = T at ht ⊢
  exact ⟨ht, by omega⟩

/-- Every run of `vbcf_check_proof` finishes within the cost bound, and its verdict is the
one `vbcf_check_proof_sound'` describes (sound: a 0 means the proof refutes its goal). -/
theorem vbcf_check_proof_sound_bounded (ga : GArg) (goal size : BitVec 32) (st : (KernelState prog State))
    (hpre : ArenaIn st.mem goal.toNat ga) :
    ∃ fuel rv st' c,
      prog.run fuel "vbcf_check_proof" [gxVal ga, .u32 goal, .uptr, .u32 size] st = .ok (rv, st') ∧
      prog.runC fuel "vbcf_check_proof" [gxVal ga, .u32 goal, .uptr, .u32 size] st = .ok (rv, st', c) ∧
      ((∀ b, st'.mem.block? b = st.mem.block? b) ∧ ∃ r, rv = some (.u32 r) ∧
        (r = 0#32 → (∃ P g,
          Bcf.decode (wordsToBytes (copiedWords st (size.toNat / 4))) = .ok P ∧
          ∀ ρ, ¬ Bcf.holds P.pool ρ g) ∧ GoalRefuted goal.toNat ga)) ∧
      c.t ≤ rateA * (128 * (size.toNat / 4 + goal.toNat) + 1048576) +
          (16003 * (size.toNat / 4) + 7850 * goal.toNat + stepAllow + 28960) ∧
      c.m ≤ 33 * (size.toNat / 4) + 32 * goal.toNat + 262144 + 1306 := by
  have hgx : gxVal ga = .null ∨ gxVal ga = .ptr (match ga with | none => 0 | some (gb, _) => gb) 0 := by
    cases ga with
    | none => exact Or.inl rfl
    | some p => exact Or.inr rfl
  obtain ⟨fuel, rv, st', c, h1, h2, h3, h4⟩ :=
    FnCost.run (vbcf_check_proof_sound' ga goal size) (vbcf_check_proof_bounded _ goal size (gxVal ga) hgx)
      ⟨rfl, hpre⟩ rfl
  exact ⟨fuel, rv, st', c, h1, h2, h3, h4⟩

end Vbcf.Proof
