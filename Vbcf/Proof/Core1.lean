import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rules

/-!
# Vbcf proofs: the smallest core functions
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

/-- What `tick` does to the state. -/
def tickM (c : CMem) : BitVec 32 × CMem :=
  if c.k.work = 0 then (0, { c with k := { c.k with err := 2 } })
  else (1, { c with k := { c.k with work := c.k.work - 1 } })

/-- `tick` changes only `work` and `err`. -/
theorem tickM_wev (c : CMem) :
    (tickM c).2 = c.wev (tickM c).2.k.work (tickM c).2.k.err c.k.val := by
  unfold tickM; split <;> rfl

/-- When `tick` fails it sets the error flag. -/
theorem tickM_err (c : CMem) (h : (tickM c).1 = 0#32) : (tickM c).2.k.err = 2#32 := by
  unfold tickM at *; split at * <;> simp_all

/-- What `spend(st, k)` does to the state. -/
def spendM (c : CMem) (k : BitVec 32) : BitVec 32 × CMem :=
  if c.k.work < k then (0, { c with k := { c.k with err := 2 } })
  else (1, { c with k := { c.k with work := c.k.work - k } })

/-- `spend` changes only `work` and `err`. -/
theorem spendM_wev (c : CMem) (k : BitVec 32) :
    (spendM c k).2 = c.wev (spendM c k).2.k.work (spendM c k).2.k.err c.k.val := by
  unfold spendM; split <;> rfl

/-- When `spend` fails it sets the error flag. -/
theorem spendM_err (c : CMem) (k : BitVec 32) (h : (spendM c k).1 = 0#32) :
    (spendM c k).2.k.err = 2#32 := by
  unfold spendM at *; split at * <;> simp_all

/-- `spend` returns 0 or 1. -/
theorem spendM_fst (c : CMem) (k : BitVec 32) : (spendM c k).1 = 0#32 ∨ (spendM c k).1 = 1#32 := by
  unfold spendM; split <;> simp

/-- When `spend` succeeds it spent `k`. -/
theorem spendM_ok (c : CMem) (k : BitVec 32) (h : (spendM c k).1 ≠ 0#32) :
    k ≤ c.k.work ∧ (spendM c k).2.k.work = c.k.work - k ∧ (spendM c k).2.k.err = c.k.err := by
  unfold spendM at h ⊢
  by_cases hlt : c.k.work < k
  · simp [hlt] at h
  · simp only [hlt, ↓reduceIte]
    refine ⟨?_, by simp, by simp⟩
    rw [BitVec.le_def]; rw [BitVec.lt_def] at hlt; omega

theorem tick_spec (W : World) (sb : Nat) (c : CMem) :
    FnSpec (State := State) Vbcf.prog "tick"
      (fun vs st => vs = [.ptr sb 0] ∧ Holds W st.mem sb c)
      (fun _ _ rv st' => rv = some (.u32 (tickM c).1) ∧ Holds W st'.mem sb (tickM c).2) := by
  have hs := prog_ck
  apply FnSpec.intro (fn := tick) rfl
  rintro vs st ⟨rfl, h⟩
  refine ⟨[("st", .ptr (.struct "ck"), .ptr sb 0)], ?_, ?_⟩
  · simp [tick, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [tick, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append]
  apply WP.seq
  apply WP.ite
  ck_simp
  constructor
  · intro hw
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro st h
    apply WP.ret
    ck_simp [retPost, tickM, hw]
    simpa [hw] using h
  · intro hw
    apply WP.skip
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro st h
    apply WP.ret
    ck_simp [retPost, tickM, hw]
    exact h

theorem spend_spec (W : World) (sb : Nat) (c : CMem) (k : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "spend"
      (fun vs st => vs = [.ptr sb 0, .u32 k] ∧ Holds W st.mem sb c)
      (fun _ _ rv st' => rv = some (.u32 (spendM c k).1) ∧ Holds W st'.mem sb (spendM c k).2) := by
  have hs := prog_ck
  apply FnSpec.intro (fn := spend) rfl
  rintro vs st ⟨rfl, h⟩
  refine ⟨[("st", .ptr (.struct "ck"), .ptr sb 0), ("k", .u32, .u32 k)], ?_, ?_⟩
  · simp [spend, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [spend, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append]
  apply WP.seq
  apply WP.ite
  ck_simp
  constructor
  · intro hw
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro st h
    apply WP.ret
    ck_simp [retPost, spendM, hw]
    simpa [hw] using h
  · intro hw
    have hnlt : ¬ c.k.work < k := by
      first
      | exact hw
      | (rw [BitVec.lt_def]; rw [BitVec.le_def] at hw; omega)
      | (intro hlt; exact absurd hlt hw)
    apply WP.skip
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro st h
    apply WP.ret
    ck_simp [retPost]
    unfold spendM
    rw [ite_eq_right hnlt]
    exact ⟨rfl, h⟩

end Vbcf.Proof
