import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCore

/-!
# Vbcf cost proofs: call-free checker functions

Each allowance counts all EmbC machine transitions, including function entry
and administrative sequencing. The loop-free functions have direct body proofs
so frequently called bit-blast predicates retain tight allowances. Loops carry
explicit counter invariants; the stack transformations also require `SpPre`.
None of these functions spends work or allocates words. The `ck_free` contract
requires `FreeOk` for each freed field so the budget cells survive.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

/-! ## `Vbcf/Rules/Basic.lean` -/

theorem r_true_elim_cost (sb A : Nat) (np na : BitVec 32) :
    FnCost (State := State) prog "r_true_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na]) (Amort sb A (allow 14) 0 noSlack) := by
  apply FnCost.intro (fn := rTrueElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rTrueElim
  wpc_auto
  wpc_done

fncost_register "r_true_elim" rTrueElim r_true_elim_cost

theorem r_eq_resolve_cost (sb A : Nat) (np na : BitVec 32) :
    FnCost (State := State) prog "r_eq_resolve" (BudPre sb [.ptr sb 0, .u32 np, .u32 na]) (Amort sb A (allow 14) 0 noSlack) := by
  apply FnCost.intro (fn := rEqResolve) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rEqResolve
  wpc_auto
  wpc_done

fncost_register "r_eq_resolve" rEqResolve r_eq_resolve_cost

theorem r_modus_ponens_cost (sb A : Nat) (np na : BitVec 32) :
    FnCost (State := State) prog "r_modus_ponens" (BudPre sb [.ptr sb 0, .u32 np, .u32 na]) (Amort sb A (allow 14) 0 noSlack) := by
  apply FnCost.intro (fn := rModusPonens) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rModusPonens
  wpc_auto
  wpc_done

fncost_register "r_modus_ponens" rModusPonens r_modus_ponens_cost

theorem r_not_not_elim_cost (sb A : Nat) (np na : BitVec 32) :
    FnCost (State := State) prog "r_not_not_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na]) (Amort sb A (allow 17) 0 noSlack) := by
  apply FnCost.intro (fn := rNotNotElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rNotNotElim
  wpc_auto
  wpc_done

fncost_register "r_not_not_elim" rNotNotElim r_not_not_elim_cost

theorem r_contra_cost (sb A : Nat) (np na : BitVec 32) :
    FnCost (State := State) prog "r_contra" (BudPre sb [.ptr sb 0, .u32 np, .u32 na]) (Amort sb A (allow 14) 0 noSlack) := by
  apply FnCost.intro (fn := rContra) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rContra
  wpc_auto
  wpc_done

fncost_register "r_contra" rContra r_contra_cost

theorem r_and_elim_cost (sb A : Nat) (np na : BitVec 32) :
    FnCost (State := State) prog "r_and_elim" (BudPre sb [.ptr sb 0, .u32 np, .u32 na]) (Amort sb A (allow 17) 0 noSlack) := by
  apply FnCost.intro (fn := rAndElim) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rAndElim
  wpc_auto
  wpc_done

fncost_register "r_and_elim" rAndElim r_and_elim_cost

/-! ## `Vbcf/Rules/Eval.lean` -/

theorem udiv_w_cost (sb A : Nat) (x y m : BitVec 64) :
    FnCost (State := State) prog "udiv_w" (BudPre sb [.u64 x, .u64 y, .u64 m]) (Amort sb A (allow 5) 0 noSlack) := by
  apply FnCost.intro (fn := udivW) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body udivW
  wpc_auto
  wpc_done

fncost_register "udiv_w" udivW udiv_w_cost

theorem umod_w_cost (sb A : Nat) (x y : BitVec 64) :
    FnCost (State := State) prog "umod_w" (BudPre sb [.u64 x, .u64 y]) (Amort sb A (allow 5) 0 noSlack) := by
  apply FnCost.intro (fn := umodW) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body umodW
  wpc_auto
  wpc_done

fncost_register "umod_w" umodW umod_w_cost

/-! ## `Vbcf/Rules/Poly.lean` -/

theorem lin_get64_cost (sb A : Nat) (i : BitVec 32) :
    FnCost (State := State) prog "lin_get64" (BudPre sb [.ptr sb 0, .u32 i]) (Amort sb A (allow 2) 0 noSlack) := by
  apply FnCost.intro (fn := linGet64) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body linGet64
  wpc_auto
  wpc_done

fncost_register "lin_get64" linGet64 lin_get64_cost

/-! ## `Vbcf/Rules/Clause.lean` -/

theorem cl_erase_cost (sb A : Nat) (base pivot n : BitVec 32) :
    FnCost (State := State) prog "cl_erase"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 base, .u32 pivot] vs st ∧ SpPre sb base n st.mem)
      (Amort sb A (allow (10 * n.toNat + 20)) 0 noSlack) := by
  apply FnCost.intro (fn := clErase) rfl
  rintro vs st ⟨⟨rfl, w, mm, hb⟩, sp, hsp, hbn⟩
  fncost_body clErase
  have hspl := hsp.load fi_sp (by simp)
  apply WPC.seq
  wpc_step
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ i : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("pivot", .u32, .u32 pivot),
        ("i", .u32, .u32 i)] ∧
      base.toNat ≤ i.toNat ∧ i.toNat ≤ sp.toNat ∧ k.t ≤ 4 * (i.toNat - base.toNat) ∧ k.m = 0)
    (μ := fun env' _ => sp.toNat - envU32 env' "i")
  · exact ⟨rfl, base, rfl, by simp, by omega, by simp, by simp⟩
  rintro env' st' k ⟨rfl, i, rfl, hbi, hisp, hk, hkm⟩
  embc_simp [hspl]
  -- after the search: `i` is where `pivot` is, or `sp`
  have hexit : ∀ (k' : Cost), k'.t ≤ k.t + 3 → k'.m = 0 →
      WPC prog [cstms|
          if (i == st->sp) { return; }
          while (i + 1 < st->sp) {
            st->stk[i] = st->stk[i + 1];
            i = i + 1;
          }
          st->sp = st->sp - 1;]
        (((retPostC none (fun rv st'' cost => Amort sb A (allow (10 * n.toNat + 20)) 0 noSlack
          [Val.ptr sb 0, Val.u32 base, Val.u32 pivot] st' rv st'' (1 + cost))).shift (1 + 2)).shift k')
        [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("pivot", .u32, .u32 pivot),
          ("i", .u32, .u32 i)] st' := by
    intro k' hk' hkm'
    apply WPC.seq
    apply WPC.ite
    embc_simp [hspl]
    constructor
    · intro _
      wpc_auto
      wpc_finish
    intro hne
    have hlt : i.toNat < sp.toNat := by
      have : i.toNat ≠ sp.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
      omega
    apply WPC.skip
    wpc_simp
    apply WPC.seq
    apply WPC.while
      (I := fun env2 st2 k2 => ∃ i2 : BitVec 32,
        env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base),
          ("pivot", .u32, .u32 pivot), ("i", .u32, .u32 i2)] ∧
        Budget st2.mem sb w mm ∧ Fld st2.mem sb 11 (.u32 sp) ∧
        i.toNat ≤ i2.toNat ∧ i2.toNat < sp.toNat ∧ k2.t ≤ 6 * (i2.toNat - i.toNat) ∧ k2.m = 0)
      (μ := fun env2 _ => sp.toNat - envU32 env2 "i")
    · exact ⟨i, rfl, hb, hsp, by simp, hlt, by simp, by simp⟩
    rintro env2 st2 k2 ⟨i2, rfl, hb2, hsp2, hii2, hi2, hk2, hkm2⟩
    have hspl2 := hsp2.load fi_sp (by simp)
    have hi21 : (i2 + 1#32).toNat = i2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    embc_simp [hspl2]
    refine ⟨fun hge => ?_, fun hlt2 => ?body2⟩
    case body2 =>
      have hlt2' : i2.toNat + 1 < sp.toNat := by
        have := BitVec.lt_def.mp hlt2; rw [hi21] at this; exact this
      apply WPC.seq
      apply WPC.store_bud_fld hb2 hsp2
      intro m' hb3 hsp3
      wpc_simp
      apply WPC.assign
      embc_simp
      simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi21]
      refine ⟨by omega, hb3, hsp3, ?_⟩
      and_intros <;> cost_arith
    wpc_auto
    wpc_finish
  by_cases hle : sp ≤ i
  · simp only [hle, ↓reduceIte]
    refine ⟨fun _ => hexit _ (by cost_arith) (by cost_arith), fun h => (h trivial).elim⟩
  · simp only [hle, ↓reduceIte]
    split
    · rename_i v _
      refine ⟨fun _ => hexit _ (by cost_arith) (by cost_arith), fun _ => ?_⟩
      have hlt : i.toNat < sp.toNat := by
        have := BitVec.not_le.mp hle; exact BitVec.lt_def.mp this
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      apply WPC.assign
      embc_simp
      simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
      and_intros <;> omega
    · trivial

fncost_register "cl_erase" clErase cl_erase_cost

theorem cl_byte_cost (sb A : Nat) (k : BitVec 32) :
    FnCost (State := State) prog "cl_byte" (BudPre sb [.ptr sb 0, .u32 k]) (Amort sb A (allow 2) 0 noSlack) := by
  apply FnCost.intro (fn := clByte) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body clByte
  wpc_auto
  wpc_done

fncost_register "cl_byte" clByte cl_byte_cost

theorem cl_half_cost (sb A : Nat) (t : BitVec 32) :
    FnCost (State := State) prog "cl_half" (BudPre sb [.ptr sb 0, .u32 t]) (Amort sb A (allow 2) 0 noSlack) := by
  apply FnCost.intro (fn := clHalf) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body clHalf
  wpc_auto
  wpc_done

fncost_register "cl_half" clHalf cl_half_cost

/-! ## `Vbcf/Rules/Aci.lean` -/

theorem aci_assoc_cost (sb A : Nat) (hdr : BitVec 32) :
    FnCost (State := State) prog "aci_assoc" (BudPre sb [.u32 hdr]) (Amort sb A (allow 5) 0 noSlack) := by
  apply FnCost.intro (fn := aciAssoc) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body aciAssoc
  wpc_auto
  wpc_done

fncost_register "aci_assoc" aciAssoc aci_assoc_cost

theorem aci_same_cost (sb A : Nat) (rop hdr : BitVec 32) :
    FnCost (State := State) prog "aci_same" (BudPre sb [.u32 rop, .u32 hdr]) (Amort sb A (allow 5) 0 noSlack) := by
  apply FnCost.intro (fn := aciSame) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body aciSame
  wpc_auto
  wpc_done

fncost_register "aci_same" aciSame aci_same_cost

theorem aci_sort_cost (sb A : Nat) (base n : BitVec 32) :
    FnCost (State := State) prog "aci_sort"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 base] vs st ∧ SpPre sb base n st.mem ∧
        base.toNat < 4294967295)
      (Amort sb A (allow ((8 * n.toNat + 20) * n.toNat + 20)) 0 noSlack) := by
  apply FnCost.intro (fn := aciSort) rfl
  rintro vs st ⟨⟨rfl, w, mm, hb⟩, ⟨sp, hsp, hbn⟩, hbmax⟩
  fncost_body aciSort
  have hb1 : (base + 1#32).toNat = base.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq
  wpc_step
  apply WPC.while
    (I := fun env2 st2 k2 => ∃ i j x : BitVec 32,
      env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base),
        ("i", .u32, .u32 i), ("j", .u32, .u32 j), ("x", .u32, .u32 x)] ∧
      Budget st2.mem sb w mm ∧ Fld st2.mem sb 11 (.u32 sp) ∧
      base.toNat + 1 ≤ i.toNat ∧ (i.toNat ≤ sp.toNat ∨ i.toNat = base.toNat + 1) ∧
      k2.t ≤ (8 * n.toNat + 20) * (i.toNat - (base.toNat + 1)) ∧ k2.m = 0)
    (μ := fun env2 _ => sp.toNat - envU32 env2 "i")
  · exact ⟨_, _, _, rfl, hb, hsp, by omega, by omega, by simp, by simp⟩
  rintro env2 st2 k2 ⟨i, j, x, rfl, hb2, hsp2, hbi, hisp, hk2, hkm2⟩
  have hspl2 := hsp2.load fi_sp (by simp)
  embc_simp [hspl2]
  refine ⟨fun hge => ?_, fun hlt2 => ?body⟩
  case body =>
    have hlt2' : i.toNat < sp.toNat := BitVec.lt_def.mp hlt2
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    rename_i x1
    apply WPC.while
      (I := fun env3 st3 k3 => ∃ j : BitVec 32,
        env3 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base),
          ("i", .u32, .u32 i), ("j", .u32, .u32 j), ("x", .u32, .u32 x1)] ∧
        Budget st3.mem sb w mm ∧ Fld st3.mem sb 11 (.u32 sp) ∧
        base.toNat ≤ j.toNat ∧ j.toNat ≤ i.toNat ∧ k3.t ≤ 6 * (i.toNat - j.toNat) ∧ k3.m = 0)
      (μ := fun env3 _ => envU32 env3 "j")
    · exact ⟨i, rfl, hb2, hsp2, by omega, by omega, by simp, by simp⟩
    rintro env3 st3 k3 ⟨j3, rfl, hb3, hsp3, hbj, hji, hk3, hkm3⟩
    embc_simp
    have hC : k2.t + (6 * (i.toNat - j3.toNat) + 20) ≤
        (8 * n.toNat + 20) * (i.toNat + 1 - (base.toNat + 1)) := by
      rw [show i.toNat + 1 - (base.toNat + 1) = i.toNat - (base.toNat + 1) + 1 by omega]
      exact le_mul_succ hk2 (by omega)
    by_cases hle : j3 ≤ base
    · simp only [hle, ↓reduceIte]
      refine ⟨fun _ => ?_, fun h => (h trivial).elim⟩
      wpc_auto
      wpc_done
      all_goals loop_nextB hi1
    have hbj' : base.toNat < j3.toNat := by
      have := BitVec.not_le.mp hle; exact BitVec.lt_def.mp this
    have hj1 : (j3 - 1#32).toNat = j3.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [hle, ↓reduceIte]
    split
    · refine ⟨fun _ => ?_, fun _ => ?_⟩
      · wpc_auto
        wpc_done
        all_goals loop_nextB hi1
      · wpc_auto
        wpc_done
        all_goals loop_nextB hj1
    · trivial
  have hmn : i.toNat - (base.toNat + 1) ≤ n.toNat := by
    have := BitVec.le_def.mp hge
    omega
  have := Nat.mul_le_mul_left (8 * n.toNat + 20) hmn
  wpc_auto
  wpc_finish

fncost_register "aci_sort" aciSort aci_sort_cost

theorem aci_uniq_cost (sb A : Nat) (base n : BitVec 32) :
    FnCost (State := State) prog "aci_uniq"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 base] vs st ∧ SpPre sb base n st.mem)
      (Amort sb A (allow (10 * n.toNat + 20)) 0 noSlack) := by
  apply FnCost.intro (fn := aciUniq) rfl
  rintro vs st ⟨⟨rfl, w, mm, hb⟩, sp, hsp, hbn⟩
  fncost_body aciUniq
  have hspl := hsp.load fi_sp (by simp)
  apply WPC.seq
  apply WPC.ite
  embc_simp [hspl]
  constructor
  · intro _
    wpc_auto
    wpc_finish
  intro hne
  have hlt : base.toNat < sp.toNat := by
    have : sp.toNat ≠ base.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
    omega
  have hb1 : (base + 1#32).toNat = base.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  wpc_step
  apply WPC.seq
  wpc_step
  apply WPC.seq
  apply WPC.while
    (I := fun env2 st2 k2 => ∃ i j : BitVec 32,
      env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base),
        ("i", .u32, .u32 i), ("j", .u32, .u32 j)] ∧
      Budget st2.mem sb w mm ∧ Fld st2.mem sb 11 (.u32 sp) ∧
      base.toNat + 1 ≤ i.toNat ∧ i.toNat ≤ sp.toNat ∧ k2.t ≤ 10 * (i.toNat - (base.toNat + 1)) ∧ k2.m = 0)
    (μ := fun env2 _ => sp.toNat - envU32 env2 "i")
  · exact ⟨_, _, rfl, hb, hsp, by omega, by omega, by simp, by simp⟩
  rintro env2 st2 k2 ⟨i, j, rfl, hb2, hsp2, hbi, hisp, hk2, hkm2⟩
  have hspl2 := hsp2.load fi_sp (by simp)
  embc_simp [hspl2]
  refine ⟨fun hge => ?_, fun hlt2 => ?body⟩
  case body =>
    have hlt2' : i.toNat < sp.toNat := BitVec.lt_def.mp hlt2
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_nextB hi1
  wpc_auto
  wpc_done

fncost_register "aci_uniq" aciUniq aci_uniq_cost

/-! ## `Vbcf/Rules/Rewrite.lean` -/

theorem rw_ty_ok_cost (sb A : Nat) (pt t : BitVec 32) :
    FnCost (State := State) prog "rw_ty_ok" (BudPre sb [.u32 pt, .u32 t]) (Amort sb A (allow 23) 0 noSlack) := by
  apply FnCost.intro (fn := rwTyOk) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rwTyOk
  wpc_auto
  wpc_done

fncost_register "rw_ty_ok" rwTyOk rw_ty_ok_cost

theorem rw_cond_match_cost (sb A : Nat) (c p : BitVec 32) :
    FnCost (State := State) prog "rw_cond_match" (BudPre sb [.ptr sb 0, .u32 c, .u32 p]) (Amort sb A (allow 8) 0 noSlack) := by
  apply FnCost.intro (fn := rwCondMatch) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rwCondMatch
  wpc_auto
  wpc_done

fncost_register "rw_cond_match" rwCondMatch rw_cond_match_cost

theorem rw0_and_half_cost (sb A : Nat) (h x y hi lo : BitVec 32) :
    FnCost (State := State) prog "rw0_and_half" (BudPre sb [.ptr sb 0, .u32 h, .u32 x, .u32 y, .u32 hi, .u32 lo]) (Amort sb A (allow 26) 0 noSlack) := by
  apply FnCost.intro (fn := rw0AndHalf) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rw0AndHalf
  wpc_auto
  wpc_done

fncost_register "rw0_and_half" rw0AndHalf rw0_and_half_cost

theorem rw0_repeat_cost (sb A : Nat) (a b : BitVec 32) :
    FnCost (State := State) prog "rw0_repeat" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow (10 * 255 + 40)) 0 noSlack) := by
  apply FnCost.intro (fn := rw0Repeat) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rw0Repeat
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro w _
  wpc_simp
  apply WPC.seq
  refine WPC.assign_shr (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat < 256 := by simpa using hn
  wpc_auto
  wpc_done
  all_goals
    apply WPC.while
      (I := fun env' st' k => st' = st ∧ ∃ y i : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
          ("w", .u32, .u32 w), ("k", .u32, .u32 n), ("y", .u32, .u32 y), ("i", .u32, .u32 i)] ∧
        i.toNat ≤ n.toNat ∧ k.t ≤ 10 * i.toNat ∧ k.m = 0)
      (μ := fun env' _ => n.toNat - envU32 env' "i")
    · exact ⟨rfl, _, 0#32, rfl, by simp, by simp, by simp⟩
    rintro env' st' k ⟨rfl, y, i, rfl, hin, hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_next hi1

fncost_register "rw0_repeat" rw0Repeat rw0_repeat_cost

theorem rw0_distinct_cost (sb A : Nat) (a b : BitVec 32) :
    FnCost (State := State) prog "rw0_distinct" (BudPre sb [.ptr sb 0, .u32 a, .u32 b]) (Amort sb A (allow 14) 0 noSlack) := by
  apply FnCost.intro (fn := rw0Distinct) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body rw0Distinct
  wpc_auto
  wpc_done

fncost_register "rw0_distinct" rw0Distinct rw0_distinct_cost

/-! ## `Vbcf/Rules/Bitblast.lean` -/

theorem bb_nargs_cost (sb A : Nat) (id : BitVec 32) :
    FnCost (State := State) prog "bb_nargs" (BudPre sb [.ptr sb 0, .u32 id]) (Amort sb A (allow 8) 0 noSlack) := by
  apply FnCost.intro (fn := bbNargs) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbNargs
  wpc_auto
  wpc_done

fncost_register "bb_nargs" bbNargs bb_nargs_cost

theorem bb_is1_cost (sb A : Nat) (i hdr a : BitVec 32) :
    FnCost (State := State) prog "bb_is1" (BudPre sb [.ptr sb 0, .u32 i, .u32 hdr, .u32 a]) (Amort sb A (allow 5) 0 noSlack) := by
  apply FnCost.intro (fn := bbIs1) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbIs1
  wpc_auto
  wpc_done

fncost_register "bb_is1" bbIs1 bb_is1_cost

theorem bb_is2_cost (sb A : Nat) (i hdr a b : BitVec 32) :
    FnCost (State := State) prog "bb_is2" (BudPre sb [.ptr sb 0, .u32 i, .u32 hdr, .u32 a, .u32 b]) (Amort sb A (allow 5) 0 noSlack) := by
  apply FnCost.intro (fn := bbIs2) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbIs2
  wpc_auto
  wpc_done

fncost_register "bb_is2" bbIs2 bb_is2_cost

theorem bb_val_cost (sb A : Nat) (a b : BitVec 32) :
    FnCost (State := State) prog "bb_val" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow (20 * 255 + 20)) 0 noSlack) := by
  apply FnCost.intro (fn := bbVal) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbVal
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro vl _
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ i bit x : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
        ("n", .u32, .u32 n), ("vl", .u32, .u32 vl), ("i", .u32, .u32 i), ("bit", .u32, .u32 bit),
        ("x", .u32, .u32 x)] ∧
      i.toNat ≤ n.toNat ∧ k.t ≤ 20 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨rfl, 0#32, 0#32, 0#32, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, i, bit, x, rfl, hin, hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals loop_next hi1

fncost_register "bb_val" bbVal bb_val_cost

theorem bb_list_eq_cost (sb A : Nat) (pb np xb nx : BitVec 32) :
    FnCost (State := State) prog "bb_list_eq" (BudPre sb [.ptr sb 0, .u32 pb, .u32 np, .u32 xb, .u32 nx])
      (Amort sb A (allow (6 * np.toNat + 10)) 0 noSlack) := by
  apply FnCost.intro (fn := bbListEq) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbListEq
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ i : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("pb", .u32, .u32 pb), ("np", .u32, .u32 np),
        ("xb", .u32, .u32 xb), ("nx", .u32, .u32 nx), ("i", .u32, .u32 i)] ∧
      i.toNat ≤ np.toNat ∧ k.t ≤ 6 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => np.toNat - envU32 env' "i")
  · exact ⟨rfl, 0#32, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, i, rfl, hin, hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < np.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.assign
  embc_simp
  have hmod : (i.toNat + 1) % 4294967296 = i.toNat + 1 := by omega
  simp only [envU32, Env.get, hmod]
  simp only [String.reduceEq, ↓reduceIte, hi1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

fncost_register "bb_list_eq" bbListEq bb_list_eq_cost

theorem bb_bitwise_cost (sb A : Nat) (code a b : BitVec 32) :
    FnCost (State := State) prog "bb_bitwise" (BudPre sb [.ptr sb 0, .u32 code, .u32 a, .u32 b])
      (Amort sb A (allow ((30 * 255 + 30) * 255 + 20)) 0 noSlack) := by
  apply FnCost.intro (fn := bbBitwise) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbBitwise
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro nb hnb
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  have hnb' : nb.toNat ≤ 255 := by simpa using hnb
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro hdr
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ i kk x cur : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("code", .u32, .u32 code), ("a", .u32, .u32 a),
        ("b", .u32, .u32 b), ("n", .u32, .u32 n), ("nb", .u32, .u32 nb), ("hdr", .u32, .u32 hdr),
        ("i", .u32, .u32 i), ("k", .u32, .u32 kk), ("x", .u32, .u32 x), ("cur", .u32, .u32 cur)] ∧
      i.toNat ≤ nb.toNat ∧ k.t ≤ (30 * 255 + 30) * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => nb.toNat - envU32 env' "i")
  · exact ⟨rfl, 0#32, 0#32, 0#32, 0#32, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, i, kk, x, cur, rfl, hin, hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < nb.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  -- the first inner loop: every operand has bit `i`
  apply WPC.while
    (I := fun env1 st1 k1 => st1 = st' ∧ ∃ kk x : BitVec 32,
      env1 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("code", .u32, .u32 code), ("a", .u32, .u32 a),
        ("b", .u32, .u32 b), ("n", .u32, .u32 n), ("nb", .u32, .u32 nb), ("hdr", .u32, .u32 hdr),
        ("i", .u32, .u32 i), ("k", .u32, .u32 kk), ("x", .u32, .u32 x), ("cur", .u32, .u32 cur)] ∧
      kk.toNat ≤ n.toNat ∧ k1.t ≤ 10 * kk.toNat ∧ k1.m = 0)
    (μ := fun env1 _ => n.toNat - envU32 env1 "k")
  · exact ⟨rfl, 0#32, x, rfl, by simp, by simp, by simp⟩
  rintro env1 st1 k1 ⟨rfl, kk1, x1, rfl, hkn1, hk1, hkm1⟩
  embc_simp
  refine ⟨fun hge1 => ?_, fun hlt1 => ?body1⟩
  case body1 =>
    have hlt1' : kk1.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt1
    have hk11 : (kk1 + 1#32).toNat = kk1.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_next hk11
  wpc_auto
  wpc_done
  -- the second inner loop: the chain of `hdr` nodes
  apply WPC.while
    (I := fun env2 st2 k2 => st2 = st1 ∧ ∃ kk x cur : BitVec 32,
      env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("code", .u32, .u32 code), ("a", .u32, .u32 a),
        ("b", .u32, .u32 b), ("n", .u32, .u32 n), ("nb", .u32, .u32 nb), ("hdr", .u32, .u32 hdr),
        ("i", .u32, .u32 i), ("k", .u32, .u32 kk), ("x", .u32, .u32 x), ("cur", .u32, .u32 cur)] ∧
      kk.toNat ≤ n.toNat ∧ k2.t + 20 * kk.toNat ≤ 20 * n.toNat ∧ k2.m = 0)
    (μ := fun env2 _ => envU32 env2 "k")
  · exact ⟨rfl, n, x1, _, rfl, by simp, by simp, by simp⟩
  rintro env2 st2 k2 ⟨rfl, kk2, x2, cur2, rfl, hkn2, hk2, hkm2⟩
  embc_simp
  refine ⟨fun hge2 => ?_, fun hlt2 => ?body2⟩
  case body2 =>
    have hlt2' : 1 < kk2.toNat := by simpa [BitVec.lt_def] using hlt2
    have hk21 : (kk2 - 1#32).toNat = kk2.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_next hk21
  wpc_auto
  wpc_done
  all_goals loop_next hi1

fncost_register "bb_bitwise" bbBitwise bb_bitwise_cost

theorem bb_concat_cost (sb A : Nat) (a b : BitVec 32) :
    FnCost (State := State) prog "bb_concat" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow ((12 * 255 + 20) * 255 + 20)) 0 noSlack) := by
  apply FnCost.intro (fn := bbConcat) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbConcat
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro nb hnb
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  wpc_auto
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ kk x nx j pos : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
        ("n", .u32, .u32 n), ("nb", .u32, .u32 nb), ("k", .u32, .u32 kk), ("x", .u32, .u32 x),
        ("nx", .u32, .u32 nx), ("j", .u32, .u32 j), ("pos", .u32, .u32 pos)] ∧
      kk.toNat ≤ n.toNat ∧ k.t + (12 * 255 + 20) * kk.toNat ≤ (12 * 255 + 20) * n.toNat ∧ k.m = 0)
    (μ := fun env' _ => envU32 env' "k")
  · exact ⟨rfl, n, 0#32, 0#32, 0#32, 0#32, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, kk, x, nx, j, pos, rfl, hkn, hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hlt' : 0 < kk.toNat := bv_pos_of_ne hlt
    have hk1 : (kk - 1#32).toNat = kk.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
    apply WPC.seq
    wpc_step
    apply WPC.seq
    apply WPC.assign_u32 (by rfl)
    intro x1
    wpc_simp
    apply WPC.seq
    refine WPC.assign_band (by rfl) ?_
    intro nx1 hnx1
    wpc_simp
    have hnx1' : nx1.toNat ≤ 255 := by simpa using hnx1
    wpc_auto
    apply WPC.while
      (I := fun env1 st1 k1 => st1 = st' ∧ ∃ j pos : BitVec 32,
        env1 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
          ("n", .u32, .u32 n), ("nb", .u32, .u32 nb), ("k", .u32, .u32 (kk - 1#32)), ("x", .u32, .u32 x1),
          ("nx", .u32, .u32 nx1), ("j", .u32, .u32 j), ("pos", .u32, .u32 pos)] ∧
        j.toNat ≤ nx1.toNat ∧ k1.t ≤ 12 * j.toNat ∧ k1.m = 0)
      (μ := fun env1 _ => nx1.toNat - envU32 env1 "j")
    · exact ⟨rfl, 0#32, pos, rfl, by simp, by simp, by simp⟩
    rintro env1 st1 k1 ⟨rfl, j1, pos1, rfl, hjn, hk1', hkm1⟩
    embc_simp
    refine ⟨fun hge1 => ?_, fun hlt1 => ?body1⟩
    case body1 =>
      have hlt1' : j1.toNat < nx1.toNat := by simpa [BitVec.lt_def] using hlt1
      have hj1 : (j1 + 1#32).toNat = j1.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      wpc_auto
      wpc_done
      all_goals loop_next hj1
    wpc_auto
    wpc_done
    all_goals loop_next hk1
  wpc_auto
  wpc_done

fncost_register "bb_concat" bbConcat bb_concat_cost

theorem bb_extract_cost (sb A : Nat) (hi lo x b : BitVec 32) :
    FnCost (State := State) prog "bb_extract" (BudPre sb [.ptr sb 0, .u32 hi, .u32 lo, .u32 x, .u32 b])
      (Amort sb A (allow (10 * 255 + 30)) 0 noSlack) := by
  apply FnCost.intro (fn := bbExtract) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbExtract
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro nx _
  wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro nb hnb
  wpc_simp
  have hnb' : nb.toNat ≤ 255 := by simpa using hnb
  wpc_auto
  wpc_done
  all_goals
    apply WPC.while
      (I := fun env' st' k => st' = st ∧ ∃ cnt avail i : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("hi", .u32, .u32 hi), ("lo", .u32, .u32 lo),
          ("x", .u32, .u32 x), ("b", .u32, .u32 b), ("nx", .u32, .u32 nx), ("nb", .u32, .u32 nb),
          ("cnt", .u32, .u32 cnt), ("avail", .u32, .u32 avail), ("i", .u32, .u32 i)] ∧
        i.toNat ≤ nb.toNat ∧ k.t ≤ 10 * i.toNat ∧ k.m = 0)
      (μ := fun env' _ => nb.toNat - envU32 env' "i")
    · exact ⟨rfl, _, _, 0#32, rfl, by simp, by simp, by simp⟩
    rintro env' st' k ⟨rfl, cnt, avail, i, rfl, hin, hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : i.toNat < nb.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_next hi1

fncost_register "bb_extract" bbExtract bb_extract_cost

theorem bb_sext_cost (sb A : Nat) (x b e : BitVec 32) :
    FnCost (State := State) prog "bb_sext" (BudPre sb [.ptr sb 0, .u32 x, .u32 b, .u32 e])
      (Amort sb A (allow (10 * 255 + 20)) 0 noSlack) := by
  apply FnCost.intro (fn := bbSext) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbSext
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro nx _
  wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro nb hnb
  wpc_simp
  have hnb' : nb.toNat ≤ 255 := by simpa using hnb
  wpc_auto
  wpc_done
  all_goals
    apply WPC.while
      (I := fun env' st' k => st' = st ∧ ∃ i : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("x", .u32, .u32 x), ("b", .u32, .u32 b),
          ("e", .u32, .u32 e), ("nx", .u32, .u32 nx), ("nb", .u32, .u32 nb), ("i", .u32, .u32 i)] ∧
        i.toNat ≤ nb.toNat ∧ k.t ≤ 10 * i.toNat ∧ k.m = 0)
      (μ := fun env' _ => nb.toNat - envU32 env' "i")
    · exact ⟨rfl, 0#32, rfl, by simp, by simp, by simp⟩
    rintro env' st' k ⟨rfl, i, rfl, hin, hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : i.toNat < nb.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_next hi1

fncost_register "bb_sext" bbSext bb_sext_cost

theorem bb_is_fill_cost (sb A : Nat) (arith xb nx f : BitVec 32) :
    FnCost (State := State) prog "bb_is_fill" (BudPre sb [.ptr sb 0, .u32 arith, .u32 xb, .u32 nx, .u32 f]) (Amort sb A (allow 8) 0 noSlack) := by
  apply FnCost.intro (fn := bbIsFill) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbIsFill
  wpc_auto
  wpc_done

fncost_register "bb_is_fill" bbIsFill bb_is_fill_cost

theorem bb_log2_cost (sb A : Nat) (n : BitVec 32) :
    FnCost (State := State) prog "bb_log2" (BudPre sb [.u32 n]) (Amort sb A (allow 200) 0 noSlack) := by
  apply FnCost.intro (fn := bbLog2) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbLog2
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ i : BitVec 32,
      env' = [("n", .u32, .u32 n), ("k", .u32, .u32 i)] ∧
      i.toNat ≤ 31 ∧ k.t ≤ 5 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => 31 - envU32 env' "k")
  · exact ⟨rfl, 0#32, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, i, rfl, hin, hk, hkm⟩
  embc_simp
  by_cases h31 : 31#32 ≤ i
  · simp only [h31, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => (h trivial).elim⟩
    wpc_auto
    wpc_finish
  have hlt : i.toNat < 31 := by
    have := BitVec.not_le.mp h31; rw [BitVec.lt_def] at this; simpa using this
  have h32 : i.toNat < 32 := by omega
  simp only [h31, h32, ↓reduceIte]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · wpc_auto
    wpc_finish
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.assign
  embc_simp
  have hmod : (i.toNat + 1) % 4294967296 = i.toNat + 1 := by omega
  simp only [envU32, Env.get, hmod]
  simp only [String.reduceEq, ↓reduceIte, hi1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

fncost_register "bb_log2" bbLog2 bb_log2_cost

/-! ## `Vbcf/Replay.lean` -/

/-- Cell `i` of the struct holds a defined value other than a pointer to the struct
itself, so `kvfree` of it keeps the struct. -/
def FreeOk (m : Mem) (sb i : Nat) : Prop := ∃ p, Fld m sb i p ∧ p ≠ .undef ∧ p ≠ .ptr sb 0

theorem FreeOk.ext {P : Prog} {st st' : (KernelState P State)} {sb i : Nat} {f : Ext} {vs : List Val}
    {rv : Option Val} (h : FreeOk st.mem sb i) (hr : Ext.run P f vs st = some (rv, st'))
    (hfree : ∀ b, vs = [.ptr b 0] → f = .kvfree → b ≠ sb) : FreeOk st'.mem sb i := by
  obtain ⟨p, hp, h1, h2⟩ := h
  exact ⟨p, hp.ext hr hfree, h1, h2⟩

/-- `kvfree(st->f)` where the field does not point to the struct. -/
theorem WPC.kvfree_fld {env : Env} {st : (KernelState prog State)} {Q : (CPost prog State)} {sb i : Nat} {f : String} {t : Ty}
    {w mm : BitVec 32} (hb : Budget st.mem sb w mm) (hfi : fieldIn ckS.fields f = some (i, t))
    (hok : FreeOk st.mem sb i) (hst : env.get "st" = some (.ptr sb 0))
    (h : ∀ st' : (KernelState prog State), Budget st'.mem sb w mm →
      (∀ j, FreeOk st.mem sb j → FreeOk st'.mem sb j) → Q .normal env st' 3) :
    WPC Vbcf.prog (.ecall none .kvfree [.field (.var "st") f]) Q env st := by
  obtain ⟨p, hp, hpu, hps⟩ := hok
  apply WPC.ecall
  have hl := hp.load hfi hpu
  simp only [evalArgs, evalE, hst, ↓reduceIte, hl]
  cases hr : Ext.run Vbcf.prog Ext.kvfree [p] st with
  | none => trivial
  | some r =>
    obtain ⟨rv, st'⟩ := r
    have hfree : ∀ b, [p] = [Val.ptr b 0] → Ext.kvfree = Ext.kvfree → b ≠ sb := by
      intro b hpb _ hbs; subst hbs; simp at hpb; exact hps hpb
    have hc : Ext.costC Vbcf.prog Ext.kvfree [p] = 0 := by
      simp [Ext.costC, Ext.cost, Ext.words]; rfl
    simp only [assignDst_none, hc]
    have := h st' (hb.ext hr hfree) (fun j hj => hj.ext hr hfree)
    simpa using this

theorem ck_free_cost (sb A : Nat) :
    FnCost (State := State) prog "ck_free"
      (fun vs st => BudPre sb [.ptr sb 0] vs st ∧ FreeOk st.mem sb 0 ∧ FreeOk st.mem sb 3 ∧
        FreeOk st.mem sb 6 ∧ FreeOk st.mem sb 10 ∧ FreeOk st.mem sb 13 ∧ FreeOk st.mem sb 23)
      (Amort sb A (allow 30) 0 noSlack) := by
  apply FnCost.intro (fn := ckFree) rfl
  rintro vs st ⟨⟨rfl, w, mm, hb⟩, h0, h3, h6, h10, h13, h23⟩
  fncost_body ckFree
  apply WPC.seq
  refine WPC.kvfree_fld hb fi_pool h0 rfl fun st1 hb1 hk1 => ?_
  wpc_simp
  apply WPC.seq
  refine WPC.kvfree_fld hb1 fi_htab (hk1 _ h3) rfl fun st2 hb2 hk2 => ?_
  wpc_simp
  apply WPC.seq
  refine WPC.kvfree_fld hb2 fi_facts (hk2 _ (hk1 _ h6)) rfl fun st3 hb3 hk3 => ?_
  wpc_simp
  apply WPC.seq
  refine WPC.kvfree_fld hb3 fi_stk (hk3 _ (hk2 _ (hk1 _ h10))) rfl fun st4 hb4 hk4 => ?_
  wpc_simp
  apply WPC.seq
  refine WPC.kvfree_fld hb4 fi_prem (hk4 _ (hk3 _ (hk2 _ (hk1 _ h13)))) rfl fun st5 hb5 hk5 => ?_
  wpc_simp
  refine WPC.kvfree_fld hb5 cfi_lr (hk5 _ (hk4 _ (hk3 _ (hk2 _ (hk1 _ h23))))) rfl
    fun st6 hb6 _ => ?_
  wpc_finish

fncost_register "ck_free" ckFree ck_free_cost

end Vbcf.Proof
