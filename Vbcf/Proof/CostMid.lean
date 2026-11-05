import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCore2
import Vbcf.Proof.CostLeaf
import Vbcf.Proof.CostAci

/-!
# Vbcf cost proofs: the middle layer (bit-blast, poly, rewrite, clause, eval, aci helpers)

26 functions whose callees are proved in `CostCore`, `CostCore2`, `CostLeaf`,
`CostAci`.  Per function `(A ≥, B, S)`, lines of proof, `auto` when
`wpc_auto; wpc_done` did it alone.  All allocate nothing beyond the budget (`Bm = 0`).

* Straight-line, `auto` (5 lines): `bb_carry` (–, 40, noSlack), `bb_ite_bit` (–, 40),
  `bb_ult_base` (–, 20), `poly_lit_val` (–, 30),
  `rw_ite` (100, 8540), `rw_lit` (100, 8530), `sdiv_w` (–, 30), `smod_w` (–, 30),
  `r_distinct_values` (100, 17100), `aci_nil` (–, 50); `rw_splice` (100, 120, 6),
  `cl_lits` (100, 120, 6).
* `lin_push64` (6, 120, `slackUnless 0#32 A`; 11): `wpc_ite_case` after the first push.
* `r_absorb` (100, 140, noSlack; 36): `aci_absorb` is not registered and its
  precondition is not `BudPre`, so its call is `WPC.call_shape` by hand.
* Counted loops over `n ≤ 255` (a mask) calling pure functions:
  `rw0_and_split` (–, 60·255+50; 33; the loop over the pieces of
  an and-split), `bb_eq_bits` (–, 20·255+30; 29), `bb_var` (–, 20·255+30; 27).
* Counted loops over an argument: `bb_zip_not` (–, 20·np+30; 28), `rw_params`
  (–, 60·na+30; 52; the `rw_ty_ok` call reads the global table `rw_tbl`, on which
  `wpc_call`'s argument `simp` and `wpc_dst`'s `trivial` exceed the recursion limit, so
  that call is done by hand).
* `r_reordering` (100, 30·255+10400; 48): swap loop bounded by `cnt ≤ n ≤ 255`
  (the `cnt > n` check is kept with `WPC.ite`).
* `rw_app` (100, 30·255+10200; 43): `n > 255` check kept; the `n == 1` branch joined
  with `WPC.seq_join`; both `ty_of` loops share one invariant.
* Loops paid by `push`'s slack: `bb_pre` (300, 150, `slackUnless NOID (100*n)`; 36), `bb_lsh_stage`
  (100, 20·n+150; 53; then a counted loop over `n`).
* `lin_scale` (–, 10·n+30; 30): stack range `stk[b0..sp)` with `SpPre sb b0 n`, plus
  `b0 + n < 2^32 - 3` (`i` steps by 3 up to `sp + 2`; without it `i + 3` may wrap and
  the loop need not end).
* `cl_dups` (–, 80·na+1537000; 157): `mid_cl_byte_cost` gives `cl_byte`'s result
  `≤ 255`.  The outer loop needs no bound on `vlen`: each completed iteration raises
  `pre` (a byte, strictly increasing), so at most 256 complete, each with ≤ 255 inner
  iterations (≤ 6000); the padding loop is ≤ 20·vlen, `vlen ≤ 4·na`.

Helpers (prefixed `mid_`): `mid_close`/`mid_next` (next-iteration goal of a loop whose
invariant carries `∃ w' mm', Budget …`), `mid_ret_band`, `mid_cl_byte_cost` (not
registered), `mid_byte_call`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

/-- The next-iteration goal of a loop whose invariant carries `∃ w' mm', Budget … ∧ …`
(the budget after a call in the body): unfold the callee's allowance and slack, simplify
the environment, take the most recent budget, close the rest by `omega`. -/
macro "mid_close" : tactic => `(tactic| ((try simp only [allow_apply, noSlack_apply,
  allowFail_apply, slackUnless_apply, slackOr_apply] at *); (try simp only [envU32, Env.get, String.reduceEq,
  ↓reduceIte, List.cons.injEq, Prod.mk.injEq, Val.u32.injEq, Val.u64.injEq, and_assoc, true_and, and_true,
  exists_eq', exists_eq_left, exists_and_left, exists_and_right, exists_const, exists_eq_left', Cost.add_t,
  Cost.add_m, Cost.one_t, Cost.one_m, Cost.zero_t, Cost.zero_m, reduceCostT, reduceCostM]); (repeat' (first | (refine ⟨_, _, ‹Budget _ _ _ _›, ?_⟩) | apply And.intro)); all_goals (first | assumption | omega | (simp +arith only at *; omega))))

/-- `mid_close` with the next value of the loop counter (`h : (i + 1#32).toNat = i.toNat + 1`). -/
macro "mid_next" h:ident : tactic => `(tactic| ((try simp only [allow_apply, noSlack_apply,
  allowFail_apply, slackUnless_apply, slackOr_apply] at *); simp only [envU32, Env.get, String.reduceEq,
  ↓reduceIte, List.cons.injEq, Prod.mk.injEq, Val.u32.injEq, Val.u64.injEq, and_assoc, true_and, and_true,
  exists_eq', exists_eq_left, exists_and_left, exists_and_right, exists_const, exists_eq_left', Cost.add_t,
  Cost.add_m, Cost.one_t, Cost.one_m, Cost.zero_t, Cost.zero_m, reduceCostT, reduceCostM, $h:ident]; (repeat' (first | (refine ⟨_, _, ‹Budget _ _ _ _›, ?_⟩) | apply And.intro)); all_goals (first | assumption | omega | (simp +arith only at *; omega))))

theorem bb_carry_cost (sb A : Nat) (pa pb pc c : BitVec 32) :
    FnCost (State := State) prog "bb_carry" (BudPre sb [.ptr sb 0, .u32 pa, .u32 pb, .u32 pc, .u32 c])
      (Amort sb A (allow 40) 0 noSlack) := by
  apply FnCost.intro (fn := bbCarry) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbCarry
  wpc_auto
  wpc_done

fncost_register "bb_carry" bbCarry bb_carry_cost

theorem bb_ite_bit_cost (sb A : Nat) (c t e b : BitVec 32) :
    FnCost (State := State) prog "bb_ite_bit" (BudPre sb [.ptr sb 0, .u32 c, .u32 t, .u32 e, .u32 b])
      (Amort sb A (allow 40) 0 noSlack) := by
  apply FnCost.intro (fn := bbIteBit) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbIteBit
  wpc_auto
  wpc_done

fncost_register "bb_ite_bit" bbIteBit bb_ite_bit_cost

theorem bb_ult_base_cost (sb A : Nat) (l0 r0 res : BitVec 32) :
    FnCost (State := State) prog "bb_ult_base" (BudPre sb [.ptr sb 0, .u32 l0, .u32 r0, .u32 res])
      (Amort sb A (allow 20) 0 noSlack) := by
  apply FnCost.intro (fn := bbUltBase) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body bbUltBase
  wpc_auto
  wpc_done

fncost_register "bb_ult_base" bbUltBase bb_ult_base_cost

theorem poly_lit_val_cost (sb A : Nat) (w id : BitVec 32) :
    FnCost (State := State) prog "poly_lit_val" (BudPre sb [.ptr sb 0, .u32 w, .u32 id])
      (Amort sb A (allow 30) 0 noSlack) := by
  apply FnCost.intro (fn := polyLitVal) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body polyLitVal
  wpc_auto
  wpc_done

fncost_register "poly_lit_val" polyLitVal poly_lit_val_cost

theorem rw0_and_split_cost (sb A : Nat) (a b : BitVec 32) :
    FnCost (State := State) prog "rw0_and_split" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow (60 * 255 + 50)) 0 noSlack) := by
  apply FnCost.intro (fn := rw0AndSplit) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rw0AndSplit
  wpc_auto
  wpc_done
  all_goals
    rename_i wv _ xv yv nv hn
    have hn' : nv.toNat ≤ 255 := by simpa using hn
    apply WPC.while
      (I := fun env' st' k => ∃ i e h p lo ok : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
          ("w", .u32, .u32 wv), ("x", .u32, .u32 xv), ("y", .u32, .u32 yv), ("n", .u32, .u32 nv),
          ("i", .u32, .u32 i), ("e", .u32, .u32 e), ("h", .u32, .u32 h), ("p", .u32, .u32 p),
          ("lo", .u32, .u32 lo), ("ok", .u32, .u32 ok)] ∧
        i.toNat ≤ nv.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w0.toNat + 60 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
      (μ := fun env' _ => nv.toNat - envU32 env' "i")
    · exact ⟨0#32, _, 0#32, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
    rintro env' st' k ⟨i, e, h, p, lo, ok, rfl, hin, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : i.toNat < nv.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1

fncost_register "rw0_and_split" rw0AndSplit rw0_and_split_cost

theorem rw_ite_cost (sb A : Nat) (hA : 100 ≤ A) (a b c : BitVec 32) :
    FnCost (State := State) prog "rw_ite" (BudPre sb [.ptr sb 0, .u32 a, .u32 b, .u32 c])
      (Amort sb A (allow 8540) 0 noSlack) := by
  apply FnCost.intro (fn := rwIte) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwIte
  wpc_auto
  wpc_done

fncost_register "rw_ite" rwIte rw_ite_cost

theorem rw_lit_cost (sb A : Nat) (hA : 100 ≤ A) (sz v : BitVec 64) :
    FnCost (State := State) prog "rw_lit" (BudPre sb [.ptr sb 0, .u64 sz, .u64 v])
      (Amort sb A (allow 8530) 0 noSlack) := by
  apply FnCost.intro (fn := rwLit) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwLit
  wpc_auto
  wpc_done

fncost_register "rw_lit" rwLit rw_lit_cost

theorem sdiv_w_cost (sb A : Nat) (x y : BitVec 64) (w : BitVec 32) (m : BitVec 64) :
    FnCost (State := State) prog "sdiv_w" (BudPre sb [.u64 x, .u64 y, .u32 w, .u64 m])
      (Amort sb A (allow 30) 0 noSlack) := by
  apply FnCost.intro (fn := sdivW) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body sdivW
  wpc_auto
  wpc_done

fncost_register "sdiv_w" sdivW sdiv_w_cost

theorem smod_w_cost (sb A : Nat) (x y : BitVec 64) (w : BitVec 32) (m : BitVec 64) :
    FnCost (State := State) prog "smod_w" (BudPre sb [.u64 x, .u64 y, .u32 w, .u64 m])
      (Amort sb A (allow 30) 0 noSlack) := by
  apply FnCost.intro (fn := smodW) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body smodW
  wpc_auto
  wpc_done

fncost_register "smod_w" smodW smod_w_cost

theorem r_distinct_values_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_distinct_values" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17100) 0 noSlack) := by
  apply FnCost.intro (fn := rDistinctValues) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rDistinctValues
  wpc_auto
  wpc_done

fncost_register "r_distinct_values" rDistinctValues r_distinct_values_cost

theorem aci_nil_cost (sb A : Nat) (rop id : BitVec 32) :
    FnCost (State := State) prog "aci_nil" (BudPre sb [.ptr sb 0, .u32 rop, .u32 id])
      (Amort sb A (allow 50) 0 noSlack) := by
  apply FnCost.intro (fn := aciNil) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body aciNil
  wpc_auto
  wpc_done

fncost_register "aci_nil" aciNil aci_nil_cost

theorem rw_splice_cost (sb A : Nat) (hA : 100 ≤ A) (i : BitVec 32) :
    FnCost (State := State) prog "rw_splice" (BudPre sb [.ptr sb 0, .u32 i])
      (Amort sb A (allow 120) 0 noSlack) := by
  apply FnCost.intro (fn := rwSplice) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwSplice
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "rw_splice" rwSplice rw_splice_cost

theorem cl_lits_cost (sb A : Nat) (hA : 100 ≤ A) (p pivot : BitVec 32) :
    FnCost (State := State) prog "cl_lits" (BudPre sb [.ptr sb 0, .u32 p, .u32 pivot])
      (Amort sb A (allow 120) 0 noSlack) := by
  apply FnCost.intro (fn := clLits) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body clLits
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "cl_lits" clLits cl_lits_cost


theorem bb_eq_bits_cost (sb A : Nat) (b x y : BitVec 32) :
    FnCost (State := State) prog "bb_eq_bits" (BudPre sb [.ptr sb 0, .u32 b, .u32 x, .u32 y])
      (Amort sb A (allow (20 * 255 + 30)) 0 noSlack) := by
  apply FnCost.intro (fn := bbEqBits) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbEqBits
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  wpc_auto
  wpc_done
  all_goals
    apply WPC.while
      (I := fun env' st' k => ∃ i ok : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b", .u32, .u32 b), ("x", .u32, .u32 x),
          ("y", .u32, .u32 y), ("n", .u32, .u32 n), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧
        i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w0.toNat + 20 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
      (μ := fun env' _ => n.toNat - envU32 env' "i")
    · exact ⟨0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
    rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1

fncost_register "bb_eq_bits" bbEqBits bb_eq_bits_cost

theorem bb_var_cost (sb A : Nat) (a b : BitVec 32) :
    FnCost (State := State) prog "bb_var" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow (20 * 255 + 30)) 0 noSlack) := by
  apply FnCost.intro (fn := bbVar) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbVar
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
        ("n", .u32, .u32 n), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 20 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "bb_var" bbVar bb_var_cost

theorem bb_zip_not_cost (sb A : Nat) (pb np xb nx : BitVec 32) :
    FnCost (State := State) prog "bb_zip_not" (BudPre sb [.ptr sb 0, .u32 pb, .u32 np, .u32 xb, .u32 nx])
      (Amort sb A (allow (20 * np.toNat + 30)) 0 noSlack) := by
  apply FnCost.intro (fn := bbZipNot) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbZipNot
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("pb", .u32, .u32 pb), ("np", .u32, .u32 np),
        ("xb", .u32, .u32 xb), ("nx", .u32, .u32 nx), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ np.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 20 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => np.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < np.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "bb_zip_not" bbZipNot bb_zip_not_cost

theorem rw_params_cost (sb A : Nat) (off ab na : BitVec 32) :
    FnCost (State := State) prog "rw_params" (BudPre sb [.ptr sb 0, .u32 off, .u32 ab, .u32 na])
      (Amort sb A (allow (60 * na.toNat + 30)) 0 noSlack) := by
  apply FnCost.intro (fn := rwParams) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwParams
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i t ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("off", .u32, .u32 off), ("ab", .u32, .u32 ab),
        ("na", .u32, .u32 na), ("i", .u32, .u32 i), ("t", .u32, .u32 t), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ na.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 60 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => na.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, t, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < na.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  -- t = ty_of(...); ok = rw_ty_ok(@rw_tbl[...], t): `cost_args` must not evaluate the table read
  apply WPC.seq
  wpc_step
  apply WPC.seq
  have hbc := ‹Budget _ _ _ _›
  apply WPC.call_shape (hf := rwTyOk_find) (hps := rwTyOk_params)
  intro vs1 _ hbp
  obtain ⟨v1, vs2, rfl, ht1, hbp1⟩ := bindParams_ne_none_cons hbp
  obtain ⟨p1, rfl⟩ := Mem.hasTy_u32_inv ht1
  obtain ⟨v2, vs3, rfl, ht2, hbp2⟩ := bindParams_ne_none_cons hbp1
  obtain ⟨p2, rfl⟩ := Mem.hasTy_u32_inv ht2
  obtain rfl := bindParams_ne_none_nil hbp2
  refine ⟨_, _, rw_ty_ok_cost sb A p1 p2, ⟨rfl, _, _, hbc⟩, ?_⟩
  rintro _rv _st' _c ⟨_w', _mm', _hb', _ht, _hm⟩
  rw [Budget.wk hbc] at _ht
  rw [Budget.mk hbc] at _hm
  split
  · trivial
  rename_i env2 hasg
  obtain ⟨r2, h1, h2⟩ := assignDst_u32' hasg rfl
  subst h1
  subst h2
  wpc_simp
  cost_clean
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "rw_params" rwParams rw_params_cost

theorem lin_push64_cost (sb A : Nat) (hA : 6 ≤ A) (v : BitVec 64) :
    FnCost (State := State) prog "lin_push64" (BudPre sb [.ptr sb 0, .u64 v])
      (Amort sb A (allow 120) 0 (slackUnless 0#32 A)) := by
  apply FnCost.intro (fn := linPush64) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body linPush64
  apply WPC.seq
  wpc_step
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  wpc_auto
  wpc_done

fncost_register "lin_push64" linPush64 lin_push64_cost

theorem r_absorb_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_absorb" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 140) 0 noSlack) := by
  apply FnCost.intro (fn := rAbsorb) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rAbsorb
  wpc_auto
  wpc_done
  all_goals
    have hbc := ‹Budget _ _ _ _›
    refine WPC.call_shape (fn := aciAbsorb) (hf := rfl) (hps := rfl) ?_
    intro vs1 hargs hbp
    obtain ⟨v0, vs2, h0, -, rfl⟩ := evalArgs_cons' hargs
    simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at h0
    subst h0
    obtain ⟨v1, vs3, e1, -, hbp1⟩ := bindParams_ne_none_cons hbp
    simp only [List.cons.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨v2, vs4, rfl, ht2, hbp2⟩ := bindParams_ne_none_cons hbp1
    obtain ⟨rop', rfl⟩ := Mem.hasTy_u32_inv ht2
    obtain ⟨v3, vs5, rfl, ht3, hbp3⟩ := bindParams_ne_none_cons hbp2
    obtain ⟨x', rfl⟩ := Mem.hasTy_u32_inv ht3
    obtain ⟨v4, vs6, rfl, ht4, hbp4⟩ := bindParams_ne_none_cons hbp3
    obtain ⟨d', rfl⟩ := Mem.hasTy_u32_inv ht4
    obtain rfl := bindParams_ne_none_nil hbp4
    refine ⟨_, _, aci_absorb_cost sb A hA, ⟨⟨rop', .u32 x', d', rfl⟩, _, _, hbc⟩, ?_⟩
    rintro _rv _st' _c ⟨_w', _mm', _hb', _ht, _hm⟩
    rw [Budget.wk hbc] at _ht
    rw [Budget.mk hbc] at _hm
    split
    · trivial
    rename_i env2 hasg
    obtain ⟨r2, h1, h2⟩ := assignDst_u32' hasg rfl
    subst h1
    subst h2
    wpc_simp
    cost_clean
    wpc_auto
    wpc_done

fncost_register "r_absorb" rAbsorb r_absorb_cost

theorem r_reordering_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_reordering" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow (30 * 255 + 10400)) 0 noSlack) := by
  apply FnCost.intro (fn := rReordering) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rReordering
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  iterate 2
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; wpc_done
    apply WPC.skip; wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; wpc_done
  intro hc
  apply WPC.skip; wpc_simp
  wpc_auto
  wpc_done
  all_goals
    name_bud st1 w1 mm1 hb1
    apply WPC.while
      (I := fun env' st' k => ∃ p cnt vec t sw j kk x base ok r : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
          ("p", .u32, .u32 p), ("n", .u32, .u32 n), ("cnt", .u32, .u32 cnt), ("vec", .u32, .u32 vec),
          ("t", .u32, .u32 t), ("sw", .u32, .u32 sw), ("j", .u32, .u32 j), ("k", .u32, .u32 kk),
          ("x", .u32, .u32 x), ("base", .u32, .u32 base), ("ok", .u32, .u32 ok), ("r", .u32, .u32 r)] ∧
        cnt.toNat ≤ n.toNat ∧ 1 ≤ t.toNat ∧ t.toNat ≤ cnt.toNat + 1 ∧
        ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
          k.t + A * w'.toNat ≤ A * w1.toNat + 30 * (t.toNat - 1) ∧ k.m + mm'.toNat ≤ mm1.toNat)
      (μ := fun env' _ => envU32 env' "cnt" + 1 - envU32 env' "t")
    · exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, BitVec.le_def.mp hc, by simp, by simp, w1, mm1, hb1,
        by simp, by simp⟩
    rintro env' st' k ⟨p, cnt, vec, t, sw, j, kk, x, base, ok, r, rfl, hcn, ht1, htc, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hle => ?_⟩
    · wpc_auto
      wpc_done
    have hle' : t.toNat ≤ cnt.toNat := BitVec.le_def.mp hle
    have hi1 : (t + 1#32).toNat = t.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1

fncost_register "r_reordering" rReordering r_reordering_cost

theorem rw_app_cost (sb A : Nat) (hA : 100 ≤ A) (code base n : BitVec 32) :
    FnCost (State := State) prog "rw_app" (BudPre sb [.ptr sb 0, .u32 code, .u32 base, .u32 n])
      (Amort sb A (allow (30 * 255 + 10200)) 0 noSlack) := by
  apply FnCost.intro (fn := rwApp) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwApp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  -- if (n == 1) { if (...) return st->stk[base]; }: the branches join
  apply WPC.seq_join (J := fun env' st' k => env' = [("st", .ptr (.struct "ck"), .ptr sb 0),
      ("code", .u32, .u32 code), ("base", .u32, .u32 base), ("n", .u32, .u32 n), ("i", .u32, .u32 0),
      ("t", .u32, .u32 0), ("w", .u32, .u32 0), ("r", .u32, .u32 0)] ∧ st' = st ∧ k.t ≤ 10 ∧ k.m = 0)
  · wpc_auto
    wpc_done
    all_goals (and_intros <;> first | trivial | rfl | cost_arith)
  rintro env' st' k0 ⟨rfl, rfl, hk0, hkm0⟩
  -- if (n > 255) return NOID;
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; wpc_done
  intro hn
  have hn' : n.toNat ≤ 255 := by have := BitVec.le_def.mp hn; simpa using this
  apply WPC.skip; wpc_simp
  wpc_auto
  wpc_done
  -- both loops: `i < n`, one `ty_of` per iteration, exit by `break` or at `n`
  all_goals
    apply WPC.while
      (I := fun env' st' k => ∃ i t w r : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("code", .u32, .u32 code), ("base", .u32, .u32 base),
          ("n", .u32, .u32 n), ("i", .u32, .u32 i), ("t", .u32, .u32 t), ("w", .u32, .u32 w),
          ("r", .u32, .u32 r)] ∧
        i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w0.toNat + 30 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
      (μ := fun env' _ => n.toNat - envU32 env' "i")
    · exact ⟨0#32, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
    rintro env' st' k ⟨i, t, w, r, rfl, hin, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1

fncost_register "rw_app" rwApp rw_app_cost

theorem bb_pre_cost (sb A : Nat) (hA : 300 ≤ A) (rb n k : BitVec 32) :
    FnCost (State := State) prog "bb_pre" (BudPre sb [.ptr sb 0, .u32 rb, .u32 n, .u32 k])
      (Amort sb A (allow 150) 0 (slackUnless 0xffffffff#32 (100 * n.toNat))) := by
  apply FnCost.intro (fn := bbPre) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbPre
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq
  wpc_step
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' c => ∃ base i r s m ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("rb", .u32, .u32 rb), ("n", .u32, .u32 n),
        ("k", .u32, .u32 k), ("base", .u32, .u32 base), ("i", .u32, .u32 i), ("r", .u32, .u32 r),
        ("s", .u32, .u32 s), ("m", .u32, .u32 m), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat + 100 * i.toNat ≤ A * w0.toNat ∧ c.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨_, 0#32, 0#32, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' c ⟨base, i, r, s, m, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hin_eq : i.toNat = n.toNat := by
      have := BitVec.le_def.mp hge
      omega
    have hslack : slackUnless 0xffffffff#32 (100 * n.toNat) (some (.u32 base)) ≤ 100 * n.toNat := by
      simp only [slackUnless_apply]
      split <;> omega
    wpc_auto
    wpc_done
  have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  iterate 2
    apply WPC.seq; wpc_step
    apply WPC.seq; wpc_step
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; wpc_done
    apply WPC.skip; wpc_simp
  -- ok = push(...); if (ok == 0) return NOID;  (the push pays for the iteration)
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_ite_case
  · wpc_auto; wpc_done
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "bb_pre" bbPre bb_pre_cost

theorem bb_lsh_stage_cost (sb A : Nat) (hA : 100 ≤ A) (b t rb n : BitVec 32) :
    FnCost (State := State) prog "bb_lsh_stage" (BudPre sb [.ptr sb 0, .u32 b, .u32 t, .u32 rb, .u32 n])
      (Amort sb A (allow (20 * n.toNat + 150)) 0 noSlack) := by
  apply FnCost.intro (fn := bbLshStage) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbLshStage
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq
  wpc_step
  -- the pushes: each paid by its `push`
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' c => ∃ base j r inj ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b", .u32, .u32 b), ("t", .u32, .u32 t),
        ("rb", .u32, .u32 rb), ("n", .u32, .u32 n), ("base", .u32, .u32 base), ("j", .u32, .u32 j),
        ("r", .u32, .u32 r), ("inj", .u32, .u32 inj), ("ok", .u32, .u32 ok)] ∧
      j.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * w0.toNat ∧ c.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "j")
  · exact ⟨_, 0#32, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' c ⟨base, j, r, inj, ok, rfl, hjn, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hlt' : j.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq; wpc_step
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; wpc_done
    apply WPC.skip; wpc_simp
    apply WPC.seq; wpc_step
    apply WPC.seq; wpc_ite_case
    · wpc_auto; wpc_done
    wpc_auto
    wpc_done
    all_goals mid_next hj1
  -- the checks: no spending, at most `n` iterations
  wpc_auto
  apply WPC.while
    (I := fun env2 st2 k2 => st2 = st' ∧ ∃ j r inj ok : BitVec 32,
      env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b", .u32, .u32 b), ("t", .u32, .u32 t),
        ("rb", .u32, .u32 rb), ("n", .u32, .u32 n), ("base", .u32, .u32 base), ("j", .u32, .u32 j),
        ("r", .u32, .u32 r), ("inj", .u32, .u32 inj), ("ok", .u32, .u32 ok)] ∧
      j.toNat ≤ n.toNat ∧ k2.t ≤ 20 * j.toNat ∧ k2.m = 0)
    (μ := fun env2 _ => n.toNat - envU32 env2 "j")
  · exact ⟨rfl, 0#32, _, _, _, rfl, by simp, by simp, by simp⟩
  rintro env2 st2 k2 ⟨rfl, j2, r2, inj2, ok2, rfl, hjn2, hk2, hkm2⟩
  embc_simp
  refine ⟨fun hge2 => ?_, fun hlt2 => ?_⟩
  · wpc_auto
    wpc_done
  have hlt2' : j2.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt2
  have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals loop_next hj21

fncost_register "bb_lsh_stage" bbLshStage bb_lsh_stage_cost

theorem lin_scale_cost (sb A : Nat) (b0 : BitVec 32) (k m : BitVec 64) (n : BitVec 32) :
    FnCost (State := State) prog "lin_scale"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 b0, .u64 k, .u64 m] vs st ∧ SpPre sb b0 n st.mem ∧
        b0.toNat + n.toNat < 4294967293)
      (Amort sb A (allow (10 * n.toNat + 30)) 0 noSlack) := by
  apply FnCost.intro (fn := linScale) rfl
  rintro vs st ⟨⟨rfl, w0, mm, hb⟩, ⟨sp, hsp, hbn⟩, hwrap⟩
  fncost_body linScale
  have hspl := hsp.load fi_sp (by simp)
  have hb2 : (b0 + 2#32).toNat = b0.toNat + 2 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq
  apply WPC.assign
  embc_simp [hspl]
  wpc_auto
  name_bud st1 w1 mm1 hb1
  apply WPC.while
    (I := fun env' st' c => ∃ i j : BitVec 32, ∃ cv : BitVec 64,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b0", .u32, .u32 b0), ("k", .u64, .u64 k),
        ("m", .u64, .u64 m), ("e", .u32, .u32 sp), ("i", .u32, .u32 i), ("j", .u32, .u32 j),
        ("c", .u64, .u64 cv)] ∧
      b0.toNat + 2 ≤ i.toNat ∧ i.toNat ≤ sp.toNat + 2 ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * w1.toNat + 10 * (i.toNat - (b0.toNat + 2)) ∧ c.m + mm'.toNat ≤ mm1.toNat)
    (μ := fun env' _ => sp.toNat + 2 - envU32 env' "i")
  · exact ⟨_, _, _, rfl, by omega, by omega, w1, mm1, hb1, by simp, by simp⟩
  rintro env' st' c ⟨i, j, cv, rfl, hbi, hisp, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hge' : sp.toNat ≤ i.toNat := by
      have := BitVec.not_lt.mp (by simpa using hge); exact BitVec.le_def.mp this
    wpc_auto
    wpc_done
  have hlt' : i.toNat < sp.toNat := by simpa [BitVec.lt_def] using hlt
  have hi3 : (i + 3#32).toNat = i.toNat + 3 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals mid_next hi3

fncost_register "lin_scale" linScale lin_scale_cost

/-! ## `cl_dups` -/

/-- `cl_byte`'s cost, and that it returns a byte (`& 0xff`): `cl_dups` needs the bound
on the lengths and positions it reads to bound its loops.  Not registered (the
registered `cl_byte_cost` stays the one `wpc_call` uses); applied by `mid_byte_call`. -/
theorem mid_ret_band {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {e : Expr} {k : BitVec 32}
    (h : ∀ n : BitVec 32, n.toNat ≤ k.toNat → Q (.ret (some (.u32 n))) env st 1) :
    WPC P (.ret (some (.bin .band e (.lit32 k)))) Q env st := by
  apply WPC.ret
  simp only [evalE]
  cases evalE P env st.mem e with
  | none => trivial
  | some v =>
    cases v with
    | u32 a =>
      simp only [evalBin, evalArith]
      exact h _ (by rw [BitVec.toNat_and]; exact Nat.and_le_right)
    | _ => simp [evalBin]

theorem mid_cl_byte_cost (sb A : Nat) (k : BitVec 32) :
    FnCost (State := State) prog "cl_byte" (BudPre sb [.ptr sb 0, .u32 k])
      (fun vs st rv st' c => Amort sb A (allow 2) 0 noSlack vs st rv st' c ∧
        ∃ v : BitVec 32, rv = some (.u32 v) ∧ v.toNat ≤ 255) := by
  apply FnCost.intro (fn := clByte) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body clByte
  apply mid_ret_band
  intro n hn
  intro _
  refine ⟨⟨w, mm, hb, ?_, ?_⟩, n, rfl, by simpa using hn⟩
  · rw [hwk]; simp; omega
  · rw [hmk]; simp

/-- A call `x = cl_byte(st, e)` with the byte bound of the result. -/
theorem mid_byte_call {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb A : Nat} {w mm : BitVec 32}
    {x : Var} {e : Expr} (hb : Budget st.mem sb w mm) (hst : env.get "st" = some (.ptr sb 0))
    (hx : env.ty x = some .u32)
    (h : ∀ (v : BitVec 32) (st' : (KernelState prog State)) (c : Cost) (w' mm' : BitVec 32), v.toNat ≤ 255 →
      Budget st'.mem sb w' mm' → c.t + A * w'.toNat ≤ A * w.toNat + 2 → c.m + mm'.toNat ≤ mm.toNat →
      Q .normal (env.set x (.u32 v)) st' (c + 2)) :
    WPC prog (.call (some x) "cl_byte" [.var "st", e]) Q env st := by
  apply WPC.call_shape (hf := clByte_find) (hps := clByte_params)
  intro vs hargs hbp
  obtain ⟨v0, vs0, h0, -, rfl⟩ := evalArgs_cons' hargs
  simp only [evalE, hst, Option.some.injEq] at h0
  subst h0
  obtain ⟨v1, vs1, e1, -, hbp1⟩ := bindParams_ne_none_cons hbp
  simp only [List.cons.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨v2, vs2, rfl, ht2, hbp2⟩ := bindParams_ne_none_cons hbp1
  obtain ⟨kk, rfl⟩ := Mem.hasTy_u32_inv ht2
  obtain rfl := bindParams_ne_none_nil hbp2
  refine ⟨_, _, mid_cl_byte_cost sb A kk, ⟨rfl, w, mm, hb⟩, ?_⟩
  rintro rv st' c ⟨⟨w', mm', hb', ht, hm⟩, v, rfl, hv⟩
  rw [hb.wk] at ht
  rw [hb.mk] at hm
  simp only [assignDst_some, Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
  exact h v st' c w' mm' hv hb' (by simpa using ht) (by simpa using hm)

theorem cl_dups_cost (sb A : Nat) (p n na mb : BitVec 32) :
    FnCost (State := State) prog "cl_dups" (BudPre sb [.ptr sb 0, .u32 p, .u32 n, .u32 na, .u32 mb])
      (Amort sb A (allow (80 * na.toNat + 1537000)) 0 noSlack) := by
  apply FnCost.intro (fn := clDups) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body clDups
  have hvl0 : (na * 4#32).toNat ≤ 4 * na.toNat := by
    rw [BitVec.toNat_mul]; simp; omega
  apply WPC.seq
  wpc_step
  -- the outer loop: every completed iteration raises `pre` (a byte), so at most 256 of them
  apply WPC.seq_join (J := fun env' st' k => ∃ vlen idx pl uniq haspre pre j d cnt b : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("p", .u32, .u32 p), ("n", .u32, .u32 n),
          ("na", .u32, .u32 na), ("mb", .u32, .u32 mb), ("vlen", .u32, .u32 vlen), ("idx", .u32, .u32 idx),
          ("pl", .u32, .u32 pl), ("uniq", .u32, .u32 uniq), ("haspre", .u32, .u32 haspre),
          ("pre", .u32, .u32 pre), ("j", .u32, .u32 j), ("d", .u32, .u32 d), ("cnt", .u32, .u32 cnt),
          ("b", .u32, .u32 b)] ∧
      vlen.toNat ≤ 4 * na.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 1536000 + 20 ∧ k.m + mm'.toNat ≤ mm.toNat)
  · apply WPC.while
      (I := fun env' st' k => ∃ vlen idx pl uniq haspre pre j d cnt b : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("p", .u32, .u32 p), ("n", .u32, .u32 n),
          ("na", .u32, .u32 na), ("mb", .u32, .u32 mb), ("vlen", .u32, .u32 vlen), ("idx", .u32, .u32 idx),
          ("pl", .u32, .u32 pl), ("uniq", .u32, .u32 uniq), ("haspre", .u32, .u32 haspre),
          ("pre", .u32, .u32 pre), ("j", .u32, .u32 j), ("d", .u32, .u32 d), ("cnt", .u32, .u32 cnt),
          ("b", .u32, .u32 b)] ∧
        vlen.toNat ≤ 4 * na.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.m + mm'.toNat ≤ mm.toNat ∧
        ((haspre = 0#32 ∧ k.t + A * w'.toNat ≤ A * w0.toNat) ∨
          (haspre = 1#32 ∧ pre.toNat ≤ 255 ∧ k.t + A * w'.toNat ≤ A * w0.toNat + 6000 * pre.toNat + 6000)))
      (μ := fun env' _ => 257 - envU32 env' "haspre" * (envU32 env' "pre" + 1))
    · exact ⟨_, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, rfl, hvl0, w0, mm, hb, by simp,
        Or.inl ⟨rfl, by simp⟩⟩
    rintro env' st' k ⟨vlen, idx, pl, uniq, haspre, pre, j, d, cnt, b, rfl, hvl, w', mm', hb', hkm, hcase⟩
    have hk' : k.t + A * w'.toNat ≤ A * w0.toNat + 1536000 := by
      rcases hcase with ⟨-, h⟩ | ⟨-, h1, h⟩ <;> omega
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?body⟩
    · mid_close
    case body =>
    have hlt' : idx.toNat < vlen.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (idx + 1#32).toNat = idx.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    -- pl = cl_byte(st, idx); idx = idx + 1; if (pl == 0) break;
    apply WPC.seq
    apply mid_byte_call (A := A) hb' rfl rfl
    intro pl1 st1 c1 w1 mm1 hpl hb1 ht1 hm1
    wpc_simp
    apply WPC.seq
    wpc_step
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      mid_close
    apply WPC.skip
    wpc_simp
    -- if (pl < 2 || idx + pl > vlen) return 0;
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    -- uniq = cl_byte(st, idx); if (uniq >= n) return 0;
    apply WPC.seq
    apply mid_byte_call (A := A) hb1 rfl rfl
    intro u st2 c2 w2 mm2 hu hb2 ht2 hm2
    wpc_simp
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    -- if (haspre != 0 && uniq <= pre) return 0;
    rcases hcase with ⟨rfl, hk⟩ | ⟨rfl, hpre, hk⟩
    case' inl =>
      apply WPC.seq
      apply WPC.ite_any
      · wpc_auto
        wpc_done
      apply WPC.skip
      wpc_simp
      have hku : k.t + A * w'.toNat ≤ A * w0.toNat + 6000 * u.toNat := by omega
    case' inr =>
      apply WPC.seq
      apply WPC.ite
      embc_simp
      refine ⟨fun _ => ?_, fun hgt => ?_⟩
      · wpc_auto
        wpc_done
      have hpu : pre.toNat < u.toNat := BitVec.lt_def.mp hgt
      have hku : k.t + A * w'.toNat ≤ A * w0.toNat + 6000 * u.toNat := by omega
      apply WPC.skip
      wpc_simp
    -- haspre = 1; pre = uniq; j = 1; then the inner loop (`j < pl`, `pl` a byte)
    all_goals
      apply WPC.seq; wpc_step
      apply WPC.seq; wpc_step
      apply WPC.seq; wpc_step
      apply WPC.seq
      apply WPC.while
        (I := fun env2 st3 k2 => ∃ j2 d2 cnt2 b2 : BitVec 32,
          env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("p", .u32, .u32 p), ("n", .u32, .u32 n),
            ("na", .u32, .u32 na), ("mb", .u32, .u32 mb), ("vlen", .u32, .u32 vlen), ("idx", .u32, .u32 (idx + 1#32)),
            ("pl", .u32, .u32 pl1), ("uniq", .u32, .u32 u), ("haspre", .u32, .u32 1#32),
            ("pre", .u32, .u32 u), ("j", .u32, .u32 j2), ("d", .u32, .u32 d2), ("cnt", .u32, .u32 cnt2),
            ("b", .u32, .u32 b2)] ∧
          1 ≤ j2.toNat ∧ j2.toNat ≤ pl1.toNat + 1 ∧ ∃ w3 mm3 : BitVec 32, Budget st3.mem sb w3 mm3 ∧
          k2.t + A * w3.toNat ≤ A * w2.toNat + 22 * (j2.toNat - 1) ∧ k2.m + mm3.toNat ≤ mm2.toNat)
        (μ := fun env2 _ => pl1.toNat + 1 - envU32 env2 "j")
      · exact ⟨_, _, _, _, rfl, by simp, by simp, w2, mm2, hb2, by simp, by simp⟩
      rintro env2 st3 k2 ⟨j2, d2, cnt2, b2, rfl, hj1, hjpl, w3, mm3, hb3, hk3, hkm3⟩
      embc_simp
      refine ⟨fun hge2 => ?_, fun hlt2 => ?body2⟩
      case body2 =>
        have hlt2' : j2.toNat < pl1.toNat := by simpa [BitVec.lt_def] using hlt2
        have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
        wpc_auto
        wpc_done
        all_goals mid_next hj21
      have hge2' : pl1.toNat ≤ j2.toNat := by
        have := BitVec.not_lt.mp (by simpa using hge2); exact BitVec.le_def.mp this
      -- idx = idx + pl; the iteration raised `pre` to `uniq`
      wpc_auto
      simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, List.cons.injEq, Prod.mk.injEq,
        Val.u32.injEq, and_assoc, true_and, and_true, exists_eq', exists_and_left,
        exists_and_right, exists_eq_left', Cost.add_t, Cost.add_m, Cost.one_t, Cost.one_m,
        BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq,
        false_and, false_or, true_and, Nat.one_mul, Nat.zero_mul]
      mid_close
  -- if (cnt == 0) return 0; then the padding: `idx` up to `vlen`, one byte each
  rintro env' st' k ⟨vlen, idx0, pl, uniq, haspre, pre, j, d, cnt, b, rfl, hvl, w3, mm3, hb3, hk3, hkm3⟩
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env2 st4 k4 => ∃ idx b2 : BitVec 32,
      env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("p", .u32, .u32 p), ("n", .u32, .u32 n),
        ("na", .u32, .u32 na), ("mb", .u32, .u32 mb), ("vlen", .u32, .u32 vlen), ("idx", .u32, .u32 idx),
        ("pl", .u32, .u32 pl), ("uniq", .u32, .u32 uniq), ("haspre", .u32, .u32 haspre),
        ("pre", .u32, .u32 pre), ("j", .u32, .u32 j), ("d", .u32, .u32 d), ("cnt", .u32, .u32 cnt),
        ("b", .u32, .u32 b2)] ∧
      idx0.toNat ≤ idx.toNat ∧ (idx.toNat ≤ vlen.toNat ∨ idx.toNat = idx0.toNat) ∧
      ∃ w4 mm4 : BitVec 32, Budget st4.mem sb w4 mm4 ∧
        k4.t + A * w4.toNat ≤ A * w3.toNat + 20 * (idx.toNat - idx0.toNat) ∧ k4.m + mm4.toNat ≤ mm3.toNat)
    (μ := fun env2 _ => vlen.toNat - envU32 env2 "idx")
  · exact ⟨idx0, b, rfl, by simp, by simp, w3, mm3, hb3, by simp, by simp⟩
  rintro env2 st4 k4 ⟨idx, b2, rfl, hi0, hiv, w4, mm4, hb4, hk4, hkm4⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body3⟩
  case body3 =>
    have hlt' : idx.toNat < vlen.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (idx + 1#32).toNat = idx.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1
  have hge' : vlen.toNat ≤ idx.toNat := by
    have := BitVec.not_lt.mp (by simpa using hge); exact BitVec.le_def.mp this
  wpc_auto
  wpc_done

fncost_register "cl_dups" clDups cl_dups_cost

end Vbcf.Proof
