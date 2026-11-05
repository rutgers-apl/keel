import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCore

/-!
# Vbcf cost proofs: the core node-building family

Cost lemmas for the functions of `Vbcf/Core.lean` that build and intern
nodes, bottom-up.  Per function: `(A ≥, B, S)` (allowance `B`, slack `S`),
lines of proof, and how it was proved (`pure`: `FnCost.amort_of_pure`;
`auto2`: `wpc_auto; wpc_done` alone; `loop`/`manual`: by hand).

| function    | A ≥ | B              | S       | lines | how |
|-------------|-----|----------------|---------|-------|-----|
| `ty_of`     | –   | 15             | noSlack | 2     | pure |
| `expr_at`   | –   | 9              | noSlack | 2     | pure |
| `ck_hash`   | –   | 5·n + 12       | noSlack | 31    | loop (`words_eq` style) |
| `ck_all_ty` | –   | 25·n + 5       | noSlack | 35    | loop, calls `ty_of` |
| `ck_sum_bv` | –   | 25·n + 5       | noSlack | 39    | loop, calls `ty_of` |
| `ck_tyck`   | –   | 7000           | noSlack | 5     | auto2 + `wpc_join` |
| `ck_room`   | 6   | 60             | noSlack | 64    | manual (`charge_work/mem`, kvrealloc) |
| `ck_hput`   | 20  | 60             | noSlack | 68    | manual; probe loop paid unit by unit |
| `ck_hgrow`  | 100 | 80             | noSlack | 166   | manual; rehash loop paid by the 2·hcap charge |
| `ck_intern` | 100 | 7300           | noSlack | 123   | manual; probes paid by `spend`'s slack |
| `mk0`–`mk3`, `mkval` | 100 | 7400  | noSlack | 6     | auto2 |
| `mk_eq`, `mk_not` | 100 | 7410     | noSlack | 5     | auto2 |
| `mkn`       | 100 | 8800           | noSlack | 54    | loop (≤ 255 words) |
| `find_not`  | 20  | 30             | noSlack | 49    | loop paid by `tick`'s slack |
| `push_args` | 100 | 80             | noSlack | 37    | loop paid by `push`'s slack |

`n` is the length argument of `ck_hash`/`ck_all_ty`/`ck_sum_bv`; their
callers bound it (`ck_tyck` keeps the `& 0xff` bound of its `n`).

Helpers defined here (general, candidates for `CostAuto.lean`):
* `cost_args` (after `wpc_call`: evaluate the callee's local arguments, so
  that e.g. a mask bound carries over), `name_bud` (name the budget after a
  call), `wpc_step`/`wpc_auto` (`wpc_step` with `assign_band`,
  `assign_set` and `cost_args`), `cost_clean`, `cost_arith`,
  `wpc_finish`/`wpc_done` (normalise numeral sums before `omega`: `omega`
  can run for minutes on deeply nested `1 + (1 + …)` sums),
  `wpc_ite_case` (an `if` on a call's result, settling its slack).
* `WPC.ite_call_join`/`wpc_join`, `WPC.ite_assign_join`, `WPC.seq_join`:
  join the branches of an `if` before the rest (else the rest is proved
  once per branch: `ck_tyck` is 8× slower without).
* `WPC.charge_work`/`charge_mem` (+ `_fld`, keeping one struct cell): the
  `if (st->work < E) { …; return 0; } st->work = st->work - E;` pattern.
* `WPC.assign_u64`, `WPC.assign_set`, `WPC.assign_one_band`,
  `Budget.fld4`, `Fld.load_undef`, `ptr_u32_ne_sb` (a `u32 *` value is not
  the struct, so freeing it keeps the budget), `costC_kvfree`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000

theorem evalArgs_last2 {P : Prog} {env : Env} {m : Mem} {e1 e2 : Expr} {v1 v2 : Val}
    (h : evalArgs P env m [e1, e2] = some [v1, v2]) : evalE P env m e2 = some v2 := by
  obtain ⟨x, y, -, h2, e⟩ := evalArgs_two h
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨-, rfl⟩ := e
  exact h2

/-! ## Leaves -/

theorem ty_of_cost (sb A : Nat) (hdr : BitVec 32) :
    FnCost (State := State) Vbcf.prog "ty_of" (BudPre sb [.u32 hdr]) (Amort sb A (allow 17) 0 noSlack) := by
  apply FnCost.intro (fn := tyOf) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body tyOf
  wpc_auto
  wpc_done

fncost_register "ty_of" tyOf ty_of_cost

theorem expr_at_cost (sb A : Nat) (p : BitVec 32) :
    FnCost (State := State) Vbcf.prog "expr_at" (BudPre sb [.ptr sb 0, .u32 p]) (Amort sb A (allow 11) 0 noSlack) := by
  apply FnCost.intro (fn := exprAt) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body exprAt
  wpc_auto
  wpc_done

fncost_register "expr_at" exprAt expr_at_cost

theorem ck_hash_cost (sb A : Nat) (off n : BitVec 32) :
    FnCost (State := State) Vbcf.prog "ck_hash" (BudPre sb [.ptr sb 0, .u32 off, .u32 n])
      (Amort sb A (allow (6 * n.toNat + 17)) 0 noSlack) := by
  apply FnCost.intro (fn := ckHash) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckHash
  wpc_auto
  apply WPC.while
    (I := fun env' st' k => st' = st ∧ ∃ h i : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("off", .u32, .u32 off), ("n", .u32, .u32 n),
        ("h", .u32, .u32 h), ("i", .u32, .u32 i)] ∧
      i.toNat ≤ n.toNat ∧ k.t ≤ 6 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨rfl, _, 0#32, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, h, i, rfl, hin, hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have : i.toNat = n.toNat := by
      have := BitVec.not_lt.mp (by simpa using hge); rw [BitVec.le_def] at this; omega
    wpc_auto
    wpc_done
  · have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq
    apply WPC.assign_u32 (by rfl)
    intro h'
    wpc_simp
    apply WPC.assign
    embc_simp
    simp only [envU32, Env.get]
    simp only [String.reduceEq, ↓reduceIte, hi1]
    exact ⟨by omega, h', i + 1#32, ⟨rfl, rfl⟩, by omega, by omega, hkm⟩

fncost_register "ck_hash" ckHash ck_hash_cost

theorem ck_all_ty_cost (sb A : Nat) (base n t : BitVec 32) :
    FnCost (State := State) Vbcf.prog "ck_all_ty" (BudPre sb [.ptr sb 0, .u32 base, .u32 n, .u32 t])
      (Amort sb A (allow (27 * n.toNat + 8)) 0 noSlack) := by
  apply FnCost.intro (fn := ckAllTy) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckAllTy
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i ta : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("n", .u32, .u32 n),
        ("t", .u32, .u32 t), ("i", .u32, .u32 i), ("ta", .u32, .u32 ta)] ∧
      i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w.toNat + 27 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, rfl, by simp, w, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, ta, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have : i.toNat = n.toNat := by
      have := BitVec.not_lt.mp (by simpa using hge); rw [BitVec.le_def] at this; omega
    wpc_auto
    wpc_done
  · have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq
    wpc_call
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    apply WPC.assign
    embc_simp
    simp only [envU32, Env.get]
    simp only [String.reduceEq, ↓reduceIte, hi1]
    exact ⟨by omega, by omega, _, _, by assumption, by cost_arith, by cost_arith⟩

fncost_register "ck_all_ty" ckAllTy ck_all_ty_cost

theorem ck_sum_bv_cost (sb A : Nat) (base n : BitVec 32) :
    FnCost (State := State) Vbcf.prog "ck_sum_bv" (BudPre sb [.ptr sb 0, .u32 base, .u32 n])
      (Amort sb A (allow (30 * n.toNat + 8)) 0 noSlack) := by
  apply FnCost.intro (fn := ckSumBv) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckSumBv
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i t s : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("n", .u32, .u32 n),
        ("i", .u32, .u32 i), ("t", .u32, .u32 t), ("sum", .u32, .u32 s)] ∧
      i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w.toNat + 30 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, 0#32, rfl, by simp, w, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, t, s, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have : i.toNat = n.toNat := by
      have := BitVec.not_lt.mp (by simpa using hge); rw [BitVec.le_def] at this; omega
    wpc_auto
    wpc_done
  · have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq
    wpc_call
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    apply WPC.seq
    apply WPC.assign_u32 (by rfl)
    intro s'
    wpc_simp
    apply WPC.assign
    embc_simp
    simp only [envU32, Env.get]
    simp only [String.reduceEq, ↓reduceIte, hi1]
    exact ⟨by omega, by omega, _, _, by assumption, by cost_arith, by cost_arith⟩

fncost_register "ck_sum_bv" ckSumBv ck_sum_bv_cost



theorem ck_tyck_cost (sb A : Nat) :
    FnCost (State := State) Vbcf.prog "ck_tyck" (BudPre sb [.ptr sb 0]) (Amort sb A (allow 8000) 0 noSlack) := by
  apply FnCost.intro (fn := ckTyck) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckTyck
  repeat (any_goals (first | wpc_join A 30 | wpc_step))
  wpc_done

fncost_register "ck_tyck" ckTyck ck_tyck_cost

theorem ck_room_cost (sb A : Nat) (hA : 6 ≤ A) (n : BitVec 32) :
    FnCost (State := State) Vbcf.prog "ck_room" (BudPre sb [.ptr sb 0, .u32 n]) (Amort sb A (allow 60) 0 noSlack) := by
  apply FnCost.intro (fn := ckRoom) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckRoom
  apply WPC.seq
  apply WPC.assign_u64 (by rfl)
  intro need
  wpc_simp
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro nc0
  wpc_simp
  apply WPC.ite_assign_join (by rfl) ⟨nc0, by simp [Env.set]⟩
  intro nc1 _cost1 _hcost1 _hmem1
  wpc_simp
  apply WPC.ite_assign_join (by rfl) ⟨nc1, by simp [Env.set]⟩
  intro nc _cost2 _hcost2 _hmem2
  wpc_simp
  apply WPC.charge_work (k := nc) hb (by rfl) (by simp [evalE, Env.get])
  · intro m' hb'
    wpc_finish
  intro hle m1 hb1
  have hle' : nc.toNat ≤ w.toNat := BitVec.le_def.mp hle
  have hw1 : (w - nc).toNat = w.toNat - nc.toNat := bv_sub_toNat_of_le hle
  have hpot : A * (w - nc).toNat + A * nc.toNat = A * w.toNat := by rw [hw1]; exact mul_sub_add hle'
  apply WPC.charge_mem (k := nc) hb1 (by rfl) (by simp [evalE, Env.get])
  · intro m' hb'
    wpc_finish
  intro hlem m2 hb2
  have hm2 : (mm - nc).toNat = mm.toNat - nc.toNat := bv_sub_toNat_of_le hlem
  have hlem' : nc.toNat ≤ mm.toNat := BitVec.le_def.mp hlem
  have hAnc : 2 * nc.toNat ≤ A * nc.toNat := Nat.mul_le_mul_right _ (by omega)
  apply WPC.seq
  apply WPC.ecall_bud hb2
  intro vs hvs
  obtain ⟨x, y, -, hy, rfl⟩ := evalArgs_two hvs
  simp [evalE, evalCast, Env.get] at hy
  subst hy
  have hcost : Ext.costC prog (.kvrealloc .u32) [x, .u64 (nc.setWidth 64)] =
      ⟨2 * nc.toNat, nc.toNat⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]; have := nc.isLt; omega
  refine ⟨by simp, ?_⟩
  intro rv st3 hb3
  rw [hcost]
  cases rv with
  | none => simp [assignDst]
  | some np =>
    simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
    by_cases hty : st3.mem.hasTy np (.ptr .u32) = true
    · simp only [hty, ↓reduceIte, Env.set, String.reduceEq]
      wpc_auto
      wpc_done
    · simp [hty]

fncost_register "ck_room" ckRoom ck_room_cost

theorem ck_hput_cost (sb A : Nat) (hA : 20 ≤ A) (id : BitVec 32) :
    FnCost (State := State) Vbcf.prog "ck_hput" (BudPre sb [.ptr sb 0, .u32 id]) (Amort sb A (allow 60) 0 noSlack) := by
  apply FnCost.intro (fn := ckHput) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckHput
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro mask
  wpc_simp
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro n
  wpc_simp
  apply WPC.charge_work (k := n) hb (by rfl) (by simp [evalE, Env.get])
  · intro m' hb'
    wpc_finish
  intro hle m1 hb1
  have hle' : n.toNat ≤ w.toNat := BitVec.le_def.mp hle
  have hpot : A * (w - n).toNat + A * n.toNat = A * w.toNat := by
    rw [bv_sub_toNat_of_le hle]; exact mul_sub_add hle'
  have hAn : 6 * n.toNat ≤ A * n.toNat := Nat.mul_le_mul_right _ (by omega)
  apply WPC.seq
  wpc_call
  cost_args
  name_bud st2 w2 mm2 hb2
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro i0
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i h' : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, .u32 id), ("i", .u32, .u32 i),
        ("mask", .u32, .u32 mask), ("h", .u32, .u32 h'), ("n", .u32, .u32 n)] ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w2.toNat ∧ k.m + mm'.toNat ≤ mm2.toNat)
    (μ := fun _ st' => wk st'.mem sb)
  · exact ⟨i0, _, rfl, w2, mm2, hb2, by simp, by simp⟩
  rintro env' st' k ⟨i, h', rfl, w', mm', hb', hk, hkm⟩
  split
  case h_2 => trivial
  rename_i v hv
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · wpc_auto
    wpc_done
  apply WPC.seq
  apply WPC.ite
  embc_simp [hb'.ld_work]
  constructor
  · intro hz
    wpc_auto
    wpc_done
  intro hz
  apply WPC.skip
  wpc_simp
  have h1 := bv_sub_one_toNat hz
  have h2 := bv_pos_of_ne hz
  have h3 : A * (w' - 1#32).toNat + A = A * w'.toNat := by
    rw [h1]; simpa using mul_sub_add (A := A) h2
  apply WPC.seq
  apply WPC.setWork (x := w' - 1#32) hb' (by embc_simp) (by embc_simp [hb'.ld_work])
  intro m' hb''
  wpc_simp
  apply WPC.assign_u32 (by rfl)
  intro i'
  wpc_simp
  refine ⟨?_, ⟨i', h', rfl⟩, _, _, hb'', ?_, ?_⟩
  · rw [hb''.wk, hb'.wk]; omega
  · cost_arith
  · cost_arith

fncost_register "ck_hput" ckHput ck_hput_cost

theorem ck_hgrow_cost (sb A : Nat) (hA : 100 ≤ A) :
    FnCost (State := State) Vbcf.prog "ck_hgrow" (BudPre sb [.ptr sb 0]) (Amort sb A (allow 80) 0 noSlack) := by
  apply FnCost.intro (fn := ckHgrow) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckHgrow
  have hA20 : 20 ≤ A := by omega
  obtain ⟨hv, hfld⟩ := hb.fld4
  apply WPC.seq
  apply WPC.ite
  cases hv with
  | undef => simp [evalE, Env.get, hfld.load_undef fi_hcap]
  | u64 _ => simp [evalE, Env.get, hfld.load fi_hcap (by simp), evalBin]
  | ptr _ _ => simp [evalE, Env.get, hfld.load fi_hcap (by simp), evalBin]
  | null => simp [evalE, Env.get, hfld.load fi_hcap (by simp), evalBin]
  | uptr => simp [evalE, Env.get, hfld.load fi_hcap (by simp), evalBin]
  | u32 h =>
  simp only [evalE, Env.get, ↓reduceIte, hfld.load fi_hcap (by simp)]
  simp only [evalBin, evalArith, Val.ofBool]
  constructor
  · intro _
    wpc_auto
    wpc_done
  intro hge
  have hlt : h.toNat < 1073741824 := by
    by_cases hc : (1073741824#32 ≤ h)
    · simp [hc] at hge
    · rw [BitVec.le_def] at hc; simpa using hc
  apply WPC.skip
  wpc_simp
  have h2 : (h * 2#32).toNat = 2 * h.toNat := by rw [BitVec.toNat_mul]; simp; omega
  apply WPC.charge_work_fld (k := h * 2#32) hb hfld (fieldIn_ne_of_ne fi_hcap (by decide)) (by rfl)
    (by simp [evalE, Env.get, hfld.load fi_hcap (by simp), evalBin, evalArith])
  · intro m' hb'
    wpc_finish
  intro hle m1 hb1 hfld1
  have hle' : 2 * h.toNat ≤ w.toNat := by rw [← h2]; exact BitVec.le_def.mp hle
  have hpot : A * (w - h * 2#32).toNat + A * (2 * h.toNat) = A * w.toNat := by
    rw [bv_sub_toNat_of_le hle, h2]; exact mul_sub_add hle'
  apply WPC.charge_mem_fld (k := h * 2#32) hb1 hfld1 (fieldIn_ne_of_ne fi_hcap (by decide)) (by rfl)
    (by simp [evalE, Env.get, hfld1.load fi_hcap (by simp), evalBin, evalArith])
  · intro m' hb'
    wpc_finish
  intro hlem m2 hb2 hfld2
  have hlem' : 2 * h.toNat ≤ mm.toNat := by rw [← h2]; exact BitVec.le_def.mp hlem
  have hm2 : (mm - h * 2#32).toNat = mm.toNat - 2 * h.toNat := by rw [bv_sub_toNat_of_le hlem, h2]
  -- nt = kvcalloc(2 * hcap)
  apply WPC.seq
  apply WPC.ecall
  simp only [evalArgs, evalE, Env.get, ↓reduceIte, hfld2.load fi_hcap (by simp), evalCast,
    evalBin, evalArith]
  have hx : (BitVec.setWidth 64 h * 2#64).toNat = 2 * h.toNat := by
    rw [BitVec.toNat_mul]; simp; omega
  cases hr : Ext.run prog (Ext.kvcalloc Ty.u32) [Val.u64 (BitVec.setWidth 64 h * 2#64)]
      { mem := m2, oracle := st.oracle } with
  | none => trivial
  | some r =>
  obtain ⟨rv, st3⟩ := r
  have hb3 := Budget.ext (st := { mem := m2, oracle := st.oracle }) hb2 hr (by intro _ _ h; cases h)
  have hfld3 := Fld.ext (st := { mem := m2, oracle := st.oracle }) hfld2 hr (by intro _ _ h; cases h)
  have hcost : Ext.costC prog (.kvcalloc .u32) [.u64 (BitVec.setWidth 64 h * 2#64)] =
      ⟨2 * (2 * h.toNat), 2 * h.toNat⟩ := by
    simp only [Ext.costC, Ext.cost, Ext.words, hx]
  simp only [hcost]
  have hAh : 47 * (2 * h.toNat) ≤ A * (2 * h.toNat) := Nat.mul_le_mul_right _ (by omega)
  cases rv with
  | none => simp [assignDst]
  | some vnt =>
  simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
  by_cases hty : st3.mem.hasTy vnt (.ptr .u32) = true
  case neg => simp [hty]
  simp only [hty, ↓reduceIte, Env.set, String.reduceEq]
  have hnt := ptr_u32_ne_sb hfld3 hty
  -- if (nt == NULL) return 0;
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  -- old = st->htab;
  apply WPC.seq
  apply WPC.assign_set
  intro vold t ht hvold
  simp only [Env.ty, String.reduceEq, ↓reduceIte, Option.some.injEq] at ht
  subst ht
  have hold := ptr_u32_ne_sb hfld3 hvold
  wpc_simp
  -- ocap = st->hcap;
  apply WPC.seq
  apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, hfld3.load fi_hcap (by simp), Env.assign, Env.ty,
    Mem.hasTy_u32, Env.set]
  -- ocnt = st->hcnt;
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro ocnt
  wpc_simp
  -- st->htab = nt; st->hcap = ocap * 2; st->hcnt = 0;
  apply WPC.seq; apply WPC.setField_bud hb3 (by decide) (by decide); intro m4 hb4; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb4 (by decide) (by decide); intro m5 hb5; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb5 (by decide) (by decide); intro m6 hb6; wpc_simp
  -- the loop over the old table: each entry is paid by the charge
  generalize hW3 : w - h * 2#32 = W3 at *
  generalize hM3 : mm - h * 2#32 = M3 at *
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i e ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("old", .ptr .u32, vold), ("nt", .ptr .u32, vnt),
        ("ocap", .u32, .u32 h), ("ocnt", .u32, .u32 ocnt), ("i", .u32, .u32 i), ("e", .u32, .u32 e),
        ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ h.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * W3.toNat + 90 * i.toNat ∧
      k.m + mm'.toNat ≤ M3.toNat)
    (μ := fun env' _ => h.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, 0#32, rfl, by simp, _, _, hb6, by simp, by simp⟩
  rintro env' st' k ⟨i, e, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt' => ?_⟩
  · -- done: kvfree(old); return 1;
    have : i.toNat = h.toNat := by
      have := BitVec.not_lt.mp (by simpa using hge); rw [BitVec.le_def] at this; omega
    apply WPC.seq
    apply WPC.ecall_bud hb'
    intro vs hvs
    simp only [evalArgs, evalE, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at hvs
    subst hvs
    refine ⟨fun b hb e => hold b (by simpa using hb), ?_⟩
    intro rv st4 hb4
    simp only [assignDst_none, costC_kvfree]
    wpc_auto
    wpc_done
  have hlt'' : i.toNat < h.toNat := by simpa [BitVec.lt_def] using hlt'
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  -- e = old[i];
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro e'
  wpc_simp
  apply WPC.seq
  apply WPC.ite_any
  · -- ok = ck_hput(st, e - 1); if (ok == 0) { restore; kvfree(nt); return 0; }
    apply WPC.seq
    wpc_call
    cost_args
    name_bud st5 w5 mm5 hb5
    apply WPC.ite_any
    · wpc_auto
      apply WPC.ecall_bud ‹Budget _ _ _ _›
      intro vs hvs
      simp only [evalArgs, evalE, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at hvs
      subst hvs
      refine ⟨fun b hb e => hnt b (by simpa using hb), ?_⟩
      intro rv st4 hb4
      simp only [assignDst_none, costC_kvfree]
      wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    apply WPC.assign
    embc_simp
    simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
    refine ⟨by omega, by omega, _, _, hb5, ?_, ?_⟩ <;> cost_arith
  apply WPC.skip
  wpc_simp
  apply WPC.assign
  embc_simp
  simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
  refine ⟨by omega, by omega, _, _, hb', ?_, ?_⟩ <;> cost_arith

fncost_register "ck_hgrow" ckHgrow ck_hgrow_cost

theorem ck_intern_cost (sb A : Nat) (hA : 100 ≤ A) :
    FnCost (State := State) Vbcf.prog "ck_intern" (BudPre sb [.ptr sb 0]) (Amort sb A (allow 8400) 0 noSlack) := by
  apply FnCost.intro (fn := ckIntern) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckIntern
  have hA6 : 6 ≤ A := by omega
  -- base = st->plen; ok = ck_tyck(st); if (ok == 0) return NOID;
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro base
  wpc_simp
  apply WPC.seq
  wpc_call
  name_bud st1 w1 mm1 hb1
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  -- n = 1 + ((st->pool[base] >> 8) & 0xff);
  apply WPC.seq
  apply WPC.assign_one_band (by rfl) (by decide)
  intro n hn1 hn2
  wpc_simp
  -- ok = spend(st, n); if (ok == 0) return NOID;
  apply WPC.seq
  wpc_call
  cost_args
  name_bud st2 w2 mm2 hb2
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  have hAn : A ≤ A * n.toNat := Nat.le_mul_of_pos_right _ hn1
  have hAn5 : 25 * n.toNat ≤ A * n.toNat := Nat.mul_le_mul_right _ (by omega)
  -- if (the table is half full) { ok = ck_hgrow(st); if (ok == 0) return NOID; }
  apply WPC.seq_join (J := fun env' st' k => ∃ ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("n", .u32, .u32 n),
        ("h", .u32, .u32 0), ("i", .u32, .u32 0), ("mask", .u32, .u32 0), ("e", .u32, .u32 0),
        ("ok", .u32, .u32 ok)] ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w2.toNat + 90 ∧ k.m + mm'.toNat ≤ mm2.toNat)
  · apply WPC.ite_any
    · apply WPC.seq
      wpc_call
      apply WPC.ite_any
      · wpc_auto
        wpc_done
      apply WPC.skip
      wpc_simp
      exact ⟨_, rfl, _, _, ‹Budget _ _ _ _›, by cost_arith, by cost_arith⟩
    · apply WPC.skip
      wpc_simp
      exact ⟨_, rfl, w2, mm2, hb2, by cost_arith, by cost_arith⟩
  rintro env3 st3 k3 ⟨ok3, rfl, w3, mm3, hb3, hk3, hkm3⟩
  -- mask = st->hcap - 1; h = ck_hash(st, base, n); i = h & mask;
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro mask
  wpc_simp
  apply WPC.seq
  wpc_call
  cost_args
  name_bud st4 w4 mm4 hb4
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro i0
  wpc_simp
  -- the probes: each is paid by its `spend`
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ h i e ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("n", .u32, .u32 n),
        ("h", .u32, .u32 h), ("i", .u32, .u32 i), ("mask", .u32, .u32 mask), ("e", .u32, .u32 e),
        ("ok", .u32, .u32 ok)] ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w4.toNat ∧ k.m + mm'.toNat ≤ mm4.toNat)
    (μ := fun _ st' => wk st'.mem sb)
  · exact ⟨_, _, _, _, rfl, w4, mm4, hb4, by simp, by simp⟩
  rintro env' st' k ⟨h', i, e, ok, rfl, w', mm', hb', hk, hkm⟩
  split
  case h_2 => trivial
  rename_i v hv
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · wpc_auto
    wpc_done
  -- ok = spend(st, n); if (ok == 0) return NOID;
  apply WPC.seq
  wpc_call
  cost_args
  name_bud st5 w5 mm5 hb5
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  -- e = st->htab[i] - 1; ok = words_eq(...)
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro e'
  wpc_simp
  apply WPC.seq
  wpc_call
  have hlast := evalArgs_last2 ‹evalArgs _ _ _ [_, _] = some [_, _]›
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq, Val.u32.injEq] at hlast
  subst hlast
  name_bud st6 w6 mm6 hb6
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.assign_u32 (by rfl)
  intro i'
  wpc_simp
  have hlt6 : A * w6.toNat < A * w'.toNat := by cost_arith
  refine ⟨?_, _, _, _, _, rfl, _, _, hb6, ?_, ?_⟩
  · rw [hb6.wk, hb'.wk]; exact Nat.lt_of_mul_lt_mul_left hlt6
  · cost_arith
  · cost_arith

fncost_register "ck_intern" ckIntern ck_intern_cost

theorem mk0_cost (sb A : Nat) (hA : 100 ≤ A) (hdr : BitVec 32) :
    FnCost (State := State) Vbcf.prog "mk0" (BudPre sb [.ptr sb 0, .u32 hdr]) (Amort sb A (allow 8500) 0 noSlack) := by
  apply FnCost.intro (fn := mk0) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body mk0
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "mk0" mk0 mk0_cost

theorem mk1_cost (sb A : Nat) (hA : 100 ≤ A) (hdr a : BitVec 32) :
    FnCost (State := State) Vbcf.prog "mk1" (BudPre sb [.ptr sb 0, .u32 hdr, .u32 a]) (Amort sb A (allow 8500) 0 noSlack) := by
  apply FnCost.intro (fn := mk1) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body mk1
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "mk1" mk1 mk1_cost

theorem mk2_cost (sb A : Nat) (hA : 100 ≤ A) (hdr a b : BitVec 32) :
    FnCost (State := State) Vbcf.prog "mk2" (BudPre sb [.ptr sb 0, .u32 hdr, .u32 a, .u32 b])
      (Amort sb A (allow 8500) 0 noSlack) := by
  apply FnCost.intro (fn := mk2) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body mk2
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "mk2" mk2 mk2_cost

theorem mk3_cost (sb A : Nat) (hA : 100 ≤ A) (hdr a b c : BitVec 32) :
    FnCost (State := State) Vbcf.prog "mk3" (BudPre sb [.ptr sb 0, .u32 hdr, .u32 a, .u32 b, .u32 c])
      (Amort sb A (allow 8500) 0 noSlack) := by
  apply FnCost.intro (fn := mk3) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body mk3
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "mk3" mk3 mk3_cost

theorem mkval_cost (sb A : Nat) (hA : 100 ≤ A) (w : BitVec 32) (v : BitVec 64) :
    FnCost (State := State) Vbcf.prog "mkval" (BudPre sb [.ptr sb 0, .u32 w, .u64 v]) (Amort sb A (allow 8500) 0 noSlack) := by
  apply FnCost.intro (fn := mkval) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body mkval
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  wpc_done

fncost_register "mkval" mkval mkval_cost

theorem mk_eq_cost (sb A : Nat) (hA : 100 ≤ A) (a b : BitVec 32) :
    FnCost (State := State) Vbcf.prog "mk_eq" (BudPre sb [.ptr sb 0, .u32 a, .u32 b]) (Amort sb A (allow 8510) 0 noSlack) := by
  apply FnCost.intro (fn := mkEq) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body mkEq
  wpc_auto
  wpc_done

fncost_register "mk_eq" mkEq mk_eq_cost

theorem mk_not_cost (sb A : Nat) (hA : 100 ≤ A) (a : BitVec 32) :
    FnCost (State := State) Vbcf.prog "mk_not" (BudPre sb [.ptr sb 0, .u32 a]) (Amort sb A (allow 8510) 0 noSlack) := by
  apply FnCost.intro (fn := mkNot) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body mkNot
  wpc_auto
  wpc_done

fncost_register "mk_not" mkNot mk_not_cost

theorem mkn_cost (sb A : Nat) (hA : 100 ≤ A) (hdr base n : BitVec 32) :
    FnCost (State := State) Vbcf.prog "mkn" (BudPre sb [.ptr sb 0, .u32 hdr, .u32 base, .u32 n])
      (Amort sb A (allow 10100) 0 noSlack) := by
  apply FnCost.intro (fn := mkn) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body mkn
  have hA6 : 6 ≤ A := by omega
  -- if (n > 255) return NOID;
  apply WPC.seq
  apply WPC.ite
  embc_simp
  constructor
  · intro _
    wpc_auto
    wpc_done
  intro hn
  have hn' : n.toNat ≤ 255 := by have := BitVec.le_def.mp hn; simpa using this
  apply WPC.skip
  wpc_simp
  -- r = ck_room(st, 1 + n); if (r == 0) return NOID; st->pool[st->plen] = ...;
  apply WPC.seq
  wpc_call
  name_bud st1 w1 mm1 hb1
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.store_bud hb1
  intro m2 hb2
  wpc_simp
  -- the copy loop: at most 255 words
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i r : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("hdr", .u32, .u32 hdr), ("base", .u32, .u32 base),
        ("n", .u32, .u32 n), ("r", .u32, .u32 r), ("i", .u32, .u32 i)] ∧
      i.toNat ≤ n.toNat ∧ Budget st'.mem sb w1 mm1 ∧ k.t ≤ 6 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨0#32, _, rfl, by simp, hb2, by simp, by simp⟩
  rintro env' st' k ⟨i, r, rfl, hin, hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq
  apply WPC.store_bud hb'
  intro m3 hb3
  wpc_simp
  apply WPC.assign
  embc_simp
  simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
  exact ⟨by omega, by omega, hb3, by omega, by simpa using hkm⟩

fncost_register "mkn" mkn mkn_cost

theorem find_not_cost (sb A : Nat) (hA : 30 ≤ A) (a : BitVec 32) :
    FnCost (State := State) Vbcf.prog "find_not" (BudPre sb [.ptr sb 0, .u32 a]) (Amort sb A (allow 50) 0 noSlack) := by
  apply FnCost.intro (fn := findNot) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body findNot
  have hA6 : 6 ≤ A := by omega
  iterate 8 (apply WPC.seq; apply WPC.assign_u32 (by rfl); intro _; wpc_simp)
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ h i mask e ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("h", .u32, .u32 h),
        ("i", .u32, .u32 i), ("mask", .u32, .u32 mask), ("e", .u32, .u32 e), ("ok", .u32, .u32 ok)] ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun _ st' => wk st'.mem sb)
  · exact ⟨_, _, _, _, _, rfl, w, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨h', i, mask, e, ok, rfl, w', mm', hb', hk, hkm⟩
  split
  case h_2 => trivial
  rename_i v hv
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · wpc_auto
    wpc_done
  -- ok = tick(st); if (ok == 0) return NOID;
  apply WPC.seq
  wpc_call
  name_bud st5 w5 mm5 hb5
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro e'
  wpc_simp
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.assign_u32 (by rfl)
  intro i'
  wpc_simp
  have hlt5 : A * w5.toNat < A * w'.toNat := by cost_arith
  refine ⟨?_, _, _, _, _, _, rfl, _, _, hb5, ?_, ?_⟩
  · rw [hb5.wk, hb'.wk]; exact Nat.lt_of_mul_lt_mul_left hlt5
  · cost_arith
  · cost_arith

fncost_register "find_not" findNot find_not_cost

theorem push_args_cost (sb A : Nat) (hA : 100 ≤ A) (id : BitVec 32) :
    FnCost (State := State) Vbcf.prog "push_args" (BudPre sb [.ptr sb 0, .u32 id]) (Amort sb A (allow 80) 0 noSlack) := by
  apply FnCost.intro (fn := pushArgs) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body pushArgs
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq
  apply WPC.assign_band (by rfl)
  intro n hn
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, .u32 id), ("n", .u32, .u32 n),
        ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧ i.toNat ≤ n.toNat ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨_, _, rfl, by simp, w, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
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
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.assign
  embc_simp
  simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]
  refine ⟨by omega, by omega, _, _, hb5, ?_, ?_⟩ <;> cost_arith

fncost_register "push_args" pushArgs push_args_cost

end Vbcf.Proof
