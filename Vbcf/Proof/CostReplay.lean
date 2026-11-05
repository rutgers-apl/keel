import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCore2

/-!
# Vbcf cost proofs: the replay driver (`Vbcf/Replay.lean`)

`ck_init` sets the two budgets from the input size, so its cost lemma is not
an `Amort`: it starts from a zeroed struct and ends with the budgets
`workBudget`/`memBudget`, having spent `1280` words (the hash table and the
premise array) and the two `mk0` calls.  It also says the memory budget is
then at most `2^30` (`ck_init` checks it against `MAX_POOL`); `ck_compact`
needs that bound.

The other three are `Amort` lemmas.  Per function: `(A ≥, B, S)`, lines of
proof (statement included), how it was proved.

| function  | A ≥ | B                     | S       | lines | how |
|-----------|-----|-----------------------|---------|-------|-----|
| `ck_scan` | 100 | 100                   | noSlack | 186   | manual: each of the two passes over the steps paid by its own `spend(st, ns)`; the premise loop of the second (`≤ 255`) inside; `charge_mem` + kvcalloc for `facts` and `lr` |
| `ck_goal` | 100 | 7850·goal + 8100      | noSlack | 111   | manual: zeroing loop paid by `spend(st, n)`; sweep of `goal + 1` nodes, inner loops ≤ 255 |
| `ck_load` | 100 | 16000·nwords + 100    | noSlack | 121   | manual: ≤ `ne` nodes (`ne + ns + 3 = nwords`), each `ck_room` + `ck_intern` + 3 loops ≤ 255 |

None is automatic: each has loops whose bound needs a branch condition
(`WPC.ite`).  Helpers here: `replay_scan_step`, `replay_load_step` (the
loop counter steps without wrapping), `replay_load_sizes` (the `u64` size
check as numbers), `replay_scanEnv`/`replay_goalEnv`/`replay_loadEnv` (the
locals, for the loop invariants).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

/-- The work budget `ck_init` grants: `WORK_PER_WORD * (nwords + goal) + WORK_BASE`. -/
def workBudget (n g : BitVec 32) : Nat := 128 * (n.toNat + g.toNat) + 2 ^ 20

/-- The memory budget `ck_init` grants: `MEM_PER_WORD * (nwords + goal) + MEM_BASE`. -/
def memBudget (n g : BitVec 32) : Nat := 32 * (n.toNat + g.toNat) + 2 ^ 18

theorem bv64_budget_toNat (k b : Nat) (n g : BitVec 32) (hk : k ≤ 128) (hb : b ≤ 2 ^ 20)
    (hle : ¬ (1073741824#64 < BitVec.ofNat 64 k * (n.setWidth 64 + g.setWidth 64) + BitVec.ofNat 64 b)) :
    ((BitVec.ofNat 64 k * (n.setWidth 64 + g.setWidth 64) + BitVec.ofNat 64 b).setWidth 32).toNat =
      k * (n.toNat + g.toNat) + b ∧ k * (n.toNat + g.toNat) + b ≤ 2 ^ 30 := by
  have hn := n.isLt
  have hg := g.isLt
  have hp : k * (n.toNat + g.toNat) ≤ 128 * (2 ^ 32 + 2 ^ 32) := Nat.mul_le_mul hk (by omega)
  have h1 : (n.setWidth 64 + g.setWidth 64).toNat = n.toNat + g.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show n.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show g.toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show n.toNat + g.toNat < 2 ^ 64 by omega)]
  have hk64 : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  have hb64 : b % 2 ^ 64 = b := Nat.mod_eq_of_lt (by omega)
  have h2 : (BitVec.ofNat 64 k * (n.setWidth 64 + g.setWidth 64) + BitVec.ofNat 64 b).toNat =
      k * (n.toNat + g.toNat) + b := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk64, hb64,
      Nat.mod_eq_of_lt (show k * (n.toNat + g.toNat) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show k * (n.toNat + g.toNat) + b < 2 ^ 64 by omega)]
  rw [BitVec.lt_def, h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 1073741824 < 2 ^ 64 by omega)] at hle
  refine ⟨?_, by omega⟩
  rw [BitVec.toNat_setWidth, h2, Nat.mod_eq_of_lt (show k * (n.toNat + g.toNat) + b < 2 ^ 32 by omega)]

/-- Close a goal of `ck_init`'s postcondition by arithmetic, after rewriting with the
given facts (the values of the budget cells). -/
syntax "init_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| init_finish) => `(tactic| init_finish [])
  | `(tactic| init_finish [$ls,*]) => `(tactic| ((try simp only [retPostC]); (try intro _); (try cost_clean); refine ⟨_, _, ‹Budget _ _ _ _›, ?_, ?_⟩ <;> ((try simp only [Cost.add_t, Cost.add_m, Cost.zero_t, Cost.zero_m, Cost.one_t, Cost.one_m, Cost.mk_t, Cost.mk_m, reduceCostT, reduceCostM, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply, Option.some.injEq, Val.u32.injEq, ↓reduceIte, BitVec.reduceEq, or_false, false_or, or_true, true_or, $ls,*] at *); ((try simp +arith only) <;> omega))))

/-- `init_finish` for `ck_init`'s own postcondition, which also bounds the memory budget. -/
syntax "init_finish3" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| init_finish3) => `(tactic| init_finish3 [])
  | `(tactic| init_finish3 [$ls,*]) => `(tactic| ((try simp only [retPostC]); (try intro _); (try cost_clean); refine ⟨_, _, ‹Budget _ _ _ _›, ?_, ?_, ?_⟩ <;> ((try simp only [Cost.add_t, Cost.add_m, Cost.zero_t, Cost.zero_m, Cost.one_t, Cost.one_m, Cost.mk_t, Cost.mk_m, reduceCostT, reduceCostM, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply, Option.some.injEq, Val.u32.injEq, ↓reduceIte, BitVec.reduceEq, or_false, false_or, or_true, true_or, $ls,*] at *); ((try simp +arith only) <;> omega))))

theorem ck_init_cost (sb A : Nat) (hA : 100 ≤ A) (n g : BitVec 32) :
    FnCost (State := State) prog "ck_init"
      (fun vs st => vs = [.ptr sb 0, .u32 n, .u32 g] ∧ Budget st.mem sb 0#32 0#32)
      (fun _ _ _ st' c => ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        c.t + A * w'.toNat ≤ A * workBudget n g + 20000 ∧
        c.m + mm'.toNat ≤ memBudget n g + 1280 ∧ mm'.toNat ≤ 2 ^ 30) := by
  apply FnCost.intro (fn := ckInit) rfl
  rintro vs st ⟨rfl, hb⟩
  fncost_body ckInit
  -- t = kvcalloc(1024ull, sizeof(u32));
  apply WPC.seq
  apply WPC.ecall_bud hb
  intro vs hvs
  simp [evalArgs, evalE] at hvs
  subst hvs
  refine ⟨by simp, ?_⟩
  intro rv st1 hb1
  have hcost : Ext.costC prog (.kvcalloc .u32) [.u64 1024#64] = ⟨2048, 1024⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]
  rw [hcost]
  cases rv with
  | none => simp [assignDst]
  | some t =>
    simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
    by_cases hty : st1.mem.hasTy t (.ptr .u32) = true
    · simp only [hty, ↓reduceIte, Env.set, String.reduceEq]
      wpc_auto
      all_goals (try init_finish3)
      -- q = kvcalloc(256ull, sizeof(u32));
      apply WPC.ecall_bud ‹Budget _ _ _ _›
      intro vs hvs
      simp [evalArgs, evalE] at hvs
      subst hvs
      refine ⟨by simp, ?_⟩
      intro rv st2 hb2
      have hcost2 : Ext.costC prog (.kvcalloc .u32) [.u64 256#64] = ⟨512, 256⟩ := by
        simp [Ext.costC, Ext.cost, Ext.words]
      rw [hcost2]
      cases rv with
      | none => simp [assignDst]
      | some q =>
        simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
        by_cases hty2 : st2.mem.hasTy q (.ptr .u32) = true
        · simp only [hty2, ↓reduceIte, Env.set, String.reduceEq]
          -- if (q == NULL) { st->err = ERR_NOMEM; return 0; }
          apply WPC.seq
          apply WPC.ite_any
          · wpc_auto
            init_finish3
          apply WPC.skip
          wpc_simp
          -- st->prem = q;
          apply WPC.seq
          wpc_step
          -- b = (u64)WORK_PER_WORD * ((u64)nwords + (u64)goal) + (u64)WORK_BASE;
          apply WPC.seq
          apply WPC.assign_eval
          intro v hv
          simp [evalE, evalCast, evalBin, evalArith, Env.get] at hv
          subst hv
          simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u64]
          wpc_simp
          -- if (b > (u64)MAX_POOL) { st->err = ERR_LIMIT; return 0; }
          apply WPC.seq
          apply WPC.ite
          simp [evalE, evalCast, evalBin, evalArith, Env.get, MAX_POOL]
          constructor
          · intro _
            wpc_auto
            init_finish3
          intro hle1
          apply WPC.skip
          wpc_simp
          have hW := bv64_budget_toNat 128 1048576 n g (by decide) (by decide)
            (by intro h; simp [h] at hle1)
          clear hle1
          generalize 128#64 * (BitVec.setWidth 64 n + BitVec.setWidth 64 g) + 1048576#64 = Ew at hW ⊢
          have hW1 : (Ew.setWidth 32).toNat = workBudget n g := by rw [hW.1]; rfl
          -- st->work = (u32)b;
          apply WPC.seq
          refine WPC.setWork (x := Ew.setWidth 32) ‹Budget _ _ _ _› ?_ ?_ ?_
          · simp [evalE, Env.get]
          · simp [evalE, evalCast, Env.get]
          intro m3 hb3
          wpc_simp
          -- b = (u64)MEM_PER_WORD * ((u64)nwords + (u64)goal) + (u64)MEM_BASE;
          apply WPC.seq
          apply WPC.assign_eval
          intro v hv
          simp [evalE, evalCast, evalBin, evalArith, Env.get] at hv
          subst hv
          simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u64]
          wpc_simp
          -- if (b > (u64)MAX_POOL) { st->err = ERR_LIMIT; return 0; }
          apply WPC.seq
          apply WPC.ite
          simp [evalE, evalCast, evalBin, evalArith, Env.get]
          constructor
          · intro _
            wpc_auto
            init_finish3 [hW1]
          intro hle2
          apply WPC.skip
          wpc_simp
          have hM := bv64_budget_toNat 32 262144 n g (by decide) (by decide)
            (by intro h; simp [h] at hle2)
          clear hle2
          generalize 32#64 * (BitVec.setWidth 64 n + BitVec.setWidth 64 g) + 262144#64 = Em at hM ⊢
          have hM1 : (Em.setWidth 32).toNat = memBudget n g := by rw [hM.1]; rfl
          have hM2 : memBudget n g ≤ 2 ^ 30 := by unfold memBudget; have := hM.2; omega
          -- st->mem = (u32)b;
          apply WPC.seq
          refine WPC.setMem (x := Em.setWidth 32) ‹Budget _ _ _ _› ?_ ?_ ?_
          · simp [evalE, Env.get]
          · simp [evalE, evalCast, Env.get]
          intro m4 hb4
          wpc_simp
          wpc_auto
          all_goals init_finish3 [hW1, hM1, hM2]
        · simp [hty2]
    · simp [hty]

/-- One step of `ck_scan`'s loop: `p + 1 + pc + ac` does not wrap and stays within `ns`. -/
theorem replay_scan_step {p ns pc ac : BitVec 32} (hlt : p.toNat < ns.toNat) (hpc : pc.toNat ≤ 255)
    (hac : ac.toNat < 256) (hle : pc + ac ≤ ns - p - 1#32) :
    (p + 1#32 + pc + ac).toNat = p.toNat + 1 + pc.toNat + ac.toNat ∧
      p.toNat + 1 + pc.toNat + ac.toNat ≤ ns.toNat := by
  have hn := ns.isLt
  rw [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub] at hle
  simp only [BitVec.toNat_ofNat] at hle
  have h2 : p.toNat + 1 + pc.toNat + ac.toNat ≤ ns.toNat := by omega
  refine ⟨?_, h2⟩
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The locals of `ck_scan`. -/
def replay_scanEnv (sb : Nat) (base ns p hdr pc ac cnt na bad gpos g : BitVec 32) (f l : Val)
    (k i q : BitVec 32) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("base", .u32, .u32 base), ("ns", .u32, .u32 ns),
    ("p", .u32, .u32 p), ("hdr", .u32, .u32 hdr), ("pc", .u32, .u32 pc), ("ac", .u32, .u32 ac),
    ("cnt", .u32, .u32 cnt), ("nassume", .u32, .u32 na), ("bad", .u32, .u32 bad),
    ("gpos", .u32, .u32 gpos), ("g", .u32, .u32 g), ("f", Ty.u32.ptr, f), ("l", Ty.u32.ptr, l),
    ("k", .u32, .u32 k), ("i", .u32, .u32 i), ("q", .u32, .u32 q)]

theorem ck_scan_cost (sb A : Nat) (hA : 100 ≤ A) :
    FnCost (State := State) prog "ck_scan" (BudPre sb [.ptr sb 0]) (Amort sb A (allow 200) 0 noSlack) := by
  apply FnCost.intro (fn := ckScan) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckScan
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro base
  wpc_simp
  apply WPC.seq
  apply WPC.assign_u32 (by rfl)
  intro ns
  wpc_simp
  apply WPC.seq
  wpc_call
  cost_args
  name_bud st1 w1 mm1 hb1
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  have hAns : 100 * ns.toNat ≤ A * ns.toNat := Nat.mul_le_mul_right _ hA
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st1 ∧ ∃ p hdr pc ac cnt na bad gpos g : BitVec 32,
      env' = replay_scanEnv sb base ns p hdr pc ac cnt na bad gpos g .null .null 0 0 0 ∧
      cnt.toNat ≤ p.toNat ∧ p.toNat ≤ ns.toNat ∧ k.t ≤ 50 * p.toNat ∧ k.m = 0)
    (μ := fun env' _ => ns.toNat - envU32 env' "p")
  · exact ⟨rfl, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, _, rfl, by simp, by simp, by simp, by simp⟩
  rintro env' st' k ⟨rfl, p, hdr, pc, ac, cnt, na, bad, gpos, g, rfl, hcp, hpn, hk, hkm⟩
  simp only [replay_scanEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt' : p.toNat < ns.toNat := by simpa [BitVec.lt_def] using hlt
    apply WPC.seq; apply WPC.assign_u32 (by rfl); intro hdr'; wpc_simp
    apply WPC.seq; apply WPC.assign_band (by rfl); intro pc' hpc; wpc_simp
    apply WPC.seq; refine WPC.assign_shr (by rfl) ?_; intro ac' hac; wpc_simp
    apply WPC.seq; apply WPC.ite; embc_simp
    constructor
    · intro _
      wpc_auto
      wpc_done
    intro hle
    have hs := replay_scan_step hlt' (by simpa using hpc) (by simpa using hac) hle
    have hc1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    apply WPC.skip
    wpc_simp
    obtain ⟨hs1, hs2⟩ := hs
    wpc_auto
    wpc_done
    all_goals loop_next hs1
  have hpe : p.toNat = ns.toNat := by have := BitVec.le_def.mp hge; omega
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_call; cost_args
  name_bud st2 w2 mm2 hb2
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb2 (by decide) (by decide); intro m3 hb3; wpc_simp
  apply WPC.charge_mem (k := cnt) hb3 (by rfl) (by simp [evalE, Env.get])
  · intro m' hb'
    wpc_finish
  intro hlem m4 hb4
  have hm4 : (mm2 - cnt).toNat = mm2.toNat - cnt.toNat := bv_sub_toNat_of_le hlem
  have hlem' : cnt.toNat ≤ mm2.toNat := BitVec.le_def.mp hlem
  have hcost : Ext.costC prog (.kvcalloc .u32) [.u64 (cnt.setWidth 64)] = ⟨2 * cnt.toNat, cnt.toNat⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]; have := cnt.isLt; omega
  apply WPC.seq
  apply WPC.ecall_bud hb4
  intro vs hvs
  simp [evalArgs, evalE, evalCast, Env.get] at hvs
  subst hvs
  refine ⟨by simp, ?_⟩
  intro rv st5 hb5
  rw [hcost]
  cases rv with
  | none => simp [assignDst]
  | some f =>
  simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
  by_cases hty : st5.mem.hasTy f (.ptr .u32) = true
  case neg => simp [hty]
  simp only [hty, ↓reduceIte, Env.set, String.reduceEq]
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb5 (by decide) (by decide); intro m6 hb6; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb6 (by decide) (by decide); intro m7 hb7; wpc_simp
  -- the last-use table: paid from the memory budget like the fact array
  apply WPC.charge_mem (k := cnt) hb7 (by rfl) (by simp [evalE, Env.get])
  · intro m' hb'
    wpc_finish
  intro hlem2 m8 hb8
  have hm8 : (mm2 - cnt - cnt).toNat = mm2.toNat - cnt.toNat - cnt.toNat := by
    rw [bv_sub_toNat_of_le hlem2, hm4]
  have hlem2' : cnt.toNat ≤ (mm2 - cnt).toNat := BitVec.le_def.mp hlem2
  apply WPC.seq
  apply WPC.ecall_bud hb8
  intro vs hvs
  simp [evalArgs, evalE, evalCast, Env.get] at hvs
  subst hvs
  refine ⟨by simp, ?_⟩
  intro rv st9 hb9
  rw [hcost]
  cases rv with
  | none => simp [assignDst]
  | some l =>
  simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
  by_cases htl : st9.mem.hasTy l (.ptr .u32) = true
  case neg => simp [htl]
  simp only [htl, ↓reduceIte, Env.set, String.reduceEq]
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb9 (by decide) (by decide); intro m10 hb10; wpc_simp
  -- the second pass: paid by a second `spend(st, ns)`
  apply WPC.seq; wpc_call; cost_args
  name_bud st11 w11 mm11 hb11
  apply WPC.seq
  wpc_ite_case
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ p hdr pc ac g kk i q : BitVec 32,
      env' = replay_scanEnv sb base ns p hdr pc ac cnt na bad gpos g f l kk i q ∧
      p.toNat ≤ ns.toNat ∧ Budget st'.mem sb w11 mm11 ∧ k.t ≤ 40 * p.toNat ∧ k.m = 0)
    (μ := fun env' _ => ns.toNat - envU32 env' "p")
  · exact ⟨0#32, _, _, _, _, _, _, _, rfl, by simp, hb11, by simp, by simp⟩
  rintro env' st' k ⟨p2, hdr2, pc2, ac2, g2, kk, i2, q2, rfl, hpn2, hb', hk2, hkm2⟩
  simp only [replay_scanEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt' : p2.toNat < ns.toNat := by simpa [BitVec.lt_def] using hlt
    apply WPC.seq; apply WPC.assign_u32 (by rfl); intro hdr'; wpc_simp
    apply WPC.seq; apply WPC.assign_band (by rfl); intro pc' hpc; wpc_simp
    apply WPC.seq; refine WPC.assign_shr (by rfl) ?_; intro ac' hac; wpc_simp
    have hpc' : pc'.toNat ≤ 255 := by simpa using hpc
    apply WPC.seq; apply WPC.ite; embc_simp
    constructor
    · intro _
      wpc_auto
      wpc_done
    intro hle
    obtain ⟨hs1, hs2⟩ := replay_scan_step hlt' hpc' (by simpa using hac) hle
    apply WPC.skip
    wpc_simp
    apply WPC.seq
    apply WPC.ite_any
    · apply WPC.seq; wpc_step
      -- the premises of one step: at most 255
      apply WPC.while
        (I := fun env5 st5 k5 => ∃ i5 q5 : BitVec 32,
          env5 = replay_scanEnv sb base ns p2 hdr' pc' ac' cnt na bad gpos g2 f l kk i5 q5 ∧
          i5.toNat ≤ pc'.toNat ∧ Budget st5.mem sb w11 mm11 ∧ k5.t ≤ 12 * i5.toNat ∧ k5.m = 0)
        (μ := fun env5 _ => pc'.toNat - envU32 env5 "i")
      · exact ⟨0#32, _, rfl, by simp, hb', by simp, by simp⟩
      rintro env5 st5 k5 ⟨i5, q5, rfl, hip, hb5', hk5, hkm5⟩
      simp only [replay_scanEnv]
      embc_simp
      refine ⟨fun hge5 => ?_, fun hlt5 => ?_⟩
      · have := BitVec.le_def.mp hge5
        wpc_auto
        wpc_done
        all_goals loop_nextB hs1
      have hlt5' : i5.toNat < pc'.toNat := by simpa [BitVec.lt_def] using hlt5
      have hi1 : (i5 + 1#32).toNat = i5.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      wpc_auto
      wpc_done
      all_goals loop_nextB hi1
    apply WPC.skip; wpc_simp
    wpc_auto
    wpc_done
    all_goals loop_nextB hs1
  have hpe2 : p2.toNat = ns.toNat := by have := BitVec.le_def.mp hge; omega
  wpc_auto
  wpc_done

fncost_register "ck_scan" ckScan ck_scan_cost

/-- The locals of `ck_goal`. -/
def replay_goalEnv (sb gb : Nat) (goal n base sbase j q m ci ah ph code vlen k a pa pv ok : BitVec 32) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("gx", Ty.u32.ptr, .ptr gb 0), ("goal", .u32, .u32 goal),
    ("n", .u32, .u32 n), ("base", .u32, .u32 base), ("sbase", .u32, .u32 sbase), ("j", .u32, .u32 j),
    ("q", .u32, .u32 q), ("m", .u32, .u32 m), ("ci", .u32, .u32 ci), ("ah", .u32, .u32 ah),
    ("ph", .u32, .u32 ph), ("code", .u32, .u32 code), ("vlen", .u32, .u32 vlen), ("k", .u32, .u32 k),
    ("a", .u32, .u32 a), ("pa", .u32, .u32 pa), ("pv", .u32, .u32 pv), ("ok", .u32, .u32 ok)]

theorem ck_goal_cost (sb A : Nat) (hA : 100 ≤ A) (gb : Nat) (goal : BitVec 32) :
    FnCost (State := State) prog "ck_goal" (BudPre sb [.ptr sb 0, .ptr gb 0, .u32 goal])
      (Amort sb A (allow (7850 * goal.toNat + 8100)) 0 noSlack) := by
  apply FnCost.intro (fn := ckGoal) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckGoal
  have hA6 : 6 ≤ A := by omega
  by_cases hgx : st.mem.hasTy (.ptr gb 0) (.ptr .u32) = true
  rotate_left
  · simp [hgx]
  simp only [hgx, ↓reduceIte, List.cons_append, List.nil_append]
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.assign_u32 (by rfl); intro n; wpc_simp
  apply WPC.seq; wpc_call; cost_args
  name_bud st1 w1 mm1 hb1
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_call; cost_args
  name_bud st2 w2 mm2 hb2
  apply WPC.seq
  wpc_ite_case
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.assign_u32 (by rfl); intro base; wpc_simp
  apply WPC.seq; apply WPC.assign_u32 (by rfl); intro sbase; wpc_simp
  have hAn : 100 * n.toNat ≤ A * n.toNat := Nat.mul_le_mul_right _ hA
  -- the zeroing loop: paid by `spend`'s slack
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ j ok : BitVec 32,
      env' = replay_goalEnv sb gb goal n base sbase j 0 0 0 0 0 0 0 0 0 0 0 ok ∧
      j.toNat ≤ n.toNat ∧ Budget st'.mem sb w2 mm2 ∧ k.t ≤ 10 * j.toNat ∧ k.m = 0)
    (μ := fun env' _ => n.toNat - envU32 env' "j")
  · exact ⟨0#32, _, rfl, by simp, hb2, by simp, by simp⟩
  rintro env' st' k ⟨j, ok, rfl, hjn, hb', hk, hkm⟩
  simp only [replay_goalEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt' : j.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    loop_nextB hj1
  have hjn' : j.toNat = n.toNat := by have := BitVec.le_def.mp hge; omega
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  have hg1 : (goal + 1#32).toNat ≤ goal.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  have hG : (goal + 1#32).toNat = (goal.toNat + 1) % 4294967296 := by simp [BitVec.toNat_add]
  -- the sweep from `goal` down to 0
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ j q m ci ah ph code vlen kk a pa pv ok : BitVec 32,
      env' = replay_goalEnv sb gb goal n base sbase j q m ci ah ph code vlen kk a pa pv ok ∧
      q.toNat ≤ (goal + 1#32).toNat ∧ Budget st'.mem sb w2 mm2 ∧
      k.t + 7850 * q.toNat ≤ 7850 * (goal + 1#32).toNat ∧ k.m = 0)
    (μ := fun env' _ => envU32 env' "q")
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp, ‹Budget _ _ _ _›, by simp, by simp⟩
  rintro env' st' k ⟨j, q, m, ci, ah, ph, code, vlen, kk, a, pa, pv, ok, rfl, hqg, hb', hk, hkm⟩
  simp only [replay_goalEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hq0 : q ≠ 0#32 := by intro h; subst h; simp at hlt
    have hq1 := bv_sub_one_toNat hq0
    have hq2 := bv_pos_of_ne hq0
    wpc_auto
    wpc_done
    all_goals (try (loop_nextB hq1))
    · -- `BV_VAL`: compare the words
      rename_i m' ah' ph' vl hvl
      apply WPC.while
        (I := fun env' st'' k' => ∃ kk : BitVec 32,
          env' = replay_goalEnv sb gb goal n base sbase j (q - 1#32) m' (m' - 1#32) ah' ph' (ph' &&& 255#32)
            vl kk a pa pv ok ∧
          kk.toNat ≤ vl.toNat ∧ Budget st''.mem sb w2 mm2 ∧ k'.t ≤ 10 * kk.toNat ∧ k'.m = 0)
        (μ := fun env' _ => vl.toNat - envU32 env' "k")
      · exact ⟨0#32, rfl, by simp, hb', by simp, by simp⟩
      rintro env'' st'' k' ⟨kk, rfl, hkv, hb'', hk', hkm'⟩
      simp only [replay_goalEnv]
      embc_simp
      refine ⟨fun hge => ?_, fun hlt => ?_⟩
      · loop_nextB hq1
      have hlt' : kk.toNat < vl.toNat := by simpa [BitVec.lt_def] using hlt
      have hk1 : (kk + 1#32).toNat = kk.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      wpc_auto
      wpc_done
      all_goals loop_nextB hk1
    · -- the arguments: mark them
      rename_i m' ah' ph' vl hvl
      apply WPC.while
        (I := fun env' st'' k' => ∃ kk a' pa' m'' : BitVec 32,
          env' = replay_goalEnv sb gb goal n base sbase j (q - 1#32) m'' (m' - 1#32) ah' ph' (ph' &&& 255#32)
            vl kk a' pa' pv ok ∧
          kk.toNat ≤ vl.toNat ∧ Budget st''.mem sb w2 mm2 ∧ k'.t ≤ 30 * kk.toNat ∧ k'.m = 0)
        (μ := fun env' _ => vl.toNat - envU32 env' "k")
      · exact ⟨0#32, _, _, _, rfl, by simp, hb', by simp, by simp⟩
      rintro env'' st'' k' ⟨kk, a', pa', m'', rfl, hkv, hb'', hk', hkm'⟩
      simp only [replay_goalEnv]
      embc_simp
      refine ⟨fun hge => ?_, fun hlt => ?_⟩
      · loop_nextB hq1
      have hlt' : kk.toNat < vl.toNat := by simpa [BitVec.lt_def] using hlt
      have hk1 : (kk + 1#32).toNat = kk.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      wpc_auto
      wpc_done
      all_goals loop_nextB hk1
  wpc_auto
  wpc_done

fncost_register "ck_goal" ckGoal ck_goal_cost

/-- The locals of `ck_load`. -/
def replay_loadEnv (sb pb : Nat) (nwords ne ns p hdr code vlen i a id ok : BitVec 32) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("proof", Ty.u32.ptr, .ptr pb 0), ("nwords", .u32, .u32 nwords),
    ("ne", .u32, .u32 ne), ("ns", .u32, .u32 ns), ("p", .u32, .u32 p), ("hdr", .u32, .u32 hdr),
    ("code", .u32, .u32 code), ("vlen", .u32, .u32 vlen), ("i", .u32, .u32 i), ("a", .u32, .u32 a),
    ("id", .u32, .u32 id), ("ok", .u32, .u32 ok)]

/-- `(u64)ne + (u64)ns + 3 == (u64)nwords`, as numbers. -/
theorem replay_load_sizes {ne ns nwords : BitVec 32}
    (h : ne.setWidth 64 + ns.setWidth 64 + 3#64 = nwords.setWidth 64) :
    ne.toNat + ns.toNat + 3 = nwords.toNat := by
  have := congrArg BitVec.toNat h
  have h1 := ne.isLt
  have h2 := ns.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  omega

/-- One step of `ck_load`'s loop: `p + 1 + vlen` does not wrap and stays within `ne`. -/
theorem replay_load_step {p ne vlen : BitVec 32} (hlt : p.toNat < ne.toNat) (hv : vlen.toNat ≤ 255)
    (hle : vlen ≤ ne - p - 1#32) :
    (p + 1#32 + vlen).toNat = p.toNat + 1 + vlen.toNat ∧ p.toNat + 1 + vlen.toNat ≤ ne.toNat := by
  have hn := ne.isLt
  rw [BitVec.le_def, BitVec.toNat_sub, BitVec.toNat_sub] at hle
  simp only [BitVec.toNat_ofNat] at hle
  have h2 : p.toNat + 1 + vlen.toNat ≤ ne.toNat := by omega
  refine ⟨?_, h2⟩
  rw [BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem ck_load_cost (sb A : Nat) (hA : 100 ≤ A) (pb : Nat) (nwords : BitVec 32) :
    FnCost (State := State) prog "ck_load" (BudPre sb [.ptr sb 0, .ptr pb 0, .u32 nwords])
      (Amort sb A (allow (16000 * nwords.toNat + 100)) 0 noSlack) := by
  apply FnCost.intro (fn := ckLoad) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckLoad
  have hA6 : 6 ≤ A := by omega
  by_cases hpf : st.mem.hasTy (.ptr pb 0) (.ptr .u32) = true
  rotate_left
  · simp [hpf]
  simp only [hpf, ↓reduceIte, List.cons_append, List.nil_append]
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.assign_u32 (by rfl); intro ne; wpc_simp
  apply WPC.seq; apply WPC.assign_u32 (by rfl); intro ns; wpc_simp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.ite
  embc_simp
  constructor
  · intro _
    wpc_auto; wpc_done
  intro heq
  have hsz := replay_load_sizes heq
  clear heq
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ p hdr code vlen i a id ok : BitVec 32,
      env' = replay_loadEnv sb pb nwords ne ns p hdr code vlen i a id ok ∧ p.toNat ≤ ne.toNat ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat + 16000 * p.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => ne.toNat - envU32 env' "p")
  · exact ⟨0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, rfl, by simp, w, mm, ‹Budget _ _ _ _›,
      by simp, by simp⟩
  rintro env' st' k ⟨p, hdr, code, vlen, i, a, id, ok, rfl, hpn, w', mm', hb', hk, hkm⟩
  simp only [replay_loadEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt' : p.toNat < ne.toNat := by simpa [BitVec.lt_def] using hlt
    apply WPC.seq; apply WPC.assign_u32 (by rfl); intro hdr'; wpc_simp
    apply WPC.seq; apply WPC.assign_band (by rfl); intro code' hcode; wpc_simp
    apply WPC.seq; apply WPC.assign_band (by rfl); intro vl hvl; wpc_simp
    have hvl' : vl.toNat ≤ 255 := by simpa using hvl
    apply WPC.seq; apply WPC.ite; embc_simp
    constructor
    · intro _; wpc_auto; wpc_done
    intro hle
    obtain ⟨hs1, hs2⟩ := replay_load_step hlt' hvl' hle
    apply WPC.skip; wpc_simp
    apply WPC.seq; wpc_call; cost_args
    name_bud st3 w3 mm3 hb3
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; wpc_done
    apply WPC.skip; wpc_simp
    -- the node's three cases join before `ck_intern`
    apply WPC.seq_join (J := fun env'' st'' k' => ∃ i' a' ok' : BitVec 32,
      env'' = replay_loadEnv sb pb nwords ne ns p hdr' code' vl i' a' id ok' ∧
      Budget st''.mem sb w3 mm3 ∧ k'.t ≤ 20 * vl.toNat + 40 ∧ k'.m = 0)
    · wpc_auto
      wpc_done
      · exact ⟨_, _, _, rfl, ‹Budget _ _ _ _›, by cost_arith, by cost_simp⟩
      all_goals
        apply WPC.while
          (I := fun env5 st5 k5 => ∃ i5 a5 ok5 : BitVec 32,
            env5 = replay_loadEnv sb pb nwords ne ns p hdr' code' vl i5 a5 id ok5 ∧ i5.toNat ≤ vl.toNat ∧
            Budget st5.mem sb w3 mm3 ∧ k5.t ≤ 20 * i5.toNat ∧ k5.m = 0)
          (μ := fun env5 _ => vl.toNat - envU32 env5 "i")
        · refine ⟨0#32, _, _, rfl, ?_, ‹Budget _ _ _ _›, ?_⟩ <;> simp
        rintro env5 st5 k5 ⟨i5, a5, ok5, rfl, hiv, hb5, hk5, hkm5⟩
        simp only [replay_loadEnv]
        embc_simp
        refine ⟨fun hge => ?_, fun hlt => ?_⟩
        · exact ⟨hb5, by have := BitVec.le_def.mp hge; omega, hkm5⟩
        have hlt5 : i5.toNat < vl.toNat := by simpa [BitVec.lt_def] using hlt
        have hi1 : (i5 + 1#32).toNat = i5.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
        wpc_auto
        wpc_done
        all_goals loop_nextB hi1
    rintro env4 st4 k4 ⟨i4, a4, ok4, rfl, hb4, hk4, hkm4⟩
    simp only [replay_loadEnv]
    apply WPC.seq; wpc_call
    name_bud st6 w6 mm6 hb6
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; wpc_done
    apply WPC.skip; wpc_simp
    apply WPC.seq; wpc_step
    apply WPC.seq; wpc_step
    -- clear the expression's argument words
    apply WPC.seq
    apply WPC.while
      (I := fun env7 st7 k7 => ∃ i7 id7 : BitVec 32,
        env7 = replay_loadEnv sb pb nwords ne ns p hdr' code' vl i7 a4 id7 ok4 ∧ i7.toNat ≤ vl.toNat ∧
        Budget st7.mem sb w6 mm6 ∧ k7.t ≤ 10 * i7.toNat ∧ k7.m = 0)
      (μ := fun env7 _ => vl.toNat - envU32 env7 "i")
    · refine ⟨0#32, _, rfl, ?_, ‹Budget _ _ _ _›, ?_⟩ <;> simp
    rintro env7 st7 k7 ⟨i7, id7, rfl, hiv7, hb7, hk7, hkm7⟩
    simp only [replay_loadEnv]
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · have := BitVec.le_def.mp hge
      apply WPC.assign
      embc_simp
      simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hs1]
      refine ⟨by omega, by omega, _, _, hb7, ?_, ?_⟩ <;> cost_arith
    have hlt7 : i7.toNat < vl.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i7 + 1#32).toNat = i7.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_nextB hi1
  have := BitVec.le_def.mp hge
  wpc_auto
  wpc_done

fncost_register "ck_load" ckLoad ck_load_cost

end Vbcf.Proof
