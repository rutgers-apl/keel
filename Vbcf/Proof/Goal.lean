import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Goal6

/-!
# Vbcf proofs: `ck_goal`

`ck_goal_spec : GoalSpec`.  The parts:

* `Goal1`: bit lemmas, `GLocal` monotonicity and introduction rules;
* `Goal2`: the sweep invariant `SweepOK` and its transitions (pure);
* `Goal3`: frames, arena reads, the local environment, `MInv`;
* `Goal4`: the variable branch and the literal comparison loop;
* `Goal5`: the argument loop;
* `Goal6`: one position of the sweep;
* here: the prologue (`ck_room`, zeroing the tables, marking the root), the sweep loop,
  and the result.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC Vbcf
set_option autoImplicit false

section
variable {W : World} {sb : Nat} {c c1 c2 : CMem} {X : Ctx} {st : St} {gws : Array (BitVec 32)}
  {goal : BitVec 32} {s : (KernelState prog State)} {env : Env}

/-- Returning 0 after the pool has only been grown and its tail written. -/
theorem goal_ret0 (hinv : RInv0 W X c st) (hf1 : PoolFrame c c1) (hc1 : CoreInv X.posOf c1 st)
    (h : Holds W s.mem sb c2) (ht : TailEq c1 c2) :
    retPost (some .u32) (GoalPost W sb c X st gws goal) (.ret (some (.u32 0#32))) env s := by
  refine ⟨rfl, c2, 0#32, rfl, h, ?_, ?_, fun e => absurd rfl e⟩
  · exact hinv.goalFrame h (hf1.trans ht.poolFrame) (hc1.tailEq ht)
  · exact StepFrame.ofPoolFrame (hf1.trans ht.poolFrame)

end

/-- The work counter and error flag may change under a `PoolFrame`. -/
theorem PoolFrame.wev (c : CMem) (wk er : BitVec 32) : PoolFrame c (c.wev wk er c.k.val) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

/-- Invariant of the loop that zeroes the tables. -/
def ZInv (W : World) (sb gb : Nat) (c1 : CMem) (goal nv sbv : BitVec 32) : Env → (KernelState prog State) → Prop :=
  fun env s => ∃ (c2 : CMem) (j : BitVec 32),
    env = genv sb gb goal nv c1.k.plen sbv j 0#32 0#32 0#32 0#32 0#32 0#32 0#32 0#32 0#32 0#32 0#32
      1#32 ∧
    j.toNat ≤ nv.toNat ∧ Holds W s.mem sb c2 ∧ TailEq c1 c2 ∧
    ∀ t, t < j.toNat → U c2.pool (c1.k.plen.toNat + t) 0

theorem ck_goal_spec : GoalSpec (State := State) := by
  intro W sb c X st gb gws goal
  show FnSpec (State := State) Vbcf.prog "ck_goal" _ (fun _ _ => GoalPost W sb c X st gws goal)
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckGoal) rfl
  rintro vs s ⟨rfl, h, hinv, ha⟩
  simp [ckGoal, bindParams, Mem.hasTy_ptr h.ck rfl, Mem.hasTy_ptr (h.arena ha) rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hglt := goal.isLt
  have hnelt := c.k.nexpr.isLt
  have h64 : (BitVec.setWidth 64 goal + 1#64 + BitVec.setWidth 64 c.k.nexpr).toNat =
      goal.toNat + 1 + c.k.nexpr.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    simp; omega
  -- if ((u64)goal + 1 + (u64)st->nexpr > MAX_POOL) { st->err = ERR_LIMIT; return 0; }
  apply WP.seq
  apply WP.ite
  ck_simp
  refine ⟨fun hbig => ?_, fun hsmall => ?_⟩
  · apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s' h'
    apply WP.ret
    ck_simp
    have hf := PoolFrame.setErr c 2#32
    exact ⟨rfl, _, 0#32, rfl, h', hinv.goalFrame h' hf (hinv.core.setErr _), StepFrame.ofPoolFrame hf,
      fun e => absurd rfl e⟩
  apply WP.skip
  have hsm : goal.toNat + 1 + c.k.nexpr.toNat ≤ 2 ^ 30 := by
    rw [BitVec.le_def, h64] at hsmall; simpa using hsmall
  -- n = goal + 1 + st->nexpr;
  apply WP.assign_seq
  ck_simp
  have hnv : (goal + 1#32 + c.k.nexpr).toNat = goal.toNat + 1 + c.k.nexpr.toNat := by
    rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
  generalize goal + 1#32 + c.k.nexpr = nv at hnv
  -- ok = ck_room(st, n);
  apply WP.call_seq (ck_room_spec W sb c X.posOf st nv) (by ck_simp) ⟨rfl, h, hinv.core⟩
  rintro rv s1 ⟨c1, h1, hf1, hc1, hpl, hres⟩
  clear h
  have h := h1
  clear h1
  rcases hres with rfl | ⟨rfl, hroom⟩
  · ck_simp
    apply WP.ifRet
    ck_simp
    exact goal_ret0 hinv hf1 hc1 h (TailEq.refl c1)
  ck_simp
  apply WP.ifRet
  ck_simp
  rw [← hpl] at hroom
  have hpc := hc1.poolCap
  simp only [maxPool] at hpc
  obtain ⟨pb, hpool1⟩ := hc1.poolPtr_of_pcap h (by have := hinv.goal.1; omega)
  have hpsz := hc1.poolSize pb 0 hpool1
  -- ok = spend(st, n); if (ok == 0) { return 0; }
  apply WP.call_seq (spend_spec W sb c1 nv) (by ck_simp) ⟨rfl, h⟩
  rintro rv s2 ⟨rfl, h2⟩
  rw [spendM_wev] at h2
  ck_simp
  apply WP.ifRet
  ck_simp
  refine ⟨fun _ => ?_, fun hnz => ?_⟩
  · exact goal_ret0 hinv (hf1.trans (PoolFrame.wev _ _ _)) hc1.wev h2 (TailEq.refl _)
  obtain h1 : (spendM c1 nv).1 = 1#32 := (spendM_fst c1 nv).resolve_left hnz
  rw [h1]
  generalize (spendM c1 nv).2.k.work = wk at h2
  generalize (spendM c1 nv).2.k.err = er at h2
  have hf1' : PoolFrame c (c1.wev wk er c1.k.val) := hf1.trans (PoolFrame.wev c1 wk er)
  have hc1' : CoreInv X.posOf (c1.wev wk er c1.k.val) st := hc1.wev
  have hpool1' : (c1.wev wk er c1.k.val).k.pool = some (pb, 0) := hpool1
  have hroom' : (c1.wev wk er c1.k.val).k.plen.toNat + nv.toNat ≤
      (c1.wev wk er c1.k.val).k.pcap.toNat := hroom
  clear hf1 hc1 hpool1 hpsz hroom hpc h hpl
  generalize c1.wev wk er c1.k.val = c1 at h2 hf1' hc1' hpool1' hroom'
  have h := h2
  have hf1 := hf1'
  have hc1 := hc1'
  have hpool1 := hpool1'
  have hroom := hroom'
  clear h2 hf1' hc1' hpool1' hroom'
  have hpc := hc1.poolCap
  simp only [maxPool] at hpc
  have hpsz := hc1.poolSize pb 0 hpool1
  -- base = st->plen; sbase = base + goal + 1;
  apply WP.assign_seq
  ck_simp
  apply WP.assign_seq
  ck_simp
  have hsbv : (c1.k.plen + goal + 1#32).toNat = c1.k.plen.toNat + goal.toNat + 1 := by
    rw [bv_add_toNat, bv_add_toNat]
    all_goals (try simp)
    all_goals omega
  generalize c1.k.plen + goal + 1#32 = sbv at hsbv
  -- while (j < n) { st->pool[base + j] = 0; j = j + 1; }
  apply WP.loop_seq (ZInv W sb gb c1 goal nv sbv)
  · exact ⟨c1, 0#32, rfl, by simp, h, TailEq.refl c1, fun t ht => by simp at ht⟩
  clear h
  rintro env s ⟨c2, jj, rfl, hjle, h, ht, hz⟩
  have hk := ht.k
  have hpool2 : c2.k.pool = some (pb, 0) := by rw [hk]; exact hpool1
  ck_simp [genv]
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hj : jj.toNat < nv.toNat := by rw [BitVec.lt_def] at hlt; omega
    have hidx : (c1.k.plen + jj).toNat = c1.k.plen.toNat + jj.toNat := by
      rw [bv_add_toNat]; omega
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool2
    ck_simp [genv, hpool2, hidx]
    refine ⟨by rw [ht.size]; omega, fun s' h' => ?_⟩
    apply WP.assign
    ck_simp [genv]
    have hj1 : (jj + 1#32).toNat = jj.toNat + 1 := by rw [bv_add_toNat] <;> simp <;> omega
    refine ⟨_, jj + 1#32, rfl, by omega, h', ht.trans (TailEq.wr (by rw [hk]; omega)), ?_⟩
    intro t htl
    rw [hj1] at htl
    rcases Nat.lt_or_ge t jj.toNat with e | e
    · exact U_set_ne (hz t e) (by omega)
    · have : t = jj.toNat := by omega
      subst this
      exact U_set_self (by rw [ht.size]; omega) rfl
  have hjn : jj.toNat = nv.toNat := by rw [BitVec.le_def] at hge; omega
  rw [hjn] at hz
  obtain rfl : nv = jj := (BitVec.eq_of_toNat_eq hjn).symm
  have hne1 : c1.k.nexpr.toNat = c.k.nexpr.toNat := by rw [hf1.nexpr]
  have hgf : c1.k.goal.toNat = offs st.pool X.goal := by rw [hf1.goal]; exact hinv.goal.2
  have hgi := hinv.goal.1
  have hgoff := hc1.off_lt hgi
  have hF : GFacts W sb gb pb c1 X st gws goal nv sbv :=
    { core := hc1, pool := hpool1, psize := hpsz, room := hroom, nv := by rw [hf1.nexpr]; exact hnv, sbv := hsbv, arena := ha,
      gidx := hgi, gfield := hgf }
  -- st->pool[base + goal] = st->goal + 1;
  have hidx : (c1.k.plen + goal).toNat = c1.k.plen.toNat + goal.toNat := by
    rw [bv_add_toNat]; omega
  have hg1 : c1.k.goal + 1#32 = BitVec.ofNat 32 (offs st.pool X.goal + 1) :=
    bv_add_one_ofNat hgf (by omega)
  have hg2 : c2.k.goal + 1#32 = BitVec.ofNat 32 (offs st.pool X.goal + 1) := by rw [hk]; exact hg1
  apply WP.seq
  apply WP.ck_store .pool h (by rfl) hpool2
  ck_simp [genv, hpool2, hidx, hg2]
  refine ⟨by rw [ht.size]; omega, fun s' h' => ?_⟩
  clear h
  have h := h'
  clear h'
  have ht' : TailEq c1 _ := ht.trans (TailEq.wr (c := c2) (i := c1.k.plen.toNat + goal.toNat)
    (x := BitVec.ofNat 32 (offs st.pool X.goal + 1)) (by rw [hk]; omega))
  -- q = goal + 1;
  apply WP.assign_seq
  ck_simp [genv]
  have hq0 : (goal + 1#32).toNat = goal.toNat + 1 := by rw [bv_add_toNat] <;> simp <;> omega
  -- the sweep
  apply WP.loop_seq (MInv W sb gb c1 X st gws goal nv sbv)
  · refine ⟨_, goal + 1#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32,
      fun t => if t = goal.toNat then some X.goal else none, fun _ => none, rfl,
      by omega, h, ht', ?_⟩
    rw [hq0]
    apply SweepOK.init hgi ?_ ?_ ?_
    · exact ha.fits
    · intro t htn hne
      exact U_set_ne (hz t (by omega)) (by omega)
    · exact U_set_self (by rw [ht.size]; omega) rfl
  clear h ht ht' hz
  rintro env s ⟨c2, q, m, ci, ah, ph, code, vlen, k, a, pa, pv, μ, σP, rfl, hqle, h, ht, hsw⟩
  ck_simp [genv]
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · subst hq
    apply WP.ret
    ck_simp
    have hfr := hf1.trans ht.poolFrame
    exact ⟨rfl, c2, 1#32, rfl, h, hinv.goalFrame h hfr (hc1.tailEq ht), StepFrame.ofPoolFrame hfr,
      fun _ => by simpa using hsw.goalOK⟩
  have hqpos : 0 < q.toNat := by
    rcases Nat.eq_zero_or_pos q.toNat with e | e
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using e)) hq
    · exact e
  exact goal_body_wp hF
    (Q := LoopQ (MInv W sb gb c1 X st gws goal nv sbv) (retPost (some .u32) (GoalPost W sb c X st gws goal)))
    (fun _ _ hI => hI) (fun env3 _ c3 h3 ht3 => goal_ret0 (env := env3) hinv hf1 hc1 h3 ht3)
    h ht hqpos hqle hsw

end Vbcf.Proof
