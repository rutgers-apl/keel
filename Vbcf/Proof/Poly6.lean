import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly5

/-!
# Vbcf proofs: the Poly family, part 6 — `lin_f`: subtraction and negation
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


section cases
variable {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {w i : Nat} {d : BitVec 32} {s : (KernelState prog State)}

/-- All argument indices of pool nodes are nodes. -/
theorem RCtx.pl_args (hR : RCtx W X c0 prems params c st) :
    ∀ (i : Nat) (n : Node), st.cs.pool[i]? = some n → ∀ a ∈ n.args, a < st.cs.pool.size :=
  fun _ _ hn a ha => (hR.core.cinv.ok.typed hn).args_lt a ha

/-- A subtraction. -/
theorem lfT2_sub (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → LinFSpecD (State := State) d') (hd : d ≠ 0#32)
    {w' a b : Nat} (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    (hi : i < st.cs.pool.size) (hn : st.cs.pool[i]? = some ⟨.bvSub w', #[a, b]⟩)
    (hf : Fits X.posOf ⟨.bvSub w', #[a, b]⟩) (hw1 : 1 ≤ w) (hw64 : w ≤ 64)
    (av bv mid i' ok : BitVec 32) (k : BitVec 64) :
    WP Vbcf.prog plT2 (RetQ (PlRet W sb X c0 prems params st c c.k.sp.toNat
        (plEnc st.cs.pool (Bcf.lin st.cs.pool w i))))
      (plFE sb w st i ⟨.bvSub w', #[a, b]⟩ d av bv c.k.sp mid i' ok k) s := by
  have hs := prog_ck
  have ha : a < st.cs.pool.size := hR.pl_args i _ hn a (by simp)
  have hb : b < st.cs.pool.size := hR.pl_args i _ hn b (by simp)
  have hrd := hR.core.cinv.rd2 hn (by simp [IsLeaf, isLeaf])
  have hlo := hf.lo
  simp only [opLo] at hlo
  have hoa := hR.core.cinv.off_lt ha
  have hob := hR.core.cinv.off_lt hb
  have hoi := hR.core.cinv.off_lt hi
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hm := mask64M_toNat hw1 hw64
  unfold plT2
  apply WP.ite_seq
  rule_simp [plFE, plFEnv, opC, tailLen]
  unfold plFSub
  simp only [Stmt.block]
  rule_assign [hrd]
  rule_assign [hrd]
  apply WP.ite
  rule_simp [opLo, opHi, offs_lt_iff (Nat.le_of_lt hi)]
  refine ⟨fun hc hca hcb => ?_, fun hc => ?_⟩
  rotate_left
  · apply WP.skip; simp only [LoopQ]
    have hlin : Bcf.lin st.cs.pool w i = Lin.atom i := by
      rw [pl_lin_sub hn, ite_eq_right (fun ⟨e1, e2, e3⟩ => by have := hc e1 e2; omega)]
    have := opC_lt32 (Op.bvSub w')
    apply lfT3_skip (by decide) (by decide) (by decide)
    apply lfT4_skip (by decide) (by decide) (by decide)
    exact lfT5_spec h hR hi hw1 hw64 hlin _ _ _ _ _ _ _ _ _ _ _
  have hlin : Bcf.lin st.cs.pool w i = Lin.add (Bcf.lin st.cs.pool w a) (Lin.neg (Bcf.lin st.cs.pool w b)) := by
    rw [pl_lin_sub hn, ite_eq_left ⟨hc, hca, hcb⟩]
  rw [hlin]
  have hokA := lin_ok (w := w) hR.pl_args ha
  have hokB := lin_ok (w := w) hR.pl_args hb
  -- `ok = lin_f(st, w, b, depth - 1);`
  apply WP.pl_call (IH _ (cv_dec_lt hd) W sb X c0 c prems params st w b) (by rule_simp)
    ⟨rfl, h, hR, hb, hw1, hw64⟩
  intro s1 r1 hr1
  clear h
  obtain ⟨c1, h, hR1, hpre1, hcase1⟩ := hr1
  rcases hcase1 with rfl | ⟨rfl, hw1'⟩
  · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR1, hpre1, Or.inl rfl⟩
  rule_simp; apply WP.ite_seq; rule_simp
  -- `if (st->sp < base || st->sp > MAX_POOL) { return 0; }`: a failure return
  apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR1, hpre1, Or.inl rfl⟩
  intro _
  -- `ok = spend(st, st->sp - base);`
  apply WP.rule_spend h hR1
  rule_simp
  intro s1' wk1 er1 ok1 h _
  have hR1 := hR1.wev (wk := wk1) (er := er1) (vl := c1.k.val)
  unfold PlStkW at hw1'
  rw [show c1.stk = (c1.wev wk1 er1 c1.k.val).stk from rfl] at hpre1
  rw [show c1.stk = (c1.wev wk1 er1 c1.k.val).stk from rfl] at hw1'
  rw [show c1.k.sp = (c1.wev wk1 er1 c1.k.val).k.sp from rfl] at hw1'
  generalize c1.wev wk1 er1 c1.k.val = c1 at h hR1 hpre1 hw1'
  have hw1' : PlStkW c1 _ _ := hw1'
  (try rule_simp); apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR1, hpre1, Or.inl rfl⟩
  -- `lin_scale(st, base, m, m);`
  apply WP.pl_scale h hR1 (kk := -1) hw1 hw64 hm (by rw [hm, pl_neg_one hw1]) hw1'
  refine ⟨by rule_simp, ?_⟩
  intro s2 c2 h2 hR2 hpre2 hst2
  clear h
  have h := h2
  have hsp2 := hst2.1
  -- `mid = st->sp;`
  rule_assign [show c2.k.sp = BitVec.ofNat 32 (c.k.sp.toNat + (plEnc st.cs.pool (Lin.scale (-1) (Bcf.lin st.cs.pool w b))).length) from by
    rw [← hsp2]; exact (bv_ofNat_toNat _).symm]
  -- `ok = lin_f(st, w, a, depth - 1);`
  apply WP.pl_call (IH _ (cv_dec_lt hd) W sb X c0 c2 prems params st w a) (by rule_simp)
    ⟨rfl, h, hR2, ha, hw1, hw64⟩
  intro s3 r3 hr3
  clear h
  obtain ⟨c3, h, hR3, hpre3, hcase3⟩ := hr3
  rcases hcase3 with rfl | ⟨rfl, hw3⟩
  · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c3, h, hR3, pl_pre_trans (by omega) hpre3 (pl_pre_trans (by omega) hpre2 hpre1),
      Or.inl rfl⟩
  rule_simp; apply WP.ite_seq; rule_simp
  -- `ok = lin_add(st, base, mid, m); return ok;`
  apply WP.pl_add h hR3 hw1 hw64 hm hokA (LinOK.negL hokB) (PlStkW.push_more hst2 hpre3 hw3)
  refine ⟨by rule_simp [Lin.neg], ?_⟩
  intro s4 r4 hr4
  rule_simp
  apply WP.rule_ret; rule_simp
  obtain ⟨c4, h4, hR4, hpre4, hcase4⟩ := hr4
  exact ⟨c4, h4, hR4, pl_pre_trans (Nat.le_refl _) hpre4 (pl_pre_trans (by omega) hpre3
    (pl_pre_trans (Nat.le_refl _) hpre2 hpre1)), hcase4⟩

/-- A negation. -/
theorem lfT3_neg (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → LinFSpecD (State := State) d') (hd : d ≠ 0#32)
    {w' a : Nat} (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    (hi : i < st.cs.pool.size) (hn : st.cs.pool[i]? = some ⟨.bvNeg w', #[a]⟩)
    (hf : Fits X.posOf ⟨.bvNeg w', #[a]⟩) (hw1 : 1 ≤ w) (hw64 : w ≤ 64)
    (av bv mid i' ok : BitVec 32) (k : BitVec 64) :
    WP Vbcf.prog plT3 (RetQ (PlRet W sb X c0 prems params st c c.k.sp.toNat
        (plEnc st.cs.pool (Bcf.lin st.cs.pool w i))))
      (plFE sb w st i ⟨.bvNeg w', #[a]⟩ d av bv c.k.sp mid i' ok k) s := by
  have hs := prog_ck
  have ha : a < st.cs.pool.size := hR.pl_args i _ hn a (by simp)
  have hrd := hR.core.cinv.rd1 hn (by simp [IsLeaf, isLeaf])
  have hlo := hf.lo
  simp only [opLo] at hlo
  have hoa := hR.core.cinv.off_lt ha
  have hoi := hR.core.cinv.off_lt hi
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hm := mask64M_toNat hw1 hw64
  unfold plT3
  apply WP.ite_seq
  rule_simp [plFE, plFEnv, opC, tailLen]
  unfold plFNeg
  simp only [Stmt.block]
  rule_assign [hrd]
  apply WP.ite
  rule_simp [opLo, opHi, offs_lt_iff (Nat.le_of_lt hi)]
  refine ⟨fun hc hca => ?_, fun hc => ?_⟩
  rotate_left
  · apply WP.skip; simp only [LoopQ]
    have hlin : Bcf.lin st.cs.pool w i = Lin.atom i := by
      rw [pl_lin_neg hn, ite_eq_right (fun ⟨e1, e2⟩ => by have := hc e1; omega)]
    apply lfT4_skip (by decide) (by decide) (by decide)
    exact lfT5_spec h hR hi hw1 hw64 hlin _ _ _ _ _ _ _ _ _ _ _
  have hlin : Bcf.lin st.cs.pool w i = Lin.neg (Bcf.lin st.cs.pool w a) := by
    rw [pl_lin_neg hn, ite_eq_left ⟨hc, hca⟩]
  rw [hlin]
  apply WP.pl_call (IH _ (cv_dec_lt hd) W sb X c0 c prems params st w a) (by rule_simp)
    ⟨rfl, h, hR, ha, hw1, hw64⟩
  intro s1 r1 hr1
  clear h
  obtain ⟨c1, h, hR1, hpre1, hcase1⟩ := hr1
  rcases hcase1 with rfl | ⟨rfl, hw1'⟩
  · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR1, hpre1, Or.inl rfl⟩
  rule_simp; apply WP.ite_seq; rule_simp
  -- `if (st->sp < base || st->sp > MAX_POOL) { return 0; }`: a failure return
  apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR1, hpre1, Or.inl rfl⟩
  intro _
  -- `ok = spend(st, st->sp - base);`
  apply WP.rule_spend h hR1
  rule_simp
  intro s1' wk1 er1 ok1 h _
  have hR1 := hR1.wev (wk := wk1) (er := er1) (vl := c1.k.val)
  unfold PlStkW at hw1'
  rw [show c1.stk = (c1.wev wk1 er1 c1.k.val).stk from rfl] at hpre1
  rw [show c1.stk = (c1.wev wk1 er1 c1.k.val).stk from rfl] at hw1'
  rw [show c1.k.sp = (c1.wev wk1 er1 c1.k.val).k.sp from rfl] at hw1'
  generalize c1.wev wk1 er1 c1.k.val = c1 at h hR1 hpre1 hw1'
  have hw1' : PlStkW c1 _ _ := hw1'
  (try rule_simp); apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR1, hpre1, Or.inl rfl⟩
  apply WP.pl_scale h hR1 (kk := -1) hw1 hw64 hm (by rw [hm, pl_neg_one hw1]) hw1'
  refine ⟨by rule_simp, ?_⟩
  intro s2 c2 h2 hR2 hpre2 hst2
  apply WP.rule_ret; rule_simp [LoopQ]
  exact ⟨c2, h2, hR2, pl_pre_trans (Nat.le_refl _) hpre2 hpre1, Or.inr ⟨rfl, hst2⟩⟩

/-- A product of two arguments. -/
theorem lfT4_mul (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → LinFSpecD (State := State) d') (hd : d ≠ 0#32)
    {w' a b : Nat} (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    (hi : i < st.cs.pool.size) (hn : st.cs.pool[i]? = some ⟨.bvMul w', #[a, b]⟩)
    (hf : Fits X.posOf ⟨.bvMul w', #[a, b]⟩) (hw1 : 1 ≤ w) (hw64 : w ≤ 64)
    (av bv mid i' ok : BitVec 32) (k : BitVec 64) :
    WP Vbcf.prog plT4 (RetQ (PlRet W sb X c0 prems params st c c.k.sp.toNat
        (plEnc st.cs.pool (Bcf.lin st.cs.pool w i))))
      (plFE sb w st i ⟨.bvMul w', #[a, b]⟩ d av bv c.k.sp mid i' ok k) s := by
  have hs := prog_ck
  have ha : a < st.cs.pool.size := hR.pl_args i _ hn a (by simp)
  have hb : b < st.cs.pool.size := hR.pl_args i _ hn b (by simp)
  have hrd := hR.core.cinv.rd2 hn (by simp [IsLeaf, isLeaf])
  have hlo := hf.lo
  simp only [opLo] at hlo
  have hoa := hR.core.cinv.off_lt ha
  have hob := hR.core.cinv.off_lt hb
  have hoi := hR.core.cinv.off_lt hi
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hm := mask64M_toNat hw1 hw64
  unfold plT4
  apply WP.ite_seq
  rule_simp [plFE, plFEnv, opC, tailLen]
  unfold plFMul
  simp only [Stmt.block]
  rule_assign [hrd]
  rule_assign [hrd]
  apply WP.ite
  rule_simp [opLo, opHi, offs_lt_iff (Nat.le_of_lt hi)]
  refine ⟨fun hc hca hcb => ?_, fun hc => ?_⟩
  rotate_left
  · apply WP.skip; simp only [LoopQ]
    have hlin : Bcf.lin st.cs.pool w i = Lin.atom i :=
      pl_lin_mul_no hn (fun ⟨e1, e2, e3⟩ => by have := hc e1 e2; omega)
    exact lfT5_spec h hR hi hw1 hw64 hlin _ _ _ _ _ _ _ _ _ _ _
  have hcond : w' = w ∧ a < i ∧ b < i := ⟨hc, hca, hcb⟩
  -- `ok = poly_lit_val(st, w, a);`
  apply WP.call_seq (poly_lit_val_spec W sb X c0 c prems params st w a)
    (vs := [.ptr sb 0, uv w, uv (offs st.cs.pool a)]) (by rule_simp) ⟨rfl, h, hR, ha, by omega⟩
  rintro rv s1 ⟨r1, rfl, hr1⟩
  rcases hr1 with ⟨rfl, rfl, hnoneA⟩ | ⟨rfl, kk, vl, hsome, hvl, h1⟩
  rotate_left
  · -- the first argument is a literal
    rule_simp
    apply WP.ite_seq; rule_simp
    have hR1 := hR.wev (wk := c.k.work) (er := c.k.err) (vl := vl)
    clear h
    have h := h1
    rule_assign
    rw [pl_lin_mul_a hn hcond hsome]
    apply WP.pl_call (IH _ (cv_dec_lt hd) W sb X c0 _ prems params st w b) (by rule_simp)
      ⟨rfl, h, hR1, hb, hw1, hw64⟩
    intro s2 r2 hr2
    clear h
    obtain ⟨c2, h, hR2, hpre2, hcase2⟩ := hr2
    rcases hcase2 with rfl | ⟨rfl, hw2⟩
    · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c2, h, hR2, hpre2, Or.inl rfl⟩
    rule_simp; apply WP.ite_seq; rule_simp
    -- `if (st->sp < base || st->sp > MAX_POOL) { return 0; }`: a failure return
    apply WP.ite_seq; rule_simp
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c2, h, hR2, hpre2, Or.inl rfl⟩
    intro _
    -- `ok = spend(st, st->sp - base);`
    apply WP.rule_spend h hR2
    rule_simp
    intro s2' wk2 er2 ok2 h _
    have hR2 := hR2.wev (wk := wk2) (er := er2) (vl := c2.k.val)
    unfold PlStkW at hw2
    rw [show c2.stk = (c2.wev wk2 er2 c2.k.val).stk from rfl] at hpre2
    rw [show c2.stk = (c2.wev wk2 er2 c2.k.val).stk from rfl] at hw2
    rw [show c2.k.sp = (c2.wev wk2 er2 c2.k.val).k.sp from rfl] at hw2
    generalize c2.wev wk2 er2 c2.k.val = c2 at h hR2 hpre2 hw2
    have hw2 : PlStkW c2 _ _ := hw2
    (try rule_simp); apply WP.ite_seq; rule_simp
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c2, h, hR2, hpre2, Or.inl rfl⟩
    apply WP.pl_scale h hR2 (kk := kk) hw1 hw64 hm hvl hw2
    refine ⟨by rule_simp, ?_⟩
    intro s3 c3 h3 hR3 hpre3 hst3
    apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c3, h3, hR3, pl_pre_trans (Nat.le_refl _) hpre3 hpre2, Or.inr ⟨rfl, hst3⟩⟩
  rule_simp
  apply WP.ite_seq; rule_simp
  -- `ok = poly_lit_val(st, w, b);`
  apply WP.call_seq (poly_lit_val_spec W sb X c0 c prems params st w b)
    (vs := [.ptr sb 0, uv w, uv (offs st.cs.pool b)]) (by rule_simp) ⟨rfl, h, hR, hb, by omega⟩
  rintro rv s1 ⟨r1, rfl, hr1⟩
  rcases hr1 with ⟨rfl, rfl, hnoneB⟩ | ⟨rfl, kk, vl, hsome, hvl, h1⟩
  · rule_simp
    apply WP.ite; rule_simp; apply WP.skip; simp only [LoopQ]
    exact lfT5_spec h hR hi hw1 hw64 (pl_lin_mul_none hn hnoneA hnoneB) _ _ _ _ _ _ _ _ _ _ _
  rule_simp
  apply WP.ite; rule_simp
  have hR1 := hR.wev (wk := c.k.work) (er := c.k.err) (vl := vl)
  clear h
  have h := h1
  rule_assign
  rw [pl_lin_mul_b hn hcond hnoneA hsome]
  apply WP.pl_call (IH _ (cv_dec_lt hd) W sb X c0 _ prems params st w a) (by rule_simp)
    ⟨rfl, h, hR1, ha, hw1, hw64⟩
  intro s2 r2 hr2
  clear h
  obtain ⟨c2, h, hR2, hpre2, hcase2⟩ := hr2
  rcases hcase2 with rfl | ⟨rfl, hw2⟩
  · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c2, h, hR2, hpre2, Or.inl rfl⟩
  rule_simp; apply WP.ite_seq; rule_simp
  -- `if (st->sp < base || st->sp > MAX_POOL) { return 0; }`: a failure return
  apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c2, h, hR2, hpre2, Or.inl rfl⟩
  intro _
  -- `ok = spend(st, st->sp - base);`
  apply WP.rule_spend h hR2
  rule_simp
  intro s2' wk2 er2 ok2 h _
  have hR2 := hR2.wev (wk := wk2) (er := er2) (vl := c2.k.val)
  unfold PlStkW at hw2
  rw [show c2.stk = (c2.wev wk2 er2 c2.k.val).stk from rfl] at hpre2
  rw [show c2.stk = (c2.wev wk2 er2 c2.k.val).stk from rfl] at hw2
  rw [show c2.k.sp = (c2.wev wk2 er2 c2.k.val).k.sp from rfl] at hw2
  generalize c2.wev wk2 er2 c2.k.val = c2 at h hR2 hpre2 hw2
  have hw2 : PlStkW c2 _ _ := hw2
  (try rule_simp); apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c2, h, hR2, hpre2, Or.inl rfl⟩
  apply WP.pl_scale h hR2 (kk := kk) hw1 hw64 hm hvl hw2
  refine ⟨by rule_simp, ?_⟩
  intro s3 c3 h3 hR3 hpre3 hst3
  apply WP.rule_ret; rule_simp [LoopQ]
  exact ⟨c3, h3, hR3, pl_pre_trans (Nat.le_refl _) hpre3 hpre2, Or.inr ⟨rfl, hst3⟩⟩

end cases

end Vbcf.Proof
