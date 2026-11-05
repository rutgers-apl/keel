import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite11

/-!
# Vbcf proofs: the Rewrite family, part 12 — the end of `r_rewrite`

Parameter check (`paramsOK`), condition (`checkCond`), and the conclusion (`rwConclude`):
`RrTailSpec`, hence **`r_rewrite_spec`**.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-- After the condition. -/
def RrMid2 (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (prems ps args : List Nat)
    (rid off : Nat) (r : RwRule) (i a : BitVec 32) (env' : Env) (s' : (KernelState prog State)) : Prop :=
  ∃ (c' : CMem) (st1 : VSt) (ok cv : BitVec 32),
    env' = rrEnv sb prems.length (ps.length + 1) rid off 0#32 (BitVec.ofNat 32 ps.length) i a ok
      cv 0#32 0#32 ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems (rid :: ps) c' st1 ∧
    ruleRewrite rwTable X.bi X.ei st prems (rid :: ps) = rwConclude X.bi args.toArray r st1 ∧
    RwArgsAt c' st1 0 args

theorem rr_tail_spec : RrTailSpec (State := State) := by
  intro W sb X c0 c st prems ps args rid off r s i a ok h hR hsp0 htop hmap hr0 hr hrec hwf hoff0
    hoffl hnp hna
  have hs := prog_ck
  dsimp only [rrTail, rRewrite, Stmt.block, rrEnv]
  simp only [wfRule, Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨hwp, hwc⟩, hwl⟩, hwr⟩ := hwf
  have hlen := htop.1
  have hal : args.length = ps.length := by have := mapOpt_length hmap; simpa using this
  have hrl : off + recHdr + r.params.length < 65536 := by
    simp [encRule, recHdr] at hoffl; simp [recHdr]; omega
  have hargs : RwArgsAt c st 0 args := ⟨htop.2, by omega⟩
  apply WP.call_seq (rw_params_spec W sb X c0 c prems (rid :: ps) st off r 0 args)
    (by rule_simp [hal]) ⟨rfl, h, hR, hrec, hwp, hrl, hargs⟩
  rintro rv s1 ⟨v, rfl, rfl, hv⟩
  rule_simp
  rule_guard
  intro hv0
  have hpar := hv hv0
  obtain ⟨cw', hcw, hcm⟩ := hrec.cond
  have hcw' : cw' < 65536 := by
    revert hcm; cases r.cond with
    | none => intro e; omega
    | some ce => intro ⟨_, hat⟩; have := hat.le (rw_encE_len_pos ce); have := rw_words_len; omega
  apply WP.assign_seq
  rw [rw_eval_cload (q := BitVec.ofNat 32 (off + 1)) rw_findConst (by rule_simp)
    (show (BitVec.ofNat 32 (off + 1)).toNat = off + 1 from bv_toNat_ofNat (by omega))
    (rw_tbl_get hcw)]
  rule_simp
  apply WP.seq_mid (RrMid2 W sb X c0 st prems ps args rid off r i a)
  · apply WP.ite
    rule_simp
    cases hc : r.cond with
    | none =>
      simp only [hc] at hcm
      subst hcm
      refine ⟨fun _ => ?_, fun h0 => absurd rfl h0⟩
      apply WP.ite
      rule_simp
      refine ⟨fun _ => WP.rule_fail h, fun hnp0 => WP.skip ?_⟩
      subst hnp0
      exact ⟨c, st, _, _, rfl, h, hR, by simp [ruleRewrite, hr0, hr, hmap, hpar, hc], hargs⟩
    | some ce =>
      simp only [hc] at hcm hwc
      obtain ⟨hc0, hatc⟩ := hcm
      simp only [wfOpt] at hwc
      refine ⟨fun h0 => absurd h0 (by omega), fun _ => ?_⟩
      apply WP.call_seq (rw_inst_spec 32#32 W sb X c0 c prems (rid :: ps) st ce cw' 0 args)
        (by rule_simp [hal]) ⟨rfl, h, hR, hatc, hwc, hargs⟩
      rintro rv s3 ⟨c2, rfl, c3, h3, hB3⟩
      clear h
      have h := h3
      rule_simp
      rule_guard
      intro hne
      obtain ⟨st2, ci, hP2, hR2, hext2, hsp2, hpre2, hci, rfl⟩ := hB3.resolve_left hne
      have hargs2 := hargs.frame hext2 (by rw [hsp2]; exact Nat.le_refl _) hpre2
      clear hR
      have hR := hR2
      apply WP.call_seq (rw_check_cond_spec W sb X c0 c3 prems (rid :: ps) st2 ci) (by rule_simp)
        ⟨rfl, h, hR, hci⟩
      rintro rv s4 ⟨v4, rfl, ⟨wk, er, vl, h4⟩, hv4⟩
      have hR4 := hR.wev (wk := wk) (er := er) (vl := vl)
      have hstk := rw_wev_stk c3 wk er vl
      have hargs4 := hargs2.frame (VExt.refl _) (by rw [hstk.2]; exact Nat.le_refl _)
        (fun j _ => by rw [hstk.1])
      clear h hR
      generalize c3.wev wk er vl = c5 at h4 hR4 hargs4
      have h := h4
      have hR := hR4
      rule_simp
      apply WP.ite
      rule_simp
      refine ⟨fun _ => WP.rule_fail h, fun hv0 => WP.skip ?_⟩
      exact ⟨c5, st2, _, _, rfl, h, hR,
        by simp [ruleRewrite, hr0, hr, hmap, hpar, hc, hP2, hv4 hv0], hargs4⟩
  rintro env2 s3 ⟨c2, st1, ok2, cv2, rfl, h2, hR2, hrule, hargs1⟩
  clear h hR
  have h := h2
  have hR := hR2
  simp only [rrEnv]
  obtain ⟨lw, hlw, hatl⟩ := hrec.lhs
  obtain ⟨rw', hrw, hatr⟩ := hrec.rhs
  have hlw' := hatl.le (rw_encE_len_pos _)
  have hrw' := hatr.le (rw_encE_len_pos _)
  have hwl2 := rw_words_len
  refine WP.call_seq (rw_inst_spec 32#32 W sb X c0 c2 prems (rid :: ps) st1 r.lhs lw 0 args)
    ?_ ⟨rfl, h, hR, hatl, hwl, hargs1⟩ ?_
  · apply rw_evalArgs_cons (by rule_simp)
    apply rw_evalArgs_cons (rw_eval_cload (q := BitVec.ofNat 32 (off + 2))
      rw_findConst (by rule_simp)
      (show (BitVec.ofNat 32 (off + 2)).toNat = off + 2 from
        bv_toNat_ofNat (by omega)) (rw_tbl_get hlw))
    apply rw_evalArgs_cons (by rule_simp)
    apply rw_evalArgs_cons (by rule_simp [hal])
    exact rw_evalArgs_cons (by rule_simp) rfl
  rintro rv s4 ⟨l1, rfl, c4, h4, hB4⟩
  clear h
  have h := h4
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st2, m, hP2, hR4, hext4, hsp4, hpre4, hm, rfl⟩ := hB4.resolve_left hne
  clear hR
  have hR := hR4
  have hargs2 := hargs1.frame hext4 (by rw [hsp4]; exact Nat.le_refl _) hpre4
  refine WP.call_seq (rw_inst_spec 32#32 W sb X c0 c4 prems (rid :: ps) st2 r.rhs rw' 0 args)
    ?_ ⟨rfl, h, hR, hatr, hwr, hargs2⟩ ?_
  · apply rw_evalArgs_cons (by rule_simp)
    apply rw_evalArgs_cons (rw_eval_cload (q := BitVec.ofNat 32 (off + 3))
      rw_findConst (by rule_simp)
      (show (BitVec.ofNat 32 (off + 3)).toNat = off + 3 from
        bv_toNat_ofNat (by omega)) (rw_tbl_get hrw))
    apply rw_evalArgs_cons (by rule_simp)
    apply rw_evalArgs_cons (by rule_simp [hal])
    exact rw_evalArgs_cons (by rule_simp) rfl
  rintro rv s5 ⟨r1, rfl, c5, h5, hB5⟩
  clear h
  have h := h5
  rule_simp
  rule_guard
  intro hne'
  obtain ⟨st3, t, hP3, hR5, hext5, hsp5, hpre5, ht, rfl⟩ := hB5.resolve_left hne'
  clear hR
  have hR := hR5
  have hm' := hext5.lt hm
  rw [← hext5.id hm]
  apply WP.rule_mk_eq mk_eq_specT h hR m t hm' ht
  refine ⟨by rule_simp, ?_⟩
  intro s6 c6 rr h6 hB
  rule_simp
  rule_ret
  exact hB.ret h6 (fun st' i hP => by rw [hrule]; simp [rwConclude, hP2, hP3, hP])

/-- **`r_rewrite` is `ruleRewrite rwTable`.** -/
theorem r_rewrite_spec :
    RuleSpec (State := State) "r_rewrite" (fun X st pr pa => ruleRewrite rwTable X.bi X.ei st pr pa) :=
  r_rewrite_of_tail rr_tail_spec

end Vbcf.Proof
