import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite10

/-!
# Vbcf proofs: the Rewrite family, part 11 — `r_rewrite` (`ruleRewrite`)
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-- The locals of `r_rewrite`. -/
def rrEnv (sb np na rid off : Nat) (ab n i a ok cv l r : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv np), ("na", .u32, uv na),
    ("rid", .u32, uv rid), ("off", .u32, uv off), ("ab", .u32, .u32 ab), ("n", .u32, .u32 n),
    ("i", .u32, .u32 i), ("a", .u32, .u32 a), ("ok", .u32, .u32 ok),
    ("c", .u32, .u32 cv), ("l", .u32, .u32 l), ("r", .u32, .u32 r)]

/-- The body of `r_rewrite` after the arguments have been pushed. -/
def rrTail : Stmt :=
  match rRewrite.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ t))))))))) => t
  | _ => .skip

/-- The rest of `r_rewrite` once the arguments `args` of rule `rid` (record at `off`) are on the
stack from 0. -/
def RrTailSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (st : VSt) (prems ps args : List Nat)
    (rid off : Nat) (r : RwRule) (s : (KernelState prog State)) (i a ok : BitVec 32),
    Holds W s.mem sb c → RCtx W X c0 prems (rid :: ps) c st → c0.k.sp = 0#32 →
    StkTop c st 0 args → mapOpt X.ei ps = some args → rid ≠ 0 → rwTable rid = some r →
    RwRec off r → wfRule r = true → 0 < off → off + (encRule off r).length < 65536 →
    prems.length ≤ 255 → ps.length + 1 ≤ 255 →
    WP Vbcf.prog rrTail (RuleQ W sb c0 X (ruleRewrite rwTable X.bi X.ei st prems (rid :: ps)))
      (rrEnv sb prems.length (ps.length + 1) rid off 0#32 (BitVec.ofNat 32 ps.length) i a ok 0#32 0#32
        0#32) s

/-- The loop that pushes the arguments of `r_rewrite`. -/
def RrArgInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (prems ps : List Nat)
    (rid off : Nat) (env' : Env) (s' : (KernelState prog State)) : Prop :=
  ∃ (c' : CMem) (acc : List Nat) (i : Nat) (a ok : BitVec 32),
    env' = rrEnv sb prems.length (ps.length + 1) rid off 0#32 (BitVec.ofNat 32 ps.length)
      (BitVec.ofNat 32 i) a ok 0#32 0#32 0#32 ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems (rid :: ps) c' st ∧ StkTop c' st 0 acc ∧
    1 ≤ i ∧ i ≤ ps.length + 1 ∧ mapOpt X.ei (ps.take (i - 1)) = some acc

theorem r_rewrite_of_tail (hT : RrTailSpec (State := State)) :
    RuleSpec (State := State) "r_rewrite" (fun X st pr pa => ruleRewrite rwTable X.bi X.ei st pr pa) := by
  rule_begin rRewrite
  rule_guard
  intro hna0
  obtain ⟨rid, ps, rfl⟩ : ∃ rid ps, params = rid :: ps := by
    rcases params with _ | ⟨rid, ps⟩
    · simp at hna0
    · exact ⟨rid, ps, rfl⟩
  have hrid := hR.par_lt (j := 0) (by simp)
  simp only [List.getElem_cons_zero] at hrid
  rule_assign
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hr0 => ?_, fun hr0 => ?_⟩
  · subst hr0
    rule_guard
    intro hnp0 hna2
    have hna2' : ps.length + 1 = 2 := by
      simp only [List.length_cons] at hna hna2
      rw [show (2#32 : BitVec 32) = BitVec.ofNat 32 2 from rfl, uv_inj (by omega) (by omega)] at hna2
      exact hna2
    obtain ⟨p, rfl⟩ : ∃ p, ps = [p] := by
      rcases ps with _ | ⟨p, _ | ⟨q, _⟩⟩ <;> simp at hna2' ⊢
    subst hnp0
    have hp := hR.par_lt (j := 1) (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hp
    apply WP.rule_expr_at expr_at_spec' h hR p hp
    refine ⟨by rule_simp [hR.rd_par (j := 1) (by simp)], ?_⟩
    intro r her
    rule_simp
    rule_guard
    intro hne
    obtain ⟨e, hea, he, rfl⟩ := her.ok hne
    apply WP.call_seq (rw_zero_spec W sb X c c [] [0, p] st e) (by rule_simp) ⟨rfl, h, hR, he⟩
    rintro rv s1 ⟨v, rfl, rfl, hv⟩
    rule_simp
    rule_guard
    intro hv0
    apply WP.ret
    rule_simp [LoopQ]
    exact hR.ret h he (by simp [ruleRewrite, hea, hv hv0])
  rule_guard
  intro hrid152
  have hrb : rid < bound := by simpa [RwEnc.bound] using hrid152
  cases hr : rwTable rid with
  | none =>
    apply WP.assign_seq
    rw [rw_eval_cload (q := BitVec.ofNat 32 rid) rw_findConst (by rule_simp)
      (show (BitVec.ofNat 32 rid).toNat = rid from bv_toNat_ofNat (by omega))
      (rw_tbl_get ((rw_tbl_index hrb).1 hr))]
    rule_simp
    rule_guard
  | some r =>
  obtain ⟨off, hoff, hboff, hat⟩ := (rw_tbl_index hrb).2 r hr
  have hrec := rw_rec (by simp [RwEnc.bound] at hboff; omega) hat
  have hwf := rw_tbl_wf hrb hr
  have hlen := hat.le (by simp [encRule])
  have hwl := rw_words_len
  have hoff' : off + (encRule off r).length < 65536 := by omega
  have hboff' : 0 < off := by simp [RwEnc.bound] at hboff; omega
  apply WP.assign_seq
  rw [rw_eval_cload (q := BitVec.ofNat 32 rid) rw_findConst (by rule_simp)
    (show (BitVec.ofNat 32 rid).toNat = rid from bv_toNat_ofNat (by omega)) (rw_tbl_get hoff)]
  rule_simp
  rule_guard
  intro _
  rule_assign [hsp]
  rule_assign
  rule_assign
  simp only [List.length_cons] at hna
  have hn1 : BitVec.ofNat 32 (ps.length + 1) - 1#32 = BitVec.ofNat 32 ps.length := by
    rw [cw_sub (by omega) (by omega)]; rfl
  rw [hn1]
  apply WP.loop_seq (RrArgInv W sb X c st prems ps rid off)
  · exact ⟨c, [], 1, 0#32, 0#32, rfl, h, hR, StkTop.nil (by rw [hsp]; rfl), Nat.le_refl _, by omega,
      by simp [mapOpt]⟩
  clear h hR
  rintro env s1 ⟨c1, acc, i, a, ok, rfl, h, hR, htop, hi1, hi2, hmap⟩
  simp only [rrEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hi : i = ps.length + 1 := by omega
    subst hi
    simp only [Nat.add_sub_cancel, List.take_length] at hmap
    exact hT W sb X c c1 st prems ps acc rid off r s1 _ a ok h hR hsp htop hmap hr0 hr hrec hwf hboff'
      hoff' hnp (by omega)
  have hpi := hR.par_lt (j := i) (by simp; omega)
  apply WP.rule_expr_at expr_at_spec' h hR _ hpi
  refine ⟨by rule_simp [hR.rd_par (j := i) (by simp; omega)], ?_⟩
  intro r' her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hea, he, rfl⟩ := her.ok hne
  apply WP.rule_push h hR
  rule_simp
  intro s2 c2 ok2 h2 hP
  clear h
  have h := h2
  have hR2 := hP.1
  apply WP.rule_guard h
  rule_simp
  intro hok
  apply WP.assign_loop
  rule_simp
  refine ⟨c2, acc ++ [e], i + 1, _, _, rfl, h, hR2, StkTop.push htop hP hok he, by omega, by omega, ?_⟩
  have e1 : (rid :: ps)[i]'(by simp; omega) = ps[i - 1]'(by omega) := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp
  rw [e1] at hea
  rw [show i + 1 - 1 = (i - 1) + 1 by omega, List.take_succ_eq_append_getElem (by omega)]
  exact cl_mapOpt_snoc hmap hea

end Vbcf.Proof
