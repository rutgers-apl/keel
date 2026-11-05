import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast11

/-!
# Vbcf proofs: the Bitblast family, part 12 — `bb_term`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


theorem BbChk.ofOK {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat}
    {st : VSt} {P : Prop} {s s' : (KernelState prog State)} {r : BitVec 32} (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (ho : BbOK s P r s') :
    BbChk W sb X c0 prems params st c P r s' := by
  obtain ⟨rfl, hp⟩ := ho
  exact ⟨c, h, hR, fun hne => ⟨fun _ _ => rfl, Nat.le_refl _, hp hne⟩⟩

theorem BbChk.trans {W : World} {sb : Nat} {X : Ctx} {c0 c c1 : CMem} {prems params : List Nat}
    {st : VSt} {P : Prop} {s' : (KernelState prog State)} {r : BitVec 32}
    (hpre1 : ∀ j, j < c.k.sp.toNat → c1.stk[j]? = c.stk[j]?) (hsp1 : c.k.sp.toNat ≤ c1.k.sp.toNat)
    (H : BbChk W sb X c0 prems params st c1 P r s') : BbChk W sb X c0 prems params st c P r s' := by
  obtain ⟨c', h', hR', hr⟩ := H
  refine ⟨c', h', hR', fun hne => ?_⟩
  obtain ⟨hp, hs, hP⟩ := hr hne
  exact ⟨bb_pre_trans hpre1 hsp1 hp, by omega, hP⟩

theorem BbChk.mono {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat}
    {st : VSt} {P P' : Prop} {s' : (KernelState prog State)} {r : BitVec 32} (H : BbChk W sb X c0 prems params st c P r s')
    (himp : P → P') : BbChk W sb X c0 prems params st c P' r s' := by
  obtain ⟨c', h', hR', hr⟩ := H
  exact ⟨c', h', hR', fun hne => let ⟨a, b, p⟩ := hr hne; ⟨a, b, himp p⟩⟩

/-- `x = f(args);` as the last statement, for a read-only helper. -/
theorem WP.bb_call_last_ok {Q : (Post prog State)} {env : Env} {s : (KernelState prog State)} {x : Var} {f : String}
    {es : List Expr} {vs : List EmbC.Val} {pre : List EmbC.Val → (KernelState prog State) → Prop} {P : Prop}
    (hspec : FnSpec (State := State) Vbcf.prog f pre (fun _ s0 rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s0 P r s'))
    (hargs : evalArgs Vbcf.prog env s.mem es = some vs) (hpre : pre vs s)
    (H : ∀ r, (r ≠ 0#32 → P) →
      match env.assign s.mem x (.u32 r) with
      | none => False
      | some env' => Q .normal env' s) :
    WP Vbcf.prog (.call (some x) f es) Q env s := by
  apply WP.call hspec
  rw [hargs]
  refine ⟨hpre, ?_⟩
  rintro rv s' ⟨r, rfl, rfl, hr⟩
  exact H r hr

def BbTermSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b : Nat) (na : Node) (bs : Array Nat),
    FnSpec (State := State) Vbcf.prog "bb_term"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.pool[a]? = some na ∧ st.lv a ∧
        opC na.op % 8 = 0 ∧ st.pool[b]? = some ⟨.bvFromBool, bs⟩∧ st.lv b )
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        BbChk W sb X c0 prems params st c (Bcf.bbTerm st X.bi a bs.toList = true) r s')

set_option maxHeartbeats 1000000 in
theorem bb_term_spec : BbTermSpec (State := State) := by
  intro W sb X c0 c prems params st a b na bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbTerm) rfl
  rintro vs s ⟨rfl, h, hR, hna, hal, hbv, hnb, hb⟩
  simp [bbTerm, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbTerm) rfl
  simp only [bbTerm, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨op, args⟩ := na
  have hfa := hR.core.rep.fits a _ hna
  obtain ⟨hszb, hargsb⟩ := hR.core.bb_args hnb (by decide)
  rule_assign [hR.core.rdHdr hna]
  rule_assign [hdrW_mod256]
  rule_assign [hdr_len_bv hfa]
  rule_assign [(hR.core.rdN hnb).1, (hR.core.rdN hnb).2.1]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w id hop => ?_, fun hc1 => ?_⟩
  · subst hop
    refine WP.bb_call (bb_var_spec W sb X c0 c prems params st a b bs) ?_ ⟨rfl, h, hR, hal, hnb, by vlv⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hne => by rw [bbTerm_var hna]; exact hr hne⟩
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w v hop => ?_, fun hc2 => ?_⟩
  · subst hop
    refine WP.bb_call (bb_val_spec W sb X c0 c prems params st a b w v args bs) ?_
      ⟨rfl, h, hR, hna, by vlv, hnb, by vlv⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hne => by rw [bbTerm_val hna]; exact hr hne⟩
  have hnl : ¬ IsLeaf op := by
    rw [isLeaf_iff]
    rintro (⟨w, id, rfl⟩ | ⟨id, rfl⟩ | ⟨w, v, rfl⟩ | ⟨bb, rfl⟩)
    · exact hc1 w id rfl
    · simp [opC] at hbv
    · exact hc2 w v rfl
    · simp [opC] at hbv
  obtain ⟨hsza, hargsa⟩ := hR.core.bb_args hna hnl
  rw [tailLen_of_not_leaf hnl]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w hop => ?_, fun hc3 => ?_⟩
  · subst hop
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun h3 => ?_⟩
    obtain ⟨cc, t, e, rfl⟩ := array_eq_three h3
    have hcc := hargsa 0 (by simp)
    have ht := hargsa 1 (by simp)
    have he := hargsa 2 (by simp)
    simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hcc ht he
    have hrd := hR.core.rd3 hna hnl
    rule_assign [hrd]
    rule_assign [hrd]
    obtain ⟨nt, hnt⟩ := node_of_lv ht
    obtain ⟨ne, hne⟩ := node_of_lv he
    apply WP.guard_lit
    rule_simp [hR.core.rdHdr hnt, hR.core.rdHdr hne]
    refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun hft hfe => ?_⟩
    obtain ⟨opt, ts⟩ := nt
    obtain ⟨ope, es⟩ := ne
    simp only at hft hfe
    subst hft hfe
    refine WP.bb_call (bb_ite_spec W sb X c0 c prems params st cc t e b ts es bs) ?_
      ⟨rfl, h, hR, hcc, hnt, by vlv, hne, by vlv, hnb, by vlv⟩ ?_
    · rule_simp [hrd]
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbTerm_ite hna hnt hne]; exact hr hn0⟩
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" ["x"] args.size
    (fun k => ∀ (j : Nat) (hj : j < args.size), j < k → ∃ xa, st.pool[args[j]]? = some ⟨.bvFromBool, xa⟩))
  · exact ⟨rfl, 0, [0#32], rfl, by simp [bbSets, Env.set], by omega, fun j _ hj => absurd hj (by omega)⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hall⟩
  obtain ⟨wx, rfl⟩ := len_shape 1 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hxk := hargsa k hlt
    obtain ⟨nx, hnx⟩ := node_of_lv hxk
    rule_assign [(hR.core.rdN hna hnl).2.2 k hlt]
    apply WP.guard_lit
    rule_simp [hR.core.rdHdr hnx]
    refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun hfb => ?_⟩
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, k + 1, [BitVec.ofNat 32 (st.id args[k])], rfl, by simp [bbSets, Env.set],
      by omega, fun j hj hjk => ?_⟩
    rcases Nat.lt_or_ge j k with hjk' | hjk'
    · exact hall j hj hjk'
    · have : j = k := by omega
      subst this
      obtain ⟨opx, xa⟩ := nx
      simp only at hfb; subst hfb
      exact ⟨xa, hnx⟩
  have hfb : ∀ (j : Nat) (hj : j < args.size), ∃ xa, st.pool[args[j]]? = some ⟨.bvFromBool, xa⟩ :=
    fun j hj => hall j hj (by omega)
  obtain ⟨xss, hxss⟩ := bb_mapOpt_bits args.toList (fun j hj => by
    simpa using hfb j (by simpa using hj))
  -- bitwise operators
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w hop => ?_, fun hc4 => ?_⟩
  · subst hop
    refine WP.bb_call (bb_bitwise_spec W sb X c0 c prems params st .conj (.bvAnd w) a b args bs xss) ?_
      ⟨rfl, h, hR, Or.inl rfl, hna, by vlv, hnl, hxss, hnb, by vlv⟩ ?_
    · rule_simp [opC]
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbTerm_and hna hxss]; exact hr hn0⟩
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w hop => ?_, fun hc5 => ?_⟩
  · subst hop
    refine WP.bb_call (bb_bitwise_spec W sb X c0 c prems params st .disj (.bvOr w) a b args bs xss) ?_
      ⟨rfl, h, hR, Or.inr (Or.inl rfl), hna, by vlv, hnl, hxss, hnb, by vlv⟩ ?_
    · rule_simp [opC]
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbTerm_or hna hxss]; exact hr hn0⟩
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w hop => ?_, fun hc6 => ?_⟩
  · subst hop
    refine WP.bb_call (bb_bitwise_spec W sb X c0 c prems params st .boolXor (.bvXor w) a b args bs xss) ?_
      ⟨rfl, h, hR, Or.inr (Or.inr rfl), hna, by vlv, hnl, hxss, hnb, by vlv⟩ ?_
    · rule_simp [opC]
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbTerm_xor hna hxss]; exact hr hn0⟩
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w hop => ?_, fun hc7 => ?_⟩
  · subst hop
    refine WP.bb_call (bb_concat_spec W sb X c0 c prems params st (.bvConcat w) a b args bs xss) ?_
      ⟨rfl, h, hR, hna, by vlv, hnl, hxss, hnb, by vlv⟩ ?_
    · rule_simp
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbTerm_concat hna hxss, hr hn0]; simp⟩
  have hlo := hfa.lo
  have hhi := hfa.hi
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hi lo hop => ?_, fun hc8 => ?_⟩
  · subst hop
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun h1 => ?_⟩
    obtain ⟨x, rfl⟩ := array_eq_one h1
    obtain ⟨xa, hxa⟩ := hfb 0 (by simp)
    simp only [List.getElem_toArray, List.getElem_cons_zero] at hxa
    have hxl : st.lv x := st.args_lv hal hna (by simp)
    have hm1 : mapOpt (bitsOf st) (#[x] : Array Nat).toList = some [xa.toList] := by
      simpa using bb_mapOpt_one hxa
    have hlo' : lo < 256 := by have := hfa.lo; simpa [opLo] using this
    have hhi' : hi < 256 := by have := hfa.hi; simpa [opHi] using this
    refine WP.bb_call (bb_extract_spec W sb X c0 c prems params st hi lo x b xa bs) ?_
      ⟨rfl, h, hR, hhi', hlo', hxa, by vlv, hnb, by vlv⟩ ?_
    · have e1 := aci_par_lo (lo := opLo (Op.bvExtract hi lo)) (hi := opHi (Op.bvExtract hi lo))
        (by simp [opLo]; omega) (by simp [opHi]; omega)
      rule_simp [bb_shr24 hfa, aci_shr16 hfa, e1, hR.core.rd1 hna hnl, opLo, opHi]
      all_goals omega
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbTerm_extract hna hm1, hr hn0]; simp⟩
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w e hop => ?_, fun hc9 => ?_⟩
  · subst hop
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun h1 => ?_⟩
    obtain ⟨x, rfl⟩ := array_eq_one h1
    obtain ⟨xa, hxa⟩ := hfb 0 (by simp)
    simp only [List.getElem_toArray, List.getElem_cons_zero] at hxa
    have hxl : st.lv x := st.args_lv hal hna (by simp)
    have hm1 : mapOpt (bitsOf st) (#[x] : Array Nat).toList = some [xa.toList] := by
      simpa using bb_mapOpt_one hxa
    have he' : e < 256 := by have := hfa.hi; simpa [opHi] using this
    refine WP.bb_call (bb_sext_spec W sb X c0 c prems params st x b e xa bs) ?_
      ⟨rfl, h, hR, he', hxa, by vlv, hnb, by vlv⟩ ?_
    · rule_simp [bb_shr24 hfa, hR.core.rd1 hna hnl, opHi]
    intro r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact BbChk.ofOK h hR ⟨rfl, fun hn0 => by rw [bbTerm_sext hna hm1]; exact hr hn0⟩
  rule_assign
  apply WP.bb_push_args h hR b hnb (by simp [IsLeaf, isLeaf])
  refine ⟨by rule_simp, ?_⟩
  intro s1 c1 ok h1 hR1 hcase1
  bb_swap h1 hR1
  rule_simp
  apply WP.guard_lit
  rcases hcase1 with rfl | ⟨rfl, hpre1, hsp1, htb⟩
  · rule_simp; exact BbChk.zero h hR
  rule_simp
  simp only at htb hsp1
  have hsp1' : c.k.sp.toNat ≤ c1.k.sp.toNat := by omega
  clear hsp1
  have hsp1 := hsp1'
  have hspb := hR.bb_sp_le
  -- ADD
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w hop => ?_, fun hc10 => ?_⟩
  · subst hop
    refine WP.pl_call (bb_add_spec W sb X c0 c1 prems params st a c.k.sp.toNat (.bvAdd w) args xss
      bs.toList) ?_ ⟨rfl, h, hR, hna, by vlv, hnl, hxss, htb.bbRange⟩ ?_
    · rule_simp
    intro s2 r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact (BbChk.trans hpre1 hsp1 hr).mono (fun hp => by rw [bbTerm_add hna hxss]; exact hp)
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hcnn => ?_, fun hc11 hc12 => ?_⟩
  · have hnn : (∃ w, op = .bvNot w) ∨ (∃ w, op = .bvNeg w) := by
      by_cases e : ∃ w, op = .bvNot w
      · exact Or.inl e
      · exact Or.inr (hcnn (fun w hw => e ⟨w, hw⟩))
    clear hcnn
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun h1 => ?_⟩
    obtain ⟨x, rfl⟩ := array_eq_one h1
    obtain ⟨xa, hxa⟩ := hfb 0 (by simp)
    simp only [List.getElem_toArray, List.getElem_cons_zero] at hxa
    have hxl : st.lv x := st.args_lv hal hna (by simp)
    have hm1 : mapOpt (bitsOf st) (#[x] : Array Nat).toList = some [xa.toList] := by
      simpa using bb_mapOpt_one hxa
    obtain ⟨hszx, -⟩ := hR.core.bb_args hxa (by decide)
    rule_assign [hR.core.rd1 hna hnl]
    rule_assign [(hR.core.rdN hxa).1, (hR.core.rdN hxa).2.1]
    rule_assign
    apply WP.bb_push_args h hR x hxa (by simp [IsLeaf, isLeaf])
    refine ⟨by rule_simp [hR.core.rd1 hna hnl], ?_⟩
    intro s2 c2 ok2 h2 hR2 hcase2
    bb_swap h2 hR2
    rule_simp
    apply WP.guard_lit
    rcases hcase2 with rfl | ⟨rfl, hpre2, hsp2, htx⟩
    · rule_simp; exact BbChk.zero h hR
    rule_simp
    simp only at htx hsp2
    have hsp2' : c1.k.sp.toNat ≤ c2.k.sp.toNat := by omega
    have hb2 := htb.bbRange.frame hpre2 hsp2'
    apply WP.seq
    apply WP.ite
    rcases hnn with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rule_simp
      refine WP.bb_call_last_ok (bb_zip_not_spec W sb X c0 c2 prems params st c.k.sp.toNat
        c1.k.sp.toNat bs.toList xa.toList) ?_ ⟨rfl, h, hR, hb2, htx.bbRange⟩ ?_
      · rule_simp
      intro r hr
      rule_simp
      apply WP.rule_ret
      rule_simp
      refine BbChk.trans hpre1 hsp1 (BbChk.trans hpre2 hsp2' (BbChk.ofOK h hR ⟨rfl, fun hn0 => ?_⟩))
      rw [bbTerm_not hna hm1]; exact hr hn0
    · rule_simp
      refine WP.bb_call_last (bb_neg_spec W sb X c0 c2 prems params st c1.k.sp.toNat c.k.sp.toNat
        xa.toList bs.toList) ?_ ⟨rfl, h, hR, htx.bbRange, hb2⟩ ?_
      · rule_simp
      intro s3 r hr
      rule_simp
      apply WP.rule_ret
      rule_simp
      exact (BbChk.trans hpre1 hsp1 (BbChk.trans hpre2 hsp2' hr)).mono
        (fun hp => by rw [bbTerm_neg hna hm1]; exact hp)
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hc4 => ?_, fun _ _ _ _ => ?_⟩
  rotate_left
  · apply WP.rule_ret; rule_simp; exact BbChk.zero h hR
  have h4 : (∃ w, op = .bvSub w) ∨ (∃ w, op = .bvShl w) ∨ (∃ w, op = .bvLshr w) ∨
      (∃ w, op = .bvAshr w) := by
    by_cases e1 : ∃ w, op = .bvSub w
    · exact Or.inl e1
    by_cases e2 : ∃ w, op = .bvShl w
    · exact Or.inr (Or.inl e2)
    by_cases e3 : ∃ w, op = .bvLshr w
    · exact Or.inr (Or.inr (Or.inl e3))
    exact Or.inr (Or.inr (Or.inr (hc4 (fun w hw => e1 ⟨w, hw⟩) (fun w hw => e2 ⟨w, hw⟩)
      (fun w hw => e3 ⟨w, hw⟩))))
  clear hc4
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ]; exact BbChk.zero h hR, fun h2 => ?_⟩
  obtain ⟨x, y, rfl⟩ := array_eq_two h2
  obtain ⟨xa, hxa⟩ := hfb 0 (by simp)
  obtain ⟨ya, hya⟩ := hfb 1 (by simp)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hxa hya
  have hxl : st.lv x := st.args_lv hal hna (by simp)
  have hyl : st.lv y := st.args_lv hal hna (by simp)
  have hm2 : mapOpt (bitsOf st) (#[x, y] : Array Nat).toList = some [xa.toList, ya.toList] := by
    simpa using bb_mapOpt_two hxa hya
  obtain ⟨hszx, -⟩ := hR.core.bb_args hxa (by decide)
  obtain ⟨hszy, -⟩ := hR.core.bb_args hya (by decide)
  rule_assign [hR.core.rd2 hna hnl]
  rule_assign [(hR.core.rdN hxa).1, (hR.core.rdN hxa).2.1]
  rule_assign
  apply WP.bb_push_args h hR x hxa (by simp [IsLeaf, isLeaf])
  refine ⟨by rule_simp [hR.core.rd2 hna hnl], ?_⟩
  intro s2 c2 ok2 h2 hR2 hcase2
  bb_swap h2 hR2
  rule_simp
  apply WP.guard_lit
  rcases hcase2 with rfl | ⟨rfl, hpre2, hsp2, htx⟩
  · rule_simp; simp only [LoopQ, RetQ]; exact BbChk.zero h hR
  rule_simp
  simp only at htx hsp2
  have hsp2' : c1.k.sp.toNat ≤ c2.k.sp.toNat := by omega
  rule_assign [hR.core.rd2 hna hnl]
  rule_assign [(hR.core.rdN hya).1, (hR.core.rdN hya).2.1]
  rule_assign
  apply WP.bb_push_args h hR y hya (by simp [IsLeaf, isLeaf])
  refine ⟨by rule_simp [hR.core.rd2 hna hnl], ?_⟩
  intro s3 c3 ok3 h3 hR3 hcase3
  bb_swap h3 hR3
  rule_simp
  apply WP.guard_lit
  rcases hcase3 with rfl | ⟨rfl, hpre3, hsp3, hty⟩
  · rule_simp; exact BbChk.zero h hR
  rule_simp
  simp only at hty hsp3
  have hsp3' : c2.k.sp.toNat ≤ c3.k.sp.toNat := by omega
  have hb3 := (htb.bbRange.frame hpre2 hsp2').frame hpre3 hsp3'
  have hx3 := htx.bbRange.frame hpre3 hsp3'
  have hy3 := hty.bbRange
  have hfr : ∀ {P : Prop} {r : BitVec 32} {s4 : (KernelState prog State)},
      BbChk W sb X c0 prems params st c3 P r s4 → BbChk W sb X c0 prems params st c P r s4 :=
    fun H => BbChk.trans hpre1 hsp1 (BbChk.trans hpre2 hsp2' (BbChk.trans hpre3 hsp3' H))
  have hx255 : xa.toList.length ≤ 255 := by simpa using hszx
  apply WP.seq
  apply WP.ite
  rcases h4 with ⟨w, rfl⟩ | ⟨w, rfl⟩ | ⟨w, rfl⟩ | ⟨w, rfl⟩
  · rule_simp
    refine WP.bb_call_last (bb_sub_spec W sb X c0 c3 prems params st c1.k.sp.toNat c2.k.sp.toNat
      c.k.sp.toNat xa.toList ya.toList bs.toList) ?_ ⟨rfl, h, hR, hx3, hy3, hb3⟩ ?_
    · rule_simp
    intro s4 r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact (hfr hr).mono (fun hp => by rw [bbTerm_sub hna hm2]; exact hp)
  · rule_simp
    apply WP.ite
    rule_simp
    refine WP.bb_call_last (bb_shift_spec W sb X c0 c3 prems params st 0 c1.k.sp.toNat c2.k.sp.toNat
      c.k.sp.toNat xa.toList ya.toList bs.toList (isFalseNode st) (Bcf.bbLshStage st)) ?_
      ⟨rfl, h, hR, hx3, hy3, hb3, hx255, Or.inl ⟨rfl, rfl, rfl⟩⟩ ?_
    · rule_simp
    intro s4 r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact (hfr hr).mono (fun hp => by rw [bbTerm_shl hna hm2]; exact hp)
  · rule_simp
    apply WP.ite
    rule_simp
    apply WP.ite
    rule_simp
    refine WP.bb_call_last (bb_shift_spec W sb X c0 c3 prems params st 1 c1.k.sp.toNat c2.k.sp.toNat
      c.k.sp.toNat xa.toList ya.toList bs.toList (isFalseNode st)
      (Bcf.bbRshStage st (isFalseNode st))) ?_
      ⟨rfl, h, hR, hx3, hy3, hb3, hx255, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩ ?_
    · rule_simp
    intro s4 r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact (hfr hr).mono (fun hp => by rw [bbTerm_lshr hna hm2]; exact hp)
  · rule_simp
    apply WP.ite
    rule_simp
    apply WP.ite
    rule_simp
    refine WP.bb_call_last (bb_shift_spec W sb X c0 c3 prems params st 2 c1.k.sp.toNat c2.k.sp.toNat
      c.k.sp.toNat xa.toList ya.toList bs.toList (isLastOf xa.toList)
      (Bcf.bbRshStage st (isLastOf xa.toList))) ?_
      ⟨rfl, h, hR, hx3, hy3, hb3, hx255, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩ ?_
    · rule_simp
    intro s4 r hr
    rule_simp
    apply WP.rule_ret
    rule_simp
    exact (hfr hr).mono (fun hp => by rw [bbTerm_ashr hna hm2]; exact hp)

end Vbcf.Proof
