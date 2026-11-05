import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.RulesBasic4
import Vbcf.Proof.DecodeEnc

/-!
# Vbcf proofs: `r_cong`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem eqSides_snoc {st : St} {p a b : Nat} (hp : st.pool[p]? = some ⟨.eq, #[a, b]⟩) :
    ∀ {l as bs : List Nat}, eqSides st l = some (as, bs) →
      eqSides st (l ++ [p]) = some (as ++ [a], bs ++ [b])
  | [], as, bs, h => by
    simp [eqSides] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [eqSides, St.node, hp, isEqNode]
  | q :: l, as, bs, h => by
    simp only [eqSides] at h
    rcases hq : (st.node q).bind isEqNode with _ | ⟨a', b'⟩ <;>
      rcases hl : eqSides st l with _ | ⟨as', bs'⟩ <;> simp [hq, hl] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [eqSides, hq, eqSides_snoc hp hl]

theorem eqSides_get {st : St} :
    ∀ {l as bs : List Nat}, eqSides st l = some (as, bs) →
      as.length = l.length ∧ bs.length = l.length ∧
      ∀ k (hk : k < l.length), ∃ a b, as[k]? = some a ∧ bs[k]? = some b ∧
        st.pool[l[k]]? = some ⟨.eq, #[a, b]⟩
  | [], as, bs, h => by
    simp [eqSides] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | q :: l, as, bs, h => by
    simp only [eqSides] at h
    rcases hq : (st.node q).bind isEqNode with _ | ⟨a', b'⟩ <;>
      rcases hl : eqSides st l with _ | ⟨as', bs'⟩ <;> simp [hq, hl] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := eqSides_get hl
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro k hk
    rcases k with _ | k
    · simp only [St.node, Option.bind] at hq
      rcases hn : st.pool[q]? with _ | n <;> simp [hn] at hq
      exact ⟨a', b', rfl, rfl, by simp [hn, isEqNode_some hq]⟩
    · exact h3 k (by simpa using hk)

/-- First loop of `r_cong`: the left sides of the first `k` premises are on the stack. -/
def CongInv1 (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (prems : List Nat) (x : Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (pw ok : BitVec 32) (as bs : List Nat),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv prems.length),
      ("na", .u32, uv 1), ("hdr", .u32, uv x), ("code", .u32, uv (x % 256)), ("i", .u32, uv k),
      ("p", .u32, .u32 pw), ("ok", .u32, .u32 ok), ("l", .u32, .u32 0#32), ("r", .u32, .u32 0#32),
      ("base", .u32, .u32 0#32)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems [x] c' st ∧ k ≤ prems.length ∧
    eqSides st (prems.take k) = some (as, bs) ∧ StkTop c' st 0 as

/-- Second loop of `r_cong`: all left sides, then the right sides of the first `k` premises. -/
def CongInv2 (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (prems : List Nat) (x : Nat)
    (as bs : List Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (pw ok : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv prems.length),
      ("na", .u32, uv 1), ("hdr", .u32, uv x), ("code", .u32, uv (x % 256)), ("i", .u32, uv k),
      ("p", .u32, .u32 pw), ("ok", .u32, .u32 ok), ("l", .u32, .u32 0#32), ("r", .u32, .u32 0#32),
      ("base", .u32, .u32 0#32)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems [x] c' st ∧ k ≤ prems.length ∧
    StkTop c' st 0 (as ++ bs.take k)

/-- A node built by `mkn` with header `code | (hdr & 0xffff0000)` (the arity added) has the
operator `congOp hdr` decodes. -/
theorem congOp_of_mkn {posOf : Nat → Nat} {n : Node} {x len : Nat} (hx : x < 4294967296)
    (hlen : len < 256) (hf : Fits posOf n) (hh : hdrW n = x % 256 + x / 65536 * 65536 + len * 256)
    (hc : x % 256 ≠ 0x18 ∧ x % 256 ≠ 0x19 ∧ x % 256 ≠ 0x08 ∧ x % 256 ≠ 0x09) (v : Nat) :
    congOp x v = some n.op :=
  congOp_of_node hf (not_leaf_of_hdrW hf (by rw [hh]; omega)) (by rw [hh]; omega)
    (by rw [hh]; omega) v

theorem r_cong_spec :
    RuleSpec (State := State) "r_cong" (fun _ st pr pa => ruleCong st pr pa) := by
  rule_begin rCong
  rcases params with _ | ⟨x, _ | ⟨y, xs⟩⟩
  · rule_guard
  rotate_left
  · rule_guard
    intro h0
    simp at hna
    rw [uv_inj (by omega) (by omega)] at h0
    omega
  rule_guard
  have hx := hR.params1
  rule_assign
  rule_assign
  rule_guard
  intro hc1 hc2 hc3 hc4
  rule_assign [hsp]
  apply WP.loop_seq (CongInv1 W sb X c st prems x)
  · exact ⟨c, 0, _, _, [], [], rfl, h, hR, by omega, by simp [eqSides], StkTop.nil (by simp [hsp])⟩
  clear h hR
  rintro env s' ⟨c', k, pw, ok, as, bs, rfl, h, hR, hk, hsides, htop⟩
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkl : k = prems.length := by omega
    subst hkl
    rw [List.take_length] at hsides
    obtain ⟨hal, hbl, hget⟩ := eqSides_get hsides
    rule_assign
    apply WP.loop_seq (CongInv2 W sb X c st prems x as bs)
    · exact ⟨c', 0, _, _, rfl, h, hR, by omega, by simpa using htop⟩
    clear h hR htop
    rintro env s2 ⟨c2, k, pw2, ok2, rfl, h, hR, hk, htop⟩
    rule_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · have hkl : k = prems.length := by omega
      subst hkl
      rw [← hbl, List.take_length] at htop
      have hhd : NonLeafHdr (x % 256 + x / 65536 * 65536) := by
        unfold NonLeafHdr; omega
      rule_assign
      apply WP.rule_mkn_raw mkn_specT h hR _ 0 as hhd htop.2.append_left
        (by have := htop.1; simp at this; omega)
      refine ⟨by rule_simp [hal], ?_⟩
      intro s3 c3 l h hB
      rule_simp
      rule_guard
      intro hne
      obtain ⟨st1, i1, ⟨n1, hh1, hf1, ha1, hp1⟩, hR, hext1, hstk1, hi1, rfl⟩ := hB.ok hne
      have htop1 := StkTop.built htop hext1 hstk1
      apply WP.rule_mkn_raw mkn_specT h hR _ as.length bs hhd (by simpa using htop1.2.drop_left)
        (by have := htop1.1; simp at this; omega)
      refine ⟨by rule_simp [hal, hbl], ?_⟩
      intro s4 c4 r h hB
      rule_simp
      rule_guard
      intro hne2
      obtain ⟨st2, i2, ⟨n2, hh2, hf2, ha2, hp2⟩, hR, hext2, hstk2, hi2, rfl⟩ := hB.ok hne2
      rw [← hext2.id hi1]
      apply WP.rule_mk_eq mk_eq_specT h hR i1 i2 (hext2.lt hi1) hi2
      refine ⟨by rule_simp, ?_⟩
      intro s5 c5 r h hB
      rule_simp
      rule_ret
      have hc : x % 256 ≠ 0x18 ∧ x % 256 ≠ 0x19 ∧ x % 256 ≠ 0x08 ∧ x % 256 ≠ 0x09 := by omega
      have e1 := congOp_of_mkn hx (len := as.length) (by omega) hf1 hh1 hc prems.length
      have e2 := congOp_of_mkn hx (len := bs.length) (by omega) hf2 hh2 hc prems.length
      rw [e1] at e2
      have e3 : n2.op = n1.op := (Option.some.inj e2).symm
      rw [node_eq_of_args ha1] at hp1
      rw [node_eq_of_args ha2, e3] at hp2
      exact hB.ret h (fun st3 i3 hP3 => by
        simp [ruleCong, hsides, e1, hp1, hp2, hP3])
    · obtain ⟨a, b, hak, hbk, hn⟩ := hget k hlt
      have hp := hR.prem_lt hlt
      have hb : st.lv b := st.args_lv hp hn (by simp)
      rule_assign [hR.rd_prem hlt]
      apply WP.rule_push h hR
      rule_simp [hR.core.rd2 hn]
      intro s3 c3 ok3 h3' hP
      have htop' := fun hok => StkTop.push htop hP hok hb
      have hR3 := hP.1
      clear h hR
      have h := h3'
      have hR := hR3
      clear h3' hR3
      rule_guard
      intro hok
      apply WP.assign_loop
      rule_simp
      refine ⟨c3, k + 1, _, ok3, rfl, h, hR, by omega, ?_⟩
      rw [List.take_add_one, hbk]
      simpa using htop' hok
  · have hp := hR.prem_lt hlt
    obtain ⟨n, hn⟩ := node_of_lv hp
    rule_assign [hR.rd_prem hlt]
    rule_guard [hR.core.rdHdr hn]
    intro hop
    obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
    apply WP.rule_push h hR
    rule_simp [hR.core.rd2 hn]
    intro s2 c2 ok2 h2' hP
    have htop' := fun hok => StkTop.push htop hP hok ha
    have hR2 := hP.1
    clear h hR
    have h := h2'
    have hR := hR2
    clear h2' hR2
    rule_guard
    intro hok
    apply WP.assign_loop
    rule_simp
    refine ⟨c2, k + 1, _, ok2, as ++ [a], bs ++ [b], rfl, h, hR, by omega, ?_, htop' hok⟩
    rw [List.take_succ_eq_append_getElem hlt]
    exact eqSides_snoc hn hsides

end Vbcf.Proof
