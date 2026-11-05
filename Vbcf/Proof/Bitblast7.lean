import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast6

/-!
# Vbcf proofs: the Bitblast family, part 7 — comparators: `bb_ult_base`, `bb_ult`, `bb_slt`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Lean side -/

theorem bb_ultGo_step {st : St} {withEq : Bool} {l r cur cl cr e rest n r' : Nat}
    {ls rs : List Nat} (hls : ls ≠ []) (hrs : rs ≠ [])
    (h1 : st.pool[cur]? = some ⟨.disj, #[cl, cr]⟩) (h2 : st.pool[cl]? = some ⟨.conj, #[e, rest]⟩)
    (h3 : isEqOf st e l r = true) (h4 : st.pool[cr]? = some ⟨.conj, #[n, r']⟩)
    (h5 : isNotOf st n l = true) (h6 : r' = r) (H : ultGo st withEq ls rs rest = true) :
    ultGo st withEq (l :: ls) (r :: rs) cur = true := by
  rcases ls with _ | ⟨l1, ls⟩
  · exact absurd rfl hls
  rcases rs with _ | ⟨r1, rs⟩
  · exact absurd rfl hrs
  rw [ultGo]
  · simp only [h1, h2, h4, h3, H, h5, h6, beq_self_eq_true, Bool.and_self]
  · intro h; cases h

theorem bb_ultGo_one_noeq {st : St} {l0 r0 cur : Nat} (h : ultBase st l0 r0 cur = true) :
    ultGo st false [l0] [r0] cur = true := by
  rw [ultGo]; simpa using h

theorem bb_ultGo_one_eq {st : St} {l0 r0 cur res' e0 : Nat}
    (h1 : st.pool[cur]? = some ⟨.disj, #[res', e0]⟩) (h2 : isEqOf st e0 l0 r0 = true)
    (h3 : ultBase st l0 r0 res' = true) : ultGo st true [l0] [r0] cur = true := by
  rw [ultGo]; simp [h1, h2, h3]

theorem bb_take_rev_ne {l : List Nat} {k : Nat} (hk : 0 < k) (hl : k ≤ l.length) :
    (l.take k).reverse ≠ [] := by
  rw [Ne, List.reverse_eq_nil_iff, List.take_eq_nil_iff]
  rintro (h | h)
  · omega
  · subst h; simp at hl; omega

/-! ## `bb_ult_base` -/

def BbUltBaseSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (l0 r0 res : Nat),
    FnSpec (State := State) Vbcf.prog "bb_ult_base"
      (fun vs s => vs = [.ptr sb 0, uv (st.id l0), uv (st.id r0), uv (st.id res)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv l0 ∧
        st.lv r0 ∧ st.lv res)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (ultBase st l0 r0 res = true) r s')

theorem bb_ult_base_spec : BbUltBaseSpec (State := State) := by
  intro W sb X c0 c prems params st l0 r0 res
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbUltBase) rfl
  rintro vs s ⟨rfl, h, hR, hl0, hr0, hres⟩
  simp [bbUltBase, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbUltBase) rfl
  simp only [bbUltBase, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨nr, hnr⟩ := node_of_lv hres
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnr]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh => ?_⟩
  obtain ⟨n, r, rfl, hn, hr⟩ := hR.core.bb_hdr2 hnr (op := .conj) (by decide) (by decide)
    (by decide) (by decide) hh
  apply WP.guard_lit
  rule_simp [hR.core.rd2 hnr]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hrr => ?_⟩
  refine WP.bb_call (bb_is1_spec W sb X c0 c prems params st n 385#32 .boolNot l0) ?_
    ⟨rfl, h, hR, hn, hl0, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hR.core.rd2 hnr]
  intro r1 hr1
  rule_simp
  apply WP.rule_ret
  rule_simp
  refine ⟨rfl, fun hne => ?_⟩
  simp only [ultBase, hnr, hrr, isNotOf, hr1 hne, beq_self_eq_true, Bool.and_self]

/-! ## `bb_ult` -/

def BbUltSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (weq : Bool) (lb rb res : Nat) (ls rs : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_ult"
      (fun vs s => vs = [.ptr sb 0, .u32 (if weq then 1#32 else 0#32), uv lb, uv ls.length, uv rb,
          uv rs.length, uv (st.id res)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st lb ls ∧
        BbRange c st rb rs ∧ st.lv res)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (ultGo st weq ls.reverse rs.reverse res = true) r s')

theorem bb_ult_spec : BbUltSpec (State := State) := by
  intro W sb X c0 c prems params st weq lb rb res ls rs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbUlt) rfl
  rintro vs s ⟨rfl, h, hR, hl, hr, hres⟩
  simp [bbUlt, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbUlt) rfl
  simp only [bbUlt, Stmt.block, initLocals, List.map, Ty.zero]
  have hlb := hl.bound hR
  have hrb := hr.bound hR
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hl0 hlen => ?_⟩
  have hl1 : 0 < ls.length := by
    rcases ls with _ | _
    · exact absurd rfl hl0
    · simp
  clear hl0
  rule_assign
  rule_assign
  apply WP.bb_loop (fun env0 => BbInvW s env0 "i" ["l", "r", "cur", "cl", "cr", "ok"] ls.length
    (fun i ws => 1 ≤ i ∧ ∃ curN, st.lv curN ∧
      ws[2]? = some (BitVec.ofNat 32 (st.id curN)) ∧
      (ultGo st weq (ls.take i).reverse (rs.take i).reverse curN = true →
        ultGo st weq ls.reverse rs.reverse res = true)))
  · refine ⟨rfl, ls.length, [0#32, 0#32, BitVec.ofNat 32 (st.id res), 0#32, 0#32, 0#32], rfl,
      by simp [bbSets, Env.set], Nat.le_refl _, hl1, res, hres, rfl, fun H => ?_⟩
    rwa [List.take_of_length_le (Nat.le_refl _), List.take_of_length_le (by omega)] at H
  rintro env s' ⟨rfl, i, ws, hws, rfl, hi, hi1, curN, hcur, hwc, hresi⟩
  obtain ⟨w1, w2, w3, w4, w5, w6, rfl⟩ : ∃ w1 w2 w3 w4 w5 w6, ws = [w1, w2, w3, w4, w5, w6] := by
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, ws⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hws
    exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hwc
  subst hwc
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hgt => ?_⟩
  · have hi1' : i = 1 := by omega
    subst hi1'
    have h0r : 0 < rs.length := by omega
    have hstk := hl.stk hR h hl1
    have e1 := hl.rd hl1
    have e2 := hr.rd h0r
    simp only [Nat.add_zero] at e1 e2
    have hl0 := hl.lt hl1
    have hr0 := hr.lt h0r
    rule_assign [hstk, e1]
    rule_assign [hstk, e2]
    have t1 := bb_take_rev (l := ls) (k := 0) hl1
    have t2 := bb_take_rev (l := rs) (k := 0) h0r
    simp only [Nat.zero_add, List.take_zero, List.reverse_nil] at t1 t2
    rw [t1, t2] at hresi
    apply WP.seq
    apply WP.ite
    cases weq
    · rule_simp
      apply WP.skip
      rule_simp
      refine WP.bb_call (bb_ult_base_spec W sb X c0 c prems params st ls[0] rs[0] curN) ?_
        ⟨rfl, h, hR, hl0, hr0, hcur⟩ ?_
      · rule_simp
      intro r3 hr3
      rule_simp
      apply WP.rule_ret
      rule_simp
      exact ⟨rfl, fun hne => hresi (bb_ultGo_one_noeq (hr3 hne))⟩
    · rule_simp
      obtain ⟨nc, hnc⟩ := node_of_lv hcur
      apply WP.guard_lit
      rule_simp [hR.core.rdHdr hnc]
      refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh => ?_⟩
      obtain ⟨res', e0, rfl, hres', he0⟩ := hR.core.bb_hdr2 hnc (op := .disj) (by decide)
        (by decide) (by decide) (by decide) hh
      refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st e0 529#32 .eq ls[0] rs[0]) ?_
        ⟨rfl, h, hR, he0, hl0, hr0, by decide, by decide, by decide, by decide⟩ ?_
      · rule_simp [hR.core.rd2 hnc]
      intro r1 hr1
      rule_simp
      apply WP.guard_lit
      rule_simp
      refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hr10 => ?_⟩
      apply WP.assign
      rule_simp [hR.core.rd2 hnc]
      refine WP.bb_call (bb_ult_base_spec W sb X c0 c prems params st ls[0] rs[0] res') ?_
        ⟨rfl, h, hR, hl0, hr0, hres'⟩ ?_
      · rule_simp
      intro r3 hr3
      rule_simp
      apply WP.rule_ret
      rule_simp
      exact ⟨rfl, fun hne => hresi (bb_ultGo_one_eq hnc (hr1 hr10) (hr3 hne))⟩
  rule_assign [bb_uv_sub (show i < 2 ^ 32 by omega) (show 1 ≤ i by omega)]
  have hi' : i - 1 < ls.length := by omega
  have hir : i - 1 < rs.length := by omega
  have hstk := hl.stk hR h hi'
  have hli := hl.lt hi'
  have hri := hr.lt hir
  rule_assign [hstk, hl.rd hi']
  rule_assign [hstk, hr.rd hir]
  obtain ⟨nc, hnc⟩ := node_of_lv hcur
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnc]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hh => ?_⟩
  obtain ⟨cl, cr, rfl, hcl, hcr⟩ := hR.core.bb_hdr2 hnc (op := .disj) (by decide) (by decide)
    (by decide) (by decide) hh
  rule_assign [hR.core.rd2 hnc]
  rule_assign [hR.core.rd2 hnc]
  obtain ⟨ncl, hncl⟩ := node_of_lv hcl
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hncl]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hh2 => ?_⟩
  obtain ⟨e, rest, rfl, he, hrest⟩ := hR.core.bb_hdr2 hncl (op := .conj) (by decide) (by decide)
    (by decide) (by decide) hh2
  refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st e 529#32 .eq ls[i - 1] rs[i - 1]) ?_
    ⟨rfl, h, hR, he, hli, hri, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hR.core.rd2 hncl]
  intro r1 hr1
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hr10 => ?_⟩
  obtain ⟨ncr, hncr⟩ := node_of_lv hcr
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hncr]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hh3 => ?_⟩
  obtain ⟨n, r', rfl, hn, hr'⟩ := hR.core.bb_hdr2 hncr (op := .conj) (by decide) (by decide)
    (by decide) (by decide) hh3
  refine WP.bb_call (bb_is1_spec W sb X c0 c prems params st n 385#32 .boolNot ls[i - 1]) ?_
    ⟨rfl, h, hR, hn, hli, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hR.core.rd2 hncr]
  intro r2 hr2
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hr20 => ?_⟩
  apply WP.guard_lit
  rule_simp [hR.core.rd2 hncr]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hrr => ?_⟩
  apply WP.assign_loop
  rule_simp [hR.core.rd2 hncl]
  refine ⟨rfl, i - 1, [BitVec.ofNat 32 (st.id ls[i - 1]), BitVec.ofNat 32 (st.id rs[i - 1]),
    BitVec.ofNat 32 (st.id rest), BitVec.ofNat 32 (st.id (cl)),
    BitVec.ofNat 32 (st.id cr), r2], rfl, by simp [bbSets, Env.set], by omega, by omega,
    rest, hrest, rfl, fun H => hresi ?_⟩
  have e1 := bb_take_rev (l := ls) (k := i - 1) hi'
  have e2 := bb_take_rev (l := rs) (k := i - 1) hir
  rw [show i - 1 + 1 = i by omega] at e1 e2
  rw [e1, e2]
  refine bb_ultGo_step ?_ ?_ hnc hncl (hr1 hr10) hncr (hr2 hr20) hrr H
  · exact bb_take_rev_ne (by omega) (by omega)
  · exact bb_take_rev_ne (by omega) (by omega)

/-! ## `bb_slt` -/

theorem bb_rev_last {l : List Nat} (h : 0 < l.length) :
    l.reverse = l[l.length - 1] :: (l.take (l.length - 1)).reverse := by
  have := bb_take_rev (l := l) (k := l.length - 1) (by omega)
  rwa [show l.length - 1 + 1 = l.length by omega, List.take_of_length_le (Nat.le_refl _)] at this

theorem bb_slt_of {st : St} {withEq : Bool} {lsS rsS res S N l nr e rest : Nat} {ls rs : List Nat}
    (hls : 1 ≤ ls.length) (h1 : st.pool[res]? = some ⟨.disj, #[S, N]⟩)
    (h2 : st.pool[N]? = some ⟨.conj, #[l, nr]⟩) (h3 : l = lsS) (h4 : isNotOf st nr rsS = true)
    (h5 : st.pool[S]? = some ⟨.conj, #[e, rest]⟩) (h6 : isEqOf st e lsS rsS = true)
    (h7 : ultGo st withEq ls rs rest = true) :
    sltChain st withEq (lsS :: ls) (rsS :: rs) res = true := by
  simp only [sltChain, h1, h2, h5, h3, h4, h6, h7, beq_self_eq_true,
    Bool.and_self, hls]
  simp

def BbSltSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (weq : Bool) (lb rb res : Nat) (ls rs : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_slt"
      (fun vs s => vs = [.ptr sb 0, .u32 (if weq then 1#32 else 0#32), uv lb, uv ls.length, uv rb,
          uv rs.length, uv (st.id res)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st lb ls ∧
        BbRange c st rb rs ∧ st.lv res)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (sltChain st weq ls.reverse rs.reverse res = true) r s')

theorem bb_slt_spec : BbSltSpec (State := State) := by
  intro W sb X c0 c prems params st weq lb rb res ls rs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbSlt) rfl
  rintro vs s ⟨rfl, h, hR, hl, hr, hres⟩
  simp [bbSlt, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbSlt) rfl
  simp only [bbSlt, Stmt.block, initLocals, List.map, Ty.zero]
  have hlb := hl.bound hR
  have hrb := hr.bound hR
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hl0 hr0 => ?_⟩
  have hrpos : 0 < rs.length := by
    rcases rs with _ | _
    · exact absurd rfl hr0
    · simp
  clear hr0 hl0
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hl2 => ?_⟩
  have hli : ls.length - 1 < ls.length := by omega
  have hri : rs.length - 1 < rs.length := by omega
  have hstk := hl.stk hR h hli
  have e1 := hl.rd hli
  have e2 := hr.rd hri
  rw [show lb + (ls.length - 1) = lb + ls.length - 1 by omega] at e1
  rw [show rb + (rs.length - 1) = rb + rs.length - 1 by omega] at e2
  have hlS := hl.lt hli
  have hrS := hr.lt hri
  rule_assign [hstk, e1, bb_uv_sub (show lb + ls.length < 2 ^ 32 by omega)
    (show 1 ≤ lb + ls.length by omega)]
  rule_assign [hstk, e2, bb_uv_sub (show rb + rs.length < 2 ^ 32 by omega)
    (show 1 ≤ rb + rs.length by omega)]
  obtain ⟨nres, hnres⟩ := node_of_lv hres
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnres]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh => ?_⟩
  obtain ⟨S, N, rfl, hS, hN⟩ := hR.core.bb_hdr2 hnres (op := .disj) (by decide) (by decide)
    (by decide) (by decide) hh
  rule_assign [hR.core.rd2 hnres]
  rule_assign [hR.core.rd2 hnres]
  obtain ⟨nN, hnN⟩ := node_of_lv hN
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnN]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh2 => ?_⟩
  obtain ⟨l, nr, rfl, hl', hnr⟩ := hR.core.bb_hdr2 hnN (op := .conj) (by decide) (by decide)
    (by decide) (by decide) hh2
  apply WP.guard_lit
  rule_simp [hR.core.rd2 hnN]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hlS' => ?_⟩
  refine WP.bb_call (bb_is1_spec W sb X c0 c prems params st nr 385#32 .boolNot
    rs[rs.length - 1]) ?_ ⟨rfl, h, hR, hnr, hrS, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hR.core.rd2 hnN]
  intro r1 hr1
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hr10 => ?_⟩
  obtain ⟨nS, hnS⟩ := node_of_lv hS
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnS]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh3 => ?_⟩
  obtain ⟨e, rest, rfl, he, hrest⟩ := hR.core.bb_hdr2 hnS (op := .conj) (by decide) (by decide)
    (by decide) (by decide) hh3
  refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st e 529#32 .eq ls[ls.length - 1]
    rs[rs.length - 1]) ?_ ⟨rfl, h, hR, he, hlS, hrS, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hR.core.rd2 hnS]
  intro r2 hr2
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hr20 => ?_⟩
  have htl : (ls.take (ls.length - 1)).length = ls.length - 1 := by simp
  have htr : (rs.take (rs.length - 1)).length = rs.length - 1 := by simp
  refine WP.bb_call (bb_ult_spec W sb X c0 c prems params st weq lb rb rest
    (ls.take (ls.length - 1)) (rs.take (rs.length - 1))) ?_
    ⟨rfl, h, hR, hl.take _, hr.take _, hrest⟩ ?_
  · rule_simp [hR.core.rd2 hnS, htl, htr, bb_uv_sub (show ls.length < 2 ^ 32 by omega)
      (show 1 ≤ ls.length by omega), bb_uv_sub (show rs.length < 2 ^ 32 by omega)
      (show 1 ≤ rs.length by omega)]
  intro r3 hr3
  rule_simp
  apply WP.rule_ret
  rule_simp
  refine ⟨rfl, fun hne => ?_⟩
  rw [bb_rev_last (l := ls) (by omega), bb_rev_last (l := rs) hrpos]
  exact bb_slt_of (by simp; omega) hnres hnN hlS' (hr1 hr10) hnS (hr2 hr20) (hr3 hne)

end Vbcf.Proof
