import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast4

/-!
# Vbcf proofs: the Bitblast family, part 5 — `bb_bitwise`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Lean side -/

/-- The column `i` of the operands. -/
theorem bb_col {xss : List (List Nat)} {i : Nat}
    (h : ∀ (k : Nat) (hk : k < xss.length), i < xss[k].length) :
    mapOpt (fun xs => xs[i]?) xss = some (xss.map (fun xs => xs.getD i 0)) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    have h0 := h 0 (by simp)
    have ih' := ih (fun k hk => h (k + 1) (by simp; omega))
    simp only [List.getElem_cons_zero] at h0
    simp only [mapOpt, ih', List.getElem?_eq_getElem h0, List.map_cons, List.getD_eq_getElem?_getD,
      Option.getD_some]

theorem bb_bitwise_step {st : St} {op : Op} {xss : List (List Nat)} {bs col : List Nat} {i : Nat}
    (hi : i < bs.length) (hc : mapOpt (fun xs => xs[i]?) xss = some col)
    (h1 : chainRev st op col.reverse bs[i] = true)
    (h2 : Bcf.bbBitwise st op xss (i + 1) (bs.drop (i + 1)) = true) :
    Bcf.bbBitwise st op xss i (bs.drop i) = true := by
  rw [List.drop_eq_getElem_cons hi]
  simp only [Bcf.bbBitwise, hc, h1, h2, Bool.and_self]

theorem bb_chain_step {st : St} {op : Op} {col : List Nat} {k cur l r : Nat}
    (hk : k < col.length) (hk1 : 1 ≤ k) (hn : st.pool[cur]? = some ⟨op, #[l, r]⟩) (hr : r = col[k])
    (H : chainRev st op (col.take k).reverse l = true) :
    chainRev st op (col.take (k + 1)).reverse cur = true := by
  rw [bb_take_rev hk]
  obtain ⟨y, rest, hy⟩ : ∃ y rest, (col.take k).reverse = y :: rest := by
    cases e : (col.take k).reverse with
    | nil =>
      rw [List.reverse_eq_nil_iff, List.take_eq_nil_iff] at e
      rcases e with e | e
      · omega
      · subst e; simp at hk
    | cons y rest => exact ⟨y, rest, rfl⟩
  rw [hy] at H ⊢
  simp only [chainRev, hn, hr, H, beq_self_eq_true, Bool.and_self]

theorem bb_chain_end {st : St} {op : Op} {col : List Nat} {cur : Nat} (h0 : 0 < col.length)
    (he : cur = col[0]) : chainRev st op (col.take 1).reverse cur = true := by
  rw [bb_take_rev (k := 0) h0]
  simp [chainRev, he]

theorem bb_or_512 {c : Nat} (hc : c < 256) : (BitVec.ofNat 32 c ||| 512#32).toNat = c + 512 := by
  rw [BitVec.toNat_or, bv_toNat_ofNat (n := c) (by omega)]
  have e : (512#32 : BitVec 32).toNat = 2 <<< 8 := rfl
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : c < 2 ^ 8)]
  rw [Nat.shiftLeft_eq]; omega

/-- The three operators of `bb_bitwise`. -/
def BbBwOp (op : Op) : Prop := op = .conj ∨ op = .disj ∨ op = .boolXor

theorem BbBwOp.facts {op : Op} (h : BbBwOp op) :
    ¬ IsLeaf op ∧ opLo op = 0 ∧ opHi op = 0 ∧ opC op < 256 := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ## `bb_bitwise` -/

def BbBitwiseSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (op aop : Op) (a b : Nat) (args bs : Array Nat) (xss : List (List Nat)),
    FnSpec (State := State) Vbcf.prog "bb_bitwise"
      (fun vs s => vs = [.ptr sb 0, uv (opC op), uv (st.id a), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbBwOp op ∧
        st.pool[a]? = some ⟨aop, args⟩ ∧ st.lv a ∧ ¬ IsLeaf aop ∧ mapOpt (bitsOf st) args.toList = some xss ∧
        st.pool[b]? = some ⟨.bvFromBool, bs⟩∧ st.lv b )
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (Bcf.bbBitwise st op xss 0 bs.toList = true) r s')

theorem bb_bitwise_spec : BbBitwiseSpec (State := State) := by
  intro W sb X c0 c prems params st op aop a b args bs xss
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbBitwise) rfl
  rintro vs s ⟨rfl, h, hR, hop, hn, hal, hl, hxss, hnb, hb⟩
  simp [bbBitwise, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbBitwise) rfl
  simp only [bbBitwise, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hlop, hlo, hhi, hc⟩ := hop.facts
  obtain ⟨hsz, hargs⟩ := hR.core.bb_args hn hl
  obtain ⟨hszb, hargsb⟩ := hR.core.bb_args hnb (by decide)
  have hxl := mapOpt_length hxss
  simp only [Array.length_toList] at hxl
  rule_assign [(hR.core.rdN hn hl).1, (hR.core.rdN hn hl).2.1]
  rule_assign [(hR.core.rdN hnb).1, (hR.core.rdN hnb).2.1]
  rule_assign
  have hhd : (BitVec.ofNat 32 (opC op) ||| 512#32).toNat = opHdr op + 2 * 256 := by
    rw [bb_or_512 hc]; simp [opHdr, hlo, hhi]
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" ["k", "x", "cur"] bs.size
    (fun i => Bcf.bbBitwise st op xss i (bs.toList.drop i) = true →
      Bcf.bbBitwise st op xss 0 bs.toList = true))
  · exact ⟨rfl, 0, [0#32, 0#32, 0#32], rfl, by simp [bbSets, Env.set], by omega, fun h => h⟩
  rintro env s' ⟨rfl, i, ws, hws, rfl, hi, hres⟩
  obtain ⟨w1, w2, w3, rfl⟩ := len_shape 3 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact hres (by rw [List.drop_of_length_le (by simp; omega)]; rfl)
  rule_assign
  apply WP.bb_loop (fun env1 => BbInv s' env1 "k" ["x"] args.size
    (fun k => ∀ (j : Nat) (hj : j < xss.length), j < k → i < xss[j].length))
  · exact ⟨rfl, 0, [w2], rfl, by simp [bbSets, Env.set], by omega, fun j _ hj => absurd hj (by omega)⟩
  rintro env s'' ⟨rfl, k, ws, hws, rfl, hk, hcol⟩
  obtain ⟨w4, rfl⟩ := len_shape 1 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hak := hargs k hlt
    obtain ⟨xa, hxa, hxk⟩ := bb_bits_at hxss hlt
    obtain ⟨hxsz, -⟩ := hR.core.bb_args hxa (by decide)
    rule_assign [(hR.core.rdN hn hl).2.2 k hlt]
    apply WP.guard_lit
    rule_simp [(hR.core.rdN hxa).1, (hR.core.rdN hxa).2.1]
    refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hix => ?_⟩
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, k + 1, [BitVec.ofNat 32 (st.id args[k])], rfl, by simp [bbSets, Env.set],
      by omega, fun j hj hjk => ?_⟩
    rcases Nat.lt_or_ge j k with hjk' | hjk'
    · exact hcol j hj hjk'
    · have hjk2 : j = k := by omega
      subst hjk2
      rw [List.getElem?_eq_getElem hj] at hxk
      simp only [Option.some.injEq] at hxk
      rw [hxk]; simpa using hix
  have hcolOK : ∀ (j : Nat) (hj : j < xss.length), i < xss[j].length :=
    fun j hj => hcol j hj (by omega)
  have hcolE := bb_col hcolOK
  generalize hcd : List.map (fun xs => xs.getD i 0) xss = col at hcolE
  have hcl : col.length = xss.length := by rw [← hcd]; simp
  have hcol_k : ∀ (j : Nat) (hj : j < args.size) (xa : Array Nat),
      st.pool[args[j]]? = some ⟨.bvFromBool, xa⟩ → ∃ (hix : i < xa.size) (hjc : j < col.length),
        col[j] = xa[i] := by
    intro j hj xa hxa
    obtain ⟨xa', hxa', hxk⟩ := bb_bits_at hxss hj
    rw [hxa] at hxa'; simp only [Option.some.injEq, Node.mk.injEq, true_and] at hxa'; subst hxa'
    have hj' : j < xss.length := by omega
    rw [List.getElem?_eq_getElem hj', Option.some.injEq] at hxk
    have hix : i < xa.size := by have := hcolOK j hj'; rw [hxk] at this; simpa using this
    refine ⟨hix, by omega, ?_⟩
    subst hcd
    simp [hxk, List.getD_eq_getElem?_getD, hix]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hn0 => ?_⟩
  have hn1 : 0 < args.size := by
    rw [Nat.pos_iff_ne_zero]; intro e; exact hn0 (Array.size_eq_zero_iff.mp e)
  have hbi := hargsb i hlt
  rule_assign [(hR.core.rdN hnb).2.2 i hlt]
  rule_assign
  apply WP.bb_loop (fun env2 => BbInvW s'' env2 "k" ["x", "cur"] args.size
    (fun k ws => 1 ≤ k ∧ ∃ curN, st.lv curN ∧ ws[1]? = some (BitVec.ofNat 32 (st.id curN)) ∧
      (chainRev st op (col.take k).reverse curN = true → chainRev st op col.reverse bs[i] = true)))
  · refine ⟨rfl, args.size, [w4, BitVec.ofNat 32 (st.id bs[i])], rfl, by simp [bbSets, Env.set],
      Nat.le_refl _, hn1, bs[i], hbi, rfl, fun H => ?_⟩
    rwa [List.take_of_length_le (by omega)] at H
  rintro env s3 ⟨rfl, k, ws, hws, rfl, hk, hk1, curN, hcur, hws1, hchain⟩
  obtain ⟨w5, w6, rfl⟩ := len_shape 2 hws
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hws1
  subst hws1
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt2 => ?_⟩
  · have hk1' : k = 1 := by omega
    subst hk1'
    obtain ⟨xa0, hxa0, -⟩ := bb_bits_at hxss hn1
    obtain ⟨hix0, hc0, hcol0⟩ := hcol_k 0 hn1 xa0 hxa0
    have e0 := (hR.core.rdN hn hl).2.2 0 hn1
    simp only [Nat.add_zero] at e0
    have hx0l := hargs 0 hn1
    have hxa0l : st.lv xa0[i] := (hR.core.bb_args hxa0 (by decide) hx0l).2 i hix0
    have hiz : i < 256 := by omega
    rule_assign [e0]
    apply WP.guard_lit
    rule_simp [(hR.core.rdN hxa0).2.2 i hix0]
    refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun he => ?_⟩
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, i + 1, [BitVec.ofNat 32 1, BitVec.ofNat 32 (st.id args[0]),
      BitVec.ofNat 32 (st.id curN)], rfl, by simp [bbSets, Env.set], by omega, fun H => ?_⟩
    exact hres (bb_bitwise_step (by simpa using hlt) hcolE
      (hchain (bb_chain_end (by omega) (by rw [hcol0]; exact he))) H)
  rule_assign [bb_uv_sub (show k < 2 ^ 32 by omega) (show 1 ≤ k by omega)]
  have hk' : k - 1 < args.size := by omega
  obtain ⟨xa, hxa, -⟩ := bb_bits_at hxss hk'
  obtain ⟨hix, hjc, hcolj⟩ := hcol_k (k - 1) hk' xa hxa
  have hxkl := hargs (k - 1) hk'
  have hxai : st.lv xa[i] := (hR.core.bb_args hxa (by decide) hxkl).2 i hix
  have hiz : i < 256 := by omega
  rule_assign [(hR.core.rdN hn hl).2.2 (k - 1) hk']
  obtain ⟨nc, hnc⟩ := node_of_lv hcur
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnc]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hh => ?_⟩
  obtain ⟨l, r, rfl, hl', hr'⟩ := hR.core.bb_hdr2 hnc hhd hlop (by omega) (by omega) hh
  apply WP.guard_lit
  rule_simp [hR.core.rd2 hnc hlop, (hR.core.rdN hxa).2.2 i hix]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hre => ?_⟩
  apply WP.assign_loop
  rule_simp [hR.core.rd2 hnc hlop]
  refine ⟨rfl, k - 1, [BitVec.ofNat 32 (st.id args[k - 1]), BitVec.ofNat 32 (st.id l)],
    rfl, by simp [bbSets, Env.set], by omega, by omega, l, hl', rfl, fun H => hchain ?_⟩
  have := bb_chain_step (k := k - 1) (by omega) (by omega) hnc (by rw [hcolj, hre]) H
  rwa [show k - 1 + 1 = k by omega] at this

end Vbcf.Proof
