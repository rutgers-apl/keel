import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast3

/-!
# Vbcf proofs: the Bitblast family, part 4 — `bb_add`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## `push_args` with the whole stack frame -/

section calls
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {es : List Expr} {rest : Stmt}

/-- `x = push_args(st, e); rest`, keeping every cell below `sp`. -/
theorem WP.bb_push_args (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (i : Nat)
    {nd : Node} (hn : st.pool[i]? = some nd) (hl : ¬ IsLeaf nd.op)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv (st.id i)] ∧
      ∀ s' c' ok, Holds W s'.mem sb c' → RCtx W X c0 prems params c' st →
        (ok = 0#32 ∨ (ok = 1#32 ∧ (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧
          c'.k.sp.toNat = c.k.sp.toNat + nd.args.size ∧
          StkTop c' st c.k.sp.toNat nd.args.toList)) →
        match env.assign s'.mem x (.u32 ok) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog (.seq (.call (some x) "push_args" es) rest) Q env s := by
  have hi := h_lv
  apply WP.call_seq (push_args_spec W sb c X.posOf st.cs _ (st.σ i) (nd.ren st.σ)) H.1
    ⟨rfl, h, hR.core.cinv, st.img i nd hi hn, hl, hR.core.id_toNat hi⟩
  rintro rv s' ⟨c', h', hfr, hc', hpre, hcase⟩
  have hR' := hR.after_push hfr hc'.stk
  rcases hcase with rfl | ⟨rfl, hsp, hids⟩
  · exact H.2 s' c' 0#32 h' hR' (Or.inl rfl)
  · simp only [Node.ren_args, Array.toList_map, Array.size_map] at hids hsp
    exact H.2 s' c' 1#32 h' hR' (Or.inr ⟨rfl, hpre, hsp, by simpa using hsp,
      StkIds.ofC hids (fun a ha => st.closed i nd hi hn a (by simpa using ha))⟩)

end calls

/-- The bits of argument `k` of a node whose arguments are all `from_bool` nodes. -/
theorem bb_bits_at {st : St} {args : Array Nat} {xss : List (List Nat)}
    (h : mapOpt (bitsOf st) args.toList = some xss) {k : Nat} (hk : k < args.size) :
    ∃ xa, st.pool[args[k]]? = some ⟨.bvFromBool, xa⟩ ∧ xss[k]? = some xa.toList := by
  have e := mapOpt_getElem? h (k := k) (by simpa using hk)
  have hl := mapOpt_length h
  simp only [Array.getElem_toList] at e
  unfold bitsOf at e
  split at e
  · rename_i xa hxa
    exact ⟨xa, hxa, e.symm⟩
  · rw [List.getElem?_eq_getElem (by simp at hl; omega)] at e
    cases e

theorem bb_take_rev {α : Type} {l : List α} {k : Nat} (hk : k < l.length) :
    (l.take (k + 1)).reverse = l[k] :: (l.take k).reverse := by
  rw [List.take_succ_eq_append_getElem hk, List.reverse_append]; rfl

theorem bb_addRev_step {st : VSt} {bi : Builtins} {xk : List Nat} {rest : List (List Nat)}
    {S L : List Nat} (hr : rest ≠ []) (hp : preSum st S = some L)
    (h1 : ripple st bi L xk S false = true) (h2 : bbAddRev st bi rest L = true) :
    bbAddRev st bi (xk :: rest) S = true := by
  rcases rest with _ | ⟨y, rest⟩
  · exact absurd rfl hr
  · simp [bbAddRev, hp, h1, h2]

/-! ## `bb_add` -/

/-- Loop invariant of the peeling loop of `bb_add`: `k` operands left, the partial sum `S`
on the stack at `sbN`. -/
def BbAddInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (c : CMem) (n : Nat) (xss : List (List Nat)) (bs : List Nat) (env0 : Env) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k sbN : Nat) (S : List Nat) (ws : List (BitVec 32)), ws.length = 5 ∧
    env = bbSets ((env0.set "k" (uv k)).set "sb" (uv sbN)) (["x", "nx", "xb", "pre", "ok"].zip ws) ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧ c.k.sp.toNat ≤ c'.k.sp.toNat ∧
    1 ≤ k ∧ k ≤ n ∧ S.length = bs.length ∧ BbRange c' st sbN S ∧
    (bbAddRev st X.bi (xss.take k).reverse S = true → bbAddRev st X.bi xss.reverse bs = true)

def BbAddSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a bsb : Nat) (op : Op) (args : Array Nat) (xss : List (List Nat)) (bs : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_add"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv bsb, uv bs.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧
        st.pool[a]? = some ⟨op, args⟩ ∧ st.lv a ∧ ¬ IsLeaf op ∧ mapOpt (bitsOf st) args.toList = some xss ∧
        BbRange c st bsb bs)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        BbChk W sb X c0 prems params st c (bbAddRev st X.bi xss.reverse bs = true) r s')

theorem bb_add_spec : BbAddSpec (State := State) := by
  intro W sb X c0 c prems params st a bsb op args xss bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbAdd) rfl
  rintro vs s ⟨rfl, h, hR, hn, hal, hl, hxss, hb⟩
  simp [bbAdd, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbAdd) rfl
  simp only [bbAdd, Stmt.block, initLocals, List.map, Ty.zero]
  have hbb := hb.bound hR
  obtain ⟨hsz, hargs⟩ := hR.core.bb_args hn hl
  have hxl := mapOpt_length hxss
  simp only [Array.length_toList] at hxl
  rule_assign [(hR.core.rdN hn hl).1, (hR.core.rdN hn hl).2.1]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp only [RetQ]; exact BbChk.zero h hR, fun hn0 => ?_⟩
  have hn1 : 0 < args.size := by
    rw [Nat.pos_iff_ne_zero]; intro e; exact hn0 (Array.size_eq_zero_iff.mp e)
  clear hn0
  rule_assign
  rule_assign
  apply WP.bb_loop (BbAddInv W sb X c0 prems params st c args.size xss bs)
  · refine ⟨c, args.size, bsb, bs, [0#32, 0#32, 0#32, 0#32, 0#32], rfl, by simp [bbSets, Env.set],
      h, hR, fun _ _ => rfl, Nat.le_refl _, by omega, Nat.le_refl _, rfl, hb, fun H => ?_⟩
    rwa [List.take_of_length_le (by omega)] at H
  clear h hR
  rintro env s' ⟨c', k, sbN, S, ws, hws, rfl, h, hR, hpre, hsp, hk1, hkn, hSl, hS, hres⟩
  obtain ⟨w1, w2, w3, w4, w5, rfl⟩ : ∃ w1 w2 w3 w4 w5, ws = [w1, w2, w3, w4, w5] := by
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, ws⟩⟩⟩⟩⟩⟩ <;> simp at hws
    exact ⟨_, _, _, _, _, rfl⟩
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  have hbS := hS.bound hR
  have hspb := hR.bb_sp_le
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have hk1' : k = 1 := by omega
    subst hk1'
    obtain ⟨xa, hxa, hxk⟩ := bb_bits_at hxss hn1
    have hx0 := hargs 0 hn1
    obtain ⟨hxsz, hxargs⟩ := hR.core.bb_args hxa (by decide)
    have e0 := (hR.core.rdN hn hl).2.2 0 hn1
    simp only [Nat.add_zero] at e0
    rule_assign [e0]
    rule_assign [(hR.core.rdN hxa).1, (hR.core.rdN hxa).2.1]
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp only [RetQ]; exact BbChk.zero h hR, fun hlen => ?_⟩
    apply WP.bb_loop (fun env0 => BbInv s' env0 "i" [] bs.length
      (fun i => S.drop i = xa.toList.drop i → S = xa.toList))
    · exact ⟨rfl, 0, [], rfl, by simp [bbSets, Env.set], by omega, fun h => by simpa using h⟩
    rintro env s'' ⟨rfl, i, ws, hws, rfl, hi, hresi⟩
    obtain rfl := len_shape 0 hws
    simp only [bbSets, List.zip_nil_right]
    rule_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · apply WP.rule_ret; rule_simp
      refine ⟨c', h, hR, fun _ => ⟨hpre, hsp, hres ?_⟩⟩
      have hS' := hresi (by
        rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by simp; omega)])
      have e1 := bb_take_rev (l := xss) (k := 0) (by omega)
      have hxk' : xss[0] = xa.toList := by
        rw [List.getElem?_eq_getElem (by omega)] at hxk; simpa using hxk
      simp only [Nat.zero_add, List.take_zero, List.reverse_nil] at e1
      rw [e1, hxk', hS']
      simp [bbAddRev]
    have hiS : i < S.length := by omega
    have hix : i < xa.size := by omega
    have hstk := hS.stk hR h hiS
    have h1 := hS.lt hiS
    have h2 := hxargs i hix
    apply WP.guard_lit
    rule_simp [hstk, hS.rd hiS, (hR.core.rdN hxa).2.2 i hix]
    refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbChk.zero h hR, fun he => ?_⟩
    apply WP.assign_loop
    rule_simp
    exact ⟨rfl, i + 1, [], rfl, by simp [bbSets, Env.set], by omega,
      fun hd => hresi (bb_drop_eq_step hiS (by simpa using hix) (by simpa using he) hd)⟩
  rule_assign [bb_uv_sub (show k < 2 ^ 32 by omega) (show 1 ≤ k by omega)]
  have hk' : k - 1 < args.size := by omega
  obtain ⟨xa, hxa, hxk⟩ := bb_bits_at hxss hk'
  have hxi := hargs (k - 1) hk'
  obtain ⟨hxsz, hxargs⟩ := hR.core.bb_args hxa (by decide)
  rule_assign [(hR.core.rdN hn hl).2.2 (k - 1) hk']
  rule_assign [(hR.core.rdN hxa).1, (hR.core.rdN hxa).2.1]
  refine WP.pl_call (bb_pre_spec W sb X c0 c' prems params st sbN S 0) ?_
    ⟨rfl, h, hR, hS, by omega⟩ ?_
  · rule_simp [hSl]
  rintro s1 r1 ⟨c1, h1, hR1, hcase1⟩
  bb_swap h1 hR1
  rcases hcase1 with rfl | ⟨rfl, hpre1, hsp1, L, ⟨hL, hLp⟩, htL⟩
  · rule_simp
    apply WP.guard_lit
    rule_simp [noid]
    exact BbChk.zero h hR
  rule_simp
  apply WP.guard_lit
  rule_simp [hR.bb_ne_noid hsp1]
  rule_assign
  apply WP.bb_push_args h hR args[k - 1] hxa (by simp [IsLeaf, isLeaf])
  refine ⟨by rule_simp, ?_⟩
  intro s2 c2 ok h2 hR2 hcase2
  bb_swap h2 hR2
  rule_simp
  apply WP.guard_lit
  rcases hcase2 with rfl | ⟨rfl, hpre2, hsp2, htx⟩
  · rule_simp
    exact BbChk.zero h hR
  rule_simp
  simp only at htx
  have hpre12 := bb_pre_trans hpre1 hsp1 hpre2
  have hrL : BbRange c2 st c'.k.sp.toNat L := htL.bbRange.frame hpre2 (by omega)
  have hrS : BbRange c2 st sbN S := (hS.frame hpre1 hsp1).frame hpre2 (by omega)
  have hrX : BbRange c2 st c1.k.sp.toNat xa.toList := htx.bbRange
  refine WP.bb_call (bb_ripple_spec W sb X c0 c2 prems params st c'.k.sp.toNat c1.k.sp.toNat sbN
    L xa.toList S false) ?_ ⟨rfl, h, hR, hrL, hrX, hrS⟩ ?_
  · rule_simp [hL, hSl]
  intro r3 hr3
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbChk.zero h hR, fun hr30 => ?_⟩
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp
  intro s3 h3
  have hspx := htx.1
  have hspL := htL.1
  apply WP.assign_loop
  rule_simp
  refine ⟨_, k - 1, c'.k.sp.toNat, L, [BitVec.ofNat 32 (st.id args[k - 1]),
    BitVec.ofNat 32 xa.size, c1.k.sp, c'.k.sp, r3], rfl, by simp [bbSets, Env.set], h3,
    hR.set_sp c1.k.sp (by omega), fun j hj => ?_, by simp only; omega, by omega, by omega,
    by omega, ⟨by simp only; omega, hrL.2⟩, fun H => hres ?_⟩
  · simp only; rw [hpre12 j (by omega), hpre j hj]
  have e1 := bb_take_rev (l := xss) (k := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at e1
  rw [e1]
  have hxk' : xss[k - 1] = xa.toList := by
    rw [List.getElem?_eq_getElem (by omega)] at hxk; simpa using hxk
  rw [hxk']
  refine bb_addRev_step ?_ (bb_preSum_of (by omega) hLp) (hr3 hr30) H
  intro e
  rw [List.reverse_eq_nil_iff, List.take_eq_nil_iff] at e
  rcases e with e | e
  · omega
  · subst e; simp at hxl; omega

end Vbcf.Proof
