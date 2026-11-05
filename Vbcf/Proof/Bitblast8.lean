import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast7

/-!
# Vbcf proofs: the Bitblast family, part 8 — `bb_is_fill`, `bb_shift_limit`, `bb_log2`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- The fill test of a shift, selected by the word `arith` (`bb_is_fill`). -/
def BbFill (st : St) (arith : Nat) (xs : List Nat) (isFill : Nat → Bool) : Prop :=
  (arith = 0 ∧ isFill = isFalseNode st) ∨ (arith = 1 ∧ isFill = isLastOf xs)

theorem VInv.bb_false {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) :
    (BitVec.ofNat 32 (hdrW n) = 9#32) ↔ isFalseNode st i = true := by
  have hf := hc.rep.fits i n hn
  rw [aci_hdr_false hf]
  constructor
  · intro hop
    have hl : IsLeaf n.op := by rw [hop]; decide
    have h0 := hc.bb_leaf_args hn hl
    obtain ⟨op, args⟩ := n
    simp only at hop h0; subst hop
    rw [Array.size_eq_zero_iff] at h0; subst h0
    simp [isFalseNode, isNode, hn]
  · intro hf'
    simp [isFalseNode, isNode, hn] at hf'
    rw [hf']

/-! ## `bb_is_fill` -/

def BbIsFillSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (arith xb f : Nat) (xs : List Nat) (isFill : Nat → Bool),
    FnSpec (State := State) Vbcf.prog "bb_is_fill"
      (fun vs s => vs = [.ptr sb 0, uv arith, uv xb, uv xs.length, uv (st.id f)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st xb xs ∧
        st.lv f ∧ BbFill st arith xs isFill)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (isFill f = true) r s')

theorem bb_is_fill_spec : BbIsFillSpec (State := State) := by
  intro W sb X c0 c prems params st arith xb f xs isFill
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbIsFill) rfl
  rintro vs s ⟨rfl, h, hR, hx, hf, hfill⟩
  simp [bbIsFill, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbIsFill) rfl
  simp only [bbIsFill, Stmt.block, initLocals, List.map]
  have hxb := hx.bound hR
  obtain ⟨nf, hnf⟩ := node_of_lv hf
  rcases hfill with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply WP.ifRet
    rule_simp [hR.core.rdHdr hnf]
    refine ⟨rfl, fun hne => ?_⟩
    rw [← hR.core.bb_false hnf]
    by_cases e : BitVec.ofNat 32 (hdrW nf) = 9#32
    · exact e
    · simp [e] at hne
  apply WP.ifRet
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hx0 => ?_⟩
  have hx1 : 0 < xs.length := by
    rcases xs with _ | _
    · exact absurd rfl hx0
    · simp
  have hli : xs.length - 1 < xs.length := by omega
  have hstk := hx.stk hR h hli
  have e1 := hx.rd hli
  rw [show xb + (xs.length - 1) = xb + xs.length - 1 by omega] at e1
  have hlast := hx.lt hli
  apply WP.rule_ret
  rule_simp [hstk, e1, bb_uv_sub (show xb + xs.length < 2 ^ 32 by omega)
    (show 1 ≤ xb + xs.length by omega)]
  refine ⟨rfl, fun hne => ?_⟩
  have he : xs[xs.length - 1] = f := by
    by_cases e : xs[xs.length - 1] = f
    · exact e
    · simp [e] at hne
  simp only [isLastOf, List.getLast?_eq_getElem?, List.getElem?_eq_getElem hli, he]
  simp

/-! ## `bb_shift_limit` -/

theorem bb_iteArgs {st : St} {r c t e : Nat} (h : st.pool[r]? = some ⟨.boolIte, #[c, t, e]⟩) :
    bbIteArgs st r = some (c, t, e) := by
  simp [bbIteArgs, h]

/-- `r` is `ite(cond, p, f)` with a fill `f`. -/
def BbSLAt (st : St) (cond : Nat) (isFill : Nat → Bool) (r p : Nat) : Prop :=
  ∃ f, st.pool[r]? = some ⟨.boolIte, #[cond, p, f]⟩ ∧ isFill f = true

theorem bb_shiftLimit_of {st : St} {cond : Nat} {isFill : Nat → Bool} :
    ∀ {bs L : List Nat}, L.length = bs.length →
    (∀ (j : Nat) (hj : j < bs.length) (hj' : j < L.length), BbSLAt st cond isFill bs[j] L[j]) →
    Bcf.bbShiftLimit st cond isFill bs = some L
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: bs, p :: L, hl, H => by
    obtain ⟨f, hn, hf⟩ := H 0 (by simp) (by simp)
    have ih := bb_shiftLimit_of (bs := bs) (L := L) (by simpa using hl)
      (fun j hj hj' => H (j + 1) (by simp; omega) (by simp; omega))
    simp only [List.getElem_cons_zero] at hn
    simp [Bcf.bbShiftLimit, bb_iteArgs hn, hf, ih]

def BbShiftLimitSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (cond arith xb bsb : Nat) (xs bs : List Nat) (isFill : Nat → Bool),
    FnSpec (State := State) Vbcf.prog "bb_shift_limit"
      (fun vs s => vs = [.ptr sb 0, uv (st.id cond), uv arith, uv xb, uv xs.length, uv bsb,
          uv bs.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv cond ∧
        BbRange c st xb xs ∧ BbRange c st bsb bs ∧ BbFill st arith xs isFill)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ BbPush W sb X c0 prems params st c
        (fun L => Bcf.bbShiftLimit st cond isFill bs = some L) r s')

theorem bb_shift_limit_spec : BbShiftLimitSpec (State := State) := by
  intro W sb X c0 c prems params st cond arith xb bsb xs bs isFill
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbShiftLimit) rfl
  rintro vs s ⟨rfl, h, hR, hcond, hx, hb, hfill⟩
  simp [bbShiftLimit, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbShiftLimit) rfl
  simp only [bbShiftLimit, Stmt.block, initLocals, List.map, Ty.zero]
  have hbb := hb.bound hR
  have hxb := hx.bound hR
  rule_assign
  apply WP.bb_loop (fun env0 => BbPushInv W sb X c0 prems params st c env0 "i" ["b", "ok"]
    bs.length (fun k L => L.length = k ∧
      ∀ (j : Nat) (hj : j < bs.length) (hj' : j < L.length), BbSLAt st cond isFill bs[j] L[j]))
  · exact ⟨c, 0, [], [0#32, 0#32], rfl, by simp [bbSets, Env.set], h, hR,
      fun _ _ => rfl, Nat.le_refl _, by omega, ⟨rfl, fun j _ hj => by simp at hj⟩, StkTop.nil rfl⟩
  clear h hR
  rintro env s' ⟨c', k, L, ws, hws, rfl, h, hR, hpre, hsp, hk, ⟨hL, hLp⟩, htop⟩
  obtain ⟨wb, wok, rfl⟩ := len_shape 2 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  have hb' := hb.frame hpre hsp
  have hx' := hx.frame hpre hsp
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp
    refine ⟨c', h, hR, Or.inr ⟨(bv_ofNat_toNat _).symm, hpre, hsp, L,
      bb_shiftLimit_of (by omega) hLp, htop⟩⟩
  have hstk := hb'.stk hR h hlt
  have hbk := hb'.lt hlt
  rule_assign [hstk, hb'.rd hlt]
  obtain ⟨nb, hnb⟩ := node_of_lv hbk
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hnb]
  refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hh => ?_⟩
  obtain ⟨cc, t, f, rfl, hcc, ht, hf⟩ := hR.core.bb_hdr3 hnb (op := .boolIte) (by decide)
    (by decide) (by decide) (by decide) hh
  apply WP.ifRet
  rule_simp [hR.core.rd3 hnb]
  refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hcc' => ?_⟩
  subst hcc'
  refine WP.bb_call (bb_is_fill_spec W sb X c0 c' prems params st arith xb f xs isFill) ?_
    ⟨rfl, h, hR, hx', hf, hfill⟩ ?_
  · rule_simp [hR.core.rd3 hnb]
  intro r1 hr1
  rule_simp
  apply WP.ifRet
  rule_simp
  refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hr10 => ?_⟩
  apply WP.rule_push h hR
  rule_simp [hR.core.rd3 hnb]
  intro s2 c2 ok hh2 hP
  obtain ⟨hpre2, hsp2⟩ := hP.bb_pre
  have hpre' : ∀ j, j < c.k.sp.toNat → c2.stk[j]? = c.stk[j]? := fun j hj => by
    rw [hpre2 j (by omega), hpre j hj]
  have h := hh2
  have hR := hP.1
  apply WP.ifRet
  rule_simp
  refine ⟨fun h0 => ?_, fun hok => ?_⟩
  · simp only [LoopQ, RetQ]
    exact BbPush.fail h hR
  obtain ⟨htop2, -⟩ := hP.bb hok htop ht
  apply WP.assign_loop
  rule_simp
  refine ⟨c2, k + 1, L ++ [t], [BitVec.ofNat 32 (st.id bs[k]), ok], rfl,
    by simp [bbSets, Env.set], h, hR, hpre', by omega, by omega, ⟨by simp; omega, fun j hj hj' => ?_⟩,
    htop2⟩
  rcases Nat.lt_or_ge j L.length with hjl | hjl
  · rw [List.getElem_append_left hjl]; exact hLp j hj hjl
  · have hjk : j = k := by simp at hj'; omega
    subst hjk
    rw [List.getElem_append_right (by omega)]
    simp only [hL, Nat.sub_self, List.getElem_cons_zero]
    exact ⟨f, hnb, hr1 hr10⟩

/-! ## `bb_log2` -/

theorem bb_shl1 {k : Nat} (hk : k < 31) : 1#32 <<< k = BitVec.ofNat 32 (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, bv_toNat_ofNat (Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right
    (by decide) hk) (by decide))]
  have : (1#32 : BitVec 32).toNat = 1 := rfl
  rw [this, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Nat.pow_lt_pow_right (by decide) hk) (by decide))]

theorem bb_log2_of {n k : Nat} (h1 : ∀ j, j < k → 2 ^ j < n) (h2 : n ≤ 2 ^ k) :
    k = Bcf.bbLog2 n := by
  unfold Bcf.bbLog2
  rcases k with _ | k
  · simp at h2; simp [h2]
  · have hk := h1 k (by omega)
    have hn : ¬ n ≤ 1 := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    rw [ite_eq_right hn]
    have := (Nat.log2_eq_iff (n := n - 1) (k := k) (by omega)).mpr
      ⟨by omega, by rw [Nat.pow_succ]; rw [Nat.pow_succ] at h2; omega⟩
    omega

def BbLog2Spec : Prop :=
  ∀ (n : Nat),
    FnSpec (State := State) Vbcf.prog "bb_log2" (fun vs _ => vs = [uv n] ∧ n ≤ 255)
      (fun _ s => PureRet s (Bcf.bbLog2 n))

theorem bb_log2_spec : BbLog2Spec (State := State) := by
  intro n
  apply FnSpec.intro' (fn := bbLog2) rfl
  rintro vs s ⟨rfl, hn⟩
  simp [bbLog2, bindParams]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.bb_loop (fun env0 env s' => s' = s ∧ ∃ k, env = env0.set "k" (uv k) ∧ k ≤ 8 ∧
    ∀ j, j < k → 2 ^ j < n)
  · exact ⟨rfl, 0, by simp [Env.set], by omega, fun j hj => absurd hj (by omega)⟩
  rintro env s' ⟨rfl, k, rfl, hk, hlt⟩
  have hk31 : k < 31 := by omega
  have h2k : 2 ^ k ≤ 256 := Nat.pow_le_pow_right (by decide) hk
  embc_simp [uv_lt, bb_shl1 hk31, uv_toNat (show k < 4294967296 by omega),
    show k < 31 by omega, show k < 32 by omega, show (31 : Nat) < 4294967296 by omega,
    show k % 4294967296 = k by omega, show n % 4294967296 = n by omega,
    Nat.mod_eq_of_lt (show 2 ^ k < 4294967296 by omega), show ¬ 31 ≤ k by omega]
  refine ⟨fun hge => ?_, fun hlt' => ?_⟩
  · apply WP.ret
    embc_simp [retPost, PureRet]
    rw [← bb_log2_of hlt (by omega)]
  · apply WP.assign
    embc_simp [LoopQ, uv_add]
    refine ⟨k + 1, rfl, ?_, fun j hj => ?_⟩
    · have : 2 ^ 8 < n → False := fun h => by simp at h; omega
      rcases Nat.lt_or_ge k 8 with h8 | h8
      · omega
      · have : k = 8 := by omega
        subst this; simp at hlt'; omega
    · rcases Nat.lt_or_ge j k with hjk | hjk
      · exact hlt j hjk
      · have : j = k := by omega
        subst this; exact hlt'

end Vbcf.Proof
