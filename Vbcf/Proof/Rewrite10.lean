import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite9

/-!
# Vbcf proofs: the Rewrite family, part 10 — rewrite id 0 (`ruleRewrite0`)

`rw0_and_half` (`andHalf`), `rw0_and_split` (`rw0AndSplit`, a loop over the pieces), `rw0_repeat` (`rw0Repeat`),
`rw0_distinct` (`rw0Distinct`), `rw_zero` (`ruleRewrite0`).  All read only.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-! ## Header fields -/

section hdr
variable {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n)
include hf

/-- `hdr & 0xffff`: code and arity. -/
theorem rw_hdr_ffff :
    BitVec.ofNat 32 (hdrW n) &&& 65535#32 = BitVec.ofNat 32 (opC n.op + tailLen n * 256) := by
  have h1 := opC_lt n.op; have h2 := hf.tailLen
  rw [cw_andffff]; congr 1; unfold hdrW; omega

/-- `(hdr & 0xffff) == (code | 2 << 8)`. -/
theorem rw_hdr_code2 (k : Nat) (hk : k < 256) :
    (BitVec.ofNat 32 (opC n.op + tailLen n * 256) = BitVec.ofNat 32 (k + 512)) ↔
      (opC n.op = k ∧ tailLen n = 2) := by
  have h1 := opC_lt n.op; have h2 := hf.tailLen
  rw [uv_inj (by omega) (by omega)]; omega

theorem rw_hdr_hi : BitVec.ofNat 32 (hdrW n) >>> 24 = BitVec.ofNat 32 (opHi n.op) := by
  have := hf.hi
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_24, bv_toNat_ofNat (hdrW_lt hf), bv_toNat_ofNat (by omega), hdrW_hi hf]

theorem rw_hdr_lo : BitVec.ofNat 32 (hdrW n) >>> 16 &&& 255#32 = BitVec.ofNat 32 (opLo n.op) := by
  have := hf.lo
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_shr_16, bv_toNat_ofNat (hdrW_lt hf), bv_toNat_ofNat (by omega), hdrW_lo hf]

end hdr

/-- A node whose header says "code `k`, two arguments". -/
theorem rw_two_args {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st) {i : Nat}
    {n : Node} (hn : st.pool[i]? = some n) {op : Op} (hop : n.op = op) (hl : ¬ IsLeaf op)
    (h2 : tailLen n = 2) (hi : st.lv i := by vlv) :
    ∃ p q, n = ⟨op, #[p, q]⟩ ∧ st.lv p ∧ st.lv q := by
  obtain ⟨args, rfl, -, -, hargs⟩ := hc.argsN hn hop hl
  rw [tailLen_of_not_leaf hl] at h2
  obtain ⟨p, q, rfl⟩ := array_eq_two h2
  exact ⟨p, q, rfl, hargs 0 (by simp), hargs 1 (by simp)⟩

/-! ## `rw0_and_half` -/

def Rw0HalfSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (hn x y hi lo : Nat),
    FnSpec (State := State) Vbcf.prog "rw0_and_half"
      (fun vs s => vs = [.ptr sb 0, uv (st.id hn), uv (st.id x), uv (st.id y),
          uv hi, uv lo] ∧ Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv hn ∧
        st.lv x ∧ st.lv y ∧ hi < 256 ∧ lo < 256)
      (fun _ s rv s' => ∃ v, rv = some (.u32 v) ∧ (s' = s ∧ (v ≠ 0#32 → andHalf st hn x y hi lo = true)))

theorem rw0_and_half_spec : Rw0HalfSpec (State := State) := by
  intro W sb X c0 c prems params st hn x y hi lo
  have hs := prog_ck
  apply FnSpec.intro' (fn := rw0AndHalf) rfl
  rintro vs s ⟨rfl, h, hR, hhn, hx, hy, hhi, hlo⟩
  simp [rw0AndHalf, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rw0AndHalf) rfl
  simp only [rw0AndHalf, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨n, hnn⟩ := node_of_lv hhn
  have hf := hR.core.rep.fits _ _ hnn
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnn, rw_hdr_ffff hf,
    show (592#32 : BitVec 32) = BitVec.ofNat 32 (80 + 512) from rfl, rw_hdr_code2 hf 80 (by omega)]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun w hw h2 => ?_⟩
  obtain ⟨p, q, rfl, hp, hq⟩ := rw_two_args hR.core hnn hw (by simp [IsLeaf, isLeaf]) h2
  obtain ⟨np, hnp⟩ := node_of_lv hp
  obtain ⟨nq, hnq⟩ := node_of_lv hq
  have hfp := hR.core.rep.fits _ _ hnp
  have hfq := hR.core.rep.fits _ _ hnq
  have hrd := hR.core.rd2 hnn (by simp [IsLeaf, isLeaf])
  rule_assign [hrd]
  rule_assign [hrd]
  rule_assign [hR.core.rdHdr hnp]
  rule_assign [hR.core.rdHdr hnq]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun h1 l1 hpe h2 l2 hqe => ?_⟩
  have hhp := rw_hdr_hi hfp
  have hlp := rw_hdr_lo hfp
  have hhq := rw_hdr_hi hfq
  have hlq := rw_hdr_lo hfq
  rw [hpe] at hhp hlp
  rw [hqe] at hhq hlq
  obtain ⟨a, rfl, ha⟩ := hR.core.args1 hnp hpe
  obtain ⟨b, rfl, hb⟩ := hR.core.args1 hnq hqe
  have hrp := hR.core.rd1 hnp (by simp [IsLeaf, isLeaf])
  have hrq := hR.core.rd1 hnq (by simp [IsLeaf, isLeaf])
  rule_assign [hrp]
  rule_assign [hrq]
  apply WP.ret
  rule_simp [RetQ, hhp, hlp, hhq, hlq]
  have := hfp.hi; have := hfp.lo; have := hfq.hi; have := hfq.lo
  simp only [opHi, opLo] at *
  rw [uv_inj (by omega) (by omega), uv_inj (by omega) (by omega), uv_inj (by omega) (by omega),
    uv_inj (by omega) (by omega)]
  intro e1 e2 e3 e4 e5
  subst e1 e2 e3 e4
  simp only [andHalf, and2Of, extractOf, St.node, hnn, hnp, hnq]
  simp
  by_cases hax : a = x
  · by_cases hby : b = y
    · simp [hax, hby]
    · have := e5 (fun _ => hby); simp [this]
  · have := e5 (fun h => absurd h hax); simp [this]

/-- `x = rw0_and_half(st, …); rest`. -/
theorem WP.rw0_half_call {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat}
    {st : VSt} {env : Env} {s : (KernelState prog State)} {Q : (Post prog State)} {x : Var} {args : List Expr} {rest : Stmt}
    (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (hn a b hi lo : Nat)
    (hhn : st.lv hn) (ha : st.lv a) (hb : st.lv b) (hhi : hi < 256)
    (hlo : lo < 256)
    (H : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, uv (st.id hn),
        uv (st.id a), uv (st.id b), uv hi, uv lo] ∧
      ∀ v, (v ≠ 0#32 → andHalf st hn a b hi lo = true) →
        match env.assign s.mem x (.u32 v) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s) :
    WP Vbcf.prog (.seq (.call (some x) "rw0_and_half" args) rest) Q env s := by
  apply WP.call_seq (rw0_and_half_spec W sb X c0 c prems params st hn a b hi lo) H.1
    ⟨rfl, h, hR, hhn, ha, hb, hhi, hlo⟩
  rintro rv s' ⟨v, rfl, rfl, hv⟩
  exact H.2 v hv

/-! ## `rw0_and_split` -/

def Rw0SplitSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (a b : Nat),
    FnSpec (State := State) Vbcf.prog "rw0_and_split"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv a ∧ st.lv b)
      (fun _ s rv s' => ∃ v, rv = some (.u32 v) ∧ (s' = s ∧ (v ≠ 0#32 → Bcf.rw0AndSplit st a b = true)))

/-- `andPieces` over the tail from piece `i`, when piece `i` is the last. -/
theorem andPieces_drop_last {st : St} {x y e i lo : Nat} {hs : List Nat} (hi : i < hs.length)
    (hlast : i + 1 = hs.length) (hp : pieceLo st hs[i] = some lo)
    (hh : andHalf st hs[i] x y e lo = true) (h0 : lo = 0) :
    andPieces st x y e (hs.drop i) = true := by
  rw [List.drop_eq_getElem_cons hi]
  have hd : hs.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
  subst h0
  simp [andPieces, hp, hh, hd]

/-- `andPieces` over the tail from piece `i`, when another piece follows. -/
theorem andPieces_drop_next {st : St} {x y e i lo : Nat} {hs : List Nat} (hi : i + 1 < hs.length)
    (hp : pieceLo st hs[i] = some lo) (hh : andHalf st hs[i] x y e lo = true) (h1 : 1 ≤ lo)
    (hr : andPieces st x y (lo - 1) (hs.drop (i + 1)) = true) :
    andPieces st x y e (hs.drop i) = true := by
  rw [List.drop_eq_getElem_cons (by omega)]
  have hd : (hs.drop (i + 1)).isEmpty = false := by
    rw [List.drop_eq_getElem_cons hi]; rfl
  simp only [andPieces, hp, hh, hd, Bool.true_and, Bool.false_eq_true, ↓reduceIte, hr, Bool.and_true,
    decide_eq_true_eq]
  exact h1

/-- The locals of `rw0_and_split`. -/
def rw0SplitEnv (sb a b w x y n : Nat) (i e hh p lo ok : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, uv a), ("b", .u32, uv b),
    ("w", .u32, uv w), ("x", .u32, uv x), ("y", .u32, uv y), ("n", .u32, uv n),
    ("i", .u32, .u32 i), ("e", .u32, .u32 e), ("h", .u32, .u32 hh), ("p", .u32, .u32 p),
    ("lo", .u32, .u32 lo), ("ok", .u32, .u32 ok)]

/-- The loop invariant of `rw0_and_split`: at piece `i`, expecting it to end at bit `e`,
the pieces from `i` on checking (`andPieces … e`) implies the whole check. -/
def Rw0SplitInv (st : VSt) (sb a b w x y : Nat) (hs : Array Nat) (s : (KernelState prog State)) (env' : Env)
    (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ ∃ i e hh p lo ok, env' = rw0SplitEnv sb (st.id a) (st.id b) w (st.id x) (st.id y) hs.size
      (BitVec.ofNat 32 i) (BitVec.ofNat 32 e) hh p lo ok ∧ i < hs.size ∧ e < 256 ∧
    (andPieces st x y e (hs.toList.drop i) = true → andPieces st x y (w - 1) hs.toList = true)

theorem rw0_and_split_spec : Rw0SplitSpec (State := State) := by
  intro W sb X c0 c prems params st a b
  have hs := prog_ck
  apply FnSpec.intro' (fn := rw0AndSplit) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb⟩
  simp [rw0AndSplit, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rw0AndSplit) rfl
  simp only [rw0AndSplit, Stmt.block, initLocals, List.map, Ty.zero]
  have hl : ∀ w, ¬ IsLeaf (Op.bvAnd w) := fun w => by simp [IsLeaf, isLeaf]
  have hl' : ∀ w, ¬ IsLeaf (Op.bvConcat w) := fun w => by simp [IsLeaf, isLeaf]
  obtain ⟨na, hna⟩ := node_of_lv ha
  have hfa := hR.core.rep.fits _ _ hna
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hna, rw_hdr_ffff hfa,
    show (592#32 : BitVec 32) = BitVec.ofNat 32 (80 + 512) from rfl, rw_hdr_code2 hfa 80 (by omega)]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun w hw h2 => ?_⟩
  have hla := rw_hdr_lo hfa
  rw [hw] at hla
  have := hfa.lo; rw [hw] at this; simp only [opLo] at this hla
  obtain ⟨x, y, rfl, hx, hy⟩ := rw_two_args hR.core hna hw (hl w) h2
  have hrda := hR.core.rd2 hna (hl w)
  rule_assign [hR.core.rdHdr hna, hla]
  rule_assign [hrda]
  rule_assign [hrda]
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  have hfb := hR.core.rep.fits _ _ hnb
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnb]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun w' hop' => ?_⟩
  have hlb := rw_hdr_lo hfb
  rw [hop'] at hlb
  have := hfb.lo; rw [hop'] at this; simp only [opLo] at this hlb
  obtain ⟨ys, rfl, hsz, -, hys⟩ := hR.core.argsN hnb hop' (hl' w')
  obtain ⟨hhb, harb, hcb⟩ := hR.core.rdN hnb (hl' w')
  apply WP.guard_lit
  rule_simp [hhb, hlb]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hww => ?_⟩
  subst hww
  rule_assign [hhb, harb]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hn2 hw0 => ?_⟩
  have hw1 : BitVec.ofNat 32 w - 1#32 = BitVec.ofNat 32 (w - 1) := cw_sub (by omega) (by omega)
  rule_assign [hw1]
  apply WP.loop_seq (Rw0SplitInv st sb a b w x y ys s)
  · exact ⟨rfl, 0, w - 1, 0#32, 0#32, 0#32, 0#32, rfl, by omega, by omega, fun h => by simpa using h⟩
  rintro env s1 ⟨rfl, i, e, hh, p0, lo0, ok0, rfl, hi, he, hpre⟩
  simp only [rw0SplitEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · exact absurd hge (by omega)
  have hhi := hys i hi
  rule_assign [hcb i hi]
  obtain ⟨nh, hnh⟩ := node_of_lv hhi
  have hfh := hR.core.rep.fits _ _ hnh
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnh, rw_hdr_ffff hfh,
    show (592#32 : BitVec 32) = BitVec.ofNat 32 (80 + 512) from rfl, rw_hdr_code2 hfh 80 (by omega)]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun wh hwh h2h => ?_⟩
  obtain ⟨p, q, rfl, hp, hq⟩ := rw_two_args hR.core hnh hwh (hl wh) h2h
  rule_assign [hR.core.rd2 hnh (hl wh)]
  obtain ⟨np, hnp⟩ := node_of_lv hp
  have hfp := hR.core.rep.fits _ _ hnp
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnp]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun phi plo hpe => ?_⟩
  have hlp := rw_hdr_lo hfp
  rw [hpe] at hlp
  have := hfp.lo; rw [hpe] at this; simp only [opLo] at this hlp
  obtain ⟨z, rfl, hz⟩ := hR.core.args1 hnp hpe
  rule_assign [hR.core.rdHdr hnp, hlp]
  apply WP.rw0_half_call h hR (hn := ys[i]) (a := x) (b := y) (hi := e) (lo := plo) hhi hx hy he
    (by omega)
  refine ⟨by rule_simp, fun v1 hv1 => ?_⟩
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hv1' => ?_⟩
  have hpl : pieceLo st ys.toList[i] = some plo := by
    simp [pieceLo, and2Of, extractOf, St.node, hnh, hnp]
  have hhalf : andHalf st ys.toList[i] x y e plo = true := by simpa using hv1 hv1'
  have hfin : andPieces st x y (w - 1) ys.toList = true → Bcf.rw0AndSplit st a b = true := by
    intro hw'
    simp only [Bcf.rw0AndSplit, and2Of, St.node, hna, hnb]
    simp [hn2, hw']
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hlast => ?_, fun hlast => ?_⟩
  · apply WP.ret
    rule_simp [LoopQ, RetQ]
    intro hlo0
    exact hfin (hpre (andPieces_drop_last (by simpa using hi) (by simpa using hlast) hpl hhalf hlo0))
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hlo1 => ?_⟩
  have hlo1' : BitVec.ofNat 32 plo - 1#32 = BitVec.ofNat 32 (plo - 1) := cw_sub (by omega) (by omega)
  rule_assign [hlo1']
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, i + 1, plo - 1, _, _, _, _, rfl, by omega, by omega, fun hr => ?_⟩
  exact hpre (andPieces_drop_next (by simp; omega) hpl hhalf (by omega) hr)

/-! ## `rw0_repeat` -/

def Rw0RepeatSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (a b : Nat),
    FnSpec (State := State) Vbcf.prog "rw0_repeat"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv a ∧ st.lv b)
      (fun _ s rv s' => ∃ v, rv = some (.u32 v) ∧ (s' = s ∧ (v ≠ 0#32 → Bcf.rw0Repeat st a b = true)))

/-- The locals of `rw0_repeat`. -/
def rw0RepEnv (sb a b w k y : Nat) (i : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, uv a), ("b", .u32, uv b),
    ("w", .u32, uv w), ("k", .u32, uv k), ("y", .u32, uv y), ("i", .u32, .u32 i)]

def Rw0RepInv (sb a b w k y yi : Nat) (ys : Array Nat) (s : (KernelState prog State)) (env' : Env) (s' : (KernelState prog State)) :
    Prop :=
  s' = s ∧ ∃ i, env' = rw0RepEnv sb a b w k y (BitVec.ofNat 32 i) ∧ i ≤ k ∧
    ∀ j (hj : j < ys.size), j < i → ys[j] = yi

theorem rw0_repeat_spec : Rw0RepeatSpec (State := State) := by
  intro W sb X c0 c prems params st a b
  have hs := prog_ck
  apply FnSpec.intro' (fn := rw0Repeat) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb⟩
  simp [rw0Repeat, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rw0Repeat) rfl
  simp only [rw0Repeat, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨na, hna⟩ := node_of_lv ha
  have hfa := hR.core.rep.fits _ _ hna
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hna]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun w k hop => ?_⟩
  have hla := rw_hdr_lo hfa
  have hha := rw_hdr_hi hfa
  have hlo := hfa.lo
  have hhi := hfa.hi
  rw [hop] at hla hha hlo hhi
  simp only [opLo, opHi] at hla hha hlo hhi
  obtain ⟨y, rfl, hy⟩ := hR.core.args1 hna hop
  have hrda := hR.core.rd1 hna (by simp [IsLeaf, isLeaf])
  rule_assign [hrda, hla]
  rule_assign [hrda, hha]
  rule_assign [hrda]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hk1 => ?_, fun hk1 => ?_⟩
  · subst hk1
    apply WP.ret
    rule_simp [LoopQ, RetQ]
    intro hby
    simp [Bcf.rw0Repeat, St.node, hna, hby]
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  have hfb := hR.core.rep.fits _ _ hnb
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnb]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun w' hop' => ?_⟩
  have hlb := rw_hdr_lo hfb
  rw [hop'] at hlb
  have := hfb.lo; rw [hop'] at this; simp only [opLo] at this hlb
  obtain ⟨ys, rfl, hsz, -, hys⟩ := hR.core.argsN hnb hop' (by simp [IsLeaf, isLeaf])
  obtain ⟨hhb, harb, hcb⟩ := hR.core.rdN hnb (by simp [IsLeaf, isLeaf])
  apply WP.guard_lit
  rule_simp [hhb, hlb]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hww => ?_⟩
  subst hww
  apply WP.guard_lit
  rule_simp [hhb, harb]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hsk => ?_⟩
  apply WP.loop_seq (Rw0RepInv sb (st.id a) (st.id b) w k (st.id y) y ys s)
  · exact ⟨rfl, 0, rfl, by omega, fun j _ hj => absurd hj (by omega)⟩
  rintro env s1 ⟨rfl, i, rfl, hi, hall⟩
  simp only [rw0RepEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.ret
    rule_simp [RetQ]
    simp only [Bcf.rw0Repeat, St.node, hna, hnb]
    simp [hk1]
    rw [List.eq_replicate_iff]
    refine ⟨by simp; omega, fun z hz => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
    simp at hj
    simpa using hall j hj (by omega)
  have hysi := hys i (by omega)
  apply WP.guard_lit
  rule_simp [hcb i (by omega)]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hyi => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, i + 1, rfl, by omega, fun j hj hji => ?_⟩
  rcases Nat.lt_or_ge j i with h' | h'
  · exact hall j hj h'
  · have : j = i := by omega
    subst this; exact hyi

/-! ## `rw0_distinct` -/

def Rw0DistinctSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (a b : Nat),
    FnSpec (State := State) Vbcf.prog "rw0_distinct"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv a ∧ st.lv b)
      (fun _ s rv s' => ∃ v, rv = some (.u32 v) ∧ (s' = s ∧ (v ≠ 0#32 → Bcf.rw0Distinct st a b = true)))

theorem rw0_distinct_spec : Rw0DistinctSpec (State := State) := by
  intro W sb X c0 c prems params st a b
  have hs := prog_ck
  apply FnSpec.intro' (fn := rw0Distinct) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb⟩
  simp [rw0Distinct, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rw0Distinct) rfl
  simp only [rw0Distinct, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨na, hna⟩ := node_of_lv ha
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hna]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hopa => ?_⟩
  obtain ⟨a1, a2, rfl, ha1, ha2⟩ := hR.core.args2 hna hopa
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnb]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hopb => ?_⟩
  obtain ⟨e, rfl, he⟩ := hR.core.args1 hnb hopb
  rule_assign [hR.core.rd1 hnb]
  obtain ⟨ne, hne⟩ := node_of_lv he
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hne]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hope => ?_⟩
  obtain ⟨e1, e2, rfl, he1, he2⟩ := hR.core.args2 hne hope
  apply WP.ret
  rule_simp [RetQ, hR.core.rd2 hna, hR.core.rd2 hne]
  intro h1 h2
  simp [Bcf.rw0Distinct, St.node, hna, hnb, hne, h1, h2]

/-! ## `rw_zero` -/

def RwZeroSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (e : Nat),
    FnSpec (State := State) Vbcf.prog "rw_zero"
      (fun vs s => vs = [.ptr sb 0, uv (st.id e)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv e)
      (fun _ s rv s' => ∃ v, rv = some (.u32 v) ∧ (s' = s ∧ (v ≠ 0#32 → ruleRewrite0 st e = true)))

theorem rw_zero_spec : RwZeroSpec (State := State) := by
  intro W sb X c0 c prems params st e
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwZero) rfl
  rintro vs s ⟨rfl, h, hR, he⟩
  simp [rwZero, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwZero) rfl
  simp only [rwZero, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨ne, hne⟩ := node_of_lv he
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hne]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hop => ?_⟩
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hne hop
  have hz : ruleRewrite0 st e = (Bcf.rw0AndSplit st a b || Bcf.rw0Repeat st a b ||
      Bcf.rw0Distinct st a b) := by
    simp [ruleRewrite0, St.node, hne, isEqNode]
  rule_assign [hR.core.rd2 hne]
  rule_assign [hR.core.rd2 hne]
  apply WP.call_seq (rw0_and_split_spec W sb X c0 c prems params st a b) (by rule_simp)
    ⟨rfl, h, hR, ha, hb⟩
  rintro rv s1 ⟨v1, rfl, rfl, hv1⟩
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun hne1 => ⟨rfl, fun _ => by rw [hz, hv1 hne1]; rfl⟩, fun hv1' => ?_⟩
  apply WP.call_seq (rw0_repeat_spec W sb X c0 c prems params st a b) (by rule_simp)
    ⟨rfl, h, hR, ha, hb⟩
  rintro rv s2 ⟨v2, rfl, rfl, hv2⟩
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun hne2 => ⟨rfl, fun _ => by rw [hz, hv2 hne2]; simp⟩, fun hv2' => ?_⟩
  apply WP.call_seq (rw0_distinct_spec W sb X c0 c prems params st a b) (by rule_simp)
    ⟨rfl, h, hR, ha, hb⟩
  rintro rv s3 ⟨v3, rfl, rfl, hv3⟩
  rule_simp
  apply WP.ret
  rule_simp [RetQ]
  intro hne3
  rw [hz, hv3 hne3]; simp

end Vbcf.Proof
