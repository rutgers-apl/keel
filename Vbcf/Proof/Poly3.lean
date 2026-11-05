import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly2

/-!
# Vbcf proofs: the Poly family, part 3 — `lin_scale`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Stores into a word range -/

section words
variable {cells : Array EmbC.Val}

theorem WordsAt.plSetOut {base pos : Nat} {ws : List Nat} {v : EmbC.Val} (h : WordsAt cells base ws)
    (hp : pos < base ∨ base + ws.length ≤ pos) : WordsAt (cells.setIfInBounds pos v) base ws := by
  intro k x hx
  have := lt_length_of_getElem? hx
  unfold U
  rw [Array.getElem?_setIfInBounds_ne (by omega)]
  exact h k x hx

theorem WordsAt.plSetSnoc {base pos x : Nat} {ws : List Nat} (h : WordsAt cells base ws)
    (hp : pos = base + ws.length) (hs : pos < cells.size) :
    WordsAt (cells.setIfInBounds pos (uv x)) base (ws ++ [x]) := by
  intro k y hy
  unfold U
  rcases Nat.lt_or_ge k ws.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hy
    rw [Array.getElem?_setIfInBounds_ne (by omega)]
    exact h k y hy
  · rw [List.getElem?_append_right hge] at hy
    have hk : k - ws.length = 0 := by
      rcases Nat.lt_or_ge (k - ws.length) 1 with h1 | h1
      · omega
      · rw [List.getElem?_eq_none (by simpa using h1)] at hy; cases hy
    rw [hk] at hy
    simp at hy; subst hy
    rw [show base + k = pos by omega, Array.getElem?_setIfInBounds_self_of_lt hs]

theorem WordsAt.plNil (base : Nat) : WordsAt cells base [] := fun k x hx => by simp at hx

theorem WordsAt.plSplit {base : Nat} {A B : List Nat} (h : WordsAt cells base (A ++ B)) :
    WordsAt cells base A ∧ WordsAt cells (base + A.length) B := by
  refine ⟨fun k x hx => h k x (by rw [List.getElem?_append_left (lt_length_of_getElem? hx)]; exact hx),
    fun k x hx => ?_⟩
  have := h (A.length + k) x (by rw [List.getElem?_append_right (by omega)]; simpa using hx)
  rwa [← Nat.add_assoc] at this

theorem WordsAt.plJoin {base : Nat} {A B : List Nat} (hA : WordsAt cells base A)
    (hB : WordsAt cells (base + A.length) B) : WordsAt cells base (A ++ B) := by
  intro k x hx
  rcases Nat.lt_or_ge k A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hx
    exact hA k x hx
  · rw [List.getElem?_append_right hge] at hx
    have := hB _ _ hx
    rwa [show base + A.length + (k - A.length) = base + k by omega] at this

theorem WordsAt.plGet {base : Nat} {ws : List Nat} (h : WordsAt cells base ws) {k : Nat}
    (hk : k < ws.length) : cells[base + k]? = some (uv ws[k]) :=
  h k _ (List.getElem?_eq_getElem hk)

end words

/-! ## 64-bit arithmetic of the coefficients -/

/-- A `w`-bit value as a 64-bit word (kept folded so that `simp` leaves it alone). -/
def plV {w : Nat} (x : BitVec w) : BitVec 64 := BitVec.ofNat 64 x.toNat

/-- The low and high words of a value (folded). -/
def plLo {w : Nat} (x : BitVec w) : Nat := x.toNat % 2 ^ 32
def plHi {w : Nat} (x : BitVec w) : Nat := x.toNat / 2 ^ 32

theorem plV_lo {w : Nat} (x : BitVec w) : (plV x).setWidth 32 = BitVec.ofNat 32 (plLo x) := by
  apply BitVec.eq_of_toNat_eq
  simp [plV, plLo]

theorem plV_hi {w : Nat} (hw : w ≤ 64) (x : BitVec w) :
    (plV x >>> 32).setWidth 32 = BitVec.ofNat 32 (plHi x) := by
  have := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hw)
  unfold plV plHi
  rw [pl_hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

theorem plV_eq0 {w : Nat} (hw : w ≤ 64) (x : BitVec w) : (plV x = 0#64) ↔ x = 0#w := by
  have := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hw)
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp [plV] at this
    apply BitVec.eq_of_toNat_eq
    simp; omega
  · rintro rfl; rfl

theorem plV_toNat {w : Nat} (hw : w ≤ 64) (x : BitVec w) : (plV x).toNat = x.toNat := by
  have := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hw)
  simp [plV]; omega

theorem pl_mm {w : Nat} (hw : w ≤ 64) {k m : BitVec 64} {kk : BitVec w} (hk : k.toNat = kk.toNat)
    (hm : m.toNat = 2 ^ w - 1) (y : BitVec w) :
    (k * y.setWidth 64) &&& m = plV (kk * y) := by
  unfold plV
  have hdvd : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_mul, hk,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_mul,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) hw)),
    Nat.mod_mod_of_dvd _ hdvd]
  have := (kk * y).isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ((Nat.mod_lt _ (Nat.two_pow_pos w)))
    (Nat.pow_le_pow_right (by decide) hw))]

theorem pl_lo64 (N : Nat) : (BitVec.ofNat 64 N).setWidth 32 = BitVec.ofNat 32 (N % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem pl_hi64 {N : Nat} (h : N < 2 ^ 64) :
    (BitVec.ofNat 64 N >>> 32).setWidth 32 = BitVec.ofNat 32 (N / 2 ^ 32) := by
  rw [pl_hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem pl_eq0_64 {N : Nat} (h : N < 2 ^ 64) : (BitVec.ofNat 64 N = 0#64) ↔ N = 0 := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp at this; omega
  · rintro rfl; rfl

theorem pl_toNat_lt {w : Nat} (hw : w ≤ 64) (y : BitVec w) : y.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) hw)

/-! ## `scale` on the terms -/

/-- The terms of `Lin.scale k`. -/
def plSc {w : Nat} (k : BitVec w) (ts : List (Nat × BitVec w)) : List (Nat × BitVec w) :=
  (ts.map (fun t => (t.1, k * t.2))).filter (fun t => t.2 ≠ 0)

theorem plSc_snoc {w : Nat} (k : BitVec w) (ts : List (Nat × BitVec w)) (t : Nat × BitVec w) :
    plSc k (ts ++ [t]) = plSc k ts ++ (if k * t.2 = 0 then [] else [(t.1, k * t.2)]) := by
  unfold plSc
  rw [List.map_append, List.filter_append]
  split <;> simp_all

theorem plSc_length_le {w : Nat} (k : BitVec w) (ts : List (Nat × BitVec w)) :
    (plSc k ts).length ≤ ts.length := by
  unfold plSc
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem pl_take_succ_of_drop {α : Type} {l : List α} {i : Nat} {t : α} {rest : List α}
    (h : l.drop i = t :: rest) : l.take (i + 1) = l.take i ++ [t] := by
  have : l[i]? = some t := by rw [← List.head?_drop, h]; rfl
  rw [List.take_add_one, this]; rfl

/-! ## `lin_scale` -/

def LinScaleSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (w b0 : Nat) (p : Lin w) (kk : BitVec w) (k m : BitVec 64),
    FnSpec (State := State) Vbcf.prog "lin_scale"
      (fun vs s => vs = [.ptr sb 0, uv b0, .u64 k, .u64 m] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ 1 ≤ w ∧ w ≤ 64 ∧ m.toNat = 2 ^ w - 1 ∧
        k.toNat = kk.toNat ∧ PlStkW c b0 (plEnc st.cs.pool p))
      (fun _ _ rv s' => rv = none ∧ ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
        (∀ j, j < b0 → c'.stk[j]? = c.stk[j]?) ∧ PlStkW c' b0 (plEnc st.cs.pool (Lin.scale kk p)))

/-- The invariant of the loop of `lin_scale`: `ip` terms done. -/
def PlScInv (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    {w : Nat} (b0 : Nat) (p : Lin w) (kk : BitVec w) (k m : BitVec 64) : Env → (KernelState prog State) → Prop :=
  fun env s' => ∃ c' ip iv jv cv, env = [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("b0", .u32, uv b0),
      ("k", .u64, .u64 k), ("m", .u64, .u64 m),
      ("e", .u32, uv (b0 + (2 + 3 * p.terms.length))), ("i", .u32, uv iv),
      ("j", .u32, uv jv), ("c", .u64, .u64 cv)] ∧
    iv = b0 + 2 + 3 * ip ∧ jv = b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ c'.k.sp = c.k.sp ∧
    ip ≤ p.terms.length ∧ (∀ j, j < b0 → c'.stk[j]? = c.stk[j]?) ∧
    WordsAt c'.stk b0 (plW (kk * p.const).toNat ++ plTerms st.cs.pool (plSc kk (p.terms.take ip))) ∧
    WordsAt c'.stk iv (plTerms st.cs.pool (p.terms.drop ip))

theorem lin_scale_spec : LinScaleSpec (State := State) := by
  intro W sb X c0 c prems params st w b0 p kk k m
  have hs := prog_ck
  apply FnSpec.intro' (fn := linScale) rfl
  rintro vs s ⟨rfl, h, hR, hw1, hw64, hm, hk, hst⟩
  simp [linScale, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hsp := hst.1
  simp only [plEnc_length] at hsp
  have hspw : c.k.sp = BitVec.ofNat 32 (b0 + (2 + 3 * p.terms.length)) := by
    rw [← hsp]; exact (bv_ofNat_toNat _).symm
  have hstk := hR.stk_eq h (by omega)
  have hsz := hR.stk_size h (by omega)
  rule_assign [hspw]
  -- `c = lin_get64(st, b0);`
  have hc0 := hst.2.plGet (k := 0) (by simp only [plEnc_length]; omega)
  have hc1 := hst.2.plGet (k := 1) (by simp only [plEnc_length]; omega)
  simp only [plEnc, plW, List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_zero] at hc0 hc1
  apply WP.pl_get64 h hR b0 p.const.toNat (by omega) (pl_toNat_lt hw64 _) hc0 hc1
  refine ⟨by rule_simp, ?_⟩
  rule_simp
  rule_assign [pl_mm hw64 hk hm]
  -- the constant
  apply WP.seq
  apply WP.ck_store .stk h (by rfl) hstk
  rule_simp [hstk, plV_lo, uv_toNat (show b0 < 4294967296 by omega)]
  refine ⟨by omega, ?_⟩
  intro s1 h
  have hR1 := hR.set_stk b0 (uv (plLo (kk * p.const)))
  have hstk1 := hR1.stk_eq h (by simp; omega)
  apply WP.seq
  apply WP.ck_store .stk h (by rfl) hstk1
  rule_simp [hstk, plV_hi hw64, uv_toNat (show b0 + 1 < 4294967296 by omega)]
  refine ⟨rfl, by omega, ?_⟩
  intro s2 h
  have hR2 := hR1.set_stk (b0 + 1) (uv (plHi (kk * p.const)))
  rule_assign
  rule_assign
  have hw2 := (hst.2.plSplit).2
  simp only [plW_length] at hw2
  apply WP.loop_seq (PlScInv W sb X c0 c prems params st b0 p kk k m)
  · refine ⟨_, 0, b0 + 2, b0 + 2, plV (kk * p.const), by simp, by simp, by simp [plSc], h, hR2, rfl, by omega,
      fun j hj => ?_, ?_, ?_⟩
    · simp only
      rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega)]
    · simp only [List.take_zero, plSc, List.map_nil, List.filter_nil, plTerms_nil, List.append_nil]
      have := (((WordsAt.plNil (cells := c.stk) b0).plSetSnoc (x := plLo (kk * p.const))
        (pos := b0) (by simp) (by omega)).plSetSnoc (x := plHi (kk * p.const)) (pos := b0 + 1)
        (by simp) (by simp; omega))
      exact this
    · simp only [List.drop_zero]
      exact (hw2.plSetOut (by omega)).plSetOut (by omega)
  clear h hR hR1 hR2 hstk1 hc0 hc1
  rintro env s3 ⟨c3, ip, iv, jv, cv, rfl, rfl, rfl, h, hR, hsp3, hip, hpre, hlo, hhi⟩
  have hjle := plSc_length_le kk (p.terms.take ip)
  simp only [List.length_take] at hjle
  have hstk3 := hR.stk_eq h (by rw [hsp3]; omega)
  have hsz3 := hR.stk_size h (by rw [hsp3]; omega)
  rw [hsp3] at hsz3
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- `st->sp = j;`
    have hipe : ip = p.terms.length := by omega
    subst hipe
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s4 h4
    simp only [retPost]
    have hle := plSc_length_le kk p.terms
    refine ⟨trivial, _, h4, hR.set_sp _ ?_, hpre, ?_, ?_⟩
    · rw [hsp3, uv_toNat (by omega)]; omega
    · simp only [List.take_length] at hlo ⊢
      rw [uv_toNat (by omega)]
      simp [plEnc, Lin.scale, plSc]
      omega
    · simp only [List.take_length] at hlo
      exact hlo
  have hip' : ip < p.terms.length := by omega
  obtain ⟨t, rest, hdrop⟩ : ∃ t rest, p.terms.drop ip = t :: rest := by
    cases hd : p.terms.drop ip with
    | nil => rw [List.drop_eq_nil_iff] at hd; omega
    | cons t rest => exact ⟨t, rest, rfl⟩
  have htake := pl_take_succ_of_drop hdrop
  have hdrop' : p.terms.drop (ip + 1) = rest := by
    rw [← List.drop_drop, hdrop]; rfl
  rw [hdrop] at hhi
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop, List.length_cons] at hlen
  have r0 := hhi.plGet (k := 0) (by simp [plTerms_cons])
  have r1 := hhi.plGet (k := 1) (by simp [plTerms_cons])
  have r2 := hhi.plGet (k := 2) (by simp [plTerms_cons])
  simp only [plTerms_cons, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at r0 r1 r2
  apply WP.pl_get64 h hR (b0 + 2 + 3 * ip + 1) t.2.toNat (by rw [hsp3]; omega)
    (pl_toNat_lt hw64 _) r1 r2
  refine ⟨by rule_simp, ?_⟩
  rule_simp
  rule_assign [pl_mm hw64 hk hm]
  have hO := plSc_snoc kk (p.terms.take ip) t
  rw [← htake] at hO
  by_cases hz : kk * t.2 = 0
  · rw [ite_eq_left hz, List.append_nil] at hO
    have hz' : kk * t.2 = 0#w := hz
    apply WP.ite_seq
    rule_simp [plV_eq0 hw64, hz']
    apply WP.assign_loop
    rule_simp
    refine ⟨c3, ip + 1, b0 + 2 + 3 * (ip + 1), b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length,
      plV 0#w, ?_, rfl, by rw [hO], h, hR, hsp3, by omega, hpre, ?_, ?_⟩
    · rw [show b0 + 2 + 3 * (ip + 1) = b0 + 2 + 3 * ip + 3 by omega]
    · rw [hO]; exact hlo
    · rw [hdrop']
      have := (WordsAt.plSplit (A := [_, _, _]) hhi).2
      simpa [Nat.add_assoc, Nat.mul_add] using this
  · rw [ite_eq_right hz] at hO
    have hz' : ¬ kk * t.2 = 0#w := hz
    apply WP.ite_seq
    rule_simp [plV_eq0 hw64, hz']
    have hjb : b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length < 4294967296 := by omega
    have hib : b0 + 2 + 3 * ip < 4294967296 := by omega
    apply WP.seq
    apply WP.ck_store .stk h (by rfl) hstk3
    rule_simp [hstk3, rd_u32 r0, uv_toNat hjb, uv_toNat hib]
    refine ⟨by omega, ?_⟩
    intro s5 h
    have hR5 := hR.set_stk (b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length) (uv (offs st.cs.pool t.1))
    apply WP.seq
    apply WP.ck_store .stk h (by rfl) hstk3
    have hjb1 : b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 1 < 4294967296 := by omega
    have hjb2 : b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 2 < 4294967296 := by omega
    rule_simp [hstk3, plV_lo, uv_toNat hjb, uv_toNat hjb1]
    refine ⟨by omega, ?_⟩
    intro s6 h
    have hR6 := hR5.set_stk (b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 1)
      (uv (plLo (kk * t.2)))
    apply WP.seq
    apply WP.ck_store .stk h (by rfl) hstk3
    rule_simp [hstk3, plV_hi hw64, uv_toNat hjb, uv_toNat hjb2]
    refine ⟨by omega, ?_⟩
    intro s7 h
    have hR7 := hR6.set_stk (b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 2)
      (uv (plHi (kk * t.2)))
    apply WP.assign
    rule_simp [LoopQ]
    apply WP.assign_loop
    rule_simp
    have hlo' := ((hlo.plSetSnoc (x := offs st.cs.pool t.1)
      (pos := b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length) (by simp; omega) (by omega)).plSetSnoc
      (x := plLo (kk * t.2)) (pos := b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 1)
      (by simp; omega) (by simp; omega)).plSetSnoc
      (x := plHi (kk * t.2)) (pos := b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 2)
      (by simp; omega) (by simp; omega)
    have hhi' := (((WordsAt.plSplit (A := [_, _, _]) hhi).2.plSetOut
      (pos := b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length) (v := uv (offs st.cs.pool t.1))
      (by simp; omega)).plSetOut
      (pos := b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 1) (v := uv (plLo (kk * t.2)))
      (by simp; omega)).plSetOut
      (pos := b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 2) (v := uv (plHi (kk * t.2)))
      (by simp; omega)
    refine ⟨_, ip + 1, b0 + 2 + 3 * (ip + 1), b0 + 2 + 3 * ((plSc kk (p.terms.take ip)).length + 1),
      plV (kk * t.2), ?_, rfl, by rw [hO]; simp, h, hR7, hsp3, by omega, fun j hj => ?_, ?_, ?_⟩
    · rw [show b0 + 2 + 3 * (ip + 1) = b0 + 2 + 3 * ip + 3 by omega,
        show b0 + 2 + 3 * ((plSc kk (p.terms.take ip)).length + 1) =
          b0 + 2 + 3 * (plSc kk (p.terms.take ip)).length + 3 by omega]
    · simp only
      rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega),
        Array.getElem?_setIfInBounds_ne (by omega)]
      exact hpre j hj
    · rw [hO, plTerms_append, plTerms_cons]
      simpa [plLo, plHi] using hlo'
    · rw [hdrop']
      simpa [Nat.add_assoc, Nat.mul_add] using hhi'

end Vbcf.Proof
