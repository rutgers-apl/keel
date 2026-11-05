import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly3

/-!
# Vbcf proofs: the Poly family, part 4 — `lin_add`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Reading a form on the stack -/

section read
variable {cells : Array EmbC.Val} {pool : Pool} {w : Nat}

theorem pl_words_drop {base : Nat} {L : Lin w} (h : WordsAt cells base (plEnc pool L)) (ip : Nat) :
    WordsAt cells (base + 2 + 3 * ip) (plTerms pool (L.terms.drop ip)) := by
  have h1 := (WordsAt.plSplit (A := plW L.const.toNat) h).2
  rw [← List.take_append_drop ip L.terms, plTerms_append] at h1
  have h2 := (WordsAt.plSplit h1).2
  have hl : (L.terms.take ip).length = ip ∨ L.terms.length < ip := by
    rw [List.length_take]; omega
  rcases hl with hl | hl
  · simpa [hl, Nat.add_assoc] using h2
  · rw [List.drop_eq_nil_of_le (by omega)]
    exact WordsAt.plNil _

theorem pl_read_term {base ip : Nat} {L : Lin w} {t : Nat × BitVec w}
    {rest : List (Nat × BitVec w)} (h : WordsAt cells base (plEnc pool L))
    (hd : L.terms.drop ip = t :: rest) :
    cells[base + 2 + 3 * ip]? = some (uv (offs pool t.1)) ∧
    cells[base + 2 + 3 * ip + 1]? = some (uv (t.2.toNat % 2 ^ 32)) ∧
    cells[base + 2 + 3 * ip + 2]? = some (uv (t.2.toNat / 2 ^ 32)) := by
  have h1 := pl_words_drop h ip
  rw [hd, plTerms_cons] at h1
  exact ⟨by simpa using h1.plGet (k := 0) (by simp), h1.plGet (k := 1) (by simp),
    h1.plGet (k := 2) (by simp)⟩

end read

theorem pl_sw64 {w : Nat} (hw : w ≤ 64) (x : BitVec w) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (pl_toNat_lt hw x)]

theorem pl_am {w : Nat} (hw : w ≤ 64) {m : BitVec 64} (hm : m.toNat = 2 ^ w - 1) (x y : BitVec w) :
    (x.setWidth 64 + y.setWidth 64) &&& m = plV (x + y) := by
  have hdvd : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw
  apply BitVec.eq_of_toNat_eq
  unfold plV
  rw [BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_add, pl_sw64 hw,
    pl_sw64 hw, Nat.mod_mod_of_dvd _ hdvd, BitVec.toNat_ofNat, BitVec.toNat_add,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
      (Nat.pow_le_pow_right (by decide) hw))]

theorem plW_plV {w : Nat} (hw : w ≤ 64) (x : BitVec w) : plW (plV x).toNat = plW x.toNat := by
  rw [plV_toNat hw]

theorem plTerms_single {w : Nat} (pool : Pool) (a : Nat) (x : BitVec w) :
    plTerms pool [(a, x)] = offs pool a :: plW x.toNat := rfl

/-- More words pushed on top of a range. -/
theorem PlStkW.push_more {c1 c2 : CMem} {base : Nat} {ws1 ws2 : List Nat} (h1 : PlStkW c1 base ws1)
    (hpre : ∀ j, j < c1.k.sp.toNat → c2.stk[j]? = c1.stk[j]?) (h2 : PlStkW c2 c1.k.sp.toNat ws2) :
    PlStkW c2 base (ws1 ++ ws2) := by
  rw [h1.1] at h2 hpre
  exact PlStkW.append (h1.2.plFrame hpre) h2

/-! ## The specification -/

def LinAddSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (w b0 b1 : Nat) (p q : Lin w) (m : BitVec 64),
    FnSpec (State := State) Vbcf.prog "lin_add"
      (fun vs s => vs = [.ptr sb 0, uv b0, uv b1, .u64 m] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ 1 ≤ w ∧ w ≤ 64 ∧ m.toNat = 2 ^ w - 1 ∧
        LinOK st.cs.pool p.terms ∧ LinOK st.cs.pool q.terms ∧ b1 = b0 + (plEnc st.cs.pool q).length ∧
        PlStkW c b0 (plEnc st.cs.pool q ++ plEnc st.cs.pool p))
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        PlRet W sb X c0 prems params st c b0 (plEnc st.cs.pool (Lin.add p q)) r s')

/-- The environment of `lin_add`'s body. -/
def plAddEnv (sb b0 b1 : Nat) (m : BitVec 64) (e i j : Nat) (a b n ok : BitVec 32)
    (cv dv : BitVec 64) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("b0", .u32, uv b0), ("b1", .u32, uv b1),
   ("m", .u64, .u64 m), ("e", .u32, uv e), ("i", .u32, uv i), ("j", .u32, uv j),
   ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("n", .u32, .u32 n), ("ok", .u32, .u32 ok),
   ("c", .u64, .u64 cv), ("d", .u64, .u64 dv)]

/-- The invariant of the merge loop: `ip` terms of `p` and `jq` terms of `q` consumed,
`out` produced (after the constant) from `e` on. -/
def PlAddInv (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    {w : Nat} (b0 b1 e : Nat) (p q : Lin w) (m : BitVec 64) : Env → (KernelState prog State) → Prop :=
  fun env s' => ∃ (c' : CMem) (ip jq : Nat) (out : List (Nat × BitVec w)) (iv jv : Nat)
      (a b n ok : BitVec 32) (cv dv : BitVec 64),
    env = plAddEnv sb b0 b1 m e iv jv a b n ok cv dv ∧
    iv = b1 + 2 + 3 * ip ∧ jv = b0 + 2 + 3 * jq ∧ ip ≤ p.terms.length ∧ jq ≤ q.terms.length ∧
    Lin.mergeTerms p.terms q.terms = out ++ Lin.mergeTerms (p.terms.drop ip) (q.terms.drop jq) ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ (∀ j, j < b0 → c'.stk[j]? = c.stk[j]?) ∧
    WordsAt c'.stk b0 (plEnc st.cs.pool q) ∧ WordsAt c'.stk b1 (plEnc st.cs.pool p) ∧
    PlStkW c' e (plW (p.const + q.const).toNat ++ plTerms st.cs.pool out)

/-- The copy loop over `i`: `t` words of `RP` copied. -/
def PlAddCpI (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    {w : Nat} (b0 b1 e jv iv0 : Nat) (p q : Lin w) (m : BitVec 64) (pre RP : List Nat) :
    Env → (KernelState prog State) → Prop :=
  fun env s' => ∃ (c' : CMem) (t : Nat) (a b n ok : BitVec 32) (cv dv : BitVec 64),
    env = plAddEnv sb b0 b1 m e (iv0 + t) jv a b n ok cv dv ∧ t ≤ RP.length ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ (∀ j, j < b0 → c'.stk[j]? = c.stk[j]?) ∧
    WordsAt c'.stk b0 (plEnc st.cs.pool q) ∧ WordsAt c'.stk b1 (plEnc st.cs.pool p) ∧
    PlStkW c' e (pre ++ RP.take t)

/-- The copy loop over `j`. -/
def PlAddCpJ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    {w : Nat} (b0 b1 e iv jv0 : Nat) (_p q : Lin w) (m : BitVec 64) (pre RQ : List Nat) :
    Env → (KernelState prog State) → Prop :=
  fun env s' => ∃ (c' : CMem) (t : Nat) (a b n ok : BitVec 32) (cv dv : BitVec 64),
    env = plAddEnv sb b0 b1 m e iv (jv0 + t) a b n ok cv dv ∧ t ≤ RQ.length ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ (∀ j, j < b0 → c'.stk[j]? = c.stk[j]?) ∧
    WordsAt c'.stk b0 (plEnc st.cs.pool q) ∧ PlStkW c' e (pre ++ RQ.take t)

/-- The final move: `t` words of `R` moved down from `e` to `b0`. -/
def PlAddMv (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (b0 b1 e jv : Nat) (m : BitVec 64) (R : List Nat) : Env → (KernelState prog State) → Prop :=
  fun env s' => ∃ (c' : CMem) (t : Nat) (a b ok : BitVec 32) (cv dv : BitVec 64),
    env = plAddEnv sb b0 b1 m e t jv a b (BitVec.ofNat 32 R.length) ok cv dv ∧ t ≤ R.length ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ c'.k.sp.toNat = e + R.length ∧
    (∀ j, j < b0 → c'.stk[j]? = c.stk[j]?) ∧
    WordsAt c'.stk b0 (R.take t) ∧ WordsAt c'.stk (e + t) (R.drop t)

theorem pl_drop_cons {α : Type} {l : List α} {t : Nat} (h : t < l.length) :
    l.drop t = l[t] :: l.drop (t + 1) := List.drop_eq_getElem_cons h

/-- The statements after the merge loop of `lin_add`. -/
def plAddTail : Stmt := [cstms|
  while (i < e) {
    ok = push(st, st->stk[i]);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  while (j < b1) {
    ok = push(st, st->stk[j]);
    if (ok == 0) { return 0; }
    j = j + 1;
  }
  n = st->sp - e;
  ok = spend(st, n);
  if (ok == 0) { return 0; }
  i = 0;
  while (i < n) {
    st->stk[b0 + i] = st->stk[e + i];
    i = i + 1;
  }
  st->sp = b0 + n;
  return 1;
]

theorem lin_add_tail {W : World} {sb : Nat} {X : Ctx} {c0 c c2 : CMem} {prems params : List Nat}
    {st : VSt} {w b0 b1 ip jq : Nat} {p q : Lin w} {m : BitVec 64} {out : List (Nat × BitVec w)}
    {a b n ok : BitVec 32} {cv dv : BitVec 64} {s2 : (KernelState prog State)}
    (_hw64 : w ≤ 64) (hb1 : b1 = b0 + (2 + 3 * q.terms.length))
    (hexit : b1 + 2 + 3 * ip < b1 + (2 + 3 * p.terms.length) → b1 ≤ b0 + 2 + 3 * jq)
    (hip : ip ≤ p.terms.length) (hjq : jq ≤ q.terms.length)
    (hmerge : Lin.mergeTerms p.terms q.terms = out ++ Lin.mergeTerms (p.terms.drop ip) (q.terms.drop jq))
    (h : Holds W s2.mem sb c2) (hR : RCtx W X c0 prems params c2 st)
    (hpre : ∀ j, j < b0 → c2.stk[j]? = c.stk[j]?)
    (hq2 : WordsAt c2.stk b0 (plEnc st.cs.pool q)) (hp2 : WordsAt c2.stk b1 (plEnc st.cs.pool p))
    (hout : PlStkW c2 (b1 + (2 + 3 * p.terms.length)) (plW (p.const + q.const).toNat ++ plTerms st.cs.pool out)) :
    WP Vbcf.prog plAddTail (RetQ (PlRet W sb X c0 prems params st c b0 (plEnc st.cs.pool (Lin.add p q))))
      (plAddEnv sb b0 b1 m (b1 + (2 + 3 * p.terms.length)) (b1 + 2 + 3 * ip) (b0 + 2 + 3 * jq)
        a b n ok cv dv) s2 := by
  have hs := prog_ck
  unfold plAddTail
  have hsp2 := hout.1
  simp only [List.length_append, plW_length, plTerms_length] at hsp2
  have hspmax2 := hR.sp_lt
  simp only [maxPool] at hspmax2
  have hrest : p.terms.drop ip = [] ∨ q.terms.drop jq = [] := by
    rw [List.drop_eq_nil_iff, List.drop_eq_nil_iff]; omega
  have hres : plEnc st.cs.pool (Lin.add p q) = plW (p.const + q.const).toNat ++ plTerms st.cs.pool out ++
      plTerms st.cs.pool (p.terms.drop ip) ++ plTerms st.cs.pool (q.terms.drop jq) := by
    simp only [plEnc, Lin.add, hmerge, pl_merge_rest hrest, plTerms_append, List.append_assoc]
  have hRP := pl_words_drop hp2 ip
  have hRPl : (plTerms st.cs.pool (p.terms.drop ip)).length = 3 * (p.terms.length - ip) := by simp
  have hRQl : (plTerms st.cs.pool (q.terms.drop jq)).length = 3 * (q.terms.length - jq) := by simp
  apply WP.loop_seq (PlAddCpI W sb X c0 c prems params st b0 b1 (b1 + (2 + 3 * p.terms.length))
    (b0 + 2 + 3 * jq) (b1 + 2 + 3 * ip) p q m (plW (p.const + q.const).toNat ++ plTerms st.cs.pool out)
    (plTerms st.cs.pool (p.terms.drop ip)))
  · exact ⟨c2, 0, a, b, n, ok, cv, dv, rfl, by omega, h, hR, hpre, hq2, hp2, by simpa using hout⟩
  clear h hR hpre hout
  rintro env s3 ⟨c3, t, a3, b3, n3, ok3, cv3, dv3, rfl, ht, h, hR, hpre, hq3, hp3, hout3⟩
  have hRP3 := pl_words_drop hp3 ip
  have hsp3 := hout3.1
  simp only [List.length_append, plW_length, plTerms_length, List.length_take] at hsp3
  have hstk3 := hR.stk_eq h (by omega)
  rule_simp [plAddEnv]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · -- copy one word
    have ht' : t < (plTerms st.cs.pool (p.terms.drop ip)).length := by omega
    have hc := hRP3.plGet ht'
    apply WP.rule_push h hR
    rule_simp [hstk3, rd_u32 hc, uv_toNat (show b1 + 2 + 3 * ip + t < 4294967296 by omega)]
    intro s4 c4 ok4 h4 hP4
    obtain ⟨hR4, hpre4, hcase4⟩ := hP4.plCases
    rcases hcase4 with rfl | ⟨rfl, hw4⟩
    · apply WP.ite_seq; rule_simp
      apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c4, h4, hR4, fun j hj => (hpre4 j (by omega)).trans (hpre j hj), Or.inl rfl⟩
    apply WP.ite_seq; rule_simp
    clear h hR
    have h := h4
    have hR := hR4
    apply WP.assign_loop; rule_simp
    refine ⟨c4, t + 1, a3, b3, n3, 1#32, cv3, dv3, ?_, by omega, h, hR,
      fun j hj => (hpre4 j (by omega)).trans (hpre j hj),
      hq3.plFrame (fun j hj => hpre4 j (by simp at hj; omega)),
      hp3.plFrame (fun j hj => hpre4 j (by simp at hj; omega)), ?_⟩
    · simp only [plAddEnv, ← Nat.add_assoc]
    · rw [pl_take_succ_of_drop (pl_drop_cons ht'), ← List.append_assoc]
      exact PlStkW.push_more hout3 hpre4 hw4
  have htl : t = (plTerms st.cs.pool (p.terms.drop ip)).length := by omega
  subst htl
  rw [List.take_length] at hout3
  have hRQ := pl_words_drop hq3 jq
  apply WP.loop_seq (PlAddCpJ W sb X c0 c prems params st b0 b1 (b1 + (2 + 3 * p.terms.length))
    (b1 + 2 + 3 * ip + (plTerms st.cs.pool (p.terms.drop ip)).length) (b0 + 2 + 3 * jq) p q m
    (plW (p.const + q.const).toNat ++ plTerms st.cs.pool out ++ plTerms st.cs.pool (p.terms.drop ip))
    (plTerms st.cs.pool (q.terms.drop jq)))
  · exact ⟨c3, 0, a3, b3, n3, ok3, cv3, dv3, rfl, by omega, h, hR, hpre, hq3, by simpa using hout3⟩
  clear h hR hpre hout3 hp3 hRP3 hstk3
  rintro env s4 ⟨c4, t, a4, b4, n4, ok4, cv4, dv4, rfl, ht, h, hR, hpre, hq4, hout4⟩
  have hRQ4 := pl_words_drop hq4 jq
  have hsp4 := hout4.1
  simp only [List.length_append, plW_length, plTerms_length, List.length_take] at hsp4
  have hstk4 := hR.stk_eq h (by omega)
  rule_simp [plAddEnv]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · -- copy one word
    have ht' : t < (plTerms st.cs.pool (q.terms.drop jq)).length := by omega
    have hc := hRQ4.plGet ht'
    apply WP.rule_push h hR
    rule_simp [hstk4, rd_u32 hc, uv_toNat (show b0 + 2 + 3 * jq + t < 4294967296 by omega)]
    intro s5 c5 ok5 h5 hP5
    obtain ⟨hR5, hpre5, hcase5⟩ := hP5.plCases
    rcases hcase5 with rfl | ⟨rfl, hw5⟩
    · apply WP.ite_seq; rule_simp
      apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c5, h5, hR5, fun j hj => (hpre5 j (by omega)).trans (hpre j hj), Or.inl rfl⟩
    apply WP.ite_seq; rule_simp
    clear h hR
    have h := h5
    have hR := hR5
    apply WP.assign_loop; rule_simp
    refine ⟨c5, t + 1, a4, b4, n4, 1#32, cv4, dv4, ?_, by omega, h, hR,
      fun j hj => (hpre5 j (by omega)).trans (hpre j hj),
      hq4.plFrame (fun j hj => hpre5 j (by simp at hj; omega)), ?_⟩
    · simp only [plAddEnv, ← Nat.add_assoc]
    · rw [pl_take_succ_of_drop (pl_drop_cons ht'), ← List.append_assoc]
      exact PlStkW.push_more hout4 hpre5 hw5
  have htl : t = (plTerms st.cs.pool (q.terms.drop jq)).length := by omega
  subst htl
  rw [List.take_length, ← hres] at hout4
  have hspR := hout4.1
  have hRlen := plEnc_length (pool := st.cs.pool) (Lin.add p q)
  have hRl : (plEnc st.cs.pool (Lin.add p q)).length ≤ c4.k.sp.toNat := by omega
  have hspw4 : c4.k.sp = BitVec.ofNat 32 (b1 + (2 + 3 * p.terms.length) +
      (plEnc st.cs.pool (Lin.add p q)).length) := by
    rw [← hspR]; exact (bv_ofNat_toNat _).symm
  rule_assign [hspw4, cw_sub (show b1 + (2 + 3 * p.terms.length) + (plEnc st.cs.pool (Lin.add p q)).length
    < 4294967296 by omega) (show b1 + (2 + 3 * p.terms.length) ≤ b1 + (2 + 3 * p.terms.length) +
    (plEnc st.cs.pool (Lin.add p q)).length by omega)]
  -- `ok = spend(st, n); if (ok == 0) { return 0; }`
  apply WP.rule_spend h hR
  rule_simp
  intro s4' wk er ok' h' _
  (try rule_simp); apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨_, h', hR.wev, hpre, Or.inl rfl⟩
  have hR' := hR.wev (wk := wk) (er := er) (vl := c4.k.val)
  have hspR' : (c4.wev wk er c4.k.val).k.sp.toNat = b1 + (2 + 3 * p.terms.length) +
      (plEnc st.cs.pool (Lin.add p q)).length := hspR
  have hpre' : ∀ j, j < b0 → (c4.wev wk er c4.k.val).stk[j]? = c.stk[j]? := hpre
  have hout4' : PlStkW (c4.wev wk er c4.k.val) (b1 + (2 + 3 * p.terms.length))
      (plEnc st.cs.pool (Lin.add p q)) := hout4
  clear h hR hspR hpre hout4 hspw4
  generalize c4.wev wk er c4.k.val = c4 at h' hR' hspR' hpre' hout4'
  have h := h'
  have hR := hR'
  have hspR := hspR'
  have hpre := hpre'
  have hout4 := hout4'
  clear h' hR' hspR' hpre' hout4'
  rule_assign
  apply WP.loop_seq (PlAddMv W sb X c0 c prems params st b0 b1 (b1 + (2 + 3 * p.terms.length))
    (b0 + 2 + 3 * jq + (plTerms st.cs.pool (q.terms.drop jq)).length) m (plEnc st.cs.pool (Lin.add p q)))
  · refine ⟨c4, 0, a4, b4, ok', cv4, dv4, ?_, by omega, h, hR, hspR, hpre, by simp [WordsAt.plNil],
      by simpa using hout4.2⟩
    simp only [plAddEnv, plEnc_length]
    rw [cw_sub (a := b1 + (2 + 3 * p.terms.length) + (2 + 3 * (p.add q).terms.length))
      (b := b1 + (2 + 3 * p.terms.length)) (by omega) (by omega), Nat.add_sub_cancel_left]
    simp
  clear h hR hpre hout4
  rintro env s5 ⟨c5, t, a5, b5, ok5, cv5, dv5, rfl, ht, h, hR, hsp5, hpre, hlo, hhi⟩
  have hstk5 := hR.stk_eq h (by omega)
  have hsz5 := hR.stk_size h (by omega)
  have hspm5 := hR.sp_lt
  simp only [maxPool] at hspm5
  rule_simp [plAddEnv]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- `st->sp = b0 + n; return 1;`
    have htl : t = (plEnc st.cs.pool (Lin.add p q)).length := by omega
    subst htl
    rw [List.take_length] at hlo
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s6 h6
    apply WP.rule_ret; rule_simp
    refine ⟨_, h6, hR.set_sp _ ?_, hpre, Or.inr ⟨rfl, ?_, hlo⟩⟩
    · rw [uv_add, uv_toNat (by omega)]; omega
    · simp only; rw [uv_add, uv_toNat (by omega)]; simp
  · have ht' : t < (plEnc st.cs.pool (Lin.add p q)).length := by omega
    have hd := pl_drop_cons ht'
    rw [hd] at hhi
    have hc := hhi.plGet (k := 0) (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hc
    apply WP.seq
    apply WP.ck_store .stk h (by rfl) hstk5
    rule_simp [hstk5, rd_u32 hc, uv_toNat (show b0 + t < 4294967296 by omega),
      uv_toNat (show b1 + (2 + 3 * p.terms.length) + t < 4294967296 by omega)]
    refine ⟨by omega, ?_⟩
    intro s6 h6
    apply WP.assign_loop; rule_simp
    refine ⟨_, t + 1, a5, b5, ok5, cv5, dv5, by simp [plAddEnv], by omega, h6,
      hR.set_stk _ _, hsp5, fun j hj => ?_, ?_, ?_⟩
    · simp only; rw [Array.getElem?_setIfInBounds_ne (by omega)]; exact hpre j hj
    · rw [pl_take_succ_of_drop hd]
      exact hlo.plSetSnoc (by simp; omega) (by omega)
    · have h1 := (WordsAt.plSplit (A := [(plEnc st.cs.pool (Lin.add p q))[t]]) hhi).2
      have h2 := h1.plSetOut (pos := b0 + t) (v := uv (plEnc st.cs.pool (Lin.add p q))[t])
        (by simp only [List.length_singleton]; omega)
      rw [show b1 + (2 + 3 * p.terms.length) + t + [(plEnc st.cs.pool (Lin.add p q))[t]].length =
        b1 + (2 + 3 * p.terms.length) + (t + 1) by simp only [List.length_singleton]; omega] at h2
      exact h2

theorem lin_add_spec : LinAddSpec (State := State) := by
  intro W sb X c0 c prems params st w b0 b1 p q m
  have hs := prog_ck
  apply FnSpec.intro' (fn := linAdd) rfl
  rintro vs s ⟨rfl, h, hR, hw1, hw64, hm, hpok, hqok, hb1, hst⟩
  simp [linAdd, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := linAdd) rfl
  simp only [linAdd, Stmt.block, initLocals, List.map, Ty.zero]
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  simp only [plEnc_length] at hb1
  have hsp := hst.1
  simp only [List.length_append, plEnc_length] at hsp
  obtain ⟨hq, hp⟩ := WordsAt.plSplit hst.2
  simp only [plEnc_length] at hp
  rw [← hb1] at hp
  have he : b1 + (2 + 3 * p.terms.length) = c.k.sp.toNat := by omega
  have hspw : c.k.sp = BitVec.ofNat 32 (b1 + (2 + 3 * p.terms.length)) := by
    rw [he]; exact (bv_ofNat_toNat _).symm
  have hstk := hR.stk_eq h (by omega)
  rule_assign [hspw]
  -- `if (b1 < b0 || e < b1 || e > MAX_POOL) { return 0; }`: a failure return
  apply WP.ite_seq
  rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c, h, hR, fun _ _ => rfl, Or.inl rfl⟩
  intro _ _
  -- `ok = spend(st, e - b0);`
  apply WP.rule_spend h hR
  rule_simp
  intro s' wk er ok h _
  have hR := hR.wev (wk := wk) (er := er) (vl := c.k.val)
  have hwsp : (c.wev wk er c.k.val).k.sp.toNat = c.k.sp.toNat := rfl
  (try rule_simp); apply WP.ite_seq; rule_simp
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨_, h, hR, fun _ _ => rfl, Or.inl rfl⟩
  have hp0 := hp.plGet (k := 0) (by simp only [plEnc_length]; omega)
  have hp1 := hp.plGet (k := 1) (by simp only [plEnc_length]; omega)
  have hq0 := hq.plGet (k := 0) (by simp only [plEnc_length]; omega)
  have hq1 := hq.plGet (k := 1) (by simp only [plEnc_length]; omega)
  simp only [plEnc, plW, List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_zero] at hp0 hp1 hq0 hq1
  apply WP.pl_get64 h hR b1 p.const.toNat (by omega) (pl_toNat_lt hw64 _) hp0 hp1
  refine ⟨by rule_simp, ?_⟩
  rule_simp
  apply WP.pl_get64 h hR b0 q.const.toNat (by omega) (pl_toNat_lt hw64 _) hq0 hq1
  refine ⟨by rule_simp, ?_⟩
  rule_simp
  apply WP.pl_call (lin_push64_spec W sb X c0 _ prems params st (plV (p.const + q.const)))
    (by rule_simp [pl_am hw64 hm]) ⟨rfl, h, hR⟩
  intro s1 r1 hr1
  clear h hR
  obtain ⟨c1, h, hR, hpre1, hcase⟩ := hr1
  rcases hcase with rfl | ⟨rfl, hw1'⟩
  · rule_simp
    apply WP.ite_seq
    rule_simp
    apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR, fun j hj => hpre1 j (by omega), Or.inl rfl⟩
  rw [plW_plV hw64] at hw1'
  rule_simp
  apply WP.ite_seq
  rule_simp
  rule_assign
  rule_assign
  apply WP.loop_seq (PlAddInv W sb X c0 c prems params st b0 b1 (b1 + (2 + 3 * p.terms.length)) p q m)
  · refine ⟨c1, 0, 0, [], b1 + 2, b0 + 2, 0#32, 0#32, 0#32, 1#32, p.const.setWidth 64,
      q.const.setWidth 64, by simp [plAddEnv], by omega, by omega,
      by omega, by omega, by simp, h, hR, fun j hj => hpre1 j (by omega),
      hq.plFrame (fun j hj => hpre1 j (by simp at hj; omega)),
      hp.plFrame (fun j hj => hpre1 j (by simp at hj; omega)), ?_⟩
    rw [he]; simpa using hw1'
  clear h hR hw1' hpre1 hp0 hp1 hq0 hq1
  rintro env s2 ⟨c2, ip, jq, out, iv, jv, a, b, n, ok, cv, dv, rfl, rfl, rfl, hip, hjq, hmerge, h, hR,
    hpre, hq2, hp2, hout⟩
  rule_simp [plAddEnv]
  have hsp2 := hout.1
  simp only [List.length_append, plW_length, plTerms_length] at hsp2
  have hstk2 := hR.stk_eq h (by omega)
  have hspmax2 := hR.sp_lt
  simp only [maxPool] at hspmax2
  refine ⟨fun hexit => ?_, fun hi hj => ?_⟩
  · exact lin_add_tail hw64 hb1 hexit hip hjq hmerge h hR hpre hq2 hp2 hout
  have hip' : ip < p.terms.length := by omega
  have hjq' : jq < q.terms.length := by omega
  obtain ⟨⟨ta, tc⟩, P', hdp⟩ : ∃ t P', p.terms.drop ip = t :: P' := by
    cases hd : p.terms.drop ip with
    | nil => rw [List.drop_eq_nil_iff] at hd; omega
    | cons t rest => exact ⟨t, rest, rfl⟩
  obtain ⟨⟨ub, ud⟩, Q', hdq⟩ : ∃ t Q', q.terms.drop jq = t :: Q' := by
    cases hd : q.terms.drop jq with
    | nil => rw [List.drop_eq_nil_iff] at hd; omega
    | cons t rest => exact ⟨t, rest, rfl⟩
  have hta : ta < st.cs.pool.size := hpok (ta, tc) (List.mem_of_mem_drop (i := ip) (by rw [hdp]; simp))
  have hub : ub < st.cs.pool.size := hqok (ub, ud) (List.mem_of_mem_drop (i := jq) (by rw [hdq]; simp))
  have hoa := hR.core.cinv.off_lt hta
  have hob := hR.core.cinv.off_lt hub
  obtain ⟨rp0, rp1, rp2⟩ := pl_read_term hp2 hdp
  obtain ⟨rq0, rq1, rq2⟩ := pl_read_term hq2 hdq
  simp only at rp0 rp1 rp2 rq0 rq1 rq2
  have hlenP := congrArg List.length hdp
  have hlenQ := congrArg List.length hdq
  simp only [List.length_drop, List.length_cons] at hlenP hlenQ
  have hdp' : p.terms.drop (ip + 1) = P' := by rw [← List.drop_drop, hdp]; rfl
  have hdq' : q.terms.drop (jq + 1) = Q' := by rw [← List.drop_drop, hdq]; rfl
  rule_assign [hstk2, rd_u32 rp0, uv_toNat (show b1 + 2 + 3 * ip < 4294967296 by omega)]
  rule_assign [hstk2, rd_u32 rq0, uv_toNat (show b0 + 2 + 3 * jq < 4294967296 by omega)]
  apply WP.ite
  rule_simp [offs_lt_iff (Nat.le_of_lt hub), offs_lt_iff (Nat.le_of_lt hta)]
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · apply WP.pl_get64 h hR (b1 + 2 + 3 * ip + 1) tc.toNat (by omega) (pl_toNat_lt hw64 _) rp1 rp2
    refine ⟨by rule_simp, ?_⟩
    rule_simp
    apply WP.pl_call (lin_term_spec W sb X c0 c2 prems params st (offs st.cs.pool ta) (tc.setWidth 64))
      (by rule_simp) ⟨rfl, h, hR⟩
    intro s3 r3 hr3
    clear h hR
    obtain ⟨c3, h, hR, hpre3, hcase3⟩ := hr3
    rcases hcase3 with rfl | ⟨rfl, hw3⟩
    · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c3, h, hR, fun j hj => (hpre3 j (by omega)).trans (hpre j hj), Or.inl rfl⟩
    rule_simp; apply WP.ite_seq; rule_simp
    apply WP.assign_loop; rule_simp
    rw [pl_sw64 hw64] at hw3
    refine ⟨c3, ip + 1, jq, out ++ [(ta, tc)], _, _, _, _, _, _, _, _, rfl, by omega, rfl, by omega,
      hjq, ?_, h, hR, fun j hj => (hpre3 j (by omega)).trans (hpre j hj),
      hq2.plFrame (fun j hj => hpre3 j (by simp at hj; omega)),
      hp2.plFrame (fun j hj => hpre3 j (by simp at hj; omega)), ?_⟩
    · rw [hmerge, hdp, hdq, pl_merge_lt hlt, hdp', ← hdq]; simp
    · rw [plTerms_append, plTerms_single, ← List.append_assoc]
      exact PlStkW.push_more hout hpre3 hw3
  apply WP.ite
  rule_simp [offs_lt_iff (Nat.le_of_lt hub), offs_lt_iff (Nat.le_of_lt hta)]
  refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · apply WP.pl_get64 h hR (b0 + 2 + 3 * jq + 1) ud.toNat (by omega) (pl_toNat_lt hw64 _) rq1 rq2
    refine ⟨by rule_simp, ?_⟩
    rule_simp
    apply WP.pl_call (lin_term_spec W sb X c0 c2 prems params st (offs st.cs.pool ub) (ud.setWidth 64))
      (by rule_simp) ⟨rfl, h, hR⟩
    intro s3 r3 hr3
    clear h hR
    obtain ⟨c3, h, hR, hpre3, hcase3⟩ := hr3
    rcases hcase3 with rfl | ⟨rfl, hw3⟩
    · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c3, h, hR, fun j hj => (hpre3 j (by omega)).trans (hpre j hj), Or.inl rfl⟩
    rule_simp; apply WP.ite_seq; rule_simp
    apply WP.assign_loop; rule_simp
    rw [pl_sw64 hw64] at hw3
    refine ⟨c3, ip, jq + 1, out ++ [(ub, ud)], _, _, _, _, _, _, _, _, rfl, rfl, by omega, hip,
      by omega, ?_, h, hR, fun j hj => (hpre3 j (by omega)).trans (hpre j hj),
      hq2.plFrame (fun j hj => hpre3 j (by simp at hj; omega)),
      hp2.plFrame (fun j hj => hpre3 j (by simp at hj; omega)), ?_⟩
    · rw [hmerge, hdp, hdq, pl_merge_gt hgt, hdq', ← hdp]; simp
    · rw [plTerms_append, plTerms_single, ← List.append_assoc]
      exact PlStkW.push_more hout hpre3 hw3
  have hab : ta = ub := by omega
  subst hab
  apply WP.pl_get64 h hR (b1 + 2 + 3 * ip + 1) tc.toNat (by omega) (pl_toNat_lt hw64 _) rp1 rp2
  refine ⟨by rule_simp, ?_⟩
  rule_simp
  apply WP.pl_get64 h hR (b0 + 2 + 3 * jq + 1) ud.toNat (by omega) (pl_toNat_lt hw64 _) rq1 rq2
  refine ⟨by rule_simp, ?_⟩
  rule_simp
  rule_assign [pl_am hw64 hm]
  have hmg := @pl_merge_eq w ta tc ud P' Q'
  by_cases hz : tc + ud = 0
  · rw [ite_eq_left hz] at hmg
    have hz' : tc + ud = 0#w := hz
    apply WP.ite_seq
    rule_simp [plV_eq0 hw64, hz']
    rule_assign
    apply WP.assign_loop; rule_simp
    refine ⟨c2, ip + 1, jq + 1, out, _, _, _, _, _, _, _, _, rfl, by omega, by omega, by omega,
      by omega, ?_, h, hR, hpre, hq2, hp2, hout⟩
    rw [hmerge, hdp, hdq, hmg, hdp', hdq']
  · rw [ite_eq_right hz] at hmg
    have hz' : ¬ tc + ud = 0#w := hz
    apply WP.ite_seq
    rule_simp [plV_eq0 hw64, hz']
    apply WP.pl_call (lin_term_spec W sb X c0 c2 prems params st (offs st.cs.pool ta) (plV (tc + ud)))
      (by rule_simp) ⟨rfl, h, hR⟩
    intro s3 r3 hr3
    clear h hR
    obtain ⟨c3, h, hR, hpre3, hcase3⟩ := hr3
    rcases hcase3 with rfl | ⟨rfl, hw3⟩
    · rule_simp; apply WP.ite; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
      exact ⟨c3, h, hR, fun j hj => (hpre3 j (by omega)).trans (hpre j hj), Or.inl rfl⟩
    rule_simp; apply WP.ite; rule_simp; apply WP.skip; simp only [LoopQ]
    rule_assign
    apply WP.assign_loop; rule_simp
    rw [plW_plV hw64] at hw3
    refine ⟨c3, ip + 1, jq + 1, out ++ [(ta, tc + ud)], _, _, _, _, _, _, _, _, rfl, by omega,
      by omega, by omega, by omega, ?_, h, hR, fun j hj => (hpre3 j (by omega)).trans (hpre j hj),
      hq2.plFrame (fun j hj => hpre3 j (by simp at hj; omega)),
      hp2.plFrame (fun j hj => hpre3 j (by simp at hj; omega)), ?_⟩
    · rw [hmerge, hdp, hdq, hmg, hdp', hdq']; simp
    · rw [plTerms_append, plTerms_single, ← List.append_assoc]
      exact PlStkW.push_more hout hpre3 hw3

end Vbcf.Proof
