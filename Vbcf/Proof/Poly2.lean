import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly1

/-!
# Vbcf proofs: the Poly family, part 2 — words on the stack, `lin_push64`, `lin_get64`

* `PlStkW c base ws`: the words `ws` are on the scratch stack from `base` up to `sp`.
* `PlRet … c base ws r s'`: what a pushing helper leaves (the rule context, the cells
  below `base`, and on success `ws` from `base` on); `PlRet.trans` chains two of them.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Words on the stack -/

/-- The words `ws` are on the stack from `base` up to `sp`. -/
def PlStkW (c : CMem) (base : Nat) (ws : List Nat) : Prop :=
  c.k.sp.toNat = base + ws.length ∧ WordsAt c.stk base ws

/-- What a helper that pushes the words `ws` (from `base` on) leaves behind. -/
def PlRet (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (c : CMem) (base : Nat) (ws : List Nat) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (∀ j, j < base → c'.stk[j]? = c.stk[j]?) ∧ (r = 0#32 ∨ (r = 1#32 ∧ PlStkW c' base ws))

section stkw
variable {c c' : CMem}

theorem PlStkW.nil {base : Nat} (h : c.k.sp.toNat = base) : PlStkW c base [] :=
  ⟨by simpa using h, fun k x hx => by simp at hx⟩

theorem PlStkW.cell {base : Nat} {ws : List Nat} (h : PlStkW c base ws) {k : Nat} (hk : k < ws.length) :
    c.stk[base + k]? = some (uv ws[k]) := h.2 k _ (List.getElem?_eq_getElem hk)

/-- The cell of word `x` in `A ++ x :: R`. -/
theorem PlStkW.mid {base : Nat} {A R : List Nat} {x : Nat} (h : PlStkW c base (A ++ x :: R)) :
    c.stk[base + A.length]? = some (uv x) := by
  have := h.2 A.length x (by simp)
  exact this

theorem PlStkW.mid1 {base : Nat} {A R : List Nat} {x y : Nat} (h : PlStkW c base (A ++ x :: y :: R)) :
    c.stk[base + A.length + 1]? = some (uv y) := by
  have := h.2 (A.length + 1) y (by simp)
  rwa [← Nat.add_assoc] at this

theorem PlStkW.prefix {base : Nat} {A B : List Nat} (h : PlStkW c base (A ++ B)) : WordsAt c.stk base A :=
  fun k x hx => h.2 k x (by rw [List.getElem?_append_left (lt_length_of_getElem? hx)]; exact hx)

theorem PlStkW.suffix {base : Nat} {A B : List Nat} (h : PlStkW c base (A ++ B)) :
    PlStkW c (base + A.length) B := by
  refine ⟨by have := h.1; simp at this; omega, fun k x hx => ?_⟩
  have := h.2 (A.length + k) x (by rw [List.getElem?_append_right (by omega)]; simpa using hx)
  rwa [← Nat.add_assoc] at this

theorem PlStkW.append {base : Nat} {A B : List Nat} (hA : WordsAt c.stk base A)
    (hB : PlStkW c (base + A.length) B) : PlStkW c base (A ++ B) := by
  refine ⟨by rw [hB.1]; simp; omega, fun k x hx => ?_⟩
  rcases Nat.lt_or_ge k A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hx
    exact hA k x hx
  · rw [List.getElem?_append_right hge] at hx
    have := hB.2 _ _ hx
    rwa [show base + A.length + (k - A.length) = base + k by omega] at this

/-- Cells kept below some bound keep the words stored there. -/
theorem WordsAt.plFrame {base : Nat} {A : List Nat} (hA : WordsAt c.stk base A)
    (hpre : ∀ j, j < base + A.length → c'.stk[j]? = c.stk[j]?) : WordsAt c'.stk base A := by
  intro k x hx
  have := lt_length_of_getElem? hx
  unfold U; rw [hpre _ (by omega)]; exact hA k x hx

end stkw

section plret
variable {W : World} {X : Ctx} {c0 c c1 : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {s1 s2 : (KernelState prog State)}

/-- Failing right away. -/
theorem PlRet.fail (h : Holds W s1.mem sb c) (hR : RCtx W X c0 prems params c st)
    {base : Nat} {ws : List Nat} : PlRet W sb X c0 prems params st c base ws 0#32 s1 :=
  ⟨c, h, hR, fun _ _ => rfl, Or.inl rfl⟩

/-- Chaining: `ws₁` pushed from `base`, then `ws₂` pushed from where that ended. -/
theorem PlRet.trans {base : Nat} {ws1 ws2 : List Nat} {r : BitVec 32}
    (_h1 : Holds W s1.mem sb c1) (_hR1 : RCtx W X c0 prems params c1 st)
    (hpre1 : ∀ j, j < base → c1.stk[j]? = c.stk[j]?) (hw1 : PlStkW c1 base ws1)
    (h2 : PlRet W sb X c0 prems params st c1 c1.k.sp.toNat ws2 r s2) :
    PlRet W sb X c0 prems params st c base (ws1 ++ ws2) r s2 := by
  obtain ⟨c2, h2, hR2, hpre2, hr⟩ := h2
  refine ⟨c2, h2, hR2, fun j hj => ?_, ?_⟩
  · rw [hpre2 j (by rw [hw1.1]; omega), hpre1 j hj]
  · rcases hr with h0 | ⟨h1', hw2⟩
    · exact Or.inl h0
    · refine Or.inr ⟨h1', ?_⟩
      rw [hw1.1] at hw2
      exact PlStkW.append (hw1.2.plFrame (fun j hj => hpre2 j (by rw [hw1.1]; omega))) hw2

/-- The outcome of a `push` of the word `x`. -/
theorem Pushed.plCases {x : Nat} {ok : BitVec 32} {c' : CMem}
    (hP : Pushed W X c0 prems params st c (BitVec.ofNat 32 x) c' ok) :
    RCtx W X c0 prems params c' st ∧ (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧
      (ok = 0#32 ∨ (ok = 1#32 ∧ PlStkW c' c.k.sp.toNat [x])) := by
  obtain ⟨hR', hpre, hcase⟩ := hP
  refine ⟨hR', hpre, ?_⟩
  rcases hcase with ⟨h0, -⟩ | ⟨h1, -, hsp, htop⟩
  · exact Or.inl h0
  · refine Or.inr ⟨h1, by simpa using hsp, fun k y hy => ?_⟩
    have hk : k = 0 := by
      rcases k with _ | k
      · rfl
      · simp at hy
    subst hk
    simp at hy; subst hy
    simpa [U] using htop

/-- A `push` as a `PlRet`. -/
theorem PlRet.of_pushed {x : Nat} {ok : BitVec 32} {c' : CMem} (h' : Holds W s1.mem sb c')
    (hP : Pushed W X c0 prems params st c (BitVec.ofNat 32 x) c' ok) :
    PlRet W sb X c0 prems params st c c.k.sp.toNat [x] ok s1 := by
  obtain ⟨hR', hpre, hcase⟩ := hP
  refine ⟨c', h', hR', hpre, ?_⟩
  rcases hcase with ⟨h0, -⟩ | ⟨h1, -, hsp, htop⟩
  · exact Or.inl h0
  · refine Or.inr ⟨h1, by simpa using hsp, fun k y hy => ?_⟩
    have hk : k = 0 := by
      rcases k with _ | k
      · rfl
      · simp at hy
    subst hk
    simp at hy; subst hy
    simpa [U] using htop

end plret

/-! ## Words of a 64-bit value -/

theorem pl_lo (v : BitVec 64) : v.setWidth 32 = BitVec.ofNat 32 (v.toNat % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem pl_hi (v : BitVec 64) : (v >>> 32).setWidth 32 = BitVec.ofNat 32 (v.toNat / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]

theorem pl_hi_lt (v : BitVec 64) : v.toNat / 2 ^ 32 < 2 ^ 32 := by
  have := v.isLt; omega

/-- Two words read back as a 64-bit value. -/
theorem pl_join {lo hi : Nat} (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) :
    (BitVec.ofNat 32 lo).setWidth 64 ||| (BitVec.ofNat 32 hi).setWidth 64 <<< 32 =
      BitVec.ofNat 64 (lo + 2 ^ 32 * hi) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlo,
    Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt (by omega : lo < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : hi < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : hi * 2 ^ 32 < 2 ^ 64), Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : lo + 2 ^ 32 * hi < 2 ^ 64)]
  omega

theorem pl_join2 {x : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 (x % 4294967296) ||| BitVec.ofNat 64 (x / 4294967296) <<< 32 =
      BitVec.ofNat 64 x := by
  have e1 : BitVec.ofNat 64 (x % 4294967296) = (BitVec.ofNat 32 (x % 2 ^ 32)).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  have e2 : BitVec.ofNat 64 (x / 4294967296) = (BitVec.ofNat 32 (x / 2 ^ 32)).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  rw [e1, e2, pl_join (by omega) (by omega), pl_split]

/-! ## `lin_push64` -/

def LinPush64Spec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (v : BitVec 64),
    FnSpec (State := State) Vbcf.prog "lin_push64"
      (fun vs s => vs = [.ptr sb 0, .u64 v] ∧ Holds W s.mem sb c ∧ RCtx W X c0 prems params c st)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        PlRet W sb X c0 prems params st c c.k.sp.toNat (plW v.toNat) r s')

theorem lin_push64_spec : LinPush64Spec (State := State) := by
  intro W sb X c0 c prems params st v
  have hs := prog_ck
  apply FnSpec.intro' (fn := linPush64) rfl
  rintro vs s ⟨rfl, h, hR⟩
  simp [linPush64, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := linPush64) rfl
  simp only [linPush64, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rule_push h hR
  rule_simp [pl_lo]
  intro s1 c1 ok1 h1 hP1
  obtain ⟨hR1, hpre1, hcase⟩ := hP1.plCases
  rcases hcase with rfl | ⟨rfl, hw1⟩
  · apply WP.ite_seq
    rule_simp
    apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h1, hR1, hpre1, Or.inl rfl⟩
  apply WP.ite_seq
  rule_simp
  apply WP.rule_push h1 hR1
  rule_simp [pl_hi]
  intro s2 c2 ok2 h2 hP2
  apply WP.rule_ret; rule_simp
  exact PlRet.trans (ws1 := [_]) h1 hR1 hpre1 hw1 (PlRet.of_pushed h2 hP2)

/-! ## Calling a helper with a `u32` result -/

/-- `x = f(args); rest` for a helper whose postcondition is `R r s'` on the result word. -/
theorem WP.pl_call {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {x : Var} {f : String}
    {es : List Expr} {rest : Stmt} {vs : List EmbC.Val} {pre : List EmbC.Val → (KernelState P State) → Prop}
    {R : BitVec 32 → (KernelState P State) → Prop}
    (hspec : FnSpec (State := State) P f pre (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ R r s'))
    (hargs : evalArgs P env s.mem es = some vs) (hpre : pre vs s)
    (H : ∀ s' r, R r s' →
      match env.assign s'.mem x (.u32 r) with
      | none => False
      | some env' => WP P rest Q env' s') :
    WP P (.seq (.call (some x) f es) rest) Q env s := by
  apply WP.call_seq hspec hargs hpre
  rintro rv s' ⟨r, rfl, hr⟩
  exact H s' r hr

/-! ## `lin_get64` -/

def LinGet64Spec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (i x : Nat),
    FnSpec (State := State) Vbcf.prog "lin_get64"
      (fun vs s => vs = [.ptr sb 0, uv i] ∧ Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧
        i + 1 < c.k.sp.toNat ∧ x < 2 ^ 64 ∧ c.stk[i]? = some (uv (x % 2 ^ 32)) ∧
        c.stk[i + 1]? = some (uv (x / 2 ^ 32)))
      (fun _ s rv s' => s' = s ∧ rv = some (.u64 (BitVec.ofNat 64 x)))

theorem lin_get64_spec : LinGet64Spec (State := State) := by
  intro W sb X c0 c prems params st i x
  have hs := prog_ck
  apply FnSpec.intro' (fn := linGet64) rfl
  rintro vs s ⟨rfl, h, hR, hi, hx, h0, h1⟩
  simp [linGet64, bindParams, Mem.hasTy_ptr h.ck rfl]
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hstk := hR.stk_eq h (by omega)
  apply WP.ret
  rule_simp [hstk, rd_u32 h0, rd_u32 h1, uv_toNat (show i < 4294967296 by omega),
    uv_toNat (show i + 1 < 4294967296 by omega), retPost]
  exact pl_join2 hx

/-- `x = lin_get64(st, i); rest`. -/
theorem WP.pl_get64 {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
    {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {y : Var} {es : List Expr} {rest : Stmt}
    (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (i x : Nat)
    (hi : i + 1 < c.k.sp.toNat) (hx : x < 2 ^ 64) (h0 : c.stk[i]? = some (uv (x % 2 ^ 32)))
    (h1 : c.stk[i + 1]? = some (uv (x / 2 ^ 32)))
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv i] ∧
      match env.assign s.mem y (.u64 (BitVec.ofNat 64 x)) with
      | none => False
      | some env' => WP Vbcf.prog rest Q env' s) :
    WP Vbcf.prog (.seq (.call (some y) "lin_get64" es) rest) Q env s := by
  apply WP.call_seq (lin_get64_spec W sb X c0 c prems params st i x) H.1
    ⟨rfl, h, hR, hi, hx, h0, h1⟩
  rintro rv s' ⟨rfl, rfl⟩
  exact H.2

/-! ## `lin_term`, `lin_atom` -/

def LinTermSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a : Nat) (v : BitVec 64),
    FnSpec (State := State) Vbcf.prog "lin_term"
      (fun vs s => vs = [.ptr sb 0, uv a, .u64 v] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        PlRet W sb X c0 prems params st c c.k.sp.toNat (a :: plW v.toNat) r s')

theorem lin_term_spec : LinTermSpec (State := State) := by
  intro W sb X c0 c prems params st a v
  have hs := prog_ck
  apply FnSpec.intro' (fn := linTerm) rfl
  rintro vs s ⟨rfl, h, hR⟩
  simp [linTerm, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := linTerm) rfl
  simp only [linTerm, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rule_push h hR
  rule_simp
  intro s1 c1 ok1 h1 hP1
  obtain ⟨hR1, hpre1, hcase⟩ := hP1.plCases
  rcases hcase with rfl | ⟨rfl, hw1⟩
  · apply WP.ite_seq
    rule_simp
    apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h1, hR1, hpre1, Or.inl rfl⟩
  apply WP.ite_seq
  rule_simp
  apply WP.pl_call (lin_push64_spec W sb X c0 c1 prems params st v) (by rule_simp) ⟨rfl, h1, hR1⟩
  intro s2 r2 hr2
  rule_simp
  apply WP.rule_ret; rule_simp
  exact PlRet.trans (ws1 := [_]) h1 hR1 hpre1 hw1 hr2

/-- `1 & m` is `1`. -/
theorem pl_one_and {w : Nat} (hw : 1 ≤ w) {m : BitVec 64} (hm : m.toNat = 2 ^ w - 1) :
    1#64 &&& m = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hm]
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have : (1 : Nat) &&& (2 ^ w - 1) = 1 % 2 ^ w := Nat.and_two_pow_sub_one_eq_mod 1 w
  simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  rw [this, Nat.mod_eq_of_lt (by omega)]

theorem pl_enc_atom {w : Nat} (hw : 1 ≤ w) (pool : Pool) (a : Nat) :
    plEnc pool (Lin.atom (w := w) a) = plW 0 ++ offs pool a :: plW 1 := by
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  simp [plEnc, Lin.atom, plTerms_cons, plW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]

def LinAtomSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (w a : Nat) (m : BitVec 64),
    FnSpec (State := State) Vbcf.prog "lin_atom"
      (fun vs s => vs = [.ptr sb 0, uv (offs st.cs.pool a), .u64 m] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ 1 ≤ w ∧ m.toNat = 2 ^ w - 1)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        PlRet W sb X c0 prems params st c c.k.sp.toNat (plEnc st.cs.pool (Lin.atom (w := w) a)) r s')

theorem lin_atom_spec : LinAtomSpec (State := State) := by
  intro W sb X c0 c prems params st w a m
  have hs := prog_ck
  apply FnSpec.intro' (fn := linAtom) rfl
  rintro vs s ⟨rfl, h, hR, hw, hm⟩
  simp [linAtom, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := linAtom) rfl
  simp only [linAtom, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.pl_call (lin_push64_spec W sb X c0 c prems params st 0#64) (by rule_simp) ⟨rfl, h, hR⟩
  intro s1 r1 hr1
  obtain ⟨c1, h1, hR1, hpre1, hcase⟩ := hr1
  rcases hcase with rfl | ⟨rfl, hw1⟩
  · rule_simp
    apply WP.ite_seq
    rule_simp
    apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h1, hR1, hpre1, Or.inl rfl⟩
  rule_simp
  apply WP.ite_seq
  rule_simp
  apply WP.pl_call (lin_term_spec W sb X c0 c1 prems params st (offs st.cs.pool a) 1#64)
    (by rule_simp [pl_one_and hw hm]) ⟨rfl, h1, hR1⟩
  intro s2 r2 hr2
  rule_simp
  apply WP.rule_ret; rule_simp
  rw [pl_enc_atom hw]
  exact PlRet.trans h1 hR1 hpre1 hw1 hr2

/-! ## `poly_lit_val` -/

/-- What `poly_lit_val(st, w, id)` returns for node `i`: 0 with the state unchanged when
`litVal` fails, 1 with the literal's value in `st->val` when it succeeds. -/
def PlLitRes (W : World) (sb : Nat) (c : CMem) (st : VSt) (w i : Nat) (s : (KernelState prog State)) (r : BitVec 32)
    (s' : (KernelState prog State)) : Prop :=
  (r = 0#32 ∧ s' = s ∧ Bcf.litVal st.cs.pool w i = none) ∨
  (r = 1#32 ∧ ∃ (k : BitVec w) (vl : BitVec 64), Bcf.litVal st.cs.pool w i = some k ∧
    vl.toNat = k.toNat ∧ Holds W s'.mem sb (c.wev c.k.work c.k.err vl))

def PlPolyLitValSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (w i : Nat),
    FnSpec (State := State) Vbcf.prog "poly_lit_val"
      (fun vs s => vs = [.ptr sb 0, uv w, uv (offs st.cs.pool i)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ i < st.cs.pool.size ∧ w < 2 ^ 32)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ PlLitRes W sb c st w i s r s')

theorem pl_litVal_none {pool : Pool} {w i : Nat} {n : Node} (hn : pool[i]? = some n)
    (h : ∀ w' v, n.op ≠ .bvVal w' v) : Bcf.litVal pool w i = none := by
  obtain ⟨op, args⟩ := n
  unfold Bcf.litVal
  rw [hn]
  cases op <;> simp_all

theorem pl_litVal_val {pool : Pool} {w i w' v : Nat} {args : Array Nat}
    (hn : pool[i]? = some ⟨.bvVal w' v, args⟩) :
    Bcf.litVal pool w i = if w' = w then some (BitVec.ofNat w v) else none := by
  unfold Bcf.litVal
  rw [hn]

theorem poly_lit_val_spec : PlPolyLitValSpec (State := State) := by
  intro W sb X c0 c prems params st w i
  have hs := prog_ck
  apply FnSpec.intro' (fn := polyLitVal) rfl
  rintro vs s ⟨rfl, h, hR, hi, hw⟩
  simp [polyLitVal, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := polyLitVal) rfl
  simp only [polyLitVal, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨n, hn⟩ := node_of_lt hi
  have hf := hR.core.cinv.rep.fits i n hn
  rule_assign [hR.core.cinv.rdHdr hn]
  by_cases hop : ∃ w' v, n.op = .bvVal w' v
  · obtain ⟨w', v, hop⟩ := hop
    have hargs := cv_leaf_args hR.core.cinv.ok hn (by rw [hop]; simp [IsLeaf, isLeaf])
    obtain ⟨argTys, t, -, hrt, -, -⟩ := hR.core.cinv.ok.retype hn
    rw [hop] at hrt
    obtain ⟨hw0, hw64, hv⟩ := resultTy_bvVal hrt
    obtain ⟨op, args⟩ := n
    simp only at hop hargs
    subst hop hargs
    have hlo := hf.lo
    simp only [opLo] at hlo
    apply WP.ite_seq
    rule_simp
    by_cases hww : w' = w
    · subst hww
      apply WP.ite_seq
      rule_simp [cv_hdr_par hf, opLo, opHi]
      have hc1 := hR.core.cinv.rep.tail hn (k := 0) (w := v % 2 ^ 32)
        (by simp [tailW]; split <;> simp)
      have hmask := mask64M_toNat (k := w') (by omega) hw64
      have hfin : ∀ (x : BitVec 64) (s1 : (KernelState prog State)), x.toNat = v →
          Holds W s1.mem sb c →
          WP Vbcf.prog ((Stmt.call (some "m") "mask64" [Expr.var "w"]).seq
            ((Stmt.setField (Expr.var "st") "val" (Expr.bin BinOp.band (Expr.var "x") (Expr.var "m"))).seq
              (Stmt.ret (some (Expr.lit32 1#32))))) (RetQ (PlLitRes W sb c st w' i s))
            [("st", (Ty.struct "ck").ptr, Val.ptr sb 0), ("w", Ty.u32, uv w'),
              ("id", Ty.u32, uv (offs st.cs.pool i)),
              ("hdr", Ty.u32, uv (hdrW { op := Op.bvVal w' v, args := #[] })), ("x", Ty.u64, Val.u64 x),
              ("m", Ty.u64, Val.u64 0#64)] s1 := by
        intro x s1 hx h1
        apply WP.call_seq (mask64_spec (BitVec.ofNat 32 w')) (by rule_simp) rfl
        rintro rv s2 ⟨rfl, rfl⟩
        rule_simp
        apply WP.seq; apply WP.ck_setVal hs h1 rfl
        rule_simp
        intro s3 h3
        apply WP.rule_ret; rule_simp
        refine Or.inr ⟨rfl, BitVec.ofNat w' v, _, by rw [pl_litVal_val hn, ite_eq_left rfl], ?_, h3⟩
        rw [BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, hx, BitVec.toNat_ofNat]
      apply WP.assign_seq; rule_simp [rd_u32 hc1]
      by_cases hw32 : w' ≤ 32
      · have htl : tailLen ⟨.bvVal w' v, #[]⟩ = 1 := by simp [tailLen, hw32]
        apply WP.ite_seq; rule_simp [hdr_len_bv hf, htl]
        have hv32 : v < 2 ^ 32 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw32)
        exact hfin _ _ (by simp; omega) h
      · have htl : tailLen ⟨.bvVal w' v, #[]⟩ = 2 := by simp [tailLen, hw32]
        have hc2 : U c.pool (offs st.cs.pool i + 2) (v / 2 ^ 32) := by
          have := hR.core.cinv.rep.tail hn (k := 1) (w := v / 2 ^ 32) (by simp [tailW, hw32])
          rwa [Nat.add_assoc] at this
        apply WP.ite_seq; rule_simp [hdr_len_bv hf, htl, rd_u32 hc2]
        apply WP.assign; rule_simp [LoopQ, rd_u32 hc2]
        refine hfin _ _ ?_ h
        have hv64 : v < 2 ^ 64 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw64)
        rw [pl_join2 hv64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv64]
    · apply WP.ite_seq
      rule_simp [cv_hdr_par hf, opLo, opHi, hww]
      apply WP.rule_ret; rule_simp [LoopQ]
      exact Or.inl ⟨rfl, rfl, by rw [pl_litVal_val hn, ite_eq_right hww]⟩
  · apply WP.ite_seq
    rule_simp
    refine ⟨fun _ => ?_, fun x y he => absurd ⟨x, y, he⟩ hop⟩
    apply WP.rule_ret; rule_simp [LoopQ]
    exact Or.inl ⟨rfl, rfl, pl_litVal_none hn (fun x y he => hop ⟨x, y, he⟩)⟩

end Vbcf.Proof
