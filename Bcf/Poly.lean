import Bcf.Aci

/-!
# POLY_NORM: verified linear normalisation of bit-vector arithmetic

`lin` rewrites a width-`w` term into a linear form `c + Σ kᵢ·atomᵢ`
where atoms are the nodes that are not `+`, `-`, unary `-`, literals, or
products with a literal factor.  `lin_eval` proves the form denotes the
term.  POLY_NORM then accepts `a = b` when both sides have the same
linear form.
-/

namespace Bcf

/-! ## Commutative-monoid bookkeeping -/

theorem bv_add4 {w : Nat} (a b c d : BitVec w) : a + b + (c + d) = a + c + (b + d) := by
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc b, BitVec.add_comm b c, BitVec.add_assoc]

theorem bv_add_left_comm {w : Nat} (a b c : BitVec w) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

theorem bv_zero_mul' {w : Nat} (x : BitVec w) : (0 : BitVec w) * x = 0 := BitVec.zero_mul
theorem bv_zero_add' {w : Nat} (x : BitVec w) : (0 : BitVec w) + x = x := BitVec.zero_add x
theorem bv_mul_zero' {w : Nat} (x : BitVec w) : x * (0 : BitVec w) = 0 := BitVec.mul_zero
theorem bv_neg_one_mul {w : Nat} (x : BitVec w) : (-1 : BitVec w) * x = -x := by
  simp

namespace Lin
variable {w : Nat}

/-- Denotation, given a value for every atom. -/
def evalTerms (lv : Nat → BitVec w) : List (Nat × BitVec w) → BitVec w
  | [] => 0
  | (a, c) :: rest => c * lv a + evalTerms lv rest

def eval (lv : Nat → BitVec w) (p : Lin w) : BitVec w := p.const + evalTerms lv p.terms

theorem evalTerms_mergeTerms (lv : Nat → BitVec w) :
    ∀ (xs ys : List (Nat × BitVec w)), evalTerms lv (mergeTerms xs ys) = evalTerms lv xs + evalTerms lv ys := by
  intro xs
  induction xs with
  | nil => intro ys; simp [mergeTerms, evalTerms]
  | cons x xs ih =>
    intro ys
    induction ys with
    | nil => simp [mergeTerms, evalTerms]
    | cons y ys ih' =>
      obtain ⟨a, c⟩ := x
      obtain ⟨b, d⟩ := y
      simp only [mergeTerms]
      split
      · simp only [evalTerms]; rw [ih]; simp only [evalTerms]; rw [BitVec.add_assoc]
      · split
        · simp only [evalTerms]; rw [ih']; simp only [evalTerms]
          rw [bv_add_left_comm (d * lv b) (c * lv a + evalTerms lv xs) (evalTerms lv ys)]
        · rename_i h1 h2
          have hab : a = b := by omega
          subst hab
          split
          · rename_i h0
            rw [ih]; simp only [evalTerms]
            rw [bv_add4, ← BitVec.add_mul, h0, bv_zero_mul', bv_zero_add']
          · simp only [evalTerms]; rw [ih]
            rw [BitVec.add_mul, bv_add4]

theorem eval_add (lv : Nat → BitVec w) (p q : Lin w) : eval lv (add p q) = eval lv p + eval lv q := by
  unfold eval add
  simp only
  rw [evalTerms_mergeTerms, bv_add4]

theorem evalTerms_scale (lv : Nat → BitVec w) (k : BitVec w) (ts : List (Nat × BitVec w)) :
    evalTerms lv ((ts.map (fun t => (t.1, k * t.2))).filter (fun t => t.2 ≠ 0)) = k * evalTerms lv ts := by
  induction ts with
  | nil => simp [evalTerms]
  | cons t rest ih =>
    obtain ⟨a, c⟩ := t
    simp only [List.map_cons, List.filter_cons]
    split
    · simp only [evalTerms]; rw [ih, BitVec.mul_add, BitVec.mul_assoc]
    · rename_i h
      simp at h
      simp only [evalTerms]
      rw [ih, BitVec.mul_add, ← BitVec.mul_assoc, h]
      simp

theorem eval_scale (lv : Nat → BitVec w) (k : BitVec w) (p : Lin w) : eval lv (scale k p) = k * eval lv p := by
  unfold eval scale
  simp only
  rw [evalTerms_scale, BitVec.mul_add]

theorem eval_neg (lv : Nat → BitVec w) (p : Lin w) : eval lv (neg p) = - eval lv p := by
  unfold neg; rw [eval_scale, bv_neg_one_mul]

theorem eval_const (lv : Nat → BitVec w) (c : BitVec w) : eval lv (ofConst c) = c := by
  simp [eval, ofConst, evalTerms]

theorem eval_atom (lv : Nat → BitVec w) (a : Nat) : eval lv (atom a) = lv a := by
  simp [eval, atom, evalTerms]

theorem eval_foldr_add (lv : Nat → BitVec w) (ps : List (Lin w)) :
    eval lv (ps.foldr add (ofConst 0)) = ps.foldr (fun p acc => eval lv p + acc) 0 := by
  induction ps with
  | nil => simp [eval_const]
  | cons p rest ih => simp only [List.foldr_cons]; rw [eval_add, ih]

end Lin

/-! ## The normaliser denotes the term -/

theorem foldl_add_eq_foldr {w : Nat} (l : List (BitVec w)) :
    l.foldl (· + ·) 0 = l.foldr (· + ·) 0 := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons, List.foldr_cons]
    rw [foldl_op (fun x y z => BitVec.add_assoc x y z) (fun x y => BitVec.add_comm x y) (fun x => bv_zero_add' x) rest,
        bv_zero_add', ih]

theorem foldr_add_congr {w : Nat} (f g : Nat → BitVec w) :
    ∀ (l : List Nat), (∀ a ∈ l, f a = g a) →
      l.foldr (fun x acc => f x + acc) 0 = l.foldr (fun x acc => g x + acc) 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    simp only [List.foldr_cons]
    rw [h a (by simp), ih (fun a' ha' => h a' (by simp [ha']))]

theorem linF_stable (pool : Pool) (w : Nat) (i : Nat) :
    ∀ f f', i < f → i < f' → linF pool w f i = linF pool w f' i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f f' hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [linF]
    split
    · rfl
    · split
      · congr 1
        apply List.map_congr_left
        intro a _
        split
        · exact ih a (by assumption) g g' (by omega) (by omega)
        · rfl
      · rfl
    · split
      · split
        · rename_i hc
          rw [ih _ hc.2.1 g g' (by omega) (by omega), ih _ hc.2.2 g g' (by omega) (by omega)]
        · rfl
      · rfl
    · split
      · split
        · rename_i hc; rw [ih _ hc.2 g g' (by omega) (by omega)]
        · rfl
      · rfl
    · split
      · split
        · rename_i hc
          split
          · rw [ih _ hc.2.2 g g' (by omega) (by omega)]
          · rw [ih _ hc.2.1 g g' (by omega) (by omega)]
          · rfl
        · rfl
      · rfl
    · rfl

theorem lin_unfold (pool : Pool) (w : Nat) (i : Nat) :
    lin pool w i = linF pool w (i + 1) i := rfl

/-- Node semantics for the four arithmetic operators. -/
theorem bvSub_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i a b : Nat}
    (h : pool[i]? = some ⟨.bvSub w, #[a, b]⟩) :
    evalV pool ρ w i = evalV pool ρ w a - evalV pool ρ w b ∧
    typeOf pool a = some (.bv w) ∧ typeOf pool b = some (.bv w) ∧ typeOf pool i = some (.bv w) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := ht
  rw [typeOf_node hwf h] at h2
  cases hta : typeOf pool a <;> cases htb : typeOf pool b <;>
    simp [mapOpt, hta, htb, Op.resultTy, bvBinTy, tyGuard] at h2
  obtain ⟨⟨hw, rfl, rfl⟩, rfl⟩ := h2
  refine ⟨?_, rfl, rfl, ht⟩
  rw [evalV, eval_node hwf ρ h]
  simp only [Op.eval, List.map, evalV_spec hta, evalV_spec htb, bvBin, Val.asBv_bv]
  simp [hw]

theorem bvNeg_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i a : Nat}
    (h : pool[i]? = some ⟨.bvNeg w, #[a]⟩) :
    evalV pool ρ w i = - evalV pool ρ w a ∧ typeOf pool a = some (.bv w) ∧ typeOf pool i = some (.bv w) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := ht
  rw [typeOf_node hwf h] at h2
  cases hta : typeOf pool a <;> simp [mapOpt, hta, Op.resultTy, bvUnTy, tyGuard] at h2
  obtain ⟨⟨hw, rfl⟩, rfl⟩ := h2
  refine ⟨?_, rfl, ht⟩
  rw [evalV, eval_node hwf ρ h]
  simp only [Op.eval, List.map, evalV_spec hta, bvUn, Val.asBv_bv]
  simp [hw]

theorem bvMul2_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i a b : Nat}
    (h : pool[i]? = some ⟨.bvMul w, #[a, b]⟩) :
    evalV pool ρ w i = evalV pool ρ w a * evalV pool ρ w b ∧
    typeOf pool a = some (.bv w) ∧ typeOf pool b = some (.bv w) := by
  obtain ⟨hargs, _, hw, _⟩ := bvN_args_bv hwf h rfl
  have hta := hargs a (by simp)
  have htb := hargs b (by simp)
  refine ⟨?_, hta, htb⟩
  have := bvop_node hwf ρ w (.bvMul w) (· * ·) 1 rfl (fun _ => rfl) i _ h
  rw [this]
  simp [BitVec.one_mul]

theorem bvAdd_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i : Nat} {args : Array Nat}
    (h : pool[i]? = some ⟨.bvAdd w, args⟩) :
    evalV pool ρ w i = (args.toList.map (evalV pool ρ w)).foldr (· + ·) 0 ∧
    ∀ a ∈ args, typeOf pool a = some (.bv w) := by
  obtain ⟨hargs, _, _, _⟩ := bvN_args_bv hwf h rfl
  refine ⟨?_, hargs⟩
  rw [bvop_node hwf ρ w (.bvAdd w) (· + ·) 0 rfl (fun _ => rfl) i args h, foldl_add_eq_foldr]

theorem litVal_eval {pool : Pool} (hwf : WF pool) (ρ : Assign) {w a : Nat} {k : BitVec w}
    (h : litVal pool w a = some k) : evalV pool ρ w a = k := by
  unfold litVal at h
  split at h
  · rename_i w' v args hn
    split at h
    · rename_i hw; subst w'
      simp at h; subst h
      simp [evalV, eval_lit_bv hwf hn ρ]
    · simp at h
  · simp at h

/-- **The linear form denotes the term.** -/
theorem lin_eval {pool : Pool} (hwf : WF pool) (ρ : Assign) (w : Nat) :
    ∀ i, typeOf pool i = some (.bv w) → evalV pool ρ w i = (lin pool w i).eval (evalV pool ρ w) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    rw [lin_unfold]
    simp only [linF]
    obtain ⟨n, hn⟩ : ∃ n, pool[i]? = some n := by
      cases hn : pool[i]? with
      | none => rw [typeOf_unfold, hn] at hi; simp at hi
      | some n => exact ⟨n, rfl⟩
    have hchild : ∀ a, a < i → typeOf pool a = some (.bv w) →
        evalV pool ρ w a = (linF pool w i a).eval (evalV pool ρ w) := by
      intro a ha hta
      rw [ih a ha hta, lin_unfold, linF_stable pool w a _ _ (by omega) ha]
    rw [hn]
    obtain ⟨op, args⟩ := n
    cases op
    case bvVal w' v =>
      simp only
      split
      · rename_i hw; subst w'
        rw [Lin.eval_const]
        simp [evalV, eval_lit_bv hwf hn ρ]
      · rw [Lin.eval_atom]
    case bvAdd w' =>
      simp only
      split
      · rename_i hw; subst w'
        obtain ⟨hv, hargs⟩ := bvAdd_node hwf ρ hn
        rw [hv, Lin.eval_foldr_add, List.foldr_map, List.foldr_map]
        have hlt := (hwf i _ hn).1
        apply foldr_add_congr
        intro a ha
        have ha' : a < i := hlt a (by simpa using ha)
        simp only [ha', ite_true]
        exact hchild a ha' (hargs a (by simpa using ha))
      · rw [Lin.eval_atom]
    case bvSub w' =>
      simp only
      split
      · rename_i a b hl
        split
        · rename_i hc
          obtain ⟨hw, ha, hb⟩ := hc
          subst w'
          have hn' : pool[i]? = some ⟨.bvSub w, #[a, b]⟩ := by rw [hn]; congr; apply Array.ext' hl
          obtain ⟨hv, hta, htb, _⟩ := bvSub_node hwf ρ hn'
          rw [hv, Lin.eval_add, Lin.eval_neg, ← hchild a ha hta, ← hchild b hb htb, BitVec.sub_eq_add_neg]
        · rw [Lin.eval_atom]
      · rw [Lin.eval_atom]
    case bvNeg w' =>
      simp only
      split
      · rename_i a hl
        split
        · rename_i hc
          obtain ⟨hw, ha⟩ := hc
          subst w'
          have hn' : pool[i]? = some ⟨.bvNeg w, #[a]⟩ := by rw [hn]; congr; apply Array.ext' hl
          obtain ⟨hv, hta, _⟩ := bvNeg_node hwf ρ hn'
          rw [hv, Lin.eval_neg, ← hchild a ha hta]
        · rw [Lin.eval_atom]
      · rw [Lin.eval_atom]
    case bvMul w' =>
      simp only
      split
      · rename_i a b hl
        split
        · rename_i hc
          obtain ⟨hw, ha, hb⟩ := hc
          subst w'
          have hn' : pool[i]? = some ⟨.bvMul w, #[a, b]⟩ := by rw [hn]; congr; apply Array.ext' hl
          obtain ⟨hv, hta, htb⟩ := bvMul2_node hwf ρ hn'
          split
          · rename_i k hk
            rw [hv, Lin.eval_scale, ← hchild b hb htb, litVal_eval hwf ρ hk]
          · rename_i k _ hk
            rw [hv, Lin.eval_scale, ← hchild a ha hta, litVal_eval hwf ρ hk, BitVec.mul_comm]
          · rw [Lin.eval_atom]
        · rw [Lin.eval_atom]
      · rw [Lin.eval_atom]
    all_goals (simp only; rw [Lin.eval_atom])

/-- Both sides of a well-typed equation have the same type. -/
theorem eq_args_same_ty {pool : Pool} (hwf : WF pool) {e a b : Nat} {t : Ty}
    (he : pool[e]? = some ⟨.eq, #[a, b]⟩) (hta : typeOf pool a = some t) : typeOf pool b = some t := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hwf e _ he).2
  have h2 := hu
  rw [typeOf_node hwf he] at h2
  cases htb : typeOf pool b <;> simp [mapOpt, hta, htb, Op.resultTy, eqTy, tyGuard] at h2
  rw [h2.1.1]

theorem rulePolyNorm_sound {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat} {ei : EI}
    {prems params : List Nat} (h : rulePolyNorm ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold rulePolyNorm at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        split at h
        · rename_i w hta
          split at h
          · rename_i hlin
            simp at h; obtain ⟨rfl, rfl⟩ := h
            have hen := node_bind_eq hab
            refine ⟨hinv, idx_lt_of_get hen, ?_⟩
            intro ρ _
            rw [holds_eq_node hinv.wf hen ρ]
            obtain ⟨m, hm⟩ := node_of_lt (child_lt hinv.wf hen (a := a) (by simp))
            have hta' : typeOf st.pool a = some (.bv w) := by
              rw [(hinv.tys.2 a m hm).2]; exact hta
            have htb := eq_args_same_ty hinv.wf hen hta'
            refine ⟨?_, ⟨.bv w, by rw [eval_ty, hta'], rfl⟩⟩
            rw [evalV_spec hta', evalV_spec htb, lin_eval hinv.wf ρ w a hta', lin_eval hinv.wf ρ w b htb, hlin]
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-! ## POLY_NORM_EQ -/

theorem odd_coprime_pow {c : Nat} (hc : c % 2 = 1) (w : Nat) : Nat.Coprime (2 ^ w) c := by
  apply Nat.Coprime.pow_left
  show Nat.gcd 2 c = 1
  rw [Nat.gcd_rec, hc]
  rfl

/-- Odd bit-vectors are units: `c * z = 0` forces `z = 0`. -/
theorem odd_mul_eq_zero {w : Nat} {c z : BitVec w} (hc : c.toNat % 2 = 1) (h : c * z = 0#w) : z = 0#w := by
  rw [BitVec.toNat_eq] at h ⊢
  rw [BitVec.toNat_mul, BitVec.toNat_zero] at h
  rw [BitVec.toNat_zero]
  have hd : 2 ^ w ∣ c.toNat * z.toNat := Nat.dvd_of_mod_eq_zero h
  have hd' : 2 ^ w ∣ z.toNat := (odd_coprime_pow hc w).dvd_of_dvd_mul_left hd
  exact Nat.eq_zero_of_dvd_of_lt hd' z.isLt

theorem odd_sub_eq_iff {w : Nat} {c0 c1 x0 x1 y0 y1 : BitVec w}
    (h0 : c0.toNat % 2 = 1) (h1 : c1.toNat % 2 = 1)
    (h : c0 * (x0 - x1) = c1 * (y0 - y1)) : x0 = x1 ↔ y0 = y1 := by
  constructor
  · intro hx; subst hx
    rw [BitVec.sub_self, BitVec.mul_zero] at h
    have := odd_mul_eq_zero h1 h.symm
    exact (BitVec.sub_eq_iff_eq_add.mp this).trans (BitVec.zero_add _)
  · intro hy; subst hy
    rw [BitVec.sub_self, BitVec.mul_zero] at h
    have := odd_mul_eq_zero h0 h
    exact (BitVec.sub_eq_iff_eq_add.mp this).trans (BitVec.zero_add _)

/-- The value of `eq a b` on same-width bit-vector sides. -/
theorem eval_eq_bv {pool : Pool} (hwf : WF pool) (ρ : Assign) {e a b w : Nat}
    (he : pool[e]? = some ⟨.eq, #[a, b]⟩)
    (hta : typeOf pool a = some (.bv w)) (htb : typeOf pool b = some (.bv w)) :
    eval pool ρ e = .bool (decide (evalV pool ρ w a = evalV pool ρ w b)) := by
  rw [eval_node hwf ρ he]
  simp only [Op.eval, List.map, eqEval, evalV_spec hta, evalV_spec htb, Val.eqv]
  simp

theorem oddMulSub_spec {st : St} {m w x0 x1 : Nat} (h : oddMulSub st m = some (w, x0, x1)) :
    ∃ c s k w', st.pool[m]? = some ⟨.bvMul w, #[c, s]⟩ ∧ litVal st.pool w c = some k ∧ k.toNat % 2 = 1 ∧
      st.pool[s]? = some ⟨.bvSub w', #[x0, x1]⟩ := by
  unfold oddMulSub at h
  split at h
  · rename_i w0 args hm
    split at h
    · rename_i c s hl
      split at h
      · rename_i k w' sargs hk hs
        split at h
        · rename_i a0 a1 hl'
          split at h
          · rename_i hodd
            simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨c, s, k, w', ?_, hk, hodd, ?_⟩
            · simp only [St.node] at hm; rw [hm]; congr; apply Array.ext' hl
            · simp only [St.node] at hs; rw [hs]; congr; apply Array.ext' hl'
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem rulePolyNormEq_sound {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat}
    {prems params : List Nat} (h : rulePolyNormEq st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold rulePolyNormEq at h
  split at h
  · rename_i p
    have hpe := premise_entails hp (p := p) (by simp)
    split at h
    · rename_i m0 m1 hpn
      have hpn := node_bind_eq hpn
      split at h
      · rename_i w0 x0 x1 w1 y0 y1 h0 h1
        obtain ⟨c0, s0, k0, w0', hm0, hk0, hodd0, hs0⟩ := oddMulSub_spec h0
        obtain ⟨c1, s1, k1, w1', hm1, hk1, hodd1, hs1⟩ := oddMulSub_spec h1
        have hwf := hinv.wf
        obtain ⟨hv0, htc0, hts0⟩ := bvMul2_node hwf (ρ := fun _ => 0) hm0
        obtain ⟨hv1, htc1, hts1⟩ := bvMul2_node hwf (ρ := fun _ => 0) hm1
        -- the subtraction nodes have the multiplication's width
        obtain ⟨_, _, _, hts0'⟩ := bvSub_node hwf (fun _ => 0) hs0
        obtain ⟨_, _, _, hts1'⟩ := bvSub_node hwf (fun _ => 0) hs1
        rw [hts0] at hts0'; rw [hts1] at hts1'
        simp at hts0' hts1'; subst w0' w1'
        obtain ⟨_, htx0, htx1, _⟩ := bvSub_node hwf (fun _ => 0) hs0
        obtain ⟨_, hty0, hty1, _⟩ := bvSub_node hwf (fun _ => 0) hs1
        -- both multiplications have the same width
        have htm0 := (bvN_args_bv hwf hm0 rfl).2.2.2
        have htm1 := (bvN_args_bv hwf hm1 rfl).2.2.2
        have := eq_args_same_ty hwf hpn htm0
        rw [htm1] at this; simp at this; subst w1
        have hx0 := child_lt hwf hs0 (a := x0) (by simp)
        have hx1 := child_lt hwf hs0 (a := x1) (by simp)
        have hy0 := child_lt hwf hs1 (a := y0) (by simp)
        have hy1 := child_lt hwf hs1 (a := y1) (by simp)
        split at h
        · rename_i st1 e0 he0
          split at h
          · rename_i st2 e1 he1
            have hinv1 := hinv.push he0
            have hinv2 := hinv1.push he1
            have hpre1 := pushNode_prefix he0
            have hpre2 := pushNode_prefix he1
            have hsz1 := (pushNode_size he0).1
            have hsz2 := (pushNode_size he1).1
            have he0n : st2.pool[e0]? = some ⟨.eq, #[x0, x1]⟩ := by
              rw [hpre2 e0 (pushNode_size he0).2]; exact pushNode_get he0
            have he1n : st2.pool[e1]? = some ⟨.eq, #[y0, y1]⟩ := pushNode_get he1
            -- types in st2
            have ty2 : ∀ a, a < st.pool.size → typeOf st2.pool a = typeOf st.pool a := by
              intro a ha
              rw [typeOf_extend hpre2 a (Nat.lt_of_lt_of_le ha hsz1), typeOf_extend hpre1 a ha]
            apply mkEq_entails hinv2 h _ (Nat.lt_of_lt_of_le (pushNode_size he0).2 hsz2) (pushNode_size he1).2
            intro ρ hg
            rw [pushNode_holds he1 ρ (Nat.lt_of_lt_of_le hinv.goal hsz1),
                pushNode_holds he0 ρ hinv.goal] at hg
            have hprem := hpe ρ hg
            rw [holds_eq_node hwf hpn ρ] at hprem
            obtain ⟨hprem, _⟩ := hprem
            rw [evalV_spec htm0, evalV_spec htm1] at hprem
            simp at hprem
            obtain ⟨hv0', _, _⟩ := bvMul2_node hwf ρ hm0
            obtain ⟨hv1', _, _⟩ := bvMul2_node hwf ρ hm1
            obtain ⟨hvs0, _, _, _⟩ := bvSub_node hwf ρ hs0
            obtain ⟨hvs1, _, _, _⟩ := bvSub_node hwf ρ hs1
            rw [hv0', hv1', hvs0, hvs1, litVal_eval hwf ρ hk0, litVal_eval hwf ρ hk1] at hprem
            have hiff := odd_sub_eq_iff hodd0 hodd1 hprem
            rw [eval_eq_bv hinv2.wf ρ he0n (by rw [ty2 x0 hx0]; exact htx0) (by rw [ty2 x1 hx1]; exact htx1),
                eval_eq_bv hinv2.wf ρ he1n (by rw [ty2 y0 hy0]; exact hty0) (by rw [ty2 y1 hy1]; exact hty1)]
            have ev2 : ∀ a, a < st.pool.size → evalV st2.pool ρ w0 a = evalV st.pool ρ w0 a := by
              intro a ha
              unfold evalV
              rw [pushNode_eval he1 ρ (Nat.lt_of_lt_of_le ha hsz1), pushNode_eval he0 ρ ha]
            rw [ev2 x0 hx0, ev2 x1 hx1, ev2 y0 hy0, ev2 y1 hy1]
            congr 1
            exact decide_eq_decide.mpr hiff
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

end Bcf
