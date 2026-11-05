import Bcf.Rw.Instantiate
import Bcf.BvLemmas

/-!
# Soundness of BITBLAST

Every circuit shape accepted by `bbTerm`/`bbAtom` denotes the operator
it stands for: bit `i` of the `from_bool` side evaluates to bit `i` of
the term's value (`bbTerm_bits`), and the atom side evaluates to the
comparison (`bbAtom_val`).
-/

namespace Bcf

/-! ## Boolean nodes -/

theorem isNode_spec {st : St} {i : Nat} {n : Node} (h : isNode st i n = true) : st.pool[i]? = some n := by
  unfold isNode at h; simpa using h

theorem typed_bool_of_bool_node {pool : Pool} (hwf : WF pool) {e : Nat} {n : Node}
    (he : pool[e]? = some n)
    (hop : n.op.resultTy = boolNotTy ∨ n.op.resultTy = eqTy ∨ n.op.resultTy = impliesTy ∨
      n.op.resultTy = boolNTy ∨ n.op.resultTy = boolIteTy) (ρ : Assign) :
    eval pool ρ e = .bool (evalB pool ρ e) :=
  evalB_spec (typeOf_bool_node hwf he hop)

theorem evalB_not {st : St} (hwf : WF st.pool) (ρ : Assign) {n a : Nat} (h : isNotOf st n a = true) :
    evalB st.pool ρ n = !evalB st.pool ρ a := by
  have hn := isNode_spec h
  have he := typed_bool_of_bool_node hwf hn (Or.inl rfl) ρ
  have ha := eval_not_node hwf hn ρ he
  simp [evalB, ha]

theorem evalB_xor {st : St} (hwf : WF st.pool) (ρ : Assign) {n a b : Nat} (h : isXorOf st n a b = true) :
    evalB st.pool ρ n = (evalB st.pool ρ a ^^ evalB st.pool ρ b) := by
  have hn := isNode_spec h
  have he := typed_bool_of_bool_node hwf hn (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ρ
  obtain ⟨x, y, hx, hy, hr⟩ := eval_xor2_node hwf hn ρ he
  rw [hr]; simp [evalB, hx, hy]

theorem evalB_conj {st : St} (hwf : WF st.pool) (ρ : Assign) {n a b : Nat} (h : isConjOf st n a b = true) :
    evalB st.pool ρ n = (evalB st.pool ρ a && evalB st.pool ρ b) := by
  have hn := isNode_spec h
  have he := typed_bool_of_bool_node hwf hn (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ρ
  rw [eval_node hwf ρ hn] at he
  simp only [Op.eval, List.map] at he
  obtain ⟨x, y, hx, hy, hr⟩ := boolN2_inv he
  rw [hr]; simp [evalB, hx, hy]

theorem evalB_disj2 {st : St} (hwf : WF st.pool) (ρ : Assign) {n a b : Nat}
    (hn : st.pool[n]? = some ⟨.disj, #[a, b]⟩) :
    evalB st.pool ρ n = (evalB st.pool ρ a || evalB st.pool ρ b) := by
  have he := typed_bool_of_bool_node hwf hn (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ρ
  rw [eval_node hwf ρ hn] at he
  simp only [Op.eval, List.map] at he
  obtain ⟨x, y, hx, hy, hr⟩ := boolN2_inv he
  rw [hr]; simp [evalB, hx, hy]

theorem evalB_conj2 {st : St} (hwf : WF st.pool) (ρ : Assign) {n a b : Nat}
    (hn : st.pool[n]? = some ⟨.conj, #[a, b]⟩) :
    evalB st.pool ρ n = (evalB st.pool ρ a && evalB st.pool ρ b) :=
  evalB_conj hwf ρ (by unfold isConjOf isNode; simp [hn])

theorem evalB_xor2 {st : St} (hwf : WF st.pool) (ρ : Assign) {n a b : Nat}
    (hn : st.pool[n]? = some ⟨.boolXor, #[a, b]⟩) :
    evalB st.pool ρ n = (evalB st.pool ρ a ^^ evalB st.pool ρ b) :=
  evalB_xor hwf ρ (by unfold isXorOf isNode; simp [hn])

/-- `eq` of two boolean nodes. -/
theorem evalB_eq {st : St} (hwf : WF st.pool) (ρ : Assign) {n a b : Nat} (h : isEqOf st n a b = true)
    (ha : typeOf st.pool a = some .bool) :
    evalB st.pool ρ n = (evalB st.pool ρ a == evalB st.pool ρ b) := by
  have hn := isNode_spec h
  have hb := eq_args_same_ty hwf hn ha
  have he := typed_bool_of_bool_node hwf hn (Or.inr (Or.inl rfl)) ρ
  have hq := eval_eq_node hwf hn ρ he
  rw [evalB_spec ha, evalB_spec hb] at hq
  simp only [Val.eqv] at hq
  simp only [Val.bool.injEq] at hq
  rw [← hq]
  cases evalB st.pool ρ a <;> cases evalB st.pool ρ b <;> rfl

theorem evalB_tt {st : St} (hwf : WF st.pool) (ρ : Assign) {t : Nat}
    (ht : st.pool[t]? = some ⟨.boolVal true, #[]⟩) : evalB st.pool ρ t = true := by
  simp [evalB, eval_lit_bool hwf ht ρ]

theorem evalB_ff {st : St} (hwf : WF st.pool) (ρ : Assign) {t : Nat}
    (ht : st.pool[t]? = some ⟨.boolVal false, #[]⟩) : evalB st.pool ρ t = false := by
  simp [evalB, eval_lit_bool hwf ht ρ]

/-! ## `from_bool` nodes -/

theorem fromBool_args_bool {pool : Pool} (hwf : WF pool) {b : Nat} {args : Array Nat}
    (hb : pool[b]? = some ⟨.bvFromBool, args⟩) :
    (∀ a ∈ args, typeOf pool a = some .bool) ∧ 1 ≤ args.size ∧ typeOf pool b = some (.bv args.size) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf b _ hb).2
  have h2 := ht
  rw [typeOf_node hwf hb] at h2
  cases hm : mapOpt (typeOf pool) args.toList with
  | none => rw [hm] at h2; simp at h2
  | some tys =>
    rw [hm] at h2
    simp only [Option.bind_some, Op.resultTy, bvFromBoolTy, tyGuard] at h2
    split at h2
    · rename_i hc
      have hlen := mapOpt_length hm
      simp at hlen
      refine ⟨?_, by omega, ?_⟩
      · intro a ha
        obtain ⟨y, hy, hfy⟩ := mapOpt_mem hm (by simpa using ha)
        rw [hfy]; congr; exact allBool_mem hc.1 hy
      · rw [ht]; simp at h2; rw [← h2, hlen]
    · simp at h2

theorem eval_fromBool {pool : Pool} (hwf : WF pool) (ρ : Assign) {b : Nat} {args : Array Nat}
    (hb : pool[b]? = some ⟨.bvFromBool, args⟩) :
    eval pool ρ b = .bv (args.toList.map (evalB pool ρ)).length
      (BitVec.ofBoolListLE (args.toList.map (evalB pool ρ))) := by
  obtain ⟨hargs, hlen, _⟩ := fromBool_args_bool hwf hb
  rw [eval_node hwf ρ hb]
  simp only [Op.eval, bvFromBoolEval]
  rw [bools_map_evalB (fun a ha => hargs a (by simpa using ha))]
  simp only [List.length_map, Array.length_toList]
  rw [ite_eq_left hlen]

/-- Bits determine the value. -/
theorem ofBoolListLE_eq {n : Nat} (bs : List Bool) (x : BitVec n) (hlen : bs.length = n)
    (h : ∀ i, i < n → bs.getD i false = x.getLsbD i) :
    BitVec.ofBoolListLE bs = x.cast hlen.symm := by
  apply bv_ext
  intro i hi
  rw [BitVec.getLsbD_ofBoolListLE, BitVec.getLsbD_cast, h i (by omega)]

/-- The `i`-th bit node of a bit list, evaluated. -/
theorem getD_map_evalB {pool : Pool} (ρ : Assign) (bs : List Nat) (i : Nat) {b : Nat} (h : bs[i]? = some b) :
    (bs.map (evalB pool ρ)).getD i false = evalB pool ρ b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]; rfl

theorem allIdx_spec {f : Nat → Nat → Bool} : ∀ (k : Nat) (bs : List Nat), allIdx f k bs = true →
    ∀ j b, bs[j]? = some b → f (k + j) b = true := by
  intro k bs
  induction bs generalizing k with
  | nil => intro _ j b hj; simp at hj
  | cons x xs ih =>
    intro h j b hj
    simp only [allIdx, Bool.and_eq_true] at h
    cases j with
    | zero => simp at hj; subst hj; simpa using h.1
    | succ j =>
      simp at hj
      have := ih (k + 1) h.2 j b hj
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem zipAll_spec {f : Nat → Nat → Bool} : ∀ (xs ys : List Nat), zipAll f xs ys = true →
    xs.length = ys.length ∧ ∀ (j x y : Nat), xs[j]? = some x → ys[j]? = some y → f x y = true := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys with
    | nil => exact ⟨rfl, fun j x y hx _ => by simp at hx⟩
    | cons _ _ => simp [zipAll] at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp [zipAll] at h
    | cons y ys =>
      simp only [zipAll, Bool.and_eq_true] at h
      obtain ⟨hl, hf⟩ := ih ys h.2
      refine ⟨by simp [hl], ?_⟩
      intro j x' y' hx hy
      cases j with
      | zero => simp at hx hy; subst hx; subst hy; exact h.1
      | succ j => simp at hx hy; exact hf j x' y' hx hy

/-! ## Bits of a `from_bool` argument -/

/-- Bits as a function of position. -/
def bitD (pool : Pool) (ρ : Assign) (bs : List Nat) (i : Nat) : Bool :=
  (bs.map (evalB pool ρ)).getD i false

theorem bitD_of_get {pool : Pool} (ρ : Assign) {bs : List Nat} {i b : Nat} (h : bs[i]? = some b) :
    bitD pool ρ bs i = evalB pool ρ b := getD_map_evalB ρ bs i h

theorem bitD_of_ge {pool : Pool} (ρ : Assign) {bs : List Nat} {i : Nat} (h : bs.length ≤ i) :
    bitD pool ρ bs i = false := by
  unfold bitD
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]; rfl

theorem get_of_lt {bs : List Nat} {i : Nat} (h : i < bs.length) : ∃ b, bs[i]? = some b :=
  ⟨bs[i], by simp [h]⟩

/-- The value of a `from_bool` node, bitwise. -/
theorem fromBool_getLsbD {pool : Pool} (hwf : WF pool) (ρ : Assign) {b : Nat} {args : Array Nat}
    (hb : pool[b]? = some ⟨.bvFromBool, args⟩) {n : Nat} {x : BitVec n}
    (hx : eval pool ρ b = .bv n x) : n = args.size ∧ ∀ i, x.getLsbD i = bitD pool ρ args.toList i := by
  rw [eval_fromBool hwf ρ hb] at hx
  injection hx with hn hx
  subst hn
  refine ⟨by simp, ?_⟩
  intro i
  have hx' := eq_of_heq hx
  rw [← hx', BitVec.getLsbD_ofBoolListLE]
  rfl

theorem bitsOf_spec {st : St} {b : Nat} {bs : List Nat} (h : bitsOf st b = some bs) :
    ∃ args, st.pool[b]? = some ⟨.bvFromBool, args⟩ ∧ bs = args.toList := by
  unfold bitsOf at h
  split at h
  · rename_i args hb; simp at h; subst h; exact ⟨args, hb, rfl⟩
  · simp at h

/-- A `from_bool` argument of a term: its bits are the bits of its value. -/
theorem arg_bits {st : St} (hwf : WF st.pool) (ρ : Assign) {a : Nat} {xs : List Nat}
    (h : bitsOf st a = some xs) {w : Nat} (hty : typeOf st.pool a = some (.bv w)) :
    xs.length = w ∧ ∀ i, (evalV st.pool ρ w a).getLsbD i = bitD st.pool ρ xs i := by
  obtain ⟨args, hb, rfl⟩ := bitsOf_spec h
  obtain ⟨x, hx⟩ := eval_bv (ρ := ρ) hty
  obtain ⟨hn, hbits⟩ := fromBool_getLsbD hwf ρ hb hx
  refine ⟨by simp [hn], ?_⟩
  intro i
  rw [← hbits i]
  simp [evalV, hx]

/-! ## Per-operator bit lemmas -/

theorem bbVar_bits {st : St} (hwf : WF st.pool) (ρ : Assign) {a : Nat} {bs : List Nat}
    (h : bbVar st a bs = true) {w : Nat} {x : BitVec w} (hx : eval st.pool ρ a = .bv w x) :
    ∀ i, i < w → i < bs.length → bitD st.pool ρ bs i = x.getLsbD i := by
  intro i hi hil
  obtain ⟨b, hb⟩ := get_of_lt hil
  rw [bitD_of_get ρ hb]
  have hn := isNode_spec (allIdx_spec 0 bs h i b hb)
  simp only [Nat.zero_add] at hn
  have he := eval_node hwf ρ hn
  simp only [Op.eval, List.map, hx, bitofEval, hi, ite_true] at he
  simp [evalB, he]

theorem bbVal_bits {st : St} (hwf : WF st.pool) (ρ : Assign) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    {v : Nat} {bs : List Nat} (h : bbVal bi v bs = true) {w : Nat} :
    ∀ i, i < w → i < bs.length → bitD st.pool ρ bs i = (BitVec.ofNat w v).getLsbD i := by
  intro i hi hil
  obtain ⟨b, hb⟩ := get_of_lt hil
  rw [bitD_of_get ρ hb, BitVec.getLsbD_ofNat]
  have hf := allIdx_spec 0 bs h i b hb
  simp only [Nat.zero_add] at hf
  by_cases ht : v.testBit i
  · rw [ite_eq_left ht] at hf; simp at hf; subst hf; simp [evalB_tt hwf ρ htt, hi, ht]
  · rw [ite_eq_right ht] at hf; simp at hf; subst hf; simp [evalB_ff hwf ρ hff, ht]

theorem bbNot_bits {st : St} (hwf : WF st.pool) (ρ : Assign) {xs bs : List Nat}
    (h : zipAll (fun b x => isNotOf st b x) bs xs = true) :
    bs.length = xs.length ∧ ∀ i, i < bs.length → bitD st.pool ρ bs i = !bitD st.pool ρ xs i := by
  obtain ⟨hl, hf⟩ := zipAll_spec bs xs h
  refine ⟨hl, ?_⟩
  intro i hi
  obtain ⟨b, hb⟩ := get_of_lt hi
  obtain ⟨x, hx⟩ := get_of_lt (by rw [← hl]; exact hi)
  rw [bitD_of_get ρ hb, bitD_of_get ρ hx]
  exact evalB_not hwf ρ (hf i b x hb hx)

/-- Left-nested chains. -/
def foldChain (pool : Pool) (ρ : Assign) (f : Bool → Bool → Bool) : List Nat → Bool
  | [] => false
  | [c] => evalB pool ρ c
  | c :: rest => f (foldChain pool ρ f rest) (evalB pool ρ c)

theorem chainRev_spec {st : St} (ρ : Assign) {op : Op} {f : Bool → Bool → Bool}
    (hf : ∀ n l r, st.pool[n]? = some ⟨op, #[l, r]⟩ → evalB st.pool ρ n = f (evalB st.pool ρ l) (evalB st.pool ρ r)) :
    ∀ (rev : List Nat) (b : Nat), chainRev st op rev b = true → evalB st.pool ρ b = foldChain st.pool ρ f rev := by
  intro rev
  induction rev with
  | nil => intro b h; simp [chainRev] at h
  | cons c rest ih =>
    intro b h
    cases rest with
    | nil => simp [chainRev] at h; subst h; rfl
    | cons d rest' =>
      simp only [chainRev] at h
      split at h
      · rename_i op' args hb
        split at h
        · rename_i l r hl
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨h1, h2⟩, hc⟩ := h
          subst op'; subst r
          have hn : st.pool[b]? = some ⟨op, #[l, c]⟩ := by rw [hb]; congr; exact Array.ext' hl
          rw [hf b l c hn, ih l hc]
          rfl
        · simp at h
      · simp at h

theorem foldChain_eq_foldl {pool : Pool} (ρ : Assign) {f : Bool → Bool → Bool} {e : Bool}
    (hid : ∀ c, f e c = c) :
    ∀ (rev : List Nat), rev ≠ [] → foldChain pool ρ f rev = (rev.reverse.map (evalB pool ρ)).foldl f e := by
  intro rev
  induction rev with
  | nil => intro h; exact absurd rfl h
  | cons c rest ih =>
    intro _
    cases rest with
    | nil => simp [foldChain, hid]
    | cons d rest' =>
      simp only [foldChain]
      rw [ih (by simp)]
      simp [List.foldl_append]

/-- Bit `i` of a fold of bitwise operators is the fold of the bits. -/
theorem foldl_bv_getLsbD {w : Nat} (g : BitVec w → BitVec w → BitVec w) (f : Bool → Bool → Bool)
    (hg : ∀ (x y : BitVec w) i, i < w → (g x y).getLsbD i = f (x.getLsbD i) (y.getLsbD i)) (e : BitVec w) (i : Nat) (hi : i < w) :
    ∀ (l : List (BitVec w)), (l.foldl g e).getLsbD i = (l.map (·.getLsbD i)).foldl f (e.getLsbD i) := by
  intro l
  induction l generalizing e with
  | nil => rfl
  | cons x rest ih => simp only [List.foldl_cons, List.map_cons]; rw [ih, hg e x i hi]

theorem bbBitwise_spec {st : St} (ρ : Assign) {op : Op} {f : Bool → Bool → Bool}
    (hf : ∀ n l r, st.pool[n]? = some ⟨op, #[l, r]⟩ → evalB st.pool ρ n = f (evalB st.pool ρ l) (evalB st.pool ρ r))
    {e : Bool} (hid : ∀ c, f e c = c) (xss : List (List Nat)) (hne : xss ≠ []) :
    ∀ (k : Nat) (bs : List Nat), bbBitwise st op xss k bs = true →
      ∀ j b, bs[j]? = some b → ∃ col, mapOpt (fun xs => xs[k + j]?) xss = some col ∧
        evalB st.pool ρ b = (col.map (evalB st.pool ρ)).foldl f e := by
  intro k bs
  induction bs generalizing k with
  | nil => intro _ j b hj; simp at hj
  | cons b0 rest ih =>
    intro h j b hj
    simp only [bbBitwise] at h
    split at h
    · rename_i col hcol
      simp only [Bool.and_eq_true] at h
      cases j with
      | zero =>
        simp at hj; subst hj
        refine ⟨col, by simpa using hcol, ?_⟩
        rw [chainRev_spec ρ hf _ _ h.1, foldChain_eq_foldl ρ hid col.reverse, List.reverse_reverse]
        intro hc
        have hc' : col = [] := by simpa using hc
        subst hc'
        cases xss with
        | nil => exact hne rfl
        | cons _ _ => simp [mapOpt] at hcol; split at hcol <;> simp at hcol
      | succ j =>
        simp at hj
        obtain ⟨col', hc', hv⟩ := ih (k + 1) h.2 j b hj
        exact ⟨col', by rwa [show k + (j + 1) = k + 1 + j by omega], hv⟩
    · simp at h

/-! ## List helpers -/

theorem bitD_append {pool : Pool} (ρ : Assign) (L R : List Nat) (i : Nat) :
    bitD pool ρ (L ++ R) i = if i < L.length then bitD pool ρ L i else bitD pool ρ R (i - L.length) := by
  unfold bitD
  simp only [List.map_append, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_map]
  split <;> rfl

theorem mapOpt_singleton_inv {f : α → Option β} {l : List α} {y : β} (h : mapOpt f l = some [y]) :
    ∃ x, l = [x] ∧ f x = some y := by
  cases l with
  | nil => simp [mapOpt] at h
  | cons a rest =>
    simp only [mapOpt] at h
    split at h
    · rename_i b bs hb hbs
      simp at h; obtain ⟨rfl, rfl⟩ := h
      cases rest with
      | nil => exact ⟨a, rfl, hb⟩
      | cons _ _ => simp [mapOpt] at hbs; split at hbs <;> simp at hbs
    · simp at h

theorem mapOpt_pair_inv {f : α → Option β} {l : List α} {y1 y2 : β} (h : mapOpt f l = some [y1, y2]) :
    ∃ x1 x2, l = [x1, x2] ∧ f x1 = some y1 ∧ f x2 = some y2 := by
  cases l with
  | nil => simp [mapOpt] at h
  | cons a rest =>
    simp only [mapOpt] at h
    split at h
    · rename_i b bs hb hbs
      simp at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x2, rfl, hx2⟩ := mapOpt_singleton_inv hbs
      exact ⟨a, x2, rfl, hb, hx2⟩
    · simp at h

theorem mapOpt_cons_inv {f : α → Option β} {l : List α} {y : β} {ys : List β} (h : mapOpt f l = some (y :: ys)) :
    ∃ x xs, l = x :: xs ∧ f x = some y ∧ mapOpt f xs = some ys := by
  cases l with
  | nil => simp [mapOpt] at h
  | cons a rest =>
    simp only [mapOpt] at h
    split at h
    · rename_i b bs hb hbs
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨a, rest, rfl, hb, hbs⟩
    · simp at h

theorem mapOpt_nil_eq {f : α → Option β} {ys : List β} (h : mapOpt f [] = some ys) : ys = [] := by
  simp [mapOpt] at h; exact h

theorem mapOpt_nil_inv {f : α → Option β} {l : List α} (h : mapOpt f l = some []) : l = [] := by
  cases l with
  | nil => rfl
  | cons a rest => simp [mapOpt] at h; split at h <;> simp at h

/-! ## Unary and binary bit-vector nodes -/

theorem bvNot_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i a : Nat}
    (h : pool[i]? = some ⟨.bvNot w, #[a]⟩) :
    evalV pool ρ w i = ~~~ evalV pool ρ w a ∧ typeOf pool a = some (.bv w) ∧ typeOf pool i = some (.bv w) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := ht
  rw [typeOf_node hwf h] at h2
  cases hta : typeOf pool a <;> simp [mapOpt, hta, Op.resultTy, bvUnTy, tyGuard] at h2
  obtain ⟨⟨hw, rfl⟩, rfl⟩ := h2
  refine ⟨?_, rfl, ht⟩
  rw [evalV, eval_node hwf ρ h]
  simp only [Op.eval, List.map, evalV_spec hta, bvUn, Val.asBv_bv]
  simp [hw]

theorem unary_arg_bv {pool : Pool} (hwf : WF pool) {i x0 : Nat} {op : Op}
    (h : pool[i]? = some ⟨op, #[x0]⟩)
    (hop : (∀ t, op.resultTy [t] = none ∨ ∃ n, t = .bv n)) :
    ∃ n, typeOf pool x0 = some (.bv n) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  rw [typeOf_node hwf h] at ht
  simp only [mapOpt] at ht
  cases htx : typeOf pool x0 with
  | none => rw [htx] at ht; simp at ht
  | some tx =>
    rw [htx] at ht
    simp only [Option.bind_some] at ht
    rcases hop tx with hnone | ⟨n, rfl⟩
    · rw [hnone] at ht; simp at ht
    · exact ⟨n, rfl⟩

theorem extract_arg_bv {pool : Pool} (hwf : WF pool) {i x0 hi lo : Nat}
    (h : pool[i]? = some ⟨.bvExtract hi lo, #[x0]⟩) : ∃ n, typeOf pool x0 = some (.bv n) :=
  unary_arg_bv hwf h (fun t => by cases t <;> simp [Op.resultTy, bvExtractTy])

theorem sext_arg_bv {pool : Pool} (hwf : WF pool) {i x0 w e : Nat}
    (h : pool[i]? = some ⟨.bvSignExtend w e, #[x0]⟩) : ∃ n, typeOf pool x0 = some (.bv n) :=
  unary_arg_bv hwf h (fun t => by cases t <;> simp [Op.resultTy, bvExtTy])

/-- Concatenation of `from_bool` arguments, bitwise. -/
theorem concat_bits {st : St} (hwf : WF st.pool) (ρ : Assign) :
    ∀ (as : List Nat) (xss : List (List Nat)), mapOpt (bitsOf st) as = some xss →
      (∀ a ∈ as, ∃ n, typeOf st.pool a = some (.bv n)) → as ≠ [] →
      ∃ (n : Nat) (v : BitVec n), Val.concatVals (as.map (eval st.pool ρ)) = some (.bv n v) ∧
        n = xss.reverse.flatten.length ∧ ∀ i, v.getLsbD i = bitD st.pool ρ xss.reverse.flatten i := by
  intro as
  induction as with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons a rest ih =>
    intro xss hm hty _
    cases xss with
    | nil => exact absurd (mapOpt_nil_inv hm) (by simp)
    | cons xs xss' =>
    obtain ⟨x, xs', hl, hxs, hrest⟩ := mapOpt_cons_inv hm
    simp at hl; obtain ⟨rfl, rfl⟩ := hl
    obtain ⟨na, hna⟩ := hty a (by simp)
    obtain ⟨hla, hba⟩ := arg_bits hwf ρ hxs hna
    cases rest with
    | nil =>
      have := mapOpt_nil_eq hrest; subst this
      refine ⟨na, evalV st.pool ρ na a, ?_, by simp [hla], ?_⟩
      · simp only [List.map_cons, List.map_nil]
        rw [evalV_spec hna]; rfl
      · intro i; simpa using hba i
    | cons b rest' =>
      obtain ⟨n, v, hc, hn, hv⟩ := ih xss' hrest (fun x hx => hty x (by simp [hx])) (by simp)
      refine ⟨na + n, evalV st.pool ρ na a ++ v, ?_, ?_, ?_⟩
      · rw [List.map_cons, concatVals_cons_ne (by simp), hc, evalV_spec hna]; rfl
      · simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.length_append]; omega
      · intro i
        rw [BitVec.getLsbD_append]
        simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [bitD_append, ← hn]
        by_cases hlt : i < n
        · rw [ite_eq_left hlt, ite_eq_left hlt, hv]
        · rw [ite_eq_right hlt, ite_eq_right hlt, hba]

/-! ## The term theorem -/

/-! ## Ripple-carry adders -/

/-- The value of a bit list as a bit-vector of width `w`. -/
def valW (pool : Pool) (ρ : Assign) (w : Nat) (bs : List Nat) : BitVec w :=
  (BitVec.ofBoolListLE (bs.map (evalB pool ρ))).setWidth w

theorem valW_getLsbD {pool : Pool} (ρ : Assign) (w : Nat) (bs : List Nat) (i : Nat) :
    (valW pool ρ w bs).getLsbD i = (decide (i < w) && bitD pool ρ bs i) := by
  unfold valW bitD
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]

theorem valW_getLsbD_lt {pool : Pool} (ρ : Assign) {w : Nat} (bs : List Nat) {i : Nat} (hi : i < w) :
    (valW pool ρ w bs).getLsbD i = bitD pool ρ bs i := by
  rw [valW_getLsbD, decide_eq_true hi, Bool.true_and]

/-- A `from_bool` argument's value is the value of its bits. -/
theorem arg_valW {st : St} (hwf : WF st.pool) (ρ : Assign) {a : Nat} {xs : List Nat}
    (h : bitsOf st a = some xs) {w : Nat} (hty : typeOf st.pool a = some (.bv w)) :
    evalV st.pool ρ w a = valW st.pool ρ w xs := by
  obtain ⟨_, hb⟩ := arg_bits hwf ρ h hty
  apply bv_ext
  intro i hi
  rw [hb i, valW_getLsbD_lt ρ xs hi]

theorem args_valW {st : St} (hwf : WF st.pool) (ρ : Assign) {w : Nat} :
    ∀ (as : List Nat) (xss : List (List Nat)), mapOpt (bitsOf st) as = some xss →
      (∀ a ∈ as, typeOf st.pool a = some (.bv w)) → as.map (evalV st.pool ρ w) = xss.map (valW st.pool ρ w) := by
  intro as
  induction as with
  | nil => intro xss hm _; have := mapOpt_nil_eq hm; subst this; rfl
  | cons a rest ih =>
    intro xss hm hty
    cases xss with
    | nil => exact absurd (mapOpt_nil_inv hm) (by simp)
    | cons xs xss' =>
    obtain ⟨x, xs', hl, hx, hxs'⟩ := mapOpt_cons_inv hm
    simp at hl; obtain ⟨rfl, rfl⟩ := hl
    simp only [List.map_cons]
    rw [arg_valW hwf ρ hx (hty a (by simp)), ih xss' hxs' (fun x hx => hty x (by simp [hx]))]

/-- Carries of a ripple adder over bit lists. -/
def carryB (pool : Pool) (ρ : Assign) (as bs : List Nat) (init : Bool) : Nat → Bool
  | 0 => init
  | j + 1 => Bool.atLeastTwo (bitD pool ρ as j) (bitD pool ρ bs j) (carryB pool ρ as bs init j)

theorem atLeastTwo_eq (a b c : Bool) : Bool.atLeastTwo a b c = ((a && b) || ((a ^^ b) && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem carryNode_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {pa pb pc c : Nat}
    (h : carryNode st pa pb pc c = true) :
    evalB st.pool ρ c = Bool.atLeastTwo (evalB st.pool ρ pa) (evalB st.pool ρ pb) (evalB st.pool ρ pc) := by
  unfold carryNode at h
  split at h
  · rename_i args hc
    split at h
    · rename_i u v hl
      simp only [Bool.and_eq_true] at h
      obtain ⟨hu, hv⟩ := h
      split at hv
      · rename_i vargs hvn
        split at hv
        · rename_i x w' hl'
          simp only [Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hx, rfl⟩ := hv
          have hcn : st.pool[c]? = some ⟨.disj, #[u, v]⟩ := by rw [hc]; congr; exact Array.ext' hl
          have hvn' : st.pool[v]? = some ⟨.conj, #[x, w']⟩ := by rw [hvn]; congr; exact Array.ext' hl'
          rw [evalB_disj2 hwf ρ hcn, evalB_conj hwf ρ hu, evalB_conj2 hwf ρ hvn', evalB_xor hwf ρ hx, atLeastTwo_eq]
        · simp at hv
      · simp at hv
    · simp at h
  · simp at h

theorem rippleGo_spec {st : St} (hwf : WF st.pool) (ρ : Assign) :
    ∀ (as bs rs : List Nat) (pa pb pc : Nat), rippleGo st as bs rs pa pb pc = true →
      as.length = bs.length ∧ rs.length = as.length ∧
      ∀ j, j < rs.length → bitD st.pool ρ rs j =
        ((bitD st.pool ρ as j ^^ bitD st.pool ρ bs j) ^^
          carryB st.pool ρ (pa :: as) (pb :: bs) (evalB st.pool ρ pc) (j + 1)) := by
  intro as
  induction as with
  | nil =>
    intro bs rs pa pb pc h
    cases bs <;> cases rs <;> simp [rippleGo] at h
    exact ⟨rfl, rfl, fun j hj => by simp at hj⟩
  | cons a as ih =>
    intro bs rs pa pb pc h
    cases bs with
    | nil => simp [rippleGo] at h
    | cons b bs =>
      cases rs with
      | nil => simp [rippleGo] at h
      | cons r rs =>
        simp only [rippleGo] at h
        split at h
        · rename_i args hr
          split at h
          · rename_i s c hl
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨hs, hc⟩, hgo⟩ := h
            obtain ⟨hl1, hl2, hbits⟩ := ih bs rs a b c hgo
            refine ⟨by simp [hl1], by simp [hl2], ?_⟩
            intro j hj
            have hrn : st.pool[r]? = some ⟨.boolXor, #[s, c]⟩ := by rw [hr]; congr; exact Array.ext' hl
            cases j with
            | zero =>
              simp only [bitD, List.map_cons, List.getD_cons_zero]
              rw [evalB_xor2 hwf ρ hrn, evalB_xor hwf ρ hs, carryNode_spec hwf ρ hc]
              rfl
            | succ j =>
              simp only [List.length_cons] at hj
              have := hbits j (by omega)
              simp only [bitD, List.map_cons, List.getD_cons_succ] at this ⊢
              rw [this]
              congr 1
              -- carries agree: the prefix `pa pb pc` is one step earlier
              have key : ∀ k, carryB st.pool ρ (a :: as) (b :: bs) (evalB st.pool ρ c) k =
                  carryB st.pool ρ (pa :: a :: as) (pb :: b :: bs) (evalB st.pool ρ pc) (k + 1) := by
                intro k
                induction k with
                | zero => simp [carryB]; rw [carryNode_spec hwf ρ hc]; rfl
                | succ k ihk => simp only [carryB]; rw [ihk]; rfl
              exact key (j + 1)
          · simp at h
        · simp at h

theorem ripple_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    {a b res : List Nat} {init : Bool} (h : ripple st bi a b res init = true) :
    a.length = b.length ∧ res.length = a.length ∧
    ∀ j, j < res.length → bitD st.pool ρ res j =
      ((bitD st.pool ρ a j ^^ bitD st.pool ρ b j) ^^ carryB st.pool ρ a b init j) := by
  unfold ripple at h
  split at h
  · rename_i a0 as b0 bs r0 rs
    split at h
    · rename_i args hr
      split at h
      · rename_i s c hl
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨hs, hc⟩, hgo⟩ := h
        obtain ⟨hl1, hl2, hbits⟩ := rippleGo_spec hwf ρ as bs rs a0 b0 c hgo
        have hcv : evalB st.pool ρ c = init := by
          rw [hc]; cases init
          · exact evalB_ff hwf ρ hff
          · exact evalB_tt hwf ρ htt
        refine ⟨by simp [hl1], by simp [hl2], ?_⟩
        intro j hj
        have hrn : st.pool[r0]? = some ⟨.boolXor, #[s, c]⟩ := by rw [hr]; congr; exact Array.ext' hl
        cases j with
        | zero =>
          simp only [bitD, List.map_cons, List.getD_cons_zero, carryB]
          rw [evalB_xor2 hwf ρ hrn, evalB_xor hwf ρ hs, hcv]
        | succ j =>
          simp only [List.length_cons] at hj
          have := hbits j (by omega)
          rw [hcv] at this
          simp only [bitD, List.map_cons, List.getD_cons_succ] at this ⊢
          exact this
      · simp at h
    · simp at h
  · simp at h

theorem carryB_eq_carry {pool : Pool} (ρ : Assign) {w : Nat} (a b : List Nat) (init : Bool) :
    ∀ k, k ≤ w → carryB pool ρ a b init k = BitVec.carry k (valW pool ρ w a) (valW pool ρ w b) init := by
  intro k
  induction k with
  | zero => intro _; simp [carryB]
  | succ k ih =>
    intro hk
    rw [carryB, BitVec.carry_succ, ih (by omega), valW_getLsbD_lt ρ a (by omega), valW_getLsbD_lt ρ b (by omega)]

/-- A ripple adder computes the sum. -/
theorem ripple_valW {st : St} (hwf : WF st.pool) (ρ : Assign) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    {a b res : List Nat} {init : Bool} (h : ripple st bi a b res init = true) {w : Nat} (hw : res.length = w) :
    valW st.pool ρ w res = valW st.pool ρ w a + valW st.pool ρ w b + BitVec.setWidth w (BitVec.ofBool init) := by
  obtain ⟨_, _, hbits⟩ := ripple_spec hwf ρ htt hff h
  apply bv_ext
  intro i hi
  rw [BitVec.getLsbD_add_add_bool hi, valW_getLsbD_lt ρ res hi, valW_getLsbD_lt ρ a hi, valW_getLsbD_lt ρ b hi,
    hbits i (by omega), ← carryB_eq_carry ρ a b init i (by omega), Bool.xor_assoc]

theorem setWidth_ofBool_false (w : Nat) : BitVec.setWidth w (BitVec.ofBool false) = 0#w := by
  apply bv_ext; intro i hi; simp

theorem setWidth_ofBool_true {w : Nat} (hw : 0 < w) : BitVec.setWidth w (BitVec.ofBool true) = 1#w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_one hw]
  have h1 : (BitVec.ofBool true).toNat = 1 := rfl
  have h2 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  rw [h1]
  exact Nat.mod_eq_of_lt h2

theorem preSum_length {st : St} : ∀ (sum pre : List Nat), preSum st sum = some pre → pre.length = sum.length := by
  intro sum
  induction sum with
  | nil => intro pre h; simp [preSum] at h; subst h; rfl
  | cons r rs ih =>
    intro pre h
    simp only [preSum] at h
    split at h
    · split at h
      · split at h
        · split at h
          · rename_i p _
            cases hp : preSum st rs with
            | none => rw [hp] at h; simp at h
            | some pre' => rw [hp] at h; simp at h; subst h; simp [ih pre' hp]
          · simp at h
        · simp at h
      · simp at h
    · simp at h

theorem bbAddRev_valW {st : St} (hwf : WF st.pool) (ρ : Assign) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    {w : Nat} : ∀ (rev : List (List Nat)) (sum : List Nat), bbAddRev st bi rev sum = true → sum.length = w →
      valW st.pool ρ w sum = (rev.reverse.map (valW st.pool ρ w)).foldl (· + ·) 0 := by
  intro rev
  induction rev with
  | nil => intro sum h; simp [bbAddRev] at h
  | cons xk rest ih =>
    intro sum h hlen
    cases rest with
    | nil =>
      simp only [bbAddRev, beq_iff_eq] at h; subst h
      simp [BitVec.zero_add]
    | cons x1 rest' =>
      simp only [bbAddRev] at h
      split at h
      · rename_i pre hpre
        simp only [Bool.and_eq_true] at h
        obtain ⟨hr, hrest⟩ := h
        have hpl : pre.length = w := by rw [preSum_length sum pre hpre, hlen]
        rw [ripple_valW hwf ρ htt hff hr hlen, ih pre hrest hpl, setWidth_ofBool_false, BitVec.add_zero]
        simp [List.foldl_append]
      · simp at h

theorem bbAdd_bits {st : St} (hok : TysOK st.pool st.tys) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    (ρ : Assign) {a : Nat} {w : Nat} {args : Array Nat} {xss : List (List Nat)} {bs : List Nat}
    (hn : st.pool[a]? = some ⟨.bvAdd w, args⟩) (hxss : mapOpt (bitsOf st) args.toList = some xss)
    (h : bbAddRev st bi xss.reverse bs = true) (hlen : bs.length = w) :
    ∀ i, i < w → bitD st.pool ρ bs i = (evalV st.pool ρ w a).getLsbD i := by
  intro i hi
  have hwf := hok.wf
  obtain ⟨hargs, _, _, _⟩ := bvN_args_bv hwf hn rfl
  rw [bvop_node hwf ρ w (.bvAdd w) (· + ·) 0 rfl (fun _ => rfl) a args hn,
    args_valW hwf ρ args.toList xss hxss (fun x hx => hargs x (by simpa using hx)),
    ← List.reverse_reverse xss, ← bbAddRev_valW hwf ρ htt hff xss.reverse bs h hlen, valW_getLsbD_lt ρ bs hi]

theorem zipAll_not_valW {st : St} (hwf : WF st.pool) (ρ : Assign) {pre xs : List Nat}
    (h : zipAll (fun p x => isNotOf st p x) pre xs = true) {w : Nat} (hw : pre.length = w) :
    valW st.pool ρ w pre = ~~~ valW st.pool ρ w xs := by
  obtain ⟨hl, hb⟩ := bbNot_bits hwf ρ h
  apply bv_ext
  intro i hi
  rw [valW_getLsbD_lt ρ pre hi, BitVec.getLsbD_not, valW_getLsbD_lt ρ xs hi, hb i (by omega)]
  simp [hi]

theorem all_ff_valW {st : St} (hwf : WF st.pool) (ρ : Assign) {bi : Builtins}
    (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩) {adder : List Nat}
    (h : adder.all (· == bi.ff) = true) (w : Nat) : valW st.pool ρ w adder = 0#w := by
  apply bv_ext
  intro i hi
  rw [valW_getLsbD_lt ρ adder hi, BitVec.getLsbD_zero]
  unfold bitD
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hx : adder[i]? with
  | none => rfl
  | some b =>
    have hb : b = bi.ff := by
      have := List.all_eq_true.mp h b (List.mem_of_getElem? hx)
      simpa using this
    subst hb
    simp [evalB_ff hwf ρ hff]

theorem bbNeg_bits {st : St} (hok : TysOK st.pool st.tys) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    (ρ : Assign) {a : Nat} {w : Nat} {x0 : Nat} {xs bs : List Nat}
    (hn : st.pool[a]? = some ⟨.bvNeg w, #[x0]⟩) (hxs : bitsOf st x0 = some xs)
    (h : bbNeg st bi xs bs = true) (hlen : bs.length = w) :
    ∀ i, i < w → bitD st.pool ρ bs i = (evalV st.pool ρ w a).getLsbD i := by
  intro i hi
  have hwf := hok.wf
  obtain ⟨hv, htx, _⟩ := bvNeg_node hwf ρ hn
  cases hpre : preSum st bs with
  | none => simp [bbNeg, hpre] at h
  | some pre =>
  cases hadder : preAdder st bs with
  | none => simp [bbNeg, hpre, hadder] at h
  | some adder =>
    simp only [bbNeg, hpre, hadder, Bool.and_eq_true] at h
    obtain ⟨⟨hnot, hzero⟩, hr⟩ := h
    have hpl : pre.length = w := by rw [preSum_length bs pre hpre, hlen]
    rw [hv, arg_valW hwf ρ hxs htx, ← valW_getLsbD_lt ρ bs hi, ripple_valW hwf ρ htt hff hr hlen,
      zipAll_not_valW hwf ρ hnot hpl, all_ff_valW hwf ρ hff hzero, setWidth_ofBool_true (by omega),
      BitVec.add_zero, BitVec.neg_eq_not_add]

theorem bbSub_bits {st : St} (hok : TysOK st.pool st.tys) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    (ρ : Assign) {a : Nat} {w : Nat} {x0 y0 : Nat} {xs ys bs : List Nat}
    (hn : st.pool[a]? = some ⟨.bvSub w, #[x0, y0]⟩) (hxs : bitsOf st x0 = some xs) (hys : bitsOf st y0 = some ys)
    (h : bbSub st bi xs ys bs = true) (hlen : bs.length = w) :
    ∀ i, i < w → bitD st.pool ρ bs i = (evalV st.pool ρ w a).getLsbD i := by
  intro i hi
  have hwf := hok.wf
  obtain ⟨hv, htx, hty, _⟩ := bvSub_node hwf ρ hn
  cases hadder : preAdder st bs with
  | none => simp [bbSub, hadder] at h
  | some adder =>
    simp only [bbSub, hadder, Bool.and_eq_true] at h
    obtain ⟨hnot, hr⟩ := h
    obtain ⟨hl1, hl2, _⟩ := ripple_spec hwf ρ htt hff hr
    have hal : adder.length = w := by rw [← hl1, ← hl2, hlen]
    rw [hv, arg_valW hwf ρ hxs htx, arg_valW hwf ρ hys hty, ← valW_getLsbD_lt ρ bs hi,
      ripple_valW hwf ρ htt hff hr hlen, zipAll_not_valW hwf ρ hnot hal, setWidth_ofBool_true (by omega),
      BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]

/-- Columns of the operand bit lists are the operand bits. -/
theorem columns_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {w i : Nat} :
    ∀ (as : List Nat) (xss : List (List Nat)) (col : List Nat), mapOpt (bitsOf st) as = some xss →
      mapOpt (fun xs => xs[i]?) xss = some col → (∀ a ∈ as, typeOf st.pool a = some (.bv w)) →
      col.map (evalB st.pool ρ) = (as.map (evalV st.pool ρ w)).map (·.getLsbD i) := by
  intro as
  induction as with
  | nil =>
    intro xss col hm hc _
    have := mapOpt_nil_eq hm; subst this
    have := mapOpt_nil_eq hc; subst this
    rfl
  | cons a rest ih =>
    intro xss col hm hc hty
    cases xss with
    | nil => exact absurd (mapOpt_nil_inv hm) (by simp)
    | cons xs xss' =>
    obtain ⟨x, xs', hl, hx, hxs'⟩ := mapOpt_cons_inv hm
    simp at hl; obtain ⟨rfl, rfl⟩ := hl
    cases col with
    | nil => exact absurd (mapOpt_nil_inv hc) (by simp)
    | cons c col' =>
    obtain ⟨y, col'', hcl, hcx, hcols⟩ := mapOpt_cons_inv hc
    simp at hcl; obtain ⟨rfl, rfl⟩ := hcl
    simp only [List.map_cons]
    rw [ih xss' col' hxs' hcols (fun x hx => hty x (by simp [hx]))]
    congr 1
    obtain ⟨_, hb⟩ := arg_bits hwf ρ hx (hty a (by simp))
    rw [hb i, bitD_of_get ρ hcx]

theorem bbBitwise_bits {st : St} (hok : TysOK st.pool st.tys) (ρ : Assign) {a w : Nat} {args : Array Nat}
    {op : Op} {bop : Op} {f : Bool → Bool → Bool} {g : BitVec w → BitVec w → BitVec w} {e : BitVec w}
    (hn : st.pool[a]? = some ⟨op, args⟩) (hres : op.resultTy = bvNTy w)
    (heval : ∀ vs, op.eval ρ vs = bvN w (List.foldl g e) vs)
    (hg : ∀ (x y : BitVec w) i, i < w → (g x y).getLsbD i = f (x.getLsbD i) (y.getLsbD i))
    (hf : ∀ n l r, st.pool[n]? = some ⟨bop, #[l, r]⟩ → evalB st.pool ρ n = f (evalB st.pool ρ l) (evalB st.pool ρ r))
    (hid : ∀ i, i < w → ∀ c, f (e.getLsbD i) c = c)
    {xss : List (List Nat)} {bs : List Nat}
    (hxss : mapOpt (bitsOf st) args.toList = some xss) (h : bbBitwise st bop xss 0 bs = true) (hlen : bs.length = w) :
    ∀ i, i < w → bitD st.pool ρ bs i = (evalV st.pool ρ w a).getLsbD i := by
  intro i hi
  have hwf := hok.wf
  obtain ⟨hargs, hl2, _, _⟩ := bvN_args_bv hwf hn hres
  rw [bvop_node hwf ρ w op g e hres heval a args hn, foldl_bv_getLsbD g f hg e i hi]
  obtain ⟨b, hb⟩ := get_of_lt (by omega : i < bs.length)
  rw [bitD_of_get ρ hb]
  have hne : xss ≠ [] := by
    intro hh; subst hh
    have := mapOpt_nil_inv hxss
    simp at this; subst this; simp at hl2
  obtain ⟨col, hcol, hv⟩ := bbBitwise_spec ρ hf (hid i hi) xss hne 0 bs h i b hb
  simp only [Nat.zero_add] at hcol
  rw [hv, columns_spec hwf ρ args.toList xss col hxss hcol (fun x hx => hargs x (by simpa using hx))]

/-! ## Comparators -/

/-- The comparator chain over the low `k` bits. -/
def ultK {w : Nat} (x y : BitVec w) (withEq : Bool) : Nat → Bool
  | 0 => withEq
  | k + 1 => ((x.getLsbD k == y.getLsbD k) && ultK x y withEq k) || (!x.getLsbD k && y.getLsbD k)

theorem getLsbD_eq_div_mod {w : Nat} (x : BitVec w) (k : Nat) :
    x.getLsbD k = decide (x.toNat / 2 ^ k % 2 = 1) := by
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]

theorem ultK_spec {w : Nat} (x y : BitVec w) (withEq : Bool) :
    ∀ k, ultK x y withEq k =
      (if withEq then decide (x.toNat % 2 ^ k ≤ y.toNat % 2 ^ k) else decide (x.toNat % 2 ^ k < y.toNat % 2 ^ k)) := by
  intro k
  induction k with
  | zero => cases withEq <;> simp [ultK, Nat.mod_one]
  | succ k ih =>
    simp only [ultK, ih, getLsbD_eq_div_mod]
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ]
    have hP : 0 < 2 ^ k := Nat.two_pow_pos k
    have hlx : x.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hP
    have hly : y.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hP
    generalize x.toNat % 2 ^ k = lx at *
    generalize y.toNat % 2 ^ k = ly at *
    generalize 2 ^ k = P at *
    rcases Nat.mod_two_eq_zero_or_one (x.toNat / P) with hbx | hbx <;>
    rcases Nat.mod_two_eq_zero_or_one (y.toNat / P) with hby | hby <;>
    cases withEq <;> simp only [hbx, hby, Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;>
    simp <;> omega

theorem ultK_ult {w : Nat} (x y : BitVec w) : ultK x y false w = x.ult y := by
  rw [ultK_spec, ite_eq_right (by simp), BitVec.toNat_mod_cancel, BitVec.toNat_mod_cancel]; rfl

theorem ultK_ule {w : Nat} (x y : BitVec w) : ultK x y true w = x.ule y := by
  rw [ultK_spec, ite_eq_left rfl, BitVec.toNat_mod_cancel, BitVec.toNat_mod_cancel]; rfl

/-- Signed comparison from the sign bits and the unsigned comparison of the rest. -/
theorem slt_bits {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    x.slt y = (((x.msb == y.msb) && ultK x y false (w - 1)) || (x.msb && !y.msb)) ∧
    x.sle y = (((x.msb == y.msb) && ultK x y true (w - 1)) || (x.msb && !y.msb)) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [ultK_spec, ultK_spec]
  simp only [BitVec.slt, BitVec.sle, BitVec.toInt_eq_msb_cond, BitVec.msb_eq_getLsbD_last, Nat.add_sub_cancel,
    getLsbD_eq_div_mod]
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k from Nat.pow_succ']
  have hx := x.isLt
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k from Nat.pow_succ'] at hx
  have hy := y.isLt
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k from Nat.pow_succ'] at hy
  have hxm := @Nat.mod_pow_succ x.toNat 2 k
  have hym := @Nat.mod_pow_succ y.toNat 2 k
  rw [Nat.mod_eq_of_lt (by rw [Nat.pow_succ']; exact hx)] at hxm
  rw [Nat.mod_eq_of_lt (by rw [Nat.pow_succ']; exact hy)] at hym
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlx : x.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hP
  have hly : y.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hP
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ k) with hbx | hbx <;>
  rcases Nat.mod_two_eq_zero_or_one (y.toNat / 2 ^ k) with hby | hby <;>
  simp only [hbx, hby, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hxm hym ⊢ <;>
  generalize x.toNat % 2 ^ k = lx at * <;>
  generalize y.toNat % 2 ^ k = ly at * <;>
  generalize x.toNat = X at * <;>
  generalize y.toNat = Y at * <;>
  generalize 2 ^ k = P at * <;>
  simp <;> omega

/-- The bits of a list in reverse order. -/
theorem reverse_bits {pool : Pool} (ρ : Assign) (xs : List Nat) {j x : Nat} (h : xs.reverse[j]? = some x) :
    j < xs.length ∧ evalB pool ρ x = bitD pool ρ xs (xs.length - 1 - j) := by
  have hj : j < xs.length := by
    have := (List.getElem?_eq_some_iff.mp h).1; simpa using this
  rw [List.getElem?_reverse hj] at h
  exact ⟨hj, (bitD_of_get ρ h).symm⟩

theorem ultGo_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {w : Nat} (x y : BitVec w) (withEq : Bool) :
    ∀ (ls rs : List Nat) (res k : Nat), ls.length = k → rs.length = k → 1 ≤ k →
      (∀ (j l : Nat), ls[j]? = some l → typeOf st.pool l = some .bool) →
      (∀ (j l : Nat), ls[j]? = some l → evalB st.pool ρ l = x.getLsbD (k - 1 - j)) →
      (∀ (j r : Nat), rs[j]? = some r → evalB st.pool ρ r = y.getLsbD (k - 1 - j)) →
      ultGo st withEq ls rs res = true → evalB st.pool ρ res = ultK x y withEq k := by
  intro ls
  induction ls with
  | nil => intro rs res k hl _ hk; simp at hl; omega
  | cons l ls ih =>
    intro rs res k hl hr hk hty hxb hyb h
    cases rs with
    | nil => simp at hr; omega
    | cons r rs =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hr
    have hxl : evalB st.pool ρ l = x.getLsbD k' := by
      have := hxb 0 l (by simp); simpa using this
    have hyr : evalB st.pool ρ r = y.getLsbD k' := by
      have := hyb 0 r (by simp); simpa using this
    have htl : typeOf st.pool l = some .bool := hty 0 l (by simp)
    cases ls with
    | nil =>
      cases rs with
      | cons _ _ => simp at hl hr; omega
      | nil =>
      simp at hl; subst hl
      simp only [ultGo, ultK] at h ⊢
      cases withEq with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, ultBase] at h
        split at h
        · rename_i args hres
          split at h
          · rename_i n r' hl2
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨rfl, hn⟩ := h
            have hcn : st.pool[res]? = some ⟨.conj, #[n, r']⟩ := by rw [hres]; congr; exact Array.ext' hl2
            rw [evalB_conj2 hwf ρ hcn, evalB_not hwf ρ hn, hxl, hyr]
            simp
          · simp at h
        · simp at h
      | true =>
        simp only [↓reduceIte] at h
        split at h
        · rename_i args hres
          split at h
          · rename_i res' e0 hl2
            simp only [Bool.and_eq_true] at h
            obtain ⟨he, hb⟩ := h
            have hdn : st.pool[res]? = some ⟨.disj, #[res', e0]⟩ := by rw [hres]; congr; exact Array.ext' hl2
            simp only [ultBase] at hb
            split at hb
            · rename_i bargs hres'
              split at hb
              · rename_i n r' hl3
                simp only [Bool.and_eq_true, beq_iff_eq] at hb
                obtain ⟨rfl, hn⟩ := hb
                have hcn : st.pool[res']? = some ⟨.conj, #[n, r']⟩ := by rw [hres']; congr; exact Array.ext' hl3
                rw [evalB_disj2 hwf ρ hdn, evalB_conj2 hwf ρ hcn, evalB_not hwf ρ hn, evalB_eq hwf ρ he htl, hxl, hyr]
                cases x.getLsbD 0 <;> cases y.getLsbD 0 <;> rfl
              · simp at hb
            · simp at hb
          · simp at h
        · simp at h
    | cons l2 ls' =>
      cases rs with
      | nil => simp at hl hr; omega
      | cons r2 rs' =>
      simp only [ultGo] at h
      split at h
      · rename_i args hres
        split at h
        · rename_i L R hl2
          simp only [Bool.and_eq_true] at h
          obtain ⟨hL, hR⟩ := h
          have hdn : st.pool[res]? = some ⟨.disj, #[L, R]⟩ := by rw [hres]; congr; exact Array.ext' hl2
          split at hL
          · rename_i largs hLn
            split at hL
            · rename_i e rest hl3
              simp only [Bool.and_eq_true] at hL
              obtain ⟨he, hrest⟩ := hL
              have hLc : st.pool[L]? = some ⟨.conj, #[e, rest]⟩ := by rw [hLn]; congr; exact Array.ext' hl3
              split at hR
              · rename_i rargs hRn
                split at hR
                · rename_i n r' hl4
                  simp only [Bool.and_eq_true, beq_iff_eq] at hR
                  obtain ⟨hn, rfl⟩ := hR
                  have hRc : st.pool[R]? = some ⟨.conj, #[n, r']⟩ := by rw [hRn]; congr; exact Array.ext' hl4
                  have hk' : 1 ≤ k' := by simp at hl; omega
                  have ih' := ih (r2 :: rs') rest k' hl hr hk'
                    (fun j l' hj => hty (j + 1) l' (by simpa using hj))
                    (fun j l' hj => by
                      have := hxb (j + 1) l' (by simpa using hj)
                      rwa [show k' + 1 - 1 - (j + 1) = k' - 1 - j by omega] at this)
                    (fun j r'' hj => by
                      have := hyb (j + 1) r'' (by simpa using hj)
                      rwa [show k' + 1 - 1 - (j + 1) = k' - 1 - j by omega] at this)
                    hrest
                  simp only [ultK]
                  rw [evalB_disj2 hwf ρ hdn, evalB_conj2 hwf ρ hLc, evalB_conj2 hwf ρ hRc, evalB_not hwf ρ hn,
                    evalB_eq hwf ρ he htl, ih', hxl, hyr]
                · simp at hR
              · simp at hR
            · simp at hL
          · simp at hL
        · simp at h
      · simp at h

theorem sltChain_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {w : Nat} (x y : BitVec w) (withEq : Bool)
    (hw : 2 ≤ w) {ls rs : List Nat} {res : Nat} (hl : ls.length = w) (hr : rs.length = w)
    (hty : ∀ (j l : Nat), ls[j]? = some l → typeOf st.pool l = some .bool)
    (hxb : ∀ (j l : Nat), ls[j]? = some l → evalB st.pool ρ l = x.getLsbD (w - 1 - j))
    (hyb : ∀ (j r : Nat), rs[j]? = some r → evalB st.pool ρ r = y.getLsbD (w - 1 - j))
    (h : sltChain st withEq ls rs res = true) :
    evalB st.pool ρ res = (((x.msb == y.msb) && ultK x y withEq (w - 1)) || (x.msb && !y.msb)) := by
  cases ls with
  | nil => simp at hl; omega
  | cons s ls' =>
  cases rs with
  | nil => simp at hr; omega
  | cons t rs' =>
  simp only [sltChain, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, h⟩ := h
  have hxs : evalB st.pool ρ s = x.msb := by
    have := hxb 0 s (by simp); rw [BitVec.msb_eq_getLsbD_last]; simpa using this
  have hyt : evalB st.pool ρ t = y.msb := by
    have := hyb 0 t (by simp); rw [BitVec.msb_eq_getLsbD_last]; simpa using this
  have hts : typeOf st.pool s = some .bool := hty 0 s (by simp)
  split at h
  · rename_i args hres
    split at h
    · rename_i S N hl2
      simp only [Bool.and_eq_true] at h
      obtain ⟨hN, hS⟩ := h
      have hdn : st.pool[res]? = some ⟨.disj, #[S, N]⟩ := by rw [hres]; congr; exact Array.ext' hl2
      split at hN
      · rename_i nargs hNn
        split at hN
        · rename_i l nr hl3
          simp only [Bool.and_eq_true, beq_iff_eq] at hN
          obtain ⟨rfl, hnr⟩ := hN
          have hNc : st.pool[N]? = some ⟨.conj, #[l, nr]⟩ := by rw [hNn]; congr; exact Array.ext' hl3
          split at hS
          · rename_i sargs hSn
            split at hS
            · rename_i e rest hl4
              simp only [Bool.and_eq_true] at hS
              obtain ⟨he, hrest⟩ := hS
              have hSc : st.pool[S]? = some ⟨.conj, #[e, rest]⟩ := by rw [hSn]; congr; exact Array.ext' hl4
              simp only [List.length_cons] at hl hr
              have hrest' := ultGo_spec hwf ρ x y withEq ls' rs' rest (w - 1) (by omega) (by omega) (by omega)
                (fun j l' hj => hty (j + 1) l' (by simpa using hj))
                (fun j l' hj => by
                  have := hxb (j + 1) l' (by simpa using hj)
                  rwa [show w - 1 - (j + 1) = w - 1 - 1 - j by omega] at this)
                (fun j r'' hj => by
                  have := hyb (j + 1) r'' (by simpa using hj)
                  rwa [show w - 1 - (j + 1) = w - 1 - 1 - j by omega] at this)
                hrest
              rw [evalB_disj2 hwf ρ hdn, evalB_conj2 hwf ρ hSc, evalB_conj2 hwf ρ hNc, evalB_not hwf ρ hnr,
                evalB_eq hwf ρ he hts, hrest', hxs, hyt, Bool.or_comm]
            · simp at hS
          · simp at hS
        · simp at hN
      · simp at hN
    · simp at h
  · simp at h

/-! ## Atoms -/

/-- A conjunction node evaluates to the conjunction of its arguments. -/
theorem evalB_conjN {st : St} (hwf : WF st.pool) (ρ : Assign) {e : Nat} {args : Array Nat}
    (he : st.pool[e]? = some ⟨.conj, args⟩) :
    evalB st.pool ρ e = (args.toList.map (evalB st.pool ρ)).all id := by
  have hargs := boolN_args_bool hwf (Or.inr he)
  have hbool := typed_bool_of_bool_node hwf he (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ρ
  rw [eval_node hwf ρ he] at hbool
  simp only [Op.eval, boolN] at hbool
  simp only [bools_map_evalB (l := args.toList) (fun a ha => hargs a (by simpa using ha))] at hbool
  split at hbool
  · injection hbool with hb; exact hb.symm
  · exact absurd hbool (by simp)

theorem eqBits_spec {st : St} : ∀ (cs xs ys : List Nat), bbAtom.eqBits st cs xs ys = true →
    cs.length = xs.length ∧ xs.length = ys.length ∧
    ∀ (j c x y : Nat), cs[j]? = some c → xs[j]? = some x → ys[j]? = some y → isEqOf st c x y = true := by
  intro cs
  induction cs with
  | nil =>
    intro xs ys h
    cases xs <;> cases ys <;> simp [bbAtom.eqBits] at h
    exact ⟨rfl, rfl, fun j c x y hc _ _ => by simp at hc⟩
  | cons c cs ih =>
    intro xs ys h
    cases xs with
    | nil => simp [bbAtom.eqBits] at h
    | cons x xs =>
    cases ys with
    | nil => simp [bbAtom.eqBits] at h
    | cons y ys =>
    simp only [bbAtom.eqBits, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := ih xs ys h.2
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j c' x' y' hc hx hy
    cases j with
    | zero => simp at hc hx hy; subst hc; subst hx; subst hy; exact h.1
    | succ j => simp at hc hx hy; exact h3 j c' x' y' hc hx hy

/-- Comparison nodes on equal-width bit-vectors. -/
theorem eval_cmp_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {e a b : Nat} {op : Op}
    (he : pool[e]? = some ⟨op, #[a, b]⟩) (hop : op.resultTy = cmpTy)
    (f : {w : Nat} → BitVec w → BitVec w → Bool) (hf : op.eval ρ = bvCmp f)
    {w : Nat} (hta : typeOf pool a = some (.bv w)) :
    typeOf pool b = some (.bv w) ∧ eval pool ρ e = .bool (f (evalV pool ρ w a) (evalV pool ρ w b)) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf e _ he).2
  have h2 := ht
  rw [typeOf_node hwf he, hop] at h2
  simp only [mapOpt, hta] at h2
  cases htb : typeOf pool b with
  | none => rw [htb] at h2; simp at h2
  | some tb =>
    rw [htb] at h2
    cases tb with
    | bv w' =>
      simp [cmpTy, tyGuard, Ty.sameBv] at h2
      obtain ⟨rfl, _⟩ := h2
      refine ⟨rfl, ?_⟩
      rw [eval_node hwf ρ he, hf]
      simp only [List.map, evalV_spec hta, evalV_spec htb, bvCmp]
      simp
    | bool => simp [cmpTy, tyGuard, Ty.sameBv] at h2
    | list _ _ => simp [cmpTy, tyGuard, Ty.sameBv] at h2

theorem bits_typed {st : St} (hwf : WF st.pool) {x : Nat} {xs : List Nat} (h : bitsOf st x = some xs) :
    ∀ (j l : Nat), xs[j]? = some l → typeOf st.pool l = some .bool := by
  obtain ⟨args, hb, rfl⟩ := bitsOf_spec h
  intro j l hj
  exact (fromBool_args_bool hwf hb).1 l (by simpa using List.mem_of_getElem? hj)

theorem bits_rev {st : St} (hwf : WF st.pool) (ρ : Assign) {x : Nat} {xs : List Nat} (h : bitsOf st x = some xs)
    {w : Nat} (hty : typeOf st.pool x = some (.bv w)) :
    xs.length = w ∧ ∀ (j l : Nat), xs.reverse[j]? = some l → evalB st.pool ρ l = (evalV st.pool ρ w x).getLsbD (w - 1 - j) := by
  obtain ⟨hl, hb⟩ := arg_bits hwf ρ h hty
  refine ⟨hl, ?_⟩
  intro j l hj
  obtain ⟨_, hv⟩ := reverse_bits ρ xs hj
  rw [hv, hb, hl]

theorem rev_typed {st : St} (hwf : WF st.pool) {x : Nat} {xs : List Nat} (h : bitsOf st x = some xs) :
    ∀ (j l : Nat), xs.reverse[j]? = some l → typeOf st.pool l = some .bool := by
  intro j l hj
  have hj' : j < xs.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; simpa using this
  rw [List.getElem?_reverse hj'] at hj
  exact bits_typed hwf h _ l hj

theorem sltChain_len {st : St} {withEq : Bool} {ls rs : List Nat} {res : Nat}
    (h : sltChain st withEq ls rs res = true) : 2 ≤ ls.length := by
  unfold sltChain at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp; omega
  · simp at h

theorem bbAtom_val {st : St} (hok : TysOK st.pool st.tys) (ρ : Assign) {a b : Nat}
    (h : bbAtom st a b = true) (_hta : typeOf st.pool a = some .bool) (htb : typeOf st.pool b = some .bool) :
    eval st.pool ρ a = eval st.pool ρ b := by
  have hwf := hok.wf
  unfold bbAtom at h
  split at h
  · rename_i op args hn
    split at h
    · rename_i x y hl
      have hn' : st.pool[a]? = some ⟨op, #[x, y]⟩ := by rw [hn]; congr; exact Array.ext' hl
      split at h
      · rename_i xs ys hxs hys
        obtain ⟨xargs, hxb, rfl⟩ := bitsOf_spec hxs
        obtain ⟨yargs, hyb, rfl⟩ := bitsOf_spec hys
        have htx := (fromBool_args_bool hwf hxb).2.2
        have hx1 := (fromBool_args_bool hwf hxb).2.1
        split at h
        · -- eq
          split at h
          · rename_i cs hb
            have hty2 := eq_args_same_ty hwf hn' htx
            obtain ⟨hl1, hl2, hbits⟩ := eqBits_spec cs.toList xargs.toList yargs.toList h
            rw [evalB_spec htb, evalB_conjN hwf ρ hb, eval_eq_bv hwf ρ hn' htx hty2]
            congr 1
            obtain ⟨_, hxv⟩ := arg_bits hwf ρ hxs htx
            obtain ⟨_, hyv⟩ := arg_bits hwf ρ hys hty2
            rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq, BitVec.eq_of_getLsbD_eq_iff]
            constructor
            · intro hall v hv
              obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hv
              rw [List.getElem?_map] at hi
              cases hc : cs.toList[i]? with
              | none => rw [hc] at hi; simp at hi
              | some c =>
                rw [hc] at hi; simp at hi; subst hi
                have hi' : i < xargs.size := by
                  have := (List.getElem?_eq_some_iff.mp hc).1; simp at this hl1; omega
                obtain ⟨xi, hxi⟩ := get_of_lt (show i < xargs.toList.length by simpa using hi')
                obtain ⟨yi, hyi⟩ := get_of_lt (show i < yargs.toList.length by simp at hl2 ⊢; omega)
                rw [evalB_eq hwf ρ (hbits i c xi yi hc hxi hyi) (bits_typed hwf hxs i xi hxi)]
                have := hall i hi'
                rw [hxv, hyv, bitD_of_get ρ hxi, bitD_of_get ρ hyi] at this
                simp [this]
            · intro hall i hi
              obtain ⟨c, hc⟩ := get_of_lt (show i < cs.toList.length by simp at hl1 ⊢; omega)
              obtain ⟨xi, hxi⟩ := get_of_lt (show i < xargs.toList.length by simpa using hi)
              obtain ⟨yi, hyi⟩ := get_of_lt (show i < yargs.toList.length by simp at hl2 ⊢; omega)
              have := hall (evalB st.pool ρ c) (List.mem_iff_getElem?.mpr ⟨i, by simp [hc]⟩)
              rw [evalB_eq hwf ρ (hbits i c xi yi hc hxi hyi) (bits_typed hwf hxs i xi hxi)] at this
              rw [hxv, hyv, bitD_of_get ρ hxi, bitD_of_get ρ hyi]
              simpa using this
          · simp at h
        · -- ult
          obtain ⟨hty2, hev⟩ := eval_cmp_node hwf ρ hn' rfl BitVec.ult rfl htx
          obtain ⟨hlx, hxr⟩ := bits_rev hwf ρ hxs htx
          obtain ⟨hly, hyr⟩ := bits_rev hwf ρ hys hty2
          rw [hev, evalB_spec htb]
          congr 1
          rw [ultGo_spec hwf ρ (evalV st.pool ρ xargs.size x) (evalV st.pool ρ xargs.size y) false _ _ b xargs.size
            (by simp) (by simp [hly]) hx1 (rev_typed hwf hxs) hxr hyr h, ultK_ult]
        · -- ule
          obtain ⟨hty2, hev⟩ := eval_cmp_node hwf ρ hn' rfl BitVec.ule rfl htx
          obtain ⟨hlx, hxr⟩ := bits_rev hwf ρ hxs htx
          obtain ⟨hly, hyr⟩ := bits_rev hwf ρ hys hty2
          rw [hev, evalB_spec htb]
          congr 1
          rw [ultGo_spec hwf ρ (evalV st.pool ρ xargs.size x) (evalV st.pool ρ xargs.size y) true _ _ b xargs.size
            (by simp) (by simp [hly]) hx1 (rev_typed hwf hxs) hxr hyr h, ultK_ule]
        · -- slt
          obtain ⟨hty2, hev⟩ := eval_cmp_node hwf ρ hn' rfl BitVec.slt rfl htx
          obtain ⟨hlx, hxr⟩ := bits_rev hwf ρ hxs htx
          obtain ⟨hly, hyr⟩ := bits_rev hwf ρ hys hty2
          rw [hev, evalB_spec htb]
          congr 1
          have hw2 : 2 ≤ xargs.size := by have := sltChain_len h; simpa using this
          rw [sltChain_spec hwf ρ (evalV st.pool ρ xargs.size x) (evalV st.pool ρ xargs.size y) false hw2
            (by simp) (by simp [hly]) (rev_typed hwf hxs) hxr hyr h, (slt_bits (by omega) _ _).1]
        · -- sle
          obtain ⟨hty2, hev⟩ := eval_cmp_node hwf ρ hn' rfl BitVec.sle rfl htx
          obtain ⟨hlx, hxr⟩ := bits_rev hwf ρ hxs htx
          obtain ⟨hly, hyr⟩ := bits_rev hwf ρ hys hty2
          rw [hev, evalB_spec htb]
          congr 1
          have hw2 : 2 ≤ xargs.size := by have := sltChain_len h; simpa using this
          rw [sltChain_spec hwf ρ (evalV st.pool ρ xargs.size x) (evalV st.pool ρ xargs.size y) true hw2
            (by simp) (by simp [hly]) (rev_typed hwf hxs) hxr hyr h, (slt_bits (by omega) _ _).2]
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-! ## Shifts and bit-vector ite -/
theorem bbIteArgs_spec {st : St} {r c t e : Nat} (h : bbIteArgs st r = some (c, t, e)) :
    st.pool[r]? = some ⟨.boolIte, #[c, t, e]⟩ := by
  unfold bbIteArgs at h
  split at h
  · rename_i args hr
    split at h
    · rename_i c' t' e' hl
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      rw [hr]; congr; exact Array.ext' hl
    · simp at h
  · simp at h

theorem bbs_boolIte_args {pool : Pool} (hwf : WF pool) {n c t e : Nat}
    (hn : pool[n]? = some ⟨.boolIte, #[c, t, e]⟩) :
    typeOf pool c = some .bool ∧ typeOf pool t = some .bool ∧ typeOf pool e = some .bool := by
  have hty := (hwf n _ hn).2
  rw [typeOf_node hwf hn] at hty
  simp only [mapOpt, Op.resultTy] at hty
  cases htc : typeOf pool c <;> rw [htc] at hty <;> cases hta : typeOf pool t <;> rw [hta] at hty <;>
    cases htb : typeOf pool e <;> rw [htb] at hty <;> simp [boolIteTy, tyGuard] at hty
  obtain ⟨rfl, rfl, rfl⟩ := hty
  exact ⟨rfl, rfl, rfl⟩

theorem evalB_ite {st : St} (hwf : WF st.pool) (ρ : Assign) {n c t e : Nat}
    (hn : st.pool[n]? = some ⟨.boolIte, #[c, t, e]⟩) :
    evalB st.pool ρ n = (if evalB st.pool ρ c then evalB st.pool ρ t else evalB st.pool ρ e) := by
  obtain ⟨htc, htt, hte⟩ := bbs_boolIte_args hwf hn
  have h := eval_ite_sel hwf (Or.inl hn) ρ (evalB_spec htc)
  rw [evalB_spec htt, evalB_spec hte] at h
  by_cases hc : evalB st.pool ρ c = true
  · rw [ite_eq_left hc] at h; rw [ite_eq_left hc]; simp [evalB, h]
  · rw [ite_eq_right hc] at h; rw [ite_eq_right hc]; simp [evalB, h]

theorem bbs_not_arg_bool {pool : Pool} (hwf : WF pool) {n c : Nat}
    (hn : pool[n]? = some ⟨.boolNot, #[c]⟩) : typeOf pool c = some .bool := by
  have hty := (hwf n _ hn).2
  rw [typeOf_node hwf hn] at hty
  simp only [mapOpt, Op.resultTy] at hty
  cases htc : typeOf pool c <;> rw [htc] at hty <;> simp [boolNotTy, tyGuard] at hty
  rw [hty]

theorem evalB_falseNode {st : St} (hwf : WF st.pool) (ρ : Assign) {f : Nat} (h : isFalseNode st f = true) :
    evalB st.pool ρ f = false :=
  evalB_ff hwf ρ (isNode_spec h)

theorem bbMapIdx_spec {f : Nat → Nat → Option Nat} : ∀ (k : Nat) (l l' : List Nat), bbMapIdx f k l = some l' →
    l'.length = l.length ∧ ∀ j x, l[j]? = some x → ∃ y, l'[j]? = some y ∧ f (k + j) x = some y := by
  intro k l
  induction l generalizing k with
  | nil => intro l' h; simp [bbMapIdx] at h; subst h; exact ⟨rfl, fun j x hx => by simp at hx⟩
  | cons x xs ih =>
    intro l' h
    simp only [bbMapIdx] at h
    split at h
    · rename_i y ys hy hys
      simp at h; subst h
      obtain ⟨hl, hf⟩ := ih (k + 1) ys hys
      refine ⟨by simp [hl], ?_⟩
      intro j x' hx
      cases j with
      | zero => simp at hx; subst hx; exact ⟨y, by simp, by simpa using hy⟩
      | succ j =>
        simp at hx
        obtain ⟨y', hy', hf'⟩ := hf j x' hx
        exact ⟨y', by simpa using hy', by rwa [show k + (j + 1) = k + 1 + j by omega]⟩
    · simp at h

theorem bbShiftLimit_spec {st : St} {cond : Nat} {isFill : Nat → Bool} :
    ∀ (bs res : List Nat), bbShiftLimit st cond isFill bs = some res →
      res.length = bs.length ∧ ∀ (j b : Nat), bs[j]? = some b →
        ∃ r f, res[j]? = some r ∧ st.pool[b]? = some (⟨.boolIte, #[cond, r, f]⟩ : Node) ∧ isFill f = true := by
  intro bs
  induction bs with
  | nil => intro res h; simp [bbShiftLimit] at h; subst h; exact ⟨rfl, fun j b hb => by simp at hb⟩
  | cons b bs ih =>
    intro res h
    simp only [bbShiftLimit] at h
    split at h
    · rename_i c r f hargs
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, hfill⟩ := hc
        cases hrest : bbShiftLimit st c isFill bs with
        | none => rw [hrest] at h; simp at h
        | some res' =>
          rw [hrest] at h; simp at h; subst h
          obtain ⟨hl, hf⟩ := ih res' hrest
          refine ⟨by simp [hl], ?_⟩
          intro j b' hb
          cases j with
          | zero => simp at hb; subst hb; exact ⟨r, f, by simp, bbIteArgs_spec hargs, hfill⟩
          | succ j =>
            simp at hb
            obtain ⟨r', f', hr', hn, hf'⟩ := hf j b' hb
            exact ⟨r', f', by simpa using hr', hn, hf'⟩
      · simp at h
    · simp at h

theorem bbLog2_spec (n : Nat) : n ≤ 2 ^ bbLog2 n := by
  unfold bbLog2
  split
  · rename_i h; simp; omega
  · rename_i h
    have := @Nat.lt_log2_self (n - 1)
    omega

theorem bbWidthBits_length (bi : Builtins) (width n : Nat) : (bbWidthBits bi width n).length = n := by
  simp [bbWidthBits]

theorem bbWidthBits_bitD {st : St} (hwf : WF st.pool) (ρ : Assign) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    (width n i : Nat) (hi : i < n) :
    bitD st.pool ρ (bbWidthBits bi width n) i = width.testBit i := by
  have hg : (bbWidthBits bi width n)[i]? = some (if width.testBit i then bi.tt else bi.ff) := by
    simp [bbWidthBits, hi]
  rw [bitD_of_get ρ hg]
  by_cases ht : width.testBit i
  · simp [ht, evalB_tt hwf ρ htt]
  · simp [ht, evalB_ff hwf ρ hff]

/-! ### Barrel-shifter stages -/

theorem bbLshStage_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {b T : Nat} {res pre : List Nat}
    (h : bbLshStage st b T res = some pre) :
    pre.length = res.length ∧ ∀ j, j < res.length →
      bitD st.pool ρ res j = (if evalB st.pool ρ b then (if j < T then false else bitD st.pool ρ pre (j - T))
        else bitD st.pool ρ pre j) := by
  unfold bbLshStage at h
  split at h
  · rename_i pre' hmap
    split at h
    · rename_i hall
      simp at h; subst h
      obtain ⟨hl, hf⟩ := bbMapIdx_spec 0 res _ hmap
      refine ⟨hl, ?_⟩
      intro j hj
      obtain ⟨r, hr⟩ := get_of_lt hj
      obtain ⟨p, hp, hfp⟩ := hf j r hr
      have ha := allIdx_spec 0 res hall j r hr
      simp only [Nat.zero_add] at ha
      cases hargs : bbIteArgs st r with
      | none => simp [hargs] at hfp
      | some ct =>
        obtain ⟨c, inj, e⟩ := ct
        rw [hargs] at hfp ha
        simp at hfp; subst hfp
        simp only [Bool.and_eq_true, beq_iff_eq] at ha
        obtain ⟨rfl, ha⟩ := ha
        rw [bitD_of_get ρ hr, evalB_ite hwf ρ (bbIteArgs_spec hargs), bitD_of_get ρ hp]
        by_cases hb : evalB st.pool ρ c = true
        · simp only [hb, ite_true]
          split
          · rename_i hjT; rw [ite_eq_left hjT] at ha; exact evalB_falseNode hwf ρ ha
          · rename_i hjT; rw [ite_eq_right hjT] at ha; exact (bitD_of_get ρ (beq_iff_eq.mp ha)).symm
        · simp [hb]
    · simp at h
  · simp at h

theorem bbRshStage_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {isFill : Nat → Bool} {b T : Nat}
    {res pre : List Nat} (h : bbRshStage st isFill b T res = some pre) {fill : Bool}
    (hfill : ∀ f, isFill f = true → evalB st.pool ρ f = fill) :
    pre.length = res.length ∧ ∀ j, j < res.length →
      bitD st.pool ρ res j = (if evalB st.pool ρ b then (if j + T < res.length then bitD st.pool ρ pre (j + T) else fill)
        else bitD st.pool ρ pre j) := by
  unfold bbRshStage at h
  split at h
  · rename_i pre' hmap
    split at h
    · rename_i hall
      simp at h; subst h
      obtain ⟨hl, hf⟩ := bbMapIdx_spec 0 res _ hmap
      refine ⟨hl, ?_⟩
      intro j hj
      obtain ⟨r, hr⟩ := get_of_lt hj
      obtain ⟨p, hp, hfp⟩ := hf j r hr
      simp only [Nat.zero_add] at hfp
      have ha := allIdx_spec 0 res hall j r hr
      simp only [Nat.zero_add] at ha
      cases hargs : bbIteArgs st r with
      | none => simp [hargs] at hfp
      | some ct =>
        obtain ⟨c, t, e⟩ := ct
        rw [hargs] at hfp ha
        simp only [Option.map_some, Option.some.injEq] at hfp ha
        rw [bitD_of_get ρ hr, evalB_ite hwf ρ (bbIteArgs_spec hargs), bitD_of_get ρ hp]
        by_cases hjT : j + T ≥ res.length
        · rw [ite_eq_left hjT] at ha hfp
          simp only [Bool.and_eq_true, beq_iff_eq] at ha
          obtain ⟨rfl, ha⟩ := ha
          subst hfp
          rw [hfill t ha, ite_eq_right (show ¬ (j + T < res.length) by omega)]
        · rw [ite_eq_right hjT] at ha hfp
          simp only [Bool.and_eq_true, beq_iff_eq] at ha
          obtain ⟨hnot, he⟩ := ha
          subst hfp
          rw [evalB_not hwf ρ hnot, ite_eq_left (show j + T < res.length by omega), ← bitD_of_get ρ he]
          cases evalB st.pool ρ b <;> simp
    · simp at h
  · simp at h

theorem bbLshStage_valW {st : St} (hwf : WF st.pool) (ρ : Assign) {b T : Nat} {res pre : List Nat}
    (h : bbLshStage st b T res = some pre) {w : Nat} (hlen : res.length = w) {X : BitVec w} {s : Nat}
    (hpre : valW st.pool ρ w pre = X <<< s) :
    valW st.pool ρ w res = X <<< (if evalB st.pool ρ b then s + T else s) := by
  obtain ⟨hl, hbits⟩ := bbLshStage_spec hwf ρ h
  apply bv_ext
  intro i hi
  rw [valW_getLsbD_lt ρ res hi, hbits i (by omega)]
  have h1 : bitD st.pool ρ pre i = (X <<< s).getLsbD i := by rw [← hpre, valW_getLsbD_lt ρ pre hi]
  have h2 : bitD st.pool ρ pre (i - T) = (X <<< s).getLsbD (i - T) := by
    rw [← hpre, valW_getLsbD_lt ρ pre (by omega)]
  rw [h1, h2]
  cases evalB st.pool ρ b with
  | false => simp
  | true =>
    simp only [ite_true, BitVec.getLsbD_shiftLeft]
    by_cases hiT : i < T
    · simp [hiT]; omega
    · simp only [hiT, ite_false, hi, decide_true, Bool.true_and]
      by_cases his : i < s + T
      · simp [his]; omega
      · simp only [his, decide_false, Bool.not_false, Bool.true_and]
        rw [show i - T - s = i - (s + T) by omega]
        simp; omega

theorem bbRshStage_valW_ushift {st : St} (hwf : WF st.pool) (ρ : Assign) {isFill : Nat → Bool} {b T : Nat}
    {res pre : List Nat} (h : bbRshStage st isFill b T res = some pre)
    (hfill : ∀ f, isFill f = true → evalB st.pool ρ f = false)
    {w : Nat} (hlen : res.length = w) {X : BitVec w} {s : Nat} (hpre : valW st.pool ρ w pre = X >>> s) :
    valW st.pool ρ w res = X >>> (if evalB st.pool ρ b then s + T else s) := by
  obtain ⟨hl, hbits⟩ := bbRshStage_spec hwf ρ h hfill
  apply bv_ext
  intro i hi
  rw [valW_getLsbD_lt ρ res hi, hbits i (by omega), hlen]
  have h1 : bitD st.pool ρ pre i = (X >>> s).getLsbD i := by rw [← hpre, valW_getLsbD_lt ρ pre hi]
  rw [h1]
  cases evalB st.pool ρ b with
  | false => simp
  | true =>
    simp only [ite_true, BitVec.getLsbD_ushiftRight]
    by_cases hiT : i + T < w
    · rw [ite_eq_left hiT, ← valW_getLsbD_lt ρ pre hiT, hpre, BitVec.getLsbD_ushiftRight,
        show s + (i + T) = s + T + i by omega]
    · rw [ite_eq_right hiT, BitVec.getLsbD_of_ge _ _ (by omega)]

theorem bbRshStage_valW_sshift {st : St} (hwf : WF st.pool) (ρ : Assign) {isFill : Nat → Bool} {b T : Nat}
    {res pre : List Nat} (h : bbRshStage st isFill b T res = some pre)
    {w : Nat} {X : BitVec w} (hfill : ∀ f, isFill f = true → evalB st.pool ρ f = X.msb)
    (hlen : res.length = w) {s : Nat} (hpre : valW st.pool ρ w pre = X.sshiftRight s) :
    valW st.pool ρ w res = X.sshiftRight (if evalB st.pool ρ b then s + T else s) := by
  obtain ⟨hl, hbits⟩ := bbRshStage_spec hwf ρ h hfill
  apply bv_ext
  intro i hi
  rw [valW_getLsbD_lt ρ res hi, hbits i (by omega), hlen]
  have h1 : bitD st.pool ρ pre i = (X.sshiftRight s).getLsbD i := by rw [← hpre, valW_getLsbD_lt ρ pre hi]
  rw [h1]
  cases evalB st.pool ρ b with
  | false => simp
  | true =>
    simp only [ite_true, BitVec.getLsbD_sshiftRight]
    by_cases hiT : i + T < w
    · rw [ite_eq_left hiT, ← valW_getLsbD_lt ρ pre hiT, hpre, BitVec.getLsbD_sshiftRight]
      simp only [show ¬ (w ≤ i + T) by omega, show ¬ (w ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and]
      rw [show s + (i + T) = s + T + i by omega]
    · rw [ite_eq_right hiT]
      simp only [show ¬ (w ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and]
      rw [ite_eq_right (by omega)]

/-- The stages `L-1 … 0` shift by the low `L` bits of `y`. -/
theorem bbStages_spec {st : St} (ρ : Assign) {w : Nat} (X : BitVec w) (sh : BitVec w → Nat → BitVec w)
    (hsh0 : sh X 0 = X) {stage : Nat → Nat → List Nat → Option (List Nat)} {ys : List Nat} (y : BitVec w)
    (hys : ∀ i b, ys[i]? = some b → evalB st.pool ρ b = y.getLsbD i)
    (hstage_len : ∀ b T res pre, stage b T res = some pre → pre.length = res.length)
    (hstage : ∀ b T res pre, stage b T res = some pre → res.length = w → ∀ s, valW st.pool ρ w pre = sh X s →
        valW st.pool ρ w res = sh X (if evalB st.pool ρ b then s + T else s))
    {xs : List Nat} (hX : valW st.pool ρ w xs = X) :
    ∀ (L : Nat) (res : List Nat), bbStages stage ys L res = some xs → res.length = w →
      valW st.pool ρ w res = sh X (y.toNat % 2 ^ L) := by
  intro L
  induction L with
  | zero =>
    intro res h _
    simp only [bbStages, Option.some.injEq] at h
    subst h
    simp [Nat.mod_one, hsh0, hX]
  | succ i ih =>
    intro res h hlen
    simp only [bbStages] at h
    split at h
    · rename_i b hb
      split at h
      · rename_i pre hpre
        have hpl : pre.length = w := by rw [hstage_len b _ res pre hpre, hlen]
        have ihp := ih pre h hpl
        rw [hstage b (2 ^ i) res pre hpre hlen _ ihp, hys i b hb, getLsbD_eq_div_mod, Nat.mod_pow_succ]
        rcases Nat.mod_two_eq_zero_or_one (y.toNat / 2 ^ i) with h0 | h1
        · simp [h0]
        · simp [h1]
      · simp at h
    · simp at h

/-! ### Shift and ite nodes -/

/-- A binary same-width bit-vector node (`bvBinTy`/`bvBin`). -/
theorem bbs_bvBin_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i a b : Nat} {op : Op}
    (f : BitVec w → BitVec w → BitVec w) (hres : op.resultTy = bvBinTy w) (heval : op.eval ρ = bvBin w f)
    (h : pool[i]? = some ⟨op, #[a, b]⟩) :
    evalV pool ρ w i = f (evalV pool ρ w a) (evalV pool ρ w b) ∧
    typeOf pool a = some (.bv w) ∧ typeOf pool b = some (.bv w) ∧ typeOf pool i = some (.bv w) ∧ w ≠ 0 := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := ht
  rw [typeOf_node hwf h] at h2
  simp only [hres] at h2
  cases hta : typeOf pool a <;> cases htb : typeOf pool b <;>
    simp [mapOpt, hta, htb, bvBinTy, tyGuard] at h2
  obtain ⟨⟨hw, h3, h4⟩, h5⟩ := h2
  subst h3; subst h4; subst h5
  refine ⟨?_, rfl, rfl, ht, hw⟩
  rw [evalV, eval_node hwf ρ h]
  simp only [heval, List.map, evalV_spec hta, evalV_spec htb, bvBin, Val.asBv_bv]
  simp [hw]

/-- A bit-vector ite node whose condition is boolean. -/
theorem bbs_bvIte_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i c t e : Nat}
    (h : pool[i]? = some ⟨.bvIte w, #[c, t, e]⟩) (htc : typeOf pool c = some .bool) :
    evalV pool ρ w i = (if evalB pool ρ c then evalV pool ρ w t else evalV pool ρ w e) ∧
    typeOf pool t = some (.bv w) ∧ typeOf pool e = some (.bv w) ∧ typeOf pool i = some (.bv w) := by
  obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := hty
  rw [typeOf_node hwf h] at h2
  simp only [mapOpt, Op.resultTy, htc] at h2
  cases hta : typeOf pool t <;> rw [hta] at h2 <;> cases htb : typeOf pool e <;> rw [htb] at h2 <;>
    simp [bvIteTy, tyGuard] at h2
  obtain ⟨⟨hw, h3, h4⟩, h5⟩ := h2
  subst h3; subst h4; subst h5
  refine ⟨?_, rfl, rfl, hty⟩
  have hsel := eval_ite_sel hwf (Or.inr ⟨w, h⟩) ρ (evalB_spec htc)
  rw [evalV_spec hta, evalV_spec htb] at hsel
  have key : eval pool ρ i = .bv w (if evalB pool ρ c then evalV pool ρ w t else evalV pool ρ w e) := by
    rw [hsel]; cases evalB pool ρ c <;> simp
  generalize (if evalB pool ρ c then evalV pool ρ w t else evalV pool ρ w e) = v at key ⊢
  simp [evalV, key]

theorem bbs_ys_bits {st : St} (hwf : WF st.pool) (ρ : Assign) {y0 : Nat} {ys : List Nat}
    (hys : bitsOf st y0 = some ys) {w : Nat} (hty : typeOf st.pool y0 = some (.bv w)) :
    ∀ (i b : Nat), ys[i]? = some b → evalB st.pool ρ b = (evalV st.pool ρ w y0).getLsbD i := by
  intro i b hb
  obtain ⟨_, hbits⟩ := arg_bits hwf ρ hys hty
  rw [hbits i, bitD_of_get ρ hb]

/-- The guard `y <ᵤ width` of a shift. -/
theorem bbs_shift_cond {st : St} (hwf : WF st.pool) (ρ : Assign) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    {y0 : Nat} {ys : List Nat} (hys : bitsOf st y0 = some ys) {w : Nat} (hty : typeOf st.pool y0 = some (.bv w))
    (hw : 1 ≤ w) {cond : Nat}
    (h : ultGo st false ys.reverse (bbWidthBits bi w ys.length).reverse cond = true) :
    evalB st.pool ρ cond = decide ((evalV st.pool ρ w y0).toNat < w) := by
  obtain ⟨hyl, hyb⟩ := bits_rev hwf ρ hys hty
  have hwb : ∀ (j r : Nat), (bbWidthBits bi w ys.length).reverse[j]? = some r →
      evalB st.pool ρ r = (BitVec.ofNat w w).getLsbD (w - 1 - j) := by
    intro j r hj
    obtain ⟨hjl, hv⟩ := reverse_bits ρ _ hj
    rw [bbWidthBits_length] at hjl hv
    rw [hv, hyl, bbWidthBits_bitD hwf ρ htt hff w w (w - 1 - j) (by omega), BitVec.getLsbD_ofNat]
    simp [show w - 1 - j < w by omega]
  rw [ultGo_spec hwf ρ (evalV st.pool ρ w y0) (BitVec.ofNat w w) false _ _ cond w (by simp [hyl])
    (by simp [bbWidthBits_length, hyl]) hw (rev_typed hwf hys) hyb hwb h, ultK_ult]
  simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self]

/-- Generic shift soundness: the guarded barrel shifter computes `sh x y.toNat`. -/
theorem bbShift_bits {st : St} (hok : TysOK st.pool st.tys) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    (ρ : Assign) {a w x0 y0 : Nat} {op : Op}
    (hn : st.pool[a]? = some ⟨op, #[x0, y0]⟩) (hres : op.resultTy = bvBinTy w)
    (f : BitVec w → BitVec w → BitVec w) (heval : op.eval ρ = bvBin w f)
    (sh : BitVec w → Nat → BitVec w) (hf : ∀ x y, f x y = sh x y.toNat) (hsh0 : ∀ x, sh x 0 = x)
    (fillV : BitVec w → Bool) (hover : ∀ x s j, w ≤ s → j < w → (sh x s).getLsbD j = fillV x)
    {isFill : Nat → Bool} {stage : Nat → Nat → List Nat → Option (List Nat)}
    {xs ys bs : List Nat} (hxs : bitsOf st x0 = some xs) (hys : bitsOf st y0 = some ys)
    (hfill : ∀ g, isFill g = true → evalB st.pool ρ g = fillV (valW st.pool ρ w xs))
    (hstage_len : ∀ b T res pre, stage b T res = some pre → pre.length = res.length)
    (hstage : ∀ b T res pre, stage b T res = some pre → res.length = w → ∀ s,
        valW st.pool ρ w pre = sh (valW st.pool ρ w xs) s →
        valW st.pool ρ w res = sh (valW st.pool ρ w xs) (if evalB st.pool ρ b then s + T else s))
    (h : bbShift st bi isFill stage xs ys bs = true) (hlen : bs.length = w) :
    ∀ i, i < w → bitD st.pool ρ bs i = (evalV st.pool ρ w a).getLsbD i := by
  intro i hi
  have hwf := hok.wf
  obtain ⟨hv, htx, hty, _, hw0⟩ := bbs_bvBin_node hwf ρ f hres heval hn
  rw [hv, hf, arg_valW hwf ρ hxs htx]
  obtain ⟨hxl, _⟩ := arg_bits hwf ρ hxs htx
  cases bs with
  | nil => simp [bbShift] at h
  | cons b0 rest =>
  simp only [bbShift] at h
  generalize hc0 : bbIteArgs st b0 = ct at h
  cases ct with
  | none => simp at h
  | some ct =>
  obtain ⟨cond, r0, f0⟩ := ct
  simp only [Bool.and_eq_true] at h
  obtain ⟨hult, h⟩ := h
  generalize hlim : bbShiftLimit st cond isFill (b0 :: rest) = ores at h
  cases ores with
  | none => simp at h
  | some res =>
  dsimp only at h
  cases hst : bbStages stage ys (bbLog2 xs.length) res with
  | none => rw [hst] at h; simp at h
  | some fin =>
  rw [hst] at h
  simp only [beq_iff_eq] at h
  subst fin
  obtain ⟨hrl, hbits⟩ := bbShiftLimit_spec (b0 :: rest) res hlim
  rw [hxl] at hult hst
  have hcond := bbs_shift_cond hwf ρ htt hff hys hty (by omega) hult
  have hresv := bbStages_spec ρ (valW st.pool ρ w xs) sh (hsh0 _) (evalV st.pool ρ w y0)
    (bbs_ys_bits hwf ρ hys hty) hstage_len hstage rfl (bbLog2 w) res hst (by omega)
  obtain ⟨b, hb⟩ := get_of_lt (show i < (b0 :: rest).length by omega)
  obtain ⟨r, g, hr, hbn, hg⟩ := hbits i b hb
  rw [bitD_of_get ρ hb, evalB_ite hwf ρ hbn, hcond, hfill g hg, ← bitD_of_get ρ hr,
    ← valW_getLsbD_lt ρ res hi, hresv]
  by_cases hlt : (evalV st.pool ρ w y0).toNat < w
  · simp only [hlt, decide_true, ite_true]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (bbLog2_spec w))]
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
    rw [hover (valW st.pool ρ w xs) (evalV st.pool ρ w y0).toNat i (by omega) hi]

/-- One bit of a bit-vector ite. -/
theorem bbIteBit_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {c t e b : Nat} (h : bbIteBit st c t e b = true) :
    typeOf st.pool c = some .bool ∧
    evalB st.pool ρ b = (if evalB st.pool ρ c then evalB st.pool ρ t else evalB st.pool ρ e) := by
  unfold bbIteBit at h
  split at h
  · rename_i args hb
    split at h
    · rename_i d1 d2 hl
      simp only [Bool.and_eq_true] at h
      obtain ⟨hd2, hd1⟩ := h
      have hbn : st.pool[b]? = some ⟨.conj, #[d1, d2]⟩ := by rw [hb]; congr; exact Array.ext' hl
      split at hd1
      · rename_i dargs hd1n
        split at hd1
        · rename_i n t' hl2
          simp only [Bool.and_eq_true, beq_iff_eq] at hd1
          obtain ⟨hn, rfl⟩ := hd1
          have hd1c : st.pool[d1]? = some ⟨.disj, #[n, t']⟩ := by rw [hd1n]; congr; exact Array.ext' hl2
          refine ⟨bbs_not_arg_bool hwf (isNode_spec hn), ?_⟩
          rw [evalB_conj2 hwf ρ hbn, evalB_disj2 hwf ρ hd1c, evalB_disj2 hwf ρ (isNode_spec hd2), evalB_not hwf ρ hn]
          cases evalB st.pool ρ c <;> simp
        · simp at hd1
      · simp at hd1
    · simp at h
  · simp at h

theorem bbIte_bits {st : St} (hok : TysOK st.pool st.tys) (ρ : Assign) {a w c t0 e0 : Nat} {ts es bs : List Nat}
    (hn : st.pool[a]? = some ⟨.bvIte w, #[c, t0, e0]⟩) (hts : bitsOf st t0 = some ts) (hes : bitsOf st e0 = some es)
    (h : bbIte st c ts es bs = true) (hlen : bs.length = w) :
    ∀ i, i < w → bitD st.pool ρ bs i = (evalV st.pool ρ w a).getLsbD i := by
  intro i hi
  have hwf := hok.wf
  obtain ⟨b, hb⟩ := get_of_lt (show i < bs.length by omega)
  have hf := allIdx_spec 0 bs h i b hb
  simp only [Nat.zero_add] at hf
  cases ht : ts[i]? with
  | none => simp [ht] at hf
  | some t =>
  cases he : es[i]? with
  | none => simp [ht, he] at hf
  | some e =>
  simp only [ht, he] at hf
  obtain ⟨htc, hv⟩ := bbIteBit_spec hwf ρ hf
  obtain ⟨hsel, htt, hte, _⟩ := bbs_bvIte_node hwf ρ hn htc
  obtain ⟨_, htb⟩ := arg_bits hwf ρ hts htt
  obtain ⟨_, heb⟩ := arg_bits hwf ρ hes hte
  rw [bitD_of_get ρ hb, hv, hsel]
  cases evalB st.pool ρ c
  · simp [heb, bitD_of_get ρ he]
  · simp [htb, bitD_of_get ρ ht]


theorem bbs_bvIte_ty {pool : Pool} (hwf : WF pool) {i w : Nat} {args : Array Nat} {t : Ty}
    (h : pool[i]? = some ⟨.bvIte w, args⟩) (ht : typeOf pool i = some t) : t = .bv w := by
  rw [typeOf_node hwf h] at ht
  cases hm : mapOpt (typeOf pool) args.toList with
  | none => rw [hm] at ht; simp at ht
  | some tys =>
    rw [hm] at ht
    simp only [Option.bind_some, Op.resultTy] at ht
    unfold bvIteTy at ht
    split at ht <;> simp [tyGuard] at ht
    exact ht.2.symm

theorem bbs_isLastOf_msb {st : St} (ρ : Assign) {xs : List Nat} {w : Nat} (hxl : xs.length = w) (hw : w ≠ 0)
    {g : Nat} (hg : isLastOf xs g = true) : evalB st.pool ρ g = (valW st.pool ρ w xs).msb := by
  unfold isLastOf at hg
  simp only [beq_iff_eq] at hg
  rw [List.getLast?_eq_getElem?, hxl] at hg
  rw [BitVec.msb_eq_getLsbD_last, valW_getLsbD_lt ρ xs (by omega), bitD_of_get ρ hg]

theorem bbTerm_bits {st : St} (hok : TysOK st.pool st.tys) {bi : Builtins}
    (htt : st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩) (hff : st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩)
    (ρ : Assign) {a : Nat} {bs : List Nat} {w : Nat}
    (h : bbTerm st bi a bs = true) (hty : typeOf st.pool a = some (.bv w)) (hlen : bs.length = w) :
    ∀ i, i < w → bitD st.pool ρ bs i = (evalV st.pool ρ w a).getLsbD i := by
  have hwf := hok.wf
  intro i hi
  have hx := evalV_spec (ρ := ρ) hty
  unfold bbTerm at h
  split at h
  · -- variable
    rename_i w' id args hn
    exact bbVar_bits hwf ρ h hx i hi (by omega)
  · -- literal
    rename_i w' v args hn
    obtain ⟨rfl, hw, hw64, hv⟩ := bvVal_typing hwf hn
    have he := eval_lit_bv hwf hn ρ
    rw [hx] at he
    injection he with hw' hv'
    subst hw'
    rw [eq_of_heq hv']
    exact bbVal_bits hwf ρ htt hff h i hi (by omega)
  · -- bit-vector ite
    rename_i w' args hn
    split at h
    · rename_i c t0 e0 hl
      split at h
      · rename_i ts es hts hes
        have hn' : st.pool[a]? = some ⟨.bvIte w', #[c, t0, e0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        have hw := bbs_bvIte_ty hwf hn hty
        simp at hw; subst hw
        exact bbIte_bits hok ρ hn' hts hes h hlen i hi
      · simp at h
    · simp at h
  · rename_i op args hnv hnl hni hn
    split at h
    · simp at h
    · rename_i xss hxss
      split at h
      · -- not
        rename_i w' xs
        obtain ⟨x0, hl, hx0⟩ := mapOpt_singleton_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvNot w', #[x0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        obtain ⟨hv, htx, hta⟩ := bvNot_node hwf ρ hn'
        rw [hty] at hta; simp at hta; subst hta
        obtain ⟨hl', hb⟩ := bbNot_bits hwf ρ h
        rw [hb i (by omega), hv, BitVec.getLsbD_not]
        obtain ⟨_, hbx⟩ := arg_bits hwf ρ hx0 htx
        rw [hbx i]; simp [hi]
      · -- neg
        rename_i w' xs
        obtain ⟨x0, hl, hx0⟩ := mapOpt_singleton_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvNeg w', #[x0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        obtain ⟨_, _, hta⟩ := bvNeg_node hwf ρ hn'
        rw [hty] at hta; simp at hta; subst hta
        exact bbNeg_bits hok htt hff ρ hn' hx0 h hlen i hi
      · -- add
        rename_i w'
        have hta := (bvN_args_bv hwf hn rfl).2.2.2
        rw [hty] at hta; simp at hta; subst hta
        exact bbAdd_bits hok htt hff ρ hn hxss h hlen i hi
      · -- sub
        rename_i w' xs ys
        obtain ⟨x0, y0, hl, hx0, hy0⟩ := mapOpt_pair_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvSub w', #[x0, y0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        obtain ⟨_, _, _, hta⟩ := bvSub_node hwf ρ hn'
        rw [hty] at hta; simp at hta; subst hta
        exact bbSub_bits hok htt hff ρ hn' hx0 hy0 h hlen i hi
      · -- and
        rename_i w'
        have hta := (bvN_args_bv hwf hn rfl).2.2.2
        rw [hty] at hta; simp at hta; subst hta
        exact bbBitwise_bits hok ρ hn rfl (fun _ => rfl) (fun x y i hi => by simp)
          (fun n l r hn => evalB_conj2 hwf ρ hn) (fun i hi c => by simp [hi]) hxss h hlen i hi
      · -- or
        rename_i w'
        have hta := (bvN_args_bv hwf hn rfl).2.2.2
        rw [hty] at hta; simp at hta; subst hta
        exact bbBitwise_bits hok ρ hn rfl (fun _ => rfl) (fun x y i hi => by simp)
          (fun n l r hn => evalB_disj2 hwf ρ hn) (fun i hi c => by simp) hxss h hlen i hi
      · -- xor
        rename_i w'
        have hta := (bvN_args_bv hwf hn rfl).2.2.2
        rw [hty] at hta; simp at hta; subst hta
        exact bbBitwise_bits hok ρ hn rfl (fun _ => rfl) (fun x y i hi => by simp)
          (fun n l r hn => evalB_xor2 hwf ρ hn) (fun i hi c => by simp) hxss h hlen i hi
      · -- concat
        rename_i w'
        simp only [beq_iff_eq] at h
        subst h
        obtain ⟨hargs, hl2, _⟩ := concat_args hwf hn
        have hne : args.toList ≠ [] := by
          intro hh
          have h0 : args.toList.length = 0 := by rw [hh]; rfl
          simp only [Array.length_toList] at h0; omega
        obtain ⟨n, v, hc, hn', hv⟩ := concat_bits hwf ρ args.toList xss hxss (fun x hx => hargs x (by simpa using hx)) hne
        have he := eval_node hwf ρ hn
        simp only [Op.eval, bvConcatEval, hc] at he
        rw [hx] at he
        split at he
        · rename_i hcond
          injection he with hw hv'
          subst hw
          rw [eq_of_heq hv', BitVec.getLsbD_cast, hv i]
        · simp at he
      · -- extract
        rename_i hi' lo xs
        obtain ⟨x0, hl, hx0⟩ := mapOpt_singleton_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvExtract hi' lo, #[x0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        simp only [beq_iff_eq] at h
        subst h
        obtain ⟨n0, hn0⟩ := extract_arg_bv hwf hn'
        obtain ⟨hlx, hbx⟩ := arg_bits hwf ρ hx0 hn0
        have he := eval_node hwf ρ hn'
        simp only [Op.eval, List.map, evalV_spec hn0, bvExtractEval] at he
        rw [hx] at he
        split at he
        · rename_i hcond
          injection he with hw hv'
          subst hw
          rw [eq_of_heq hv', BitVec.getLsbD_extractLsb, hbx]
          unfold bitD
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, List.getElem?_drop, hi, ite_true]
          rfl
        · simp at he
      · -- sign extension
        rename_i w' e xs
        obtain ⟨x0, hl, hx0⟩ := mapOpt_singleton_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvSignExtend w' e, #[x0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        obtain ⟨n0, hn0⟩ := sext_arg_bv hwf hn'
        obtain ⟨hlx, hbx⟩ := arg_bits hwf ρ hx0 hn0
        have he := eval_node hwf ρ hn'
        simp only [Op.eval, List.map, evalV_spec hn0, bvExtEval, ite_true] at he
        rw [hx] at he
        split at he
        · rename_i hcond
          injection he with hw hv'
          subst hw
          rw [eq_of_heq hv', BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last, hbx, hbx]
          unfold bbSext at h
          split at h
          · rename_i s hs
            simp only [beq_iff_eq] at h
            subst h
            rw [bitD_append]
            rw [List.getLast?_eq_getElem?, hlx] at hs
            simp only [hi, decide_true, Bool.true_and]
            split
            · rename_i hlt; rw [ite_eq_left (by omega)]
            · rename_i hge
              rw [ite_eq_right (by omega)]
              have hlt : i - xs.length < e := by omega
              unfold bitD
              simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_replicate, hlt, ite_true, hs]
          · simp at h
        · simp at he
      · -- shl
        rename_i w' xs ys
        obtain ⟨x0, y0, hl, hx0, hy0⟩ := mapOpt_pair_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvShl w', #[x0, y0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        obtain ⟨_, _, _, hta, _⟩ := bbs_bvBin_node hwf ρ (fun x y => x <<< y) rfl rfl hn'
        rw [hty] at hta; simp at hta; subst hta
        exact bbShift_bits hok htt hff ρ hn' rfl (fun x y => x <<< y) rfl (fun x s => x <<< s)
          (fun _ _ => BitVec.shiftLeft_eq') BitVec.shiftLeft_zero (fun _ => false)
          (fun x s j hs hj => by rw [BitVec.getLsbD_shiftLeft]; simp [show j < s by omega])
          hx0 hy0 (fun g hg => evalB_falseNode hwf ρ hg)
          (fun _ _ _ _ hp => (bbLshStage_spec hwf ρ hp).1)
          (fun _ _ _ _ hp hl' _ hpre => bbLshStage_valW hwf ρ hp hl' hpre) h hlen i hi
      · -- lshr
        rename_i w' xs ys
        obtain ⟨x0, y0, hl, hx0, hy0⟩ := mapOpt_pair_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvLshr w', #[x0, y0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        obtain ⟨_, _, _, hta, _⟩ := bbs_bvBin_node hwf ρ (fun x y => x >>> y) rfl rfl hn'
        rw [hty] at hta; simp at hta; subst hta
        have hfl : ∀ g, isFalseNode st g = true → evalB st.pool ρ g = false := fun g hg => evalB_falseNode hwf ρ hg
        exact bbShift_bits hok htt hff ρ hn' rfl (fun x y => x >>> y) rfl (fun x s => x >>> s)
          (fun x y => BitVec.ushiftRight_eq' x y) BitVec.ushiftRight_zero (fun _ => false)
          (fun x s j hs hj => by rw [BitVec.getLsbD_ushiftRight]; exact BitVec.getLsbD_of_ge _ _ (by omega))
          hx0 hy0 hfl
          (fun _ _ _ _ hp => (bbRshStage_spec hwf ρ hp hfl).1)
          (fun _ _ _ _ hp hl' _ hpre => bbRshStage_valW_ushift hwf ρ hp hfl hl' hpre) h hlen i hi
      · -- ashr
        rename_i w' xs ys
        obtain ⟨x0, y0, hl, hx0, hy0⟩ := mapOpt_pair_inv hxss
        have hn' : st.pool[a]? = some ⟨.bvAshr w', #[x0, y0]⟩ := by rw [hn]; congr; exact Array.ext' hl
        obtain ⟨_, htx, _, hta, hw0⟩ := bbs_bvBin_node hwf ρ (fun x y => x.sshiftRight y.toNat) rfl rfl hn'
        rw [hty] at hta; simp at hta; subst hta
        obtain ⟨hxl, _⟩ := arg_bits hwf ρ hx0 htx
        have hfl : ∀ g, isLastOf xs g = true → evalB st.pool ρ g = (valW st.pool ρ w xs).msb :=
          fun g hg => bbs_isLastOf_msb ρ hxl hw0 hg
        exact bbShift_bits hok htt hff ρ hn' rfl (fun x y => x.sshiftRight y.toNat) rfl (fun x s => x.sshiftRight s)
          (fun _ _ => rfl) (fun _ => BitVec.sshiftRight_zero) (fun x => x.msb)
          (fun x s j hs hj => by
            rw [BitVec.getLsbD_sshiftRight]; simp [show ¬ (w ≤ j) by omega, show ¬ (s + j < w) by omega])
          hx0 hy0 hfl
          (fun _ _ _ _ hp => (bbRshStage_spec hwf ρ hp hfl).1)
          (fun _ _ _ _ hp hl' _ hpre => bbRshStage_valW_sshift hwf ρ hp hfl hl' hpre) h hlen i hi
      · simp at h
  · simp at h

/-! ## The step -/

theorem ruleBitblast_sound {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat} {ei : EI}
    {prems params : List Nat} (h : ruleBitblast bi ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  have hwf := hinv.wf
  unfold ruleBitblast at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        have hen := node_bind_eq hab
        have ha := child_lt hwf hen (a := a) (by simp)
        have hb := child_lt hwf hen (a := b) (by simp)
        split at h
        · rename_i w hta
          split at h
          · rename_i bs hbs
            split at h
            · rename_i hbb
              simp at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨hinv, idx_lt_of_get hen, ?_⟩
              intro ρ _
              rw [holds_eq_node hwf hen ρ]
              have hta' : typeOf st.pool a = some (.bv w) := by rw [← tys_of_lt hinv.tys ha]; exact hta
              have htb := eq_args_same_ty hwf hen hta'
              refine ⟨?_, ⟨.bv w, by rw [eval_ty, hta'], rfl⟩⟩
              obtain ⟨args, hbn, rfl⟩ := bitsOf_spec hbs
              obtain ⟨_, _, htb'⟩ := fromBool_args_bool hwf hbn
              rw [htb] at htb'; simp at htb'
              rw [evalV_spec hta', eval_fromBool hwf ρ hbn]
              have hlen : args.toList.length = w := by simp [htb']
              have key := bbTerm_bits hinv.tys hinv.tt hinv.ff ρ hbb hta' hlen
              rw [bv_cast_eq (show (List.map (evalB st.pool ρ) args.toList).length = w by simp [htb'])]
              congr 1
              rw [ofBoolListLE_eq _ (evalV st.pool ρ w a) (by simp [htb']) (fun i hi => key i hi)]
              simp
            · simp at h
          · simp at h
        · rename_i hta
          split at h
          · rename_i hbb
            simp at h; obtain ⟨rfl, rfl⟩ := h
            refine ⟨hinv, idx_lt_of_get hen, ?_⟩
            intro ρ _
            rw [holds_eq_node hwf hen ρ]
            have hta' : typeOf st.pool a = some .bool := by rw [← tys_of_lt hinv.tys ha]; exact hta
            have htb := eq_args_same_ty hwf hen hta'
            exact ⟨bbAtom_val hinv.tys ρ hbb hta' htb, ⟨.bool, by rw [eval_ty, hta'], rfl⟩⟩
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

end Bcf
