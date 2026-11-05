import Bcf.Rw.Bv

/-!
# Rewrites with `BVQs` list parameters

Concatenation/extract merging, the `*_SIMPLIFY_*` rules, `BV_ULT_ADD_ONE`,
the `XOR` pull-ups and the three-piece pull-ups.
-/
namespace Bcf

open RwExpr

/-! ## Helpers -/

syntax "lists_pat" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| lists_pat $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.ult', RwExpr.ule',
      RwExpr.slt', RwExpr.sle', RwExpr.sge', RwExpr.conj', RwExpr.bvsub', RwExpr.bvadd', RwExpr.bvmul',
      RwExpr.bvshl', RwExpr.bvashr', RwExpr.bvand', RwExpr.bvor', RwExpr.concat', RwExpr.bvsize', RwExpr.l0,
      RwExpr.l1, RwExpr.V, RwExpr.mk, RwExpr.bvxor', RwExpr.bvnot', RwArgs.ofList, denoteE, denoteA,
      spliceVal_bv, spliceVal_bool, spliceVal_list,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc,
      l0_val, l1_val, BitVec.toNat_ofNat, Nat.zero_mod, spliceVal_bvExtractEval, spliceVal_bvExtEval,
      spliceVal_bvRepeatEval, spliceVal_bvValEval, spliceVal_appVal_snoc, spliceVal_appVal_cons,
      spliceVal_appVal_two, spliceVal_appVal_append2,
      spliceVal_appVal_nonred (rfl : RwOp.reducible .eq = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsize = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsub = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .ult = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .not = false),
      appVal_concat_single] $[$loc]?)

def lists_bitXor : BitOp .bvxor where
  F w := List.foldl (· ^^^ ·) 0
  f := (· ^^ ·)
  e := false
  node _ _ := rfl
  red := rfl
  one _ _ := by simp
  bits w xs i hi := by
    rw [foldl_bv_getLsbD (· ^^^ ·) (· ^^ ·) (fun x y i _ => by simp) _ i hi]
    simp
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  id := by intro x; cases x <;> rfl

/-- Bit `i` of a value (false for non-bit-vectors). -/
def lists_vbit (i : Nat) : Val → Bool
  | .bv _ x => x.getLsbD i
  | _ => false

@[simp] theorem lists_vbit_bv (i w : Nat) (x : BitVec w) : lists_vbit i (.bv w x) = x.getLsbD i := rfl

theorem lists_bits {op : RwOp} (B : BitOp op) {l : List Val} {w : Nat} {r : BitVec w}
    (h : appVal op l = .bv w r) {i : Nat} (hi : i < w) :
    r.getLsbD i = (l.map (lists_vbit i)).foldl B.f B.e := by
  obtain ⟨xs, rfl, rfl⟩ := B.eval h
  rw [B.bits w xs i hi, List.map_map]
  rfl

theorem lists_mem_bv {op : RwOp} (B : BitOp op) {l : List Val} {w : Nat} {r : BitVec w}
    (h : appVal op l = .bv w r) {v : Val} (hv : v ∈ l) : ∃ x : BitVec w, v = .bv w x := by
  obtain ⟨xs, rfl, _⟩ := B.eval h
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
  exact ⟨x, rfl⟩

theorem lists_exists_mem {op : RwOp} (B : BitOp op) {l : List Val} {w : Nat} {r : BitVec w}
    (h : appVal op l = .bv w r) : ∃ x : BitVec w, .bv w x ∈ l := by
  obtain ⟨xs, rfl, _⟩ := B.eval h
  cases xs with
  | nil => simp [appVal] at h
  | cons x _ => exact ⟨x, by simp⟩

theorem lists_cons_bit {op : RwOp} (B : BitOp op) {vs0 vs1 : List Val} {c : Val} {w : Nat} {r s cx : BitVec w}
    (h : appVal op (vs0 ++ c :: vs1) = .bv w r) (hs : appVal op (vs0 ++ vs1) = .bv w s)
    (hc : c = .bv w cx) {i : Nat} (hi : i < w) :
    r.getLsbD i = B.f (s.getLsbD i) (cx.getLsbD i) := by
  rw [lists_bits B h hi, lists_bits B hs hi, List.map_append, List.map_cons, foldl_mid B.assoc B.comm B.id,
    ← List.map_append, hc, lists_vbit_bv]

theorem lists_bin_bit {op : RwOp} (B : BitOp op) {a b : Val} {w : Nat} {r x y : BitVec w}
    (h : appVal op [a, b] = .bv w r) (ha : a = .bv w x) (hb : b = .bv w y) {i : Nat} (hi : i < w) :
    r.getLsbD i = B.f (x.getLsbD i) (y.getLsbD i) := by
  rw [lists_bits B h hi, ha, hb]
  simp [B.id]

theorem lists_not_eval {w : Nat} (x : BitVec w) :
    appVal .bvnot [.bv w x] = if w ≠ 0 then .bv w (~~~ x) else .bad := by
  simp [appVal, RwOp.reducible, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvUn]

theorem lists_not_isBv {v : Val} (h : appVal .bvnot [v] ≠ .bad) :
    ∃ w x, v = .bv w x ∧ w ≠ 0 ∧ appVal .bvnot [v] = .bv w (~~~ x) := by
  cases v with
  | bv w x =>
    rw [lists_not_eval] at h ⊢
    by_cases hw : w ≠ 0
    · exact ⟨w, x, rfl, hw, by rw [ite_eq_left hw]⟩
    · rw [ite_eq_right hw] at h; exact absurd rfl h
  | bool _ => simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvUn, Val.asBv] at h
  | list _ _ => simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvUn, Val.asBv] at h
  | bad => simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvUn, Val.asBv] at h

theorem lists_foldl_and_false : ∀ (l : List Bool) (a : Bool), false ∈ l → l.foldl (· && ·) a = false := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons x l ih =>
    intro a h
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst h
      have : ∀ (l : List Bool), l.foldl (· && ·) false = false := by
        intro l; induction l with
        | nil => rfl
        | cons y l ih' => simp [List.foldl_cons, ih']
      simp [this]
    · exact ih _ h

theorem lists_foldl_or_true : ∀ (l : List Bool) (a : Bool), true ∈ l → l.foldl (· || ·) a = true := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons x l ih =>
    intro a h
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst h
      have : ∀ (l : List Bool), l.foldl (· || ·) true = true := by
        intro l; induction l with
        | nil => rfl
        | cons y l ih' => simp [List.foldl_cons, ih']
      simp [this]
    · exact ih _ h

theorem lists_foldl_and_mem {l : List Bool} {b : Bool} (h1 : b ∈ l) (h2 : (!b) ∈ l) :
    l.foldl (· && ·) true = false := by
  cases b with
  | false => exact lists_foldl_and_false l true h1
  | true => exact lists_foldl_and_false l true h2

theorem lists_foldl_or_mem {l : List Bool} {b : Bool} (h1 : b ∈ l) (h2 : (!b) ∈ l) :
    l.foldl (· || ·) false = true := by
  cases b with
  | true => exact lists_foldl_or_true l false h1
  | false => exact lists_foldl_or_true l false h2

theorem lists_xor_cancel (s x : Bool) : ((s ^^ x) ^^ !x) = !s := by cases s <;> cases x <;> rfl

theorem lists_and_simp {l : List Val} {w3 : Nat} {x3 : BitVec w3} (hN : appVal .bvnot [.bv w3 x3] ∈ l)
    (hx : .bv w3 x3 ∈ l) (h2 : 2 ≤ l.length) (hl : appVal .bvand l ≠ .bad) (hr : bvValEval w3 0 [] ≠ .bad) :
    appVal .bvand l = bvValEval w3 0 [] := by
  rcases lit_cases w3 0 with hL | ⟨hw3, _, _, hL⟩
  · exact absurd hL hr
  obtain ⟨_, _, hxx, _, hNv⟩ := lists_not_isBv (bitAnd.mem_ne_bad hl _ hN)
  injection hxx with e1 e2; subst e1; have := eq_of_heq e2; subst this
  obtain ⟨w, a, hla⟩ := bitAnd.isBv hl (fun v hv => by rw [hv] at h2; simp at h2)
  obtain ⟨_, hx3⟩ := lists_mem_bv bitAnd hla hx
  injection hx3 with e1 e2; subst e1
  rw [hla, hL]
  apply val_ext rfl
  intro i hi
  rw [lists_bits bitAnd hla hi, BitVec.getLsbD_ofNat, Nat.zero_testBit, Bool.and_false]
  apply lists_foldl_and_mem (b := x3.getLsbD i)
  · exact List.mem_map.mpr ⟨_, hx, rfl⟩
  · refine List.mem_map.mpr ⟨_, hN, ?_⟩
    rw [hNv, lists_vbit_bv, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]

theorem lists_or_simp {l : List Val} {w3 : Nat} {x3 : BitVec w3} (hN : appVal .bvnot [.bv w3 x3] ∈ l)
    (hx : .bv w3 x3 ∈ l) (h2 : 2 ≤ l.length) (hl : appVal .bvor l ≠ .bad)
    (hr : appVal .bvnot [bvValEval w3 0 []] ≠ .bad) :
    appVal .bvor l = appVal .bvnot [bvValEval w3 0 []] := by
  rcases lit_cases w3 0 with hL | ⟨hw3, _, _, hL⟩
  · rw [hL] at hr; exact absurd rfl hr
  rw [hL, lists_not_eval, ite_eq_left hw3] at hr ⊢
  obtain ⟨_, _, hxx, _, hNv⟩ := lists_not_isBv (bitOr.mem_ne_bad hl _ hN)
  injection hxx with e1 e2; subst e1; have := eq_of_heq e2; subst this
  obtain ⟨w, a, hla⟩ := bitOr.isBv hl (fun v hv => by rw [hv] at h2; simp at h2)
  obtain ⟨_, hx3⟩ := lists_mem_bv bitOr hla hx
  injection hx3 with e1 e2; subst e1
  rw [hla]
  apply val_ext rfl
  intro i hi
  rw [lists_bits bitOr hla hi, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, Nat.zero_testBit, Bool.and_false,
    decide_eq_true hi, Bool.true_and, Bool.not_false]
  apply lists_foldl_or_mem (b := x3.getLsbD i)
  · exact List.mem_map.mpr ⟨_, hx, rfl⟩
  · refine List.mem_map.mpr ⟨_, hN, ?_⟩
    rw [hNv, lists_vbit_bv, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]

theorem lists_bitXor_f : lists_bitXor.f = (· ^^ ·) := rfl
theorem lists_bitXor_e : lists_bitXor.e = false := rfl
theorem lists_xor_assoc : ∀ x y z : Bool, ((x ^^ y) ^^ z) = (x ^^ (y ^^ z)) := lists_bitXor.assoc
theorem lists_xor_comm : ∀ x y : Bool, (x ^^ y) = (y ^^ x) := lists_bitXor.comm
theorem lists_xor_id : ∀ x : Bool, (false ^^ x) = x := lists_bitXor.id

theorem lists_sub1 {v a : Val} {A B : List Val} (h : v ∈ A ++ B) : v ∈ A ++ a :: B := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem lists_sub2 {v a b : Val} {A B C : List Val} (h : v ∈ A ++ (B ++ C)) : v ∈ A ++ a :: (B ++ b :: C) := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- An xor whose operands are those of `l'` plus operands that flip every bit. -/
theorem lists_xor_flip {l l' : List Val} {w : Nat} {x : BitVec w} (hx : .bv w x ∈ l)
    (hsub : ∀ v ∈ l', v ∈ l) (hsingle : ∀ v, l = [v] → IsBv v)
    (hl : appVal .bvxor l ≠ .bad) (hr : appVal .bvnot (spliceVal (appVal .bvxor l')) ≠ .bad)
    (hbits : ∀ i, i < w → (l.map (lists_vbit i)).foldl (· ^^ ·) false =
      !((l'.map (lists_vbit i)).foldl (· ^^ ·) false)) :
    appVal .bvxor l = appVal .bvnot (spliceVal (appVal .bvxor l')) := by
  obtain ⟨w', a, hla⟩ := lists_bitXor.isBv hl hsingle
  obtain ⟨_, hx'⟩ := lists_mem_bv lists_bitXor hla hx
  injection hx' with e1 _; subst e1
  rw [spliceVal_appVal (fun _ v hv e vs hvl => by
    obtain ⟨_, h⟩ := lists_mem_bv lists_bitXor hla (hsub v (by rw [hv]; simp))
    rw [hvl] at h; exact Val.noConfusion h)] at hr ⊢
  obtain ⟨n, y, hin, hn, hrv⟩ := lists_not_isBv hr
  obtain ⟨z, hz⟩ := lists_exists_mem lists_bitXor hin
  obtain ⟨_, hz'⟩ := lists_mem_bv lists_bitXor hla (hsub _ hz)
  injection hz' with e1 _; subst e1
  rw [hla, hrv]
  apply val_ext rfl
  intro i hi
  rw [BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and, lists_bits lists_bitXor hla hi, lists_bits lists_bitXor hin hi,
    lists_bitXor_f, lists_bitXor_e]
  exact hbits i hi

theorem lists_single_of_append {A B : List Val} {a v : Val} (h : A ++ a :: B = [v]) : v = a := by
  cases A with
  | nil => simp at h; exact h.1.symm
  | cons _ _ => simp at h

/-! ### `bvadd` over spliced lists -/

theorem lists_add_eval {l : List Val} {w : Nat} {x : BitVec w} (h : appVal .bvadd l = .bv w x) :
    ∃ xs : List (BitVec w), l = xs.map (Val.bv w) ∧ x = xs.foldl (· + ·) 0 := by
  match l, h with
  | [], h => simp [appVal] at h
  | [v], h =>
    simp only [appVal, RwOp.reducible, ↓reduceIte] at h
    subst h
    exact ⟨[x], rfl, by simp⟩
  | a :: b :: rest, h =>
    simp only [appVal, RwOp.node, Op.eval] at h
    generalize RwOp.widthV .bvadd (a :: b :: rest) = W at h
    unfold bvN at h
    split at h
    · rename_i xs hxs
      split at h
      · injection h with hw hx
        subst hw
        exact ⟨xs, bvs_map hxs, (eq_of_heq hx).symm⟩
      · simp at h
    · simp at h

theorem lists_tys_map {w : Nat} (xs : List (BitVec w)) :
    Val.tys (xs.map (Val.bv w)) = some (xs.map (fun _ => Ty.bv w)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [ih]

theorem lists_bvN_add {w : Nat} (xs : List (BitVec w)) (h2 : 2 ≤ xs.length) (hw : w ≠ 0) (W : Nat) (hW : W = w) :
    bvN W (List.foldl (· + ·) 0) (xs.map (Val.bv w)) = .bv w (xs.foldl (· + ·) 0) := by
  subst W
  unfold bvN
  rw [bvs_of_map]
  simp [hw, h2]

theorem lists_add_map {w : Nat} (xs : List (BitVec w)) (hne : xs ≠ []) (hw : w ≠ 0) :
    appVal .bvadd (xs.map (Val.bv w)) = .bv w (xs.foldl (· + ·) 0) := by
  match xs, hne with
  | [x], _ => simp [appVal, RwOp.reducible]
  | a :: b :: rest, _ =>
    simp only [appVal, RwOp.node, Op.eval]
    exact lists_bvN_add (a :: b :: rest) (by simp) hw _ (by simp [RwOp.widthV, RwOp.width, Val.tys, lists_tys_map, firstBv])

theorem lists_ult_isBv {v : Val} {w : Nat} {x : BitVec w} (h : appVal .ult [.bv w x, v] ≠ .bad) :
    ∃ y : BitVec w, v = .bv w y ∧ appVal .ult [.bv w x, v] = .bool (x.ult y) := by
  cases v with
  | bv m y =>
    rw [ult_eval] at h ⊢
    by_cases hm : m = w
    · subst hm; exact ⟨y, rfl, by simp⟩
    · rw [dite_eq_right hm] at h; exact absurd rfl h
  | bool _ => simp [appVal, RwOp.node, Op.eval, bvCmp] at h
  | list _ _ => simp [appVal, RwOp.node, Op.eval, bvCmp] at h
  | bad => simp [appVal, RwOp.node, Op.eval, bvCmp] at h

theorem lists_eq_bad_l (v : Val) : appVal .eq [.bad, v] = .bad := by
  cases v <;> rfl
theorem lists_eq_bad_r (v : Val) : appVal .eq [v, .bad] = .bad := by
  cases v <;> rfl
theorem lists_not_bad : appVal .not [.bad] = .bad := rfl
theorem lists_bvnot_bad : appVal .bvnot [.bad] = .bad := rfl
theorem lists_conj_bad_l (v : Val) : appVal .conj [.bad, v] = .bad := by
  cases v <;> rfl
theorem lists_eq_bv {w : Nat} (a b : BitVec w) : appVal .eq [.bv w a, .bv w b] = .bool (decide (a = b)) := by
  simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]
theorem lists_not_bool (b : Bool) : appVal .not [.bool b] = .bool (!b) := rfl
theorem lists_conj_bool (p q : Bool) : appVal .conj [.bool p, .bool q] = .bool (p && q) := by
  simp [appVal, RwOp.node, Op.eval, boolN, Val.bools]

/-! ### Three-piece pull-up -/

theorem lists_piece {op : RwOp} (B : BitOp op) {hi lo : Nat} {S : Val} {wj : Nat} {xj : BitVec wj}
    {n : Nat} {p : BitVec n} (h : appVal op [bvExtractEval hi lo [S], .bv wj xj] = .bv n p) :
    n = wj ∧ ∃ (m : Nat) (y : BitVec m), S = .bv m y ∧ lo ≤ hi ∧ hi < m ∧ n = hi - lo + 1 ∧
      ∀ i, i < n → p.getLsbD i = B.f (y.getLsbD (lo + i)) (xj.getLsbD i) := by
  obtain ⟨_, hxj⟩ := lists_mem_bv B h (v := .bv wj xj) (by simp)
  injection hxj with e1 _; subst e1
  obtain ⟨e, hE⟩ := lists_mem_bv B h (v := bvExtractEval hi lo [S]) (by simp)
  obtain ⟨m, y, hS, hlo, hhi, hn, hebits⟩ := extract_val hE
  refine ⟨rfl, m, y, hS, hlo, hhi, hn, fun i hi' => ?_⟩
  rw [lists_bin_bit B h hE rfl hi', hebits, decide_eq_true (show i < hi - lo + 1 by omega), Bool.true_and]

theorem lists_pullup3 {op : RwOp} (B : BitOp op) {vs0 vs1 : List Val} {w2 w3 w4 : Nat}
    {x2 : BitVec w2} {x3 : BitVec w3} {x4 : BitVec w4} {k5 k6 k7 k8 k9 : Nat} (hk6 : k6 = w2 + w4) (hk8 : k8 = w4)
    (hl : appVal op (vs0 ++ appVal .concat [.bv w3 x3, .bv w2 x2, .bv w4 x4] :: vs1) ≠ .bad)
    (hr : appVal .concat [appVal op [bvExtractEval k5 k6 [appVal op (vs0 ++ vs1)], .bv w3 x3],
                          appVal op [bvExtractEval k7 k8 [appVal op (vs0 ++ vs1)], .bv w2 x2],
                          appVal op [bvExtractEval k9 0 [appVal op (vs0 ++ vs1)], .bv w4 x4]] ≠ .bad) :
    appVal op (vs0 ++ appVal .concat [.bv w3 x3, .bv w2 x2, .bv w4 x4] :: vs1) =
    appVal .concat [appVal op [bvExtractEval k5 k6 [appVal op (vs0 ++ vs1)], .bv w3 x3],
                    appVal op [bvExtractEval k7 k8 [appVal op (vs0 ++ vs1)], .bv w2 x2],
                    appVal op [bvExtractEval k9 0 [appVal op (vs0 ++ vs1)], .bv w4 x4]] := by
  -- the concatenation argument
  obtain ⟨Wc, cx, hC, _, hWc, hcbits⟩ := appVal_concat_bits (l := [.bv w3 x3, .bv w2 x2, .bv w4 x4])
    (B.mem_ne_bad hl _ (by simp)) (fun v hv => by simp at hv)
  rw [hC] at hl ⊢
  -- the left-hand side
  obtain ⟨w, a, hla⟩ := B.isBv hl (fun v hv => by rw [lists_single_of_append hv]; exact ⟨_, _, rfl⟩)
  obtain ⟨_, hCw⟩ := lists_mem_bv B hla (v := .bv Wc cx) (by simp)
  injection hCw with e1 e2; subst e1; have := eq_of_heq e2; subst this
  -- the right-hand side
  obtain ⟨n, r, hrr, hallP, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨n3, p3, hP3⟩ := hallP _ (by simp only [List.mem_cons]; exact Or.inl rfl)
  obtain ⟨n2, p2, hP2⟩ := hallP _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨n4, p4, hP4⟩ := hallP _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hn3, m, y, hS, h65, h5m, hn3', hb3⟩ := lists_piece B hP3
  obtain ⟨hn2, m', y', hS', h87, h7m, hn2', hb2⟩ := lists_piece B hP2
  obtain ⟨hn4, m'', y'', hS'', _, h9m, hn4', hb4⟩ := lists_piece B hP4
  rw [hS] at hS' hS''
  injection hS' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  injection hS'' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  subst n3; subst n2; subst n4
  -- the inner operator has the width of the outer one
  obtain ⟨z, hz⟩ := lists_exists_mem B hS
  obtain ⟨_, hz'⟩ := lists_mem_bv B hla (lists_sub1 hz)
  injection hz' with e1 _; subst e1
  -- widths
  rw [hP3, hP2, hP4] at hn hrbits
  simp only [catW, Nat.add_zero] at hWc hn
  rw [hla, hrr]
  apply val_ext (by omega)
  intro i hi
  rw [lists_cons_bit B hla hS rfl hi, hrbits, hcbits]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  by_cases hi2 : i < w2 + w4
  · rw [ite_eq_left hi2, ite_eq_left hi2]
    by_cases hi4 : i < w4
    · rw [ite_eq_left hi4, ite_eq_left hi4, hb4 i hi4, Nat.zero_add]
    · rw [ite_eq_right hi4, ite_eq_right hi4, hb2 _ (by omega), hk8, show w4 + (i - w4) = i by omega]
  · rw [ite_eq_right hi2, ite_eq_right hi2, hb3 _ (by omega), hk6, show w2 + w4 + (i - (w2 + w4)) = i by omega]

/-! ## The rules -/

-- rewrite id 51
theorem sound_BV_CONCAT_EXTRACT_MERGE :
    (RwRule.mk [.bvqs, .bvq, .bvqs, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (eq' (var 5) (bvadd' [var 4, l1])))
      (concat' [var 0, extract (var 6) (var 5) (var 1), extract (var 4) (var 3) (var 1), var 2])
      (concat' [var 0, extract (var 6) (var 3) (var 1), var 2])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨w1, x1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  rw [appVal_bvadd32] at hc
  have hk5 := eq_bv32 hc
  -- the left-hand side
  obtain ⟨n, x, hx, hall, hn, hxbits⟩ := appVal_concat_bits hl (fun v hv => by
    have := congrArg List.length hv; simp at this; omega)
  obtain ⟨_, _, hE1⟩ := hall (bvExtractEval k6.toNat k5.toNat [.bv w1 x1]) (by simp)
  obtain ⟨_, _, hE2⟩ := hall (bvExtractEval k4.toNat k3.toNat [.bv w1 x1]) (by simp)
  obtain ⟨_, _, hy1, h56, h6w, hE1v⟩ := extract_of_ne_bad (by rw [hE1]; simp : bvExtractEval k6.toNat k5.toNat _ ≠ .bad)
  obtain ⟨_, _, hy2, h34, h4w, hE2v⟩ := extract_of_ne_bad (by rw [hE2]; simp : bvExtractEval k4.toNat k3.toNat _ ≠ .bad)
  injection hy1 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  injection hy2 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  -- the right-hand side
  obtain ⟨n', x', hx', _, hn', hx'bits⟩ := appVal_concat_bits hr (fun v hv => by
    have hv' := lists_single_of_append hv; subst hv'
    rw [hv, appVal_concat_single] at hr
    exact bvExtractEval_isBv hr)
  have hE3 : bvExtractEval k6.toNat k3.toNat [.bv w1 x1] ≠ .bad := by
    intro hb; rw [hb] at hr; exact hr (appVal_concat_has_bad (by simp))
  obtain ⟨_, _, hy3, h36, _, hE3v⟩ := extract_of_ne_bad hE3
  injection hy3 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  -- arithmetic
  have hk5n : k5.toNat = k4.toNat + 1 := by
    rw [hk5, toNat_add32 _ _ (by rw [show (1#32 : BitVec 32).toNat = 1 by decide, two32]; omega)]
    rfl
  rw [hE1v, hE2v] at hn hxbits
  rw [hE3v] at hn' hx'bits
  rw [hx, hx']
  have hlist : vs0 ++ Val.bv (k6.toNat - k5.toNat + 1) (BitVec.extractLsb k6.toNat k5.toNat x1) ::
      Val.bv (k4.toNat - k3.toNat + 1) (BitVec.extractLsb k4.toNat k3.toNat x1) :: vs2 =
      vs0 ++ ([Val.bv (k6.toNat - k5.toNat + 1) (BitVec.extractLsb k6.toNat k5.toNat x1),
        Val.bv (k4.toNat - k3.toNat + 1) (BitVec.extractLsb k4.toNat k3.toNat x1)] ++ vs2) := by simp
  have hlist' : vs0 ++ Val.bv (k6.toNat - k3.toNat + 1) (BitVec.extractLsb k6.toNat k3.toNat x1) :: vs2 =
      vs0 ++ ([Val.bv (k6.toNat - k3.toNat + 1) (BitVec.extractLsb k6.toNat k3.toNat x1)] ++ vs2) := by simp
  rw [hlist] at hn hxbits
  rw [hlist'] at hn' hx'bits
  have hw : catW [Val.bv (k6.toNat - k5.toNat + 1) (BitVec.extractLsb k6.toNat k5.toNat x1),
      Val.bv (k4.toNat - k3.toNat + 1) (BitVec.extractLsb k4.toNat k3.toNat x1)] =
      catW [Val.bv (k6.toNat - k3.toNat + 1) (BitVec.extractLsb k6.toNat k3.toNat x1)] := by
    simp only [catW]; omega
  have hb : ∀ i, catBit [Val.bv (k6.toNat - k5.toNat + 1) (BitVec.extractLsb k6.toNat k5.toNat x1),
      Val.bv (k4.toNat - k3.toNat + 1) (BitVec.extractLsb k4.toNat k3.toNat x1)] i =
      catBit [Val.bv (k6.toNat - k3.toNat + 1) (BitVec.extractLsb k6.toNat k3.toNat x1)] i := by
    intro i
    simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, BitVec.getLsbD_extractLsb]
    by_cases hi : i < k4.toNat - k3.toNat + 1
    · rw [ite_eq_left hi, decide_eq_true hi, decide_eq_true (by omega)]
    · rw [ite_eq_right hi, show k5.toNat + (i - (k4.toNat - k3.toNat + 1)) = k3.toNat + i by omega]
      congr 1
      exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩
  apply val_ext (by rw [hn, hn', catW_append, catW_append, catW_append, catW_append, hw])
  intro i _
  rw [hxbits, hx'bits, catBit_mid _ _ _ _ hw hb]

-- rewrite id 65
theorem sound_BV_NOT_XOR :
    (RwRule.mk [.bvq, .bvq, .bvqs]
      (none)
      (bvnot' (bvxor' [var 0, var 1, var 2]))
      (bvxor' [bvnot' (var 0), var 1, var 2])).Sound := by
  intro env henv _ hl hr
  obtain ⟨w0, x0, h0, _⟩ := henv 0 .bvq rfl
  obtain ⟨w1, x1, h1, _⟩ := henv 1 .bvq rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  lists_pat at hl hr ⊢
  simp only [h0, h1, h2] at hl hr ⊢
  lists_pat at hl hr ⊢
  obtain ⟨w, a, hX, hw, hlv⟩ := lists_not_isBv hl
  obtain ⟨_, hx0⟩ := lists_mem_bv lists_bitXor hX (v := .bv w0 x0) (by simp)
  injection hx0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [lists_not_eval, ite_eq_left hw] at hr ⊢
  obtain ⟨w', b, hrv⟩ := lists_bitXor.isBv hr (fun v hv => by simp at hv)
  obtain ⟨_, hx1⟩ := lists_mem_bv lists_bitXor hrv (v := .bv w1 x1) (by simp)
  obtain ⟨_, hx1'⟩ := lists_mem_bv lists_bitXor hX (v := .bv w1 x1) (by simp)
  injection hx1 with e1 e2; subst e1
  injection hx1' with e1 e2; subst e1
  rw [hlv, hrv]
  apply val_ext rfl
  intro i hi
  rw [BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and, lists_bits lists_bitXor hX hi, lists_bits lists_bitXor hrv hi]
  simp only [List.map_cons, lists_vbit_bv, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]
  simp only [foldl_cons_op lists_bitXor.assoc lists_bitXor.comm lists_bitXor.id]
  exact (Bool.not_xor _ _).symm

-- rewrite id 66
theorem sound_BV_AND_SIMPLIFY_1 :
    (RwRule.mk [.bvqs, .bvqs, .bvqs, .bvq, .bv 32]
      (some (eq' (var 4) (bvsize' (var 3))))
      (bvand' [var 0, bvnot' (var 3), var 1, var 3, var 2])
      (symVal (l0) (var 4))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  rw [(toNat_of_bvsize hc).1] at hr ⊢
  exact lists_and_simp (x3 := x3) (by simp) (by simp) (by simp; omega) hl hr

-- rewrite id 67
theorem sound_BV_AND_SIMPLIFY_2 :
    (RwRule.mk [.bvqs, .bvqs, .bvqs, .bvq, .bv 32]
      (some (eq' (var 4) (bvsize' (var 3))))
      (bvand' [var 0, var 3, var 1, bvnot' (var 3), var 2])
      (symVal (l0) (var 4))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  rw [(toNat_of_bvsize hc).1] at hr ⊢
  exact lists_and_simp (x3 := x3) (by simp) (by simp) (by simp; omega) hl hr

-- rewrite id 68
theorem sound_BV_OR_SIMPLIFY_1 :
    (RwRule.mk [.bvqs, .bvqs, .bvqs, .bvq, .bv 32]
      (some (eq' (var 4) (bvsize' (var 3))))
      (bvor' [var 0, bvnot' (var 3), var 1, var 3, var 2])
      (bvnot' (symVal (l0) (var 4)))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  rw [(toNat_of_bvsize hc).1] at hr ⊢
  exact lists_or_simp (x3 := x3) (by simp) (by simp) (by simp; omega) hl hr

-- rewrite id 69
theorem sound_BV_OR_SIMPLIFY_2 :
    (RwRule.mk [.bvqs, .bvqs, .bvqs, .bvq, .bv 32]
      (some (eq' (var 4) (bvsize' (var 3))))
      (bvor' [var 0, var 3, var 1, bvnot' (var 3), var 2])
      (bvnot' (symVal (l0) (var 4)))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  rw [(toNat_of_bvsize hc).1] at hr ⊢
  exact lists_or_simp (x3 := x3) (by simp) (by simp) (by simp; omega) hl hr

-- rewrite id 70
theorem sound_BV_XOR_SIMPLIFY_2 :
    (RwRule.mk [.bvqs, .bvqs, .bvqs, .bvq]
      (none)
      (bvxor' [var 0, var 3, var 1, bvnot' (var 3), var 2])
      (bvnot' (bvxor' [var 0, var 1, var 2]))).Sound := by
  intro env henv _ hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  lists_pat at hl hr ⊢
  simp only [h0, h1, h2, h3] at hl hr ⊢
  lists_pat at hl hr ⊢
  obtain ⟨_, _, hxx, hw3, hNv⟩ := lists_not_isBv (lists_bitXor.mem_ne_bad hl (appVal .bvnot [.bv w3 x3]) (by simp))
  injection hxx with e1 e2; subst e1; have := eq_of_heq e2; subst this
  apply lists_xor_flip (x := x3) (by simp) (fun v hv => lists_sub2 hv)
    (fun v hv => by have := congrArg List.length hv; simp at this; omega) hl hr
  intro i hi
  simp only [List.map_append, List.map_cons, hNv, lists_vbit_bv]
  rw [foldl_mid lists_xor_assoc lists_xor_comm lists_xor_id, ← List.append_assoc,
    foldl_mid lists_xor_assoc lists_xor_comm lists_xor_id, List.append_assoc, BitVec.getLsbD_not, decide_eq_true hi,
    Bool.true_and, lists_xor_assoc, Bool.not_xor_self, Bool.xor_true]

-- rewrite id 71
theorem sound_BV_XOR_SIMPLIFY_3 :
    (RwRule.mk [.bvqs, .bvqs, .bvqs, .bvq]
      (none)
      (bvxor' [var 0, bvnot' (var 3), var 1, var 3, var 2])
      (bvnot' (bvxor' [var 0, var 1, var 2]))).Sound := by
  intro env henv _ hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  lists_pat at hl hr ⊢
  simp only [h0, h1, h2, h3] at hl hr ⊢
  lists_pat at hl hr ⊢
  obtain ⟨_, _, hxx, hw3, hNv⟩ := lists_not_isBv (lists_bitXor.mem_ne_bad hl (appVal .bvnot [.bv w3 x3]) (by simp))
  injection hxx with e1 e2; subst e1; have := eq_of_heq e2; subst this
  apply lists_xor_flip (x := x3) (by simp) (fun v hv => lists_sub2 hv)
    (fun v hv => by have := congrArg List.length hv; simp at this; omega) hl hr
  intro i hi
  simp only [List.map_append, List.map_cons, hNv, lists_vbit_bv]
  rw [foldl_mid lists_xor_assoc lists_xor_comm lists_xor_id, ← List.append_assoc,
    foldl_mid lists_xor_assoc lists_xor_comm lists_xor_id, List.append_assoc, BitVec.getLsbD_not, decide_eq_true hi,
    Bool.true_and, lists_xor_assoc, Bool.xor_not_self, Bool.xor_true]

/-- An xor keeps its value when an operand that occurs twice is dropped. -/
theorem lists_xor_same {l l' : List Val} (hsub : ∀ v ∈ l', v ∈ l) (h2 : 2 ≤ l.length)
    (hl : appVal .bvxor l ≠ .bad) (hr : appVal .bvxor l' ≠ .bad)
    (hbits : ∀ i, (l.map (lists_vbit i)).foldl (· ^^ ·) false =
      (l'.map (lists_vbit i)).foldl (· ^^ ·) false) :
    appVal .bvxor l = appVal .bvxor l' := by
  obtain ⟨w, a, hla⟩ := lists_bitXor.isBv hl (fun v hv => by rw [hv] at h2; simp at h2)
  obtain ⟨n, b, hlb⟩ := lists_bitXor.isBv hr (fun v hv => by
    obtain ⟨x, hx⟩ := lists_mem_bv lists_bitXor hla (hsub v (by rw [hv]; simp))
    exact ⟨w, x, hx⟩)
  obtain ⟨z, hz⟩ := lists_exists_mem lists_bitXor hlb
  obtain ⟨_, hz'⟩ := lists_mem_bv lists_bitXor hla (hsub _ hz)
  injection hz' with e1 _; subst e1
  rw [hla, hlb]
  apply val_ext rfl
  intro i hi
  rw [lists_bits lists_bitXor hla hi, lists_bits lists_bitXor hlb hi, lists_bitXor_f, lists_bitXor_e]
  exact hbits i

-- rewrite id 152 (cvc5 `bv-xor-simplify-1`, not in BCF's table)
theorem sound_BV_XOR_SIMPLIFY_1 :
    (RwRule.mk [.bvqs, .bvqs, .bvqs, .bvq]
      (none)
      (bvxor' [var 0, var 3, var 1, var 3, var 2])
      (bvxor' [var 0, var 1, var 2])).Sound := by
  intro env henv _ hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  lists_pat at hl hr ⊢
  simp only [h0, h1, h2, h3] at hl hr ⊢
  lists_pat at hl hr ⊢
  apply lists_xor_same (fun v hv => lists_sub2 hv)
    (by simp; omega) hl hr
  intro i
  simp only [List.map_append, List.map_cons, lists_vbit_bv]
  rw [foldl_mid lists_xor_assoc lists_xor_comm lists_xor_id, ← List.append_assoc,
    foldl_mid lists_xor_assoc lists_xor_comm lists_xor_id, List.append_assoc, lists_xor_assoc,
    Bool.xor_self, Bool.xor_false]

-- rewrite id 72
theorem sound_BV_ULT_ADD_ONE :
    (RwRule.mk [.bvq, .bvqs, .bvqs, .bvq, .bv 32]
      (some (conj' [eq' (var 3) (symVal (l1) (var 4)), eq' (var 4) (bvsize' (var 0))]))
      (ult' (var 0) (bvadd' [var 1, var 3, var 2]))
      (conj' [not' (eq' (bvadd' [var 1, var 2]) (bvnot' (symVal (l0) (var 4)))), not' (ult' (bvadd' [var 1, var 2]) (var 0))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, _⟩ := henv 0 .bvq rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  obtain ⟨hc1, hc2⟩ := conj_all2 hc
  rw [(toNat_of_bvsize hc2).1] at hc1 hr ⊢
  rw [show 1 % 2 ^ 32 = 1 by decide] at hc1
  have h1e := (eq_true hc1).symm
  have hw3 := bvValEval_width h1e
  subst hw3
  obtain ⟨hx3, hw0, _, _⟩ := bvValEval_val h1e
  subst hx3
  -- the left-hand side
  rw [spliceVal_appVal (fun _ v hv e vs hvl => by
    have := lists_single_of_append hv; rw [hvl] at this; exact Val.noConfusion this)] at hl ⊢
  obtain ⟨a, hA, hlv⟩ := lists_ult_isBv hl
  obtain ⟨xs, hxs, ha⟩ := lists_add_eval hA
  obtain ⟨ys1, zs, rfl, hys1, hzs⟩ := List.map_eq_append_iff.mp hxs.symm
  obtain ⟨c, ys2, rfl, hc3, hys2⟩ := List.map_eq_cons_iff.mp hzs
  injection hc3 with _ hc3'
  subst hc3'
  subst hys1; subst hys2
  rw [foldl_mid (f := fun x1 x2 : BitVec w3 => x1 + x2) (e := 0) BitVec.add_assoc BitVec.add_comm
    BitVec.zero_add] at ha
  -- the right-hand side
  rw [← List.map_append] at hr ⊢
  cases hys : ys1 ++ ys2 with
  | nil =>
    rw [hys] at hr
    simp only [List.map_nil, appVal, spliceVal, List.singleton_append] at hr
    exact absurd rfl hr
  | cons y ys =>
    rw [hys] at hr ha
    rw [lists_add_map _ (by simp) hw0, spliceVal_bv] at hr ⊢
    simp only [List.singleton_append] at hr ⊢
    rcases lit_cases w3 0 with hL | ⟨_, _, _, hL⟩
    · rw [hL, lists_bvnot_bad, lists_eq_bad_r, lists_not_bad, lists_conj_bad_l] at hr
      exact absurd rfl hr
    rw [hlv, ha, hL, lists_not_eval, ite_eq_left hw0, lists_eq_bv, lists_not_bool, ult_eval, dite_eq_left rfl, BitVec.cast_eq,
      lists_not_bool, lists_conj_bool]
    congr 1
    generalize List.foldl (· + ·) 0 (y :: ys) = s
    have h1 : (BitVec.ofNat w3 1).toNat = 1 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw0)
    rw [BitVec.not_zero, show decide (s = BitVec.allOnes w3) = decide (s.toNat = 2 ^ w3 - 1) from
      decide_eq_decide.mpr (by rw [BitVec.toNat_eq, BitVec.toNat_allOnes])]
    simp only [BitVec.ult, BitVec.toNat_add, h1]
    have hs := s.isLt
    have hx := x0.isLt
    have hp := Nat.two_pow_pos w3
    by_cases hmax : s.toNat = 2 ^ w3 - 1
    · rw [decide_eq_true hmax, show (s.toNat + 1) % 2 ^ w3 = 0 by rw [hmax, Nat.sub_add_cancel hp, Nat.mod_self]]
      simp
    · rw [decide_eq_false hmax, Nat.mod_eq_of_lt (by omega)]
      simp only [Bool.not_false, Bool.true_and]
      rw [show decide (x0.toNat < s.toNat + 1) = decide (¬ s.toNat < x0.toNat) from
        decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩, decide_not]

-- rewrite id 115
theorem sound_BV_XOR_CONCAT_PULLUP :
    (RwRule.mk [.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 6) (bvsize' (var 2)), eq' (var 5) (bvsub' (bvsize' (bvxor' [var 0, var 1])) (l1)), eq' (var 7) (bvsub' (bvsize' (var 2)) (l1))]))
      (bvxor' [var 0, concat' [var 4, var 3, var 2], var 1])
      (concat' [bvxor' [extract (var 5) (var 6) (bvxor' [var 0, var 1]), concat' [var 4, var 3]], bvxor' [extract (var 7) (l0) (bvxor' [var 0, var 1]), var 2]])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  obtain ⟨vs4, h4⟩ := henv 4 .bvqs rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  obtain ⟨k7, h7⟩ := henv 7 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  have hk6 := (toNat_of_bvsize (conjN_true hc _ (by apply List.mem_cons_self))).1
  have key := pullup_eq lists_bitXor (vs0 := vs0) (vs1 := vs1) (H := vs4 ++ [.bv w3 x3]) (L := [.bv w2 x2])
    (k5 := k5.toNat) (k6 := k6.toNat) (k7 := k7.toNat) (by simp) (by simp) (by simp [catW, hk6])
  simp only [List.append_assoc, List.cons_append, appVal_concat_single] at key
  exact key hl hr

-- rewrite id 118
theorem sound_BV_XOR_CONCAT_PULLUP2 :
    (RwRule.mk [.bvqs, .bvqs, .bvq, .bvq, .bvqs, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 6) (bvsize' (concat' [var 2, var 4])), eq' (var 5) (bvsub' (bvsize' (bvxor' [var 0, var 1])) (l1)), eq' (var 7) (bvsub' (bvsize' (concat' [var 2, var 4])) (l1))]))
      (bvxor' [var 0, concat' [var 3, var 2, var 4], var 1])
      (concat' [bvxor' [extract (var 5) (var 6) (bvxor' [var 0, var 1]), var 3], bvxor' [extract (var 7) (l0) (bvxor' [var 0, var 1]), concat' [var 2, var 4]]])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, h3, _⟩ := henv 3 .bvq rfl
  obtain ⟨vs4, h4⟩ := henv 4 .bvqs rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  obtain ⟨k7, h7⟩ := henv 7 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  obtain ⟨n, y, hcv, hk6, _⟩ := bvsize_eq_true (conjN_true hc _ (by apply List.mem_cons_self))
  obtain ⟨n', y', hcv', _, hn', _⟩ := appVal_concat_bits (l := .bv w2 x2 :: vs4) (by rw [hcv]; simp)
    (fun v hv => by cases vs4 with
      | nil => simp at hv; subst hv; exact ⟨_, _, rfl⟩
      | cons _ _ => simp at hv)
  rw [hcv] at hcv'
  injection hcv' with hnn _
  have key := pullup_eq lists_bitXor (vs0 := vs0) (vs1 := vs1) (H := [.bv w3 x3]) (L := .bv w2 x2 :: vs4)
    (k5 := k5.toNat) (k6 := k6.toNat) (k7 := k7.toNat) (by simp) (by simp) (by rw [hk6, hnn, hn'])
  simp only [List.cons_append, appVal_concat_single] at key
  exact key hl hr

-- rewrite id 119
theorem sound_BV_AND_CONCAT_PULLUP3 :
    (RwRule.mk [.bvqs, .bvqs, .bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 5) (bvsub' (bvsize' (bvand' [var 0, var 1])) (l1)), eq' (var 6) (bvadd' [bvsize' (var 2), bvsize' (var 4)]), eq' (var 7) (bvsub' (bvadd' [bvsize' (var 2), bvsize' (var 4)]) (l1)), eq' (var 8) (bvsize' (var 4)), eq' (var 9) (bvsub' (bvsize' (var 4)) (l1))]))
      (bvand' [var 0, concat' [var 3, var 2, var 4], var 1])
      (concat' [bvand' [extract (var 5) (var 6) (bvand' [var 0, var 1]), var 3], bvand' [extract (var 7) (var 8) (bvand' [var 0, var 1]), var 2], bvand' [extract (var 9) (l0) (bvand' [var 0, var 1]), var 4]])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, h3, hw3⟩ := henv 3 .bvq rfl
  obtain ⟨w4, x4, h4, hw4⟩ := henv 4 .bvq rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  obtain ⟨k7, h7⟩ := henv 7 (.bv 32) rfl
  obtain ⟨k8, h8⟩ := henv 8 (.bv 32) rfl
  obtain ⟨k9, h9⟩ := henv 9 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  have hc6 := conjN_true hc _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  have hc8 := conjN_true hc _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [appVal_bvsize_small x2 hw2, appVal_bvsize_small x4 hw4, appVal_bvadd32] at hc6
  have hk6 : k6.toNat = w2 + w4 := by
    rw [eq_bv32 hc6, toNat_add32 _ _ (by rw [toNat_ofNat_small hw2, toNat_ofNat_small hw4, two32]; omega),
      toNat_ofNat_small hw2, toNat_ofNat_small hw4]
  exact lists_pullup3 bitAnd hk6 (toNat_of_bvsize hc8).1 hl hr

-- rewrite id 120
theorem sound_BV_OR_CONCAT_PULLUP3 :
    (RwRule.mk [.bvqs, .bvqs, .bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 5) (bvsub' (bvsize' (bvor' [var 0, var 1])) (l1)), eq' (var 6) (bvadd' [bvsize' (var 2), bvsize' (var 4)]), eq' (var 7) (bvsub' (bvadd' [bvsize' (var 2), bvsize' (var 4)]) (l1)), eq' (var 8) (bvsize' (var 4)), eq' (var 9) (bvsub' (bvsize' (var 4)) (l1))]))
      (bvor' [var 0, concat' [var 3, var 2, var 4], var 1])
      (concat' [bvor' [extract (var 5) (var 6) (bvor' [var 0, var 1]), var 3], bvor' [extract (var 7) (var 8) (bvor' [var 0, var 1]), var 2], bvor' [extract (var 9) (l0) (bvor' [var 0, var 1]), var 4]])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, h3, hw3⟩ := henv 3 .bvq rfl
  obtain ⟨w4, x4, h4, hw4⟩ := henv 4 .bvq rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  obtain ⟨k7, h7⟩ := henv 7 (.bv 32) rfl
  obtain ⟨k8, h8⟩ := henv 8 (.bv 32) rfl
  obtain ⟨k9, h9⟩ := henv 9 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  have hc6 := conjN_true hc _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  have hc8 := conjN_true hc _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [appVal_bvsize_small x2 hw2, appVal_bvsize_small x4 hw4, appVal_bvadd32] at hc6
  have hk6 : k6.toNat = w2 + w4 := by
    rw [eq_bv32 hc6, toNat_add32 _ _ (by rw [toNat_ofNat_small hw2, toNat_ofNat_small hw4, two32]; omega),
      toNat_ofNat_small hw2, toNat_ofNat_small hw4]
  exact lists_pullup3 bitOr hk6 (toNat_of_bvsize hc8).1 hl hr

-- rewrite id 121
theorem sound_BV_XOR_CONCAT_PULLUP3 :
    (RwRule.mk [.bvqs, .bvqs, .bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 5) (bvsub' (bvsize' (bvxor' [var 0, var 1])) (l1)), eq' (var 6) (bvadd' [bvsize' (var 2), bvsize' (var 4)]), eq' (var 7) (bvsub' (bvadd' [bvsize' (var 2), bvsize' (var 4)]) (l1)), eq' (var 8) (bvsize' (var 4)), eq' (var 9) (bvsub' (bvsize' (var 4)) (l1))]))
      (bvxor' [var 0, concat' [var 3, var 2, var 4], var 1])
      (concat' [bvxor' [extract (var 5) (var 6) (bvxor' [var 0, var 1]), var 3], bvxor' [extract (var 7) (var 8) (bvxor' [var 0, var 1]), var 2], bvxor' [extract (var 9) (l0) (bvxor' [var 0, var 1]), var 4]])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, h3, hw3⟩ := henv 3 .bvq rfl
  obtain ⟨w4, x4, h4, hw4⟩ := henv 4 .bvq rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  obtain ⟨k7, h7⟩ := henv 7 (.bv 32) rfl
  obtain ⟨k8, h8⟩ := henv 8 (.bv 32) rfl
  obtain ⟨k9, h9⟩ := henv 9 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  have hc6 := conjN_true hc _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  have hc8 := conjN_true hc _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [appVal_bvsize_small x2 hw2, appVal_bvsize_small x4 hw4, appVal_bvadd32] at hc6
  have hk6 : k6.toNat = w2 + w4 := by
    rw [eq_bv32 hc6, toNat_add32 _ _ (by rw [toNat_ofNat_small hw2, toNat_ofNat_small hw4, two32]; omega),
      toNat_ofNat_small hw2, toNat_ofNat_small hw4]
  exact lists_pullup3 lists_bitXor hk6 (toNat_of_bvsize hc8).1 hl hr

-- rewrite id 123
theorem sound_BV_XOR_ONES :
    (RwRule.mk [.bvqs, .bvqs, .bv 32, .bv 32]
      (some (eq' (var 2) (bvmax (var 3))))
      (bvxor' [var 0, symVal (var 2) (var 3), var 1])
      (bvnot' (bvxor' [var 0, var 1]))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  have hce := (eq_true hc).symm
  have hk3 := bvValEval_width hce
  obtain ⟨hk2, _⟩ := bvValEval_val (by rw [← hk3] at hce; exact hce)
  rw [← hk3, lit32 _ k2.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hl ⊢
  apply lists_xor_flip (x := k2) (by simp) (fun v hv => lists_sub1 hv)
    (fun v hv => by
      cases vs0 with
      | nil =>
        cases vs1 with
        | nil => simp at hv; subst hv; exact ⟨_, _, rfl⟩
        | cons _ _ => simp at hv
      | cons _ _ => simp at hv) hl hr
  intro i hi
  simp only [List.map_append, List.map_cons, lists_vbit_bv]
  rw [foldl_mid lists_xor_assoc lists_xor_comm lists_xor_id, hk2, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    decide_eq_true hi, Bool.true_and, Bool.xor_true]

/-! ### `bvmul` by a power of two -/

/-- A well-typed product of at least two operands is a product of same-width bit-vectors. -/
theorem lists_mul_eval {l : List Val} (h2 : 2 ≤ l.length) (h : appVal .bvmul l ≠ .bad) :
    ∃ (w : Nat) (xs : List (BitVec w)), w ≠ 0 ∧ l = xs.map (Val.bv w) ∧
      appVal .bvmul l = .bv w (xs.foldl (· * ·) 1) := by
  match l, h2 with
  | a :: b :: rest, _ =>
    simp only [appVal, RwOp.node, Op.eval] at h ⊢
    generalize RwOp.widthV .bvmul (a :: b :: rest) = W at h ⊢
    unfold bvN at h ⊢
    split at h
    · rename_i xs hxs
      split at h
      · rename_i hc
        exact ⟨W, xs, hc.1, bvs_map hxs, by simp [hc]⟩
      · exact absurd rfl h
    · exact absurd rfl h

theorem lists_mul_map {w : Nat} (xs : List (BitVec w)) (hne : xs ≠ []) (hw : w ≠ 0) :
    appVal .bvmul (xs.map (Val.bv w)) = .bv w (xs.foldl (· * ·) 1) := by
  match xs, hne with
  | [x], _ => simp [appVal, RwOp.reducible]
  | a :: b :: rest, _ =>
    simp only [appVal, RwOp.node, Op.eval]
    rw [show RwOp.widthV .bvmul (List.map (Val.bv w) (a :: b :: rest)) = w by
      simp [RwOp.widthV, RwOp.width, Val.tys, lists_tys_map, firstBv]]
    unfold bvN
    rw [bvs_of_map]
    simp [hw]

-- rewrite id 157 (cvc5 `bv-mult-pow2-1`, not in BCF's table).  cvc5's condition
-- `(int.ispow2 n) ∧ exponent = (int.log2 n)` is encoded as `n ≠ 0 ∧ n = 1 << exponent` in 32 bits.
theorem sound_BV_MULT_POW2_1 :
    (RwRule.mk [.bvqs, .bvqs, .bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [not' (eq' (var 4) l0), eq' (var 4) (bvshl' l1 (var 5)),
        eq' (var 6) (bvsub' (bvsub' (var 3) (var 5)) l1)]))
      (bvmul' [var 0, var 2, symVal (var 4) (var 3), var 1])
      (concat' [extract (var 6) l0 (bvmul' [var 0, var 2, var 1]), symVal l0 (var 5)])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨kS, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨kN, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨kE, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨kU, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  simp only [appVal_bvshl32, appVal_bvsub32, lists_eq_bv, lists_not_bool] at hc
  obtain ⟨hc1, hc2, hc3⟩ := conj_all3 hc
  simp only [Val.bool.injEq, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hc1 hc2 hc3
  -- the left-hand side
  obtain ⟨w, xs, hw, hxs, hlv⟩ := lists_mul_eval (by simp; omega) hl
  obtain ⟨ys0, zs, rfl, rfl, hzs⟩ := List.map_eq_append_iff.mp hxs.symm
  obtain ⟨c2, zs, rfl, hc2', hzs⟩ := List.map_eq_cons_iff.mp hzs
  obtain ⟨c3, ys1, rfl, hc3', rfl⟩ := List.map_eq_cons_iff.mp hzs
  injection hc2' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases kS.toNat kN.toNat with hL | ⟨hS0, hS64, hNlt, hL⟩
  · rw [hL] at hc3'; exact Val.noConfusion hc3'
  rw [hL] at hc3'
  injection hc3' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hlv]
  -- the right-hand side
  rw [← List.map_cons, ← List.map_append, lists_mul_map _ (by simp) hw] at hr ⊢
  obtain ⟨n, rv, hrv, hall, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨nE, e, hE⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨nZ, z, hZ⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨w0, y0, hy0, _, hUw, hEv⟩ := extract_of_ne_bad (by rw [hE]; simp : bvExtractEval kU.toNat 0 _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases kE.toNat 0 with hZ' | ⟨hE0, hE64, _, hZv⟩
  · rw [hZ'] at hZ; simp at hZ
  rw [hEv] at hE; rw [hZv] at hZ
  injection hE with hnE he; subst hnE; have := eq_of_heq he; subst this
  injection hZ with hnZ hz; subst hnZ; have := eq_of_heq hz; subst this
  rw [hEv, hZv] at hn hrbits
  rw [hrv]
  -- arithmetic on the condition
  have hEN : kE.toNat < 32 ∧ kN.toNat = 2 ^ kE.toNat := by
    have h := congrArg BitVec.toNat hc2
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (1#32).toNat = 1 by decide, Nat.one_mul] at h
    by_cases hE : kE.toNat < 32
    · exact ⟨hE, by rw [h, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hE)]⟩
    · exfalso; apply hc1; apply BitVec.eq_of_toNat_eq
      rw [h, Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))]; rfl
  have hU : kU.toNat + 1 + kE.toNat = kS.toNat := by
    have h := congrArg BitVec.toNat hc3
    simp only [BitVec.toNat_sub, show (1#32).toNat = 1 by decide, two32] at h
    have := kS.isLt; have := kE.isLt; rw [two32] at *
    omega
  apply val_ext (by rw [hn]; simp only [catW]; omega)
  intro i hi
  rw [hrbits]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  have hc3v : BitVec.ofNat kS.toNat kN.toNat = BitVec.twoPow kS.toNat kE.toNat := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat, hEN.2]
  rw [show ys0 ++ c2 :: BitVec.ofNat kS.toNat kN.toNat :: ys1 = (ys0 ++ [c2]) ++ BitVec.ofNat kS.toNat kN.toNat :: ys1
    by simp, foldl_mid (f := fun x1 x2 : BitVec kS.toNat => x1 * x2) (e := 1) BitVec.mul_assoc BitVec.mul_comm
      BitVec.one_mul, hc3v, ← BitVec.shiftLeft_eq_mul_twoPow,
    BitVec.getLsbD_shiftLeft, List.append_assoc, List.singleton_append, decide_eq_true hi, Bool.true_and]
  by_cases hik : i < kE.toNat
  · simp [hik]
  · simp only [hik, ↓reduceIte, decide_false, BitVec.getLsbD_extractLsb, decide_eq_true (by omega : i - kE.toNat < kU.toNat - 0 + 1)]
    simp

theorem lists_neg_eval {w : Nat} (x : BitVec w) :
    appVal .bvneg [.bv w x] = if w ≠ 0 then .bv w (- x) else .bad := by
  simp [appVal, RwOp.reducible, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvUn]

-- rewrite id 158 (cvc5 `bv-mult-pow2-2`, not in BCF's table).  cvc5's condition
-- `int.ispow2 (2^size - n)`, `exponent = int.log2 (2^size - n)` is encoded as `(@bv n size) = -(1 << exponent)`
-- at width `size`.
theorem sound_BV_MULT_POW2_2 :
    (RwRule.mk [.bvqs, .bvqs, .bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (symVal (var 4) (var 3)) (bvneg' (bvshl' (symVal l1 (var 3)) (symVal (var 5) (var 3)))),
        eq' (var 6) (bvsub' (bvsub' (var 3) (var 5)) l1)]))
      (bvmul' [var 0, var 2, symVal (var 4) (var 3), var 1])
      (concat' [extract (var 6) l0 (bvneg' (bvmul' [var 0, var 2, var 1])), symVal l0 (var 5)])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨kS, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨kN, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨kE, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨kU, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.bvneg'] at hc hr ⊢
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvneg = false),
    appVal_bvsub32] at hc
  obtain ⟨hc1, hc3⟩ := conj_all2 hc
  simp only [lists_eq_bv, Val.bool.injEq, decide_eq_true_eq] at hc3
  rw [show 1 % 2 ^ 32 = 1 by decide] at hc1
  -- the left-hand side
  obtain ⟨w, xs, hw, hxs, hlv⟩ := lists_mul_eval (by simp; omega) hl
  obtain ⟨ys0, zs, rfl, rfl, hzs⟩ := List.map_eq_append_iff.mp hxs.symm
  obtain ⟨c2, zs, rfl, hc2', hzs⟩ := List.map_eq_cons_iff.mp hzs
  obtain ⟨c3, ys1, rfl, hc3', rfl⟩ := List.map_eq_cons_iff.mp hzs
  injection hc2' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases kS.toNat kN.toNat with hL | ⟨hS0, hS64, hNlt, hL⟩
  · rw [hL] at hc3'; exact Val.noConfusion hc3'
  rw [hL] at hc3' hc1
  injection hc3' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hlv]
  -- the condition
  have hc1' := eq_true hc1
  rcases lit_cases kS.toNat kE.toNat with hLE | ⟨_, _, hElt, hLE⟩
  · rw [hLE] at hc1'; simp [appVal, RwOp.node, Op.eval, bvBin, bvUn, RwOp.widthV, Val.tys, Val.ty] at hc1'
  rcases lit_cases kS.toNat 1 with hL1 | ⟨_, _, _, hL1⟩
  · rw [hL1] at hc1'; simp [appVal, RwOp.node, Op.eval, bvBin, bvUn, RwOp.widthV, Val.tys, Val.ty] at hc1'
  rw [hLE, hL1, shl_eval, dite_eq_left rfl, ite_eq_left hw, lists_neg_eval, ite_eq_left hw] at hc1'
  injection hc1' with _ hNv
  -- the right-hand side
  rw [← List.map_cons, ← List.map_append, lists_mul_map _ (by simp) hw, spliceVal_bv, lists_neg_eval,
    ite_eq_left hw] at hr ⊢
  obtain ⟨n, rv, hrv, hall, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨nE, e, hE⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨nZ, z, hZ⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨w0, y0, hy0, _, hUw, hEv⟩ := extract_of_ne_bad (by rw [hE]; simp : bvExtractEval kU.toNat 0 _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases kE.toNat 0 with hZ' | ⟨hE0, hE64, _, hZv⟩
  · rw [hZ'] at hZ; simp at hZ
  rw [hEv] at hE; rw [hZv] at hZ
  injection hE with hnE he; subst hnE; have := eq_of_heq he; subst this
  injection hZ with hnZ hz; subst hnZ; have := eq_of_heq hz; subst this
  rw [hEv, hZv] at hn hrbits
  rw [hrv]
  -- arithmetic
  have hU : kU.toNat + 1 + kE.toNat = kS.toNat := by
    have h := congrArg BitVec.toNat hc3
    simp only [BitVec.toNat_sub, show (1#32).toNat = 1 by decide, two32] at h
    have := kS.isLt; have := kE.isLt; rw [two32] at *
    omega
  have hc3v : BitVec.ofNat kS.toNat kN.toNat = -BitVec.twoPow kS.toNat kE.toNat := by
    rw [hNv, BitVec.cast_eq, BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hElt]; rfl
  apply val_ext (by rw [hn]; simp only [catW]; omega)
  intro i hi
  rw [hrbits]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  rw [show ys0 ++ c2 :: BitVec.ofNat kS.toNat kN.toNat :: ys1 = (ys0 ++ [c2]) ++ BitVec.ofNat kS.toNat kN.toNat :: ys1
    by simp, foldl_mid (f := fun x1 x2 : BitVec kS.toNat => x1 * x2) (e := 1) BitVec.mul_assoc BitVec.mul_comm
      BitVec.one_mul, hc3v, BitVec.mul_neg, ← BitVec.neg_mul, ← BitVec.shiftLeft_eq_mul_twoPow,
    BitVec.getLsbD_shiftLeft, List.append_assoc, List.singleton_append, decide_eq_true hi, Bool.true_and]
  by_cases hik : i < kE.toNat
  · simp [hik]
  · simp only [hik, ↓reduceIte, decide_false, BitVec.getLsbD_extractLsb,
      decide_eq_true (by omega : i - kE.toNat < kU.toNat - 0 + 1)]
    simp

-- rewrite id 159 (cvc5 `bv-mult-pow2-2b`, not in BCF's table); condition encoded as for 158.
theorem sound_BV_MULT_POW2_2B :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (symVal (var 2) (var 1)) (bvneg' (bvshl' (symVal l1 (var 1)) (symVal (var 3) (var 1)))),
        eq' (var 4) (bvsub' (bvsub' (var 1) (var 3)) l1)]))
      (bvmul' [var 0, symVal (var 2) (var 1)])
      (concat' [extract (var 4) l0 (bvneg' (var 0)), symVal l0 (var 3)])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨kS, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨kN, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨kE, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨kU, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.bvneg'] at hc hr ⊢
  lists_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  lists_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvneg = false),
    appVal_bvsub32] at hc
  obtain ⟨hc1, hc3⟩ := conj_all2 hc
  simp only [lists_eq_bv, Val.bool.injEq, decide_eq_true_eq] at hc3
  rw [show 1 % 2 ^ 32 = 1 by decide] at hc1
  -- the left-hand side
  obtain ⟨w, xs, hw, hxs, hlv⟩ := lists_mul_eval (by simp) hl
  obtain ⟨c0, zs, rfl, hz', hzs⟩ := List.map_eq_cons_iff.mp hxs.symm
  obtain ⟨c1, ys, rfl, hn', hys⟩ := List.map_eq_cons_iff.mp hzs
  obtain rfl := List.map_eq_nil_iff.mp hys
  injection hz' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases kS.toNat kN.toNat with hL | ⟨hS0, hS64, hNlt, hL⟩
  · rw [hL] at hn'; exact Val.noConfusion hn'
  rw [hL] at hn' hc1
  injection hn' with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hlv]
  -- the condition
  have hc1' := eq_true hc1
  rcases lit_cases kS.toNat kE.toNat with hLE | ⟨_, _, hElt, hLE⟩
  · rw [hLE] at hc1'; simp [appVal, RwOp.node, Op.eval, bvBin, bvUn, RwOp.widthV, Val.tys, Val.ty] at hc1'
  rcases lit_cases kS.toNat 1 with hL1 | ⟨_, _, _, hL1⟩
  · rw [hL1] at hc1'; simp [appVal, RwOp.node, Op.eval, bvBin, bvUn, RwOp.widthV, Val.tys, Val.ty] at hc1'
  rw [hLE, hL1, shl_eval, dite_eq_left rfl, ite_eq_left hw, lists_neg_eval, ite_eq_left hw] at hc1'
  injection hc1' with _ hNv
  -- the right-hand side
  rw [lists_neg_eval, ite_eq_left hw] at hr ⊢
  obtain ⟨n, rv, hrv, hall, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨nE, e, hE⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨nZ, z, hZ⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨w0, y0, hy0, _, hUw, hEv⟩ := extract_of_ne_bad (by rw [hE]; simp : bvExtractEval kU.toNat 0 _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases kE.toNat 0 with hZ' | ⟨hE0, hE64, _, hZv⟩
  · rw [hZ'] at hZ; simp at hZ
  rw [hEv] at hE; rw [hZv] at hZ
  injection hE with hnE he; subst hnE; have := eq_of_heq he; subst this
  injection hZ with hnZ hz; subst hnZ; have := eq_of_heq hz; subst this
  rw [hEv, hZv] at hn hrbits
  rw [hrv]
  -- arithmetic
  have hU : kU.toNat + 1 + kE.toNat = kS.toNat := by
    have h := congrArg BitVec.toNat hc3
    simp only [BitVec.toNat_sub, show (1#32).toNat = 1 by decide, two32] at h
    have := kS.isLt; have := kE.isLt; rw [two32] at *
    omega
  have hc3v : BitVec.ofNat kS.toNat kN.toNat = -BitVec.twoPow kS.toNat kE.toNat := by
    rw [hNv, BitVec.cast_eq, BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hElt]; rfl
  apply val_ext (by rw [hn]; simp only [catW]; omega)
  intro i hi
  rw [hrbits]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  rw [List.foldl_cons, List.foldl_cons, List.foldl_nil,
    show (1 : BitVec kS.toNat) * c0 = c0 by simp, hc3v, BitVec.mul_neg,
    ← BitVec.neg_mul, ← BitVec.shiftLeft_eq_mul_twoPow, BitVec.getLsbD_shiftLeft, decide_eq_true hi, Bool.true_and]
  by_cases hik : i < kE.toNat
  · simp [hik]
  · simp only [hik, ↓reduceIte, decide_false, BitVec.getLsbD_extractLsb,
      decide_eq_true (by omega : i - kE.toNat < kU.toNat - 0 + 1)]
    simp

end Bcf
