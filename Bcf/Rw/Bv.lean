import Bcf.Rw.Core
import Bcf.BitblastSound

/-!
# Soundness of the bit-vector rewrites with list parameters

The rewrites here splice list parameters (`BVQs`) into concatenations and
bitwise operators.  The first part is a small value-level library:
concatenation as a bit function (`catW`, `catBit`), bitwise operators as
folds over spliced argument lists, and extraction.
-/

namespace Bcf

def IsBv (v : Val) : Prop := ∃ (w : Nat) (x : BitVec w), v = .bv w x

theorem val_ext {n m : Nat} {x : BitVec n} {y : BitVec m} (h : n = m)
    (hb : ∀ i, i < n → x.getLsbD i = y.getLsbD i) : Val.bv n x = Val.bv m y := by
  subst h; rw [bv_ext hb]

/-! ## Concatenation as a bit function -/

def catW : List Val → Nat
  | [] => 0
  | .bv w _ :: r => w + catW r
  | _ :: r => catW r

/-- Bit `i` of the concatenation of a list (most significant first). -/
def catBit : List Val → Nat → Bool
  | [], _ => false
  | .bv _ x :: r, i => if i < catW r then catBit r i else x.getLsbD (i - catW r)
  | _ :: r, i => catBit r i

theorem catW_bv_cons {w : Nat} (x : BitVec w) (r : List Val) : catW (.bv w x :: r) = w + catW r := rfl
theorem catBit_bv_cons {w : Nat} (x : BitVec w) (r : List Val) (i : Nat) :
    catBit (.bv w x :: r) i = if i < catW r then catBit r i else x.getLsbD (i - catW r) := rfl

theorem catW_append (a b : List Val) : catW (a ++ b) = catW a + catW b := by
  induction a with
  | nil => simp [catW]
  | cons v a ih => cases v <;> simp [catW, ih] <;> omega

theorem catBit_ge : ∀ (l : List Val) (i : Nat), catW l ≤ i → catBit l i = false := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons v r ih =>
    intro i hi
    cases v with
    | bv w x =>
      rw [catBit_bv_cons]; rw [catW_bv_cons] at hi
      rw [ite_eq_right (by omega)]
      exact BitVec.getLsbD_of_ge x _ (by omega)
    | bool _ => exact ih i hi
    | list _ _ => exact ih i hi
    | bad => exact ih i hi

theorem catBit_append (a b : List Val) (i : Nat) :
    catBit (a ++ b) i = if i < catW b then catBit b i else catBit a (i - catW b) := by
  induction a with
  | nil =>
    simp only [List.nil_append]
    split
    · rfl
    · rw [catBit_ge b i (by omega)]; rfl
  | cons v a ih =>
    cases v with
    | bv w x =>
      simp only [List.cons_append, catBit_bv_cons, catW_append, ih]
      by_cases h1 : i < catW b
      · have h2 : i < catW a + catW b := by omega
        simp [h1, h2]
      · by_cases h2 : i < catW a + catW b
        · have h3 : i - catW b < catW a := by omega
          simp [h1, h2, h3]
        · have h3 : ¬ i - catW b < catW a := by omega
          have h4 : i - (catW a + catW b) = i - catW b - catW a := by omega
          simp [h1, h2, h3, h4]
    | bool _ => simp only [List.cons_append]; exact ih
    | list _ _ => simp only [List.cons_append]; exact ih
    | bad => simp only [List.cons_append]; exact ih

/-- A defined concatenation: widths add up and bits are `catBit`. -/
theorem concatVals_bits : ∀ (l : List Val) {n : Nat} {x : BitVec n}, Val.concatVals l = some (.bv n x) →
    (∀ v ∈ l, IsBv v) ∧ n = catW l ∧ ∀ i, x.getLsbD i = catBit l i := by
  intro l
  induction l with
  | nil => intro n x h; simp [Val.concatVals] at h
  | cons a rest ih =>
    intro n x h
    cases rest with
    | nil =>
      cases a with
      | bv w y =>
        simp only [Val.concatVals, Option.some.injEq] at h
        injection h with hw hy
        subst hw
        have := eq_of_heq hy; subst this
        refine ⟨fun v hv => ⟨w, y, by simpa using hv⟩, by simp [catW], fun i => by simp [catBit, catW]⟩
      | bool _ => simp [Val.concatVals] at h
      | list _ _ => simp [Val.concatVals] at h
      | bad => simp [Val.concatVals] at h
    | cons b rest' =>
      rw [concatVals_cons_ne (by simp)] at h
      cases ha : a with
      | bv w y =>
        subst ha
        cases hc : Val.concatVals (b :: rest') with
        | none => rw [hc] at h; simp [catOpt] at h
        | some u =>
          rw [hc] at h
          cases u with
          | bv m z =>
            simp only [catOpt, Option.some.injEq] at h
            injection h with hw hz
            subst hw
            have := eq_of_heq hz; subst this
            obtain ⟨hall, hm, hbits⟩ := ih hc
            refine ⟨?_, by rw [catW_bv_cons, hm], ?_⟩
            · intro v hv
              simp only [List.mem_cons] at hv
              rcases hv with rfl | hv
              · exact ⟨w, y, rfl⟩
              · exact hall v (by simpa using hv)
            · intro i
              rw [BitVec.getLsbD_append, catBit_bv_cons, hbits, ← hm]
          | bool _ => simp [catOpt] at h
          | list _ _ => simp [catOpt] at h
          | bad => simp [catOpt] at h
      | bool _ => subst ha; simp [catOpt] at h
      | list _ _ => subst ha; simp [catOpt] at h
      | bad => subst ha; simp [catOpt] at h

/-- A defined pattern concatenation. -/
theorem appVal_concat_bits {l : List Val} (h : appVal .concat l ≠ .bad)
    (hsingle : ∀ v, l = [v] → IsBv v) :
    ∃ n x, appVal .concat l = .bv n x ∧ (∀ v ∈ l, IsBv v) ∧ n = catW l ∧ ∀ i, x.getLsbD i = catBit l i := by
  match l, h, hsingle with
  | [], h, _ => exact absurd rfl h
  | [v], h, hsingle =>
    obtain ⟨w, y, rfl⟩ := hsingle v rfl
    refine ⟨w, y, rfl, fun u hu => ⟨w, y, by simpa using hu⟩, by simp [catW], fun i => by simp [catBit, catW]⟩
  | a :: b :: rest, h, _ =>
    simp only [appVal, RwOp.node, Op.eval] at h ⊢
    generalize RwOp.widthV .concat (a :: b :: rest) = W at h ⊢
    unfold bvConcatEval at h ⊢
    split at h
    · rename_i n x hc
      split at h
      · rename_i hcond
        rw [dite_eq_left hcond]
        obtain ⟨hall, hn, hbits⟩ := concatVals_bits _ hc
        refine ⟨W, x.cast hcond.2.1, rfl, hall, by rw [← hcond.2.1, hn], fun i => by rw [BitVec.getLsbD_cast, hbits]⟩
      · exact absurd rfl h
    · exact absurd rfl h

/-! ## Bitwise operators over spliced lists -/

theorem bvs_map {w : Nat} : ∀ {l : List Val} {xs : List (BitVec w)}, Val.bvs w l = some xs → l = xs.map (Val.bv w) := by
  intro l
  induction l with
  | nil => intro xs h; simp [Val.bvs] at h; subst h; rfl
  | cons v rest ih =>
    intro xs h
    simp only [Val.bvs] at h
    split at h
    · rename_i y ys hy hys
      simp at h; subst h
      rw [ih hys]
      cases v with
      | bv w' z =>
        simp only [Val.asBv] at hy
        split at hy
        · rename_i hw; subst hw; simp at hy; subst hy; simp
        · simp at hy
      | bool _ => simp [Val.asBv] at hy
      | list _ _ => simp [Val.asBv] at hy
      | bad => simp [Val.asBv] at hy
    · simp at h

theorem bvs_of_map {w : Nat} (xs : List (BitVec w)) : Val.bvs w (xs.map (Val.bv w)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [Val.bvs, Val.asBv, ih]

/-- Data describing a bitwise pattern operator. -/
structure BitOp (op : RwOp) where
  F : (w : Nat) → List (BitVec w) → BitVec w
  f : Bool → Bool → Bool
  e : Bool
  node : ∀ w vs, Op.eval (fun _ => 0) (op.node w) vs = bvN w (F w) vs
  red : op.reducible = true
  one : ∀ w (x : BitVec w), F w [x] = x
  bits : ∀ w (xs : List (BitVec w)) i, i < w → (F w xs).getLsbD i = (xs.map (·.getLsbD i)).foldl f e
  assoc : ∀ x y z, f (f x y) z = f x (f y z)
  comm : ∀ x y, f x y = f y x
  id : ∀ x, f e x = x

theorem BitOp.eval {op : RwOp} (B : BitOp op) {l : List Val} {w : Nat} {x : BitVec w}
    (h : appVal op l = .bv w x) : ∃ xs, l = xs.map (Val.bv w) ∧ x = B.F w xs := by
  match l, h with
  | [], h => simp [appVal] at h
  | [v], h =>
    simp only [appVal, B.red, ↓reduceIte] at h
    subst h
    exact ⟨[x], rfl, (B.one w x).symm⟩
  | a :: b :: rest, h =>
    simp only [appVal, B.node] at h
    generalize RwOp.widthV op (a :: b :: rest) = W at h
    unfold bvN at h
    split at h
    · rename_i xs hxs
      split at h
      · injection h with hw hx
        subst hw
        exact ⟨xs, bvs_map hxs, (eq_of_heq hx).symm⟩
      · simp at h
    · simp at h

theorem BitOp.mem_ne_bad {op : RwOp} (B : BitOp op) {l : List Val} (h : appVal op l ≠ .bad) :
    ∀ v ∈ l, v ≠ .bad := by
  match l, h with
  | [], h => exact absurd rfl h
  | [v], h =>
    simp only [appVal, B.red, ↓reduceIte] at h
    intro u hu; simp at hu; subst hu; exact h
  | a :: b :: rest, h =>
    simp only [appVal, B.node] at h
    generalize RwOp.widthV op (a :: b :: rest) = W at h
    unfold bvN at h
    split at h
    · rename_i xs hxs
      intro u hu hb
      rw [bvs_map hxs] at hu
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hu
      simp at hb
    · exact absurd rfl h

theorem BitOp.isBv {op : RwOp} (B : BitOp op) {l : List Val} (h : appVal op l ≠ .bad)
    (hsingle : ∀ v, l = [v] → IsBv v) : ∃ w x, appVal op l = .bv w x := by
  match l, h, hsingle with
  | [], h, _ => exact absurd rfl h
  | [v], h, hsingle =>
    simp only [appVal, B.red, ↓reduceIte]
    exact hsingle v rfl
  | a :: b :: rest, h, _ =>
    simp only [appVal, B.node] at h ⊢
    generalize RwOp.widthV op (a :: b :: rest) = W at h ⊢
    unfold bvN at h ⊢
    split at h
    · rename_i xs hxs
      split at h
      · rename_i hc; rw [ite_eq_left hc]; exact ⟨_, _, rfl⟩
      · exact absurd rfl h
    · exact absurd rfl h

theorem foldl_mid {α : Type} {f : α → α → α} {e : α}
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) (hcomm : ∀ x y, f x y = f y x) (hid : ∀ x, f e x = x)
    (A B : List α) (c : α) : (A ++ c :: B).foldl f e = f ((A ++ B).foldl f e) c := by
  rw [foldl_append_op hassoc hcomm hid, foldl_cons_op hassoc hcomm hid, foldl_append_op hassoc hcomm hid]
  rw [← hassoc, hassoc (A.foldl f e) c, hcomm c, ← hassoc]

def bitAnd : BitOp .bvand where
  F w := List.foldl (· &&& ·) (BitVec.allOnes w)
  f := (· && ·)
  e := true
  node _ _ := rfl
  red := rfl
  one _ _ := by simp
  bits w xs i hi := by
    rw [foldl_bv_getLsbD (· &&& ·) (· && ·) (fun x y i _ => by simp) _ i hi, BitVec.getLsbD_allOnes]
    simp [hi]
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  id := by intro x; cases x <;> rfl

def bitOr : BitOp .bvor where
  F w := List.foldl (· ||| ·) 0
  f := (· || ·)
  e := false
  node _ _ := rfl
  red := rfl
  one _ _ := by simp
  bits w xs i hi := by
    rw [foldl_bv_getLsbD (· ||| ·) (· || ·) (fun x y i _ => by simp) _ i hi]
    simp
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  id := by intro x; cases x <;> rfl

/-! ## Extraction -/

theorem extract_val {hi lo : Nat} {v : Val} {n : Nat} {x : BitVec n}
    (h : bvExtractEval hi lo [v] = .bv n x) :
    ∃ (m : Nat) (y : BitVec m), v = .bv m y ∧ lo ≤ hi ∧ hi < m ∧ n = hi - lo + 1 ∧
      ∀ j, x.getLsbD j = (decide (j < hi - lo + 1) && y.getLsbD (lo + j)) := by
  cases v with
  | bv m y =>
    simp only [bvExtractEval] at h
    split at h
    · rename_i hc
      injection h with hn hx
      subst hn
      have := eq_of_heq hx; subst this
      exact ⟨m, y, rfl, hc.1, hc.2, rfl, fun j => BitVec.getLsbD_extractLsb⟩
    · simp at h
  | bool _ => simp [bvExtractEval] at h
  | list _ _ => simp [bvExtractEval] at h
  | bad => simp [bvExtractEval] at h

theorem ne_bad_bv {v : Val} (h : v ≠ .bad) (hv : ∀ b, v ≠ .bool b) (hl : ∀ e vs, v ≠ .list e vs) : IsBv v := by
  cases v with
  | bv w x => exact ⟨w, x, rfl⟩
  | bool b => exact absurd rfl (hv b)
  | list e vs => exact absurd rfl (hl e vs)
  | bad => exact absurd rfl h

theorem bvExtractEval_isBv {hi lo : Nat} {vs : List Val} (h : bvExtractEval hi lo vs ≠ .bad) :
    IsBv (bvExtractEval hi lo vs) := by
  apply ne_bad_bv h
  · intro b; unfold bvExtractEval; split <;> (try split) <;> simp
  · intro e l; exact bvExtractEval_ne_list hi lo vs e l

/-! ## Pulling a bitwise operator through a concatenation -/

theorem bv_inj_of_map {w w' : Nat} {xs : List (BitVec w)} {ys : List (BitVec w')}
    (h : xs.map (Val.bv w) = ys.map (Val.bv w')) (hne : xs ≠ []) : w = w' := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs' =>
    cases ys with
    | nil => simp at h
    | cons y ys' =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, _⟩ := h
      injection h1

theorem map_bv_inj {w : Nat} {xs ys : List (BitVec w)} (h : xs.map (Val.bv w) = ys.map (Val.bv w)) : xs = ys :=
  (List.map_inj_right (fun x y hxy => by simpa using hxy)).mp h

theorem BitOp.bit2 {op : RwOp} (B : BitOp op) {w : Nat} (x y : BitVec w) {i : Nat} (hi : i < w) :
    (B.F w [x, y]).getLsbD i = B.f (x.getLsbD i) (y.getLsbD i) := by
  rw [B.bits w [x, y] i hi]; simp [B.id]

theorem pullup_eq {op : RwOp} (B : BitOp op) {vs0 vs1 H L : List Val} (hH : H ≠ []) (hL : L ≠ [])
    {k5 k6 k7 : Nat} (hk6 : k6 = catW L)
    (hl : appVal op (vs0 ++ appVal .concat (H ++ L) :: vs1) ≠ .bad)
    (hr : appVal .concat [appVal op [bvExtractEval k5 k6 [appVal op (vs0 ++ vs1)], appVal .concat H],
                          appVal op [bvExtractEval k7 0 [appVal op (vs0 ++ vs1)], appVal .concat L]] ≠ .bad) :
    appVal op (vs0 ++ appVal .concat (H ++ L) :: vs1) =
    appVal .concat [appVal op [bvExtractEval k5 k6 [appVal op (vs0 ++ vs1)], appVal .concat H],
                    appVal op [bvExtractEval k7 0 [appVal op (vs0 ++ vs1)], appVal .concat L]] := by
  have hH1 : 0 < H.length := by cases H with | nil => exact absurd rfl hH | cons _ _ => simp
  have hL1 : 0 < L.length := by cases L with | nil => exact absurd rfl hL | cons _ _ => simp
  -- the concatenation argument
  have hc_ne : appVal .concat (H ++ L) ≠ .bad := B.mem_ne_bad hl _ (by simp)
  obtain ⟨Wc, cx, hc, hallHL, hWc, hcbits⟩ := appVal_concat_bits hc_ne (fun v hv => by
    have := congrArg List.length hv; simp at this; omega)
  -- the left-hand side
  rw [hc] at hl ⊢
  obtain ⟨w, a, hla⟩ := B.isBv hl (fun v hv => by
    have hm : Val.bv Wc cx ∈ vs0 ++ Val.bv Wc cx :: vs1 := by simp
    rw [hv] at hm; simp at hm; rw [← hm]; exact ⟨_, _, rfl⟩)
  obtain ⟨xs, hxs, ha⟩ := B.eval hla
  obtain ⟨xa, xr, rfl, hxa, hxr⟩ := List.map_eq_append_iff.mp hxs.symm
  obtain ⟨xc, xb, rfl, hxc, hxb⟩ := List.map_eq_cons_iff.mp hxr
  injection hxc with hw hxc'
  subst hw
  have hxc2 := eq_of_heq hxc'; subst hxc2
  subst hxa; subst hxb
  -- the right-hand side
  obtain ⟨n, r, hrr, hallAB, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨nA, a', hA⟩ := hallAB _ (by simp only [List.mem_cons]; exact Or.inl rfl)
  obtain ⟨nB, b', hB⟩ := hallAB _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨ys, hys, ha'⟩ := B.eval hA
  obtain ⟨zs, hzs, hb'⟩ := B.eval hB
  obtain ⟨e56, ys', rfl, he56, hys'⟩ := List.map_eq_cons_iff.mp hys.symm
  obtain ⟨hv, ys'', rfl, hhv, hys''⟩ := List.map_eq_cons_iff.mp hys'
  obtain ⟨e70, zs', rfl, he70, hzs'⟩ := List.map_eq_cons_iff.mp hzs.symm
  obtain ⟨lv, zs'', rfl, hlv, hzs''⟩ := List.map_eq_cons_iff.mp hzs'
  simp at hys'' hzs''; subst hys''; subst hzs''
  -- the two extractions
  obtain ⟨W1, mm, hm, h56a, h56b, hnA, he56bits⟩ := extract_val he56.symm
  obtain ⟨W2, mm', hm', _, h70b, hnB, he70bits⟩ := extract_val he70.symm
  rw [hm] at hm'
  injection hm' with hW hmm
  subst hW
  have := eq_of_heq hmm; subst this
  -- the inner operator over `vs0 ++ vs1`
  obtain ⟨us, hus, hmm⟩ := B.eval hm
  have hne : xa ++ xb ≠ [] := by
    intro h0
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h0
    simp [appVal] at hm
  have hW1 : w = W1 := by
    apply bv_inj_of_map (xs := xa ++ xb) (ys := us) _ hne
    rw [List.map_append]; exact hus
  subst hW1
  have hus' : us = xa ++ xb := (map_bv_inj (by rw [List.map_append]; exact hus.symm))
  subst hus'
  -- the two concatenation pieces
  obtain ⟨nH, hvx, hHv, _, hnH, hHbits⟩ := appVal_concat_bits (l := H) (by rw [← hhv]; simp)
    (fun v hv => hallHL v (by rw [hv]; simp))
  obtain ⟨nL, lvx, hLv, _, hnL, hLbits⟩ := appVal_concat_bits (l := L) (by rw [← hlv]; simp)
    (fun v hv => hallHL v (by rw [hv]; simp))
  rw [hHv] at hhv; rw [hLv] at hlv
  injection hhv with h1 h2; subst h1; have := eq_of_heq h2; subst this
  injection hlv with h1 h2; subst h1; have := eq_of_heq h2; subst this
  -- widths
  rw [hA, hB] at hn hrbits
  subst hnH; subst hnL
  rw [hla, hrr]
  have hWc' : w = catW H + catW L := by rw [hWc, catW_append]
  have hn' : n = catW H + catW L := by rw [hn]; simp only [catW]; omega
  apply val_ext (by rw [hn']; exact hWc')
  intro i hi
  rw [ha, B.bits _ _ i hi, List.map_append, List.map_cons, foldl_mid B.assoc B.comm B.id,
    ← List.map_append, ← B.bits _ _ i hi, ← hmm, hrbits i, hcbits i, catBit_append]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte,
    Nat.sub_zero]
  by_cases hiL : i < catW L
  · rw [ite_eq_left hiL, ite_eq_left hiL, hb', B.bit2 _ _ hiL, he70bits, hLbits, Nat.zero_add,
      decide_eq_true (show i < k7 - 0 + 1 by omega), Bool.true_and]
  · rw [ite_eq_right hiL, ite_eq_right hiL]
    have hj : i - catW L < catW H := by omega
    rw [ha', B.bit2 _ _ hj, he56bits, hHbits,
      decide_eq_true (show i - catW L < k5 - k6 + 1 by omega), Bool.true_and,
      show k6 + (i - catW L) = i by omega]

/-! ## Splicing pattern results -/

theorem impliesEval_ne_list (vs : List Val) (e : Bool) (l : List Val) : impliesEval vs ≠ .list e l := by
  unfold impliesEval; split <;> simp
theorem bvUn_ne_list (w : Nat) (f : BitVec w → BitVec w) (vs : List Val) (e : Bool) (l : List Val) :
    bvUn w f vs ≠ .list e l := by
  unfold bvUn; split <;> (try split) <;> (try split) <;> simp
theorem boolIteEval_ne_list (vs : List Val) (e : Bool) (l : List Val) : boolIteEval vs ≠ .list e l := by
  unfold boolIteEval; split <;> simp

theorem opEval_ne_list (op : RwOp) (w : Nat) (vs : List Val) (e : Bool) (l : List Val) :
    Op.eval (fun _ => 0) (op.node w) vs ≠ .list e l := by
  cases op <;> simp only [RwOp.node, Op.eval]
  all_goals first
    | exact boolNotEval_ne_list _ _ _
    | exact eqEval_ne_list _ _ _ _
    | exact impliesEval_ne_list _ _ _
    | exact boolN_ne_list _ _ _ _
    | exact bvCmp_ne_list _ _ _ _
    | exact bvN_ne_list _ _ _ _ _
    | exact bvBin_ne_list _ _ _ _ _
    | exact bvUn_ne_list _ _ _ _ _
    | exact bvConcatEval_ne_list _ _ _ _
    | exact bvSizeEval_ne_list _ _ _ _

theorem appVal_ne_list {op : RwOp} {l : List Val}
    (h : op.reducible = true → ∀ v, l = [v] → ∀ e vs, v ≠ .list e vs) : ∀ e vs, appVal op l ≠ .list e vs := by
  intro e vs
  unfold appVal
  split
  · simp
  · rename_i v
    split
    · rename_i hred; exact h hred v rfl e vs
    · exact opEval_ne_list op _ _ e vs
  · exact opEval_ne_list op _ _ e vs

theorem spliceVal_appVal {op : RwOp} {l : List Val}
    (h : op.reducible = true → ∀ v, l = [v] → ∀ e vs, v ≠ .list e vs) : spliceVal (appVal op l) = [appVal op l] :=
  spliceVal_of_ne (appVal_ne_list h)

theorem spliceVal_appVal_long {op : RwOp} {l : List Val} (h : 2 ≤ l.length) :
    spliceVal (appVal op l) = [appVal op l] :=
  spliceVal_appVal (fun _ v hv => by rw [hv] at h; simp at h)

theorem spliceVal_appVal_nonred {op : RwOp} (h : op.reducible = false) (l : List Val) :
    spliceVal (appVal op l) = [appVal op l] :=
  spliceVal_appVal (fun hr => by rw [h] at hr; simp at hr)

theorem spliceVal_appVal_snoc {op : RwOp} (l : List Val) {w : Nat} (x : BitVec w) :
    spliceVal (appVal op (l ++ [.bv w x])) = [appVal op (l ++ [.bv w x])] :=
  spliceVal_appVal (fun _ v hv => by
    cases l with
    | nil => simp at hv; subst hv; simp
    | cons a l' => have := congrArg List.length hv; simp at this)

theorem spliceVal_appVal_cons {op : RwOp} (l : List Val) {w : Nat} (x : BitVec w) :
    spliceVal (appVal op (.bv w x :: l)) = [appVal op (.bv w x :: l)] :=
  spliceVal_appVal (fun _ v hv => by
    cases l with
    | nil => simp at hv; subst hv; simp
    | cons a l' => simp at hv)

theorem spliceVal_appVal_two {op : RwOp} (a b : Val) (l : List Val) :
    spliceVal (appVal op (a :: b :: l)) = [appVal op (a :: b :: l)] :=
  spliceVal_appVal_long (by simp)

theorem spliceVal_appVal_append2 {op : RwOp} (l : List Val) (a b : Val) :
    spliceVal (appVal op (l ++ [a, b])) = [appVal op (l ++ [a, b])] :=
  spliceVal_appVal_long (by simp)

theorem appVal_single {op : RwOp} (h : op.reducible = true) (v : Val) : appVal op [v] = v := by
  simp [appVal, h]

theorem appVal_concat_single (v : Val) : appVal .concat [v] = v := appVal_single rfl v

/-- Structural unfolding of patterns, keeping operator applications folded. -/
syntax "rw_pat" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rw_pat $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.not', RwExpr.ult', RwExpr.ule',
      RwExpr.slt', RwExpr.sle', RwExpr.sge', RwExpr.conj', RwExpr.bvsub', RwExpr.bvadd', RwExpr.bvmul',
      RwExpr.bvshl', RwExpr.bvashr', RwExpr.bvand', RwExpr.bvor', RwExpr.concat', RwExpr.bvsize', RwExpr.l0,
      RwExpr.l1, RwExpr.V, RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal_bv, spliceVal_bool, spliceVal_list,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc,
      l0_val, l1_val, BitVec.toNat_ofNat, Nat.zero_mod, spliceVal_bvExtractEval, spliceVal_bvExtEval,
      spliceVal_bvRepeatEval, spliceVal_bvValEval, spliceVal_appVal_snoc, spliceVal_appVal_cons,
      spliceVal_appVal_two, spliceVal_appVal_append2,
      spliceVal_appVal_nonred (rfl : RwOp.reducible .eq = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsize = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsub = false),
      appVal_concat_single] $[$loc]?)

theorem toNat_of_bvsize {w : Nat} {x : BitVec w} {k : BitVec 32}
    (h : appVal .eq [.bv 32 k, appVal .bvsize [.bv w x]] = .bool true) : k.toNat = w ∧ w < 2 ^ 32 := by
  have he := eq_true h
  rw [bvsize_val] at he
  split at he
  · rename_i hw
    injection he with _ hk
    rw [hk, toNat_ofNat32 hw]; exact ⟨rfl, hw⟩
  · simp at he

theorem bvsize_eq_true {v : Val} {k : BitVec 32} (h : appVal .eq [.bv 32 k, appVal .bvsize [v]] = .bool true) :
    ∃ n y, v = .bv n y ∧ k.toNat = n ∧ n < 2 ^ 32 := by
  have he := eq_true h
  cases v with
  | bv n y =>
    rw [bvsize_val] at he
    split at he
    · rename_i hn
      injection he with _ hk
      exact ⟨n, y, rfl, by rw [hk, toNat_ofNat32 hn], hn⟩
    · simp at he
  | bool _ => simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvSizeEval] at he
  | list _ _ => simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvSizeEval] at he
  | bad => simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvSizeEval] at he

/-! ## The four concatenation pull-ups -/

theorem sound_BV_AND_CONCAT_PULLUP : ∀ r, rwTable 113 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
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
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  have hk6 := (toNat_of_bvsize (conjN_true hc _ (by apply List.mem_cons_self))).1
  have key := pullup_eq bitAnd (vs0 := vs0) (vs1 := vs1) (H := vs4 ++ [.bv w3 x3]) (L := [.bv w2 x2])
    (k5 := k5.toNat) (k6 := k6.toNat) (k7 := k7.toNat) (by simp) (by simp) (by simp [catW, hk6])
  simp only [List.append_assoc, List.cons_append, appVal_concat_single] at key
  exact key hl hr

theorem sound_BV_OR_CONCAT_PULLUP : ∀ r, rwTable 114 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
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
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  have hk6 := (toNat_of_bvsize (conjN_true hc _ (by apply List.mem_cons_self))).1
  have key := pullup_eq bitOr (vs0 := vs0) (vs1 := vs1) (H := vs4 ++ [.bv w3 x3]) (L := [.bv w2 x2])
    (k5 := k5.toNat) (k6 := k6.toNat) (k7 := k7.toNat) (by simp) (by simp) (by simp [catW, hk6])
  simp only [List.append_assoc, List.cons_append, appVal_concat_single] at key
  exact key hl hr

theorem sound_BV_AND_CONCAT_PULLUP2 : ∀ r, rwTable 116 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
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
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  obtain ⟨n, y, hcv, hk6, _⟩ := bvsize_eq_true (conjN_true hc _ (by apply List.mem_cons_self))
  obtain ⟨n', y', hcv', _, hn', _⟩ := appVal_concat_bits (l := .bv w2 x2 :: vs4) (by rw [hcv]; simp)
    (fun v hv => by cases vs4 with
      | nil => simp at hv; subst hv; exact ⟨_, _, rfl⟩
      | cons _ _ => simp at hv)
  rw [hcv] at hcv'
  injection hcv' with hnn _
  have key := pullup_eq bitAnd (vs0 := vs0) (vs1 := vs1) (H := [.bv w3 x3]) (L := .bv w2 x2 :: vs4)
    (k5 := k5.toNat) (k6 := k6.toNat) (k7 := k7.toNat) (by simp) (by simp) (by rw [hk6, hnn, hn'])
  simp only [List.cons_append, appVal_concat_single] at key
  exact key hl hr

theorem sound_BV_OR_CONCAT_PULLUP2 : ∀ r, rwTable 117 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
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
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, h7] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  obtain ⟨n, y, hcv, hk6, _⟩ := bvsize_eq_true (conjN_true hc _ (by apply List.mem_cons_self))
  obtain ⟨n', y', hcv', _, hn', _⟩ := appVal_concat_bits (l := .bv w2 x2 :: vs4) (by rw [hcv]; simp)
    (fun v hv => by cases vs4 with
      | nil => simp at hv; subst hv; exact ⟨_, _, rfl⟩
      | cons _ _ => simp at hv)
  rw [hcv] at hcv'
  injection hcv' with hnn _
  have key := pullup_eq bitOr (vs0 := vs0) (vs1 := vs1) (H := [.bv w3 x3]) (L := .bv w2 x2 :: vs4)
    (k5 := k5.toNat) (k6 := k6.toNat) (k7 := k7.toNat) (by simp) (by simp) (by rw [hk6, hnn, hn'])
  simp only [List.cons_append, appVal_concat_single] at key
  exact key hl hr

/-! ## 32-bit size arithmetic in conditions -/

theorem appVal_bvsub32 (a b : BitVec 32) : appVal .bvsub [.bv 32 a, .bv 32 b] = .bv 32 (a - b) := by
  simp [appVal, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvBin]
theorem appVal_bvadd32 (a b : BitVec 32) : appVal .bvadd [.bv 32 a, .bv 32 b] = .bv 32 (a + b) := by
  simp [appVal, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvN,
    Val.bvs, Val.asBv]
theorem appVal_bvmul32 (a b : BitVec 32) : appVal .bvmul [.bv 32 a, .bv 32 b] = .bv 32 (a * b) := by
  simp [appVal, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvN,
    Val.bvs, Val.asBv]
theorem appVal_bvshl32 (a b : BitVec 32) : appVal .bvshl [.bv 32 a, .bv 32 b] = .bv 32 (a <<< b) := by
  simp [appVal, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvBin]
theorem appVal_bvlshr32 (a b : BitVec 32) : appVal .bvlshr [.bv 32 a, .bv 32 b] = .bv 32 (a >>> b) := by
  simp [appVal, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvBin]
theorem appVal_slt32 (a b : BitVec 32) : appVal .slt [.bv 32 a, .bv 32 b] = .bool (a.slt b) := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]
theorem appVal_sle32 (a b : BitVec 32) : appVal .sle [.bv 32 a, .bv 32 b] = .bool (a.sle b) := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]
theorem appVal_sge32 (a b : BitVec 32) : appVal .sge [.bv 32 a, .bv 32 b] = .bool (b.sle a) := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]
theorem appVal_ule32 (a b : BitVec 32) : appVal .ule [.bv 32 a, .bv 32 b] = .bool (a.ule b) := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]
theorem appVal_bvsize_small {w : Nat} (x : BitVec w) (hw : w ≤ 255) :
    appVal .bvsize [.bv w x] = .bv 32 (BitVec.ofNat 32 w) := by
  rw [bvsize_val, ite_eq_left (Nat.lt_of_le_of_lt hw (by decide))]

theorem eq_bv32 {a b : BitVec 32} (h : appVal .eq [.bv 32 a, .bv 32 b] = .bool true) : a = b := by
  have := eq_true h; injection this

theorem conj_all2 {a b : Val} (h : appVal .conj [a, b] = .bool true) : a = .bool true ∧ b = .bool true :=
  ⟨conjN_true h a (by simp), conjN_true h b (by simp)⟩
theorem conj_all3 {a b c : Val} (h : appVal .conj [a, b, c] = .bool true) :
    a = .bool true ∧ b = .bool true ∧ c = .bool true :=
  ⟨conjN_true h a (by simp), conjN_true h b (by simp), conjN_true h c (by simp)⟩
theorem conj_all4 {a b c d : Val} (h : appVal .conj [a, b, c, d] = .bool true) :
    a = .bool true ∧ b = .bool true ∧ c = .bool true ∧ d = .bool true :=
  ⟨conjN_true h a (by simp), conjN_true h b (by simp), conjN_true h c (by simp), conjN_true h d (by simp)⟩

/-- Small signed comparisons are unsigned. -/
theorem sle_true_of_small {a b : BitVec 32} (ha : a.toNat < 2 ^ 31) (h : a.sle b = true) :
    a.toNat ≤ b.toNat ∧ b.toNat < 2 ^ 31 := by
  have hma : a.msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  cases hmb : b.msb with
  | false =>
    simp only [BitVec.sle, BitVec.toInt_eq_msb_cond, hma, hmb, Bool.false_eq_true, ↓reduceIte] at h
    simp at h
    have hb' := hmb
    rw [BitVec.msb_eq_decide] at hb'; simp at hb'
    exact ⟨h, by rw [two31]; omega⟩
  | true =>
    simp only [BitVec.sle, BitVec.toInt_eq_msb_cond, hma, hmb, Bool.false_eq_true, ↓reduceIte] at h
    simp at h
    rw [two31] at ha
    omega

theorem slt_true_of_small {a b : BitVec 32} (hb : b.toNat < 2 ^ 31) (ha : a.toNat < 2 ^ 31) (h : a.slt b = true) :
    a.toNat < b.toNat := by
  rw [slt_small ha hb] at h; simpa using h

theorem toNat_sub32 {a b : BitVec 32} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)]

theorem toNat_ofNat_small {w : Nat} (hw : w ≤ 255) : (BitVec.ofNat 32 w).toNat = w :=
  toNat_ofNat32 (Nat.lt_of_le_of_lt hw (by decide))

/-! ## Extraction congruence -/

theorem extract_congr' {hi lo hi' lo' n m : Nat} {x : BitVec n} {y : BitVec m}
    (hn : hi < n) (hm : hi' < m) (hlo : lo ≤ hi) (hlo' : lo' ≤ hi') (hw : hi - lo = hi' - lo')
    (hb : ∀ j, j ≤ hi - lo → x.getLsbD (lo + j) = y.getLsbD (lo' + j)) :
    bvExtractEval hi lo [.bv n x] = bvExtractEval hi' lo' [.bv m y] := by
  simp only [bvExtractEval]
  rw [ite_eq_left ⟨hlo, hn⟩, ite_eq_left ⟨hlo', hm⟩]
  apply val_ext (by omega)
  intro i hi_
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_extractLsb, decide_eq_true hi_,
    decide_eq_true (show i < hi' - lo' + 1 by omega), Bool.true_and, Bool.true_and]
  exact hb i (by omega)

theorem catW_snoc {w : Nat} (l : List Val) (x : BitVec w) : catW (l ++ [.bv w x]) = catW l + w := by
  rw [catW_append]; simp [catW]

theorem catBit_snoc {w : Nat} (l : List Val) (x : BitVec w) (i : Nat) :
    catBit (l ++ [.bv w x]) i = if i < w then x.getLsbD i else catBit l (i - w) := by
  rw [catBit_append]; simp [catW, catBit]

/-! ## Extraction from concatenations -/

theorem concat_long_isBv {l : List Val} {n : Nat} {x : BitVec n} (h2 : 2 ≤ l.length)
    (h : appVal .concat l = .bv n x) : n = catW l ∧ ∀ i, x.getLsbD i = catBit l i := by
  obtain ⟨n', x', hv, _, hn, hb⟩ := appVal_concat_bits (l := l) (by rw [h]; simp)
    (fun v hv => by rw [hv] at h2; simp at h2)
  rw [h] at hv; injection hv with h1 h2'; subst h1; have := eq_of_heq h2'; subst this
  exact ⟨hn, hb⟩

theorem concat_snoc_isBv {l : List Val} {w : Nat} {y : BitVec w} {n : Nat} {x : BitVec n}
    (h : appVal .concat (l ++ [.bv w y]) = .bv n x) :
    n = catW (l ++ [.bv w y]) ∧ ∀ i, x.getLsbD i = catBit (l ++ [.bv w y]) i := by
  obtain ⟨n', x', hv, _, hn, hb⟩ := appVal_concat_bits (l := l ++ [.bv w y]) (by rw [h]; simp)
    (fun v hv => by
      cases l with
      | nil => simp at hv; subst hv; exact ⟨_, _, rfl⟩
      | cons _ _ => have := congrArg List.length hv; simp at this)
  rw [h] at hv; injection hv with h1 h2'; subst h1; have := eq_of_heq h2'; subst this
  exact ⟨hn, hb⟩

theorem extract_of_ne_bad {hi lo : Nat} {v : Val} (h : bvExtractEval hi lo [v] ≠ .bad) :
    ∃ (m : Nat) (y : BitVec m), v = .bv m y ∧ lo ≤ hi ∧ hi < m ∧
      bvExtractEval hi lo [v] = .bv (hi - lo + 1) (BitVec.extractLsb hi lo y) := by
  obtain ⟨n, x, hx⟩ := bvExtractEval_isBv h
  obtain ⟨m, y, rfl, hlo, hhi, hn, _⟩ := extract_val hx
  refine ⟨m, y, rfl, hlo, hhi, ?_⟩
  simp [bvExtractEval, hlo, hhi]

theorem sound_BV_EXTRACT_CONCAT_1 : ∀ r, rwTable 54 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv _ hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  rw_pat at hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hl hr ⊢
  rw_pat at hl hr ⊢
  obtain ⟨nC, cx, hC, hlo, hhi, _⟩ := extract_of_ne_bad hl
  obtain ⟨m0, y0, hy0, _, hhi0, _⟩ := extract_of_ne_bad hr
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  obtain ⟨hnC, hcbits⟩ := concat_long_isBv (by simp) hC
  rw [hC]
  apply extract_congr' hhi hhi0 hlo hlo rfl
  intro j hj
  rw [hcbits, show vs1 ++ [Val.bv w2 x2, Val.bv w0 x0] = (vs1 ++ [Val.bv w2 x2]) ++ [Val.bv w0 x0] by simp,
    catBit_snoc, ite_eq_left (by omega)]

theorem sound_BV_EXTRACT_CONCAT_2 : ∀ r, rwTable 55 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨vs1, h1⟩ := henv 1 .bvqs rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_slt32, appVal_sge32] at hc
  obtain ⟨_, hsge, he5, he6⟩ := conj_all4 hc
  simp only [Val.bool.injEq] at hsge
  have hk5 := eq_bv32 he5
  have hk6 := eq_bv32 he6
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  obtain ⟨hw0k4, _⟩ := sle_true_of_small (by rw [hw0', two31]; omega) hsge
  rw [hw0'] at hw0k4
  -- left-hand side
  obtain ⟨nC, cx, hC, hlo, hhi, hlv⟩ := extract_of_ne_bad hl
  obtain ⟨hnC, hcbits⟩ := concat_long_isBv (by simp) hC
  -- right-hand side
  obtain ⟨n, rv, hrv, hall, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨n1, e1, hE1⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨n2, e2, hE2⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨nD, dx, hD, _, hk5D, hE1v⟩ := extract_of_ne_bad (by rw [hE1]; simp : bvExtractEval k5.toNat 0 _ ≠ .bad)
  obtain ⟨m0, y0, hy0, hk36, hk6w, hE2v⟩ := extract_of_ne_bad (by rw [hE2]; simp : bvExtractEval k6.toNat k3.toNat _ ≠ .bad)
  injection hy0 with e1' e2'; subst e1'; have := eq_of_heq e2'; subst this
  obtain ⟨hnD, hdbits⟩ := concat_snoc_isBv hD
  have hk5n : k5.toNat = k4.toNat - w0 := by rw [hk5, toNat_sub32 (by rw [hw0']; exact hw0k4), hw0']
  have hk6n : k6.toNat = w0 - 1 := by rw [hk6, toNat_sub_one32 (by omega) (by omega)]
  rw [hE1v] at hE1; rw [hE2v] at hE2
  injection hE1 with hn1 he1; subst hn1; have := eq_of_heq he1; subst this
  injection hE2 with hn2 he2; subst hn2; have := eq_of_heq he2; subst this
  rw [hE1v, hE2v] at hn hrbits
  rw [hlv, hrv]
  apply val_ext (by rw [hn]; simp only [catW]; omega)
  intro i hi
  rw [BitVec.getLsbD_extractLsb, decide_eq_true hi, Bool.true_and, hcbits, hrbits,
    show vs1 ++ [Val.bv w2 x2, Val.bv w0 x0] = (vs1 ++ [Val.bv w2 x2]) ++ [Val.bv w0 x0] by simp, catBit_snoc]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  by_cases hlt : k3.toNat + i < w0
  · rw [ite_eq_left hlt, ite_eq_left (by omega), BitVec.getLsbD_extractLsb, decide_eq_true (by omega), Bool.true_and]
  · rw [ite_eq_right hlt, ite_eq_right (by omega), BitVec.getLsbD_extractLsb, decide_eq_true (by omega), Bool.true_and,
      Nat.zero_add, ← hdbits, show i - (k6.toNat - k3.toNat + 1) = k3.toNat + i - w0 by omega]

theorem sound_BV_EXTRACT_CONCAT_3 : ∀ r, rwTable 56 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨w1, x1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_sge32] at hc
  obtain ⟨hsge, he5, he6⟩ := conj_all3 hc
  simp only [Val.bool.injEq] at hsge
  have hk5 := eq_bv32 he5
  have hk6 := eq_bv32 he6
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  obtain ⟨hw0k3, _⟩ := sle_true_of_small (by rw [hw0', two31]; omega) hsge
  rw [hw0'] at hw0k3
  obtain ⟨nC, cx, hC, hlo, hhi, _⟩ := extract_of_ne_bad hl
  obtain ⟨nD, dx, hD, hlo', hhi', _⟩ := extract_of_ne_bad hr
  obtain ⟨hnC, hcbits⟩ := concat_long_isBv (by simp) hC
  obtain ⟨hnD, hdbits⟩ := concat_snoc_isBv hD
  have hk5n : k5.toNat = k4.toNat - w0 := by rw [hk5, toNat_sub32 (by rw [hw0']; omega), hw0']
  have hk6n : k6.toNat = k3.toNat - w0 := by rw [hk6, toNat_sub32 (by rw [hw0']; omega), hw0']
  rw [hC, hD]
  apply extract_congr' hhi hhi' hlo hlo' (by omega)
  intro j hj
  rw [hcbits, hdbits, show vs2 ++ [Val.bv w1 x1, Val.bv w0 x0] = (vs2 ++ [Val.bv w1 x1]) ++ [Val.bv w0 x0] by simp,
    catBit_snoc, ite_eq_right (by omega), show k3.toNat + j - w0 = k6.toNat + j by omega]

theorem sound_BV_EXTRACT_CONCAT_4 : ∀ r, rwTable 57 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv _ hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨w1, x1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨vs2, h2⟩ := henv 2 .bvqs rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  rw_pat at hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hl hr ⊢
  rw_pat at hl hr ⊢
  obtain ⟨nC, cx, hC, hlo, hhi, _⟩ := extract_of_ne_bad hl
  obtain ⟨nD, dx, hD, hlo', hhi', _⟩ := extract_of_ne_bad hr
  obtain ⟨hnC, hcbits⟩ := concat_long_isBv (by simp) hC
  obtain ⟨hnD, hdbits⟩ := concat_snoc_isBv hD
  rw [hC, hD]
  apply extract_congr' hhi hhi' hlo hlo' rfl
  intro j hj
  rw [hcbits, hdbits, catBit_bv_cons, ite_eq_left (by rw [← hnD]; omega)]

/-! ## Literals, shifts, comparisons -/

theorem lit_cases (w v : Nat) : bvValEval w v [] = .bad ∨
    (w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w ∧ bvValEval w v [] = .bv w (BitVec.ofNat w v)) := by
  unfold bvValEval
  by_cases h : w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w
  · right; exact ⟨h.1, h.2.1, h.2.2, by rw [ite_eq_left h]⟩
  · left; rw [ite_eq_right h]

theorem appVal_bin2 {op : RwOp} {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal op [.bv w x, .bv m y] = Op.eval (fun _ => 0) (op.node (op.width [.bv w, .bv m])) [.bv w x, .bv m y] := by
  simp [appVal, RwOp.widthV, Val.tys, Val.ty]

theorem shl_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvshl [.bv w x, .bv m y] = if h : m = w then (if w ≠ 0 then .bv w (x <<< (y.cast h)) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem ashr_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvashr [.bv w x, .bv m y] =
      if h : m = w then (if w ≠ 0 then .bv w (x.sshiftRight (y.cast h).toNat) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem ult_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .ult [.bv w x, .bv m y] = if h : m = w then .bool (x.ult (y.cast h)) else .bad := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]

theorem appVal_concat_bad_mem {l : List Val} (h : .bad ∈ l) (h2 : 2 ≤ l.length) : appVal .concat l = .bad := by
  by_cases hne : appVal .concat l = .bad
  · exact hne
  · exfalso
    obtain ⟨_, _, _, hall, _⟩ := appVal_concat_bits hne (fun v hv => by rw [hv] at h2; simp at h2)
    obtain ⟨_, _, hb⟩ := hall _ h
    simp at hb

theorem shl_ofNat {w k : Nat} (hk : k < 2 ^ w) (x : BitVec w) (i : Nat) (hi : i < w) :
    (x <<< BitVec.ofNat w k).getLsbD i = (!decide (i < k) && x.getLsbD (i - k)) := by
  rw [BitVec.getLsbD_shiftLeft', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, decide_eq_true hi, Bool.true_and]

theorem sound_BV_SHL_BY_CONST_1 : ∀ r, rwTable 105 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_bvadd32, appVal_slt32] at hc
  obtain ⟨hslt, he3⟩ := conj_all2 hc
  simp only [Val.bool.injEq] at hslt
  have hk3 := eq_bv32 he3
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  -- the shift amount
  rcases lit_cases k2.toNat k1.toNat with hL | ⟨hk2, hk264, hk1lt, hL⟩
  · rw [hL] at hl; simp [appVal, RwOp.widthV, Val.tys, Val.ty, RwOp.node, Op.eval, bvBin] at hl
  rw [hL] at hl ⊢
  have hkw : k2.toNat = w0 := by
    by_cases hkw : k2.toNat = w0
    · exact hkw
    · rw [shl_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [shl_eval, dite_eq_left hkw, ite_eq_left (by omega)] at hl ⊢
  -- the right-hand side
  obtain ⟨n, rv, hrv, hall, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨nE, e, hE⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨nZ, z, hZ⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨w0, y0, hy0, _, hk3w, hEv⟩ := extract_of_ne_bad (by rw [hE]; simp : bvExtractEval k3.toNat 0 _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases k1.toNat 0 with hZ' | ⟨hk10, hk164, _, hZv⟩
  · rw [hZ'] at hZ; simp at hZ
  rw [hEv] at hE; rw [hZv] at hZ
  injection hE with hnE he; subst hnE; have := eq_of_heq he; subst this
  injection hZ with hnZ hz; subst hnZ; have := eq_of_heq hz; subst this
  rw [hEv, hZv] at hn hrbits
  -- arithmetic
  have hk1w : k1.toNat < w0 := by
    rw [slt_small (by omega) (by rw [hw0', two31]; omega), hw0'] at hslt; simpa using hslt
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk3n : k3.toNat = w0 - (1 + k1.toNat) := by
    rw [hk3, toNat_sub32 (by rw [toNat_add32 _ _ (by rw [two32]; omega), hw0']; simp; omega),
      toNat_add32 _ _ (by rw [two32]; omega), hw0']
    simp
  rw [hrv]
  apply val_ext (by rw [hn]; simp only [catW]; omega)
  intro i hi
  rw [hrbits]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  have hcast : (BitVec.ofNat k2.toNat k1.toNat).cast hkw = BitVec.ofNat w0 k1.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hcast, shl_ofNat (by rw [← hkw]; exact hk1lt) _ _ hi]
  by_cases hik : i < k1.toNat
  · rw [ite_eq_left hik, decide_eq_true hik]; simp
  · rw [ite_eq_right hik, decide_eq_false hik, BitVec.getLsbD_extractLsb, decide_eq_true (by omega)]
    simp

theorem repeat_bits {w k m n : Nat} {x : BitVec m} {y : BitVec n} (h : bvRepeatEval w k [.bv m x] = .bv n y) :
    n = m * k ∧ ∀ i, y.getLsbD i = (decide (i < m * k) && x.getLsbD (i % m)) := by
  simp only [bvRepeatEval] at h
  split at h
  · rename_i hc
    injection h with hn hy
    subst hn
    refine ⟨hc.2.symm, fun i => ?_⟩
    rw [← eq_of_heq hy, BitVec.getLsbD_cast, BitVec.getLsbD_replicate]
  · simp at h

theorem extract_bad {hi lo m : Nat} {y : BitVec m} (h : ¬ (lo ≤ hi ∧ hi < m)) : bvExtractEval hi lo [.bv m y] = .bad := by
  simp [bvExtractEval, h]

theorem sound_BV_ASHR_BY_CONST_1 : ∀ r, rwTable 111 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_slt32] at hc
  obtain ⟨_, he3⟩ := conj_all2 hc
  have hk3 := eq_bv32 he3
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  -- the shift amount
  rcases lit_cases k2.toNat k1.toNat with hL | ⟨hk2, hk264, hk1lt, hL⟩
  · rw [hL] at hl; simp [appVal, RwOp.widthV, Val.tys, Val.ty, RwOp.node, Op.eval, bvBin] at hl
  rw [hL] at hl ⊢
  have hkw : k2.toNat = w0 := by
    by_cases hkw : k2.toNat = w0
    · exact hkw
    · rw [ashr_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [ashr_eval, dite_eq_left hkw, ite_eq_left (by omega)] at hl ⊢
  -- the sign-bit extraction
  have hk3w : k3.toNat < w0 := by
    by_cases hk3w : k3.toNat < w0
    · exact hk3w
    · rw [extract_bad (by omega)] at hr
      simp only [spliceVal_bad] at hr
      exact absurd (appVal_concat_bad_mem (by simp) (by simp)) hr
  have hE33 : bvExtractEval k3.toNat k3.toNat [.bv w0 x0] = .bv (k3.toNat - k3.toNat + 1)
      (BitVec.extractLsb k3.toNat k3.toNat x0) := by simp [bvExtractEval, hk3w]
  rw [hE33] at hr ⊢
  simp only [spliceVal_bvRepeatEval, List.singleton_append] at hr ⊢
  obtain ⟨n, rv, hrv, hall, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨nR, rr, hR⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨nE, ev, hE⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨hnR, hrrbits⟩ := repeat_bits hR
  obtain ⟨m0, y0, hy0, hk13, _, hEv⟩ := extract_of_ne_bad (by rw [hE]; simp : bvExtractEval k3.toNat k1.toNat _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hEv] at hE
  injection hE with hnE he; subst hnE; have := eq_of_heq he; subst this
  rw [hR, hEv] at hn hrbits
  have hk3n : k3.toNat = w0 - 1 := by rw [hk3, toNat_sub_one32 (by omega) (by omega)]
  simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul] at hnR hrrbits
  rw [hrv]
  apply val_ext (by rw [hn]; simp only [catW]; omega)
  intro i hi
  have hcast : ((BitVec.ofNat k2.toNat k1.toNat).cast hkw).toNat = k1.toNat := by
    simp only [BitVec.toNat_cast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1lt]
  rw [hcast, BitVec.getLsbD_sshiftRight, hrbits]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  rw [decide_eq_false (by omega), Bool.not_false, Bool.true_and]
  by_cases hik : k1.toNat + i < w0
  · rw [ite_eq_left hik, ite_eq_left (by omega), BitVec.getLsbD_extractLsb, decide_eq_true (by omega), Bool.true_and]
  · rw [ite_eq_right hik, ite_eq_right (by omega), hrrbits, BitVec.getLsbD_extractLsb, BitVec.msb_eq_getLsbD_last]
    simp only [Nat.mod_one, Nat.sub_self, Nat.zero_add, Nat.add_zero]
    rw [decide_eq_true (by omega), decide_eq_true (by omega), hk3n]
    simp

theorem repeat_isBv {w k : Nat} {vs : List Val} (h : bvRepeatEval w k vs ≠ .bad) :
    ∃ n y, bvRepeatEval w k vs = .bv n y := by
  unfold bvRepeatEval at h ⊢
  split at h
  · split at h
    · exact ⟨_, _, by rw [dite_eq_left (by assumption)]⟩
    · exact absurd rfl h
  · exact absurd rfl h

theorem sound_BV_EXTRACT_SIGN_EXTEND_3 : ∀ r, rwTable 64 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_bvadd32, appVal_sge32] at hc
  obtain ⟨hsge, he4, he5⟩ := conj_all3 hc
  simp only [Val.bool.injEq] at hsge
  have hk4 := eq_bv32 he4
  have hk5 := eq_bv32 he5
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  obtain ⟨hw0k1, _⟩ := sle_true_of_small (by rw [hw0', two31]; omega) hsge
  rw [hw0'] at hw0k1
  -- the sign extension
  have hS : bvExtEval true (w0 + k3.toNat) k3.toNat [.bv w0 x0] =
      .bv (w0 + k3.toNat) (x0.signExtend (w0 + k3.toNat)) := by
    by_cases hz : w0 + k3.toNat = 0
    · exfalso; apply hl; simp [bvExtEval, hz, bvExtractEval]
    · simp only [bvExtEval]; rw [ite_eq_left ⟨hz, trivial⟩]; rfl
  rw [hS] at hl ⊢
  obtain ⟨m1, y1, hy1, hk12, hk2w, hlv⟩ := extract_of_ne_bad hl
  injection hy1 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  -- the sign bit
  have hk5w : k5.toNat < w0 := by
    by_cases hk5w : k5.toNat < w0
    · exact hk5w
    · rw [extract_bad (by omega)] at hr; exact absurd rfl hr
  have hE55 : bvExtractEval k5.toNat k5.toNat [.bv w0 x0] = .bv (k5.toNat - k5.toNat + 1)
      (BitVec.extractLsb k5.toNat k5.toNat x0) := by simp [bvExtractEval, hk5w]
  rw [hE55] at hr ⊢
  simp only at hr ⊢
  obtain ⟨n, rv, hrv⟩ := repeat_isBv hr
  obtain ⟨hn, hrbits⟩ := repeat_bits hrv
  simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul] at hn hrbits
  have hk5n : k5.toNat = w0 - 1 := by rw [hk5, toNat_sub_one32 (by omega) (by omega)]
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk4n : k4.toNat = 1 + (k2.toNat - k1.toNat) := by
    rw [hk4, toNat_add32 _ _ (by rw [toNat_sub32 (by omega), h1n, two32]; have := k2.isLt; rw [two32] at this; omega),
      toNat_sub32 (by omega), h1n]
  rw [hlv, hrv]
  apply val_ext (by rw [hn]; omega)
  intro j hj
  rw [BitVec.getLsbD_extractLsb, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_signExtend,
    decide_eq_true (by omega), Bool.true_and, ite_eq_right (by omega), hrbits, decide_eq_true (by omega), Bool.true_and,
    Nat.mod_one, BitVec.getLsbD_extractLsb, BitVec.msb_eq_getLsbD_last, hk5n]
  simp

/-! ## Zero extension against constants -/

theorem bv_val_toNat {n m : Nat} {x : BitVec n} {y : BitVec m} (h : Val.bv n x = Val.bv m y) :
    n = m ∧ x.toNat = y.toNat := by
  cases h; exact ⟨rfl, rfl⟩

theorem zext_val {n : Nat} (y : BitVec n) (k : Nat) (hn : n ≠ 0) :
    bvExtEval false (n + k) k [.bv n y] = .bv (n + k) (y.setWidth (n + k)) := by
  simp only [bvExtEval]; rw [ite_eq_left ⟨by omega, trivial⟩]; rfl

theorem toNat_setWidth_up {n m : Nat} (x : BitVec n) (h : n ≤ m) : (x.setWidth m).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

theorem sound_BV_ZERO_EXTEND_ULT_CONST_1 : ∀ r, rwTable 146 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  -- the constant
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC] at hr; simp [bvExtractEval, appVal, RwOp.node, Op.eval, bvCmp] at hr
  rw [hC] at hc hl hr ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hc hl hr ⊢
  -- its low part
  have hk4 : k4.toNat < k3.toNat := by
    by_cases hk4 : k4.toNat < k3.toNat
    · exact hk4
    · rw [extract_bad (by omega)] at hr; simp [appVal, RwOp.node, Op.eval, bvCmp] at hr
  have hE : bvExtractEval k4.toNat 0 [.bv k3.toNat c] =
      .bv (k4.toNat - 0 + 1) (BitVec.extractLsb k4.toNat 0 c) := by simp [bvExtractEval, hk4]
  rw [hE] at hc hr ⊢
  rw_pat at hc
  rw [zext_val _ _ (by omega)] at hc
  obtain ⟨_, hc2⟩ := conj_all2 hc
  obtain ⟨hk3e, hcn⟩ := bv_val_toNat (eq_true hc2)
  generalize BitVec.extractLsb k4.toNat 0 c = e at hc hr hcn ⊢
  -- widths from definedness
  have hw : k4.toNat - 0 + 1 = w0 := by
    by_cases hw : k4.toNat - 0 + 1 = w0
    · exact hw
    · rw [ult_eval, dite_eq_right hw] at hr; exact absurd rfl hr
  rw [zext_val _ _ (by omega)] at hl ⊢
  have hw' : k3.toNat = w0 + k1.toNat := by
    by_cases hw' : k3.toNat = w0 + k1.toNat
    · exact hw'
    · rw [ult_eval, dite_eq_right hw'] at hl; exact absurd rfl hl
  rw [ult_eval, dite_eq_left hw', ult_eval, dite_eq_left hw]
  congr 1
  simp only [BitVec.ult, BitVec.toNat_cast, toNat_setWidth_up _ (Nat.le_add_right _ _), hcn]

theorem sound_BV_ZERO_EXTEND_ULT_CONST_2 : ∀ r, rwTable 147 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  -- the constant
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC] at hr; simp [bvExtractEval, appVal, RwOp.node, Op.eval, bvCmp] at hr
  rw [hC] at hc hl hr ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hc hl hr ⊢
  -- its low part
  have hk4 : k4.toNat < k3.toNat := by
    by_cases hk4 : k4.toNat < k3.toNat
    · exact hk4
    · rw [extract_bad (by omega)] at hr; simp [appVal, RwOp.node, Op.eval, bvCmp] at hr
  have hE : bvExtractEval k4.toNat 0 [.bv k3.toNat c] =
      .bv (k4.toNat - 0 + 1) (BitVec.extractLsb k4.toNat 0 c) := by simp [bvExtractEval, hk4]
  rw [hE] at hc hr ⊢
  rw_pat at hc
  rw [zext_val _ _ (by omega)] at hc
  obtain ⟨_, hc2⟩ := conj_all2 hc
  obtain ⟨hk3e, hcn⟩ := bv_val_toNat (eq_true hc2)
  generalize BitVec.extractLsb k4.toNat 0 c = e at hc hr hcn ⊢
  have hw : k4.toNat - 0 + 1 = w0 := by
    by_cases hw : k4.toNat - 0 + 1 = w0
    · exact hw
    · rw [ult_eval, dite_eq_right (fun h => hw h.symm)] at hr; exact absurd rfl hr
  rw [zext_val _ _ (by omega)] at hl ⊢
  have hw' : k3.toNat = w0 + k1.toNat := by
    by_cases hw' : k3.toNat = w0 + k1.toNat
    · exact hw'
    · rw [ult_eval, dite_eq_right (fun h => hw' h.symm)] at hl; exact absurd rfl hl
  rw [ult_eval, dite_eq_left hw'.symm, ult_eval, dite_eq_left hw.symm]
  congr 1
  simp only [BitVec.ult, BitVec.toNat_cast, toNat_setWidth_up _ (Nat.le_add_right _ _), hcn]

/-! ## Merging constants in a concatenation -/

theorem appVal_concat_has_bad {l : List Val} (h : .bad ∈ l) : appVal .concat l = .bad := by
  match l, h with
  | [v], h => simp at h; subst h; rfl
  | a :: b :: rest, h => exact appVal_concat_bad_mem h (by simp)

theorem catBit_mid (a m1 m2 b : List Val) (hw : catW m1 = catW m2) (hb : ∀ i, catBit m1 i = catBit m2 i) (i : Nat) :
    catBit (a ++ (m1 ++ b)) i = catBit (a ++ (m2 ++ b)) i := by
  simp only [catBit_append, catW_append, hw, hb]

theorem lit32 (v : Nat) (h : v < 2 ^ 32) : bvValEval 32 v [] = .bv 32 (BitVec.ofNat 32 v) := by
  simp [bvValEval, h]

/-- BCF computes the merged literal `k1 * 2^k4 + k3` in 32 bits.  That is the
exact value when `k1` shifted left by `k4` still fits in 32 bits. -/
theorem merge32_exact (k1 k3 k4 : BitVec 32) (hg : k1.ule (BitVec.ofNat 32 4294967295 >>> k4) = true)
    (hk3 : k3.toNat < 2 ^ k4.toNat) :
    (k1 * (1#32 <<< k4) + k3).toNat = 2 ^ k4.toNat * k1.toNat + k3.toNat := by
  have hgn : k1.toNat ≤ 4294967295 / 2 ^ k4.toNat := by
    have := hg; simp only [BitVec.ule, decide_eq_true_eq] at this
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, toNat_ofNat32 (by decide), Nat.shiftRight_eq_div_pow] at this
    exact this
  by_cases hk4 : k4.toNat < 32
  · have hpow : (1#32 <<< k4).toNat = 2 ^ k4.toNat := by
      rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, show (1#32 : BitVec 32).toNat = 1 by decide, Nat.one_shiftLeft]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk4)
    have hmul : k1.toNat * 2 ^ k4.toNat ≤ 4294967295 := (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mp hgn
    have hsplit : (2 : Nat) ^ 32 = 2 ^ (32 - k4.toNat) * 2 ^ k4.toNat := by
      rw [← Nat.pow_add]; congr 1; omega
    have hlt : k1.toNat < 2 ^ (32 - k4.toNat) :=
      Nat.lt_of_mul_lt_mul_right (a := 2 ^ k4.toNat) (by rw [← hsplit, two32]; omega)
    have h2 : (k1.toNat + 1) * 2 ^ k4.toNat ≤ 2 ^ 32 := by
      rw [hsplit]; exact Nat.mul_le_mul_right _ hlt
    have hbound : k1.toNat * 2 ^ k4.toNat + k3.toNat < 2 ^ 32 := by
      rw [Nat.succ_mul] at h2; omega
    rw [BitVec.toNat_add, BitVec.toNat_mul, hpow,
      Nat.mod_eq_of_lt (show k1.toNat * 2 ^ k4.toNat < 2 ^ 32 by omega), Nat.mod_eq_of_lt hbound, Nat.mul_comm]
  · have h0 : k1.toNat = 0 := by
      have : 4294967295 / 2 ^ k4.toNat = 0 :=
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 4294967295 < 2 ^ 32)
          (Nat.pow_le_pow_right (by decide) (by omega)))
      omega
    rw [BitVec.toNat_add, BitVec.toNat_mul, h0]
    simp [Nat.mod_eq_of_lt k3.isLt]

theorem sound_BV_CONCAT_MERGE_CONST : ∀ r, rwTable 80 = some r → r.Sound := by
  intro r h
  simp only [rwTable, Option.some.injEq] at h
  subst h
  intro env henv hcond hl hr
  obtain ⟨vs0, h0⟩ := henv 0 .bvqs rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨vs6, h6⟩ := henv 6 .bvqs rfl
  have hc := hcond _ rfl
  simp only [RwExpr.bvlshr'] at hc
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [lit32 4294967295 (by decide), appVal_bvlshr32, appVal_ule32, appVal_bvadd32] at hc
  obtain ⟨hc, hgd⟩ := conj_all2 hc
  simp only [Val.bool.injEq] at hgd
  have hk5 := eq_bv32 hc
  simp only [appVal_bvshl32, appVal_bvmul32, appVal_bvadd32, spliceVal_bvValEval, List.singleton_append] at hr ⊢
  -- the three literals
  rcases lit_cases k2.toNat k1.toNat with hL1 | ⟨hk2, hk264, hk1lt, hL1⟩
  · rw [hL1] at hl; exact absurd (appVal_concat_has_bad (by simp)) hl
  rcases lit_cases k4.toNat k3.toNat with hL2 | ⟨hk4, hk464, hk3lt, hL2⟩
  · rw [hL2] at hl; exact absurd (appVal_concat_has_bad (by simp)) hl
  generalize hV : (k1 * (1#32 <<< k4) + k3).toNat = V at hr ⊢
  rcases lit_cases k5.toNat V with hL | ⟨hk5z, hk564, hVlt, hL⟩
  · rw [hL] at hr; exact absurd (appVal_concat_has_bad (by simp)) hr
  rw [hL1, hL2] at hl ⊢
  rw [hL] at hr ⊢
  -- arithmetic
  have hk5n : k5.toNat = k2.toNat + k4.toNat := by
    rw [hk5, toNat_add32 _ _ (by rw [two32]; omega)]
  have hVn : V = 2 ^ k4.toNat * k1.toNat + k3.toNat := by
    rw [← hV]; exact merge32_exact k1 k3 k4 hgd hk3lt
  -- both sides are concatenations with the same bits
  obtain ⟨n, x, hx, _, hn, hxbits⟩ := appVal_concat_bits hl (fun v hv => by
    have := congrArg List.length hv; simp at this; omega)
  obtain ⟨n', x', hx', _, hn', hx'bits⟩ := appVal_concat_bits hr (fun v hv => by
    cases vs0 with
    | nil => cases vs6 with
      | nil => simp at hv; subst hv; exact ⟨_, _, rfl⟩
      | cons _ _ => have := congrArg List.length hv; simp at this
    | cons _ _ => have := congrArg List.length hv; simp at this)
  have hw : catW [Val.bv k2.toNat (BitVec.ofNat k2.toNat k1.toNat), Val.bv k4.toNat (BitVec.ofNat k4.toNat k3.toNat)] =
      catW [Val.bv k5.toNat (BitVec.ofNat k5.toNat V)] := by simp [catW]; omega
  have hb : ∀ i, catBit [Val.bv k2.toNat (BitVec.ofNat k2.toNat k1.toNat), Val.bv k4.toNat (BitVec.ofNat k4.toNat k3.toNat)] i =
      catBit [Val.bv k5.toNat (BitVec.ofNat k5.toNat V)] i := by
    intro i
    simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero,
      BitVec.getLsbD_ofNat, hVn, Nat.testBit_two_pow_mul_add _ hk3lt]
    by_cases hi : i < k4.toNat
    · simp [hi, show i < k5.toNat by omega]
    · simp only [hi, ↓reduceIte]
      have : decide (i - k4.toNat < k2.toNat) = decide (i < k5.toNat) :=
        decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩
      rw [this]
  rw [hx, hx']
  have hlist : vs0 ++ Val.bv k2.toNat (BitVec.ofNat k2.toNat k1.toNat) ::
      Val.bv k4.toNat (BitVec.ofNat k4.toNat k3.toNat) :: vs6 =
      vs0 ++ ([Val.bv k2.toNat (BitVec.ofNat k2.toNat k1.toNat), Val.bv k4.toNat (BitVec.ofNat k4.toNat k3.toNat)] ++ vs6) := by
    simp
  have hlist' : vs0 ++ Val.bv k5.toNat (BitVec.ofNat k5.toNat V) :: vs6 =
      vs0 ++ ([Val.bv k5.toNat (BitVec.ofNat k5.toNat V)] ++ vs6) := by simp
  rw [hlist] at hn hxbits
  rw [hlist'] at hn' hx'bits
  apply val_ext (by rw [hn, hn', catW_append, catW_append, catW_append, catW_append, hw])
  intro i _
  rw [hxbits, hx'bits, catBit_mid _ _ _ _ hw hb]

end Bcf
