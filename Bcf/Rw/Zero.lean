import Bcf.Poly
import Bcf.BvLemmas

/-!
# The three trusted-rewrite shapes

BCF accepts REWRITE steps with rewrite id 0 without checking.  The
checker accepts only three equation shapes for them, each proved valid
here: splitting a bitwise `and` into bit ranges, expanding `repeat`
into a concatenation, and eliminating `distinct`.
-/

namespace Bcf

/-! ## Node semantics -/

theorem bvAnd2_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i a b : Nat}
    (h : pool[i]? = some ⟨.bvAnd w, #[a, b]⟩) :
    evalV pool ρ w i = evalV pool ρ w a &&& evalV pool ρ w b ∧
    typeOf pool a = some (.bv w) ∧ typeOf pool b = some (.bv w) ∧ typeOf pool i = some (.bv w) := by
  obtain ⟨hargs, _, hw, hti⟩ := bvN_args_bv hwf h rfl
  have hta := hargs a (by simp)
  have htb := hargs b (by simp)
  refine ⟨?_, hta, htb, hti⟩
  have := bvop_node hwf ρ w (.bvAnd w) (· &&& ·) (BitVec.allOnes w) rfl (fun _ => rfl) i _ h
  rw [this]
  simp

theorem extract_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {i x hi lo : Nat}
    (h : pool[i]? = some ⟨.bvExtract hi lo, #[x]⟩) {n : Nat} (htx : typeOf pool x = some (.bv n)) :
    lo ≤ hi ∧ hi < n ∧ typeOf pool i = some (.bv (hi - lo + 1)) ∧
    evalV pool ρ (hi - lo + 1) i = BitVec.extractLsb hi lo (evalV pool ρ n x) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := ht
  rw [typeOf_node hwf h] at h2
  simp only [mapOpt, htx, Option.bind_some, Op.resultTy, bvExtractTy, tyGuard] at h2
  split at h2
  · rename_i hc
    simp at h2
    refine ⟨hc.1, hc.2, by rw [ht, ← h2], ?_⟩
    rw [evalV, eval_node hwf ρ h]
    simp only [List.map, Op.eval, evalV_spec htx, bvExtractEval, hc.1, hc.2, and_self, ite_true]
    simp
  · simp at h2

theorem concat2_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {i p q w : Nat}
    (h : pool[i]? = some ⟨.bvConcat w, #[p, q]⟩) {n m : Nat}
    (htp : typeOf pool p = some (.bv n)) (htq : typeOf pool q = some (.bv m)) :
    n + m = w ∧ typeOf pool i = some (.bv w) ∧
    ∃ hc : n + m = w, evalV pool ρ w i = (evalV pool ρ n p ++ evalV pool ρ m q).cast hc := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := ht
  rw [typeOf_node hwf h] at h2
  simp only [mapOpt, htp, htq, Option.bind_some, Op.resultTy, bvConcatTy, tyGuard] at h2
  split at h2
  · rename_i hc
    obtain ⟨hw0, hnm', _⟩ := hc
    have hnm : n + m = w := by simpa [bvWidths] using hnm'
    simp at h2
    refine ⟨hnm, by rw [ht, ← h2], hnm, ?_⟩
    rw [evalV, eval_node hwf ρ h]
    simp only [List.map, Op.eval, evalV_spec htp, evalV_spec htq, bvConcatEval,
      Val.concatVals]
    rw [dite_eq_left ⟨hw0, hnm, by simp⟩]
    simp
  · simp at h2

/-! ## Shape 1: and-split -/

theorem extractOf_spec {st : St} {i hi lo a : Nat} (h : extractOf st i = some (hi, lo, a)) :
    st.pool[i]? = some ⟨.bvExtract hi lo, #[a]⟩ := by
  unfold extractOf at h
  split at h
  · rename_i hi' lo' args hn
    split at h
    · rename_i a' hl
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [St.node] at hn; rw [hn]; congr; exact Array.ext' hl
    · simp at h
  · simp at h

theorem and2Of_spec {st : St} {i w p q : Nat} (h : and2Of st i = some (w, p, q)) :
    st.pool[i]? = some ⟨.bvAnd w, #[p, q]⟩ := by
  unfold and2Of at h
  split at h
  · rename_i w' args hn
    split at h
    · rename_i p' q' hl
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [St.node] at hn; rw [hn]; congr; exact Array.ext' hl
    · simp at h
  · simp at h

/-- A half of the split: `x[hi:lo] & y[hi:lo]`. -/
theorem andHalf_spec {st : St} (hwf : WF st.pool) (ρ : Assign) {h x y hi lo : Nat}
    (hh : andHalf st h x y hi lo = true) {w : Nat}
    (htx : typeOf st.pool x = some (.bv w)) (hty : typeOf st.pool y = some (.bv w)) :
    lo ≤ hi ∧ hi < w ∧ typeOf st.pool h = some (.bv (hi - lo + 1)) ∧
    evalV st.pool ρ (hi - lo + 1) h =
      BitVec.extractLsb hi lo (evalV st.pool ρ w x) &&& BitVec.extractLsb hi lo (evalV st.pool ρ w y) := by
  unfold andHalf at hh
  split at hh
  · rename_i w' p q hpq
    split at hh
    · rename_i h1 l1 a h2 l2 b hp hq
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hh
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hab⟩ := hh
      have hn := and2Of_spec hpq
      obtain ⟨hv, htp, htq, hth⟩ := bvAnd2_node hwf ρ hn
      have hpn := extractOf_spec hp
      have hqn := extractOf_spec hq
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hlo, hhi, htp', hvp⟩ := extract_node hwf ρ hpn htx
        obtain ⟨_, _, htq', hvq⟩ := extract_node hwf ρ hqn hty
        rw [htp'] at htp; simp at htp; subst htp
        refine ⟨hlo, hhi, hth, ?_⟩
        rw [hv, hvp, hvq]
      · obtain ⟨hlo, hhi, htp', hvp⟩ := extract_node hwf ρ hpn hty
        obtain ⟨_, _, htq', hvq⟩ := extract_node hwf ρ hqn htx
        rw [htp'] at htp; simp at htp; subst htp
        refine ⟨hlo, hhi, hth, ?_⟩
        rw [hv, hvp, hvq, BitVec.and_comm]
    · simp at hh
  · simp at hh

/-- The pieces of an and-split, concatenated, are `x[hi:0] & y[hi:0]`
(stated bitwise, which avoids casts between the widths). -/
theorem andPieces_eval {st : St} (hwf : WF st.pool) (ρ : Assign) {x y w : Nat}
    (htx : typeOf st.pool x = some (.bv w)) (hty : typeOf st.pool y = some (.bv w)) :
    ∀ (l : List Nat) (hi : Nat), andPieces st x y hi l = true →
      hi < w ∧ ∃ v : BitVec (hi + 1), Val.concatVals (l.map (eval st.pool ρ)) = some (.bv (hi + 1) v) ∧
        ∀ i, i ≤ hi → v.getLsbD i = ((evalV st.pool ρ w x).getLsbD i && (evalV st.pool ρ w y).getLsbD i)
  | [], _, hp => by simp [andPieces] at hp
  | h :: rest, hi, hp => by
    unfold andPieces at hp
    split at hp
    · rename_i lo _
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hH, hR⟩ := hp
      obtain ⟨hlo, hhi, hth, hvh⟩ := andHalf_spec hwf ρ hH htx hty
      refine ⟨hhi, ?_⟩
      have heh := evalV_spec (ρ := ρ) hth
      split at hR
      · rename_i hemp
        simp only [List.isEmpty_iff] at hemp
        simp only [beq_iff_eq] at hR
        subst hemp hR
        refine ⟨(evalV st.pool ρ (hi - 0 + 1) h).cast (by omega), ?_, ?_⟩
        · simp only [List.map, heh, Val.concatVals]
          rw [bv_cast_eq (show hi - 0 + 1 = hi + 1 by omega)]
        · intro i hi'
          rw [BitVec.getLsbD_cast, hvh]
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb]
          have : i < hi + 1 := by omega
          simp [this]
      · rename_i hemp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hR
        obtain ⟨hlo1, hrest⟩ := hR
        obtain ⟨_, v', hv', hbits⟩ := andPieces_eval hwf ρ htx hty rest (lo - 1) hrest
        have hne : rest.map (eval st.pool ρ) ≠ [] := by
          cases rest with
          | nil => simp at hemp
          | cons _ _ => simp
        refine ⟨((evalV st.pool ρ (hi - lo + 1) h) ++ v').cast (by omega), ?_, ?_⟩
        · rw [List.map_cons, concatVals_cons_ne hne, hv', heh]
          simp only [catOpt]
          rw [bv_cast_eq (show hi - lo + 1 + (lo - 1 + 1) = hi + 1 by omega)]
        · intro i hi'
          rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
          split
          · rename_i hil
            exact hbits i (by omega)
          · rename_i hil
            rw [hvh]
            simp only [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb]
            have h1 : i - (lo - 1 + 1) < hi - lo + 1 := by omega
            have h2 : lo + (i - (lo - 1 + 1)) = i := by omega
            simp [h1, h2]
    · simp at hp

theorem rw0AndSplit_sound {st : St} (hwf : WF st.pool) (ρ : Assign) {a b : Nat}
    (h : rw0AndSplit st a b = true) : eval st.pool ρ a = eval st.pool ρ b := by
  unfold rw0AndSplit at h
  split at h
  · rename_i w x y w' hs hxy hb
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, h2⟩, hp⟩ := h
    have han := and2Of_spec hxy
    obtain ⟨hv, htx, hty, hta⟩ := bvAnd2_node hwf ρ han
    obtain ⟨hw, v, hcv, hbits⟩ := andPieces_eval hwf ρ htx hty _ _ hp
    have hbn : st.pool[b]? = some ⟨.bvConcat w, hs⟩ := by simpa [St.node] using hb
    rw [evalV_spec hta, eval_node hwf ρ hbn, hv]
    simp only [Op.eval, bvConcatEval, hcv]
    rw [dite_eq_left ⟨by omega, by omega, by simpa using h2⟩]
    congr 1
    apply bv_ext
    intro i hi
    rw [BitVec.getLsbD_cast, hbits i (by omega), BitVec.getLsbD_and]
  · simp at h

/-! ## Shape 2: repeat -/

theorem replicate_one {w : Nat} (x : BitVec w) : x.replicate 1 = x.cast (by simp) := by
  apply bv_ext
  intro i hi
  rw [BitVec.getLsbD_replicate, BitVec.getLsbD_cast]
  have : i < w * 1 := by simpa using hi
  have h2 : i % w = i := Nat.mod_eq_of_lt (by simpa using hi)
  rw [decide_eq_true this, Bool.true_and, h2]

theorem concatVals_replicate {m : Nat} (v : BitVec m) :
    ∀ k, 1 ≤ k → ∃ hc : m * k = m * k, Val.concatVals (List.replicate k (.bv m v)) = some (.bv (m * k) ((v.replicate k).cast hc)) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    cases k with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp only [List.replicate, Val.concatVals]
      rw [replicate_one, bv_cast_eq (show m = m * 1 by simp)]
      simp
    | succ k =>
      obtain ⟨_, hc⟩ := ih (by omega)
      refine ⟨rfl, ?_⟩
      rw [List.replicate_succ, concatVals_cons_ne (by simp), hc]
      simp only [catOpt]
      rw [replicate_succ_cast, bv_cast_eq (show m + m * (k + 1) = m * (k + 1 + 1) by simp only [Nat.mul_succ]; omega)]
      simp

theorem rw0Repeat_sound {st : St} (hwf : WF st.pool) (ρ : Assign) {a b : Nat}
    (h : rw0Repeat st a b = true) : eval st.pool ρ a = eval st.pool ρ b := by
  unfold rw0Repeat at h
  split at h
  · rename_i w k args ha
    split at h
    · rename_i y hl
      have han : st.pool[a]? = some ⟨.bvRepeat w k, #[y]⟩ := by
        simp only [St.node] at ha; rw [ha]; congr; exact Array.ext' hl
      -- typing of the repeat node
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf a _ han).2
      have h2 := ht
      rw [typeOf_node hwf han] at h2
      simp only [mapOpt] at h2
      cases hty : typeOf st.pool y with
      | none => rw [hty] at h2; simp at h2
      | some ty =>
      rw [hty] at h2
      cases ty with
      | bv m =>
        simp only [Option.bind_some, Op.resultTy, bvRepeatTy, tyGuard] at h2
        split at h2
        · rename_i hc
          obtain ⟨hw0, hmk⟩ := hc
          have hva : eval st.pool ρ a = .bv w ((evalV st.pool ρ m y).replicate k |>.cast hmk) := by
            rw [eval_node hwf ρ han]
            simp only [List.map, Op.eval, evalV_spec hty, bvRepeatEval]
            rw [dite_eq_left ⟨hw0, hmk⟩]
          split at h
          · rename_i hk1
            simp only [beq_iff_eq] at hk1 h
            subst hk1; subst h
            rw [hva, evalV_spec hty, replicate_one, bv_cast_eq (show m = w by simpa using hmk)]
            simp
          · rename_i hk1
            split at h
            · rename_i w' ys hb
              simp only [Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨rfl, hys⟩ := h
              have hk : 1 ≤ k := by
                cases k with
                | zero => simp at hmk; exact absurd hmk.symm hw0
                | succ k => omega
              have hbn : st.pool[b]? = some ⟨.bvConcat w, (List.replicate k y).toArray⟩ := by
                simp only [St.node] at hb; rw [hb]; congr; exact Array.ext' hys
              rw [hva, eval_node hwf ρ hbn]
              simp only [List.map_replicate, Op.eval, bvConcatEval, evalV_spec hty]
              obtain ⟨_, hcv⟩ := concatVals_replicate (evalV st.pool ρ m y) k hk
              simp only [hcv]
              have h2k : 2 ≤ k := by
                cases k with
                | zero => omega
                | succ k => cases k with
                  | zero => simp at hk1
                  | succ k => omega
              rw [dite_eq_left ⟨hw0, hmk, by simpa using h2k⟩]
              simp
            · simp at h
        · simp at h2
      | bool => simp [Op.resultTy, bvRepeatTy] at h2
      | list _ _ => simp [Op.resultTy, bvRepeatTy] at h2
    · simp at h
  · simp at h

/-! ## Shape 3: distinct -/

theorem rw0Distinct_sound {st : St} (hwf : WF st.pool) (ρ : Assign) {a b : Nat}
    (h : rw0Distinct st a b = true) : eval st.pool ρ a = eval st.pool ρ b := by
  unfold rw0Distinct at h
  split at h
  · rename_i xs ns ha hb
    split at h
    · rename_i e hl
      split at h
      · rename_i ys he
        simp only [beq_iff_eq] at h
        subst h
        simp only [St.node] at ha hb he
        have hbn : st.pool[b]? = some ⟨.boolNot, #[e]⟩ := by rw [hb]; congr; exact Array.ext' hl
        -- both `distinct xs` and `eq xs` are boolean nodes over the same arguments
        have hta := typeOf_bool_node hwf ha (Or.inr (Or.inl rfl))
        have hte := typeOf_bool_node hwf he (Or.inr (Or.inl rfl))
        obtain ⟨ra, hra⟩ := eval_bool (ρ := ρ) hta
        obtain ⟨re, hre⟩ := eval_bool (ρ := ρ) hte
        rw [eval_node hwf ρ hbn]
        simp only [List.map, Op.eval, boolNotEval, hre]
        rw [eval_node hwf ρ ha] at hra ⊢
        rw [eval_node hwf ρ he] at hre
        simp only [Op.eval] at hra hre ⊢
        -- eqEval on the same argument list, negated vs not
        generalize xs.toList.map (eval st.pool ρ) = vs at hra hre ⊢
        unfold eqEval at hra hre ⊢
        split at hra
        · rename_i v1 v2
          dsimp only at hre ⊢
          split at hra
          · rename_i r hr
            try rw [hr] at hre
            simp at hra hre
            simp [hre]
          · simp at hra
        · simp at hra
      · simp at h
    · simp at h
  · simp at h

/-! ## The step -/

theorem rw0_sound {base : Pool} {g : Nat} {bi : Builtins} {st : St} (hinv : Inv base g bi st) {e : Nat}
    (h : ruleRewrite0 st e = true) : Entails st g e := by
  have hwf := hinv.wf
  unfold ruleRewrite0 at h
  split at h
  · rename_i a b hab
    have hen := node_bind_eq hab
    refine ⟨idx_lt_of_get hen, ?_⟩
    intro ρ _
    rw [holds_eq_node hwf hen ρ]
    have hab' : eval st.pool ρ a = eval st.pool ρ b := by
      simp only [Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact rw0AndSplit_sound hwf ρ h
      · exact rw0Repeat_sound hwf ρ h
      · exact rw0Distinct_sound hwf ρ h
    refine ⟨hab', ?_⟩
    -- the sides are scalars, from the typing of `eq`
    obtain ⟨m, hm⟩ := node_of_lt (child_lt hwf hen (a := a) (by simp))
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf a _ hm).2
    have htb := eq_args_same_ty hwf hen ht
    -- `eqTy` demands a scalar type
    obtain ⟨te, hte⟩ := Option.isSome_iff_exists.mp (hwf e _ hen).2
    have h2 := hte
    rw [typeOf_node hwf hen] at h2
    simp only [mapOpt, ht, htb, Option.bind_some, Op.resultTy, eqTy, tyGuard] at h2
    split at h2
    · rename_i hc
      exact ⟨t, by rw [eval_ty, ht], hc.2⟩
    · simp at h2
  · simp at h

end Bcf
