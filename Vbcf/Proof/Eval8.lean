import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval7

/-!
# Vbcf proofs: the Eval family, part 8 — the n-ary group of `cval`, operator by operator
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- The accumulator after `j` arguments is `G` of their values. -/
def CvAccR (st : St) (args : Array Nat) (G : List Bcf.Val → Nat) (j : Nat) (acc : BitVec 64) : Prop :=
  ∃ vs, mapOpt (memoVal st) (args.toList.take j) = some vs ∧ acc.toNat = G vs

theorem CvAccR.zero {st : St} {args : Array Nat} {G : List Bcf.Val → Nat} {acc : BitVec 64}
    (h : acc.toNat = G []) : CvAccR st args G 0 acc := ⟨[], by simp [mapOpt], h⟩

theorem CvAccR.succ {st : St} {args : Array Nat} {G : List Bcf.Val → Nat} {j : Nat} {acc acc' : BitVec 64}
    (hR : CvAccR st args G j acc) (hj : j < args.size) {v : Bcf.Val} (hv : memoVal st args[j] = some v)
    (H : ∀ vs, mapOpt (memoVal st) (args.toList.take j) = some vs → acc.toNat = G vs →
      acc'.toNat = G (vs ++ [v])) : CvAccR st args G (j + 1) acc' := by
  obtain ⟨vs, hvs, hacc⟩ := hR
  exact ⟨vs ++ [v], cv_mapOpt_take_succ (by simpa using hj) hvs (by simpa using hv), H vs hvs hacc⟩

theorem CvAccR.all {st : St} {args : Array Nat} {G : List Bcf.Val → Nat} {acc : BitVec 64}
    (hR : CvAccR st args G args.size acc) :
    ∃ vs, mapOpt (memoVal st) args.toList = some vs ∧ acc.toNat = G vs := by
  obtain ⟨vs, hvs, hacc⟩ := hR
  exact ⟨vs, cv_mapOpt_take_all (by simpa using hvs), hacc⟩

/-! ### Boolean folds -/

theorem cv_bfold_and_aux : ∀ (bs : List Bool) (a : Bool),
    (bs.map (fun b => if b then 1 else 0)).foldl (· &&& ·) (if a then 1 else 0) =
      if a && bs.all id then 1 else 0
  | [], a => by cases a <;> rfl
  | b :: bs, a => by
    have := cv_bfold_and_aux bs (a && b)
    simp only [List.map_cons, List.foldl_cons, List.all_cons]
    cases a <;> cases b <;> simp_all

theorem cv_bfold_and (bs : List Bool) :
    (bs.map (fun b => if b then 1 else 0)).foldl (· &&& ·) 1 = if bs.all id then 1 else 0 := by
  have := cv_bfold_and_aux bs true; simpa using this

theorem cv_bfold_or_aux : ∀ (bs : List Bool) (a : Bool),
    (bs.map (fun b => if b then 1 else 0)).foldl (· ||| ·) (if a then 1 else 0) =
      if a || bs.any id then 1 else 0
  | [], a => by cases a <;> rfl
  | b :: bs, a => by
    have := cv_bfold_or_aux bs (a || b)
    simp only [List.map_cons, List.foldl_cons, List.any_cons]
    cases a <;> cases b <;> simp_all

theorem cv_bfold_or (bs : List Bool) :
    (bs.map (fun b => if b then 1 else 0)).foldl (· ||| ·) 0 = if bs.any id then 1 else 0 := by
  have := cv_bfold_or_aux bs false; simpa using this

theorem cv_bfold_xor_aux : ∀ (bs : List Bool) (a : Bool),
    (bs.map (fun b => if b then 1 else 0)).foldl (· ^^^ ·) (if a then 1 else 0) =
      if bs.foldl (fun acc b => acc ^^ b) a then 1 else 0
  | [], a => by cases a <;> rfl
  | b :: bs, a => by
    have := cv_bfold_xor_aux bs (a ^^ b)
    simp only [List.map_cons, List.foldl_cons]
    cases a <;> cases b <;> simp_all

theorem cv_bfold_xor (bs : List Bool) :
    (bs.map (fun b => if b then 1 else 0)).foldl (· ^^^ ·) 0 =
      if bs.foldl (fun acc b => acc ^^ b) false then 1 else 0 := by
  have := cv_bfold_xor_aux bs false; simpa using this


/-! ### `bvfrombool` -/

/-- The C loop for `bvfrombool`: or in argument `k` shifted by `k`. -/
def cvFbGo : Nat → List Bcf.Val → Nat → Nat
  | _, [], a => a
  | k, v :: rest, a => cvFbGo (k + 1) rest (a ||| (cvNv v * 2 ^ k % 2 ^ 64))

theorem cvFbGo_append : ∀ (l : List Bcf.Val) (k a : Nat) (v : Bcf.Val),
    cvFbGo k (l ++ [v]) a = cvFbGo k l a ||| (cvNv v * 2 ^ (k + l.length) % 2 ^ 64)
  | [], k, a, v => by simp [cvFbGo]
  | u :: l, k, a, v => by
    simp only [List.cons_append, cvFbGo, List.length_cons]
    rw [cvFbGo_append l (k + 1), show k + (l.length + 1) = k + 1 + l.length by omega]

theorem cvFbGo_bools : ∀ (bs : List Bool) (k a : Nat), k + bs.length ≤ 64 →
    cvFbGo k (bs.map Val.bool) a = a ||| ((BitVec.ofBoolListLE bs).toNat * 2 ^ k)
  | [], k, a, _ => by simp [cvFbGo, BitVec.ofBoolListLE]
  | b :: bs, k, a, h => by
    simp only [List.map_cons, cvFbGo, List.length_cons] at h ⊢
    rw [cvFbGo_bools bs (k + 1) _ (by omega)]
    have hk : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    have hb : cvNv (Val.bool b) * 2 ^ k % 2 ^ 64 = (if b then 1 else 0) * 2 ^ k := by
      cases b <;> simp [cvNv, Nat.mod_eq_of_lt hk]
    rw [hb, BitVec.ofBoolListLE, BitVec.toNat_concat, Nat.or_assoc]
    congr 1
    have e1 : ((BitVec.ofBoolListLE bs).toNat * 2 + b.toNat) * 2 ^ k =
        ((BitVec.ofBoolListLE bs).toNat <<< (k + 1)) + (if b then 1 else 0) * 2 ^ k := by
      rw [Nat.shiftLeft_eq, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k)]
      cases b <;> simp
    have hlt : (if b then 1 else 0) * 2 ^ k < 2 ^ (k + 1) := by
      have := Nat.two_pow_pos k
      rw [Nat.pow_succ]; cases b <;> simp <;> omega
    rw [e1, Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.or_comm, Nat.shiftLeft_eq]


/-! ### `concat` -/

/-- One step of the C loop for `concat`. -/
def cvCcStep (a : Nat) (v : Bcf.Val) : Nat := (a * 2 ^ cvVw v) % 2 ^ 64 ||| cvNv v

theorem cv_cc_step_add {a n : Nat} {x : BitVec n} (ha : a * 2 ^ n < 2 ^ 64) :
    cvCcStep a (.bv n x) = a * 2 ^ n + x.toNat := by
  unfold cvCcStep
  simp only [cvVw, cvNv]
  rw [Nat.mod_eq_of_lt ha, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt]

theorem cv_cc_fold : ∀ (vs : List Bcf.Val) (a N : Nat) (X : BitVec N),
    Val.concatVals vs = some (.bv N X) → N ≤ 64 → a < 2 ^ (64 - N) →
    vs.foldl cvCcStep a = a * 2 ^ N + X.toNat
  | [], a, N, X, h, _, _ => by simp [Val.concatVals] at h
  | [v], a, N, X, h, hN, ha => by
    rcases v with ⟨n, x⟩ | b | ⟨e, l⟩ | _ <;> simp [Val.concatVals] at h
    obtain ⟨rfl, h2⟩ := h
    subst h2
    have : a * 2 ^ n < 2 ^ 64 := by
      calc a * 2 ^ n < 2 ^ (64 - n) * 2 ^ n := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by rw [← Nat.pow_add, Nat.sub_add_cancel hN]
    simp only [List.foldl_cons, List.foldl_nil]
    exact cv_cc_step_add this
  | v :: v' :: rest, a, N, X, h, hN, ha => by
    rcases v with ⟨n, x⟩ | b | ⟨e, l⟩ | _ <;> simp only [Val.concatVals] at h
    all_goals try (simp at h)
    split at h
    · rename_i M Y hY
      simp at h
      obtain ⟨rfl, h2⟩ := h
      subst h2
      have hn64 : n * 1 ≤ 64 := by omega
      have h1 : a * 2 ^ n < 2 ^ 64 := by
        calc a * 2 ^ n < 2 ^ (64 - (n + M)) * 2 ^ n :=
              Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _)
          _ ≤ 2 ^ 64 := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : a * 2 ^ n + x.toNat < 2 ^ (64 - M) := by
        have hx := x.isLt
        calc a * 2 ^ n + x.toNat < a * 2 ^ n + 2 ^ n := by omega
          _ = (a + 1) * 2 ^ n := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ 2 ^ (64 - (n + M)) * 2 ^ n := Nat.mul_le_mul_right _ ha
          _ = 2 ^ (64 - M) := by rw [← Nat.pow_add]; congr 1; omega
      rw [List.foldl_cons, cv_cc_step_add h1, cv_cc_fold (v' :: rest) _ M Y hY (by omega) h2,
        BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt Y.isLt,
        Nat.shiftLeft_eq, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_assoc]
    · simp at h

theorem cv_fin_concat {ρ : Assign} {w' : Nat} {vs : List Bcf.Val} {t : Bcf.Ty} {w : BitVec 32}
    {acc : BitVec 64}
    (hty : (Op.eval ρ (.bvConcat w') vs).ty = some t) (hw : CvW t w)
    (hacc : acc.toNat = vs.foldl cvCcStep 0) :
    CvRep w acc (Op.eval ρ (.bvConcat w') vs) := by
  simp only [Op.eval, bvConcatEval] at hty ⊢
  split at hty
  · rename_i N X hX
    by_cases hg : w' ≠ 0 ∧ N = w' ∧ 2 ≤ vs.length
    · rw [dite_eq_left hg] at hty ⊢
      simp at hty; subst hty
      have h64 := hw.bv.2.1
      apply CvRep.of_bv hw
      rw [hacc, BitVec.toNat_cast, cv_cc_fold vs 0 N X hX (by omega) (Nat.two_pow_pos _)]
      simp
    · simp [hg] at hty
  · simp at hty


theorem cv_mapOpt_mem_rev {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    mapOpt f l = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by simp [mapOpt] at h; subst h; simp at hy
  | a :: rest, l', h, y, hy => by
    simp only [mapOpt] at h
    split at h
    · rename_i b bs hb hbs
      simp at h; subst h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, by simp, hb⟩
      · obtain ⟨x, hx, hfx⟩ := cv_mapOpt_mem_rev hbs y hy
        exact ⟨x, by simp [hx], hfx⟩
    · simp at h

theorem cv_bvWidths_len : ∀ (l : List Bcf.Ty) (N : Nat), bvWidths l = some N →
    (∀ m, Bcf.Ty.bv m ∈ l → 1 ≤ m) → l.length ≤ N
  | [], N, h, _ => by simp [bvWidths] at h
  | [ty], N, h, hp => by
    cases ty <;> simp [bvWidths] at h
    rename_i n
    subst h; have := hp n (by simp); simp; omega
  | ty :: ty' :: rest, N, h, hp => by
    cases ty <;> simp only [bvWidths] at h
    all_goals try (simp at h)
    rename_i n
    obtain ⟨M, hM, rfl⟩ := h
    have hlen := cv_bvWidths_len (ty' :: rest) M hM (fun m hm => hp m (by simp [hm]))
    have hn := hp n (by simp)
    simp at hlen ⊢; omega

theorem cv_bvWidths_mem : ∀ (l : List Bcf.Ty) (N : Nat), bvWidths l = some N →
    (∀ m, Bcf.Ty.bv m ∈ l → 1 ≤ m) → ∀ ty ∈ l, ∃ m, ty = .bv m ∧ m + l.length ≤ N + 1
  | [], N, h, _, _, _ => by simp [bvWidths] at h
  | [ty], N, h, _, ty', hty => by
    cases ty <;> simp [bvWidths] at h
    subst h; simp at hty; subst hty; exact ⟨_, rfl, by simp⟩
  | ty :: ty' :: rest, N, h, hp, ty0, hty0 => by
    cases ty <;> simp only [bvWidths] at h
    all_goals try (simp at h)
    rename_i n
    obtain ⟨M, hM, rfl⟩ := h
    have hlen := cv_bvWidths_len (ty' :: rest) M hM (fun m hm => hp m (by simp [hm]))
    have hn := hp n (by simp)
    rcases List.mem_cons.mp hty0 with rfl | hmem
    · refine ⟨n, rfl, ?_⟩; simp at hlen ⊢; omega
    · obtain ⟨m, rfl, hm⟩ := cv_bvWidths_mem (ty' :: rest) M hM (fun m hm => hp m (by simp [hm])) _ hmem
      refine ⟨m, rfl, ?_⟩; simp at hm ⊢; omega

section ops
variable {d : BitVec 32} {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt}
  {i : Nat} {args : Array Nat} {t : Bcf.Ty} {hdr par w cw : BitVec 32}
  {x y z sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}

theorem grpN_add {w' : Nat} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨.bvAdd w', args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (.bvAdd w')))
        (BitVec.ofNat 32 (tailLen ⟨.bvAdd w', args⟩)) par (BitVec.ofNat 32 (opLo (.bvAdd w')))
        (BitVec.ofNat 32 (opHi (.bvAdd w'))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.bvAdd w') := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨.bvAdd w', args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp, opLo] at hto; subst hto
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).sum % 2 ^ w'))
    (CvAccR.zero (by simp))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [cv_and_mW hk1 hk2, BitVec.toNat_setWidth, BitVec.toNat_add, hacc, hvr.cvNv,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk2)]
    simp
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_bvN rfl (fun l => l.sum % 2 ^ w')
      (fun xs => by rw [cv_foldl_add_toNat]; simp) hty hw hacc⟩

theorem grpN_mul {w' : Nat} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.bvMul w', args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.bvMul w')))
        (BitVec.ofNat 32 (tailLen ⟨Op.bvMul w', args⟩)) par (BitVec.ofNat 32 (opLo (Op.bvMul w')))
        (BitVec.ofNat 32 (opHi (Op.bvMul w'))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.bvMul w') := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.bvMul w', args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp, opLo] at hto; subst hto
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.assign; cv_simp0 [LoopQ]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).prod % 2 ^ w'))
    (CvAccR.zero (by simp; exact (Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))).symm))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [cv_and_mW hk1 hk2, BitVec.toNat_setWidth, BitVec.toNat_mul, hacc, hvr.cvNv,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk2)]
    simp [Nat.mod_mul_mod]
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_bvN rfl (fun l => l.prod % 2 ^ w')
      (fun xs => by rw [cv_foldl_mul_toNat]; simp) hty hw hacc⟩

theorem grpN_or {w' : Nat} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.bvOr w', args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.bvOr w')))
        (BitVec.ofNat 32 (tailLen ⟨Op.bvOr w', args⟩)) par (BitVec.ofNat 32 (opLo (Op.bvOr w')))
        (BitVec.ofNat 32 (opHi (Op.bvOr w'))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.bvOr w') := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.bvOr w', args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp, opLo] at hto; subst hto
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).foldl (· ||| ·) 0))
    (CvAccR.zero (by simp))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [BitVec.toNat_or, hacc, hvr.cvNv]
    simp [List.foldl_append]
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_bvN rfl (fun l => l.foldl (· ||| ·) 0)
      (fun xs => by rw [cv_foldl_or_toNat]; rfl) hty hw hacc⟩

theorem grpN_and {w' : Nat} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.bvAnd w', args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.bvAnd w')))
        (BitVec.ofNat 32 (tailLen ⟨Op.bvAnd w', args⟩)) par (BitVec.ofNat 32 (opLo (Op.bvAnd w')))
        (BitVec.ofNat 32 (opHi (Op.bvAnd w'))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.bvAnd w') := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.bvAnd w', args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp, opLo] at hto; subst hto
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.assign; cv_simp0 [LoopQ]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).foldl (· &&& ·) (2 ^ w' - 1)))
    (CvAccR.zero (by simp; exact mW_bv_toNat hk1 hk2))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [BitVec.toNat_and, hacc, hvr.cvNv]
    simp [List.foldl_append]
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_bvN rfl (fun l => l.foldl (· &&& ·) (2 ^ w' - 1))
      (fun xs => by rw [cv_foldl_and_toNat]; simp) hty hw hacc⟩

theorem grpN_xor {w' : Nat} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.bvXor w', args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.bvXor w')))
        (BitVec.ofNat 32 (tailLen ⟨Op.bvXor w', args⟩)) par (BitVec.ofNat 32 (opLo (Op.bvXor w')))
        (BitVec.ofNat 32 (opHi (Op.bvXor w'))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.bvXor w') := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.bvXor w', args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp, opLo] at hto; subst hto
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).foldl (· ^^^ ·) 0))
    (CvAccR.zero (by simp))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [BitVec.toNat_xor, hacc, hvr.cvNv]
    simp [List.foldl_append]
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_bvN rfl (fun l => l.foldl (· ^^^ ·) 0)
      (fun xs => by rw [cv_foldl_xor_toNat]; rfl) hty hw hacc⟩

theorem grpN_conj (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.conj, args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.conj)))
        (BitVec.ofNat 32 (tailLen ⟨Op.conj, args⟩)) par (BitVec.ofNat 32 (opLo (Op.conj)))
        (BitVec.ofNat 32 (opHi (Op.conj))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.conj) := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.conj, args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp] at hto; subst hto
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.assign; cv_simp0 [LoopQ]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).foldl (· &&& ·) 1))
    (CvAccR.zero (by simp))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [BitVec.toNat_and, hacc, hvr.cvNv]
    simp [List.foldl_append]
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_boolN rfl (fun l => l.foldl (· &&& ·) 1) cv_bfold_and hty hw hacc⟩

theorem grpN_disj (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.disj, args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.disj)))
        (BitVec.ofNat 32 (tailLen ⟨Op.disj, args⟩)) par (BitVec.ofNat 32 (opLo (Op.disj)))
        (BitVec.ofNat 32 (opHi (Op.disj))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.disj) := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.disj, args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp] at hto; subst hto
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).foldl (· ||| ·) 0))
    (CvAccR.zero (by simp))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [BitVec.toNat_or, hacc, hvr.cvNv]
    simp [List.foldl_append]
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_boolN rfl (fun l => l.foldl (· ||| ·) 0) cv_bfold_or hty hw hacc⟩

theorem grpN_bxor (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.boolXor, args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.boolXor)))
        (BitVec.ofNat 32 (tailLen ⟨Op.boolXor, args⟩)) par (BitVec.ofNat 32 (opLo (Op.boolXor)))
        (BitVec.ofNat 32 (opHi (Op.boolXor))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.boolXor) := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.boolXor, args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp] at hto; subst hto
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => (vs.map cvNv).foldl (· ^^^ ·) 0))
    (CvAccR.zero (by simp))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0
    apply K
    refine hR.succ hj hmv (fun vs _ hacc => ?_)
    rw [BitVec.toNat_xor, hacc, hvr.cvNv]
    simp [List.foldl_append]
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_boolN rfl (fun l => l.foldl (· ^^^ ·) 0) cv_bfold_xor hty hw hacc⟩

theorem cv_fin_frombool {ρ : Assign} {vs : List Bcf.Val} {t : Bcf.Ty} {w : BitVec 32} {acc : BitVec 64}
    (hty : (Op.eval ρ .bvFromBool vs).ty = some t) (hw : CvW t w) (hacc : acc.toNat = cvFbGo 0 vs 0) :
    CvRep w acc (Op.eval ρ .bvFromBool vs) := by
  simp only [Op.eval, bvFromBoolEval] at hty ⊢
  split at hty
  · rename_i bs hbs
    by_cases hg : 1 ≤ bs.length
    · rw [ite_eq_left hg] at hty ⊢
      simp at hty; subst hty
      have h64 := hw.bv.2.1
      apply CvRep.of_bv hw
      rw [hacc, cv_bools_eq_map hbs, cvFbGo_bools bs 0 0 (by omega)]
      simp
    · simp [hg] at hty
  · simp at hty

theorem grpN_frombool (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.bvFromBool, args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.bvFromBool)))
        (BitVec.ofNat 32 (tailLen ⟨Op.bvFromBool, args⟩)) par (BitVec.ofNat 32 (opLo (Op.bvFromBool)))
        (BitVec.ofNat 32 (opHi (Op.bvFromBool))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.bvFromBool) := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.bvFromBool, args⟩) hl]
  obtain ⟨argTys, t', -, hrt, ht', hlen⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  simp [opTy, isBoolOp] at hto; subst hto
  have h64 : args.size ≤ 64 := by have := hw.bv.2.1; simp at hlen; omega
  simp only [cvN, Stmt.block]
  apply WP.assign_seq; cv_simp0
  apply WP.ite_seq; cv_simp0 [opC]
  apply WP.ite_seq; cv_simp0 [opC]
  apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => cvFbGo 0 vs 0))
    (CvAccR.zero (by simp [cvFbGo]))
  · intro j acc r vl v s' Q' hj hR hmv hvr K
    have hj64 : j < 64 := by omega
    have hjm : j % 18446744073709551616 = j := Nat.mod_eq_of_lt (by omega)
    simp only [cvNc]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.ite; cv_simp0 [opC]
    apply WP.assign; cv_simp0 [hj64, hjm]
    apply K
    refine hR.succ hj hmv (fun vs hvs hacc => ?_)
    have hl' : vs.length = j := by
      have := mapOpt_length hvs; simp at this; omega
    rw [cvFbGo_append, BitVec.toNat_or, BitVec.toNat_shiftLeft, hacc, hvr.cvNv, hl', Nat.shiftLeft_eq]
    simp
  · intro acc hR
    obtain ⟨vs, hall, hacc⟩ := hR.all
    have hm := cv_memoVal_list hok hn hl (by simp) hall
    have hty := cv_memoVal_ty hok hm
    rw [ht] at hty
    exact ⟨_, hm, cv_fin_frombool hty hw hacc⟩

theorem grpN_concat {w' : Nat} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) (h : Holds W s.mem sb c) (hc : VInv posOf c st)
    (hpool : c.k.pool = some (pb, 0)) (hn : st.pool[i]? = some ⟨Op.bvConcat w', args⟩)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC (Op.bvConcat w')))
        (BitVec.ofNat 32 (tailLen ⟨Op.bvConcat w', args⟩)) par (BitVec.ofNat 32 (opLo (Op.bvConcat w')))
        (BitVec.ofNat 32 (opHi (Op.bvConcat w'))) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  have hok := hc.ok.tys
  have hl : ¬ IsLeaf (Op.bvConcat w') := by simp [IsLeaf, isLeaf]
  rw [tailLen_of_not_leaf (n := ⟨Op.bvConcat w', args⟩) hl]
  obtain ⟨argTys, t', hmap, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hrt' := hrt
  simp only [Op.resultTy, bvConcatTy, tyGuard] at hrt'
  split at hrt'
  · rename_i hg
    obtain ⟨-, hwid, h2⟩ := hg
    simp at hrt'; subst hrt'
    have h64 := hw.bv.2.1
    obtain ⟨args', he, hargsz, -, hargs⟩ := hc.argsN hn rfl hl
    injection he with _ he2
    subst he2
    have hp : ∀ m, Bcf.Ty.bv m ∈ argTys → 1 ≤ m := by
      intro m hm
      obtain ⟨a, ha, hta⟩ := cv_mapOpt_mem_rev hmap _ hm
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      simp at hk
      obtain ⟨na, hna⟩ := node_of_lv (hargs k hk)
      obtain ⟨t2, ht2, -, hfit⟩ := hc.tyOf hna
      simp at hta
      rw [hta] at ht2; cases ht2
      exact hfit.1
    simp only [cvN, Stmt.block]
    apply WP.assign_seq; cv_simp0
    apply WP.ite_seq; cv_simp0 [opC]
    apply WP.ite_seq; cv_simp0 [opC]
    apply grpN_loop IH hd h hc hpool hn hl hQ (CvAccR st args (fun vs => vs.foldl cvCcStep 0))
      (CvAccR.zero (by simp))
    · intro j acc r vl v s' Q' hj hR hmv hvr K
      have hvty := cv_memoVal_ty hok hmv
      obtain ⟨ty, hty1, hty2⟩ := mapOpt_mem hmap (x := args[j]) (by simp)
      obtain ⟨m, rfl, hm⟩ := cv_bvWidths_mem argTys w' hwid hp ty hty1
      rw [hty2] at hvty
      obtain ⟨xv, rfl⟩ := Val.ty_eq_bv_iff.mp hvty
      have hr : r.toNat = m := hvr.1
      have hm64 : m < 64 := by omega
      have hrm : r.toNat % 18446744073709551616 = r.toNat := Nat.mod_eq_of_lt (by omega)
      have hr64 : r.toNat < 64 := by omega
      simp only [cvNc]
      apply WP.ite; cv_simp0 [opC]
      apply WP.ite; cv_simp0 [opC]
      apply WP.ite; cv_simp0 [opC]
      apply WP.ite; cv_simp0 [opC]
      apply WP.ite; cv_simp0 [opC]
      apply WP.ite; cv_simp0 [opC]
      apply WP.assign; cv_simp0 [hrm, hr64]
      apply K
      refine hR.succ hj hmv (fun vs _ hacc => ?_)
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, cvCcStep, cvVw, cvNv]
      rw [← hacc]
      simp [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hr, hvr.2.2.2]
    · intro acc hR
      obtain ⟨vs, hall, hacc⟩ := hR.all
      have hm := cv_memoVal_list hok hn hl (by simp) hall
      have hty := cv_memoVal_ty hok hm
      rw [ht] at hty
      exact ⟨_, hm, cv_fin_concat hty hw hacc⟩
  · simp at hrt'

end ops

/-- The codes of the n-ary group, as the dispatch test leaves them. -/
def CvNaryC (k : Nat) : Prop :=
  ¬k = 0 → ¬k = 32 → ¬k = 64 → ¬k = 80 → ¬k = 160 → ¬k = 152 → ¬k = 136 → ¬k = 1 → ¬k = 65 →
  k = 57

theorem grpN_spec {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {n : Node} {t : Bcf.Ty} {hdr par w cw : BitVec 32}
    {x y z sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some n) (hop : CvNaryC (opC n.op))
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvN Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC n.op))
        (BitVec.ofNat 32 (tailLen n)) par (BitVec.ofNat 32 (opLo n.op)) (BitVec.ofNat 32 (opHi n.op))
        w cw 0#32 x y z (mW w) sbv acc) s := by
  have hi := h_lv
  obtain ⟨op, args⟩ := n
  cases op <;> simp only [CvNaryC, opC] at hop <;> (try (exfalso; omega))
  case bvAdd => exact grpN_add IH hd h hc hpool hn ht hw hQ
  case bvMul => exact grpN_mul IH hd h hc hpool hn ht hw hQ
  case bvOr => exact grpN_or IH hd h hc hpool hn ht hw hQ
  case bvAnd => exact grpN_and IH hd h hc hpool hn ht hw hQ
  case bvXor => exact grpN_xor IH hd h hc hpool hn ht hw hQ
  case bvConcat => exact grpN_concat IH hd h hc hpool hn ht hw hQ
  case bvFromBool => exact grpN_frombool IH hd h hc hpool hn ht hw hQ
  case conj => exact grpN_conj IH hd h hc hpool hn ht hw hQ
  case disj => exact grpN_disj IH hd h hc hpool hn ht hw hQ
  case boolXor => exact grpN_bxor IH hd h hc hpool hn ht hw hQ

end Vbcf.Proof
