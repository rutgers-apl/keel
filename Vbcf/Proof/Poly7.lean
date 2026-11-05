import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly6

/-!
# Vbcf proofs: the Poly family, part 7 — `lin_f`: the sum
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- The form `lin_f` uses for argument `a` of node `i`. -/
def plG (pool : Pool) (w i a : Nat) : Lin w := if a < i then Bcf.lin pool w a else Lin.atom a

/-- The loop invariant of the sum: arguments `kk..` done. -/
def PlAdInv (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (w i : Nat) (args : Array Nat) (d hdr code nn wn bv : BitVec 32) (k : BitVec 64) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (kk : Nat) (av mid ok : BitVec 32),
    env = plFEnv sb w (offs st.cs.pool i) d hdr code nn wn av bv c.k.sp mid (BitVec.ofNat 32 kk) ok
      (mask64M (BitVec.ofNat 32 w)) k ∧ kk ≤ args.size ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧
    PlStkW c' c.k.sp.toNat (plEnc st.cs.pool
      (((args.toList.drop kk).map (plG st.cs.pool w i)).foldr Lin.add (Lin.ofConst 0)))

/-- After the argument's form has been pushed (before `if (ok == 0)`). -/
def PlAdMid (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (w i : Nat) (d hdr code nn wn av bv base mid iv : BitVec 32) (k : BitVec 64) (c1 : CMem)
    (L : Lin w) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ r, env = plFEnv sb w (offs st.cs.pool i) d hdr code nn wn av bv base mid iv r
      (mask64M (BitVec.ofNat 32 w)) k ∧
    PlRet W sb X c0 prems params st c1 c1.k.sp.toNat (plEnc st.cs.pool L) r s'

theorem pl_drop_pred {α : Type} {l : List α} {kk : Nat} (h : 0 < kk) (hk : kk ≤ l.length) :
    l.drop (kk - 1) = l[kk - 1] :: l.drop kk := by
  rw [List.drop_eq_getElem_cons (by omega)]
  congr 2; omega

section add
variable {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {w i : Nat} {d : BitVec 32} {s : (KernelState prog State)}

theorem lfT1_add (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → LinFSpecD (State := State) d') (hd : d ≠ 0#32)
    {args : Array Nat} (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    (hi : i < st.cs.pool.size) (hn : st.cs.pool[i]? = some ⟨.bvAdd w, args⟩)
    (hf : Fits X.posOf ⟨.bvAdd w, args⟩) (hw1 : 1 ≤ w) (hw64 : w ≤ 64)
    (av bv mid i' ok : BitVec 32) (k : BitVec 64) :
    WP Vbcf.prog plT1 (RetQ (PlRet W sb X c0 prems params st c c.k.sp.toNat
        (plEnc st.cs.pool (Bcf.lin st.cs.pool w i))))
      (plFE sb w st i ⟨.bvAdd w, args⟩ d av bv c.k.sp mid i' ok k) s := by
  have hs := prog_ck
  have hrd := hR.core.cinv.rdN hn (by simp [IsLeaf, isLeaf])
  have hlo := hf.lo
  simp only [opLo] at hlo
  have htl := hf.tailLen
  simp only [tailLen] at htl
  have hoi := hR.core.cinv.off_lt hi
  have hm := mask64M_toNat hw1 hw64
  have hargs : ∀ (kq : Nat) (hk : kq < args.size), args[kq] < st.cs.pool.size :=
    fun kq hk => hR.pl_args i _ hn _ (by simp)
  have hgok : ∀ a, a < st.cs.pool.size → LinOK st.cs.pool (plG st.cs.pool w i a).terms := by
    intro a ha
    unfold plG
    split
    · exact lin_ok hR.pl_args ha
    · exact LinOK.atomL ha
  unfold plT1
  apply WP.ite_seq
  rule_simp [plFE, plFEnv, opC, opLo, opHi]
  unfold plFAdd
  simp only [Stmt.block]
  apply WP.pl_call (lin_push64_spec W sb X c0 c prems params st 0#64) (by rule_simp) ⟨rfl, h, hR⟩
  intro s1 r1 hr1
  clear h
  obtain ⟨c1, h, hR1, hpre1, hcase1⟩ := hr1
  rcases hcase1 with rfl | ⟨rfl, hw1'⟩
  · rule_simp; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c1, h, hR1, hpre1, Or.inl rfl⟩
  rule_simp; apply WP.ite_seq; rule_simp
  rule_assign
  have htl' : tailLen ⟨.bvAdd w, args⟩ = args.size := rfl
  rw [htl']
  apply WP.loop_seq (PlAdInv W sb X c0 c prems params st w i args d
    (BitVec.ofNat 32 (hdrW ⟨.bvAdd w, args⟩)) 0#32 (BitVec.ofNat 32 args.size) (BitVec.ofNat 32 w) bv k)
  · refine ⟨c1, args.size, av, mid, 1#32, rfl, Nat.le_refl _, h, hR1, hpre1, ?_⟩
    rw [List.drop_eq_nil_of_le (by simp)]
    simpa [plEnc, Lin.ofConst] using hw1'
  clear h hR1 hpre1 hw1'
  rintro env s2 ⟨c2, kk, av2, mid2, ok2, rfl, hkk, h, hR, hpre, hst⟩
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  generalize hacc : ((args.toList.drop kk).map (plG st.cs.pool w i)).foldr Lin.add (Lin.ofConst 0) = acc
    at hst
  have hsp2 := hst.1
  simp only [plEnc_length] at hsp2
  rule_simp [plFEnv]
  refine ⟨fun h0 => ?_, fun hpos => ?_⟩
  · -- `return 1;`
    have hk0 : kk = 0 := by omega
    subst hk0
    apply WP.rule_ret; rule_simp
    refine ⟨c2, h, hR, hpre, Or.inr ⟨rfl, ?_⟩⟩
    rw [pl_lin_add hn, ite_eq_left rfl]
    rw [← hacc] at hst
    have e : plG st.cs.pool w i = fun a => if a < i then Bcf.lin st.cs.pool w a else Lin.atom a := rfl
    rw [e] at hst
    simpa using hst
  have hk1 : kk - 1 < args.size := by omega
  have ha := hargs (kk - 1) hk1
  have hoa := hR.core.cinv.off_lt ha
  rule_assign [cw_sub (show kk < 4294967296 by omega) (show 1 ≤ kk by omega)]
  have hrd2 := hR.core.cinv.rdN hn (by simp [IsLeaf, isLeaf])
  rule_assign [hrd2.2.2 (kk - 1) hk1, uv_toNat (show kk - 1 < 4294967296 by omega)]
  have hspw : c2.k.sp = BitVec.ofNat 32 (c.k.sp.toNat + (2 + 3 * acc.terms.length)) := by
    rw [← hsp2]; exact (bv_ofNat_toNat _).symm
  rule_assign [hspw]
  have hga := hgok _ ha
  apply WP.seq_mid (PlAdMid W sb X c0 prems params st w i d (BitVec.ofNat 32 (hdrW ⟨.bvAdd w, args⟩))
    0#32 (BitVec.ofNat 32 args.size) (BitVec.ofNat 32 w) (BitVec.ofNat 32 (offs st.cs.pool args[kk - 1])) bv c.k.sp
    (BitVec.ofNat 32 (c.k.sp.toNat + (2 + 3 * acc.terms.length))) (BitVec.ofNat 32 (kk - 1)) k c2
    (plG st.cs.pool w i args[kk - 1]))
  · apply WP.ite
    rule_simp [offs_lt_iff (Nat.le_of_lt hi)]
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · apply WP.call (IH _ (cv_dec_lt hd) W sb X c0 c2 prems params st w args[kk - 1])
      rule_simp
      refine ⟨⟨h, hR, ha, hw1, hw64⟩, ?_⟩
      rintro rv s3 r3 rfl hr3
      rule_simp [LoopQ]
      refine ⟨r3, rfl, ?_⟩
      simpa [plG, hlt] using hr3
    · apply WP.call (lin_atom_spec W sb X c0 c2 prems params st w args[kk - 1]
        (mask64M (BitVec.ofNat 32 w)))
      rule_simp
      refine ⟨⟨h, hR, hw1, hm⟩, ?_⟩
      rintro rv s3 r3 rfl hr3
      rule_simp [LoopQ]
      refine ⟨r3, rfl, ?_⟩
      simpa [plG, show ¬ args[kk - 1] < i by omega] using hr3
  rintro env3 s3 ⟨r3, rfl, hr3⟩
  clear h
  obtain ⟨c3, h, hR3, hpre3, hcase3⟩ := hr3
  rcases hcase3 with rfl | ⟨rfl, hw3⟩
  · rule_simp [plFEnv]; apply WP.ite_seq; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c3, h, hR3, pl_pre_trans (by omega) hpre3 hpre, Or.inl rfl⟩
  rule_simp [plFEnv]; apply WP.ite_seq; rule_simp
  have hacc_ok : LinOK st.cs.pool acc.terms := by
    rw [← hacc]
    apply LinOK.foldr
    intro q hq
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hq
    have := List.mem_of_mem_drop ha'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem this
    exact hgok _ (hargs j (by simpa using hj))
  apply WP.pl_add h hR3 hw1 hw64 hm hga hacc_ok (PlStkW.push_more hst hpre3 hw3)
  refine ⟨by rule_simp, ?_⟩
  intro s4 r4 hr4
  clear h
  obtain ⟨c4, h, hR4, hpre4, hcase4⟩ := hr4
  rcases hcase4 with rfl | ⟨rfl, hw4⟩
  · rule_simp; apply WP.ite; rule_simp; apply WP.rule_ret; rule_simp [LoopQ]
    exact ⟨c4, h, hR4, pl_pre_trans (Nat.le_refl _) hpre4 (pl_pre_trans (by omega) hpre3 hpre),
      Or.inl rfl⟩
  rule_simp; apply WP.ite; rule_simp; apply WP.skip; simp only [LoopQ]
  refine ⟨c4, kk - 1, _, _, 1#32, rfl, by omega, h, hR4,
    pl_pre_trans (Nat.le_refl _) hpre4 (pl_pre_trans (by omega) hpre3 hpre), ?_⟩
  rw [pl_drop_pred (l := args.toList) (by omega) (by simpa using hkk), List.map_cons, List.foldr_cons,
    hacc]
  simpa using hw4

end add

end Vbcf.Proof
