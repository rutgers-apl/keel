import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Aci6

/-!
# Vbcf proofs: the Aci family, part 7 — `r_aci_norm`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Lean side: `aciEq` -/

section
variable {st : VSt} {a b : Nat}

theorem aci_eq_refl : aciEq st a a = true := by simp [aciEq]

theorem aci_eq_of_nf {op : Op} {L : List Nat} (ha : aciNF st.pool a = some (op, L))
    (hb : aciNF st.pool b = some (op, L)) : aciEq st a b = true := by
  simp [aciEq, ha, hb]

theorem aci_eq_of_red {op : Op} (ha : aciNF st.pool a = some (op, [b])) : aciEq st a b = true := by
  simp [aciEq, aciReduces, ha]

theorem aci_eq_of_red' {op : Op} (hb : aciNF st.pool b = some (op, [a])) : aciEq st a b = true := by
  simp [aciEq, aciReduces, hb]

theorem aci_eq_of_nil {op : Op} {nb : Node} (ha : aciNF st.pool a = some (op, []))
    (hb : st.pool[b]? = some nb) (hnil : isNilElem op nb = true) : aciEq st a b = true := by
  simp [aciEq, aciReduces, ha, St.node, hb, hnil]

theorem aci_eq_of_nil' {op : Op} {na : Node} (hb : aciNF st.pool b = some (op, []))
    (ha : st.pool[a]? = some na) (hnil : isNilElem op na = true) : aciEq st a b = true := by
  simp [aciEq, aciReduces, hb, St.node, ha, hnil]

end

theorem aci_nf_op {pool : Pool} {i : Nat} {n : Node} {op : Op} {L : List Nat}
    (h : aciNF pool i = some (op, L)) (hn : pool[i]? = some n) : op = n.op ∧ isAssocOp n.op = true := by
  unfold aciNF at h
  rw [hn] at h
  simp only at h
  split at h
  · rename_i ha
    simp at h
    exact ⟨h.1.symm, ha⟩
  · cases h

theorem aci_assoc_not_leaf {op : Op} (h : isAssocOp op = true) : ¬ IsLeaf op := by
  revert h; cases op <;> simp [isAssocOp, IsLeaf, isLeaf]

/-- The outcome of one `aci_nf` call inside the rule: `r = 0` and no normal form, or
`r ≠ 0` and the C's leaf list `L'` represents the normal form's leaves `L`. -/
def AciNfOK (st : St) (i : Nat) (r : BitVec 32) (L' : List Nat) : Prop :=
  (r = 0#32 ∧ aciNF st.pool i = none ∧ L' = []) ∨
  (r ≠ 0#32 ∧ ∃ op L, aciNF st.pool i = some (op, L) ∧ AciRep op L L')

/-- The leaves of a commutative normal form are sorted. -/
theorem aci_nf_sorted {pool : Pool} {i : Nat} {op : Op} {L : List Nat}
    (h : aciNF pool i = some (op, L)) (hc : isConcatOp op = false) : L.Pairwise (· ≤ ·) := by
  unfold aciNF at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [aciLeaves, hc, Bool.false_eq_true, ↓reduceIte]
      exact aci_sortNat_sorted _
    · cases h
  · cases h

/-- Two normal forms with the same operator represented by the same C list are equal. -/
theorem aci_rep_eq {pool : Pool} {a b : Nat} {op : Op} {La Lb L' : List Nat}
    (ha : aciNF pool a = some (op, La)) (hb : aciNF pool b = some (op, Lb))
    (rA : AciRep op La L') (rB : AciRep op Lb L') : La = Lb := by
  cases hc : isConcatOp op
  · exact List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun x y _ _ h1 h2 => Nat.le_antisymm h1 h2)
      (aci_nf_sorted ha hc) (aci_nf_sorted hb hc) (rA.1.symm.trans rB.1)
  · rw [← rA.2 hc, ← rB.2 hc]

/-- The environment of `r_aci_norm` after both normal forms are computed. -/
def AciNmEnv (sb pe pa pb : Nat) (ra rb : BitVec 32) (la lb : Nat) (iv rv : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv 0), ("na", .u32, uv 1),
    ("e", .u32, .u32 (BitVec.ofNat 32 pe)), ("a", .u32, uv pa), ("b", .u32, uv pb),
    ("ra", .u32, .u32 ra), ("rb", .u32, .u32 rb), ("ba", .u32, .u32 0#32),
    ("bb", .u32, .u32 (BitVec.ofNat 32 la)), ("la", .u32, .u32 (BitVec.ofNat 32 la)),
    ("lb", .u32, .u32 (BitVec.ofNat 32 lb)), ("i", .u32, .u32 iv), ("r", .u32, .u32 rv)]

/-- The comparison loop of `r_aci_norm`: the first `t` leaves agree. -/
def AciNmLoop (s : (KernelState prog State)) (sb pe pa pb : Nat) (ra rb : BitVec 32) (LA LB : List Nat) : Env → (KernelState prog State) → Prop :=
  fun env' s' => s' = s ∧ ∃ t, env' = AciNmEnv sb pe pa pb ra rb LA.length LB.length (BitVec.ofNat 32 t) 1#32 ∧
    t ≤ LA.length ∧ ∀ j, j < t → LA[j]? = LB[j]?

/-- Between the tests of `r_aci_norm`: only `i` and `r` have changed. -/
def AciNmMid (s : (KernelState prog State)) (sb pe pa pb : Nat) (ra rb : BitVec 32) (la lb : Nat) : Env → (KernelState prog State) → Prop :=
  fun env' s' => s' = s ∧ ∃ iv rv, env' = AciNmEnv sb pe pa pb ra rb la lb iv rv

theorem r_aci_norm_spec :
    RuleSpec (State := State) "r_aci_norm" (fun X st pr pa => ruleAciNorm X.ei st pr pa) := by
  rule_begin rAciNorm
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  rule_assign [hR.core.rd2 hn]
  rule_assign [hR.core.rd2 hn]
  have hres : aciEq st a b = true → ruleAciNorm X.ei st [] [x] = some (st.toSt, e) := by
    intro hq
    simp [ruleAciNorm, hee, St.node, hn, isEqNode, hq]
  apply WP.ifRet
  rule_simp
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · subst hab
    exact hR.ret h he (hres aci_eq_refl)
  obtain ⟨na, hna⟩ := node_of_lv ha
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  have hfa := hR.core.rep.fits a na hna
  have hfb := hR.core.rep.fits b nb hnb
  rule_assign [hsp]
  apply WP.call_seq (aci_nf_spec W sb X c c [] [x] st a 0 []) (by rule_simp)
    ⟨rfl, h, hR, ha, StkTop.nil (by rw [hsp]; rfl)⟩
  rintro rv s1 ⟨ra, rfl, c1, h1, hR1, hra⟩
  clear h hR
  have h := h1
  have hR := hR1
  clear h1 hR1
  rule_simp
  apply WP.ifRet
  rule_simp
  refine ⟨fun hra' => RuleRet.fail h, fun hra' => ?_⟩
  obtain ⟨LA, hLA, htopA⟩ : ∃ LA, AciNfOK st a ra LA ∧ StkTop c1 st 0 LA := by
    by_cases h0 : ra = 0#32
    · exact ⟨[], Or.inl ⟨h0, (hra.1 h0).1, rfl⟩, (hra.1 h0).2⟩
    · obtain ⟨op, L, L', hL, hrep, ht⟩ := hra.2 h0 hra'
      exact ⟨L', Or.inr ⟨h0, op, L, hL, hrep⟩, by simpa using ht⟩
  clear hra
  have hspA := htopA.1
  simp only [Nat.zero_add] at hspA
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hspwA : c1.k.sp = BitVec.ofNat 32 LA.length := by
    rw [← bv_ofNat_toNat c1.k.sp, hspA]
  rule_assign [hspwA]
  -- `r = spend(st, la); if (r == 0) { return NOID; }`
  apply WP.rule_spend h hR
  rule_simp
  intro s1' wk er r1 h hr01
  have hR := hR.wev (wk := wk) (er := er) (vl := c1.k.val)
  have htopA := htopA.wev (wk := wk) (er := er) (vl := c1.k.val)
  have hspwA' : (c1.wev wk er c1.k.val).k.sp = BitVec.ofNat 32 LA.length := hspwA
  (try rule_simp)
  rule_guard
  intro hr1
  obtain rfl : r1 = 1#32 := hr01.resolve_left hr1
  generalize c1.wev wk er c1.k.val = c1 at h hR htopA hspwA'
  rule_assign [hspwA']
  apply WP.call_seq (aci_nf_spec W sb X c c1 [] [x] st b 0 LA) (by rule_simp)
    ⟨rfl, h, hR, hb, htopA⟩
  rintro rv s2 ⟨rb, rfl, c2, h2, hR2, hrb⟩
  clear h hR
  have h := h2
  have hR := hR2
  clear h2 hR2
  rule_simp
  apply WP.ifRet
  rule_simp
  refine ⟨fun hrb' => RuleRet.fail h, fun hrb' => ?_⟩
  obtain ⟨LB, hLB, htop⟩ : ∃ LB, AciNfOK st b rb LB ∧ StkTop c2 st 0 (LA ++ LB) := by
    by_cases h0 : rb = 0#32
    · exact ⟨[], Or.inl ⟨h0, (hrb.1 h0).1, rfl⟩, by simpa using (hrb.1 h0).2⟩
    · obtain ⟨op, L, L', hL, hrep, ht⟩ := hrb.2 h0 hrb'
      exact ⟨L', Or.inr ⟨h0, op, L, hL, hrep⟩, ht⟩
  clear hrb htopA
  have hsp2 := htop.1
  simp only [Nat.zero_add, List.length_append] at hsp2
  have hspmax2 := hR.sp_lt
  simp only [maxPool] at hspmax2
  have hspw2 : c2.k.sp = BitVec.ofNat 32 (LA.length + LB.length) := by
    rw [← bv_ofNat_toNat c2.k.sp, hsp2]
  have hsub : BitVec.ofNat 32 (LA.length + LB.length) - BitVec.ofNat 32 LA.length =
      BitVec.ofNat 32 LB.length := by
    rw [cw_sub (by omega) (by omega)]; congr 1; omega
  rule_assign [hspw2, hsub]
  have hst : ∀ j (hj : j < (LA ++ LB).length), rd c2.stk j = some (uv (st.id (LA ++ LB)[j])) :=
    fun j hj => by simpa using htop.aci_rd hj
  have hlt : ∀ j (hj : j < (LA ++ LB).length), st.lv (LA ++ LB)[j] :=
    fun j hj => htop.lt_size hj
  have hstk : 0 < (LA ++ LB).length → c2.k.stk = some (stkB c2, 0) := fun hp =>
    hR.stk_eq h (by rw [hsp2]; simpa using hp)
  change WP _ _ _ (AciNmEnv sb (st.id e) (st.id a) (st.id b) ra rb LA.length
    LB.length 0#32 1#32) s2
  apply WP.seq_mid (AciNmMid s2 sb (st.id e) (st.id a) (st.id b) ra rb LA.length
    LB.length)
  · apply WP.ite
    rule_simp [AciNmEnv, hR.core.rdHdr hna, hR.core.rdHdr hnb, aci_hdr_mask hfa, aci_hdr_mask hfb]
    refine ⟨fun hra0 hrb0 hops hlen => ?_, fun _ => WP.skip ⟨rfl, _, _, rfl⟩⟩
    obtain ⟨opA, La, hnfa, hrA⟩ := (hLA.resolve_left (fun e => hra0 e.1)).2
    obtain ⟨opB, Lb, hnfb, hrB⟩ := (hLB.resolve_left (fun e => hrb0 e.1)).2
    obtain ⟨rfl, hasA⟩ := aci_nf_op hnfa hna
    obtain ⟨rfl, hasB⟩ := aci_nf_op hnfb hnb
    have hopeq : na.op = nb.op :=
      (aci_opHdr_inj (aci_assoc_not_leaf hasB) hfa.lo hfa.hi hfb.lo hfb.hi).mp hops
    have hexit : ∀ t, t ≤ LA.length → (∀ j, j < t → LA[j]? = LB[j]?) →
        WP Vbcf.prog (Stmt.ite (Expr.bin BinOp.eq (Expr.var "i") (Expr.var "la"))
            (Stmt.ret (some (Expr.var "e"))) Stmt.skip)
          (LoopQ (AciNmMid s2 sb (st.id e) (st.id a) (st.id b) ra rb LA.length
            LB.length) (RuleQ W sb c X (ruleAciNorm X.ei st [] [x])))
          (AciNmEnv sb (st.id e) (st.id a) (st.id b) ra rb LA.length LB.length
            (BitVec.ofNat 32 t) 1#32) s2 := by
      intro t ht heqs
      apply WP.ite
      rule_simp [AciNmEnv]
      refine ⟨fun htl => ?_, fun _ => WP.skip ⟨rfl, _, _, rfl⟩⟩
      have hLL : LA = LB := List.ext_getElem? (fun j => by
        rcases Nat.lt_or_ge j LA.length with hj | hj
        · exact heqs j (by omega)
        · rw [List.getElem?_eq_none hj, List.getElem?_eq_none (by omega)])
      subst hLL
      have hab := aci_rep_eq (hopeq ▸ hnfa) hnfb (hopeq ▸ hrA) hrB
      subst hab
      apply WP.ret
      rule_simp [LoopQ]
      exact hR.ret h he (hres (aci_eq_of_nf (hopeq ▸ hnfa) hnfb))
    apply WP.loop_seq (AciNmLoop s2 sb (st.id e) (st.id a) (st.id b) ra rb LA LB)
    · exact ⟨rfl, 0, rfl, by omega, fun j hj => by omega⟩
    rintro env' s' ⟨hs', t, rfl, ht, heqs⟩
    rw [hs']
    by_cases htl : t < LA.length
    · have hc1 := hst t (by simp; omega)
      have hc2 := hst (LA.length + t) (by simp; omega)
      have hl1 := hlt t (by simp; omega)
      have hl2 := hlt (LA.length + t) (by simp; omega)
      rw [List.getElem_append_left htl] at hc1 hl1
      rw [List.getElem_append_right (by omega)] at hc2 hl2
      simp only [Nat.add_sub_cancel_left] at hc2 hl2
      have hstk' := hstk (by simp; omega)
      rule_simp [AciNmEnv, hstk', hc1, hc2, hR.core.id_inj hl1 hl2]
      refine ⟨fun _ => hexit t ht heqs, fun _ heq => ?_⟩
      apply WP.assign_loop
      rule_simp
      refine ⟨rfl, t + 1, by simp [AciNmEnv], by omega, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j t with hj' | hj'
      · exact heqs j hj'
      · have : j = t := by omega
        subst this
        rw [List.getElem?_eq_getElem htl, List.getElem?_eq_getElem (by omega), heq]
    · have htl' : LA.length ≤ t := by omega
      rule_simp [AciNmEnv, htl']
      exact hexit t ht heqs
  rintro env' s' ⟨hs', iv, rv, rfl⟩
  rw [hs']
  apply WP.seq_mid (AciNmMid s2 sb (st.id e) (st.id a) (st.id b) ra rb LA.length
    LB.length)
  · apply WP.ite
    rule_simp [AciNmEnv]
    refine ⟨fun hra0 => ?_, fun _ => WP.skip ⟨rfl, _, _, rfl⟩⟩
    obtain ⟨opA, La, hnfa, hrA⟩ := (hLA.resolve_left (fun e => hra0 e.1)).2
    obtain ⟨rfl, hasA⟩ := aci_nf_op hnfa hna
    apply WP.ite_seq
    by_cases hl1 : LA.length = 1
    · have hc0 := hst 0 (by simp; omega)
      have hl0 := hlt 0 (by simp; omega)
      rw [List.getElem_append_left (by omega)] at hc0 hl0
      have hstk' := hstk (by simp; omega)
      rule_simp [hl1, hstk', hc0, hR.core.id_inj hl0 hb]
      refine ⟨fun hb0 => ?_, fun _ => ?_⟩
      · apply WP.ret
        rule_simp [LoopQ]
        have : LA = [b] := by
          obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hl1
          subst hy
          simp at hb0
          rw [hb0]
        have hLa : La = [b] := List.perm_singleton.mp (this ▸ hrA.1).symm
        rw [hLa] at hnfa
        exact hR.ret h he (hres (aci_eq_of_red hnfa))
      · apply WP.ite
        rule_simp [hl1]
        exact WP.skip ⟨rfl, _, _, rfl⟩
    · rule_simp [hl1]
      apply WP.ite
      by_cases hl0 : LA.length = 0
      · rule_simp [hl0]
        apply WP.call_seq (aci_nil_spec W sb X c c2 [] [x] st na.op b nb)
          (by rule_simp [hR.core.rdHdr hna, aci_hdr_mask hfa]) ⟨rfl, h, hR, hnb, by vlv, hfa.lo, hfa.hi⟩
        rintro rv s3 ⟨rfl, rfl⟩
        rule_simp
        apply WP.ite
        rule_simp
        refine ⟨fun hnil => ?_, fun _ => WP.skip ⟨rfl, _, _, rfl⟩⟩
        apply WP.ret
        rule_simp [LoopQ]
        have hLa : La = [] := List.nil_perm.mp (List.eq_nil_of_length_eq_zero hl0 ▸ hrA.1)
        rw [hLa] at hnfa
        have hz : isNilElem na.op nb = true := by
          cases e : isNilElem na.op nb
          · simp [e] at hnil
          · rfl
        exact hR.ret h he (hres (aci_eq_of_nil hnfa hnb hz))
      · rule_simp [hl0]
        exact WP.skip ⟨rfl, _, _, rfl⟩
  rintro env' s' ⟨hs', iv, rv, rfl⟩
  rw [hs']
  apply WP.seq_mid (AciNmMid s2 sb (st.id e) (st.id a) (st.id b) ra rb LA.length
    LB.length)
  · apply WP.ite
    rule_simp [AciNmEnv]
    refine ⟨fun hrb0 => ?_, fun _ => WP.skip ⟨rfl, _, _, rfl⟩⟩
    obtain ⟨opB, Lb, hnfb, hrB⟩ := (hLB.resolve_left (fun e => hrb0 e.1)).2
    obtain ⟨rfl, hasB⟩ := aci_nf_op hnfb hnb
    apply WP.ite_seq
    by_cases hl1 : LB.length = 1
    · have hc0 := hst LA.length (by simp; omega)
      have hl0 := hlt LA.length (by simp; omega)
      rw [List.getElem_append_right (by omega)] at hc0 hl0
      simp only [Nat.sub_self] at hc0 hl0
      have hstk' := hstk (by simp; omega)
      rule_simp [hl1, hstk', hc0, hR.core.id_inj hl0 ha]
      refine ⟨fun hb0 => ?_, fun _ => ?_⟩
      · apply WP.ret
        rule_simp [LoopQ]
        have : LB = [a] := by
          obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hl1
          subst hy
          simp at hb0
          rw [hb0]
        have hLb : Lb = [a] := List.perm_singleton.mp (this ▸ hrB.1).symm
        rw [hLb] at hnfb
        exact hR.ret h he (hres (aci_eq_of_red' hnfb))
      · apply WP.ite
        rule_simp [hl1]
        exact WP.skip ⟨rfl, _, _, rfl⟩
    · rule_simp [hl1]
      apply WP.ite
      by_cases hl0 : LB.length = 0
      · rule_simp [hl0]
        apply WP.call_seq (aci_nil_spec W sb X c c2 [] [x] st nb.op a na)
          (by rule_simp [hR.core.rdHdr hnb, aci_hdr_mask hfb]) ⟨rfl, h, hR, hna, by vlv, hfb.lo, hfb.hi⟩
        rintro rv s3 ⟨rfl, rfl⟩
        rule_simp
        apply WP.ite
        rule_simp
        refine ⟨fun hnil => ?_, fun _ => WP.skip ⟨rfl, _, _, rfl⟩⟩
        apply WP.ret
        rule_simp [LoopQ]
        have hLb : Lb = [] := List.nil_perm.mp (List.eq_nil_of_length_eq_zero hl0 ▸ hrB.1)
        rw [hLb] at hnfb
        have hz : isNilElem nb.op na = true := by
          cases e : isNilElem nb.op na
          · simp [e] at hnil
          · rfl
        exact hR.ret h he (hres (aci_eq_of_nil' hnfb hna hz))
      · rule_simp [hl0]
        exact WP.skip ⟨rfl, _, _, rfl⟩
  rintro env' s' ⟨hs', iv, rv, rfl⟩
  rw [hs']
  apply WP.ret
  simp only [evalE]
  exact RuleRet.fail h

end Vbcf.Proof
