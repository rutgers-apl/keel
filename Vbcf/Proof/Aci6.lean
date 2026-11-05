import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Aci5

/-!
# Vbcf proofs: the Aci family, part 6 — `aci_nf`

`aci_nf(st, i)` returns 0 when `aciNF pool i = none`, and 1 with the leaf list of
`aciNF pool i = some (op, L)` pushed on the stack; anything else (`NOID`) is a rejection.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


theorem aci_sortNat_sorted (L : List Nat) : (sortNat L).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) L
  exact this.imp (fun h => by simpa using h)

/-- The leaf list `L'` the C computes for the normal form `(op, L)`: a permutation of `L`
(the C sorts by id, the Lean checker by index), and `L` itself for a concatenation
(which is not sorted). -/
def AciRep (op : Op) (L L' : List Nat) : Prop :=
  L'.Perm L ∧ (isConcatOp op = true → L' = L)

/-- What `aci_nf` guarantees about the final state for the returned word `r`. -/
def AciNfR (st : VSt) (i base : Nat) (A : List Nat) (r : BitVec 32) (c' : CMem) : Prop :=
  (r = 0#32 → aciNF st.pool i = none ∧ StkTop c' st base A) ∧
  (r ≠ 0#32 → r ≠ 4294967295#32 → ∃ op L L', aciNF st.pool i = some (op, L) ∧
    AciRep op L L' ∧ StkTop c' st base (A ++ L'))

/-- A list strictly sorted by an injective key is duplicate-free. -/
theorem aci_nodup_of_key {f : Nat → Nat} {U : List Nat} (hs : U.Pairwise (fun a b => f a < f b)) :
    U.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (hs.imp (fun h e => by subst e; omega))

/-- A duplicate-free list with the elements of `L` is a permutation of `sortNat (dedupNat L)`. -/
theorem aci_perm_dedup {U L : List Nat} (hU : U.Nodup) (hm : ∀ x, x ∈ U ↔ x ∈ L) :
    U.Perm (sortNat (dedupNat L)) := by
  have hp1 := sortNat_perm (dedupNat L)
  have hnd : (sortNat (dedupNat L)).Nodup := hp1.nodup_iff.mpr (aci_dedup_nodup L)
  refine (List.perm_ext_iff_of_nodup hU hnd).mpr (fun x => ?_)
  rw [hm, hp1.mem_iff, mem_dedupNat]

def AciNfSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (i base : Nat) (A : List Nat),
    FnSpec (State := State) Vbcf.prog "aci_nf"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv i ∧ StkTop c st base A)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        AciRet W sb X c0 prems params st (AciNfR st i base A) r s')

/-- A call of a `void` function followed by more statements. -/
theorem WP.aci_call_void {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {f : String}
    {args : List Expr} {rest : Stmt} {vs : List EmbC.Val}
    {pre : List EmbC.Val → (KernelState P State) → Prop} {post : List EmbC.Val → (KernelState P State) → Option EmbC.Val → (KernelState P State) → Prop}
    (hspec : FnSpec (State := State) P f pre post)
    (hargs : evalArgs P env s.mem args = some vs) (hpre : pre vs s)
    (H : ∀ rv s', post vs s rv s' → WP P rest Q env s') :
    WP P (.seq (.call none f args) rest) Q env s := by
  apply WP.seq
  apply WP.call hspec
  rw [hargs]
  exact ⟨hpre, fun rv s' hp => H rv s' hp⟩

theorem aci_nf_spec : AciNfSpec (State := State) := by
  intro W sb X c0 c prems params st i base A
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciNf) rfl
  rintro vs s ⟨rfl, h, hR, hi, htop⟩
  simp [aciNf, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := aciNf) rfl
  simp only [aciNf, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨n, hn⟩ := node_of_lv hi
  have hf := hR.core.rep.fits i n hn
  rule_assign [hR.core.rdHdr hn]
  apply WP.call_seq (aci_assoc_spec n) (by rule_simp) rfl
  rintro rv s1 ⟨rfl, rfl⟩
  rule_simp
  apply WP.guard_lit
  by_cases ha : isAssocOp n.op = false
  · rule_simp [ha]
    exact ⟨c, h, hR, fun _ => ⟨by simp [aciNF, hn, ha], htop⟩, by simp⟩
  replace ha : isAssocOp n.op = true := by simpa using ha
  rule_simp [ha]
  have hl : ¬ IsLeaf n.op := by
    revert ha; cases n.op <;> simp [isAssocOp, IsLeaf, isLeaf]
  have hb := htop.1
  have hspw : c.k.sp = BitVec.ofNat 32 (base + A.length) := by
    rw [← bv_ofNat_toNat c.k.sp, hb]
  rule_assign [hspw]
  apply WP.call_seq (aci_flat_spec 32#32 W sb X c0 c prems params st n.op i base A)
    (by rule_simp [aci_hdr_mask hf]) ⟨rfl, h, hR, hi, hl, hf.lo, hf.hi, htop⟩
  rintro rv s2 ⟨r2, rfl, c2, h2, hR2, hr2⟩
  clear h hR htop
  have h := h2
  have hR := hR2
  clear h2 hR2
  rule_simp
  apply WP.ifRet
  rule_simp
  refine ⟨fun he => ⟨c2, h, hR, by simp, by simp⟩, fun hne => ?_⟩
  have htop := hr2 hne
  clear hr2
  rule_assign [hR.core.rdHdr hn]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun w hw => ⟨c2, h, hR, by simp, fun _ _ => ?_⟩, fun hc => ?_⟩
  · exact ⟨n.op, _, _, by simp [aciNF, hn, aciLeaves, hw, isConcatOp, isAssocOp],
      ⟨List.Perm.refl _, fun _ => rfl⟩, htop⟩
  have hnc : isConcatOp n.op = false := by
    cases e : isConcatOp n.op
    · rfl
    · obtain ⟨w, hw⟩ := (isConcatOp_iff _).mp e
      exact absurd hw (hc w)
  generalize hL : flatten st.pool n.op i = L at htop
  have hsp2 := htop.1
  simp only [List.length_append] at hsp2
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hspw2 : c2.k.sp = BitVec.ofNat 32 (base + A.length + L.length) := by
    rw [← bv_ofNat_toNat c2.k.sp, hsp2]; congr 1; omega
  have hsub : BitVec.ofNat 32 (base + A.length + L.length) - BitVec.ofNat 32 (base + A.length) =
      BitVec.ofNat 32 L.length := by
    rw [cw_sub (by omega) (by omega)]; congr 1; omega
  rule_assign [hspw2, hsub]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hbig => ?_, fun hsmall => ?_⟩
  · apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s3 h3
    apply WP.ret
    simp only [evalE, LoopQ, RetQ]
    exact ⟨_, h3, hR.aci_err _, by simp, by simp⟩
  -- `if (base > MAX_POOL) …` and `if (st->sp < base) …`: never taken, checked for the cost proof
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hbig => ?_, fun hsmall => ?_⟩
  · apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s3 h3
    apply WP.ret
    simp only [evalE, LoopQ, RetQ]
    exact ⟨_, h3, hR.aci_err _, by simp, by simp⟩
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hbig => ?_, fun hsmall => ?_⟩
  · apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s3 h3
    apply WP.ret
    simp only [evalE, LoopQ, RetQ]
    exact ⟨_, h3, hR.aci_err _, by simp, by simp⟩
  -- `r = spend(st, n * (n - 1) / 2);`
  apply WP.rule_spend h hR
  rule_simp
  intro s2' wk2 er2 r2 h _
  have hR := hR.wev (wk := wk2) (er := er2) (vl := c2.k.val)
  have htop := htop.wev (wk := wk2) (er := er2) (vl := c2.k.val)
  apply WP.ifRet
  rule_simp
  refine ⟨fun he => ⟨_, h, hR, by simp, by simp⟩, fun hne => ?_⟩
  apply WP.aci_call_void (aci_sort_spec W sb X c0 _ prems params st base A L) (by rule_simp)
    ⟨rfl, h, hR, htop⟩
  rintro rv s3 ⟨c3, h3, hR3, L', hL'p, hL's, htop3⟩
  clear h hR htop
  have h := h3
  have hR := hR3
  clear h3 hR3
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hx => ?_, fun w hw => ?_⟩
  · apply WP.call (aci_uniq_spec W sb X c0 c3 prems params st base A L')
    rule_simp
    refine ⟨⟨h, hR, htop3, hL's⟩, ?_⟩
    rintro s4 ⟨c4, U, h4, hR4, htop4, hU, hUm⟩
    apply WP.ret
    simp only [evalE, RetQ]
    refine ⟨c4, h4, hR4, by simp, fun _ _ => ⟨n.op, sortNat (dedupNat L), U, ?_,
      ⟨aci_perm_dedup (aci_nodup_of_key hU) (fun x => by rw [hUm, hL'p.mem_iff]),
        fun e => by rw [hnc] at e; cases e⟩, htop4⟩⟩
    have hid : isIdemOp n.op = true := by
      revert ha hnc hx; cases n.op <;> simp [isAssocOp, isConcatOp, isIdemOp]
    simp [aciNF, hn, ha, aciLeaves, hnc, hid, hL]
  · apply WP.ret
    simp only [evalE, RetQ]
    refine ⟨c3, h, hR, by simp, fun _ _ => ⟨n.op, sortNat L, L', ?_,
      ⟨hL'p.trans (sortNat_perm L).symm, fun e => by rw [hnc] at e; cases e⟩, htop3⟩⟩
    rw [hw] at hL
    simp [aciNF, hn, hw, aciLeaves, isConcatOp, isIdemOp, isAssocOp, hL]

end Vbcf.Proof
