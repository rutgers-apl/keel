import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly9
import Vbcf.Proof.PolyRen

/-!
# Vbcf proofs: the Poly family, part 10 — `odd_mul_sub`, `r_poly_norm_eq`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- What `odd_mul_sub(st, m)` returns: `NOID`, or the id of a subtraction node `x0 - x1`
for which the Lean `oddMulSub` succeeds with those arguments.  Only `st->val` changes. -/
def PlOmsRes (st : VSt) (m : Nat) (r : BitVec 32) : Prop :=
  r = 4294967295#32 ∨
  ∃ (si w w' x0 x1 : Nat), Bcf.oddMulSub st m = some (w, x0, x1) ∧
    st.pool[si]? = some ⟨.bvSub w', #[x0, x1]⟩ ∧ st.lv si ∧ r = BitVec.ofNat 32 (st.id si)

/-- `if (cond) { return NOID; } rest` in a helper whose result `NOID` satisfies `R`. -/
theorem WP.pl_guard {Q : (Post prog State)} {R : BitVec 32 → (KernelState prog State) → Prop} [RetsTo Q R] {env : Env} {s : (KernelState prog State)}
    {cond : Expr} {rest : Stmt} {nm : String} (hfail : R 4294967295#32 s)
    (H : match evalE Vbcf.prog env s.mem cond with
      | some (.u32 v) => v = 0 → WP Vbcf.prog rest Q env s
      | _ => False) :
    WP Vbcf.prog (.seq (.ite cond (.ret (some (.named nm 4294967295#32))) .skip) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun _ => ?_, fun he => ?_⟩
    · apply WP.ret
      simp only [evalE]
      exact RetsTo.ret (Q := Q) _ _ _ hfail
    · apply WP.skip
      exact H he
  · exact H.elim

/-- The postcondition of `odd_mul_sub` on its result word. -/
def PlOmsPost (W : World) (sb : Nat) (c : CMem) (st : VSt) (m : Nat) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ vl, Holds W s'.mem sb (c.wev c.k.work c.k.err vl) ∧ PlOmsRes st m r

def PlOddMulSubSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (m : Nat),
    FnSpec (State := State) Vbcf.prog "odd_mul_sub"
      (fun vs s => vs = [.ptr sb 0, uv (st.id m)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv m)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ PlOmsPost W sb c st m r s')

theorem odd_mul_sub_spec : PlOddMulSubSpec (State := State) := by
  intro W sb X c0 c prems params st m
  have hs := prog_ck
  apply FnSpec.intro' (fn := Vbcf.oddMulSub) rfl
  rintro vs s ⟨rfl, h, hR, hm⟩
  simp [Vbcf.oddMulSub, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := Vbcf.oddMulSub) rfl
  simp only [Vbcf.oddMulSub, Stmt.block, initLocals, List.map, Ty.zero]
  have hfail : ∀ s' : (KernelState prog State), Holds W s'.mem sb c → PlOmsPost W sb c st m 4294967295#32 s' :=
    fun s' h' => ⟨c.k.val, by rw [wev_self]; exact h', Or.inl rfl⟩
  obtain ⟨n, hn⟩ := node_of_lv hm
  have hf := hR.core.rep.fits m n hn
  rule_assign [hR.core.rdHdr hn]
  apply WP.pl_guard (hfail s h)
  rule_simp
  intro w hop
  obtain ⟨args, rfl, -, -, hargs⟩ := hR.core.argsN hn hop (by simp [IsLeaf, isLeaf])
  have hrdN := hR.core.rdN hn (by simp [IsLeaf, isLeaf])
  have hsz8 := (hR.core.rep.fits m _ hn).tailLen
  simp only [tailLen] at hsz8
  apply WP.pl_guard (hfail s h)
  rule_simp [hrdN.2.1]
  intro hsz
  obtain ⟨ci, si, rfl⟩ := array_eq_two hsz
  have hci := hargs 0 (by simp)
  have hsi := hargs 1 (by simp)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at hci hsi
  have hrd := hR.core.rd2 hn (by simp [IsLeaf, isLeaf])
  rule_assign [hrd]
  rule_assign [hrd]
  have hlo := hf.lo
  simp only [opLo] at hlo
  apply WP.call_seq (poly_lit_val_spec W sb X c0 c prems params st w (st.σ ci))
    (vs := [.ptr sb 0, uv w, uv (st.id ci)]) (by rule_simp [cv_hdr_par hf, opLo, opHi])
    ⟨rfl, h, hR, st.σ_lt hci, by omega⟩
  rintro rv s1 ⟨r1, rfl, hr1⟩
  have hlr := litVal_ren st (w := w) hR.core.cinv.ok hci
  unfold PlLitRes at hr1
  rw [hlr] at hr1
  rcases hr1 with ⟨rfl, rfl, hnone⟩ | ⟨rfl, kk, vl, hsome, hvl, h1⟩
  · rule_simp
    apply WP.pl_guard (hfail _ h)
    rule_simp
  have hR1 := hR.wev (wk := c.k.work) (er := c.k.err) (vl := vl)
  have hfail1 : PlOmsPost W sb c st m 4294967295#32 s1 := ⟨vl, h1, Or.inl rfl⟩
  generalize hc1 : c.wev c.k.work c.k.err vl = c1 at h1 hR1
  have hval : c1.k.val = vl := by rw [← hc1]; rfl
  clear h hR
  have h := h1
  have hR := hR1
  clear h1 hR1
  rule_simp
  apply WP.pl_guard hfail1
  rule_simp
  obtain ⟨ns, hns⟩ := node_of_lv hsi
  apply WP.pl_guard hfail1
  rule_simp [hR.core.rdHdr hns]
  intro w' hop'
  obtain ⟨x0, x1, rfl, hx0, hx1⟩ := hR.core.args2 hns hop'
  apply WP.pl_guard hfail1
  rule_simp [hR.core.rdHdr hns, hdr_len_bv (hR.core.rep.fits si _ hns), tailLen]
  apply WP.pl_guard hfail1
  rule_simp [hval]
  intro hodd
  apply WP.rule_ret
  rule_simp
  refine ⟨vl, by rw [hc1]; exact h, Or.inr ⟨si, w, w', x0, x1, ?_, hns, hsi, rfl⟩⟩
  have hk : kk.toNat % 2 = 1 := by
    have := congrArg BitVec.toNat hodd
    rw [BitVec.toNat_and] at this
    have e : (1#64).toNat = 2 ^ 1 - 1 := rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
    omega
  simp [Bcf.oddMulSub, St.node, hn, hsome, hns, hk]

/-- `x = odd_mul_sub(st, m); rest`. -/
theorem WP.pl_oms {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
    {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {es : List Expr} {rest : Stmt}
    (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (m : Nat) (hm : st.lv m)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv (st.id m)] ∧
      ∀ s' r vl, Holds W s'.mem sb (c.wev c.k.work c.k.err vl) → PlOmsRes st m r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "odd_mul_sub" es) rest) Q env s := by
  apply WP.pl_call (odd_mul_sub_spec W sb X c0 c prems params st m) H.1 ⟨rfl, h, hR, hm⟩
  rintro s' r ⟨vl, h', hr⟩
  exact H.2 s' r vl h' hr

theorem r_poly_norm_eq_spec :
    RuleSpec (State := State) "r_poly_norm_eq" (fun _ st pr pa => rulePolyNormEq st pr pa) := by
  rule_begin rPolyNormEq
  rule_arity ⟨p, rfl⟩ rfl
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨m0, m1, rfl, hm0, hm1⟩ := hR.core.args2 hn hop
  have hrd := hR.core.rd2 hn
  apply WP.pl_oms h hR m0 hm0
  refine ⟨by rule_simp [hrd], ?_⟩
  intro s1 r1 vl1 h1 hr1
  have hR1 := hR.wev (wk := c.k.work) (er := c.k.err) (vl := vl1)
  generalize c.wev c.k.work c.k.err vl1 = c1 at h1 hR1
  clear h hR
  have h := h1
  have hR := hR1
  clear h1 hR1
  rule_simp
  rule_guard
  intro hne
  rcases hr1 with rfl | ⟨si0, w0, w0', x0, x1, homs0, hns0, hsi0, rfl⟩
  · exact absurd rfl hne
  have hrd1 := hR.core.rd2 hn
  apply WP.pl_oms h hR m1 hm1
  refine ⟨by rule_simp [hrd1], ?_⟩
  intro s2 r2 vl2 h2 hr2
  have hR2 := hR.wev (wk := c1.k.work) (er := c1.k.err) (vl := vl2)
  generalize c1.wev c1.k.work c1.k.err vl2 = c2 at h2 hR2
  clear h hR
  have h := h2
  have hR := hR2
  clear h2 hR2
  rule_simp
  rule_guard
  intro hne'
  rcases hr2 with rfl | ⟨si1, w1, w1', y0, y1, homs1, hns1, hsi1, rfl⟩
  · exact absurd rfl hne'
  have hx0 : st.lv x0 := st.args_lv hsi0 hns0 (by simp)
  have hx1 : st.lv x1 := st.args_lv hsi0 hns0 (by simp)
  have hy0 : st.lv y0 := st.args_lv hsi1 hns1 (by simp)
  have hy1 : st.lv y1 := st.args_lv hsi1 hns1 (by simp)
  have hs0 := hR.core.rd2 hns0 (by simp [IsLeaf, isLeaf])
  have hos1 := hR.core.off_lt hsi1
  have hm1a : (st.id si1 + 1) % 4294967296 = st.id si1 + 1 := Nat.mod_eq_of_lt (by omega)
  have hm1b : (st.id si1 + 2) % 4294967296 = st.id si1 + 2 := Nat.mod_eq_of_lt (by omega)
  apply WP.rule_mk_eq mk_eq_specT h hR x0 x1 hx0 hx1
  refine ⟨by rule_simp [hs0], ?_⟩
  intro s3 c3 r3 h hB
  rule_simp
  rule_guard
  intro hne3
  obtain ⟨st1, e0, hP0, hR, hext, hstk, he0, rfl⟩ := hB.ok hne3
  have hs1 := hR.core.rd2_ext hext hns1 (by simp [IsLeaf, isLeaf])
  apply WP.rule_mk_eq mk_eq_specT h hR y0 y1 (hext.lt hy0) (hext.lt hy1)
  refine ⟨by rule_simp [hs1, hm1a, hm1b], ?_⟩
  intro s4 c4 r4 h hB
  rule_simp
  rule_guard
  intro hne4
  obtain ⟨st2, e1, hP1, hR, hext', hstk', he1, rfl⟩ := hB.ok hne4
  rw [← hext'.id he0]
  apply WP.rule_mk_eq mk_eq_specT h hR e0 e1 (hext'.lt he0) he1
  refine ⟨by rule_simp, ?_⟩
  intro s5 c5 r5 h hB
  rule_simp
  rule_ret
  exact Built.ret hB h (fun st' i hP => by
    simp [rulePolyNormEq, St.node, hn, isEqNode, homs0, homs1, hP0, hP1, hP])

end Vbcf.Proof
