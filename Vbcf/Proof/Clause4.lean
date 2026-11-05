import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Clause3

/-!
# Vbcf proofs: the Clause family, part 4 — `r_reordering`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


section calls
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {es : List Expr} {rest : Stmt}

/-- `x = cl_half(st, e); rest`. -/
theorem WP.rule_cl_half (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (t : Nat)
    (ht : t < 2 * params.length)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv t] ∧
      match env.assign s.mem x (uv (clHalfW params t)) with
      | none => False
      | some env' => WP Vbcf.prog rest Q env' s) :
    WP Vbcf.prog (.seq (.call (some x) "cl_half" es) rest) Q env s := by
  apply WP.call_seq (cl_half_spec W sb X c0 c prems params st t) H.1 ⟨rfl, h, hR, ht⟩
  rintro rv s' ⟨rfl, rfl⟩
  exact H.2

/-- `x = cl_byte(st, e); rest`. -/
theorem WP.rule_cl_byte (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (k : Nat)
    (hk : k < 4 * params.length)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv k] ∧
      match env.assign s.mem x (uv (paramByte params k)) with
      | none => False
      | some env' => WP Vbcf.prog rest Q env' s) :
    WP Vbcf.prog (.seq (.call (some x) "cl_byte" es) rest) Q env s := by
  apply WP.call_seq (cl_byte_spec W sb X c0 c prems params st k) H.1 ⟨rfl, h, hR, hk⟩
  rintro rv s' ⟨rfl, rfl⟩
  exact H.2

end calls

theorem clHalfW_lt (params : List Nat) (t : Nat) : clHalfW params t < 65536 := by
  unfold clHalfW
  rw [show (0xffff : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem clSwapStep_eq (params : List Nat) (a : Array Nat) (t : Nat) :
    clSwapStep params a t =
      a.swapIfInBounds (clHalfW params t % 256) (clHalfW params t / 256 % 256) := by
  unfold clSwapStep
  rw [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- Swapping two entries of the list on the stack. -/
theorem StkTop.swap {c c2 : CMem} {st : VSt} {a : Array Nat} {j k : Nat}
    (ht : StkTop c st 0 a.toList) (hj : j < a.size) (hk : k < a.size) (hsp : c2.k.sp = c.k.sp)
    (hcells : ∀ m, c2.stk[m]? = if m = k then c.stk[j]? else if m = j then c.stk[k]? else c.stk[m]?) :
    StkTop c2 st 0 (a.swapIfInBounds j k).toList := by
  refine ⟨by rw [hsp, ht.1]; simp, ?_⟩
  intro m i hm
  have hml : m < a.size := by simpa using lt_length_of_getElem? hm
  rw [Array.swapIfInBounds_def, dite_eq_left hj, dite_eq_left hk, Array.getElem?_toList,
    Array.getElem?_swap] at hm
  have hc : ∀ q (hq : q < a.size), c.stk[q]? = some (uv (st.id a[q])) := by
    intro q hq
    have := ht.cell (j := q) (by simpa using hq)
    simpa using this
  have hl : ∀ q (hq : q < a.size), st.lv a[q] := by
    intro q hq
    have := ht.lt_size (j := q) (by simpa using hq)
    simpa using this
  unfold U
  rw [Nat.zero_add, hcells m]
  by_cases h1 : k = m
  · subst h1
    rw [ite_eq_left rfl] at hm
    cases hm
    rw [ite_eq_left rfl]
    exact ⟨hl j hj, hc j hj⟩
  · rw [ite_eq_right h1] at hm
    by_cases h2 : j = m
    · subst h2
      rw [ite_eq_left rfl] at hm
      cases hm
      rw [ite_eq_right (fun e => h1 e.symm), ite_eq_left rfl]
      exact ⟨hl k hk, hc k hk⟩
    · rw [ite_eq_right h2, Array.getElem?_eq_getElem hml] at hm
      cases hm
      rw [ite_eq_right (fun e => h1 e.symm), ite_eq_right (fun e => h2 e.symm)]
      exact ⟨hl m hml, hc m hml⟩

/-- After the padding check: the padding half-word is zero when there is one. -/
def SwMid (s : (KernelState prog State)) (P : Prop) (env0 env' : Env) (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ P ∧ ∃ a, env' = env0.set "sw" (.u32 a)

/-- Loop invariant of `r_reordering`: the first `t - 1` swaps are done on the stack. -/
def ReoInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (p : Nat) (params : List Nat)
    (args : Array Nat) (cnt : Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (t : Nat) (a1 a2 a3 a4 a5 : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv 1),
      ("na", .u32, uv params.length), ("p", .u32, uv (st.id p)),
      ("n", .u32, uv args.size), ("cnt", .u32, uv cnt), ("vec", .u32, uv ((cnt + 1) * 2)),
      ("t", .u32, uv t), ("sw", .u32, .u32 a1), ("j", .u32, .u32 a2), ("k", .u32, .u32 a3),
      ("x", .u32, .u32 a4), ("base", .u32, .u32 0#32), ("ok", .u32, .u32 a5),
      ("r", .u32, .u32 0#32)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 [p] params c' st ∧ 1 ≤ t ∧ t ≤ cnt + 1 ∧
    (∀ t', 1 ≤ t' → t' < t →
      clHalfW params t' % 256 < args.size ∧ clHalfW params t' / 256 % 256 < args.size) ∧
    StkTop c' st 0 (clSwaps params args (t - 1)).toList

theorem r_reordering_spec :
    RuleSpec (State := State) "r_reordering" (fun _ st pr pa => ruleReordering st pr pa) := by
  rule_begin rReordering
  rcases prems with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rule_guard
  rotate_left
  · rule_guard
    intro h0
    simp at hnp
    rw [uv_inj (by omega) (by omega)] at h0
    simp at h0
  rule_guard
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  apply WP.ite_seq
  rule_simp [hR.core.rdHdr hn]
  refine ⟨fun hop => ?_, fun hop => ?_⟩
  · rule_ret
    exact hR.ret h hp (by
      obtain ⟨op, args⟩ := n
      simp only at hop
      cases op <;> simp_all [ruleReordering, St.node, isDisjNode])
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rule_ret
    exact hR.ret h hp (by
      have : params = [] := by
        cases params with
        | nil => rfl
        | cons _ _ => simp at h0
      subst this
      simp [ruleReordering, St.node, hn, isDisjNode])
  have hpl : 0 < params.length := by
    cases params with
    | nil => simp at h0
    | cons _ _ => simp
  rule_assign [hR.core.rdN hn]
  apply WP.rule_cl_half h hR 0 (by omega)
  refine ⟨by rule_simp, ?_⟩
  have hc16 := clHalfW_lt params 0
  rule_simp
  rule_guard
  intro hcnt
  rule_assign [cw_mul]
  rule_guard [cw_div]
  intro hvec
  generalize hcd : clHalfW params 0 = cnt at hcnt hvec hc16 ⊢
  apply WP.seq_mid_env (SwMid s ((cnt + 1) * 2 % 4 ≠ 0 → clHalfW params (cnt + 1) = 0))
  · apply WP.ite
    rule_simp [cw_mod]
    refine ⟨fun hodd => ?_, fun hev => ?_⟩
    · have hc2 := clHalfW_lt params (cnt + 1)
      apply WP.rule_cl_half h hR (cnt + 1) (by omega)
      refine ⟨by rule_simp, ?_⟩
      rule_simp
      apply WP.ite
      rule_simp [uv_eq_zero_iff, clHalfW_lt]
      refine ⟨fun hne => WP.rule_fail h, fun hz => WP.skip ?_⟩
      exact ⟨rfl, fun _ => hz, _, rfl⟩
    · apply WP.skip
      exact ⟨rfl, fun h1 => absurd hev h1, 0#32, by simp [Env.set]⟩
  rintro env' s2 ⟨rfl, hpad, a, rfl⟩
  rule_assign [hsp]
  apply WP.rule_push_args h hR p hn (show ¬ IsLeaf Op.disj by decide) (StkTop.nil (c := c) (st := st) (base := 0) (by simp [hsp]))
  refine ⟨by rule_simp, ?_⟩
  intro s3 c3 ok h3 hR3 hok
  clear h hR
  have h := h3
  have hR := hR3
  clear h3 hR3
  rule_simp
  rule_guard
  intro hok0
  rcases hok with rfl | ⟨rfl, htop⟩
  · simp at hok0
  rule_assign
  apply WP.loop_seq (ReoInv W sb X c st p params args cnt)
  · exact ⟨c3, 1, _, _, _, _, _, rfl, h, hR, Nat.le_refl _, by omega, fun t' h1 h2 => by omega,
      by simpa [clSwaps_zero] using htop⟩
  clear h hR htop
  rintro env s4 ⟨c4, t, a1, a2, a3, a4, a5, rfl, h, hR, ht1, ht2, hin, htop⟩
  rule_simp
  refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · -- the result
    have ht : t = cnt + 1 := by omega
    subst ht
    simp only [Nat.add_sub_cancel] at htop
    have hsz' : (clSwaps params args cnt).toList.length = args.size := by simp [clSwaps_size]
    apply WP.rule_mkn mkn_specT h hR .disj 65#32 0 (clSwaps params args cnt).toList htop.2
      (by have := htop.1; omega)
    refine ⟨by rule_simp [hsz'], ?_⟩
    intro s5 c5 r h hB
    rule_simp
    rule_ret
    refine hB.ret h (fun st' i hP => ?_)
    have hsw : applySwaps params args = some (clSwaps params args cnt) := by
      rw [← hcd]
      refine applySwaps_eq_fold (by omega) (by omega) (by rw [hcd]; exact hpad) ?_
      intro t' h1 h2
      have := hin t' h1 (by omega)
      rw [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
      exact this
    have hperm := clSwaps_perm params args cnt
    simp only [ruleReordering, St.node, hn, Option.bind_some, isDisjNode, List.isEmpty_iff, h0,
      ite_false, hsw, cl_subsetB_perm hperm, cl_subsetB_perm hperm.symm, and_self, ite_true, mkDisj]
    simpa using hP
  · have hht := clHalfW_lt params t
    apply WP.rule_cl_half h hR t (by omega)
    refine ⟨by rule_simp, ?_⟩
    rule_simp
    rule_assign
    rule_assign [cw_shr (show clHalfW params t < 4294967296 by omega)]
    rule_guard
    intro hjk hk2
    have hAs : (clSwaps params args (t - 1)).size = args.size := clSwaps_size _ _ _
    have hspA : c4.k.sp.toNat = args.size := by have := htop.1; simpa [hAs] using this
    have hsz2 : args.size ≤ 2147483648 := by
      have := hR.sp_lt; simp only [maxPool] at this; omega
    generalize hjj : clHalfW params t % 256 = jj at hjk ⊢
    generalize hkk : clHalfW params t / 256 % 256 = kk at hk2 ⊢
    generalize hA : clSwaps params args (t - 1) = A at htop hAs
    have hstk := hR.stk_eq h (by omega)
    have hssz := hR.stk_size h (by omega)
    have hcj : c4.stk[jj]? = some (uv (st.id (A[jj]'(by omega)))) := by
      have := htop.cell (j := jj) (by simp; omega)
      simpa only [Array.getElem_toList, Nat.zero_add] using this
    have hck : c4.stk[kk]? = some (uv (st.id (A[kk]'(by omega)))) := by
      have := htop.cell (j := kk) (by simp; omega)
      simpa only [Array.getElem_toList, Nat.zero_add] using this
    rule_assign [hstk, h.rd_stk hstk, rd_u32 hcj]
    apply WP.seq
    apply WP.ck_store .stk h (by rfl) hstk
    ck_simp [hstk, h.rd_stk hstk, rd_u32 hck, uv_toNat (show jj < 4294967296 by omega),
      uv_toNat (show kk < 4294967296 by omega)]
    refine ⟨by omega, ?_⟩
    intro s5 h5
    clear h
    have h := h5
    clear h5
    have hR5 := hR.set_stk jj (.u32 (BitVec.ofNat 32 (st.id A[kk])))
    apply WP.seq
    apply WP.ck_store .stk h (by rfl) hstk
    ck_simp [hstk, uv_toNat (show kk < 4294967296 by omega)]
    refine ⟨by omega, ?_⟩
    intro s6 h6
    clear h
    have h := h6
    clear h6
    have hR6 := hR5.set_stk kk (.u32 (BitVec.ofNat 32 (st.id A[jj])))
    apply WP.assign_loop
    rule_simp
    refine ⟨_, t + 1, _, _, _, _, _, rfl, h, hR6, by omega, by omega, ?_, ?_⟩
    · intro t' h1 h2
      rcases Nat.lt_or_ge t' t with h3 | h3
      · exact hin t' h1 h3
      · rw [show t' = t by omega, hjj, hkk]; exact ⟨hjk, hk2⟩
    · rw [show t + 1 - 1 = (t - 1) + 1 by omega, clSwaps_succ, clSwapStep_eq,
        show t - 1 + 1 = t by omega, hA, hjj, hkk]
      refine StkTop.swap htop (by omega) (by omega) rfl (fun m => ?_)
      simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
      by_cases e1 : kk = m
      · subst e1; simp [hcj, show kk < c4.stk.size by omega]
      · by_cases e2 : jj = m
        · subst e2; simp [e1, Ne.symm e1, hck, show jj < c4.stk.size by omega]
        · simp [e1, e2, Ne.symm e1, Ne.symm e2]

end Vbcf.Proof
