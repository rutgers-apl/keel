import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly8
import Vbcf.Proof.PolyRen

/-!
# Vbcf proofs: the Poly family, part 9 — `r_poly_norm`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- Every word of an encoded form fits 32 bits. -/
theorem plTerms_lt {w : Nat} {pool : Pool} (hw : w ≤ 64)
    (hoff : ∀ a, a < pool.size → offs pool a < 2 ^ 32) :
    ∀ {ts : List (Nat × BitVec w)}, LinOK pool ts → ∀ x ∈ plTerms pool ts, x < 2 ^ 32
  | [], _, x, hx => by simp at hx
  | t :: ts, hok, x, hx => by
    have h1 := hoff t.1 hok.head
    have h2 := pl_toNat_lt hw t.2
    simp only [plTerms_cons, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact h1
    · omega
    · omega
    · exact plTerms_lt hw hoff hok.tail x hx

theorem plEnc_lt {w : Nat} {pool : Pool} (hw : w ≤ 64)
    (hoff : ∀ a, a < pool.size → offs pool a < 2 ^ 32) {L : Lin w} (hok : LinOK pool L.terms) :
    ∀ x ∈ plEnc pool L, x < 2 ^ 32 := by
  intro x hx
  have h2 := pl_toNat_lt hw L.const
  simp only [plEnc, plW, List.cons_append, List.nil_append, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · omega
  · omega
  · exact plTerms_lt hw hoff hok x hx

/-- The comparison loop of `r_poly_norm`: the first `t` words are equal. -/
def PlPnInv (sb : Nat) (s : (KernelState prog State)) (e a b w base mid n ok : Nat) (A B : List Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  s' = s ∧ ∃ t, env = [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("np", .u32, uv 0), ("na", .u32, uv 1),
      ("e", .u32, uv e), ("a", .u32, uv a), ("b", .u32, uv b), ("w", .u32, uv w),
      ("base", .u32, uv base), ("mid", .u32, uv mid), ("n", .u32, uv n), ("i", .u32, uv t),
      ("ok", .u32, uv ok)] ∧ t ≤ n ∧ ∀ j, j < t → A[j]? = B[j]?

theorem r_poly_norm_spec :
    RuleSpec (State := State) "r_poly_norm" (fun X st pr pa => rulePolyNorm X.ei st pr pa) := by
  rule_begin rPolyNorm
  rule_arity rfl ⟨pe, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR pe hx
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
  obtain ⟨na, hna⟩ := node_of_lv ha
  apply WP.rule_ty_of ty_of_spec
  obtain ⟨t, ht, hty, hfit⟩ := hR.core.tyOf hna
  rule_simp [hR.core.rdHdr hna, hty]
  cases t with
  | bool => rule_guard
  | list e' k' =>
    simp only [TyFits] at hfit
    rule_guard [tyW_list]
    intro _ hle
    exfalso
    split at hle <;> omega
  | bv w =>
  simp only [TyFits] at hfit
  rule_guard
  intro hw0 hw64
  have hw1 : 1 ≤ w := by omega
  rule_assign [hsp]
  apply WP.pl_call (lin_f_spec 32#32 W sb X c c [] [pe] st w (st.σ a)) (by rule_simp [VSt.id])
    ⟨rfl, h, hR, st.σ_lt ha, hw1, hw64⟩
  intro s1 r1 hr1
  clear h
  obtain ⟨c1, h, hR1, hpre1, hcase1⟩ := hr1
  rcases hcase1 with rfl | ⟨rfl, hst1⟩
  · rule_simp; rule_guard
  rule_simp
  rule_guard
  have hsp1 := hst1.1
  have hsp1' : c1.k.sp.toNat = (plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ a))).length := by
    rw [hsp1, hsp]; simp
  have hspw1 : c1.k.sp = BitVec.ofNat 32 ((plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ a))).length) := by
    rw [← hsp1']; exact (bv_ofNat_toNat _).symm
  rule_assign [hspw1]
  apply WP.pl_call (lin_f_spec 32#32 W sb X c c1 [] [pe] st w (st.σ b)) (by rule_simp [VSt.id])
    ⟨rfl, h, hR1, st.σ_lt hb, hw1, hw64⟩
  intro s2 r2 hr2
  clear h
  obtain ⟨c2, h, hR2, hpre2, hcase2⟩ := hr2
  rcases hcase2 with rfl | ⟨rfl, hst2⟩
  · rule_simp; rule_guard
  rule_simp
  rule_guard
  rule_assign
  have hLA := plEnc_length (pool := st.cs.pool) (Bcf.lin st.cs.pool w (st.σ a))
  have hLB := plEnc_length (pool := st.cs.pool) (Bcf.lin st.cs.pool w (st.σ b))
  have hspmax := hR2.sp_lt
  simp only [maxPool] at hspmax
  have hsp2 := hst2.1
  rw [hsp1'] at hsp2 hst2
  have hspw2 : c2.k.sp = BitVec.ofNat 32 ((plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ a))).length +
      (plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ b))).length) := by
    rw [← hsp2]; exact (bv_ofNat_toNat _).symm
  rw [hLA, hLB] at hspw2
  rule_guard [hspw2, cw_sub (show 2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length +
    (2 + 3 * (Bcf.lin st.cs.pool w (st.σ b)).terms.length) < 4294967296 by omega)
    (show 2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length ≤ 2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length +
    (2 + 3 * (Bcf.lin st.cs.pool w (st.σ b)).terms.length) by omega)]
  intro hlen
  have hokA := lin_ok (w := w) hR.pl_args (st.σ_lt ha)
  have hokB := lin_ok (w := w) hR.pl_args (st.σ_lt hb)
  have hoff : ∀ x, x < st.cs.pool.size → offs st.cs.pool x < 2 ^ 32 := fun x hx => by
    have := hR.core.cinv.off_lt hx; omega
  have hltA := plEnc_lt hw64 hoff hokA
  have hltB := plEnc_lt hw64 hoff hokB
  have hA : WordsAt c2.stk 0 (plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ a))) := by
    have := hst1.2.plFrame (fun j hj => hpre2 j (by rw [hsp1']; omega))
    rwa [hsp] at this
  have hB := hst2.2
  rw [hLA] at hB
  -- `ok = spend(st, n);`
  apply WP.rule_spend h hR2
  rule_simp
  intro s2 wk2 er2 ok2 h hok01
  have hR2 := hR2.wev (wk := wk2) (er := er2) (vl := c2.k.val)
  rw [show c2.stk = (c2.wev wk2 er2 c2.k.val).stk from rfl] at hA
  rw [show c2.stk = (c2.wev wk2 er2 c2.k.val).stk from rfl] at hB
  rw [show c2.k.sp = (c2.wev wk2 er2 c2.k.val).k.sp from rfl] at hsp2
  rw [show c2.k.sp = (c2.wev wk2 er2 c2.k.val).k.sp from rfl] at hspw2
  rw [show c2.k.sp = (c2.wev wk2 er2 c2.k.val).k.sp from rfl] at hspmax
  generalize c2.wev wk2 er2 c2.k.val = c2 at h hR2 hA hB hsp2 hspw2 hspmax
  rule_guard
  intro hok2
  obtain rfl : ok2 = 1#32 := by
    rcases hok01 with h0 | h1
    · exact absurd h0 hok2
    · exact h1
  have hstk2 := hR2.stk_eq h (by omega)
  apply WP.loop_seq (PlPnInv sb s2 (st.id e) (st.id a) (st.id b) w 0
    (2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length) (2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length) 1
    (plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ a))) (plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ b))))
  · exact ⟨rfl, 0, by simp, by omega, fun j hj => by omega⟩
  rintro env s3 ⟨rfl, t, rfl, htn, heq⟩
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- all words equal: `return e;`
    have htn : t = 2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length := by omega
    subst htn
    have hAB : plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ a)) = plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ b)) := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < 2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length
      · exact heq j hj
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have hlin := lin_ren st hR.core.cinv.ok hw1 ha hb (plEnc_inj hw64 hokA hokB hAB)
    rule_ret
    exact hR2.ret h he (by simp [rulePolyNorm, St.node, hn, isEqNode, hee, ht, hlin])
  have hta : t < (plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ a))).length := by omega
  have htb : t < (plEnc st.cs.pool (Bcf.lin st.cs.pool w (st.σ b))).length := by omega
  have ra := hA.plGet hta
  have rb := hB.plGet htb
  simp only [Nat.zero_add] at ra
  have hxa := hltA _ (List.getElem_mem hta)
  have hxb := hltB _ (List.getElem_mem htb)
  rule_guard [hstk2, rd_u32 ra, rd_u32 rb, uv_toNat (show t < 4294967296 by omega),
    uv_toNat (show 2 + 3 * (Bcf.lin st.cs.pool w (st.σ a)).terms.length + t < 4294967296 by omega)]
  intro hne
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, t + 1, by simp, by omega, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j t with hjt | hjt
  · exact heq j hjt
  · rw [show j = t by omega, List.getElem?_eq_getElem hta, List.getElem?_eq_getElem htb, hne]

end Vbcf.Proof
