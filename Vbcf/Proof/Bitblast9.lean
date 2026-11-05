import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast8

/-!
# Vbcf proofs: the Bitblast family, part 9 — the barrel-shifter stages `bb_lsh_stage`,
`bb_rsh_stage`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


theorem bb_mapIdx_of {f : Nat → Nat → Option Nat} :
    ∀ {j : Nat} {xs L : List Nat}, L.length = xs.length →
    (∀ (k : Nat) (hk : k < xs.length) (hk' : k < L.length), f (j + k) xs[k] = some L[k]) →
    bbMapIdx f j xs = some L
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, _ => by simp at h
  | _, _ :: _, [], h, _ => by simp at h
  | j, x :: xs, y :: L, hl, H => by
    have h0 := H 0 (by simp) (by simp)
    have ih := bb_mapIdx_of (j := j + 1) (xs := xs) (L := L) (by simpa using hl)
      (fun k hk hk' => by
        have := H (k + 1) (by simp; omega) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    simp [bbMapIdx, h0, ih]

section push
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {args : List Expr}

/-- `x = push(st, e);` as the last statement of a block. -/
theorem WP.bb_push_last (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    (H : match evalArgs Vbcf.prog env s.mem args with
      | some [.ptr b o, .u32 v] => b = sb ∧ o = 0 ∧
        ∀ s' c' ok, Holds W s'.mem sb c' → Pushed W X c0 prems params st c v c' ok →
          match env.assign s'.mem x (.u32 ok) with
          | none => False
          | some env' => Q .normal env' s'
      | _ => False) :
    WP Vbcf.prog (.call (some x) "push" args) Q env s := by
  split at H
  · rename_i b o v hargs
    obtain ⟨rfl, rfl, H⟩ := H
    apply WP.call (push_spec W b c v)
    rw [hargs]
    refine ⟨⟨rfl, h, hR.core.stk⟩, ?_⟩
    rintro rv s' ⟨c', h', hok, hfr, hpre, hcase⟩
    have hR' := hR.after_push hfr hok
    rcases hcase with ⟨rfl, hsp⟩ | ⟨rfl, hsp, htop⟩
    · exact H s' c' 0#32 h' ⟨hR', hpre, Or.inl ⟨rfl, hsp⟩⟩
    · refine H s' c' 1#32 h' ⟨hR', hpre, Or.inr ⟨rfl, hsp, ?_, htop⟩⟩
      have h1 := hok.cap
      have h2 := hR.core.stk.cap
      simp only [maxPool] at h1 h2
      rw [hsp, BitVec.toNat_add]
      simp
      omega
  · exact H.elim

end push

/-! ## `bb_lsh_stage` -/

/-- The per-position test of `bbLshStage`. -/
def bbLshF (st : St) (b T : Nat) (pre : List Nat) (j r : Nat) : Bool :=
  match bbIteArgs st r with
  | some (c, inj, _) => c == b && (if j < T then isFalseNode st inj else pre[j - T]? == some inj)
  | none => false

theorem bbLshStage_eq {st : St} {b T : Nat} {res pre : List Nat}
    (hm : bbMapIdx (fun _ r => (bbIteArgs st r).map (·.2.2)) 0 res = some pre)
    (ha : allIdx (bbLshF st b T pre) 0 res = true) : Bcf.bbLshStage st b T res = some pre := by
  unfold Bcf.bbLshStage
  rw [hm]
  exact ite_eq_left ha

/-- `r` is a boolean `ite` node with else-branch `e`. -/
def BbIteE (st : St) (r e : Nat) : Prop := ∃ cc t, st.pool[r]? = some ⟨.boolIte, #[cc, t, e]⟩

theorem bb_mapIdx_ite {st : St} {res L : List Nat} (hL : L.length = res.length)
    (H : ∀ (j : Nat) (hj : j < res.length) (hj' : j < L.length), BbIteE st res[j] L[j]) :
    bbMapIdx (fun _ r => (bbIteArgs st r).map (·.2.2)) 0 res = some L := by
  apply bb_mapIdx_of hL
  intro k hk hk'
  obtain ⟨cc, t, hn⟩ := H k hk hk'
  simp [bb_iteArgs hn]

/-- The first loop of a stage: the pushed list is the else-branches. -/
def BbStage1 (st : St) (res : List Nat) (k : Nat) (L : List Nat) : Prop :=
  L.length = k ∧ ∀ (j : Nat) (hj : j < res.length) (hj' : j < L.length), BbIteE st res[j] L[j]

def BbLshStageSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (bN T rb : Nat) (res : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_lsh_stage"
      (fun vs s => vs = [.ptr sb 0, uv (st.id bN), uv T, uv rb, uv res.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv bN ∧
        T < 2147483648 ∧ BbRange c st rb res)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ BbPush W sb X c0 prems params st c
        (fun L => Bcf.bbLshStage st bN T res = some L) r s')

theorem bb_lsh_stage_spec : BbLshStageSpec (State := State) := by
  intro W sb X c0 c prems params st bN T rb res
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbLshStage) rfl
  rintro vs s ⟨rfl, h, hR, hbN, hT, hr⟩
  simp [bbLshStage, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbLshStage) rfl
  simp only [bbLshStage, Stmt.block, initLocals, List.map, Ty.zero]
  have hrb := hr.bound hR
  rule_assign
  apply WP.bb_loop (fun env0 => BbPushInv W sb X c0 prems params st c env0 "j" ["r", "inj", "ok"]
    res.length (BbStage1 st res))
  · exact ⟨c, 0, [], [0#32, 0#32, 0#32], rfl, by simp [bbSets, Env.set], h, hR,
      fun _ _ => rfl, Nat.le_refl _, by omega, ⟨rfl, fun j _ hj => by simp at hj⟩, StkTop.nil rfl⟩
  clear h hR
  rintro env s' ⟨c', k, L, ws, hws, rfl, h, hR, hpre, hsp, hk, ⟨hL, hLp⟩, htop⟩
  obtain ⟨w1, w2, w3, rfl⟩ := len_shape 3 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  have hr' := hr.frame hpre hsp
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkn : k = res.length := by omega
    subst hkn
    have hspb := hR.bb_sp_le
    rule_assign
    apply WP.bb_loop (fun env1 => BbInv s' env1 "j" ["r", "inj", "ok"] res.length
      (fun j => allIdx (bbLshF st bN T L) j (res.drop j) = true →
        allIdx (bbLshF st bN T L) 0 res = true))
    · exact ⟨rfl, 0, [w1, w2, w3], rfl, by simp [bbSets, Env.set], by omega, fun h => h⟩
    rintro env s'' ⟨rfl, j, ws, hws, rfl, hj, hres⟩
    obtain ⟨v1, v2, v3, rfl⟩ := len_shape 3 hws
    simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
    rule_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · apply WP.rule_ret; rule_simp
      exact ⟨c', h, hR, Or.inr ⟨(bv_ofNat_toNat _).symm, hpre, hsp, L,
        bbLshStage_eq (bb_mapIdx_ite hL hLp) (bb_allIdx_end (by omega) hres), htop⟩⟩
    have hstk := hr'.stk hR h hlt
    have hrj := hr'.lt hlt
    obtain ⟨cc, t, hnj⟩ := hLp j hlt (by omega)
    have hcc := hR.core.bb_arg_lt hnj (x := cc) (by simp)
    have ht := hR.core.bb_arg_lt hnj (x := t) (by simp)
    rule_assign [hstk, hr'.rd hlt]
    apply WP.ifRet
    rule_simp [hR.core.rd3 hnj]
    refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hcb => ?_⟩
    rule_assign [hR.core.rd3 hnj]
    apply WP.seq
    apply WP.ite
    by_cases hjT : j < T
    · rule_simp [hjT]
      obtain ⟨nt, hnt⟩ := node_of_lv ht
      apply WP.ite
      rule_simp [hR.core.rdHdr hnt]
      refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ]; exact BbPush.fail h hR,
        fun hf => ?_⟩
      apply WP.skip
      apply WP.assign_loop
      rule_simp
      refine ⟨rfl, j + 1, [BitVec.ofNat 32 (st.id res[j]), BitVec.ofNat 32 (st.id t), v3],
        rfl, by simp [bbSets, Env.set], by omega,
        bb_allIdx_step (by simpa using hlt) hres ?_⟩
      have hf' := (hR.core.bb_false hnt).mp hf
      simp [bbLshF, bb_iteArgs hnj, hcb, hjT, hf']
    · rule_simp [hjT]
      have hjT' : j - T < L.length := by omega
      have hLj := (htop.2 (j - T) _ (List.getElem?_eq_getElem hjT')).1
      apply WP.ite
      rule_simp [bb_uv_sub (show j < 2 ^ 32 by omega) (show T ≤ j by omega), bb_add_toNat',
        hR.stk_eq h (by have := htop.1; omega), rd_u32 (htop.2 (j - T) _ (List.getElem?_eq_getElem hjT')).2]
      refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ]; exact BbPush.fail h hR,
        fun he => ?_⟩
      apply WP.skip
      apply WP.assign_loop
      rule_simp
      refine ⟨rfl, j + 1, [BitVec.ofNat 32 (st.id res[j]), BitVec.ofNat 32 (st.id t), v3],
        rfl, by simp [bbSets, Env.set], by omega,
        bb_allIdx_step (by simpa using hlt) hres ?_⟩
      simp [bbLshF, bb_iteArgs hnj, hcb, hjT, List.getElem?_eq_getElem hjT', he]
  have hstk := hr'.stk hR h hlt
  have hrk := hr'.lt hlt
  rule_assign [hstk, hr'.rd hlt]
  obtain ⟨nr, hnr⟩ := node_of_lv hrk
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hnr]
  refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hh => ?_⟩
  obtain ⟨cc, t, e, rfl, hcc, ht, he⟩ := hR.core.bb_hdr3 hnr (op := .boolIte) (by decide)
    (by decide) (by decide) (by decide) hh
  apply WP.rule_push h hR
  rule_simp [hR.core.rd3 hnr]
  intro s2 c2 ok hh2 hP
  obtain ⟨hpre2, hsp2⟩ := hP.bb_pre
  have hpre' : ∀ j, j < c.k.sp.toNat → c2.stk[j]? = c.stk[j]? := fun j hj => by
    rw [hpre2 j (by omega), hpre j hj]
  have h := hh2
  have hR := hP.1
  apply WP.ifRet
  rule_simp
  refine ⟨fun h0 => ?_, fun hok => ?_⟩
  · simp only [LoopQ, RetQ]
    exact BbPush.fail h hR
  obtain ⟨htop2, -⟩ := hP.bb hok htop he
  apply WP.assign_loop
  rule_simp
  refine ⟨c2, k + 1, L ++ [e], [BitVec.ofNat 32 (st.id res[k]), w2, ok], rfl,
    by simp [bbSets, Env.set], h, hR, hpre', by omega, by omega, ⟨by simp; omega, fun j hj hj' => ?_⟩,
    htop2⟩
  rcases Nat.lt_or_ge j L.length with hjl | hjl
  · rw [List.getElem_append_left hjl]; exact hLp j hj hjl
  · have hjk : j = k := by simp at hj'; omega
    subst hjk
    rw [List.getElem_append_right (by omega)]
    simp only [hL, Nat.sub_self, List.getElem_cons_zero]
    exact ⟨cc, t, hnr⟩

/-! ## `bb_rsh_stage` -/

/-- The per-position test of `bbRshStage`. -/
def bbRshF (st : St) (isFill : Nat → Bool) (b T n : Nat) (pre : List Nat) (j r : Nat) : Bool :=
  match bbIteArgs st r with
  | some (c, t, e) =>
    if j + T ≥ n then c == b && isFill t else isNotOf st c b && pre[j + T]? == some e
  | none => false

theorem bbRshStage_eq {st : St} {isFill : Nat → Bool} {b T : Nat} {res pre : List Nat}
    (hm : bbMapIdx (fun j r => (bbIteArgs st r).map fun (_, t, e) =>
      if j + T ≥ res.length then e else t) 0 res = some pre)
    (ha : allIdx (bbRshF st isFill b T res.length pre) 0 res = true) :
    Bcf.bbRshStage st isFill b T res = some pre := by
  unfold Bcf.bbRshStage
  rw [hm]
  exact ite_eq_left ha

/-- `r` is `ite(c, t, e)` and `p` is the branch the stage keeps at position `j`. -/
def BbRshAt (st : St) (T n j r p : Nat) : Prop :=
  ∃ cc t e, st.pool[r]? = some ⟨.boolIte, #[cc, t, e]⟩ ∧ p = if j + T ≥ n then e else t

theorem bb_mapIdx_rsh {st : St} {T : Nat} {res L : List Nat} (hL : L.length = res.length)
    (H : ∀ (j : Nat) (hj : j < res.length) (hj' : j < L.length), BbRshAt st T res.length j res[j] L[j]) :
    bbMapIdx (fun j r => (bbIteArgs st r).map fun (_, t, e) =>
      if j + T ≥ res.length then e else t) 0 res = some L := by
  apply bb_mapIdx_of hL
  intro k hk hk'
  obtain ⟨cc, t, e, hn, hp⟩ := H k hk hk'
  rw [hp]
  simp [bb_iteArgs hn]

def BbRshStageSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (arith xb bN T rb : Nat) (xs res : List Nat) (isFill : Nat → Bool),
    FnSpec (State := State) Vbcf.prog "bb_rsh_stage"
      (fun vs s => vs = [.ptr sb 0, uv arith, uv xb, uv xs.length, uv (st.id bN), uv T, uv rb,
          uv res.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv bN ∧
        T < 2147483648 ∧ BbRange c st xb xs ∧ BbRange c st rb res ∧ BbFill st arith xs isFill)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ BbPush W sb X c0 prems params st c
        (fun L => Bcf.bbRshStage st isFill bN T res = some L) r s')

theorem bb_rsh_stage_spec : BbRshStageSpec (State := State) := by
  intro W sb X c0 c prems params st arith xb bN T rb xs res isFill
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbRshStage) rfl
  rintro vs s ⟨rfl, h, hR, hbN, hT, hx, hr, hfill⟩
  simp [bbRshStage, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbRshStage) rfl
  simp only [bbRshStage, Stmt.block, initLocals, List.map, Ty.zero]
  have hrb := hr.bound hR
  have hxb := hx.bound hR
  rule_assign
  apply WP.bb_loop (fun env0 => BbPushInv W sb X c0 prems params st c env0 "j" ["r", "ok"]
    res.length (fun k L => L.length = k ∧
      ∀ (j : Nat) (hj : j < res.length) (hj' : j < L.length), BbRshAt st T res.length j res[j] L[j]))
  · exact ⟨c, 0, [], [0#32, 0#32], rfl, by simp [bbSets, Env.set], h, hR,
      fun _ _ => rfl, Nat.le_refl _, by omega, ⟨rfl, fun j _ hj => by simp at hj⟩, StkTop.nil rfl⟩
  clear h hR
  rintro env s' ⟨c', k, L, ws, hws, rfl, h, hR, hpre, hsp, hk, ⟨hL, hLp⟩, htop⟩
  obtain ⟨w1, w2, rfl⟩ := len_shape 2 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  have hr' := hr.frame hpre hsp
  have hx' := hx.frame hpre hsp
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkn : k = res.length := by omega
    subst hkn
    have hspb := hR.bb_sp_le
    rule_assign
    apply WP.bb_loop (fun env1 => BbInv s' env1 "j" ["r", "ok"] res.length
      (fun j => allIdx (bbRshF st isFill bN T res.length L) j (res.drop j) = true →
        allIdx (bbRshF st isFill bN T res.length L) 0 res = true))
    · exact ⟨rfl, 0, [w1, w2], rfl, by simp [bbSets, Env.set], by omega, fun h => h⟩
    rintro env s'' ⟨rfl, j, ws, hws, rfl, hj, hres⟩
    obtain ⟨v1, v2, rfl⟩ := len_shape 2 hws
    simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
    rule_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · apply WP.rule_ret; rule_simp
      exact ⟨c', h, hR, Or.inr ⟨(bv_ofNat_toNat _).symm, hpre, hsp, L,
        bbRshStage_eq (bb_mapIdx_rsh hL hLp) (bb_allIdx_end (by omega) hres), htop⟩⟩
    have hstk := hr'.stk hR h hlt
    have hrj := hr'.lt hlt
    obtain ⟨cc, t, e, hnj, hpv⟩ := hLp j hlt (by omega)
    have hcc := hR.core.bb_arg_lt hnj (x := cc) (by simp)
    have ht := hR.core.bb_arg_lt hnj (x := t) (by simp)
    have he := hR.core.bb_arg_lt hnj (x := e) (by simp)
    rule_assign [hstk, hr'.rd hlt]
    apply WP.seq
    apply WP.ite
    by_cases hjT : j + T ≥ res.length
    · rule_simp [hjT]
      apply WP.ifRet
      rule_simp [hR.core.rd3 hnj]
      refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hcb => ?_⟩
      refine WP.bb_call (bb_is_fill_spec W sb X c0 c' prems params st arith xb t xs isFill) ?_
        ⟨rfl, h, hR, hx', ht, hfill⟩ ?_
      · rule_simp [hR.core.rd3 hnj]
      intro r1 hr1
      rule_simp
      apply WP.ite
      rule_simp
      refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ]; exact BbPush.fail h hR,
        fun hr10 => ?_⟩
      apply WP.skip
      apply WP.assign_loop
      rule_simp
      refine ⟨rfl, j + 1, [BitVec.ofNat 32 (st.id res[j]), r1], rfl, by simp [bbSets, Env.set],
        by omega, bb_allIdx_step (by simpa using hlt) hres ?_⟩
      simp [bbRshF, bb_iteArgs hnj, hjT, hcb, hr1 hr10]
    · rule_simp [hjT]
      refine WP.bb_call (bb_is1_spec W sb X c0 c' prems params st cc 385#32 .boolNot bN) ?_
        ⟨rfl, h, hR, hcc, hbN, by decide, by decide, by decide, by decide⟩ ?_
      · rule_simp [hR.core.rd3 hnj]
      intro r1 hr1
      rule_simp
      apply WP.ifRet
      rule_simp
      refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hr10 => ?_⟩
      have hjT' : j + T < L.length := by omega
      have hcell := (htop.2 (j + T) _ (List.getElem?_eq_getElem hjT'))
      have eidx : (c.k.sp + BitVec.ofNat 32 j + BitVec.ofNat 32 T).toNat = c.k.sp.toNat + j + T := by
        rw [bb_add_toNat' (by rw [bb_add_toNat' (by omega)]; omega), bb_add_toNat' (by omega)]
      have erd : rd c'.stk (c.k.sp.toNat + j + T) = some (uv (st.id L[j + T])) := by
        rw [Nat.add_assoc]; exact rd_u32 hcell.2
      have hLjT := hcell.1
      apply WP.ite
      rule_simp [eidx, erd, hR.stk_eq h (by have := htop.1; omega), hR.core.rd3 hnj]
      refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ]; exact BbPush.fail h hR,
        fun heq => ?_⟩
      apply WP.skip
      apply WP.assign_loop
      rule_simp
      refine ⟨rfl, j + 1, [BitVec.ofNat 32 (st.id res[j]), r1], rfl, by simp [bbSets, Env.set],
        by omega, bb_allIdx_step (by simpa using hlt) hres ?_⟩
      simp [bbRshF, bb_iteArgs hnj, hjT, isNotOf, hr1 hr10, List.getElem?_eq_getElem hjT', heq]
  have hstk := hr'.stk hR h hlt
  have hrk := hr'.lt hlt
  rule_assign [hstk, hr'.rd hlt]
  obtain ⟨nr, hnr⟩ := node_of_lv hrk
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hnr]
  refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbPush.fail h hR, fun hh => ?_⟩
  obtain ⟨cc, t, e, rfl, hcc, ht, he⟩ := hR.core.bb_hdr3 hnr (op := .boolIte) (by decide)
    (by decide) (by decide) (by decide) hh
  have key : ∀ (p : Nat), st.lv p → p = (if k + T ≥ res.length then e else t) →
      ∀ (s2 : KernelState prog State) c2 ok, Holds W s2.mem sb c2 →
      Pushed W X c0 prems params st c' (BitVec.ofNat 32 (st.id p)) c2 ok →
      WP Vbcf.prog (.seq (.ite (.bin .eq (.var "ok") (.lit32 0#32)) (.ret (some (.named "NOID" 4294967295#32)))
          .skip) (.assign "j" (.bin .add (.var "j") (.lit32 1#32))))
        (LoopQ (BbPushInv W sb X c0 prems params st c
          [("st", (Ty.struct "ck").ptr, Val.ptr sb 0), ("arith", Ty.u32, uv arith), ("xb", Ty.u32, uv xb),
            ("nx", Ty.u32, uv xs.length), ("b", Ty.u32, uv (st.id bN)), ("t", Ty.u32, uv T),
            ("rb", Ty.u32, uv rb), ("n", Ty.u32, uv res.length), ("base", Ty.u32, Val.u32 c.k.sp),
            ("j", Ty.u32, Val.u32 0#32), ("r", Ty.u32, Val.u32 0#32), ("ok", Ty.u32, Val.u32 0#32)]
          "j" ["r", "ok"] res.length (fun k L => L.length = k ∧
            ∀ (j : Nat) (hj : j < res.length) (hj' : j < L.length), BbRshAt st T res.length j res[j] L[j]))
          (RetQ (BbPush W sb X c0 prems params st c (fun L => Bcf.bbRshStage st isFill bN T res = some L))))
        [("st", (Ty.struct "ck").ptr, Val.ptr sb 0), ("arith", Ty.u32, uv arith), ("xb", Ty.u32, uv xb),
          ("nx", Ty.u32, uv xs.length), ("b", Ty.u32, uv (st.id bN)), ("t", Ty.u32, uv T),
          ("rb", Ty.u32, uv rb), ("n", Ty.u32, uv res.length), ("base", Ty.u32, Val.u32 c.k.sp),
          ("j", Ty.u32, uv k), ("r", Ty.u32, uv (st.id res[k])), ("ok", Ty.u32, Val.u32 ok)] s2 := by
    intro p hp hpv s2 c2 ok hh2 hP
    obtain ⟨hpre2, hsp2⟩ := hP.bb_pre
    have hpre' : ∀ j, j < c.k.sp.toNat → c2.stk[j]? = c.stk[j]? := fun j hj => by
      rw [hpre2 j (by omega), hpre j hj]
    have h := hh2
    have hR := hP.1
    apply WP.ifRet
    rule_simp
    refine ⟨fun h0 => ?_, fun hok => ?_⟩
    · simp only [LoopQ, RetQ]
      exact BbPush.fail h hR
    obtain ⟨htop2, -⟩ := hP.bb hok htop hp
    apply WP.assign_loop
    rule_simp
    refine ⟨c2, k + 1, L ++ [p], [BitVec.ofNat 32 (st.id res[k]), ok], rfl,
      by simp [bbSets, Env.set], h, hR, hpre', by omega, by omega,
      ⟨by simp; omega, fun j hj hj' => ?_⟩, htop2⟩
    rcases Nat.lt_or_ge j L.length with hjl | hjl
    · rw [List.getElem_append_left hjl]; exact hLp j hj hjl
    · have hjk : j = k := by simp at hj'; omega
      subst hjk
      rw [List.getElem_append_right (by omega)]
      simp only [hL, Nat.sub_self, List.getElem_cons_zero]
      exact ⟨cc, t, e, hnr, hpv⟩
  apply WP.seq
  apply WP.ite
  by_cases hkT : k + T ≥ res.length
  · rule_simp [hkT]
    apply WP.bb_push_last h hR
    rule_simp [hR.core.rd3 hnr]
    intro s2 c2 ok hh2 hP
    exact key e he (by simp [hkT]) s2 c2 ok hh2 hP
  · rule_simp [hkT]
    apply WP.bb_push_last h hR
    rule_simp [hR.core.rd3 hnr]
    intro s2 c2 ok hh2 hP
    exact key t ht (by simp [hkT]) s2 c2 ok hh2 hP

end Vbcf.Proof
