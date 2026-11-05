import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite8

/-!
# Vbcf proofs: the Rewrite family, part 9 — `rw_params` (`paramsOK`), `rw_cond_one`, `rw_check_cond` (`checkCond`)
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-! ## Lean side -/

theorem rw_paramsOK_of (st : St) : ∀ (ts : List RwTy) (as : List Nat), ts.length = as.length →
    (∀ j (hj : j < ts.length) (hj' : j < as.length), rwTyOK ts[j] st.tys[as[j]]? = true) →
    paramsOK st ts as = true
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | t :: ts, a :: as, hl, h => by
    simp only [paramsOK, Bool.and_eq_true]
    refine ⟨h 0 (by simp) (by simp), rw_paramsOK_of st ts as (by simpa using hl) (fun j hj hj' => ?_)⟩
    exact h (j + 1) (by simp; omega) (by simp; omega)

/-- One position of an instantiated condition: conjunct `ci` at index `i` is matched by the
premise there or, past the last premise, evaluates to `true`. -/
def CondOne (bi : Builtins) (st : St) (ci i : Nat) (ps : List Nat) : Prop :=
  match ps[i]? with
  | some p => condMatch bi st ci p = true
  | none => Bcf.cval st ci = some (Val.bool true)

/-- The memory after some calls to `cval`: `c` with other work, error and value cells. -/
def WevHolds (W : World) (sb : Nat) (c : CMem) (s' : (KernelState prog State)) : Prop :=
  ∃ wk er vl, Holds W s'.mem sb (c.wev wk er vl)

theorem WevHolds.refl {W : World} {sb : Nat} {c : CMem} {s : (KernelState prog State)} (h : Holds W s.mem sb c) :
    WevHolds W sb c s := ⟨c.k.work, c.k.err, c.k.val, by rw [wev_self]; exact h⟩

theorem rw_condsOK_of (bi : Builtins) (st : St) : ∀ (cs ps : List Nat), ps.length ≤ cs.length →
    (∀ j (hj : j < cs.length), CondOne bi st cs[j] j ps) → condsOK bi st cs ps = true
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | c :: cs, [], _, h => by
    have h0 := h 0 (by simp)
    simp only [CondOne, List.getElem?_nil, List.getElem_cons_zero] at h0
    simp only [condsOK, h0]
    exact rw_condsOK_of bi st cs [] (by simp) (fun j hj => by
      have := h (j + 1) (by simp; omega)
      simpa [CondOne] using this)
  | c :: cs, p :: ps, hl, h => by
    have h0 := h 0 (by simp)
    simp only [CondOne, List.getElem?_cons_zero, List.getElem_cons_zero] at h0
    simp only [condsOK, Bool.and_eq_true]
    refine ⟨h0, rw_condsOK_of bi st cs ps (by simpa using hl) (fun j hj => ?_)⟩
    have := h (j + 1) (by simp; omega)
    simpa [CondOne] using this

/-! ## `rw_params` -/

def RwParamsSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (off : Nat) (r : RwRule) (ab : Nat) (args : List Nat),
    FnSpec (State := State) Vbcf.prog "rw_params"
      (fun vs s => vs = [.ptr sb 0, uv off, uv ab, uv args.length] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ RwRec off r ∧ r.params.all wfTy = true ∧
        off + recHdr + r.params.length < 65536 ∧ RwArgsAt c st ab args)
      (fun _ s rv s' => ∃ v, rv = some (.u32 v) ∧ (s' = s ∧ (v ≠ 0#32 → paramsOK st r.params args = true)))

/-- The locals of `rw_params`. -/
def rwParamsEnv (sb off ab na : Nat) (i t ok : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("off", .u32, uv off), ("ab", .u32, uv ab),
    ("na", .u32, uv na), ("i", .u32, .u32 i), ("t", .u32, .u32 t), ("ok", .u32, .u32 ok)]

def RwParamsInv (sb off ab : Nat) (st : VSt) (r : RwRule) (args : List Nat) (s : (KernelState prog State)) (env' : Env)
    (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ ∃ i t ok, env' = rwParamsEnv sb off ab args.length (BitVec.ofNat 32 i) t ok ∧
    i ≤ args.length ∧
    ∀ j (hj : j < r.params.length) (hj' : j < args.length), j < i →
      rwTyOK r.params[j] st.tys[args[j]]? = true

theorem rw_params_spec : RwParamsSpec (State := State) := by
  intro W sb X c0 c prems params st off r ab args
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwParams) rfl
  rintro vs s ⟨rfl, h, hR, hrec, hwf, hoff, hargs⟩
  simp [rwParams, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwParams) rfl
  simp only [rwParams, Stmt.block, initLocals, List.map, Ty.zero]
  have hsp := hR.sp_lt
  have hal := hargs.2
  simp only [maxPool] at hsp
  apply WP.guard_lit
  rw [EmbC.evalE]
  rw [rw_eval_cload (q := BitVec.ofNat 32 off) rw_findConst (by rule_simp)
    (show (BitVec.ofNat 32 off).toNat = off from bv_toNat_ofNat (by omega))
    (rw_tbl_get hrec.np)]
  rule_simp
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun hnp => ?_⟩
  apply WP.loop_seq (RwParamsInv sb off ab st r args s)
  · exact ⟨rfl, 0, 0#32, 0#32, rfl, by omega, fun j _ _ hj => absurd hj (by omega)⟩
  rintro env s1 ⟨rfl, i, t, ok, rfl, hi, hall⟩
  simp only [rwParamsEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.ret
    rule_simp [RetQ]
    exact rw_paramsOK_of st _ _ hnp (fun j hj hj' => hall j hj hj' (by omega))
  obtain ⟨hia, hU⟩ := hargs.1 i args[i] (List.getElem?_eq_getElem hlt)
  obtain ⟨n, hn⟩ := node_of_lv hia
  obtain ⟨ty, hty, htyw, hfit⟩ := hR.core.tyOf hn
  have hstk := hR.stk_eq h (by omega)
  have hcell : rd c.stk (ab + i) = some (uv (st.id args[i])) := by
    apply rd_u32; unfold U at hU; exact hU
  have hpi : i < r.params.length := by omega
  have hpw : RwEnc.words[off + recHdr + i]? = some (encTy r.params[i]) := by
    have := hrec.params i (by simpa using hpi)
    simpa using this
  have hwt : wfTy r.params[i] = true := List.all_eq_true.mp hwf _ (List.getElem_mem hpi)
  apply WP.rule_ty_of ty_of_spec
  rule_simp [hstk, hcell, hR.core.rdHdr hn, htyw]
  refine WP.call_seq (rw_ty_ok_spec r.params[i] ty hwt hfit) ?_ rfl ?_
  · apply rw_evalArgs_cons (rw_eval_cload (q := BitVec.ofNat 32 (off + recHdr + i))
      rw_findConst (by rule_simp)
      (show (BitVec.ofNat 32 (off + recHdr + i)).toNat = off + recHdr + i from
        bv_toNat_ofNat (by omega)) (rw_tbl_get hpw))
    exact rw_evalArgs_cons (by rule_simp) rfl
  rintro rv s2 ⟨rfl, v, rfl, hv⟩
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => ⟨rfl, fun h1 => absurd rfl h1⟩, fun hne => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, i + 1, _, _, rfl, by omega, fun j hj hj' hji => ?_⟩
  rcases Nat.lt_or_ge j i with hji' | hji'
  · exact hall j hj hj' hji'
  · have : j = i := by omega
    subst this
    rw [hty]; exact hv hne

/-! ## `rw_cond_one` -/

def RwCondOneSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (ci i : Nat),
    FnSpec (State := State) Vbcf.prog "rw_cond_one"
      (fun vs s => vs = [.ptr sb 0, uv (st.id ci), uv i, uv prems.length] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv ci ∧ i < 4294967296)
      (fun _ _ rv s' => ∃ v, rv = some (.u32 v) ∧ WevHolds W sb c s' ∧
        (v ≠ 0#32 → CondOne X.bi st ci i prems))

theorem rw_cond_one_spec : RwCondOneSpec (State := State) := by
  intro W sb X c0 c prems params st ci i
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwCondOne) rfl
  rintro vs s ⟨rfl, h, hR, hci, hi⟩
  simp [rwCondOne, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwCondOne) rfl
  simp only [rwCondOne, Stmt.block, initLocals, List.map, Ty.zero]
  have hpl := hR.prem.1
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · -- the premise in position `i`
    have hpi : i < prems.length := by omega
    have hpri := hR.prem_lt hpi
    apply WP.call_seq (rw_cond_match_spec W sb X c0 c prems params st ci prems[i])
      (by rule_simp [hR.rd_prem hpi]) ⟨rfl, h, hR, hci, hpri⟩
    rintro rv s2 ⟨v, rfl, rfl, hv⟩
    rule_simp
    apply WP.ret
    rule_simp [LoopQ, RetQ]
    refine ⟨WevHolds.refl h, fun hne => ?_⟩
    simp only [CondOne, List.getElem?_eq_getElem hpi]
    exact hv hne
  · -- past the premises: evaluate
    have hge' : prems.length ≤ i := by omega
    apply WP.call_seq (cval_spec 32#32 W sb c X.posOf st ci) (by rule_simp) ⟨rfl, h, hR.core, hci⟩
    rintro rv s3 ⟨cw, wk, er, vl, rfl, h3, hcv⟩
    have hval := wev_k_val c wk er vl
    clear h
    generalize hc3 : c.wev wk er vl = c3 at h3 hval
    have h := h3
    rule_simp
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => ⟨⟨wk, er, vl, hc3 ▸ h⟩, fun h0 => absurd rfl h0⟩, fun hcw => ?_⟩
    apply WP.ret
    rule_simp [RetQ, hval]
    refine ⟨⟨wk, er, vl, hc3 ▸ h⟩, fun hne => ?_⟩
    simp only [CondOne, List.getElem?_eq_none hge', rw_cval_eq]
    obtain ⟨cv, hm, hrep⟩ := hcv (by rw [hcw]; decide) (by rw [hcw]; decide)
    rw [hm]
    cases cv with
    | bool b =>
      cases b
      · simp only [CvRep] at hrep
        rw [hrep.2] at hne
        simp at hne
      · rfl
    | bv w x => simp only [CvRep] at hrep; rw [hcw] at hrep; simp at hrep; omega
    | _ => exact hrep.elim

/-! ## `rw_check_cond` -/

def RwCheckCondSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (ci : Nat),
    FnSpec (State := State) Vbcf.prog "rw_check_cond"
      (fun vs s => vs = [.ptr sb 0, uv (st.id ci), uv prems.length] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv ci)
      (fun _ _ rv s' => ∃ v, rv = some (.u32 v) ∧ WevHolds W sb c s' ∧
        (v ≠ 0#32 → checkCond X.bi st ci prems = true))

/-- The locals of `rw_check_cond`. -/
def rwCcEnv (sb ci np : Nat) (n i ok : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("c", .u32, uv ci), ("np", .u32, uv np),
    ("n", .u32, .u32 n), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)]

def RwCcInv (W : World) (sb : Nat) (X : Ctx) (c : CMem) (ci : Nat) (st : VSt) (prems : List Nat)
    (cs : Array Nat) (env' : Env) (s' : (KernelState prog State)) : Prop :=
  WevHolds W sb c s' ∧
  ∃ i ok, env' = rwCcEnv sb (st.id ci) prems.length (BitVec.ofNat 32 cs.size) (BitVec.ofNat 32 i) ok ∧
    i ≤ cs.size ∧ ∀ j (hj : j < cs.size), j < i → CondOne X.bi st cs[j] j prems

theorem rw_check_cond_spec : RwCheckCondSpec (State := State) := by
  intro W sb X c0 c prems params st ci
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwCheckCond) rfl
  rintro vs s ⟨rfl, h, hR, hci⟩
  simp [rwCheckCond, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwCheckCond) rfl
  simp only [rwCheckCond, Stmt.block, initLocals, List.map, Ty.zero]
  have hpl := hR.prem.1
  obtain ⟨n, hn⟩ := node_of_lv hci
  apply WP.ite_seq
  rule_simp [hR.core.rdHdr hn]
  refine ⟨fun hop => ?_, fun hop => ?_⟩
  · obtain ⟨cs, rfl, hsz, -, hcs⟩ := hR.core.argsN hn hop
    obtain ⟨hh, har, -⟩ := hR.core.rdN hn
    apply WP.assign_seq
    rule_simp [hh, har]
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => ⟨WevHolds.refl h, fun h0 => absurd rfl h0⟩, fun hnp => ?_⟩
    apply WP.loop_seq (RwCcInv W sb X c ci st prems cs)
    · exact ⟨WevHolds.refl h, 0, 0#32, rfl, by omega, fun j _ hj => absurd hj (by omega)⟩
    rintro env s1 ⟨⟨wk, er, vl, h1⟩, i, ok, rfl, hi, hall⟩
    have hR1 := hR.wev (wk := wk) (er := er) (vl := vl)
    obtain ⟨-, -, hcell⟩ := hR1.core.rdN hn
    clear h hR
    generalize hc1 : c.wev wk er vl = c1 at h1 hR1 hcell
    have h := h1
    have hR := hR1
    simp only [rwCcEnv]
    rule_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · apply WP.ret
      rule_simp [LoopQ, RetQ]
      refine ⟨⟨wk, er, vl, hc1 ▸ h⟩, ?_⟩
      simp only [checkCond, St.node, hn]
      exact rw_condsOK_of X.bi st _ _ (by simpa using hnp)
        (fun j hj => hall j (by simpa using hj) (by simp at hj; omega))
    have hcsi := hcs i hlt
    apply WP.call_seq (rw_cond_one_spec W sb X c0 c1 prems params st cs[i] i)
      (by rule_simp [hcell i hlt]) ⟨rfl, h, hR, hcsi, by omega⟩
    rintro rv s2 ⟨v, rfl, ⟨wk2, er2, vl2, h2⟩, hv⟩
    have h2' : Holds W s2.mem sb (c.wev wk2 er2 vl2) := by rw [← hc1, wev_wev] at h2; exact h2
    rule_simp
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => ⟨⟨wk2, er2, vl2, h2'⟩, fun h0 => absurd rfl h0⟩, fun hne => ?_⟩
    apply WP.assign_loop
    rule_simp
    refine ⟨⟨wk2, er2, vl2, h2'⟩, i + 1, _, rfl, by omega, fun j hj hji => ?_⟩
    rcases Nat.lt_or_ge j i with hji' | hji'
    · exact hall j hj hji'
    · have : j = i := by omega
      subst this
      exact hv hne
  · apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => ⟨WevHolds.refl h, fun h0 => absurd rfl h0⟩, fun hnp => ?_⟩
    apply WP.call_seq (rw_cond_one_spec W sb X c0 c prems params st ci 0) (by rule_simp)
      ⟨rfl, h, hR, hci, by omega⟩
    rintro rv s2 ⟨v, rfl, hw2, hv⟩
    rule_simp
    apply WP.ret
    rule_simp [RetQ]
    refine ⟨hw2, fun hne => ?_⟩
    obtain ⟨op, args⟩ := n
    simp only at hop
    simp only [checkCond, St.node, hn]
    split
    · rename_i cs heq; simp at heq; exact absurd heq.1 hop
    · exact rw_condsOK_of X.bi st [ci] prems (by simp; omega)
        (fun j hj => by simp at hj; subst hj; simpa using hv hne)

end Vbcf.Proof
