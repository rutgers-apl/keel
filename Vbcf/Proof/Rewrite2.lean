import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite1
import Vbcf.Proof.Bool4
import Vbcf.Proof.Clause6

/-!
# Vbcf proofs: the Rewrite family, part 2 — small helpers

`rw_const` (`constNat`), `rw_lit` (`pushLit`), `rw_ty_ok` (`rwTyOK`), `rw_cond_match`
(`condMatch`), `rw_splice` (`spliceIdx`).
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## `rw_const` -/

/-- What `rw_const` returns: a word `r`, `st->val = vl`, and if `r ≠ 0` the node is the
constant `vl`. -/
def RwConstR (W : World) (sb : Nat) (c : CMem) (st : VSt) (i : Nat) (r : BitVec 32) (s' : (KernelState prog State)) :
    Prop :=
  ∃ wk er vl, Holds W s'.mem sb (c.wev wk er vl) ∧
    (r ≠ 0#32 → ∃ x, constNat st i = some x ∧ vl.toNat = x)

def RwConstSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (i : Nat),
    FnSpec (State := State) Vbcf.prog "rw_const"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv i)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ RwConstR W sb c st i r s')

theorem rw_const_spec : RwConstSpec (State := State) := by
  intro W sb X c0 c prems params st i
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwConst) rfl
  rintro vs s ⟨rfl, h, hR, hi⟩
  simp [rwConst, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwConst) rfl
  simp only [rwConst, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.call_seq (cval_spec 32#32 W sb c X.posOf st i) (by rule_simp) ⟨rfl, h, hR.core, hi⟩
  rintro rv s' ⟨w, wk, er, vl, rfl, h', hv⟩
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => ⟨wk, er, vl, h', fun h0 => absurd rfl h0⟩, fun hw0 hw64 => ?_⟩
  apply WP.ret
  rule_simp [RetQ]
  refine ⟨wk, er, vl, h', fun _ => ?_⟩
  have hne : w ≠ 4294967295#32 := by
    intro e; subst e; exact absurd hw64 (by decide)
  obtain ⟨v, hm, hrep⟩ := hv hw0 hne
  cases v with
  | bool b =>
    obtain ⟨rfl, -⟩ := hrep
    exact absurd hw64 (by decide)
  | bv k x =>
    exact ⟨x.toNat, by simp [constNat, rw_cval_eq, hm], hrep.2.2.2⟩
  | _ => exact hrep.elim

/-! ## `rw_lit` -/

def RwLitSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (sz v : BitVec 64),
    FnSpec (State := State) Vbcf.prog "rw_lit"
      (fun vs s => vs = [.ptr sb 0, .u64 sz, .u64 v] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st)
      (fun _ _ => HPost W sb X c0 prems params c st
        (fun st' i => pushLit st sz.toNat v.toNat = some (st', i)))

theorem rw_lit_spec : RwLitSpec (State := State) := by
  intro W sb X c0 c prems params st sz v
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwLit) rfl
  rintro vs s ⟨rfl, h, hR⟩
  simp [rwLit, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := rwLit) rfl
  simp only [rwLit, Stmt.block, initLocals, List.map, Ty.zero]
  h_guard
  intro h255
  h_guard
  intro h0 h64
  have hszn : sz.toNat ≤ 64 := by rw [BitVec.le_def] at h64; simpa using h64
  have hsz0 : 1 ≤ sz.toNat := by
    have : sz.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e))
    omega
  -- the value fits the width
  have hfin : ∀ (hv : sz.toNat < 64 → (v >>> sz.toNat) = 0#64), v.toNat < 2 ^ sz.toNat := by
    intro hv
    by_cases e : sz.toNat < 64
    · have := hv e
      have h2 := congrArg BitVec.toNat this
      rw [BitVec.toNat_ushiftRight] at h2
      simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.shiftRight_eq_div_pow] at h2
      rcases Nat.lt_or_ge v.toNat (2 ^ sz.toNat) with hh | hh
      · exact hh
      · have := Nat.div_pos hh (Nat.two_pow_pos _); omega
    · have : sz.toNat = 64 := by omega
      rw [this]; exact v.isLt
  apply WP.h_guard h
  by_cases e : sz.toNat < 64
  · have e' : ¬ 64#64 ≤ sz := by rw [BitVec.le_def]; simpa using e
    rule_simp [e, e']
    intro hv
    have hv' := hfin (fun _ => hv)
    have hw : (sz.setWidth 32).toNat = sz.toNat := by
      rw [BitVec.toNat_setWidth]; omega
    apply WP.rule_mkval mkval_lt_specT h hR (sz.setWidth 32) v (fun h32 => by
      rw [hw] at h32
      exact Nat.lt_of_lt_of_le hv' (Nat.pow_le_pow_right (by decide) h32))
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built h hB (fun st' i hP => by
      rw [hw] at hP; simp [pushLit, show sz.toNat ≤ 255 by omega, hP])
  · have e' : 64#64 ≤ sz := by rw [BitVec.le_def]; simp; omega
    rule_simp [e']
    have hv' := hfin (fun h => absurd h e)
    have hw : (sz.setWidth 32).toNat = sz.toNat := by
      rw [BitVec.toNat_setWidth]; omega
    apply WP.rule_mkval mkval_lt_specT h hR (sz.setWidth 32) v (fun h32 => by
      rw [hw] at h32
      exact Nat.lt_of_lt_of_le hv' (Nat.pow_le_pow_right (by decide) h32))
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built h hB (fun st' i hP => by
      rw [hw] at hP; simp [pushLit, show sz.toNat ≤ 255 by omega, hP])

/-! ## `rw_ty_ok` -/

theorem rw_encTy_bv (w : Nat) : RwEnc.encTy (.bv w) = 2 + w * 256 := by
  simp only [RwEnc.encTy, RwEnc.yBv]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : 2 < 2 ^ 8), Nat.shiftLeft_eq]
  simp only [Nat.reducePow]; omega

theorem rw_encTy_bv_k {w : Nat} (hw : w < 65536) :
    BitVec.ofNat 32 (2 + w * 256) &&& 255#32 = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_toNat_ofNat (by omega)]; simp; try omega

theorem rw_encTy_bv_w {w : Nat} (hw : w < 65536) :
    BitVec.ofNat 32 (2 + w * 256) >>> 8 = BitVec.ofNat 32 w := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_8, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]; omega

theorem rw_tyW_list_bit (e : Bool) {k : Nat} (hk : k < 256) :
    BitVec.ofNat 32 (tyW (.list e k)) >>> 8 &&& 1#32 = if e then 1#32 else 0#32 := by
  rw [tyW_list]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, bv_shr_8, bv_toNat_ofNat (by split <;> omega)]
  cases e <;> simp <;> omega

def RwTyOkSpec : Prop :=
  ∀ (rt : RwTy) (ty : Bcf.Ty), wfTy rt = true → TyFits ty →
    FnSpec (State := State) Vbcf.prog "rw_ty_ok" (fun vs _ => vs = [uv (RwEnc.encTy rt), uv (tyW ty)])
      (fun _ s rv s' => s' = s ∧ ∃ r, rv = some (.u32 r) ∧ (r ≠ 0#32 → rwTyOK rt (some ty) = true))

/-- `embc_simp` with `omega` as discharger. -/
macro "rw_esimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (disch := omega) [EmbC.evalE, EmbC.evalBin, EmbC.evalArith, EmbC.evalCast,
      EmbC.evalArgs, EmbC.ptrEq, EmbC.Env.get, EmbC.Env.ty, EmbC.Env.set, EmbC.Env.assign,
      EmbC.Val.toIdx, EmbC.Val.ofBool, $ts,*])

/-- One `if (k == …) { return …; }` of `rw_ty_ok`. -/
macro "rw_tyok_step" : tactic => do
  let hw := Lean.mkIdent `hw
  `(tactic| (apply WP.ifRet; embc_simp [RwEnc.yAny, RwEnc.yBool,
    RwEnc.yBvq, RwEnc.yBools, RwEnc.yBvqs, RwEnc.yBv, rw_encTy_bv_k, rw_encTy_bv_w, $hw:ident]))

theorem rw_ty_ok_spec : RwTyOkSpec (State := State) := by
  intro rt ty hw hfit
  apply FnSpec.intro' (fn := rwTyOk) rfl
  rintro vs s rfl
  simp [rwTyOk, bindParams]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.assign_seq
  cases rt
  · simp only [wfTy] at hw
    try simp only [rw_encTy_bv]
    rcases ty with _ | w2 | ⟨_ | _, k⟩ <;> simp only [TyFits] at hfit <;>
      simp only [RwEnc.encTy, tyW_list, tyW_bool, tyW_bv] <;>
      embc_simp [RwEnc.yAny, RwEnc.yBool, RwEnc.yBvq, RwEnc.yBools, RwEnc.yBvqs,
        RwEnc.yBv, rw_encTy_bv_k, rw_encTy_bv_w, hw]
    all_goals iterate 1 rw_tyok_step
    all_goals simp [retPost]
    all_goals (intros; simp_all [rwTyOK] <;> omega)
  · simp only [wfTy] at hw
    try simp only [rw_encTy_bv]
    rcases ty with _ | w2 | ⟨_ | _, k⟩ <;> simp only [TyFits] at hfit <;>
      simp only [RwEnc.encTy, tyW_list, tyW_bool, tyW_bv] <;>
      embc_simp [RwEnc.yAny, RwEnc.yBool, RwEnc.yBvq, RwEnc.yBools, RwEnc.yBvqs,
        RwEnc.yBv, rw_encTy_bv_k, rw_encTy_bv_w, hw]
    all_goals iterate 2 rw_tyok_step
    all_goals simp [retPost]
    all_goals (intros; simp_all [rwTyOK, ← BitVec.toNat_inj] <;> omega)
  · simp only [wfTy, decide_eq_true_eq] at hw
    try simp only [rw_encTy_bv]
    rcases ty with _ | w2 | ⟨_ | _, k⟩ <;> simp only [TyFits] at hfit <;>
      simp only [tyW_list, tyW_bool, tyW_bv] <;>
      embc_simp [RwEnc.yAny, RwEnc.yBool, RwEnc.yBvq, RwEnc.yBools, RwEnc.yBvqs,
        RwEnc.yBv, rw_encTy_bv_k, rw_encTy_bv_w, hw]
    all_goals iterate 3 rw_tyok_step
    all_goals simp [ite_some_u32, retPost]
    all_goals (intros; simp_all [rwTyOK, ← BitVec.toNat_inj] <;> omega)
  · simp only [wfTy] at hw
    try simp only [rw_encTy_bv]
    rcases ty with _ | w2 | ⟨_ | _, k⟩ <;> simp only [TyFits] at hfit <;>
      simp only [RwEnc.encTy, tyW_list, tyW_bool, tyW_bv] <;>
      embc_simp [RwEnc.yAny, RwEnc.yBool, RwEnc.yBvq, RwEnc.yBools, RwEnc.yBvqs,
        RwEnc.yBv, rw_encTy_bv_k, rw_encTy_bv_w, hw]
    all_goals iterate 4 rw_tyok_step
    all_goals simp [ite_some_u32, retPost]
    all_goals (intros; simp_all [rwTyOK] <;> omega)
  · simp only [wfTy] at hw
    try simp only [rw_encTy_bv]
    rcases ty with _ | w2 | ⟨_ | _, k⟩ <;> simp only [TyFits] at hfit <;>
      simp only [RwEnc.encTy, tyW_list, tyW_bool, tyW_bv] <;>
      embc_simp [RwEnc.yAny, RwEnc.yBool, RwEnc.yBvq, RwEnc.yBools, RwEnc.yBvqs,
        RwEnc.yBv, rw_encTy_bv_k, rw_encTy_bv_w, hw]
    all_goals iterate 5 rw_tyok_step
    all_goals simp [ite_some_u32, retPost]
    all_goals (intros; simp_all [rwTyOK, ← BitVec.toNat_inj, BitVec.toNat_and,
      BitVec.toNat_ushiftRight] <;> omega)
  · simp only [wfTy] at hw
    try simp only [rw_encTy_bv]
    rcases ty with _ | w2 | ⟨_ | _, k⟩ <;> simp only [TyFits] at hfit <;>
      simp only [RwEnc.encTy, tyW_list, tyW_bool, tyW_bv] <;>
      embc_simp [RwEnc.yAny, RwEnc.yBool, RwEnc.yBvq, RwEnc.yBools, RwEnc.yBvqs,
        RwEnc.yBv, rw_encTy_bv_k, rw_encTy_bv_w, hw]
    all_goals iterate 6 rw_tyok_step
    all_goals simp [ite_some_u32, retPost]
    all_goals (intros; simp_all [rwTyOK, ← BitVec.toNat_inj, BitVec.toNat_and,
      BitVec.toNat_ushiftRight] <;> omega)

/-! ## `rw_cond_match` -/

def RwCondMatchSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (a p : Nat),
    FnSpec (State := State) Vbcf.prog "rw_cond_match"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id p)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv a ∧ st.lv p)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        (s' = s ∧ (r ≠ 0#32 → condMatch X.bi st a p = true)))

theorem rw_cond_match_spec : RwCondMatchSpec (State := State) := by
  intro W sb X c0 c prems params st a p
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwCondMatch) rfl
  rintro vs s ⟨rfl, h, hR, ha, hp⟩
  simp [rwCondMatch, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwCondMatch) rfl
  simp only [rwCondMatch, Stmt.block, initLocals, List.map]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun e => ⟨rfl, fun _ => by simp [condMatch, e]⟩, fun hne => ?_⟩
  obtain ⟨n, hn⟩ := node_of_lv hp
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hn]
  refine ⟨fun _ => ⟨rfl, fun h0 => absurd rfl h0⟩, fun heq => ?_⟩
  obtain ⟨x, t, rfl, hx, ht⟩ := hR.core.args2 hn heq
  apply WP.ret
  rule_simp [RetQ, hR.core.rd2 hn]
  intro hxt hxa
  simp [condMatch, St.node, hn, hxt, hxa]

/-! ## `rw_splice` -/

/-- What `rw_splice(st, i)` leaves: the rule context, the stack below `sp` untouched, and on
success the elements `spliceIdx st i` pushed. -/
def RwSpliceR (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem)
    (st : VSt) (i : Nat) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧
    (r ≠ 0#32 → ∃ items, spliceIdx st i = some items ∧
      c'.k.sp.toNat = c.k.sp.toNat + items.length ∧ StkIds c' st c.k.sp.toNat items)

def RwSpliceSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (i : Nat),
    FnSpec (State := State) Vbcf.prog "rw_splice"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv i)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ RwSpliceR W sb X c0 prems params c st i r s')

theorem rw_splice_spec : RwSpliceSpec (State := State) := by
  intro W sb X c0 c prems params st i
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwSplice) rfl
  rintro vs s ⟨rfl, h, hR, hi⟩
  simp [rwSplice, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwSplice) rfl
  simp only [rwSplice, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨n, hn⟩ := node_of_lv hi
  obtain ⟨t, ht, hty, hfit⟩ := hR.core.tyOf hn
  apply WP.rule_ty_of ty_of_spec
  rule_simp [hR.core.rdHdr hn, hty]
  apply WP.ite_seq
  rule_simp [uv_tyW_ge_list hfit]
  refine ⟨fun hl => ?_, fun hsc => ?_⟩
  · cases t with
    | bool => simp [Ty.isScalar] at hl
    | bv w => simp [Ty.isScalar] at hl
    | list e k =>
    by_cases hlv : ∃ e', n.op = .listVal e'
    · obtain ⟨e', hop⟩ := hlv
      obtain ⟨op, args⟩ := n
      simp only at hop
      subst hop
      apply WP.guard_lit
      rule_simp [hR.core.rdHdr hn]
      apply WP.call_seq (push_args_spec W sb c X.posOf st.cs _ (st.σ i) _) (by rule_simp)
        ⟨rfl, h, hR.core.cinv, st.img i _ hi hn, by simp [IsLeaf, isLeaf], hR.core.id_toNat hi⟩
      rintro rv s' ⟨c', h', hfr, hc', hpre, hcase⟩
      have hR' := hR.after_push hfr hc'.stk
      rcases hcase with rfl | ⟨rfl, hsp, hids⟩
      · rule_simp
        apply WP.ret
        rule_simp [RetQ]
        exact ⟨c', h', hR', hpre, fun h0 => absurd rfl h0⟩
      · rule_simp
        apply WP.ret
        rule_simp [RetQ]
        simp only [Node.ren_args, Array.toList_map] at hids
        refine ⟨c', h', hR', hpre, fun _ => ⟨args.toList, ?_, by simpa using hsp,
          StkIds.ofC hids (fun a ha => st.closed i _ hi hn a (by simpa using ha))⟩⟩
        simp [spliceIdx, ht, hn]
    · have h1 : ¬ n.op = .listVal false := fun e => hlv ⟨_, e⟩
      have h2 : ¬ n.op = .listVal true := fun e => hlv ⟨_, e⟩
      apply WP.guard_lit
      rule_simp [hR.core.rdHdr hn, h1, h2]
      exact ⟨c, h, hR, fun _ _ => rfl, fun h0 => absurd rfl h0⟩
  · apply WP.rule_push h hR
    rule_simp
    intro s' c' ok h' hP
    apply WP.ret
    rule_simp [RetQ]
    obtain ⟨hR', hpre, hcase⟩ := hP
    refine ⟨c', h', hR', hpre, fun hok => ?_⟩
    rcases hcase with ⟨rfl, -⟩ | ⟨-, -, hsp, htop⟩
    · exact absurd rfl hok
    · refine ⟨[i], ?_, by simpa using hsp, ?_⟩
      · cases t with
        | list e k => simp [Ty.isScalar] at hsc
        | bool => simp [spliceIdx, ht]
        | bv w => simp [spliceIdx, ht]
      · intro j a hj
        cases j with
        | zero => simp at hj; subst hj; exact ⟨hi, by unfold U; simpa using htop⟩
        | succ j => simp at hj

end Vbcf.Proof
