import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite2

/-!
# Vbcf proofs: the Rewrite family, part 3 — `rw_app` (`pushApp`)

The C gets the operator as its node code `opC (op.node 0)`.  It computes a width `w` from
the argument types only as far as it needs to; the node it builds, `⟨op.node w, is⟩`, is
then shown to be Lean's `⟨op.node (op.width tys), is⟩` from the typing of the built node
(`rw_node_width`), so the loops need no invariant about `w`.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## Lean side -/

theorem rw_bvWidths_sum : ∀ {tys : List Bcf.Ty} {w : Nat}, bvWidths tys = some w → sumBv tys = w
  | [], _, h => by simp [bvWidths] at h
  | [t], w, h => by
    cases t <;> simp [bvWidths] at h
    subst h; simp [sumBv]
  | t :: u :: rest, w, h => by
    cases t with
    | bv n =>
      simp only [bvWidths] at h
      cases hr : bvWidths (u :: rest) with
      | none => rw [hr] at h; cases h
      | some m =>
        rw [hr] at h
        simp at h
        subst h
        simp [sumBv, rw_bvWidths_sum hr]
    | bool => simp [bvWidths] at h
    | list _ _ => simp [bvWidths] at h

theorem rw_allBv_first : ∀ {tys : List Bcf.Ty} {w : Nat}, allBv w tys = true → tys ≠ [] → firstBv tys = w
  | [], _, _, h => absurd rfl h
  | t :: rest, w, h, _ => by
    cases t <;> simp [allBv] at h
    simp [firstBv, h.1]

/-- The bit-vector operators whose width is the first argument's. -/
def rwBvW : RwOp → Bool
  | .bvadd | .bvsub | .bvmul | .bvneg | .bvnot | .bvshl | .bvlshr | .bvashr | .bvor | .bvand
  | .bvxor | .bvudiv | .bvurem => true
  | _ => false

/-- A typed node of `op.node w` has `w = op.width tys`, as far as `op.node` sees it. -/
theorem rw_node_width (op : RwOp) (w : Nat) (tys : List Bcf.Ty) (t : Bcf.Ty)
    (h : (op.node w).resultTy tys = some t) : op.node (op.width tys) = op.node w := by
  cases op <;> simp only [RwOp.node, RwOp.width] at h ⊢
  case concat =>
    simp only [Op.resultTy, bvConcatTy, tyGuard] at h
    split at h
    · rename_i hc; rw [rw_bvWidths_sum hc.2.1]
    · cases h
  all_goals first
    | rfl
    | (simp only [Op.resultTy, bvNTy, tyGuard] at h
       split at h
       · rename_i hc
         rw [rw_allBv_first hc.2.1 (by intro e; rw [e] at hc; simp at hc)]
       · cases h)
    | (simp only [Op.resultTy, bvBinTy, tyGuard] at h
       split at h
       · split at h
         · rename_i a b _ hc; rw [hc.2.1]; rfl
         · cases h
       · cases h)
    | (simp only [Op.resultTy, bvUnTy, tyGuard] at h
       split at h
       · split at h
         · rename_i a _ hc; rw [hc.2]; rfl
         · cases h
       · cases h)

theorem rw_pushApp_one {st : St} {op : RwOp} {a : Nat} (h : op.reducible = true) :
    pushApp st op [a] = some (st, a) := by
  simp [pushApp, h]

theorem rw_pushApp_eq {st : St} {op : RwOp} {is : List Nat} {tys : List Bcf.Ty} (hne : is ≠ [])
    (hred : is.length = 1 → op.reducible = false) (hm : mapOpt (fun a => st.tys[a]?) is = some tys) :
    pushApp st op is = pushNode st ⟨op.node (op.width tys), is.toArray⟩ := by
  rcases is with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact absurd rfl hne
  · simp only [pushApp, hred rfl, Bool.false_eq_true, ↓reduceIte]
    rw [hm]
  · simp only [pushApp]
    rw [hm]

/-! ## Operator codes -/

theorem rw_opC_concat (op : RwOp) : opC (op.node 0) = 152 ↔ op = .concat := by
  cases op <;> decide

theorem rw_opC_size (op : RwOp) : opC (op.node 0) = 104 ↔ op = .bvsize := by
  cases op <;> decide

theorem rw_opC_and7 (op : RwOp) :
    (BitVec.ofNat 32 (opC (op.node 0)) &&& 7#32 = 0#32) ↔
      (rwBvW op = true ∨ op = .concat ∨ op = .bvsize) := by
  cases op <;> decide

theorem rw_opC_node (op : RwOp) (w : Nat) : opC (op.node w) = opC (op.node 0) := by
  cases op <;> rfl

theorem rw_node_leaf (op : RwOp) (w : Nat) : ¬ IsLeaf (op.node w) := by
  cases op <;> simp [RwOp.node, IsLeaf, isLeaf]

/-- The header `code | w << 16` that the C passes to `mkn` is `opHdr (op.node w)`, for the
`w` it has computed. -/
def RwAppW (op : RwOp) (w : Nat) : Prop :=
  w < 256 → opHdr (op.node w) = opC (op.node 0) + w * 65536 ∧ opLo (op.node w) < 256 ∧
    opHi (op.node w) < 256

theorem rw_appW_bv {op : RwOp} (h : rwBvW op = true ∨ op = .concat) (w : Nat) : RwAppW op w := by
  intro hw
  rcases h with h | rfl
  · cases op <;> simp [rwBvW] at h <;> simp [opHdr, RwOp.node, opC, opLo, opHi] <;> omega
  · simp [opHdr, RwOp.node, opC, opLo, opHi]; omega

theorem rw_appW_size : RwAppW .bvsize 32 := by
  intro _; simp [opHdr, RwOp.node, opC, opLo, opHi]

theorem rw_appW_bool {op : RwOp} (h1 : rwBvW op = false) (h2 : op ≠ .concat) (h3 : op ≠ .bvsize) :
    RwAppW op 0 := by
  intro _
  cases op <;> simp [rwBvW] at h1 h2 h3 <;> simp [opHdr, RwOp.node, opC, opLo, opHi]

/-- `code | (w << 16)`. -/
theorem rw_or_shl {k w : Nat} (hk : k < 256) (hw : w < 256) :
    BitVec.ofNat 32 k ||| BitVec.ofNat 32 w <<< 16 = BitVec.ofNat 32 (k + w * 65536) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega),
    bv_toNat_ofNat (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by simp; omega), Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : k < 2 ^ 16), Nat.shiftLeft_eq]
  simp; omega

/-- The reducibility test of `rw_app`. -/
theorem rw_red_eval (op : RwOp) {P : Prog} {env : Env} {m : Mem}
    (hc : env.get "code" = some (uv (opC (op.node 0)))) :
    evalE P env m [cexp| code == BOOL_CONJ || code == BOOL_DISJ || code == BOOL_XOR || code == BV_ADD
        || code == BV_MUL || code == BV_OR || code == BV_AND || code == BV_XOR
        || code == BV_CONCAT] = some (.u32 (if op.reducible then 1#32 else 0#32)) := by
  cases op <;> simp [evalE, hc, evalBin, evalArith, Val.ofBool, RwOp.node, opC, RwOp.reducible]

/-! ## `rw_app` -/

/-- The locals of `rw_app`. -/
def rwAppEnv (sb : Nat) (code base n : Nat) (i t w r : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("code", .u32, uv code), ("base", .u32, uv base),
    ("n", .u32, uv n), ("i", .u32, .u32 i), ("t", .u32, .u32 t), ("w", .u32, .u32 w),
    ("r", .u32, .u32 r)]

/-- After the singleton test. -/
def RwAppMid1 (sb : Nat) (op : RwOp) (base : Nat) (is : List Nat) (s : (KernelState prog State)) (env' : Env)
    (s' : (KernelState prog State)) : Prop :=
  env' = rwAppEnv sb (opC (op.node 0)) base is.length 0#32 0#32 0#32 0#32 ∧ s' = s ∧
    (is.length = 1 → op.reducible = false)

/-- The invariant of the two loops of `rw_app`. -/
def RwAppLoop (sb : Nat) (op : RwOp) (base : Nat) (is : List Nat) (s : (KernelState prog State)) (env' : Env)
    (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ ∃ i t w, env' = rwAppEnv sb (opC (op.node 0)) base is.length i t w 0#32 ∧
    i.toNat ≤ is.length

theorem rw_node0_concat {op : RwOp} {x : Nat} (h : op.node 0 = .bvConcat x) : op = .concat := by
  cases op <;> simp [RwOp.node] at h ⊢

theorem rw_node0_size {op : RwOp} {x : Nat} (h : op.node 0 = .bvSize x) : op = .bvsize := by
  cases op <;> simp [RwOp.node] at h ⊢

/-- After the width computation. -/
def RwAppMid2 (sb : Nat) (op : RwOp) (base : Nat) (is : List Nat) (s : (KernelState prog State)) (env' : Env)
    (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ ∃ i t w, env' = rwAppEnv sb (opC (op.node 0)) base is.length i t w 0#32 ∧
    RwAppW op w.toNat

def RwAppSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (op : RwOp) (base : Nat) (is : List Nat),
    FnSpec (State := State) Vbcf.prog "rw_app"
      (fun vs s => vs = [.ptr sb 0, uv (opC (op.node 0)), uv base, uv is.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ StkTop c st base is)
      (fun _ _ => HPost W sb X c0 prems params c st (fun st' i => pushApp st op is = some (st', i)))

theorem rw_app_spec : RwAppSpec (State := State) := by
  intro W sb X c0 c prems params st op base is
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwApp) rfl
  rintro vs s ⟨rfl, h, hR, htop⟩
  simp [rwApp, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := rwApp) rfl
  simp only [rwApp, Stmt.block, initLocals, List.map, Ty.zero]
  have hlen := htop.1
  have hsp := hR.sp_lt
  simp only [maxPool] at hsp
  h_guard
  intro hn0
  apply WP.seq_mid (RwAppMid1 sb op base is s)
  · apply WP.ite
    rule_simp
    refine ⟨fun hn1 => ?_, fun hn1 => ?_⟩
    · obtain ⟨a, rfl⟩ : ∃ a, is = [a] := by
        rcases is with _ | ⟨a, _ | ⟨b, _⟩⟩
        · simp at hn0
        · exact ⟨a, rfl⟩
        · simp at hn1
      apply WP.ite
      rw [rw_red_eval op (by simp [Env.get])]
      by_cases hred : op.reducible = true
      · simp only [hred, ↓reduceIte]
        refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
        have ha := htop.lt_size (j := 0) (by simp)
        have hcell : rd c.stk base = some (uv (st.id a)) := by
          apply rd_u32
          have := (htop.2 0 a (by simp)).2
          unfold U at this; simpa using this
        have hstk := hR.stk_eq h (by simp at hlen; omega)
        apply WP.ret
        rule_simp [hstk, hcell, LoopQ]
        exact RetsTo.ret (Q := HQ W sb X c0 prems params c st
          (fun st' i => pushApp st op [a] = some (st', i))) _ _ _
          (HRet.id (P := fun st' i => pushApp st op [a] = some (st', i)) h hR (by simpa using ha)
            (rw_pushApp_one hred))
      · simp only [hred, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun h0 => absurd rfl h0, fun _ => ?_⟩
        apply WP.skip
        exact ⟨rfl, rfl, fun _ => by simpa using hred⟩
    · apply WP.skip
      exact ⟨rfl, rfl, fun e => absurd e hn1⟩
  rintro env1 s1 ⟨rfl, rfl, hred⟩
  simp only [rwAppEnv]
  h_guard
  intro hn255
  apply WP.seq_mid (RwAppMid2 sb op base is s1)
  · have hsp0 : 0 < c.k.sp.toNat := by
      have : is.length ≠ 0 := fun e => hn0 (List.eq_nil_of_length_eq_zero e)
      omega
    have hstk := hR.stk_eq h hsp0
    -- reading the header of argument `i`
    have hrd : ∀ j, j < is.length → ∃ a n, st.pool[a]? = some n ∧ st.lv a ∧
        rd c.stk (base + j) = some (uv (st.id a)) ∧
        rd c.pool (st.id a) = some (uv (hdrW n)) := by
      intro j hj
      have hlj := htop.lt_size hj
      obtain ⟨n, hn⟩ := node_of_lv hlj
      refine ⟨_, n, hn, hlj, ?_, hR.core.rdHdr hn hlj⟩
      apply rd_u32
      have := (htop.2 j _ (List.getElem?_eq_getElem hj)).2
      unfold U at this; exact this
    have hidx : ∀ (i : BitVec 32), i.toNat < is.length →
        (BitVec.ofNat 32 base + i).toNat = base + i.toNat := by
      intro i hi
      rw [BitVec.toNat_add, bv_toNat_ofNat (by omega)]; omega
    apply WP.ite
    rule_simp
    refine ⟨fun x hx => ?_, fun hnc => ?_⟩
    · have hop := rw_node0_concat hx
      apply WP.while (RwAppLoop sb op base is s1) ⟨rfl, 0#32, 0#32, 0#32, rfl, by simp⟩
      rintro env s' ⟨rfl, i, t, w, rfl, hi⟩
      simp only [rwAppEnv]
      rule_simp
      refine ⟨fun hge => ⟨rfl, i, t, w, rfl, rw_appW_bv (Or.inr hop) _⟩, fun hlt => ?_⟩
      have hlt' : i.toNat < is.length := by
        rw [BitVec.lt_def, bv_toNat_ofNat (by omega)] at hlt; exact hlt
      obtain ⟨a, n, hn, ha, hcs, hcp⟩ := hrd i.toNat hlt'
      apply WP.rule_ty_of ty_of_spec
      rule_simp [hidx i hlt', hstk, hcs, hcp]
      apply WP.seq
      apply WP.ite
      rule_simp
      refine ⟨fun _ => WP.brk ⟨rfl, i, _, w, rfl, rw_appW_bv (Or.inr hop) _⟩, fun _ => WP.skip ?_⟩
      apply WP.assign_seq
      rule_simp
      apply WP.assign
      rule_simp
      refine ⟨rfl, _, _, _, rfl, ?_⟩
      rw [BitVec.toNat_add]; simp; omega
    have hnc' : op ≠ .concat := by intro e; subst e; exact hnc 0 rfl
    apply WP.ite
    rule_simp
    refine ⟨fun x hx => ?_, fun hns => ?_⟩
    · have hop := rw_node0_size hx
      subst hop
      apply WP.assign
      rule_simp [LoopQ]
      exact ⟨rfl, 0#32, 0#32, 32#32, rfl, rw_appW_size⟩
    have hns' : op ≠ .bvsize := by intro e; subst e; exact hns 32 rfl
    apply WP.ite
    rule_simp [rw_opC_and7, hnc', hns']
    refine ⟨fun hbv => ?_, fun hbv => ?_⟩
    · apply WP.while (RwAppLoop sb op base is s1) ⟨rfl, 0#32, 0#32, 0#32, rfl, by simp⟩
      rintro env s' ⟨rfl, i, t, w, rfl, hi⟩
      simp only [rwAppEnv]
      rule_simp
      refine ⟨fun hge => ⟨rfl, i, t, w, rfl, rw_appW_bv (Or.inl hbv) _⟩, fun hlt => ?_⟩
      have hlt' : i.toNat < is.length := by
        rw [BitVec.lt_def, bv_toNat_ofNat (by omega)] at hlt; exact hlt
      obtain ⟨a, n, hn, ha, hcs, hcp⟩ := hrd i.toNat hlt'
      apply WP.rule_ty_of ty_of_spec
      rule_simp [hidx i hlt', hstk, hcs, hcp]
      apply WP.seq
      apply WP.ite
      rule_simp
      refine ⟨fun _ => ?_, fun _ => WP.skip ?_⟩
      · apply WP.seq
        apply WP.assign
        rule_simp
        apply WP.brk
        exact ⟨rfl, i, _, _, rfl, rw_appW_bv (Or.inl hbv) _⟩
      apply WP.assign
      rule_simp
      refine ⟨rfl, _, _, _, rfl, ?_⟩
      rw [BitVec.toNat_add]; simp; omega
    · apply WP.skip
      simp only [LoopQ]
      exact ⟨rfl, 0#32, 0#32, 0#32, rfl, rw_appW_bool (by simpa using hbv) hnc' hns'⟩
  rintro env2 s2 ⟨rfl, i, t, w, rfl, hw⟩
  simp only [rwAppEnv]
  obtain ⟨wn, rfl⟩ : ∃ wn, w = BitVec.ofNat 32 wn := ⟨w.toNat, (bv_ofNat_toNat w).symm⟩
  h_guard
  intro hw255
  have hw' : wn % 4294967296 < 256 := by omega
  have hwv : (BitVec.ofNat 32 wn).toNat = wn % 4294967296 := by simp
  rw [hwv] at hw
  obtain ⟨hhd, hlo, hhi⟩ := hw hw'
  have hk := rw_opC_lt op
  have hnl := rw_node_leaf op (wn % 4294967296)
  have hhdr : NonLeafHdr (opC (op.node 0) + wn % 4294967296 * 65536) := by
    rw [← hhd]; exact opHdr_nonLeaf hnl hlo hhi
  apply WP.rule_mkn_raw mkn_specT h hR _ base is hhdr htop.2 (by omega)
  refine ⟨?_, ?_⟩
  · have e : BitVec.ofNat 32 wn = BitVec.ofNat 32 (wn % 4294967296) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [e]
    rule_simp [rw_or_shl hk hw']
  intro s' c' r h hB
  rule_simp
  apply WP.ret
  rule_simp
  refine HRet.of_built h hB (fun st' i ⟨n, hh, hf, ha, hpn⟩ => ?_)
  have hn : n = ⟨op.node (wn % 4294967296), is.toArray⟩ :=
    node_of_hdr hf ha (by rw [hh, hhd]; simp) hnl hlo hhi
  subst hn
  obtain ⟨argTys, t', -, hmap, hrt, -⟩ := pushNode_cases hpn
  simp only at hmap
  rw [rw_pushApp_eq hn0 hred hmap, rw_node_width op _ argTys t' hrt]
  exact hpn

end Vbcf.Proof
