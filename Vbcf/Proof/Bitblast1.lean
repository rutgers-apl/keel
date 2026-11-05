import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly2
import Vbcf.Proof.Bool4
import Vbcf.Proof.Aci4

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- A leaf of a well-typed pool has no arguments. -/
theorem VInv.bb_leaf_args {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) (hl : IsLeaf n.op) : n.args.size = 0 := by
  obtain ⟨argTys, t, -, hrt, -, hlen⟩ := hc.ok.retype hn
  have := resultTy_leaf hl hrt
  subst this
  simp at hlen; omega

/-- The arity field of a node that is not a variable or a literal is its number of arguments. -/
theorem VInv.bb_tailLen {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) (h1 : opC n.op ≠ 0x08) (h2 : opC n.op ≠ 0x18)
    (h3 : opC n.op ≠ 0x19) : tailLen n = n.args.size := by
  by_cases hl : IsLeaf n.op
  · rw [hc.bb_leaf_args hn hl]
    obtain ⟨op, args⟩ := n
    cases op <;> simp_all [opC, tailLen, IsLeaf, isLeaf]
  · exact tailLen_of_not_leaf hl

theorem VInv.bb_tailLen' {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) (h1 : ∀ w v, ¬ n.op = .bvVal w v)
    (h2 : ∀ w v, ¬ n.op = .bvVar w v) (h3 : ∀ v, ¬ n.op = .boolVar v) : tailLen n = n.args.size := by
  apply hc.bb_tailLen hn
  · intro e; obtain ⟨w, v, e⟩ := opC_bvVal_iff.mp e; exact h1 w v e
  · intro e; obtain ⟨w, v, e⟩ := opC_bvVar_iff.mp e; exact h2 w v e
  · intro e; obtain ⟨v, e⟩ := opC_boolVar_iff.mp e; exact h3 v e

def BbNargsSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (i : Nat) (n : Node),
    FnSpec (State := State) Vbcf.prog "bb_nargs"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.pool[i]? = some n ∧ st.lv i)
      (fun _ s => PureRet s n.args.size)

theorem bb_nargs_spec : BbNargsSpec (State := State) := by
  intro W sb X c0 c prems params st i n
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbNargs) rfl
  rintro vs s ⟨rfl, h, hR, hn, hi⟩
  simp [bbNargs, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  rule_assign [hR.core.rdHdr hn]
  have hf := hR.core.rep.fits i n hn
  apply WP.guard_lit
  rule_simp
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hl : IsLeaf n.op := by
      rcases n with ⟨op, args⟩; cases op <;> simp_all [IsLeaf, isLeaf]
    simp [retPost, PureRet, hR.core.bb_leaf_args hn hl]
  · intro h2 h3
    apply WP.ret
    rule_simp [hR.core.rdHdr hn, hdr_len_bv hf, retPost, PureRet]
    rw [hR.core.bb_tailLen' hn hc h2 h3]

/-! ## Read-only helpers -/

/-- What a helper that only reads guarantees when it returns `r`: the state is unchanged,
and a non-zero answer means `P`. -/
def BbOK (s : (KernelState prog State)) (P : Prop) (r : BitVec 32) (s' : (KernelState prog State)) : Prop := s' = s ∧ (r ≠ 0#32 → P)

theorem BbOK.zero {s : (KernelState prog State)} {P : Prop} : BbOK s P 0#32 s := ⟨rfl, fun h => absurd rfl h⟩

/-- `x = f(args); rest` for a read-only helper. -/
theorem WP.bb_call {Q : (Post prog State)} {env : Env} {s : (KernelState prog State)} {x : Var} {f : String}
    {es : List Expr} {rest : Stmt} {vs : List EmbC.Val} {pre : List EmbC.Val → (KernelState prog State) → Prop}
    {P : Prop}
    (hspec : FnSpec (State := State) Vbcf.prog f pre (fun _ s0 rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s0 P r s'))
    (hargs : evalArgs Vbcf.prog env s.mem es = some vs) (hpre : pre vs s)
    (H : ∀ r, (r ≠ 0#32 → P) →
      match env.assign s.mem x (.u32 r) with
      | none => False
      | some env' => WP Vbcf.prog rest Q env' s) :
    WP Vbcf.prog (.seq (.call (some x) f es) rest) Q env s := by
  apply WP.call_seq hspec hargs hpre
  rintro rv s' ⟨r, rfl, rfl, hr⟩
  exact H r hr

/-- A header test: a node whose header word is that of `op` with `k` arguments. -/
theorem VInv.bb_hdr {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) {op : Op} {k : Nat} {hd : BitVec 32}
    (hhd : hd.toNat = opHdr op + k * 256) (hk : k < 256) (hl : ¬ IsLeaf op)
    (hlo : opLo op < 256) (hhi : opHi op < 256) (e : BitVec.ofNat 32 (hdrW n) = hd) :
    n = ⟨op, n.args⟩ ∧ n.args.size = k := by
  have hf := hc.rep.fits i n hn
  have e' : hdrW n = opHdr op + k * 256 := by rw [← hhd, ← e, bv_toNat_ofNat (hdrW_lt hf)]
  have hcode := hdrW_code hf
  have hlen := hdrW_len hf
  have h1 := opC_lt op
  have hl' : ¬ IsLeaf n.op := by
    rw [isLeaf_iff_opC] at hl ⊢; rw [← hcode, e']; unfold opHdr; omega
  rw [tailLen_of_not_leaf hl', e'] at hlen
  have hsz : n.args.size = k := by unfold opHdr at hlen; omega
  exact ⟨node_of_hdr hf rfl (by rw [e', hsz]) hl hlo hhi, hsz⟩

theorem VInv.bb_arg_lt {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) {x : Nat} (hx : x ∈ n.args)
    (hi_lv : st.lv i := by vlv) : st.lv x :=
  hc.arg_lv hn x hx hi_lv

theorem bb_isNode_of {st : St} {i : Nat} {n : Node} (hn : st.pool[i]? = some n) :
    isNode st i n = true := by simp [isNode, hn]

theorem VInv.bb_hdr1 {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) {op : Op} {hd : BitVec 32}
    (hhd : hd.toNat = opHdr op + 1 * 256) (hl : ¬ IsLeaf op)
    (hlo : opLo op < 256) (hhi : opHi op < 256) (e : BitVec.ofNat 32 (hdrW n) = hd) (h_lv : st.lv i := by vlv) :
    ∃ x, n = ⟨op, #[x]⟩ ∧ st.lv x := by
  have hi_lv := h_lv
  obtain ⟨hn', hsz⟩ := hc.bb_hdr hn hhd (by omega) hl hlo hhi e
  obtain ⟨x, hx⟩ := array_eq_one hsz
  rw [hx] at hn'; rw [hn'] at hn
  exact ⟨x, hn', st.args_lv hi_lv hn (by simp)⟩

theorem VInv.bb_hdr2 {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) {op : Op} {hd : BitVec 32}
    (hhd : hd.toNat = opHdr op + 2 * 256) (hl : ¬ IsLeaf op)
    (hlo : opLo op < 256) (hhi : opHi op < 256) (e : BitVec.ofNat 32 (hdrW n) = hd) (h_lv : st.lv i := by vlv) :
    ∃ x y, n = ⟨op, #[x, y]⟩ ∧ st.lv x ∧ st.lv y := by
  have hi_lv := h_lv
  obtain ⟨hn', hsz⟩ := hc.bb_hdr hn hhd (by omega) hl hlo hhi e
  obtain ⟨x, y, hx⟩ := array_eq_two hsz
  rw [hx] at hn'; rw [hn'] at hn
  exact ⟨x, y, hn', st.args_lv hi_lv hn (by simp), st.args_lv hi_lv hn (by simp)⟩

theorem VInv.bb_hdr3 {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) {op : Op} {hd : BitVec 32}
    (hhd : hd.toNat = opHdr op + 3 * 256) (hl : ¬ IsLeaf op)
    (hlo : opLo op < 256) (hhi : opHi op < 256) (e : BitVec.ofNat 32 (hdrW n) = hd) (h_lv : st.lv i := by vlv) :
    ∃ x y z, n = ⟨op, #[x, y, z]⟩ ∧ st.lv x ∧ st.lv y ∧ st.lv z := by
  have hi_lv := h_lv
  obtain ⟨hn', hsz⟩ := hc.bb_hdr hn hhd (by omega) hl hlo hhi e
  obtain ⟨x, y, z, hx⟩ := array_eq_three hsz
  rw [hx] at hn'; rw [hn'] at hn
  exact ⟨x, y, z, hn', st.args_lv hi_lv hn (by simp), st.args_lv hi_lv hn (by simp),
    st.args_lv hi_lv hn (by simp)⟩

def BbIs1Spec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (i : Nat) (hd : BitVec 32) (op : Op) (a : Nat),
    FnSpec (State := State) Vbcf.prog "bb_is1"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i), .u32 hd, uv (st.id a)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv i ∧
        st.lv a ∧ hd.toNat = opHdr op + 1 * 256 ∧ ¬ IsLeaf op ∧ opLo op < 256 ∧
        opHi op < 256)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (isNode st i ⟨op, #[a]⟩ = true) r s')

theorem bb_is1_spec : BbIs1Spec (State := State) := by
  intro W sb X c0 c prems params st i hd op a
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbIs1) rfl
  rintro vs s ⟨rfl, h, hR, hi, ha, hhd, hl, hlo, hhi⟩
  simp [bbIs1, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbIs1) rfl
  simp only [bbIs1, Stmt.block, initLocals, List.map]
  obtain ⟨n, hn⟩ := node_of_lv hi
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hn]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun he => ?_⟩
  obtain ⟨hn', hsz⟩ := hR.core.bb_hdr hn hhd (by omega) hl hlo hhi he
  obtain ⟨x, hx⟩ := array_eq_one hsz
  rw [hx] at hn'; rw [hn'] at hn
  have hxl : st.lv x := hR.core.bb_arg_lt hn (by simp)
  apply WP.rule_ret
  rule_simp [hR.core.rd1 hn hl]
  refine ⟨rfl, fun h0 => ?_⟩
  by_cases e : x = a
  · subst e; exact bb_isNode_of hn
  · simp [e] at h0

def BbIs2Spec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (i : Nat) (hd : BitVec 32) (op : Op) (a b : Nat),
    FnSpec (State := State) Vbcf.prog "bb_is2"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i), .u32 hd, uv (st.id a),
          uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv i ∧
        st.lv a ∧ st.lv b ∧ hd.toNat = opHdr op + 2 * 256 ∧ ¬ IsLeaf op ∧
        opLo op < 256 ∧ opHi op < 256)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (isNode st i ⟨op, #[a, b]⟩ = true) r s')

theorem bb_is2_spec : BbIs2Spec (State := State) := by
  intro W sb X c0 c prems params st i hd op a b
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbIs2) rfl
  rintro vs s ⟨rfl, h, hR, hi, ha, hb, hhd, hl, hlo, hhi⟩
  simp [bbIs2, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbIs2) rfl
  simp only [bbIs2, Stmt.block, initLocals, List.map]
  obtain ⟨n, hn⟩ := node_of_lv hi
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hn]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun he => ?_⟩
  obtain ⟨hn', hsz⟩ := hR.core.bb_hdr hn hhd (by omega) hl hlo hhi he
  obtain ⟨x, y, hx⟩ := array_eq_two hsz
  rw [hx] at hn'; rw [hn'] at hn
  have hxl : st.lv x := hR.core.bb_arg_lt hn (by simp)
  have hyl : st.lv y := hR.core.bb_arg_lt hn (by simp)
  apply WP.rule_ret
  rule_simp [hR.core.rd2 hn hl]
  refine ⟨rfl, fun h0 => ?_⟩
  by_cases e : x = a
  · by_cases e2 : y = b
    · subst e e2; exact bb_isNode_of hn
    · simp [e, e2] at h0
  · simp [e] at h0

/-! ## Lists, one position at a time -/

theorem bb_allIdx_drop (f : Nat → Nat → Bool) (l : List Nat) {i : Nat} (hi : i < l.length) :
    allIdx f i (l.drop i) = (f i l[i] && allIdx f (i + 1) (l.drop (i + 1))) := by
  rw [List.drop_eq_getElem_cons hi]; rfl

/-- One more position checked. -/
theorem bb_allIdx_step {f : Nat → Nat → Bool} {l : List Nat} {i : Nat} {P : Prop}
    (hi : i < l.length) (H : allIdx f i (l.drop i) = true → P) (hf : f i l[i] = true) :
    allIdx f (i + 1) (l.drop (i + 1)) = true → P := fun h' =>
  H (by rw [bb_allIdx_drop f l hi, hf, h']; rfl)

theorem bb_allIdx_end {f : Nat → Nat → Bool} {l : List Nat} {i : Nat} {P : Prop}
    (hi : l.length ≤ i) (H : allIdx f i (l.drop i) = true → P) : P :=
  H (by rw [List.drop_of_length_le hi]; rfl)

/-! ## `bb_var` -/

/-- The arguments of a non-leaf node: at most 255, all nodes. -/
theorem VInv.bb_args {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {op : Op} {args : Array Nat} (hn : st.pool[i]? = some ⟨op, args⟩) (hl : ¬ IsLeaf op) (h_lv : st.lv i := by vlv) :
    args.size ≤ 255 ∧ ∀ (k : Nat) (hk : k < args.size), st.lv args[k] := by
  have hi_lv := h_lv
  obtain ⟨args', he, hsz, -, hargs⟩ := hc.argsN hn rfl hl
  cases he
  exact ⟨hsz, hargs⟩

theorem bb_bitof_hdr {k : Nat} (hk : k < 256) :
    (329#32 ||| BitVec.ofNat 32 k <<< 16).toNat = opHdr (.boolBitof k) + 1 * 256 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, bv_toNat_ofNat (n := k) (by omega),
    Nat.mod_eq_of_lt (by omega : k * 2 ^ 16 < 2 ^ 32)]
  have e : (329#32 : BitVec 32).toNat = 329 := rfl
  rw [e, Nat.or_comm, show k * 2 ^ 16 = k <<< 16 by rw [Nat.shiftLeft_eq],
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega : 329 < 2 ^ 16), Nat.shiftLeft_eq]
  simp [opHdr, opC, opLo, opHi]; omega

/-- Setting several `u32` variables. -/
def bbSets (env : Env) : List (Var × BitVec 32) → Env
  | [] => env
  | (x, v) :: r => bbSets (env.set x (.u32 v)) r

/-- Loop invariant of a read-only loop with counter `iv`: the state is unchanged, the counter
is `k ≤ n`, the scratch variables `vs` hold some words, and `P k`. -/
def BbInv (s : (KernelState prog State)) (env0 : Env) (iv : Var) (vs : List Var) (n : Nat) (P : Nat → Prop) :
    Env → (KernelState prog State) → Prop :=
  fun env s' => s' = s ∧ ∃ (k : Nat) (ws : List (BitVec 32)), ws.length = vs.length ∧
    env = bbSets (env0.set iv (uv k)) (vs.zip ws) ∧ k ≤ n ∧ P k

/-- `while (cond) body; rest` with an invariant that may mention the environment on entry. -/
theorem WP.bb_loop {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {cond : Expr}
    {body rest : Stmt} (I : Env → Env → (KernelState P State) → Prop) (h0 : I env env s)
    (hstep : ∀ env' s', I env env' s' →
      match evalE P env' s'.mem cond with
      | some (.u32 v) => (v = 0 → WP P rest Q env' s') ∧ (v ≠ 0 → WP P body (LoopQ (I env) Q) env' s')
      | _ => False) :
    WP P (.seq (.while cond body) rest) Q env s :=
  WP.loop_seq (I env) h0 hstep

def BbVarSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b : Nat) (bs : Array Nat),
    FnSpec (State := State) Vbcf.prog "bb_var"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv a ∧
        st.pool[b]? = some ⟨.bvFromBool, bs⟩ ∧ st.lv b)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (Bcf.bbVar st a bs.toList = true) r s')

theorem bb_var_spec : BbVarSpec (State := State) := by
  intro W sb X c0 c prems params st a b bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbVar) rfl
  rintro vs s ⟨rfl, h, hR, ha, hn, hb⟩
  simp [bbVar, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbVar) rfl
  simp only [bbVar, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hsz, hargs⟩ := hR.core.bb_args hn (by decide)
  rule_assign [(hR.core.rdN hn).1, (hR.core.rdN hn).2.1]
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" ["ok"] bs.size
    (fun k => allIdx (fun i b => isNode st b ⟨.boolBitof i, #[a]⟩) k (bs.toList.drop k) = true →
      Bcf.bbVar st a bs.toList = true))
  · exact ⟨rfl, 0, [0#32], rfl, by simp [bbSets, Env.set], by omega, fun h => h⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain ⟨ok, rfl⟩ := len_shape 1 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact bb_allIdx_end (by simp; omega) hres
  have hbk := hargs k hlt
  refine WP.bb_call (bb_is1_spec W sb X c0 c prems params st bs[k]
    (329#32 ||| BitVec.ofNat 32 k <<< 16) (.boolBitof k) a) ?_
    ⟨rfl, h, hR, hbk, ha, bb_bitof_hdr (by omega), by simp [IsLeaf, isLeaf], by simp [opLo]; omega,
      by simp [opHi]⟩ ?_
  · rule_simp [(hR.core.rdN hn).2.2 k hlt]
  intro r hr
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hr0 => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, k + 1, [r], rfl, by simp [bbSets, Env.set], by omega, ?_⟩
  exact bb_allIdx_step (by simpa using hlt) hres (by simpa using hr hr0)

/-! ## `bb_val` -/

theorem bb_bit_word {x k : Nat} (hx : x < 2 ^ 32) (_hk : k < 32) :
    (BitVec.ofNat 32 x >>> k &&& 1#32) = if x.testBit k then 1#32 else 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, bv_toNat_ofNat hx, Nat.shiftRight_eq_div_pow]
  have : (1#32 : BitVec 32).toNat = 1 := rfl
  rw [this, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq]
  split
  · rename_i h; simp at h; simp [h]
  · rename_i h; simp at h; simp; omega

theorem bb_uv_sub {a b : Nat} (ha : a < 2 ^ 32) (hb : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, bv_toNat_ofNat ha, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]
  omega

theorem bb_testBit_lo {v k : Nat} (hk : k < 32) : (v % 4294967296).testBit k = v.testBit k := by
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, Nat.testBit_mod_two_pow]; simp [hk]

theorem bb_testBit_hi {v k : Nat} (hk : 32 ≤ k) :
    (v / 4294967296).testBit (k - 32) = v.testBit k := by
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, Nat.testBit_div_two_pow,
    show k - 32 + 32 = k by omega]

theorem bb_testBit_big {v k w : Nat} (hv : v < 2 ^ w) (hk : w ≤ k) : v.testBit k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hk))

def BbValSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b w v : Nat) (args bs : Array Nat),
    FnSpec (State := State) Vbcf.prog "bb_val"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧
        st.pool[a]? = some ⟨.bvVal w v, args⟩ ∧ st.lv a ∧ st.pool[b]? = some ⟨.bvFromBool, bs⟩∧ st.lv b )
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (Bcf.bbVal X.bi v bs.toList = true) r s')

theorem bb_val_spec : BbValSpec (State := State) := by
  intro W sb X c0 c prems params st a b w v args bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbVal) rfl
  rintro vs s ⟨rfl, h, hR, ha, hal, hn, hb⟩
  simp [bbVal, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbVal) rfl
  simp only [bbVal, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hsz, hargs⟩ := hR.core.bb_args hn (by decide)
  have hfa := hR.core.rep.fits a _ ha
  obtain ⟨hw0, hw64, hv⟩ := aci_typed_val hR.core ha rfl
  have hc1 := hR.core.rep.tail ha (k := 0) (w := v % 2 ^ 32) (by simp [tailW]; split <;> simp)
  rule_assign [(hR.core.rdN hn).1, (hR.core.rdN hn).2.1]
  rule_assign [hR.core.rdHdr ha, hdr_len_bv hfa]
  have htl : tailLen ⟨.bvVal w v, args⟩ = if w ≤ 32 then 1 else 2 := by simp [tailLen]
  have hvl1 : 1 ≤ tailLen ⟨.bvVal w v, args⟩ := by rw [htl]; split <;> omega
  have hvl2 : tailLen ⟨.bvVal w v, args⟩ ≤ 2 := by rw [htl]; split <;> omega
  have hvl3 : 2 ≤ tailLen ⟨.bvVal w v, args⟩ → 32 < w := by rw [htl]; split <;> omega
  have hvl4 : 32 < w → 2 ≤ tailLen ⟨.bvVal w v, args⟩ := by rw [htl]; split <;> omega
  generalize tailLen ⟨.bvVal w v, args⟩ = vl at hvl1 hvl2 hvl3 hvl4
  simp only [Nat.add_zero] at hc1
  have hv64 : v < 2 ^ 64 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw64)
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" ["bit", "x"] bs.size
    (fun k => allIdx (fun i b => if v.testBit i then b == X.bi.tt else b == X.bi.ff) k
      (bs.toList.drop k) = true → Bcf.bbVal X.bi v bs.toList = true))
  · exact ⟨rfl, 0, [0#32, 0#32], rfl, by simp [bbSets, Env.set], by omega, fun h => h⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain ⟨bt, x, rfl⟩ := len_shape 2 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact bb_allIdx_end (by simp; omega) hres
  have hbk := hargs k hlt
  rule_assign
  apply WP.seq_mid_env (fun env0 env' s'' => s'' = s' ∧
    env' = env0.set "bit" (.u32 (if v.testBit k then 1#32 else 0#32)))
  · apply WP.ite
    rule_simp
    refine ⟨fun hk32 => ?_, fun hk32 => ?_⟩
    · apply WP.ite
      rule_simp [hvl1]
      apply WP.assign
      rule_simp [rd_u32 hc1, bb_bit_word (Nat.mod_lt v (by decide : 2 ^ 32 > 0)) hk32, LoopQ, hk32,
        bb_testBit_lo hk32]
    · apply WP.ite
      rule_simp
      refine ⟨fun hk64 => ?_, fun hk64 => ?_⟩
      · apply WP.ite
        by_cases hw32 : 32 < w
        · have hc2 : U c.pool (st.id a + 2) (v / 2 ^ 32) := by
            have := hR.core.rep.tail ha (k := 1) (w := v / 2 ^ 32)
              (by simp [tailW, show ¬ w ≤ 32 by omega])
            rwa [Nat.add_assoc] at this
          have hhi : v / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by simpa using hv64)
          rule_simp [hvl4 hw32]
          apply WP.assign
          rule_simp [rd_u32 hc2, bb_uv_sub (show k < 2 ^ 32 by omega) hk32,
            show k - 32 < 32 by omega, bb_bit_word hhi (show k - 32 < 32 by omega), LoopQ,
            bb_testBit_hi hk32]
        · have hvl : vl < 2 := by omega
          rule_simp [hvl]
          apply WP.skip
          rule_simp [LoopQ, bb_testBit_big hv (show w ≤ k by omega)]
      · apply WP.skip
        rule_simp [LoopQ, bb_testBit_big hv (show w ≤ k by omega)]
  rintro env' s'' ⟨rfl, rfl⟩
  rule_assign [(hR.core.rdN hn).2.2 k hlt]
  apply WP.seq
  apply WP.ite
  have htt := hR.tt_lt
  have hff := hR.ff_lt
  by_cases hbit : v.testBit k
  · rule_simp [hbit]
    apply WP.ite
    rule_simp
    refine ⟨fun hne => ?_, fun he => ?_⟩
    · apply WP.ret; rule_simp [LoopQ, RetQ, BbOK.zero]
    apply WP.skip
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, k + 1, [1#32, BitVec.ofNat 32 (st.id bs[k])], rfl, by simp [bbSets, Env.set], by omega, ?_⟩
    exact bb_allIdx_step (by simpa using hlt) hres (by simp [hbit, he])
  · rule_simp [hbit]
    apply WP.ite
    rule_simp
    refine ⟨fun hne => ?_, fun he => ?_⟩
    · apply WP.ret; rule_simp [LoopQ, RetQ, BbOK.zero]
    apply WP.skip
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, k + 1, [0#32, BitVec.ofNat 32 (st.id bs[k])], rfl, by simp [bbSets, Env.set], by omega, ?_⟩
    exact bb_allIdx_step (by simpa using hlt) hres (by simp [hbit, he])

/-! ## `bb_ite_bit`, `bb_ite` -/

def BbIteBitSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (cc t e b : Nat),
    FnSpec (State := State) Vbcf.prog "bb_ite_bit"
      (fun vs s => vs = [.ptr sb 0, uv (st.id cc), uv (st.id t), uv (st.id e),
          uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv cc ∧
        st.lv t ∧ st.lv e ∧ st.lv b)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (Bcf.bbIteBit st cc t e b = true) r s')

theorem bb_ite_bit_spec : BbIteBitSpec (State := State) := by
  intro W sb X c0 c prems params st cc t e b
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbIteBit) rfl
  rintro vs s ⟨rfl, h, hR, hcc, ht, he, hb⟩
  simp [bbIteBit, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbIteBit) rfl
  simp only [bbIteBit, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnb]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh => ?_⟩
  obtain ⟨d1, d2, rfl, hd1, hd2⟩ := hR.core.bb_hdr2 hnb (op := .conj) (by decide) (by decide)
    (by decide) (by decide) hh
  rule_assign [hR.core.rd2 hnb]
  rule_assign [hR.core.rd2 hnb]
  refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st d2 577#32 .disj cc e) ?_
    ⟨rfl, h, hR, hd2, hcc, he, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp
  intro r hr
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hr0 => ?_⟩
  obtain ⟨n1, hn1⟩ := node_of_lv hd1
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hn1]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh1 => ?_⟩
  obtain ⟨x, t', rfl, hx, ht'⟩ := hR.core.bb_hdr2 hn1 (op := .disj) (by decide) (by decide)
    (by decide) (by decide) hh1
  refine WP.bb_call (bb_is1_spec W sb X c0 c prems params st x 385#32 .boolNot cc) ?_
    ⟨rfl, h, hR, hx, hcc, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hR.core.rd2 hn1]
  intro r2 hr2
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hr20 => ?_⟩
  apply WP.rule_ret
  rule_simp [hR.core.rd2 hn1]
  refine ⟨rfl, fun hne => ?_⟩
  have htt : t' = t := by
    by_cases hc : t' = t
    · exact hc
    · simp [hc] at hne
  have e1 := hr hr0
  have e2 := hr2 hr20
  simp only [Bcf.bbIteBit, hnb, hn1]
  simp only [e1, isNotOf, e2, htt, beq_self_eq_true, Bool.and_self]

/-- The per-bit test of `bbIte`. -/
def bbIteF (st : St) (cc : Nat) (ts es : List Nat) (i b : Nat) : Bool :=
  match ts[i]?, es[i]? with
  | some t, some e => Bcf.bbIteBit st cc t e b
  | _, _ => false

theorem bbIte_eq (st : St) (cc : Nat) (ts es bs : List Nat) :
    Bcf.bbIte st cc ts es bs = allIdx (bbIteF st cc ts es) 0 bs := rfl

def BbIteSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (cc t e b : Nat) (ts es bs : Array Nat),
    FnSpec (State := State) Vbcf.prog "bb_ite"
      (fun vs s => vs = [.ptr sb 0, uv (st.id cc), uv (st.id t), uv (st.id e),
          uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv cc ∧
        st.pool[t]? = some ⟨.bvFromBool, ts⟩ ∧ st.lv t ∧ st.pool[e]? = some ⟨.bvFromBool, es⟩ ∧ st.lv e ∧
        st.pool[b]? = some ⟨.bvFromBool, bs⟩∧ st.lv b )
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (Bcf.bbIte st cc ts.toList es.toList bs.toList = true) r s')

theorem bb_ite_spec : BbIteSpec (State := State) := by
  intro W sb X c0 c prems params st cc t e b ts es bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbIte) rfl
  rintro vs s ⟨rfl, h, hR, hcc, hnt, ht, hne, he, hnb, hb⟩
  simp [bbIte, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbIte) rfl
  simp only [bbIte, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hszb, hargsb⟩ := hR.core.bb_args hnb (by decide)
  obtain ⟨hszt, hargst⟩ := hR.core.bb_args hnt (by decide)
  obtain ⟨hsze, hargse⟩ := hR.core.bb_args hne (by decide)
  rule_assign [(hR.core.rdN hnb).1, (hR.core.rdN hnb).2.1]
  rule_assign [(hR.core.rdN hnt).1, (hR.core.rdN hnt).2.1]
  rule_assign [(hR.core.rdN hne).1, (hR.core.rdN hne).2.1]
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" ["ok"] bs.size
    (fun k => allIdx (bbIteF st cc ts.toList es.toList) k (bs.toList.drop k) = true →
      Bcf.bbIte st cc ts.toList es.toList bs.toList = true))
  · exact ⟨rfl, 0, [0#32], rfl, by simp [bbSets, Env.set], by omega, fun h => h⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain ⟨ok, rfl⟩ := len_shape 1 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact bb_allIdx_end (by simp; omega) hres
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hkt hke => ?_⟩
  refine WP.bb_call (bb_ite_bit_spec W sb X c0 c prems params st cc ts[k] es[k] bs[k]) ?_
    ⟨rfl, h, hR, hcc, hargst k hkt, hargse k hke, hargsb k hlt⟩ ?_
  · rule_simp [(hR.core.rdN hnb).2.2 k hlt, (hR.core.rdN hnt).2.2 k hkt, (hR.core.rdN hne).2.2 k hke]
  intro r hr
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hr0 => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, k + 1, [r], rfl, by simp [bbSets, Env.set], by omega, ?_⟩
  refine bb_allIdx_step (by simpa using hlt) hres ?_
  simp [bbIteF, hkt, hke, hr hr0]

end Vbcf.Proof
