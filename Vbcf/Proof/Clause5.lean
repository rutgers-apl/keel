import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Clause4

/-!
# Vbcf proofs: the Clause family, part 5 — `cl_dups`

`cl_dups(st, p, n, na, mb)` is `parseDupPairs` for the `n` disjuncts of `p`, recording
the duplicate positions in the mark table `stk[mb..mb+n)`.  The table is zero on entry
(`r_factoring` pushes `n` zeros right before the call), so no invariant between rules is
needed for it.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- The mark table `stk[mb..mb+n)` records membership in `dups`. -/
def Marks (c : CMem) (mb n : Nat) (dups : List Nat) : Prop :=
  ∀ d, d < n → U c.stk (mb + d) (if d ∈ dups then 1 else 0)

/-- Only the mark table changed. -/
def MarkFrame (c c' : CMem) (mb n : Nat) : Prop :=
  c'.k.sp = c.k.sp ∧ ∀ j, (j < mb ∨ mb + n ≤ j) → c'.stk[j]? = c.stk[j]?

theorem MarkFrame.refl (c : CMem) (mb n : Nat) : MarkFrame c c mb n := ⟨rfl, fun _ _ => rfl⟩

/-- What `cl_dups` returns. -/
def DupsRet (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (args : Array Nat) (mb : Nat) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ MarkFrame c c' mb args.size ∧
    (r = 0#32 ∨ (r = 1#32 ∧ ∃ dups, parseDupPairs args params = some dups ∧
      Marks c' mb args.size dups))

def ClDupsSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (p : Nat) (args : Array Nat) (mb : Nat),
    FnSpec (State := State) Vbcf.prog "cl_dups"
      (fun vs s => vs = [.ptr sb 0, uv (st.id p), uv args.size, uv params.length, uv mb] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧
        st.pool[p]? = some ⟨.disj, args⟩ ∧ mb + args.size ≤ c.k.sp.toNat ∧ Marks c mb args.size [] ∧
        st.lv p)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ DupsRet W sb X c0 c prems params st args mb r s')

/-- The `haspre`/`pre` pair for `preUniq`. -/
def hasPreW (pre : Option Nat) : Nat := if pre = none then 0 else 1

/-- The environment of `cl_dups`. -/
def dupsEnv (sb : Nat) (st : VSt) (p : Nat) (args : Array Nat) (params : List Nat) (mb : Nat)
    (idx : Nat) (wpl wuniq : BitVec 32) (pre : Option Nat) (wj wd : BitVec 32) (cnt : Nat)
    (wb : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("p", .u32, uv (st.id p)),
    ("n", .u32, uv args.size), ("na", .u32, uv params.length), ("mb", .u32, uv mb),
    ("vlen", .u32, uv (params.length * 4)), ("idx", .u32, uv idx), ("pl", .u32, .u32 wpl),
    ("uniq", .u32, .u32 wuniq), ("haspre", .u32, uv (hasPreW pre)), ("pre", .u32, uv (pre.getD 0)),
    ("j", .u32, .u32 wj), ("d", .u32, .u32 wd), ("cnt", .u32, uv cnt), ("b", .u32, .u32 wb)]

/-- Loop invariant of the pair loop. -/
def DupInv (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (p : Nat) (args : Array Nat) (mb : Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (idx : Nat) (dups : List Nat) (pre : Option Nat) (wpl wuniq wj wd wb : BitVec 32),
    env = dupsEnv sb st p args params mb idx wpl wuniq pre wj wd dups.length wb ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ MarkFrame c c' mb args.size ∧
    idx ≤ params.length * 4 ∧ dups.length ≤ idx ∧ pre.getD 0 < 256 ∧
    parseDupPairs args params = clPd args params idx dups pre ∧ Marks c' mb args.size dups

/-- After the pair loop: `parseDupPairs` succeeds if the rest of the bytes are zero. -/
def DupMid (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (p : Nat) (args : Array Nat) (mb : Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (idx : Nat) (dups : List Nat) (pre : Option Nat) (wpl wuniq wj wd wb : BitVec 32),
    env = dupsEnv sb st p args params mb idx wpl wuniq pre wj wd dups.length wb ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ MarkFrame c c' mb args.size ∧
    idx ≤ params.length * 4 ∧ dups.length ≤ params.length * 4 ∧
    ((∀ k, idx ≤ k → k < params.length * 4 → paramByte params k = 0) → dups ≠ [] →
      parseDupPairs args params = some dups) ∧ Marks c' mb args.size dups

/-- The trailing-zero loop. -/
def TailInv (sb : Nat) (s : (KernelState prog State)) (st : VSt) (p : Nat) (args : Array Nat) (params : List Nat)
    (mb : Nat) (idx0 : Nat) (wpl wuniq : BitVec 32) (pre : Option Nat) (wj wd : BitVec 32)
    (cnt : Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  s' = s ∧ ∃ (idx : Nat) (wb : BitVec 32),
    env = dupsEnv sb st p args params mb idx wpl wuniq pre wj wd cnt wb ∧
    idx0 ≤ idx ∧ idx ≤ params.length * 4 ∧ ∀ k, idx0 ≤ k → k < idx → paramByte params k = 0

theorem DupsRet.zero {W : World} {sb : Nat} {X : Ctx} {c0 c c' : CMem} {prems params : List Nat}
    {st : VSt} {args : Array Nat} {mb : Nat} {s' : (KernelState prog State)} (h : Holds W s'.mem sb c')
    (hR : RCtx W X c0 prems params c' st) (hfr : MarkFrame c c' mb args.size) :
    DupsRet W sb X c0 c prems params st args mb 0#32 s' := ⟨c', h, hR, hfr, Or.inl rfl⟩

theorem cw_hasPre (pre : Option Nat) : (BitVec.ofNat 32 (hasPreW pre) = 0#32) ↔ pre = none := by
  unfold hasPreW
  split <;> simp_all

theorem paramByte_lt (params : List Nat) (k : Nat) : paramByte params k < 256 := by
  unfold paramByte
  rw [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The positions recorded by the first `jn - 1` steps of the inner loop. -/
def clNewJ (params : List Nat) (idx jn : Nat) : List Nat :=
  ((List.range' 1 (jn - 1)).map (fun j => paramByte params (idx + 1 + j))).reverse

/-- Loop invariant of the inner loop (one pair). -/
def DupInner (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (p : Nat) (args : Array Nat) (mb : Nat) (idx : Nat) (dups : List Nat) (wb : BitVec 32) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (jn : Nat) (wd : BitVec 32),
    env = dupsEnv sb st p args params mb (idx + 1) (BitVec.ofNat 32 (paramByte params idx))
      (BitVec.ofNat 32 (paramByte params (idx + 1))) (some (paramByte params (idx + 1)))
      (BitVec.ofNat 32 jn) wd (clNewJ params idx jn ++ dups).length wb ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ MarkFrame c c' mb args.size ∧
    1 ≤ jn ∧ jn ≤ paramByte params idx ∧
    (∀ j, 1 ≤ j → j < jn →
      paramByte params (idx + 1 + j) < args.size ∧
      paramByte params (idx + 1) < paramByte params (idx + 1 + j) ∧
      args[paramByte params (idx + 1)]? = args[paramByte params (idx + 1 + j)]?) ∧
    Marks c' mb args.size (clNewJ params idx jn ++ dups)

theorem clNewJ_succ (params : List Nat) (idx : Nat) {jn : Nat} (h : 1 ≤ jn) :
    clNewJ params idx (jn + 1) = paramByte params (idx + 1 + jn) :: clNewJ params idx jn := by
  unfold clNewJ
  rw [show jn + 1 - 1 = (jn - 1) + 1 by omega, cl_range'_snoc, show jn - 1 + 1 = jn by omega]

theorem clNewJ_length (params : List Nat) (idx jn : Nat) : (clNewJ params idx jn).length = jn - 1 := by
  simp [clNewJ]

theorem Marks.set {c : CMem} {mb n d : Nat} {L : List Nat} (hm : Marks c mb n L)
    (hsz : mb + d < c.stk.size) :
    Marks { c with stk := c.stk.setIfInBounds (mb + d) (.u32 1#32) } mb n (d :: L) := by
  intro d' hd'
  unfold U
  simp only
  by_cases e : d = d'
  · subst e
    rw [Array.getElem?_setIfInBounds_self_of_lt hsz]
    simp
  · rw [Array.getElem?_setIfInBounds_ne (by omega)]
    have := hm d' hd'
    unfold U at this
    rw [this]
    simp [List.mem_cons, Ne.symm e]

theorem cl_dups_spec : ClDupsSpec (State := State) := by
  intro W sb X c0 c prems params st p args mb
  have hs := prog_ck
  apply FnSpec.intro' (fn := clDups) rfl
  rintro vs s ⟨rfl, h, hR, hn, hmb, hm0, hp⟩
  simp [clDups, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := clDups) rfl
  simp only [clDups, Stmt.block, initLocals, List.map, Ty.zero]
  have hpar := hR.par.1
  obtain ⟨args', he, hsz, -, hargs⟩ := hR.core.argsN hn rfl (show ¬ IsLeaf Op.disj by decide)
  cases he
  rule_assign [cw_mul]
  apply WP.seq_mid (DupMid W sb X c0 c prems params st p args mb)
  · apply WP.while (I := DupInv W sb X c0 c prems params st p args mb)
    · exact ⟨c, 0, [], none, _, _, _, _, _, rfl, h, hR, MarkFrame.refl c mb args.size, by omega,
        by simp, by simp, parseDupPairs_eq_clPd args params, hm0⟩
    clear h hR
    rintro env s1 ⟨c1, idx, dups, pre, wpl, wuniq, wj, wd, wb, rfl, h, hR, hfr, hidx, hdl, hpre8, hparse, hmk⟩
    simp only [dupsEnv]
    rule_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · exact ⟨c1, idx, dups, pre, wpl, wuniq, wj, wd, wb, rfl, h, hR, hfr, hidx, by omega,
        fun _ hd => by rw [hparse]; exact clPd_ge (by omega) hd, hmk⟩
    have hpl := paramByte_lt params idx
    apply WP.rule_cl_byte h hR idx (by omega)
    refine ⟨by rule_simp, ?_⟩
    rule_simp
    rule_assign
    apply WP.seq
    apply WP.ite
    rule_simp [uv_eq_zero_iff]
    refine ⟨fun hpl0 => WP.brk ?_, fun hpl0 => WP.skip ?_⟩
    · exact ⟨c1, idx + 1, dups, pre, _, wuniq, wj, wd, wb, rfl, h, hR, hfr, by omega, by omega,
        fun hz hd => by rw [hparse]; exact clPd_zero hlt hpl0 hd hz, hmk⟩
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => DupsRet.zero h hR hfr, fun hc hle => ?_⟩
    have hu := paramByte_lt params (idx + 1)
    apply WP.rule_cl_byte h hR (idx + 1) (by omega)
    refine ⟨by rule_simp, ?_⟩
    rule_simp
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => DupsRet.zero h hR hfr, fun hu2 => ?_⟩
    apply WP.guard_lit
    rule_simp [cw_hasPre]
    refine ⟨fun _ _ => DupsRet.zero h hR hfr, fun hpu => ?_⟩
    rule_assign
    rule_assign
    rule_assign
    apply WP.loop_seq (DupInner W sb X c0 c prems params st p args mb idx dups wb)
    · exact ⟨c1, 1, wd, rfl, h, hR, hfr, Nat.le_refl 1, by omega, fun j h1 h2 => by omega, by simpa [clNewJ] using hmk⟩
    clear h hR hfr hmk
    rintro env s2 ⟨c2, jn, wd2, rfl, h, hR, hfr, hj1, hj2, hgood, hmk⟩
    simp only [dupsEnv]
    rule_simp
    refine ⟨fun hge => ?_, fun hlt2 => ?_⟩
    · have hjn : jn = paramByte params idx := by omega
      subst hjn
      apply WP.assign
      rule_simp
      refine ⟨c2, idx + 1 + paramByte params idx, clNew params idx ++ dups,
        some (paramByte params (idx + 1)), BitVec.ofNat 32 (paramByte params idx),
        BitVec.ofNat 32 (paramByte params (idx + 1)), BitVec.ofNat 32 (paramByte params idx), wd2, wb,
        ?_, h, hR, hfr, by omega, ?_, hu, ?_, hmk⟩
      · simp only [dupsEnv, List.length_append]
        rfl
      · rw [List.length_append]
        have := clNewJ_length params idx (paramByte params idx)
        unfold clNewJ at this
        simp only [clNew]
        omega
      · rw [hparse]
        exact clPd_step hlt hpl0 hc hle hu2
          (fun pu e => by subst e; exact hpu (by simp)) hgood
    have hd8 := paramByte_lt params (idx + 1 + jn)
    apply WP.rule_cl_byte h hR (idx + 1 + jn) (by omega)
    refine ⟨by rule_simp, ?_⟩
    rule_simp
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => DupsRet.zero h hR hfr, fun hdn hdu => ?_⟩
    have ha1 := hargs _ hu2
    have ha2 := hargs _ hdn
    apply WP.guard_lit
    rule_simp [hR.core.rdN hn]
    refine ⟨fun _ => DupsRet.zero h hR hfr, fun heq => ?_⟩
    have hsp0 : 0 < c2.k.sp.toNat := by rw [hfr.1]; omega
    have hstk := hR.stk_eq h hsp0
    have hssz := hR.stk_size h hsp0
    rw [hfr.1] at hssz
    apply WP.seq
    apply WP.ck_store .stk h (by rfl) hstk
    ck_simp [hstk, uv_add, uv_toNat (show mb + paramByte params (idx + 1 + jn) < 4294967296 by omega)]
    refine ⟨by omega, ?_⟩
    intro s3 h3
    clear h
    have h := h3
    clear h3
    have hR3 := hR.set_stk (mb + paramByte params (idx + 1 + jn)) (.u32 1#32)
    rule_assign
    apply WP.assign_loop
    rule_simp
    refine ⟨_, jn + 1, BitVec.ofNat 32 (paramByte params (idx + 1 + jn)), ?_, h, hR3,
      ⟨hfr.1, fun j' hj' => ?_⟩, by omega, by omega, ?_, ?_⟩
    · simp only [dupsEnv, clNewJ_succ params idx hj1, List.cons_append, List.length_cons,
        List.length_append]
      rfl
    · simp only
      rw [Array.getElem?_setIfInBounds_ne (by omega)]
      exact hfr.2 j' hj'
    · intro j' h1 h2
      rcases Nat.lt_or_ge j' jn with h3 | h3
      · exact hgood j' h1 h3
      · rw [show j' = jn by omega]
        refine ⟨hdn, hdu, ?_⟩
        rw [Array.getElem?_eq_getElem hu2, Array.getElem?_eq_getElem hdn, heq]
    · rw [clNewJ_succ params idx hj1, List.cons_append]
      exact hmk.set (by omega)
  clear h hR
  rintro env s1 ⟨c1, idx, dups, pre, wpl, wuniq, wj, wd, wb, rfl, h, hR, hfr, hidx, hdl, hparse, hmk⟩
  simp only [dupsEnv]
  apply WP.guard_lit
  rule_simp [uv_eq_zero_iff]
  refine ⟨fun _ => DupsRet.zero h hR hfr, fun hd0 => ?_⟩
  have hd : dups ≠ [] := fun e => by simp [e] at hd0
  apply WP.loop_seq (TailInv sb s1 st p args params mb idx wpl wuniq pre wj wd dups.length)
  · exact ⟨rfl, idx, wb, rfl, Nat.le_refl _, hidx, fun k h1 h2 => by omega⟩
  rintro env s2 ⟨rfl, idx', wb', rfl, hi1, hi2, hz⟩
  simp only [dupsEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · rule_ret
    exact ⟨c1, h, hR, hfr, Or.inr ⟨rfl, dups, hparse (fun k h1 h2 => hz k h1 (by omega)) hd, hmk⟩⟩
  have hb8 := paramByte_lt params idx'
  apply WP.rule_cl_byte h hR idx' (by omega)
  refine ⟨by rule_simp, ?_⟩
  rule_simp
  apply WP.guard_lit
  rule_simp [uv_eq_zero_iff]
  refine ⟨fun _ => DupsRet.zero h hR hfr, fun hb0 => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, idx' + 1, _, rfl, by omega, by omega, fun k h1 h2 => ?_⟩
  rcases Nat.lt_or_ge k idx' with h3 | h3
  · exact hz k h1 h3
  · rw [show k = idx' by omega]; exact hb0

end Vbcf.Proof
