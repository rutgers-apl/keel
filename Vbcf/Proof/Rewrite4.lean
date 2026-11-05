import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite3

/-!
# Vbcf proofs: the Rewrite family, part 4 — the node-building ends of `instE`

`rw_sym`, `rw_max`, `rw_ext`, `rw_ite`, `rw_extract`: each is the last step of one case of
`Bcf.instE`, after the sub-patterns have been instantiated.  The Lean side of each is a
named function (`rwSymTail`, …), and `rw_instE_*` restate `instE` with them.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## The Lean tails -/

def rwSymTail (st : St) (v s : Nat) : Option (St × Nat) :=
  match constNat st v, constNat st s with
  | some vn, some sn => pushLit st sn vn
  | _, _ => none

def rwMaxTail (st : St) (s : Nat) : Option (St × Nat) :=
  match constNat st s with
  | some sn => pushLit st sn (2 ^ sn - 1)
  | none => none

/-- The operator of `zext` (tag 9), `sext` (tag 10), `repeat` (tag 11). -/
def rwExtOp (tag n k : Nat) : Op :=
  if tag = RwEnc.tRepeat then .bvRepeat (n * k) k
  else if tag = RwEnc.tZext then .bvZeroExtend (n + k) k
  else .bvSignExtend (n + k) k

def rwExtTail (st : St) (tag e xi : Nat) : Option (St × Nat) :=
  match constNat st e, st.tys[xi]? with
  | some k, some (.bv n) => if k ≤ 255 then pushNode st ⟨rwExtOp tag n k, #[xi]⟩ else none
  | _, _ => none

def rwIteTail (st : St) (ci ti ei : Nat) : Option (St × Nat) :=
  match st.tys[ti]? with
  | some .bool => pushNode st ⟨.boolIte, #[ci, ti, ei]⟩
  | some (.bv w) => pushNode st ⟨.bvIte w, #[ci, ti, ei]⟩
  | _ => none

def rwExtractTail (st : St) (hi lo xi : Nat) : Option (St × Nat) :=
  match constNat st hi, constNat st lo with
  | some h, some l => if h ≤ 255 ∧ l ≤ 255 then pushNode st ⟨.bvExtract h l, #[xi]⟩ else none
  | _, _ => none

/-! ## Calling `rw_const` -/

section calls
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {args : List Expr} {rest : Stmt}

/-- `x = rw_const(st, e); rest`, where `e` evaluates to the id of `i`. -/
theorem WP.rw_const_call (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (i : Nat)
    (hi : st.lv i)
    (H : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, uv (st.id i)] ∧
      ∀ r wk er vl s', Holds W s'.mem sb (c.wev wk er vl) →
        (r ≠ 0#32 → ∃ x, constNat st i = some x ∧ vl.toNat = x) →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "rw_const" args) rest) Q env s := by
  apply WP.call_seq (rw_const_spec W sb X c0 c prems params st i) H.1 ⟨rfl, h, hR, hi⟩
  rintro rv s' ⟨r, rfl, wk, er, vl, h', hr⟩
  exact H.2 r wk er vl s' h' hr

end calls

theorem rw_wev_stk (c : CMem) (wk er : BitVec 32) (vl : BitVec 64) :
    (c.wev wk er vl).stk = c.stk ∧ (c.wev wk er vl).k.sp = c.k.sp := ⟨rfl, rfl⟩

/-! ## `rw_sym` -/

def RwSymSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (a b : Nat),
    FnSpec (State := State) Vbcf.prog "rw_sym"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv a ∧ st.lv b)
      (fun _ _ => HPost W sb X c0 prems params c st (fun st' i => rwSymTail st a b = some (st', i)))

theorem rw_sym_spec : RwSymSpec (State := State) := by
  intro W sb X c0 c prems params st a b
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwSym) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb⟩
  simp [rwSym, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := rwSym) rfl
  simp only [rwSym, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rw_const_call h hR a ha
  refine ⟨by rule_simp, ?_⟩
  intro r1 wk1 er1 vl1 s1 h1 hr1
  have hR1 := hR.wev (wk := wk1) (er := er1) (vl := vl1)
  clear h
  have h := h1
  rule_simp
  h_guard
  intro hne1
  obtain ⟨xv, hxv, hvl1⟩ := hr1 hne1
  rule_assign
  clear hR
  have hR := hR1
  apply WP.rw_const_call h hR b hb
  refine ⟨by rule_simp, ?_⟩
  intro r2 wk2 er2 vl2 s2 h2 hr2
  have hR2 := hR.wev (wk := wk2) (er := er2) (vl := vl2)
  clear h
  have h := h2
  rule_simp
  h_guard
  intro hne2
  obtain ⟨yv, hyv, hvl2⟩ := hr2 hne2
  rule_assign
  clear hR
  have hR := hR2
  apply WP.rule_hcall (rw_lit_spec W sb X c0 _ prems params st vl2 vl1) (by rule_simp) ⟨rfl, h, hR⟩
  intro s3 c3 r3 h3 hB
  rule_simp
  apply WP.ret
  rule_simp
  exact HRet.of_built2 h3 (VExt.refl st) ⟨by rfl, by rfl⟩ hB (fun st' i hP => by
    simp [rwSymTail, hxv, hyv, ← hvl1, ← hvl2, hP])

/-! ## `rw_max` -/

def RwMaxSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt) (a : Nat),
    FnSpec (State := State) Vbcf.prog "rw_max"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.lv a)
      (fun _ _ => HPost W sb X c0 prems params c st (fun st' i => rwMaxTail st a = some (st', i)))

theorem rw_max_spec : RwMaxSpec (State := State) := by
  intro W sb X c0 c prems params st a
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwMax) rfl
  rintro vs s ⟨rfl, h, hR, ha⟩
  simp [rwMax, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := rwMax) rfl
  simp only [rwMax, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rw_const_call h hR a ha
  refine ⟨by rule_simp, ?_⟩
  intro r1 wk1 er1 vl1 s1 h1 hr1
  have hR1 := hR.wev (wk := wk1) (er := er1) (vl := vl1)
  clear h
  have h := h1
  rule_simp
  h_guard
  intro hne1
  obtain ⟨sn, hsn, hvl1⟩ := hr1 hne1
  rule_assign
  clear hR
  have hR := hR1
  h_guard
  intro hy0 hy64
  have hs1 : 1 ≤ sn := by
    have : vl1.toNat ≠ 0 := fun e => hy0 (BitVec.eq_of_toNat_eq (by simpa using e))
    omega
  have h64 : sn ≤ 64 := by rw [BitVec.le_def] at hy64; simp at hy64; omega
  have hw : vl1.setWidth 32 = BitVec.ofNat 32 sn := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, bv_toNat_ofNat (by omega)]; omega
  apply WP.call_seq (mask64_spec (vl1.setWidth 32)) (by rule_simp) rfl
  rintro rv s2 ⟨rfl, rfl⟩
  rule_simp
  apply WP.rule_hcall (rw_lit_spec W sb X c0 _ prems params st vl1 (mask64M (vl1.setWidth 32)))
    (by rule_simp) ⟨rfl, h, hR⟩
  intro s3 c3 r3 h3 hB
  rule_simp
  apply WP.ret
  rule_simp
  exact HRet.of_built2 h3 (VExt.refl st) ⟨by rfl, by rfl⟩ hB (fun st' i hP => by
    rw [hw, mask64M_toNat hs1 h64, hvl1] at hP
    simp [rwMaxTail, hsn, hP])

/-! ## `rw_ext` -/

/-- A header `code | a << 16 | b << 24`. -/
theorem rw_hdr3 {a b k : Nat} (ha : a < 256) (hb : b < 256) (hk : k < 256) :
    BitVec.ofNat 32 k ||| BitVec.ofNat 32 a <<< 16 ||| BitVec.ofNat 32 b <<< 24 =
      BitVec.ofNat 32 (k + (a + b * 256) * 65536) := by
  rw [rw_or_shl hk ha]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega),
    bv_toNat_ofNat (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by simp; omega), Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : k + a * 65536 < 2 ^ 24),
    Nat.shiftLeft_eq]
  simp; omega

def RwExtSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (tag a b : Nat),
    FnSpec (State := State) Vbcf.prog "rw_ext"
      (fun vs s => vs = [.ptr sb 0, uv tag, uv (st.id a), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv a ∧
        st.lv b ∧ (tag = 9 ∨ tag = 10 ∨ tag = 11))
      (fun _ _ => HPost W sb X c0 prems params c st (fun st' i => rwExtTail st tag a b = some (st', i)))

theorem rw_ext_spec : RwExtSpec (State := State) := by
  intro W sb X c0 c prems params st tag a b
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwExt) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb, htag⟩
  simp [rwExt, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := rwExt) rfl
  simp only [rwExt, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rw_const_call h hR a ha
  refine ⟨by rule_simp, ?_⟩
  intro r1 wk1 er1 vl1 s1 h1 hr1
  have hR1 := hR.wev (wk := wk1) (er := er1) (vl := vl1)
  have hstk1 := rw_wev_stk c wk1 er1 vl1
  have hval := wev_k_val c wk1 er1 vl1
  generalize c.wev wk1 er1 vl1 = c1 at h1 hR1 hstk1 hval
  clear h hR
  have h := h1
  have hR := hR1
  clear h1 hR1
  rule_simp
  h_guard
  intro hne1
  obtain ⟨kn, hkn, hvl1⟩ := hr1 hne1
  rule_assign [hval]
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  obtain ⟨t, ht, hty, hfit⟩ := hR.core.tyOf hnb
  apply WP.rule_ty_of ty_of_spec
  rule_simp [hR.core.rdHdr hnb, hty]
  cases t with
  | bool => h_guard
  | list e k =>
    h_guard
    intro h0
    have := tyW_list_ge e k
    simp only [TyFits] at hfit
    rw [Nat.mod_eq_of_lt (by rw [tyW_list]; split <;> omega)] at h0
    omega
  | bv m =>
  simp only [TyFits] at hfit
  h_guard
  intro hm
  h_guard
  intro hk255
  have hkn255 : kn ≤ 255 := by rw [BitVec.le_def] at hk255; simp at hk255; omega
  have hkw : vl1.setWidth 32 = BitVec.ofNat 32 kn := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, bv_toNat_ofNat (by omega)]; omega
  rule_assign [hkw]
  have hmk : m * kn ≤ 65280 := Nat.mul_le_mul (show m ≤ 256 by omega) hkn255
  have htg : tag < 4294967296 := by omega
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h11 => ?_, fun h11 => ?_⟩
  · subst h11
    apply WP.h_guard h
    rule_simp [cw_mul]
    intro hmk'
    apply WP.rule_mk1 mk1_specT h hR (.bvRepeat (m * kn) kn)
      (BitVec.ofNat 32 (opHdr (.bvRepeat (m * kn) kn))) b hb (by simp [IsLeaf, isLeaf])
      (by simp [opLo]; omega) (by simp [opHi]; omega)
      (by rw [bv_toNat_ofNat (opHdr_lt (by simp [opLo]; omega) (by simp [opHi]; omega))])
    refine ⟨?_, ?_⟩
    · rule_simp [cw_mul, rw_hdr3 (show m * kn < 256 by omega) (show kn < 256 by omega)
        (show 168 < 256 by omega)]
      simp [opHdr, opC, opLo, opHi]
    intro s' c' r h' hB
    rule_simp
    apply WP.ret
    rule_simp [LoopQ]
    exact HRet.of_built2 h' (VExt.refl st) hstk1 hB (fun st' i hP => by
      simp [rwExtTail, hkn, ht, rwExtOp, RwEnc.tRepeat, hkn255, hP])
  h_guard
  intro hmk'
  have hmk2 : m + kn ≤ 255 := by omega
  have hRT : RwEnc.tRepeat = 11 := rfl
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h9 => ?_, fun h9 => ?_⟩
  · subst h9
    apply WP.rule_mk1 mk1_specT h hR (.bvZeroExtend (m + kn) kn)
      (BitVec.ofNat 32 (opHdr (.bvZeroExtend (m + kn) kn))) b hb (by simp [IsLeaf, isLeaf])
      (by simp [opLo]; omega) (by simp [opHi]; omega)
      (by rw [bv_toNat_ofNat (opHdr_lt (by simp [opLo]; omega) (by simp [opHi]; omega))])
    refine ⟨?_, ?_⟩
    · rule_simp [rw_hdr3 (show m + kn < 256 by omega) (show kn < 256 by omega)
        (show 88 < 256 by omega)]
      simp [opHdr, opC, opLo, opHi]
    intro s' c' r h' hB
    rule_simp
    apply WP.ret
    rule_simp [LoopQ]
    exact HRet.of_built2 h' (VExt.refl st) hstk1 hB (fun st' i hP => by
      simp [rwExtTail, hkn, ht, rwExtOp, RwEnc.tRepeat, RwEnc.tZext, hkn255, hP])
  have h10 : tag = 10 := by simp [RwEnc.tRepeat, RwEnc.tZext] at h11 h9; omega
  subst h10
  apply WP.rule_mk1 mk1_specT h hR (.bvSignExtend (m + kn) kn)
    (BitVec.ofNat 32 (opHdr (.bvSignExtend (m + kn) kn))) b hb (by simp [IsLeaf, isLeaf])
    (by simp [opLo]; omega) (by simp [opHi]; omega)
    (by rw [bv_toNat_ofNat (opHdr_lt (by simp [opLo]; omega) (by simp [opHi]; omega))])
  refine ⟨?_, ?_⟩
  · rule_simp [rw_hdr3 (show m + kn < 256 by omega) (show kn < 256 by omega)
      (show 72 < 256 by omega)]
    simp [opHdr, opC, opLo, opHi]
  intro s' c' r h' hB
  rule_simp
  apply WP.ret
  rule_simp
  exact HRet.of_built2 h' (VExt.refl st) hstk1 hB (fun st' i hP => by
    simp [rwExtTail, hkn, ht, rwExtOp, RwEnc.tRepeat, RwEnc.tZext, hkn255, hP])

/-! ## `rw_ite` -/

def RwIteSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b d : Nat),
    FnSpec (State := State) Vbcf.prog "rw_ite"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b), uv (st.id d)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv a ∧
        st.lv b ∧ st.lv d)
      (fun _ _ => HPost W sb X c0 prems params c st (fun st' i => rwIteTail st a b d = some (st', i)))

theorem rw_ite_spec : RwIteSpec (State := State) := by
  intro W sb X c0 c prems params st a b d
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwIte) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb, hd⟩
  simp [rwIte, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := rwIte) rfl
  simp only [rwIte, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  obtain ⟨t, ht, hty, hfit⟩ := hR.core.tyOf hnb
  apply WP.rule_ty_of ty_of_spec
  rule_simp [hR.core.rdHdr hnb, hty]
  cases t with
  | bool =>
    apply WP.ite_seq
    rule_simp
    apply WP.rule_mk3 mk3_specT h hR .boolIte 41#32 a b d ha hb hd
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h' hB
    rule_simp
    apply WP.ret
    rule_simp [LoopQ]
    exact HRet.of_built h' hB (fun st' i hP => by simp [rwIteTail, ht, hP])
  | list e k =>
    have := tyW_list_ge e k
    simp only [TyFits] at hfit
    have hlt : tyW (.list e k) < 4294967296 := by rw [tyW_list]; split <;> omega
    apply WP.ite_seq
    rule_simp [Nat.mod_eq_of_lt hlt]
    refine ⟨fun h0 => by omega, fun _ => ?_⟩
    apply WP.ite_seq
    rule_simp [Nat.mod_eq_of_lt hlt]
    refine ⟨fun h0 => by omega, fun _ => ?_⟩
    exact WP.h_fail h
  | bv w =>
    simp only [TyFits] at hfit
    apply WP.ite_seq
    rule_simp
    refine ⟨fun h0 => by omega, fun _ => ?_⟩
    apply WP.ite_seq
    rule_simp
    refine ⟨fun _ => ?_, fun h0 => by omega⟩
    by_cases hw : w < 256
    · apply WP.rule_mk3 mk3_specT h hR (.bvIte w) (BitVec.ofNat 32 (opHdr (.bvIte w))) a b d ha hb hd
        (by simp [IsLeaf, isLeaf]) (by simp [opLo]; omega) (by simp [opHi])
        (by rw [bv_toNat_ofNat (opHdr_lt (by simp [opLo]; omega) (by simp [opHi]))])
      refine ⟨?_, ?_⟩
      · rule_simp [rw_or_shl (show 40 < 256 by omega) hw]
        simp [opHdr, opC, opLo, opHi]
      intro s' c' r h' hB
      rule_simp
      apply WP.ret
      rule_simp [LoopQ]
      exact HRet.of_built h' hB (fun st' i hP => by simp [rwIteTail, ht, hP])
    · have hw' : w = 256 := by omega
      subst hw'
      have hhd : NonLeafHdr (40 + 256 * 65536) := by unfold NonLeafHdr; omega
      apply WP.rule_build (P := fun st' i => ∃ n, hdrW n = 40 + 256 * 65536 + [a, b, d].length * 256 ∧
          Fits X.posOf n ∧ n.args = [a, b, d].toArray ∧ pushNode st n = some (st', i))
        (mk3_specT W sb c X.posOf st.cs (BitVec.ofNat 32 (40 + 256 * 65536)) _ _ _
          (st.σ a) (st.σ b) (st.σ d)) hR
        (fun _ _ hp => MkPost.build (is := [st.σ a, st.σ b, st.σ d])
          (by rw [bv_toNat_ofNat hhd.1] at hp; exact hp))
        (raw_htr hR (is := [a, b, d]) (by simp [ha, hb, hd])) (by rule_simp)
        ⟨rfl, h, hR.core.cinv, by rw [bv_toNat_ofNat hhd.1]; exact hhd, st.σ_lt ha, hR.core.id_toNat ha,
          st.σ_lt hb, hR.core.id_toNat hb, st.σ_lt hd, hR.core.id_toNat hd⟩
      intro s' c' r h' hB
      rule_simp
      apply WP.ret
      rule_simp [LoopQ]
      refine HRet.of_built h' hB (fun st' i ⟨n, hh, hf, _, _⟩ => ?_)
      exfalso
      have h1 := hdrW_code hf
      have h2 := hdrW_hi hf
      rw [hh] at h1 h2
      simp at h1 h2
      obtain ⟨w', hw'⟩ := opC_bvIte_iff.mp h1.symm
      rw [hw'] at h2
      simp [opHi] at h2

/-! ## `rw_extract` -/

def RwExtractSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b d : Nat),
    FnSpec (State := State) Vbcf.prog "rw_extract"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b), uv (st.id d)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv a ∧
        st.lv b ∧ st.lv d)
      (fun _ _ => HPost W sb X c0 prems params c st
        (fun st' i => rwExtractTail st a b d = some (st', i)))

theorem rw_extract_spec : RwExtractSpec (State := State) := by
  intro W sb X c0 c prems params st a b d
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwExtract) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb, hd⟩
  simp [rwExtract, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := rwExtract) rfl
  simp only [rwExtract, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rw_const_call h hR a ha
  refine ⟨by rule_simp, ?_⟩
  intro r1 wk1 er1 vl1 s1 h1 hr1
  have hR1 := hR.wev (wk := wk1) (er := er1) (vl := vl1)
  clear h
  have h := h1
  rule_simp
  h_guard
  intro hne1
  obtain ⟨xv, hxv, hvl1⟩ := hr1 hne1
  rule_assign
  clear hR
  have hR := hR1
  apply WP.rw_const_call h hR b hb
  refine ⟨by rule_simp, ?_⟩
  intro r2 wk2 er2 vl2 s2 h2 hr2
  have hR2 := hR.wev (wk := wk2) (er := er2) (vl := vl2)
  clear h
  have h := h2
  rule_simp
  h_guard
  intro hne2
  obtain ⟨yv, hyv, hvl2⟩ := hr2 hne2
  rule_assign
  clear hR
  have hR := hR2
  h_guard
  intro hx hy
  have hx' : xv ≤ 255 := by rw [BitVec.le_def] at hx; simp at hx; omega
  have hy' : yv ≤ 255 := by rw [BitVec.le_def] at hy; simp at hy; omega
  have hxw : vl1.setWidth 32 = BitVec.ofNat 32 xv := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, bv_toNat_ofNat (by omega)]; omega
  have hyw : vl2.setWidth 32 = BitVec.ofNat 32 yv := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, bv_toNat_ofNat (by omega)]; omega
  apply WP.rule_mk1 mk1_specT h hR (.bvExtract xv yv) (BitVec.ofNat 32 (opHdr (.bvExtract xv yv))) d hd
    (by simp [IsLeaf, isLeaf]) (by simp [opLo]; omega) (by simp [opHi]; omega)
    (by rw [bv_toNat_ofNat (opHdr_lt (by simp [opLo]; omega) (by simp [opHi]; omega))])
  refine ⟨?_, ?_⟩
  · rule_simp [hxw, hyw, rw_hdr3 (show yv < 256 by omega) (show xv < 256 by omega)
      (show 56 < 256 by omega)]
    simp [opHdr, opC, opLo, opHi]
  intro s' c' r h' hB
  rule_simp
  apply WP.ret
  rule_simp
  exact HRet.of_built2 h' (VExt.refl st) ⟨by rfl, by rfl⟩ hB (fun st' i hP => by
    simp [rwExtractTail, hxv, hyv, hx', hy', hP])

end Vbcf.Proof
