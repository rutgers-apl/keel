import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Clause
import Bcf.Aci

/-!
# Vbcf proofs: the Aci family, part 1 — header words and the pure helpers

`aci_is_val`, `aci_is_ones` (with our own copy of the `mask64` specification), `aci_zero`,
`aci_nil`, `aci_assoc`, `aci_same`.  Each is exact: it returns 1 exactly when the Lean
predicate (`n.op = .bvVal w v`, `isZeroElem`, `isNilElem`, `isAssocOp`, `sameAssoc`) holds.
An operator is passed to C as `opHdr op` (`hdr & ACI_OPMASK`).
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem aci_shr16 {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    BitVec.ofNat 32 (hdrW n) >>> 16 = BitVec.ofNat 32 (opLo n.op + opHi n.op * 256) := by
  have := hdrW_lt hf; have := hf.lo; have := hf.hi
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_16, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega), hdrW_params hf]

theorem aci_par_lo {lo hi : Nat} (hlo : lo < 256) (hhi : hi < 256) :
    BitVec.ofNat 32 (lo + hi * 256) &&& 255#32 = BitVec.ofNat 32 lo := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]; omega

theorem aci_split64 {v : Nat} (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 (v % 4294967296) ||| BitVec.setWidth 64 (BitVec.ofNat 32 (v / 4294967296)) <<< 32).toNat
      = v := by
  have h1 : v / 4294967296 < 2 ^ 32 := by omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v % 4294967296 < 2 ^ 64),
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : v / 4294967296 < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : v / 4294967296 * 2 ^ 32 < 2 ^ 64), Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : v % 4294967296 < 2 ^ 32),
    Nat.shiftLeft_eq]
  omega

def AciIsValSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (i : Nat) (n : Node) (w : Nat) (v : BitVec 64),
    FnSpec (State := State) Vbcf.prog "aci_is_val"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i), uv w, .u64 v] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.pool[i]? = some n ∧ st.lv i ∧ w < 256)
      (fun _ s => PureRet s (if n.op = .bvVal w v.toNat then 1 else 0))

theorem aci_is_val_spec : AciIsValSpec (State := State) := by
  intro W sb X c0 c prems params st i n w v
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciIsVal) rfl
  rintro vs s ⟨rfl, h, hR, hn, hi, hw⟩
  simp [aciIsVal, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hf := hR.core.rep.fits i n hn
  have := hf.lo; have := hf.hi
  rule_assign [hR.core.rdHdr hn]
  apply WP.guard_lit
  rule_simp [aci_shr16 hf, aci_par_lo hf.lo hf.hi]
  refine ⟨fun hne => ?_, fun w' v' hop hlo => ?_⟩
  · have : ¬ n.op = .bvVal w v.toNat := fun e => hne w v.toNat e (by rw [e]; rfl)
    simp [retPost, PureRet, this]
  obtain ⟨argTys, t, -, hrt, -, -⟩ := hR.core.ok.retype hn
  rw [hop] at hrt hlo
  obtain ⟨hw0, hw64, hv⟩ := resultTy_bvVal hrt
  simp only [opLo] at hlo
  subst hlo
  have hc1 := hR.core.rep.tail hn (k := 0) (w := v' % 2 ^ 32) (by simp [tailW, hop]; split <;> simp)
  rule_assign [rd_u32 hc1]
  have hres : ∀ x : BitVec 64, x.toNat = v' → ∀ env, env.get "x" = some (.u64 x) →
      env.get "v" = some (.u64 v) →
      WP Vbcf.prog (.ret (some (.bin .eq (.var "x") (.var "v"))))
        (retPost (some Ty.u32) (PureRet s (if n.op = Op.bvVal w' v.toNat then 1 else 0))) env s := by
    intro x hx env hex hev
    apply WP.ret
    simp only [evalE, hex, hev, evalBin, evalArith]
    rw [hop]
    by_cases e : x = v
    · subst e; simp [Val.ofBool, retPost, PureRet, hx]
    · have : v' ≠ v.toNat := fun e' => e (BitVec.eq_of_toNat_eq (by rw [hx, e']))
      simp [Val.ofBool, retPost, PureRet, e, this]
  apply WP.ite_seq
  by_cases hw32 : w' ≤ 32
  · have htl : tailLen n = 1 := by simp [tailLen, hop, hw32]
    rule_simp [hdr_len_bv hf, htl]
    have hv32 : v' < 2 ^ 32 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw32)
    exact hres (BitVec.ofNat 64 v') (by simp; omega) _
      (by simp [Env.get, Nat.mod_eq_of_lt hv32]) (by simp [Env.get])
  · have htl : tailLen n = 2 := by simp [tailLen, hop, hw32]
    have hc2 : U c.pool (st.id i + 2) (v' / 2 ^ 32) := by
      have := hR.core.rep.tail hn (k := 1) (w := v' / 2 ^ 32) (by simp [tailW, hop, hw32])
      rwa [Nat.add_assoc] at this
    rule_simp [hdr_len_bv hf, htl]
    apply WP.assign_loop
    rule_simp [rd_u32 hc2]
    have hv64 : v' < 2 ^ 64 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw64)
    exact hres _ (aci_split64 hv64) _ (by simp [Env.get]) (by simp [Env.get])

/-! ## Header words -/

theorem aci_typed_val {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st) {i : Nat}
    {n : Node} (hn : st.pool[i]? = some n) {w v : Nat} (hop : n.op = .bvVal w v) :
    w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w := by
  obtain ⟨argTys, t, -, hrt, -, -⟩ := hc.ok.retype hn
  rw [hop] at hrt
  exact resultTy_bvVal hrt

theorem aci_rop_code {op : Op} (hlo : opLo op < 256) (hhi : opHi op < 256) :
    BitVec.ofNat 32 (opHdr op) &&& 255#32 = BitVec.ofNat 32 (opC op) := by
  have := opC_lt op
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_toNat_ofNat (opHdr_lt hlo hhi), bv_toNat_ofNat (by omega)]
  unfold opHdr; omega

theorem aci_rop_lo {op : Op} (hlo : opLo op < 256) (hhi : opHi op < 256) :
    BitVec.ofNat 32 (opHdr op) >>> 16 &&& 255#32 = BitVec.ofNat 32 (opLo op) := by
  have := opC_lt op
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_shr_16, bv_toNat_ofNat (opHdr_lt hlo hhi), bv_toNat_ofNat (by omega)]
  unfold opHdr; omega

theorem aci_hdr_true {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    (BitVec.ofNat 32 (hdrW n) = 65545#32) ↔ n.op = .boolVal true := by
  rw [show (65545#32 : BitVec 32) = BitVec.ofNat 32 65545 from rfl,
    bv_ofNat_inj (hdrW_lt hf) (by omega)]
  constructor
  · intro e
    have h1 := hdrW_code hf
    rw [e] at h1
    obtain ⟨b, hb⟩ := opC_boolVal_iff.mp (by simpa using h1.symm)
    have h2 := hdrW_lo hf
    rw [e, hb] at h2
    cases b <;> simp [opLo] at h2
    exact hb
  · intro e
    simp [hdrW, e, opC, opLo, opHi, tailLen]

theorem aci_hdr_false {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    (BitVec.ofNat 32 (hdrW n) = 9#32) ↔ n.op = .boolVal false := by
  rw [show (9#32 : BitVec 32) = BitVec.ofNat 32 9 from rfl,
    bv_ofNat_inj (hdrW_lt hf) (by omega)]
  constructor
  · intro e
    have h1 := hdrW_code hf
    rw [e] at h1
    obtain ⟨b, hb⟩ := opC_boolVal_iff.mp (by simpa using h1.symm)
    have h2 := hdrW_lo hf
    rw [e, hb] at h2
    cases b <;> simp [opLo] at h2
    exact hb
  · intro e
    simp [hdrW, e, opC, opLo, opHi, tailLen]

/-! ## `mask64` (own copy of the specification, so as not to depend on the Eval family) -/

theorem aci_mask64_spec (w : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "mask64" (fun vs _ => vs = [.u32 w])
      (fun _ s rv s' => s' = s ∧
        rv = some (.u64 (if 64#32 ≤ w then 0xffffffffffffffff#64 else (1#64 <<< w.toNat) - 1#64))) := by
  apply FnSpec.intro' (fn := mask64) rfl
  rintro vs st rfl
  simp [mask64, bindParams]
  simp only [Stmt.block, initLocals, List.map]
  apply WP.ifRet
  embc_simp
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · simp [retPost, hw]
  · apply WP.ret
    have hlt : w.toNat < 64 := by rw [BitVec.lt_def] at hw; simpa using hw
    have hm : w.toNat % 18446744073709551616 = w.toNat := Nat.mod_eq_of_lt (by omega)
    have hw' : ¬ 64#32 ≤ w := by rw [BitVec.le_def]; simp; omega
    embc_simp [retPost, hlt, hm, hw']

theorem aci_mask64_val {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ 64) :
    (if 64#32 ≤ BitVec.ofNat 32 w then 0xffffffffffffffff#64
      else (1#64 <<< (BitVec.ofNat 32 w).toNat) - 1#64).toNat = 2 ^ w - 1 := by
  rw [bv_toNat_ofNat (by omega)]
  by_cases h : w = 64
  · subst h; decide
  · have : ¬ 64#32 ≤ BitVec.ofNat 32 w := by
      rw [BitVec.le_def, bv_toNat_ofNat (by omega)]; simp; omega
    rw [ite_eq_right this, BitVec.toNat_sub, BitVec.toNat_shiftLeft]
    have hp : 2 ^ w < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    have hp1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    simp only [BitVec.toNat_ofNat, Nat.one_mod, Nat.shiftLeft_eq, Nat.one_mul]
    rw [Nat.mod_eq_of_lt (by omega : 2 ^ w < 2 ^ 64)]
    omega


def AciIsOnesSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (i : Nat) (n : Node) (w : Nat),
    FnSpec (State := State) Vbcf.prog "aci_is_ones"
      (fun vs s => vs = [.ptr sb 0, uv (st.id i), uv w] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.pool[i]? = some n ∧ st.lv i ∧ w < 256)
      (fun _ s => PureRet s (if n.op = .bvVal w (2 ^ w - 1) then 1 else 0))

theorem aci_is_ones_spec : AciIsOnesSpec (State := State) := by
  intro W sb X c0 c prems params st i n w
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciIsOnes) rfl
  rintro vs s ⟨rfl, h, hR, hn, hlv_i, hw⟩
  simp [aciIsOnes, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun hw' => ?_, fun hw0 hw64 => ?_⟩
  · have : ¬ n.op = .bvVal w (2 ^ w - 1) := fun e => by
      have := aci_typed_val hR.core hn e
      omega
    simp [retPost, PureRet, this]
  apply WP.call_seq (aci_mask64_spec (BitVec.ofNat 32 w)) (by rule_simp) rfl
  rintro rv s' ⟨rfl, rfl⟩
  have hmv := aci_mask64_val (by omega : 1 ≤ w) hw64
  generalize (if 64#32 ≤ BitVec.ofNat 32 w then 0xffffffffffffffff#64
      else (1#64 <<< (BitVec.ofNat 32 w).toNat) - 1#64) = m at hmv ⊢
  rule_simp
  apply WP.call_seq (aci_is_val_spec W sb X c0 c prems params st i n w m) (by rule_simp)
    ⟨rfl, h, hR, hn, by vlv, hw⟩
  rintro rv s' ⟨rfl, rfl⟩
  rule_simp
  apply WP.ret
  rule_simp [retPost, PureRet, hmv]


def AciZeroSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (op : Op) (i : Nat) (n : Node),
    FnSpec (State := State) Vbcf.prog "aci_zero"
      (fun vs s => vs = [.ptr sb 0, uv (opHdr op), uv (st.id i)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.pool[i]? = some n ∧ st.lv i ∧ opLo op < 256 ∧ opHi op < 256)
      (fun _ s => PureRet s (if isZeroElem op n then 1 else 0))

theorem aci_zero_spec : AciZeroSpec (State := State) := by
  intro W sb X c0 c prems params st op i n
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciZero) rfl
  rintro vs s ⟨rfl, h, hR, hn, hi, hlo, hhi⟩
  simp [aciZero, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hf := hR.core.rep.fits i n hn
  rule_assign [aci_rop_code hlo hhi]
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hn, aci_hdr_true hf]
  refine ⟨fun e => ?_, fun e1 => ?_⟩
  · subst e
    by_cases hz : n.op = .boolVal true <;> simp [retPost, PureRet, isZeroElem, hz]
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hn, aci_hdr_false hf]
  refine ⟨fun e => ?_, fun e2 => ?_⟩
  · subst e
    by_cases hz : n.op = .boolVal false <;> simp [retPost, PureRet, isZeroElem, hz]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w e => ?_, fun e3 => ?_⟩
  · subst e
    have hr := aci_rop_lo hlo hhi
    simp only [opLo] at hlo hr
    apply WP.call_seq (aci_is_val_spec W sb X c0 c prems params st i n w 0#64)
      (by rule_simp [hr]) ⟨rfl, h, hR, hn, by vlv, hlo⟩
    rintro rv s' ⟨rfl, rfl⟩
    rule_simp
    apply WP.ret
    rule_simp [LoopQ, retPost, PureRet, isZeroElem]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w e => ?_, fun e4 => ?_⟩
  · subst e
    have hr := aci_rop_lo hlo hhi
    simp only [opLo] at hlo hr
    apply WP.call_seq (aci_is_ones_spec W sb X c0 c prems params st i n w)
      (by rule_simp [hr]) ⟨rfl, h, hR, hn, by vlv, hlo⟩
    rintro rv s' ⟨rfl, rfl⟩
    rule_simp
    apply WP.ret
    rule_simp [LoopQ, retPost, PureRet, isZeroElem]
  apply WP.ret
  have : isZeroElem op n = false := by
    unfold isZeroElem; split <;> simp_all
  rule_simp [retPost, PureRet, this]


def AciNilSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (op : Op) (i : Nat) (n : Node),
    FnSpec (State := State) Vbcf.prog "aci_nil"
      (fun vs s => vs = [.ptr sb 0, uv (opHdr op), uv (st.id i)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ st.pool[i]? = some n ∧ st.lv i ∧ opLo op < 256 ∧ opHi op < 256)
      (fun _ s => PureRet s (if isNilElem op n then 1 else 0))

theorem aci_nil_spec : AciNilSpec (State := State) := by
  intro W sb X c0 c prems params st op i n
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciNil) rfl
  rintro vs s ⟨rfl, h, hR, hn, hi, hlo, hhi⟩
  simp [aciNil, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hf := hR.core.rep.fits i n hn
  rule_assign [aci_rop_code hlo hhi]
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hn, aci_hdr_false hf]
  refine ⟨fun e => ?_, fun e1 => ?_⟩
  · subst e
    by_cases hz : n.op = .boolVal false <;> simp [retPost, PureRet, isNilElem, hz]
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hn, aci_hdr_true hf]
  refine ⟨fun e => ?_, fun e2 => ?_⟩
  · subst e
    by_cases hz : n.op = .boolVal true <;> simp [retPost, PureRet, isNilElem, hz]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun w e => ?_, fun e3 => ?_⟩
  · subst e
    have hr := aci_rop_lo hlo hhi
    simp only [opLo] at hlo hr
    apply WP.call_seq (aci_is_ones_spec W sb X c0 c prems params st i n w)
      (by rule_simp [hr]) ⟨rfl, h, hR, hn, by vlv, hlo⟩
    rintro rv s' ⟨rfl, rfl⟩
    rule_simp
    apply WP.ret
    rule_simp [LoopQ, retPost, PureRet, isNilElem]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hc => ?_, fun e4 e5 => ?_⟩
  · have hw : ∃ w, opLo op = w ∧ isNilElem op n = (n.op == .bvVal w 0) := by
      by_cases ho : ∃ w, op = .bvOr w
      · obtain ⟨w, rfl⟩ := ho
        exact ⟨w, rfl, rfl⟩
      · obtain ⟨w, rfl⟩ := hc (fun x e => ho ⟨x, e⟩)
        exact ⟨w, rfl, rfl⟩
    obtain ⟨w, hwl, hnil⟩ := hw
    have hr := aci_rop_lo hlo hhi
    rw [hwl] at hlo hr
    apply WP.call_seq (aci_is_val_spec W sb X c0 c prems params st i n w 0#64)
      (by rule_simp [hr]) ⟨rfl, h, hR, hn, by vlv, hlo⟩
    rintro rv s' ⟨rfl, rfl⟩
    rule_simp
    apply WP.ret
    rule_simp [LoopQ, retPost, PureRet, hnil]
  apply WP.ret
  have : isNilElem op n = false := by
    unfold isNilElem; split <;> simp_all
  rule_simp [retPost, PureRet, this]


/-! ## Operators as masked header words -/

/-- `hdr & ACI_OPMASK` on the header of a fitting node. -/
theorem aci_hdr_mask {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    BitVec.ofNat 32 (hdrW n) &&& 4294902015#32 = BitVec.ofNat 32 (opHdr n.op) := by
  have h1 := opC_lt n.op; have := hf.lo; have := hf.hi; have := hf.tailLen
  have hl := hdrW_lt hf
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, bv_toNat_ofNat hl, bv_toNat_ofNat (opHdr_lt hf.lo hf.hi)]
  show hdrW n &&& 4294902015 = opHdr n.op
  have e1 : (4294902015 : Nat) = 255 + 4294901760 := rfl
  have e2 : hdrW n &&& 4294902015 = hdrW n % 256 + hdrW n / 65536 * 65536 := by
    apply Nat.eq_of_testBit_eq
    intro j
    have hlo : hdrW n % 256 + hdrW n / 65536 * 65536 = hdrW n % 256 ||| hdrW n / 65536 * 65536 :=
      (or_lo_hi (hdrW n)).symm
    rw [hlo, Nat.testBit_or, Nat.testBit_and]
    rw [← and_hi16 hl]
    rw [Nat.testBit_and]
    have : hdrW n % 256 = hdrW n &&& 255 := by
      rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rw [this, Nat.testBit_and]
    have hm : (4294902015 : Nat).testBit j = ((255 : Nat).testBit j || (4294901760 : Nat).testBit j) := by
      rw [show (4294902015 : Nat) = 255 ||| 4294901760 from rfl, Nat.testBit_or]
    rw [hm]
    cases (hdrW n).testBit j <;> simp
  rw [e2]
  unfold opHdr hdrW
  omega

theorem aci_opHdr_inj {a b : Op} (hl : ¬ IsLeaf b) (ha1 : opLo a < 256) (ha2 : opHi a < 256)
    (hb1 : opLo b < 256) (hb2 : opHi b < 256) :
    (BitVec.ofNat 32 (opHdr a) = BitVec.ofNat 32 (opHdr b)) ↔ a = b := by
  rw [bv_ofNat_inj (opHdr_lt ha1 ha2) (opHdr_lt hb1 hb2)]
  refine ⟨fun e => ?_, fun e => e ▸ rfl⟩
  have h1 := opC_lt a; have h2 := opC_lt b
  have hc : opC a = opC b := by unfold opHdr at e; omega
  have hlo : opLo a = opLo b := by unfold opHdr at e; omega
  have hhi : opHi a = opHi b := by unfold opHdr at e; omega
  rw [isLeaf_iff_opC] at hl
  exact op_eq_of_enc hc hlo hhi (by
    rw [opData_eq_zero (by omega) (by omega) (by omega), opData_eq_zero (by omega) (by omega) (by omega)])

/-! ## `aci_assoc`, `aci_same` -/

def AciAssocSpec : Prop :=
  ∀ (n : Node), FnSpec (State := State) Vbcf.prog "aci_assoc" (fun vs _ => vs = [uv (hdrW n)])
    (fun _ s => PureRet s (if isAssocOp n.op then 1 else 0))

theorem aci_assoc_spec : AciAssocSpec (State := State) := by
  intro n
  apply FnSpec.intro' (fn := aciAssoc) rfl
  rintro vs s rfl
  simp [aciAssoc, bindParams]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.assign_seq
  have e : BitVec.ofNat 32 (hdrW n) &&& 255#32 = BitVec.ofNat 32 (opC n.op) := by
    rw [uv_and_ff, hdrW_mod256]
  apply WP.ret
  simp [evalE, Env.get, evalBin, evalArith, Env.set, Val.ofBool, e, retPost, PureRet]
  cases n.op <;> simp [opC, isAssocOp] <;> decide

def AciSameSpec : Prop :=
  ∀ (posOf : Nat → Nat) (op : Op) (n : Node), FnSpec (State := State) Vbcf.prog "aci_same"
    (fun vs _ => vs = [uv (opHdr op), uv (hdrW n)] ∧ ¬ IsLeaf op ∧ opLo op < 256 ∧ opHi op < 256 ∧
      Fits posOf n)
    (fun _ s => PureRet s (if sameAssoc op n.op then 1 else 0))

theorem aci_same_spec : AciSameSpec (State := State) := by
  intro posOf op n
  apply FnSpec.intro' (fn := aciSame) rfl
  rintro vs s ⟨rfl, hl, hlo, hhi, hf⟩
  simp [aciSame, bindParams]
  simp only [Stmt.block, initLocals, List.map]
  have e1 : BitVec.ofNat 32 (hdrW n) &&& 255#32 = BitVec.ofNat 32 (opC n.op) := by
    rw [uv_and_ff, hdrW_mod256]
  have e2 := aci_rop_code hlo hhi
  have e3 := aci_hdr_mask hf
  have h1 := opC_lt n.op
  have h2 := opC_lt op
  apply WP.ifRet
  simp [evalE, Env.get, evalBin, evalArith, Val.ofBool, e1, e2]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hc' : opC op = 0x98 := by
      rw [show (152#32 : BitVec 32) = BitVec.ofNat 32 152 from rfl, uv_inj (by omega) (by omega)] at hc
      exact hc
    obtain ⟨w, rfl⟩ := opC_bvConcat_iff.mp hc'
    have : (BitVec.ofNat 32 (opC n.op) = 152#32) ↔ isConcatOp n.op = true := by
      rw [show (152#32 : BitVec 32) = BitVec.ofNat 32 152 from rfl, uv_inj (by omega) (by omega),
        isConcatOp_iff, opC_bvConcat_iff]
    by_cases hcc : isConcatOp n.op = true
    · simp [retPost, PureRet, sameAssoc_concat, hcc, this.mpr hcc]
    · have hcc' : ¬ BitVec.ofNat 32 (opC n.op) = 152#32 := fun e => hcc (this.mp e)
      simp [retPost, PureRet, sameAssoc_concat, hcc, hcc']
  · have hnc : isConcatOp op = false := by
      cases hco : isConcatOp op
      · rfl
      · obtain ⟨w, rfl⟩ := (isConcatOp_iff _).mp hco
        exact absurd rfl hc
    apply WP.ret
    have hf' := hf
    simp [evalE, Env.get, evalBin, evalArith, Val.ofBool, e3, retPost, PureRet,
      sameAssoc_of_not_concat hnc, aci_opHdr_inj hl hf.lo hf.hi hlo hhi]
    split <;> rfl

end Vbcf.Proof
