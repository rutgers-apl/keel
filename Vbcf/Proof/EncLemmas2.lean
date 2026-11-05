import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.EncLemmas1

/-!
# Vbcf proofs: header arithmetic, the `BitVec` bridge, and operator codes

Part 2 of `Vbcf/Proof/EncLemmas.lean`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ## C. Header arithmetic -/

theorem opC_lt (op : Op) : opC op < 256 := by
  cases op <;> simp [opC]

theorem Fits.lo {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) : opLo n.op < 256 := h.1
theorem Fits.hi {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) : opHi n.op < 256 := h.2.1
theorem Fits.tailLen {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) : tailLen n < 256 := h.2.2.1
theorem Fits.tail {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    ∀ w ∈ tailW posOf (fun _ => 0) n, w < 2 ^ 32 := h.2.2.2

theorem hdrW_lt {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) : hdrW n < 2 ^ 32 := by
  have h1 := opC_lt n.op; have h2 := h.lo; have h3 := h.hi; have h4 := h.tailLen
  unfold hdrW; omega

theorem hdrW_code {posOf : Nat → Nat} {n : Node} (_h : Fits posOf n) :
    hdrW n % 256 = opC n.op := by
  have h1 := opC_lt n.op
  unfold hdrW; omega

theorem hdrW_len {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    hdrW n / 256 % 256 = tailLen n := by
  have h1 := opC_lt n.op; have h4 := h.tailLen
  unfold hdrW; omega

theorem hdrW_params {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    hdrW n / 65536 = opLo n.op + opHi n.op * 256 := by
  have h1 := opC_lt n.op; have h4 := h.tailLen
  unfold hdrW; omega

theorem hdrW_lo {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    hdrW n / 65536 % 256 = opLo n.op := by
  have h2 := h.lo
  rw [hdrW_params h]; omega

theorem hdrW_hi {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    hdrW n / 16777216 = opHi n.op := by
  have h2 := h.lo
  have := hdrW_params h
  omega

/-- The same fields seen the way `ck_tyck` computes them from `par = hdr >> 16`. -/
theorem hdrW_par_lo {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    (hdrW n / 65536) % 256 = opLo n.op := hdrW_lo h

theorem hdrW_par_hi {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    (hdrW n / 65536) / 256 = opHi n.op := by
  have h2 := h.lo
  rw [hdrW_params h]; omega

theorem hdrW_params_lt {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    hdrW n / 65536 < 65536 := by
  have h2 := h.lo; have h3 := h.hi
  rw [hdrW_params h]; omega

/-- The node size as `ck_intern` reads it from the header. -/
theorem hdrW_nodeSize {posOf : Nat → Nat} {n : Node} (h : Fits posOf n) :
    1 + hdrW n / 256 % 256 = nodeSize n := by
  rw [hdrW_len h, nodeSize]

/-- Two fitting nodes with the same header agree on all four header fields. -/
theorem hdrW_inj {posOf : Nat → Nat} {n n' : Node} (h : Fits posOf n) (h' : Fits posOf n')
    (e : hdrW n = hdrW n') :
    opC n.op = opC n'.op ∧ tailLen n = tailLen n' ∧ opLo n.op = opLo n'.op ∧
      opHi n.op = opHi n'.op := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdrW_code h, ← hdrW_code h', e]
  · rw [← hdrW_len h, ← hdrW_len h', e]
  · rw [← hdrW_lo h, ← hdrW_lo h', e]
  · rw [← hdrW_hi h, ← hdrW_hi h', e]

/-! ## D. `BitVec` bridge

The shift amounts are `Nat`s: the C semantics produces `x >>> (8#32).toNat`,
which `simp` turns into `x >>> 8`. -/

theorem bv_toNat_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem bv_ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  exact bv_toNat_ofNat x.isLt

theorem bv_eq_ofNat_iff {x : BitVec 32} {n : Nat} (h : n < 2 ^ 32) :
    x = BitVec.ofNat 32 n ↔ x.toNat = n := by
  rw [← BitVec.toNat_inj, bv_toNat_ofNat h]

theorem bv_ofNat_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a = BitVec.ofNat 32 b ↔ a = b := by
  rw [← BitVec.toNat_inj, bv_toNat_ofNat ha, bv_toNat_ofNat hb]

/-! Natural-number forms.  Plain `simp` pushes `toNat` inside (`BitVec.toNat_and`,
`BitVec.toNat_ushiftRight`) before the `bv_*` lemmas below can fire, and merges
`x >>> 16 >>> 8` into `x >>> 24`; these are what is left afterwards. -/

theorem nat_and_ff (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
theorem nat_and_7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem nat_and_1 (n : Nat) : n &&& 1 = n % 2 := Nat.and_two_pow_sub_one_eq_mod n 1
theorem nat_shr_8 (n : Nat) : n >>> 8 = n / 256 := Nat.shiftRight_eq_div_pow n 8
theorem nat_shr_16 (n : Nat) : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
theorem nat_shr_24 (n : Nat) : n >>> 24 = n / 16777216 := Nat.shiftRight_eq_div_pow n 24

theorem nat_and_fffe {n : Nat} (h : n < 65536) : n &&& 65534 = n - n % 2 := by
  have h1 : (n &&& 65534) / 2 = n / 2 := by
    rw [Nat.and_div_two]
    show n / 2 &&& (2 ^ 15 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h2 : (n &&& 65534) % 2 = 0 := by
    have := Nat.and_mod_two_pow (a := n) (b := 65534) (n := 1)
    simp at this
    omega
  omega

/-! `BitVec` forms, for `rw` and `simp only`. -/

theorem bv_and_ff (x : BitVec 32) : (x &&& 0xff#32).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and]; exact nat_and_ff x.toNat

theorem bv_and_7 (x : BitVec 32) : (x &&& 7#32).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and]; exact nat_and_7 x.toNat

theorem bv_and_1 (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]; exact nat_and_1 x.toNat

theorem bv_shr (x : BitVec 32) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv_shr_8 (x : BitVec 32) : (x >>> 8).toNat = x.toNat / 256 := bv_shr x 8
theorem bv_shr_16 (x : BitVec 32) : (x >>> 16).toNat = x.toNat / 65536 := bv_shr x 16
theorem bv_shr_24 (x : BitVec 32) : (x >>> 24).toNat = x.toNat / 16777216 := bv_shr x 24

/-- `par & 0xfffe` for a 16-bit `par`: clears bit 0. -/
theorem bv_and_fffe {x : BitVec 32} (h : x.toNat < 65536) :
    (x &&& 0xfffe#32).toNat = x.toNat - x.toNat % 2 := by
  rw [BitVec.toNat_and]; exact nat_and_fffe h

/-- The `BOOL_VAL` test `(par & 0xfffe) == 0`. -/
theorem bv_and_fffe_eq_zero_iff {x : BitVec 32} (h : x.toNat < 65536) :
    x &&& 0xfffe#32 = 0#32 ↔ x.toNat < 2 := by
  rw [← BitVec.toNat_inj, bv_and_fffe h]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  omega

/-- `hdr >> 16` is a 16-bit quantity. -/
theorem bv_shr_16_lt (x : BitVec 32) : (x >>> 16).toNat < 65536 := by
  have := x.isLt
  rw [bv_shr_16]; omega

theorem bv_shr_24_lt (x : BitVec 32) : (x >>> 24).toNat < 256 := by
  have := x.isLt
  rw [bv_shr_24]; omega

/-! ## E. Which operator a code is -/

theorem opC_bvVar_iff {op : Op} : opC op = 0x18 ↔ ∃ w id, op = .bvVar w id := by
  cases op <;> simp [opC]

theorem opC_bvVal_iff {op : Op} : opC op = 0x08 ↔ ∃ w v, op = .bvVal w v := by
  cases op <;> simp [opC]

theorem opC_bvIte_iff {op : Op} : opC op = 0x28 ↔ ∃ w, op = .bvIte w := by
  cases op <;> simp [opC]

theorem opC_bvNeg_iff {op : Op} : opC op = 0x80 ↔ ∃ w, op = .bvNeg w := by
  cases op <;> simp [opC]

theorem opC_bvNot_iff {op : Op} : opC op = 0x78 ↔ ∃ w, op = .bvNot w := by
  cases op <;> simp [opC]

theorem opC_bvExtract_iff {op : Op} : opC op = 0x38 ↔ ∃ hi lo, op = .bvExtract hi lo := by
  cases op <;> simp [opC]

theorem opC_bvSignExtend_iff {op : Op} : opC op = 0x48 ↔ ∃ w e, op = .bvSignExtend w e := by
  cases op <;> simp [opC]

theorem opC_bvZeroExtend_iff {op : Op} : opC op = 0x58 ↔ ∃ w e, op = .bvZeroExtend w e := by
  cases op <;> simp [opC]

theorem opC_bvSize_iff {op : Op} : opC op = 0x68 ↔ ∃ w, op = .bvSize w := by
  cases op <;> simp [opC]

theorem opC_bvRepeat_iff {op : Op} : opC op = 0xa8 ↔ ∃ w k, op = .bvRepeat w k := by
  cases op <;> simp [opC]

theorem opC_bvSub_iff {op : Op} : opC op = 0x10 ↔ ∃ w, op = .bvSub w := by
  cases op <;> simp [opC]

theorem opC_bvShl_iff {op : Op} : opC op = 0x60 ↔ ∃ w, op = .bvShl w := by
  cases op <;> simp [opC]

theorem opC_bvLshr_iff {op : Op} : opC op = 0x70 ↔ ∃ w, op = .bvLshr w := by
  cases op <;> simp [opC]

theorem opC_bvAshr_iff {op : Op} : opC op = 0xc0 ↔ ∃ w, op = .bvAshr w := by
  cases op <;> simp [opC]

theorem opC_bvUdiv_iff {op : Op} : opC op = 0x30 ↔ ∃ w, op = .bvUdiv w := by
  cases op <;> simp [opC]

theorem opC_bvUrem_iff {op : Op} : opC op = 0x90 ↔ ∃ w, op = .bvUrem w := by
  cases op <;> simp [opC]

theorem opC_bvSdiv_iff {op : Op} : opC op = 0xb0 ↔ ∃ w, op = .bvSdiv w := by
  cases op <;> simp [opC]

theorem opC_bvSmod_iff {op : Op} : opC op = 0xd0 ↔ ∃ w, op = .bvSmod w := by
  cases op <;> simp [opC]

theorem opC_bvAdd_iff {op : Op} : opC op = 0x00 ↔ ∃ w, op = .bvAdd w := by
  cases op <;> simp [opC]

theorem opC_bvMul_iff {op : Op} : opC op = 0x20 ↔ ∃ w, op = .bvMul w := by
  cases op <;> simp [opC]

theorem opC_bvOr_iff {op : Op} : opC op = 0x40 ↔ ∃ w, op = .bvOr w := by
  cases op <;> simp [opC]

theorem opC_bvAnd_iff {op : Op} : opC op = 0x50 ↔ ∃ w, op = .bvAnd w := by
  cases op <;> simp [opC]

theorem opC_bvXor_iff {op : Op} : opC op = 0xa0 ↔ ∃ w, op = .bvXor w := by
  cases op <;> simp [opC]

theorem opC_bvConcat_iff {op : Op} : opC op = 0x98 ↔ ∃ w, op = .bvConcat w := by
  cases op <;> simp [opC]

theorem opC_bvFromBool_iff {op : Op} : opC op = 0x88 ↔ op = .bvFromBool := by
  cases op <;> simp [opC]

theorem opC_boolVal_iff {op : Op} : opC op = 0x09 ↔ ∃ b, op = .boolVal b := by
  cases op <;> simp [opC]

theorem opC_boolVar_iff {op : Op} : opC op = 0x19 ↔ ∃ id, op = .boolVar id := by
  cases op <;> simp [opC]

theorem opC_boolNot_iff {op : Op} : opC op = 0x81 ↔ op = .boolNot := by
  cases op <;> simp [opC]

theorem opC_boolBitof_iff {op : Op} : opC op = 0x49 ↔ ∃ i, op = .boolBitof i := by
  cases op <;> simp [opC]

theorem opC_eq_iff {op : Op} : opC op = 0x11 ↔ op = .eq := by
  cases op <;> simp [opC]

theorem opC_distinct_iff {op : Op} : opC op = 0x51 ↔ op = .distinct := by
  cases op <;> simp [opC]

theorem opC_ugt_iff {op : Op} : opC op = 0x21 ↔ op = .ugt := by
  cases op <;> simp [opC]

theorem opC_uge_iff {op : Op} : opC op = 0x31 ↔ op = .uge := by
  cases op <;> simp [opC]

theorem opC_sgt_iff {op : Op} : opC op = 0x61 ↔ op = .sgt := by
  cases op <;> simp [opC]

theorem opC_sge_iff {op : Op} : opC op = 0x71 ↔ op = .sge := by
  cases op <;> simp [opC]

theorem opC_ult_iff {op : Op} : opC op = 0xa1 ↔ op = .ult := by
  cases op <;> simp [opC]

theorem opC_ule_iff {op : Op} : opC op = 0xb1 ↔ op = .ule := by
  cases op <;> simp [opC]

theorem opC_slt_iff {op : Op} : opC op = 0xc1 ↔ op = .slt := by
  cases op <;> simp [opC]

theorem opC_sle_iff {op : Op} : opC op = 0xd1 ↔ op = .sle := by
  cases op <;> simp [opC]

theorem opC_implies_iff {op : Op} : opC op = 0x91 ↔ op = .implies := by
  cases op <;> simp [opC]

theorem opC_boolIte_iff {op : Op} : opC op = 0x29 ↔ op = .boolIte := by
  cases op <;> simp [opC]

theorem opC_conj_iff {op : Op} : opC op = 0x01 ↔ op = .conj := by
  cases op <;> simp [opC]

theorem opC_disj_iff {op : Op} : opC op = 0x41 ↔ op = .disj := by
  cases op <;> simp [opC]

theorem opC_boolXor_iff {op : Op} : opC op = 0x39 ↔ op = .boolXor := by
  cases op <;> simp [opC]

theorem opC_listVal_iff {op : Op} : opC op = 0x0a ↔ ∃ e, op = .listVal e := by
  cases op <;> simp [opC]

/-! ### The type class of a code (`code & 7`) -/

/-- The operators whose result is boolean. -/
def isBoolOp : Op → Bool
  | .boolVal _ => true
  | .boolVar _ => true
  | .boolNot => true
  | .boolBitof _ => true
  | .eq => true
  | .distinct => true
  | .ugt => true
  | .uge => true
  | .sgt => true
  | .sge => true
  | .ult => true
  | .ule => true
  | .slt => true
  | .sle => true
  | .implies => true
  | .boolIte => true
  | .conj => true
  | .disj => true
  | .boolXor => true
  | _ => false

/-- The operators whose result is a bit-vector. -/
def isBvOp : Op → Bool
  | .bvVar _ _ => true
  | .bvVal _ _ => true
  | .bvIte _ => true
  | .bvNeg _ => true
  | .bvNot _ => true
  | .bvExtract _ _ => true
  | .bvSignExtend _ _ => true
  | .bvZeroExtend _ _ => true
  | .bvSize _ => true
  | .bvRepeat _ _ => true
  | .bvSub _ => true
  | .bvShl _ => true
  | .bvLshr _ => true
  | .bvAshr _ => true
  | .bvUdiv _ => true
  | .bvUrem _ => true
  | .bvSdiv _ => true
  | .bvSmod _ => true
  | .bvAdd _ => true
  | .bvMul _ => true
  | .bvOr _ => true
  | .bvAnd _ => true
  | .bvXor _ => true
  | .bvConcat _ => true
  | .bvFromBool => true
  | _ => false

theorem opC_mod8 (op : Op) : opC op % 8 = 0 ∨ opC op % 8 = 1 ∨ opC op % 8 = 2 := by
  cases op <;> simp [opC]

theorem opC_mod8_lt (op : Op) : opC op % 8 < 3 := by
  rcases opC_mod8 op with h | h | h <;> omega

theorem opC_mod8_eq_zero_iff {op : Op} : opC op % 8 = 0 ↔ isBvOp op = true := by
  cases op <;> simp [opC, isBvOp]

theorem opC_mod8_eq_one_iff {op : Op} : opC op % 8 = 1 ↔ isBoolOp op = true := by
  cases op <;> simp [opC, isBoolOp]

theorem opC_mod8_eq_two_iff {op : Op} : opC op % 8 = 2 ↔ ∃ e, op = .listVal e := by
  cases op <;> simp [opC]

theorem opC_listVal_iff' {op : Op} : opC op % 8 = 2 ↔ opC op = 0x0a := by
  cases op <;> simp [opC]

end Vbcf.Proof
