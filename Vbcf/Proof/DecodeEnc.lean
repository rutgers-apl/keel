import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.EncLemmas
import Vbcf.Proof.LoadSpec2

/-!
# Vbcf proofs: `decodeNode` inverts the C encoding of a node header

The C checker never calls a decoder: it writes a candidate's words into the
pool and lets `ck_intern` (through `ck_tyck`) accept or reject them.  The Lean
checker decodes a header with `Bcf.decodeNode` (in the loader and in
`Bcf.congOp`).  This file connects the two: **a fitting node whose header word
is `h` is what `decodeNode` produces from the fields of `h`**.

* `decodeNode_enc_inner`, `decodeNode_enc_boolVal`, `decodeNode_enc_var`,
  `decodeNode_enc_bvVal`: on operators (`opC`, `opLo`, `opHi`);
* `decodeNode_hdrW_inner`, `decodeNode_hdrW_boolVal`, `decodeNode_hdrW_var`,
  `decodeNode_hdrW_bvVal`: on the header word `hdrW n` of a fitting node,
  with the fields extracted the way the loader does (`h % 256`,
  `h / 256 % 256`, `h / 65536`);
* `decodeNode_hdrW_op`: for *every* fitting, non-literal node, whatever
  argument words are supplied, the decoded operator is the node's (variables
  up to their identity);
* `congOp_hdrW`: the form `Bcf.congOp` uses.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-! ## Parameter bytes -/

theorem params_lo {lo hi : Nat} (hlo : lo < 256) : (lo + hi * 256) &&& 0xff = lo := by
  rw [nat_and_ff]; omega

theorem params_hi {lo hi : Nat} (hlo : lo < 256) (hhi : hi < 256) :
    ((lo + hi * 256) >>> 8) &&& 0xff = hi := by
  rw [nat_and_ff, nat_shr_8]; omega

/-! ## On operators -/

/-- A non-leaf operator is decoded from its code and parameter bytes, with
whatever argument words are supplied. -/
theorem decodeNode_enc_inner (op : Op) (hl : ¬ IsLeaf op) (hlo : opLo op < 256)
    (hhi : opHi op < 256) (d v : Nat) (ws : Array Nat) :
    decodeNode d (opC op) v (opLo op + opHi op * 256) ws = some ⟨op, ws⟩ := by
  have e1 := params_lo (hi := opHi op) hlo
  have e2 := params_hi hlo hhi
  cases op <;> first
    | exact absurd rfl hl
    | (simp only [opC, opLo, opHi, Nat.zero_mul, Nat.add_zero] at e1 e2 hlo hhi ⊢
       simp [decodeNode, e1, e2, guard]; done)
    | (rename_i b; cases b <;> simp [decodeNode, opC, opLo, opHi, guard])

/-- A boolean literal: no arguments, whatever words are supplied. -/
theorem decodeNode_enc_boolVal (b : Bool) (d v : Nat) (ws : Array Nat) :
    decodeNode d 0x09 v (if b then 1 else 0) ws = some ⟨.boolVal b, #[]⟩ := by
  cases b <;> simp [decodeNode, guard]

/-- A bit-vector variable: its identity is the index given to the decoder. -/
theorem decodeNode_enc_bvVar {w : Nat} (hw : w < 256) (d v : Nat) (ws : Array Nat) :
    decodeNode d 0x18 v w ws = some ⟨.bvVar w d, #[]⟩ := by
  have e1 : w &&& 255 = w := by rw [nat_and_ff]; omega
  have e2 : w >>> 8 &&& 255 = 0 := by rw [nat_and_ff, nat_shr_8]; omega
  simp [decodeNode, guard, e1, e2]

theorem decodeNode_enc_boolVar (d v : Nat) (ws : Array Nat) :
    decodeNode d 0x19 v 0 ws = some ⟨.boolVar d, #[]⟩ := by
  simp [decodeNode, guard]

/-- A typed bit-vector literal is decoded from its value words. -/
theorem decodeNode_enc_bvVal {w val : Nat} (hw0 : w ≠ 0) (hw : w ≤ 64) (hv : val < 2 ^ w)
    (d : Nat) (ws : Array Nat) (h0 : ws[0]! = val % 2 ^ 32) (h1 : 32 < w → ws[1]! = val / 2 ^ 32) :
    decodeNode d 0x08 (if w ≤ 32 then 1 else 2) w ws = some ⟨.bvVal w val, #[]⟩ := by
  have e1 : w &&& 255 = w := by rw [nat_and_ff]; omega
  have e2 : w >>> 8 &&& 255 = 0 := by rw [nat_and_ff, nat_shr_8]; omega
  by_cases h32 : w ≤ 32
  · have hq : (w + 31) / 32 = 1 := by omega
    have : 2 ^ w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) h32
    have hval : val % 2 ^ 32 = val := Nat.mod_eq_of_lt (by omega)
    simp [decodeNode, guard, e1, e2, h32, hw0, hq, h0]
    simpa using hval
  · have hq : (w + 31) / 32 = 2 := by omega
    have hval : val % 2 ^ 32 ||| (val / 2 ^ 32) <<< 32 = val := by
      rw [LoadSpec.or_shl_eq_add _ _ _ (Nat.mod_lt _ (by decide))]
      have := Nat.div_add_mod val (2 ^ 32)
      omega
    simp [decodeNode, guard, e1, e2, h32, hw0, hq, h0, h1 (by omega)]
    simpa using hval

/-- Every operator other than a bit-vector literal, in one statement: the
decoder returns the operator (a variable gets the decoder's index as its
identity); a leaf has no arguments, any other node has the supplied words. -/
theorem decodeNode_enc_op (op : Op) (hnv : ∀ w v, op ≠ .bvVal w v) (hlo : opLo op < 256)
    (hhi : opHi op < 256) (d v : Nat) (ws : Array Nat) :
    decodeNode d (opC op) v (opLo op + opHi op * 256) ws =
      some ⟨reidx op d, if IsLeaf op then #[] else ws⟩ := by
  by_cases hl : IsLeaf op
  · rcases isLeaf_iff.mp hl with ⟨w, id, rfl⟩ | ⟨id, rfl⟩ | ⟨w, v', rfl⟩ | ⟨b, rfl⟩
    · simpa [opC, opLo, opHi, reidx, IsLeaf, isLeaf] using decodeNode_enc_bvVar (w := w) hlo d v ws
    · simpa [opC, opLo, opHi, reidx, IsLeaf, isLeaf] using decodeNode_enc_boolVar d v ws
    · exact absurd rfl (hnv w v')
    · simpa [opC, opLo, opHi, reidx, IsLeaf, isLeaf] using decodeNode_enc_boolVal b d v ws
  · rw [decodeNode_enc_inner op hl hlo hhi]; simp only [hl, ↓reduceIte]
    have : reidx op d = op := by
      cases op <;> first | rfl | exact absurd rfl hl
    rw [this]

/-! ## On header words -/

section
variable {posOf : Nat → Nat} {n : Node}

/-- The header fields of a fitting node, as the loader extracts them. -/
theorem hdrCode_hdrW (hf : Fits posOf n) : hdrCode (hdrW n) = opC n.op := hdrW_code hf
theorem hdrVlen_hdrW (hf : Fits posOf n) : hdrVlen (hdrW n) = tailLen n := hdrW_len hf
theorem hdrParams_hdrW (hf : Fits posOf n) : hdrParams (hdrW n) = opLo n.op + opHi n.op * 256 :=
  hdrW_params hf

/-- **A fitting non-leaf node whose header word is `h` is what `decodeNode`
produces from `h`**, for any argument words (and any `vlen`, any index). -/
theorem decodeNode_hdrW_inner (hf : Fits posOf n) (hl : ¬ IsLeaf n.op) (d v : Nat)
    (ws : Array Nat) :
    decodeNode d (hdrW n % 256) v (hdrW n / 65536) ws = some ⟨n.op, ws⟩ := by
  rw [hdrW_code hf, hdrW_params hf]
  exact decodeNode_enc_inner n.op hl hf.lo hf.hi d v ws

/-- The same from the fields, however they were obtained. -/
theorem decodeNode_of_fields (hf : Fits posOf n) (hl : ¬ IsLeaf n.op) {code params : Nat}
    (hc : code = hdrW n % 256) (hp : params = hdrW n / 65536) (d v : Nat) (ws : Array Nat) :
    decodeNode d code v params ws = some ⟨n.op, ws⟩ := by
  subst hc hp; exact decodeNode_hdrW_inner hf hl d v ws

/-- Every fitting node other than a bit-vector literal. -/
theorem decodeNode_hdrW_op (hf : Fits posOf n) (hnv : ∀ w v, n.op ≠ .bvVal w v) (d v : Nat)
    (ws : Array Nat) :
    decodeNode d (hdrW n % 256) v (hdrW n / 65536) ws =
      some ⟨reidx n.op d, if IsLeaf n.op then #[] else ws⟩ := by
  rw [hdrW_code hf, hdrW_params hf]
  exact decodeNode_enc_op n.op hnv hf.lo hf.hi d v ws

/-- A fitting variable node: the wire header has arity 0 (the C header has 1);
the decoder ignores it. -/
theorem decodeNode_hdrW_var (hf : Fits posOf n) (hv : opC n.op = 0x18 ∨ opC n.op = 0x19)
    (d v : Nat) (ws : Array Nat) :
    decodeNode d (hdrW n % 256) v (hdrW n / 65536) ws = some ⟨reidx n.op d, #[]⟩ := by
  rw [decodeNode_hdrW_op hf (fun w v' e => by rw [e] at hv; simp [opC] at hv)]
  have : IsLeaf n.op := by
    rcases hv with hv | hv
    · obtain ⟨w, id, e⟩ := opC_bvVar_iff.mp hv; rw [e]; rfl
    · obtain ⟨id, e⟩ := opC_boolVar_iff.mp hv; rw [e]; rfl
  exact congrArg (fun a => some (Node.mk (reidx n.op d) a)) (by simp [this])

theorem decodeNode_hdrW_boolVal (hf : Fits posOf n) (hv : opC n.op = 0x09) (d v : Nat)
    (ws : Array Nat) :
    decodeNode d (hdrW n % 256) v (hdrW n / 65536) ws = some ⟨n.op, #[]⟩ := by
  obtain ⟨b, e⟩ := opC_boolVal_iff.mp hv
  rw [decodeNode_hdrW_op hf (fun w v' e' => by rw [e'] at hv; simp [opC] at hv), e]
  rfl

/-- A fitting, typed bit-vector literal is decoded from its header and its
tail words (the words the C stores after the header). -/
theorem decodeNode_hdrW_bvVal (hf : Fits posOf n) {argTys : List Ty} {t : Ty}
    (ht : n.op.resultTy argTys = some t) (hv : opC n.op = 0x08) (off : Nat → Nat) (d : Nat) :
    decodeNode d (hdrW n % 256) (hdrW n / 256 % 256) (hdrW n / 65536)
      (tailW posOf off n).toArray = some ⟨n.op, #[]⟩ := by
  rw [hdrW_code hf, hdrW_params hf, hdrW_len hf]
  obtain ⟨w, val, e⟩ := opC_bvVal_iff.mp hv
  rcases n with ⟨op, args⟩
  simp only at e
  subst e
  obtain ⟨hw0, hw, hval⟩ := resultTy_bvVal ht
  simp only [opC, opLo, opHi, tailLen, tailW, Nat.zero_mul, Nat.add_zero]
  apply decodeNode_enc_bvVal hw0 hw hval
  · by_cases h32 : w ≤ 32 <;> simp [h32]
  · intro h32
    have : ¬ w ≤ 32 := by omega
    simp [this]

end

/-! ## `Bcf.congOp` -/

/-- `congOp` on a header whose code and parameter fields are those of a
fitting non-leaf node returns that node's operator (the arity field of the
header and the `vlen` argument are irrelevant). -/
theorem congOp_of_node {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) (hl : ¬ IsLeaf n.op)
    {hdr : Nat} (hc : hdr % 256 = hdrW n % 256) (hp : hdr / 65536 % 65536 = hdrW n / 65536)
    (v : Nat) : congOp hdr v = some n.op := by
  unfold congOp
  have e1 : hdr &&& 0xff = hdrW n % 256 := by rw [nat_and_ff]; exact hc
  have e2 : (hdr >>> 16) &&& 0xffff = hdrW n / 65536 := by
    rw [LoadSpec.and_ffff, nat_shr_16]; exact hp
  simp only [e1, e2, decodeNode_hdrW_inner hf hl, bind, Option.bind]
  cases hop : n.op <;> first | rfl | (rw [hop] at hl; exact absurd rfl hl)

/-- `congOp` on the header word of a fitting non-leaf node. -/
theorem congOp_hdrW {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) (hl : ¬ IsLeaf n.op)
    (v : Nat) : congOp (hdrW n) v = some n.op :=
  congOp_of_node hf hl rfl (Nat.mod_eq_of_lt (hdrW_params_lt hf)) v

end Vbcf.Proof
