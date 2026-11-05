import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.LoadSpec1

/-!
# Vbcf proofs: the one-pass loader — basic lemmas and the forward invariant

Words and bytes, positions, the shape of `decodeNode`'s results, and the
incremental description `specN` of what `Bcf.decode` + `Bcf.canonicalize`
compute for the first `d` expressions.  `LoadInv` says the one-pass loader
has reached the state described by `specN`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-! ## Words and bytes -/

theorem wordsToBytes_size (ws : Array (BitVec 32)) : (wordsToBytes ws).size = 4 * ws.size := by
  simp [wordsToBytes, ByteArray.size]

theorem wordsToBytes_get (ws : Array (BitVec 32)) (i k : Nat) (hi : i < ws.size) (hk : k < 4) :
    (wordsToBytes ws)[4 * i + k]!.toNat = ws[i].toNat / 2 ^ (8 * k) % 256 := by
  have hlt : 4 * i + k < (wordsToBytes ws).size := by rw [wordsToBytes_size]; omega
  rw [getElem!_pos (wordsToBytes ws) (4 * i + k) hlt]
  show ((wordsToBytes ws).data[4 * i + k]'_).toNat = _
  simp only [wordsToBytes, Array.getElem_ofFn]
  have h1 : (4 * i + k) / 4 = i := by omega
  have h2 : (4 * i + k) % 4 = k := by omega
  simp only [h1, h2, getElem!_pos ws i hi, UInt8.toNat_ofNat']

theorem LoadSpec.or_shl_eq_add (a b i : Nat) (hb : b < 2 ^ i) : b ||| (a <<< i) = a * 2 ^ i + b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

theorem LoadSpec.u32_assemble (x : Nat) (hx : x < 2 ^ 32) :
    (x / 2 ^ (8 * 0) % 256) ||| ((x / 2 ^ (8 * 1) % 256) <<< 8) ||| ((x / 2 ^ (8 * 2) % 256) <<< 16) |||
      ((x / 2 ^ (8 * 3) % 256) <<< 24) = x := by
  rw [LoadSpec.or_shl_eq_add _ _ 8 (by omega), LoadSpec.or_shl_eq_add _ _ 16 (by omega), LoadSpec.or_shl_eq_add _ _ 24 (by omega)]
  omega

theorem u32At_wordsToBytes (ws : Array (BitVec 32)) (i : Nat) (hi : i < ws.size) :
    u32At (wordsToBytes ws) (4 * i) = ws[i].toNat := by
  unfold u32At
  have h0 := wordsToBytes_get ws i 0 hi (by omega)
  rw [wordsToBytes_get ws i 1 hi (by omega), wordsToBytes_get ws i 2 hi (by omega),
    wordsToBytes_get ws i 3 hi (by omega)]
  rw [Nat.add_zero] at h0
  rw [h0]
  exact LoadSpec.u32_assemble _ ws[i].isLt

theorem wordFn_lt (ws : Array (BitVec 32)) (i : Nat) : wordFn ws i < 2 ^ 32 := (ws[i]!).isLt

theorem wordFn_eq (ws : Array (BitVec 32)) (i : Nat) (hi : i < ws.size) :
    wordFn ws i = ws[i].toNat := by
  rw [wordFn, getElem!_pos ws i hi]

theorem u32At_wordFn (ws : Array (BitVec 32)) (i : Nat) (hi : i < ws.size) :
    u32At (wordsToBytes ws) (4 * i) = wordFn ws i := by
  rw [u32At_wordsToBytes ws i hi, wordFn, getElem!_pos ws i hi]

/-! ## Bit operations of the decoder as arithmetic -/

theorem LoadSpec.and_ff (x : Nat) : x &&& 0xff = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
theorem LoadSpec.and_ffff (x : Nat) : x &&& 0xffff = x % 65536 := Nat.and_two_pow_sub_one_eq_mod x 16
theorem LoadSpec.shr8 (x : Nat) : x >>> 8 = x / 256 := Nat.shiftRight_eq_div_pow x 8
theorem LoadSpec.shr16 (x : Nat) : x >>> 16 = x / 65536 := Nat.shiftRight_eq_div_pow x 16
theorem LoadSpec.shr24 (x : Nat) : x >>> 24 = x / 16777216 := Nat.shiftRight_eq_div_pow x 24

/-! ## Positions -/

theorem posOfW_succ (w : Nat → Nat) (d : Nat) :
    posOfW w (d + 1) = posOfW w d + 1 + hdrVlen (w (3 + posOfW w d)) := rfl

theorem posOfW_lt_succ (w : Nat → Nat) (d : Nat) : posOfW w d < posOfW w (d + 1) := by
  show _ < posOfW w d + 1 + _; omega

theorem posOfW_mono (w : Nat → Nat) {i j : Nat} (h : i ≤ j) : posOfW w i ≤ posOfW w j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega)) (Nat.le_of_lt (posOfW_lt_succ w j))
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

theorem posOfW_strictMono (w : Nat → Nat) {i j : Nat} (h : i < j) : posOfW w i < posOfW w j :=
  Nat.lt_of_lt_of_le (posOfW_lt_succ w i) (posOfW_mono w h)

theorem posOfW_inj (w : Nat → Nat) {i j : Nat} (h : posOfW w i = posOfW w j) : i = j := by
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · have := posOfW_strictMono w h'; omega
  · exact h'
  · have := posOfW_strictMono w h'; omega

theorem le_posOfW (w : Nat → Nat) (d : Nat) : d ≤ posOfW w d := by
  induction d with
  | zero => exact Nat.zero_le _
  | succ d ih => have := posOfW_lt_succ w d; omega

theorem idxOf_eq_some (w : Nat → Nat) (n a j : Nat) :
    idxOf w n a = some j ↔ j < n ∧ posOfW w j = a := by
  induction n with
  | zero => simp [idxOf]
  | succ n ih =>
    unfold idxOf
    split
    · rename_i h
      constructor
      · intro h'; simp at h'; subst h'; exact ⟨by omega, h⟩
      · rintro ⟨_, h2⟩
        rw [← h2] at h
        rw [posOfW_inj w h]
    · rename_i h
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_or_ge j n with h' | h'
        · exact h'
        · have : j = n := by omega
          subst this; exact absurd h2 h

theorem idxOf_posOfW (w : Nat → Nat) {n j : Nat} (h : j < n) : idxOf w n (posOfW w j) = some j :=
  (idxOf_eq_some w n _ j).2 ⟨h, rfl⟩

theorem pmOf_push (w : Nat → Nat) (remap : Array Nat) (r a : Nat) :
    pmOf w (remap.push r) a = pmSet (pmOf w remap) (posOfW w remap.size) r a := by
  unfold pmOf pmSet
  simp only [Array.size_push, idxOf]
  split
  · rename_i h
    simp [h]
  · rename_i h
    have h' : ¬ a = posOfW w remap.size := fun e => h e.symm
    simp only [h', ↓reduceIte]
    cases hj : idxOf w remap.size a with
    | none => rfl
    | some j =>
      have := ((idxOf_eq_some w _ _ _).1 hj).1
      simp [Array.getElem?_push, Nat.ne_of_lt this]


/-! ## The shape of `decodeNode`'s results -/

/-- Give a variable operator the identity `i` (what `densify` does to variables). -/
def reidx (o : Op) (i : Nat) : Op :=
  match o with
  | .bvVar w _ => .bvVar w i
  | .boolVar _ => .boolVar i
  | o => o

/-- The number of words after a node's header, as `densify` and `positionMap`
recompute it from the decoded node. -/
def vlenOf (n : Node) : Nat :=
  match n.op with
  | .bvVal w _ => (w + 31) / 32
  | _ => n.args.size

theorem LoadSpec.guard_bind_opt {α : Type} (p : Prop) [Decidable p] (x : Unit → Option α) :
    (guard p : Option Unit).bind x = if p then x () else none := by
  by_cases h : p <;> simp [guard, h]

/-- `decodeNode` uses its index argument only as the identity of a variable. -/
theorem decodeNode_reidx (i j c v ps : Nat) (ws : Array Nat) :
    decodeNode j c v ps ws = (decodeNode i c v ps ws).map (fun n => ⟨reidx n.op j, n.args⟩) := by
  unfold decodeNode
  simp only [bind, pure, LoadSpec.guard_bind_opt]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> simp [reidx]
  · split
    · split <;> (try split) <;> simp [reidx]
    · split
      · split
        · split <;> (try split) <;> simp [reidx]
        · rfl
      · rfl

set_option maxRecDepth 100000 in
theorem LoadSpec.code_split : ∀ c, c < 256 → (c &&& 248) + (c &&& 7) = c := by decide

/-- Arguments and recomputed length of a decoded node, by kind of header:
variables and boolean literals have no arguments and recomputed length 0
(whatever `vlen` says); bit-vector literals have no arguments and recomputed
length `vlen`; every other node has the words after the header as arguments. -/
theorem decodeNode_shape {i c v ps : Nat} {ws : Array Nat} {n : Node}
    (h : decodeNode i c v ps ws = some n) :
    (((c &&& 0xf8 = 0x18 ∧ (c &&& 7 = 0 ∨ c &&& 7 = 1)) ∨ (c &&& 0xf8 = 0x08 ∧ c &&& 7 = 1)) →
      n.args = #[] ∧ vlenOf n = 0 ∧ (c &&& 0xf8 = 0x08 → ∃ b, n.op = .boolVal b)) ∧
    ((c &&& 0xf8 = 0x08 ∧ c &&& 7 = 0) → n.args = #[] ∧ vlenOf n = v) ∧
    (¬ (c &&& 0xf8 = 0x18 ∧ (c &&& 7 = 0 ∨ c &&& 7 = 1)) →
      ¬ (c &&& 0xf8 = 0x08 ∧ (c &&& 7 = 0 ∨ c &&& 7 = 1)) → n.args = ws ∧ vlenOf n = ws.size) := by
  unfold decodeNode at h
  simp only [bind, pure, LoadSpec.guard_bind_opt] at h
  split at h
  · rename_i h1
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp at h <;>
      (try replace h := h.2) <;> (try replace h := h.2) <;> subst h <;> simp_all [vlenOf]
  · split at h
    · rename_i h1
      split at h <;> (try split at h) <;> simp at h <;>
        (try replace h := h.2) <;> subst h <;> simp_all [vlenOf]
    · split at h
      · split at h
        · split at h <;> (try split at h) <;> simp at h <;> subst h <;> simp_all [vlenOf]
        · simp at h
      · simp at h

theorem hdrCode_lt (h : Nat) : hdrCode h < 256 := by unfold hdrCode; omega

theorem decodeNode_leaf0 {i c v ps : Nat} {ws : Array Nat} {n : Node}
    (h : decodeNode i c v ps ws = some n) (hc : c = 0x18 ∨ c = 0x19 ∨ c = 0x09) :
    n.args = #[] ∧ vlenOf n = 0 ∧ (c = 0x09 → ∃ b, n.op = .boolVal b) := by
  have := (decodeNode_shape h).1
  rcases hc with rfl | rfl | rfl
  · obtain ⟨h1, h2, _⟩ := this (by decide)
    exact ⟨h1, h2, fun h => absurd h (by decide)⟩
  · obtain ⟨h1, h2, _⟩ := this (by decide)
    exact ⟨h1, h2, fun h => absurd h (by decide)⟩
  · obtain ⟨h1, h2, h3⟩ := this (by decide)
    exact ⟨h1, h2, fun _ => h3 (by decide)⟩

theorem decodeNode_val {i v ps : Nat} {ws : Array Nat} {n : Node}
    (h : decodeNode i 0x08 v ps ws = some n) : n.args = #[] ∧ vlenOf n = v :=
  (decodeNode_shape h).2.1 (by decide)

theorem decodeNode_inner {i c v ps : Nat} {ws : Array Nat} {n : Node}
    (h : decodeNode i c v ps ws = some n) (hc : c < 256)
    (h1 : c ≠ 0x18) (h2 : c ≠ 0x19) (h3 : c ≠ 0x08) (h4 : c ≠ 0x09) :
    n.args = ws ∧ vlenOf n = ws.size := by
  have hs := LoadSpec.code_split c hc
  exact (decodeNode_shape h).2.2 (by omega) (by omega)

theorem decodeNode_reidx_some {i j c v ps : Nat} {ws : Array Nat} {n : Node}
    (h : decodeNode i c v ps ws = some n) :
    decodeNode j c v ps ws = some ⟨reidx n.op j, n.args⟩ := by
  rw [decodeNode_reidx i j, h]; rfl

theorem reidx_reidx_of_decode {i j c v ps : Nat} {ws : Array Nat} {n : Node}
    (h : decodeNode i c v ps ws = some n) : reidx (reidx n.op j) i = n.op := by
  have h1 := decodeNode_reidx_some (j := j) h
  have h2 := decodeNode_reidx_some (j := i) h1
  rw [h] at h2
  simp only [Option.some.injEq] at h2
  exact (congrArg Node.op h2).symm

theorem argWords_length (w : Nat → Nat) (p v : Nat) : (argWords w p v).length = v := by
  simp [argWords]

/-! ## The incremental description of the Lean pipeline -/

/-- The raw node of the `d`-th expression, as `decodeExprs` produces it
(variables carry their position). -/
def rawNode (w : Nat → Nat) (d : Nat) : Option Node :=
  decodeNode (posOfW w d) (hdrCode (w (3 + posOfW w d))) (hdrVlen (w (3 + posOfW w d)))
    (hdrParams (w (3 + posOfW w d))) (argWords w (posOfW w d) (hdrVlen (w (3 + posOfW w d)))).toArray

/-- What the Lean pipeline has computed after the first `d` expressions: the
raw pool (`decodeExprs`), the dense pool (`densify`), the checker state and
the raw-to-canonical map (`canonicalize`). -/
structure Loaded where
  raw : Pool
  dense : Pool
  st : St
  remap : Array Nat

/-- Process the `d`-th expression. -/
def specStep (w : Nat → Nat) (t : Loaded) (d : Nat) : Option Loaded :=
  match rawNode w d with
  | none => none
  | some rn =>
    if vlenOf rn = hdrVlen (w (3 + posOfW w d)) then
      match mapOpt (idxOf w d) rn.args.toList with
      | none => none
      | some dargs =>
        match remapArgs t.remap dargs.toArray with
        | none => none
        | some cargs =>
          match pushNode t.st ⟨reidx rn.op d, cargs⟩ with
          | none => none
          | some (st', r) =>
            some ⟨t.raw.push rn, t.dense.push ⟨reidx rn.op d, dargs.toArray⟩, st', t.remap.push r⟩
    else none

/-- The first `d` expressions, processed in order from state `st1`. -/
def specN (w : Nat → Nat) (st1 : St) : Nat → Option Loaded
  | 0 => some ⟨#[], #[], st1, #[]⟩
  | d + 1 =>
    match specN w st1 d with
    | none => none
    | some t => specStep w t d

theorem LoadSpec.mapOpt_factor {α β γ : Type} {F : α → Option γ} {f : α → Option β} {g : β → Option γ}
    {l : List α} {cs : List γ} (h : mapOpt F l = some cs)
    (hF : ∀ a c, F a = some c → ∃ b, f a = some b ∧ g b = some c) :
    ∃ bs, mapOpt f l = some bs ∧ mapOpt g bs = some cs := by
  induction l generalizing cs with
  | nil => simp [mapOpt] at h; subst h; exact ⟨[], rfl, rfl⟩
  | cons a rest ih =>
    simp only [mapOpt] at h
    split at h
    · rename_i c cs' hc hrest
      simp at h; subst h
      obtain ⟨b, hb, hg⟩ := hF a c hc
      obtain ⟨bs, hbs, hgs⟩ := ih hrest
      exact ⟨b :: bs, by simp [mapOpt, hb, hbs], by simp [mapOpt, hg, hgs]⟩
    · simp at h

/-- What `loadNode` returns, when the node is then accepted by `pushNode`. -/
theorem loadNode_spec {w : Nat → Nat} {p d : Nat} {pm : Nat → Option Nat} {cn : Node} {st st' : St}
    {r : Nat} (hn : loadNode w p d pm = some cn) (hp : pushNode st cn = some (st', r)) :
    ∃ n0 cargs,
      decodeNode d (hdrCode (w (3 + p))) (hdrVlen (w (3 + p))) (hdrParams (w (3 + p)))
        (argWords w p (hdrVlen (w (3 + p)))).toArray = some n0 ∧
      cn = ⟨n0.op, cargs.toArray⟩ ∧
      mapOpt (fun a => if a < p then pm a else none) n0.args.toList = some cargs ∧
      (hdrCode (w (3 + p)) = 0x18 ∨ hdrCode (w (3 + p)) = 0x19 ∨ hdrCode (w (3 + p)) = 0x09 →
        hdrVlen (w (3 + p)) = 0) := by
  unfold loadNode at hn
  split at hn
  · rename_i hc
    split at hn
    · rename_i hv
      have hl := decodeNode_leaf0 hn (by omega)
      refine ⟨cn, [], ?_, ?_, ?_, fun _ => hv⟩
      · rw [hv]; simpa [argWords] using hn
      · cases cn; simp_all
      · rw [hl.1]; rfl
    · simp at hn
  · rename_i hc
    split at hn
    · rename_i hc8
      rw [hc8] at hn
      have hl := decodeNode_val hn
      refine ⟨cn, [], ?_, ?_, ?_, fun h => ?_⟩
      · rw [hc8]; exact hn
      · cases cn; simp_all
      · rw [hl.1]; rfl
      · omega
    · rename_i hc8
      split at hn
      · simp at hn
      · rename_i n hdn
        split at hn
        · simp at hn
        · rename_i cargs hmap
          simp only [Option.some.injEq] at hn
          subst hn
          by_cases hc9 : hdrCode (w (3 + p)) = 0x09
          · -- a boolean literal with arguments does not type-check
            have hl := decodeNode_leaf0 hdn (by omega)
            obtain ⟨b, hb⟩ := hl.2.2 hc9
            obtain ⟨argTys, t, _, hm, ht, _⟩ := pushNode_cases hp
            simp only [hb, Op.resultTy] at ht
            have hty : argTys = [] := by
              cases argTys with
              | nil => rfl
              | cons a l => simp [boolNullTy] at ht
            subst hty
            have h1 := mapOpt_nil_inv hm
            have h1' : cargs = [] := by simpa using h1
            subst h1'
            have h2 := mapOpt_nil_inv hmap
            have hv : hdrVlen (w (3 + p)) = 0 := by rw [← argWords_length w p (hdrVlen (w (3 + p))), h2]; rfl
            refine ⟨n, [], hdn, rfl, ?_, fun _ => hv⟩
            rw [hl.1]; rfl
          · have hi := decodeNode_inner hdn (hdrCode_lt _) (by omega) (by omega) hc8 hc9
            refine ⟨n, cargs, hdn, rfl, ?_, fun h => by omega⟩
            rw [hi.1]; exact hmap

/-- One iteration of the one-pass loader is one step of the incremental
description of the Lean pipeline. -/
theorem specStep_of_load {w : Nat → Nat} {t : Loaded} {d : Nat} {pm : Nat → Option Nat} {cn : Node}
    {st' : St} {r : Nat} (hsz : t.remap.size = d) (hpm : ∀ a, pm a = pmOf w t.remap a)
    (hn : loadNode w (posOfW w d) d pm = some cn) (hp : pushNode t.st cn = some (st', r)) :
    ∃ rn dn, specStep w t d = some ⟨t.raw.push rn, t.dense.push dn, st', t.remap.push r⟩ := by
  obtain ⟨n0, cargs, hdn, rfl, hmap, hv0⟩ := loadNode_spec hn hp
  have hraw := decodeNode_reidx_some (j := posOfW w d) hdn
  have hvl : vlenOf (⟨reidx n0.op (posOfW w d), n0.args⟩ : Node) = hdrVlen (w (3 + posOfW w d)) := by
    by_cases hc : hdrCode (w (3 + posOfW w d)) = 0x18 ∨ hdrCode (w (3 + posOfW w d)) = 0x19 ∨
        hdrCode (w (3 + posOfW w d)) = 0x09
    · rw [(decodeNode_leaf0 hraw hc).2.1, hv0 hc]
    · by_cases hc8 : hdrCode (w (3 + posOfW w d)) = 0x08
      · rw [hc8] at hraw; exact (decodeNode_val hraw).2
      · rw [(decodeNode_inner hraw (hdrCode_lt _) (by omega) (by omega) hc8 (by omega)).2]
        simp [argWords_length]
  obtain ⟨dargs, hd, hc⟩ := LoadSpec.mapOpt_factor (f := idxOf w d) (g := fun a => t.remap[a]?) hmap (by
    intro a c hF
    split at hF
    · rw [hpm a, pmOf, hsz] at hF
      cases hj : idxOf w d a with
      | none => rw [hj] at hF; simp at hF
      | some j => rw [hj] at hF; exact ⟨j, rfl, hF⟩
    · simp at hF)
  refine ⟨⟨reidx n0.op (posOfW w d), n0.args⟩, ⟨reidx (reidx n0.op (posOfW w d)) d, dargs.toArray⟩, ?_⟩
  unfold specStep
  simp only [rawNode, hraw, hvl, ↓reduceIte, hd, remapArgs, hc, Option.map_some,
    reidx_reidx_of_decode hdn, hp]

theorem specStep_inv {w : Nat → Nat} {t t' : Loaded} {d : Nat} (h : specStep w t d = some t') :
    ∃ rn dargs cargs r, rawNode w d = some rn ∧ vlenOf rn = hdrVlen (w (3 + posOfW w d)) ∧
      mapOpt (idxOf w d) rn.args.toList = some dargs ∧
      remapArgs t.remap dargs.toArray = some cargs ∧
      pushNode t.st ⟨reidx rn.op d, cargs⟩ = some (t'.st, r) ∧
      t'.raw = t.raw.push rn ∧ t'.dense = t.dense.push ⟨reidx rn.op d, dargs.toArray⟩ ∧
      t'.remap = t.remap.push r := by
  unfold specStep at h
  split at h
  · simp at h
  · rename_i rn hrn
    split at h
    · rename_i hv
      split at h
      · simp at h
      · rename_i dargs hd
        split at h
        · simp at h
        · rename_i cargs hc
          split at h
          · simp at h
          · rename_i st' r hp
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨rn, dargs, cargs, r, hrn, hv, hd, hc, hp, rfl, rfl, rfl⟩
    · simp at h

theorem specN_succ {w : Nat → Nat} {st1 : St} {d : Nat} {t' : Loaded}
    (h : specN w st1 (d + 1) = some t') : ∃ t, specN w st1 d = some t ∧ specStep w t d = some t' := by
  simp only [specN] at h
  split at h
  · simp at h
  · rename_i t ht; exact ⟨t, ht, h⟩

theorem specN_sizes {w : Nat → Nat} {st1 : St} {d : Nat} {t : Loaded} (h : specN w st1 d = some t) :
    t.raw.size = d ∧ t.dense.size = d ∧ t.remap.size = d := by
  induction d generalizing t with
  | zero => simp only [specN, Option.some.injEq] at h; subst h; simp
  | succ d ih =>
    obtain ⟨t0, h0, hs⟩ := specN_succ h
    obtain ⟨rn, dargs, cargs, r, _, _, _, _, _, h1, h2, h3⟩ := specStep_inv hs
    obtain ⟨i1, i2, i3⟩ := ih h0
    rw [h1, h2, h3]; simp [i1, i2, i3]

/-- Earlier stages of a successful run exist and are prefixes of the result. -/
theorem specN_prefix {w : Nat → Nat} {st1 : St} {D : Nat} {T : Loaded} (h : specN w st1 D = some T)
    {d : Nat} (hd : d ≤ D) :
    ∃ t, specN w st1 d = some t ∧ t.st.pool.size ≤ T.st.pool.size ∧
      ∀ j, j < d → t.raw[j]? = T.raw[j]? ∧ t.dense[j]? = T.dense[j]? ∧ t.remap[j]? = T.remap[j]? := by
  induction D generalizing T with
  | zero =>
    have : d = 0 := by omega
    subst this
    exact ⟨T, h, Nat.le_refl _, fun j hj => ⟨rfl, rfl, rfl⟩⟩
  | succ D ih =>
    rcases Nat.lt_or_ge d (D + 1) with hlt | hge
    · obtain ⟨t0, h0, hs⟩ := specN_succ h
      obtain ⟨t, ht, hsz, hpre⟩ := ih h0 (by omega)
      obtain ⟨rn, dargs, cargs, r, _, _, _, _, hp, h1, h2, h3⟩ := specStep_inv hs
      obtain ⟨s1, s2, s3⟩ := specN_sizes h0
      refine ⟨t, ht, Nat.le_trans hsz (pushNode_size hp).1, fun j hj => ?_⟩
      obtain ⟨p1, p2, p3⟩ := hpre j hj
      rw [h1, h2, h3, p1, p2, p3]
      simp [Array.getElem?_push, show j ≠ t0.raw.size by omega, show j ≠ t0.dense.size by omega,
        show j ≠ t0.remap.size by omega]
    · have : d = D + 1 := by omega
      subst this
      exact ⟨T, h, Nat.le_refl _, fun j hj => ⟨rfl, rfl, rfl⟩⟩

/-- Everything known about the `d`-th expression of a successful run. -/
theorem specN_at {w : Nat → Nat} {st1 : St} {D : Nat} {T : Loaded} (h : specN w st1 D = some T)
    {d : Nat} (hd : d < D) :
    ∃ t t' rn dargs cargs r, specN w st1 d = some t ∧ specN w st1 (d + 1) = some t' ∧
      rawNode w d = some rn ∧ vlenOf rn = hdrVlen (w (3 + posOfW w d)) ∧
      mapOpt (idxOf w d) rn.args.toList = some dargs ∧
      remapArgs t.remap dargs.toArray = some cargs ∧
      pushNode t.st ⟨reidx rn.op d, cargs⟩ = some (t'.st, r) ∧
      t'.raw = t.raw.push rn ∧ t'.dense = t.dense.push ⟨reidx rn.op d, dargs.toArray⟩ ∧
      t'.remap = t.remap.push r ∧
      T.raw[d]? = some rn ∧ T.dense[d]? = some ⟨reidx rn.op d, dargs.toArray⟩ ∧ T.remap[d]? = some r ∧
      t'.st.pool.size ≤ T.st.pool.size := by
  obtain ⟨t', ht', hsz, hpre⟩ := specN_prefix h (d := d + 1) (by omega)
  obtain ⟨t, ht, hs⟩ := specN_succ ht'
  obtain ⟨rn, dargs, cargs, r, a1, a2, a3, a4, a5, a6, a7, a8⟩ := specStep_inv hs
  obtain ⟨s1, s2, s3⟩ := specN_sizes ht
  obtain ⟨p1, p2, p3⟩ := hpre d (by omega)
  refine ⟨t, t', rn, dargs, cargs, r, ht, ht', a1, a2, a3, a4, a5, a6, a7, a8, ?_, ?_, ?_, hsz⟩
  · rw [← p1, a6, ← s1]; simp
  · rw [← p2, a7, ← s2]; simp
  · rw [← p3, a8, ← s3]; simp

/-! ## The loader's forward invariant -/

/-- The one-pass loader, started from `st1` with the empty position map, has
loaded the first `d` expressions and stands at position `p` with state `st`
and position map `pm`. -/
def LoadInv (w : Nat → Nat) (st1 : St) (p d : Nat) (st : St) (pm : Nat → Option Nat) : Prop :=
  p = posOfW w d ∧ ∃ t, specN w st1 d = some t ∧ t.st = st ∧ ∀ a, pm a = pmOf w t.remap a

theorem LoadInv.init (w : Nat → Nat) (st1 : St) : LoadInv w st1 0 0 st1 (fun _ => none) :=
  ⟨rfl, _, rfl, rfl, fun _ => rfl⟩

/-- One iteration of `ck_load`'s loop preserves the invariant. -/
theorem LoadInv.step {w : Nat → Nat} {st1 : St} {p d : Nat} {st st' : St} {pm : Nat → Option Nat}
    {n : Node} {r : Nat} (h : LoadInv w st1 p d st pm) (hn : loadNode w p d pm = some n)
    (hp : pushNode st n = some (st', r)) :
    LoadInv w st1 (p + 1 + hdrVlen (w (3 + p))) (d + 1) st' (pmSet pm p r) := by
  obtain ⟨rfl, t, ht, rfl, hpm⟩ := h
  obtain ⟨_, _, hsz⟩ := specN_sizes ht
  obtain ⟨rn, dn, hs⟩ := specStep_of_load hsz hpm hn hp
  refine ⟨rfl, ⟨t.raw.push rn, t.dense.push dn, st', t.remap.push r⟩, ?_, rfl, fun a => ?_⟩
  · simp only [specN, ht, hs]
  · simp only [pmOf_push, hsz, pmSet, hpm]

/-- A successful run of `loadExprs` ends in the invariant at position `ne`. -/
theorem loadExprs_inv {w : Nat → Nat} {ne : Nat} {st1 st2 : St} {pm2 : Nat → Option Nat} :
    ∀ (fuel p d : Nat) (st : St) (pm : Nat → Option Nat), LoadInv w st1 p d st pm →
      loadExprs w ne fuel p d st pm = some (st2, pm2) → ∃ D, LoadInv w st1 ne D st2 pm2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro p d st pm hinv h
    simp only [loadExprs] at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hp; exact ⟨d, hinv⟩
    · simp at h
  | succ fuel ih =>
    intro p d st pm hinv h
    simp only [loadExprs] at h
    split at h
    · split at h
      · split at h
        · simp at h
        · rename_i n hn
          split at h
          · simp at h
          · rename_i st' r hp
            exact ih _ _ _ _ (hinv.step hn hp) h
      · simp at h
    · split at h
      · rename_i _ hp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hp; exact ⟨d, hinv⟩
      · simp at h

end Vbcf.Proof
