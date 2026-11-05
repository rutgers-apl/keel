import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.GoalSpecs
import Vbcf.Proof.Builders
import Vbcf.Proof.DecodeEnc

/-!
# Vbcf proofs: `ck_goal`, part 1 (pure lemmas)

No C semantics here.

* bit lemmas for the header masks the C uses (`& 0xffff00ff`);
* `GLocal` is monotone in the matching and the renaming (`GLocal.mono`);
* the three ways a matched pair is checked, as `GLocal` introduction rules:
  a variable (`glocal_var`), a bit-vector literal (`glocal_val`), anything else
  (`glocal_inner`);
* `RInv0` after a change that keeps the represented pool (`RInv0.goalFrame`).
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC
set_option autoImplicit false

/-! ## Bits -/

theorem goal_and_varmask {x : Nat} (hx : x < 2 ^ 32) :
    x &&& 0xffff00ff = x % 256 + x / 65536 * 65536 := by
  have hM : (0xffff00ff : Nat) = 2 ^ 16 * (2 ^ 16 - 1) + (2 ^ 8 - 1) := by decide
  have hy : x % 256 + x / 65536 * 65536 = 2 ^ 16 * (x / 2 ^ 16) + x % 2 ^ 8 := by
    simp only [Nat.reducePow]; omega
  rw [hM, hy]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (by decide),
    Nat.testBit_two_pow_mul_add _ (by omega), Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h8 : i < 8
  · have : i < 16 := by omega
    simp [h8, this]
  · by_cases h16 : i < 16
    · simp [h8, h16]
    · by_cases h32 : i < 32
      · have : i - 16 < 16 := by omega
        have e : i - 16 + 16 = i := by omega
        simp [h16, this, e]
      · have : ¬ i - 16 < 16 := by omega
        have e : i - 16 + 16 = i := by omega
        have hf : x.testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
        simp [h16, this, e, hf]

theorem goal_bv_varmask (x : BitVec 32) :
    (x &&& 0xffff00ff#32).toNat = x.toNat % 256 + x.toNat / 65536 * 65536 := by
  rw [BitVec.toNat_and]
  exact goal_and_varmask x.isLt

/-! ## The arena node, with the fields as arithmetic -/

theorem arenaNode_eq (w : Nat → Nat) (q : Nat) :
    arenaNode w q = decodeNode q (w q % 256) (w q / 256 % 256) (w q / 65536 % 65536)
      ((List.range (w q / 256 % 256)).map (fun k => w (q + 1 + k))).toArray := by
  unfold arenaNode
  simp only [LoadSpec.and_ff, LoadSpec.shr8, LoadSpec.shr16, LoadSpec.and_ffff]

/-! ## `GLocal` -/

/-- The variable identity of a variable operator. -/
def gvid : Op → Nat
  | .bvVar _ d => d
  | .boolVar d => d
  | _ => 0

theorem GLocal.mono {pool : Pool} {w : Nat → Nat} {μ μ' σ σ' : Nat → Option Nat} {q i : Nat}
    (h : GLocal pool w μ σ q i) (hμ : ∀ t j, μ t = some j → μ' t = some j)
    (hσ : ∀ d t, σ d = some t → σ' d = some t) : GLocal pool w μ' σ' q i := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  rcases h with ⟨wd, d, h1, h2, h3, h4⟩ | ⟨d, h1, h2, h3, h4⟩ | ⟨h1, an, h2, h3, h4, h5⟩
  · exact Or.inl ⟨wd, d, h1, h2, h3, hσ _ _ h4⟩
  · exact Or.inr (Or.inl ⟨d, h1, h2, h3, hσ _ _ h4⟩)
  · refine Or.inr (Or.inr ⟨h1, an, h2, h3, h4, fun k hk => ?_⟩)
    obtain ⟨a1, a2⟩ := h5 k hk
    exact ⟨a1, hμ _ _ a2⟩

/-- A variable: the arena header is the pool header with the arity byte cleared. -/
theorem glocal_var {pool : Pool} {w : Nat → Nat} {μ σ : Nat → Option Nat} {q i : Nat}
    {posOf : Nat → Nat} {n : Node} (hn : pool[i]? = some n) (hf : Fits posOf n)
    (hv : opC n.op = 0x18 ∨ opC n.op = 0x19) (hargs : n.args = #[])
    (hw : w q = hdrW n % 256 + hdrW n / 65536 * 65536) (hσ : σ (gvid n.op) = some q) :
    GLocal pool w μ σ q i := by
  have hp := hdrW_params_lt hf
  have hlt := hdrW_lt hf
  have hA : arenaNode w q = some ⟨reidx n.op q, #[]⟩ := by
    rw [arenaNode_eq]
    have e1 : w q % 256 = hdrW n % 256 := by rw [hw]; omega
    have e2 : w q / 256 % 256 = 0 := by rw [hw]; omega
    have e3 : w q / 65536 % 65536 = hdrW n / 65536 := by rw [hw]; omega
    rw [e1, e2, e3]
    exact decodeNode_hdrW_var hf hv q 0 _
  refine ⟨n, hn, ?_⟩
  rcases hv with hv | hv
  · obtain ⟨wd, d, e⟩ := opC_bvVar_iff.mp hv
    rw [e] at hA hσ
    exact Or.inl ⟨wd, d, e, hargs, hA, hσ⟩
  · obtain ⟨d, e⟩ := opC_boolVar_iff.mp hv
    rw [e] at hA hσ
    exact Or.inr (Or.inl ⟨d, e, hargs, hA, hσ⟩)

/-- The arena's argument words of node `q`, as the decoder sees them. -/
theorem arena_words_eq {w : Nat → Nat} {q L : Nat} {ws : List Nat} (hL : ws.length = L)
    (h : ∀ k, k < L → ws[k]? = some (w (q + 1 + k))) :
    (List.range L).map (fun k => w (q + 1 + k)) = ws := by
  apply List.ext_getElem
  · simp [hL]
  · intro k h1 h2
    have := h k (by simpa using h1)
    rw [List.getElem?_eq_getElem h2] at this
    simp only [Option.some.injEq] at this
    simp [this]

/-- A bit-vector literal: the same header and the same value words. -/
theorem glocal_val {pool : Pool} {w : Nat → Nat} {μ σ : Nat → Option Nat} {q i : Nat}
    {posOf : Nat → Nat} {n : Node} {argTys : List Bcf.Ty} {t : Bcf.Ty} (hn : pool[i]? = some n)
    (hf : Fits posOf n) (ht : n.op.resultTy argTys = some t) (hv : opC n.op = 0x08)
    (hargs : n.args = #[]) (hw : w q = hdrW n)
    (hws : ∀ k, k < tailLen n → (tailW posOf (offs pool) n)[k]? = some (w (q + 1 + k))) :
    GLocal pool w μ σ q i := by
  have hp := hdrW_params_lt hf
  have hA : arenaNode w q = some ⟨n.op, #[]⟩ := by
    rw [arenaNode_eq, hw, hdrW_len hf, Nat.mod_eq_of_lt hp,
      arena_words_eq (tailW_length posOf (offs pool) n) hws, ← hdrW_len hf]
    exact decodeNode_hdrW_bvVal hf ht hv _ q
  refine ⟨n, hn, Or.inr (Or.inr ⟨?_, _, hA, rfl, by simp [hargs], fun k hk => ?_⟩)⟩
  · obtain ⟨_, _, e⟩ := opC_bvVal_iff.mp hv
    rw [e]; rfl
  · rw [hargs] at hk; simp at hk

/-- Any other node: the same header, and each argument word names an earlier
arena node matched with the corresponding argument. -/
theorem glocal_inner {pool : Pool} {w : Nat → Nat} {μ σ : Nat → Option Nat} {q i : Nat}
    {posOf : Nat → Nat} {n : Node} (hn : pool[i]? = some n) (hf : Fits posOf n)
    (h18 : opC n.op ≠ 0x18) (h19 : opC n.op ≠ 0x19) (h08 : opC n.op ≠ 0x08)
    (hleaf : IsLeaf n.op → n.args = #[]) (hw : w q = hdrW n)
    (hargs : ∀ k (hk : k < n.args.size), w (q + 1 + k) < q ∧ μ (w (q + 1 + k)) = some n.args[k]) :
    GLocal pool w μ σ q i := by
  have hp := hdrW_params_lt hf
  have hnv : isVarOp n.op = false := by
    cases hop : n.op <;> simp_all [isVarOp, opC]
  refine ⟨n, hn, Or.inr (Or.inr ⟨hnv, ?_⟩)⟩
  by_cases hl : IsLeaf n.op
  · have h09 : opC n.op = 0x09 := by
      rcases isLeaf_iff.mp hl with ⟨_, _, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;>
        rw [e] at h18 h19 h08 ⊢ <;> simp [opC] at h18 h19 h08 ⊢
    have hA : arenaNode w q = some ⟨n.op, #[]⟩ := by
      rw [arenaNode_eq, hw, Nat.mod_eq_of_lt hp]
      exact decodeNode_hdrW_boolVal hf h09 q _ _
    have ha := hleaf hl
    refine ⟨_, hA, rfl, by simp [ha], fun k hk => ?_⟩
    rw [ha] at hk; simp at hk
  · have hlen : hdrW n / 256 % 256 = n.args.size := by
      rw [hdrW_len hf, tailLen_of_not_leaf hl]
    have hA := decodeNode_hdrW_inner hf hl q (hdrW n / 256 % 256)
      ((List.range (hdrW n / 256 % 256)).map (fun k => w (q + 1 + k))).toArray
    rw [← Nat.mod_eq_of_lt hp, ← hw] at hA
    rw [← arenaNode_eq] at hA
    refine ⟨_, hA, rfl, by simp [hw, hlen], fun k hk => ?_⟩
    have hk' : k < w q / 256 % 256 := by rw [hw]; omega
    have e : ((List.range (w q / 256 % 256)).map (fun k => w (q + 1 + k))).toArray[k]! =
        w (q + 1 + k) := by
      simp [hk']
    simp only [e]
    exact hargs k hk

end Vbcf.Proof
