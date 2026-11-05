import EmbC.Clight.Proof.Priv

/-!
# Injectivity of the identifier encoding on byte strings
-/

expose_private CCLib.Positive CC appendBit nthBit appendCharPos

namespace EmbC.Clight.Proof

open CC

theorem appendBit_inj {b b' : Bool} {p p' : Positive}
    (h : Priv.appendBit b p = Priv.appendBit b' p') : b = b' ∧ p = p' := by
  cases b <;> cases b' <;> simp_all [Priv.appendBit]

theorem nthBit_eq (n i : Nat) : Priv.nthBit n i = n.testBit i := by
  simp only [Priv.nthBit, Nat.testBit]
  rw [Nat.and_comm]
  have : (1 &&& n >>> i) < 2 := by
    have := Nat.and_le_left (n := 1) (m := n >>> i); omega
  cases h : (1 &&& n >>> i) with
  | zero => simp
  | succ k => cases k with
    | zero => simp
    | succ k => omega

theorem appendCharPos_inj {c c' : Char} {p p' : Positive} (hc : c.toNat < 256)
    (hc' : c'.toNat < 256) (h : Priv.appendCharPos c p = Priv.appendCharPos c' p') :
    c = c' ∧ p = p' := by
  simp only [Priv.appendCharPos, Positive.xI.injEq] at h
  obtain ⟨h0, h⟩ := appendBit_inj h
  obtain ⟨h1, h⟩ := appendBit_inj h
  obtain ⟨h2, h⟩ := appendBit_inj h
  obtain ⟨h3, h⟩ := appendBit_inj h
  obtain ⟨h4, h⟩ := appendBit_inj h
  obtain ⟨h5, h⟩ := appendBit_inj h
  obtain ⟨h6, h⟩ := appendBit_inj h
  obtain ⟨h7, h⟩ := appendBit_inj h
  refine ⟨?_, h⟩
  apply Char.ext
  apply UInt32.toNat_inj.mp
  show c.toNat = c'.toNat
  apply Nat.eq_of_testBit_eq
  intro i
  rw [nthBit_eq, nthBit_eq] at h0 h1 h2 h3 h4 h5 h6 h7
  by_cases hi : i < 8
  · match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
  · have hp : 256 ≤ 2 ^ i := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) (show 8 ≤ i by omega)
      simpa using this
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-- All characters are bytes. -/
def ByteString (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 256

theorem identOfList_inj : ∀ (l l' : List Char), (∀ c ∈ l, c.toNat < 256) →
    (∀ c ∈ l', c.toNat < 256) →
    l.foldr Priv.appendCharPos Positive.xH = l'.foldr Priv.appendCharPos Positive.xH → l = l'
  | [], [], _, _, _ => rfl
  | [], c :: l, _, _, h => by
    simp only [List.foldr, Priv.appendCharPos] at h; cases h
  | c :: l, [], _, _, h => by
    simp only [List.foldr, Priv.appendCharPos] at h; cases h
  | c :: l, c' :: l', hl, hl', h => by
    simp only [List.foldr] at h
    obtain ⟨rfl, h2⟩ := appendCharPos_inj (hl c (by simp)) (hl' c' (by simp)) h
    rw [identOfList_inj l l' (fun x hx => hl x (by simp [hx])) (fun x hx => hl' x (by simp [hx])) h2]

theorem identOfString_inj {s s' : String} (hs : ByteString s) (hs' : ByteString s')
    (h : identOfString s = identOfString s') : s = s' := by
  have := identOfList_inj s.toList s'.toList hs hs' h
  exact String.toList_inj.mp this

end EmbC.Clight.Proof
