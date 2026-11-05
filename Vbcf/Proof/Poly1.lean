import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval
import Vbcf.Proof.Clause
import Bcf.Poly

/-!
# Vbcf proofs: the Poly family, part 1 — the Lean side

* `plEnc pool L`: the words of a linear form `L : Lin w` on the scratch stack (the constant
  as two words, then per term the atom's id and the coefficient as two words), and its
  injectivity (`plEnc_inj`), which is what makes the word-by-word comparison of
  `r_poly_norm` sound.
* `LinOK pool ts`: every atom is a node of the pool; preserved by `mergeTerms`, `scale`,
  and true of every `Bcf.linF` (`linF_ok`).
* `lin` unfolded one level per operator (`pl_lin_*`), with the children's forms
  expressed through `lin` again (by `linF_stable`).
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf


/-! ## The encoding -/

/-- The two words of a 64-bit value, low word first. -/
def plW (x : Nat) : List Nat := [x % 2 ^ 32, x / 2 ^ 32]

/-- The words of a list of terms. -/
def plTerms {w : Nat} (pool : Pool) : List (Nat × BitVec w) → List Nat
  | [] => []
  | t :: ts => offs pool t.1 :: t.2.toNat % 2 ^ 32 :: t.2.toNat / 2 ^ 32 :: plTerms pool ts

/-- The words of a linear form. -/
def plEnc {w : Nat} (pool : Pool) (L : Lin w) : List Nat := plW L.const.toNat ++ plTerms pool L.terms

/-- Every atom of the terms is a node of the pool. -/
def LinOK {w : Nat} (pool : Pool) (ts : List (Nat × BitVec w)) : Prop := ∀ t ∈ ts, t.1 < pool.size

section enc
variable {w : Nat} {pool : Pool}

@[simp] theorem plW_length (x : Nat) : (plW x).length = 2 := rfl

@[simp] theorem plTerms_nil : plTerms (w := w) pool [] = [] := rfl

theorem plTerms_cons (t : Nat × BitVec w) (ts : List (Nat × BitVec w)) :
    plTerms pool (t :: ts) = offs pool t.1 :: t.2.toNat % 2 ^ 32 :: t.2.toNat / 2 ^ 32 :: plTerms pool ts :=
  rfl

@[simp] theorem plTerms_length (ts : List (Nat × BitVec w)) : (plTerms pool ts).length = 3 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [plTerms_cons, ih]; omega

theorem plTerms_append (A B : List (Nat × BitVec w)) :
    plTerms pool (A ++ B) = plTerms pool A ++ plTerms pool B := by
  induction A with
  | nil => rfl
  | cons t ts ih => simp [plTerms_cons, ih]

@[simp] theorem plEnc_length (L : Lin w) : (plEnc pool L).length = 2 + 3 * L.terms.length := by
  simp [plEnc]

theorem LinOK.nil : LinOK (w := w) pool [] := fun _ h => by simp at h

theorem LinOK.cons {t : Nat × BitVec w} {ts : List (Nat × BitVec w)} (ht : t.1 < pool.size)
    (hts : LinOK pool ts) : LinOK pool (t :: ts) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ht
  · exact hts x hx

theorem LinOK.tail {t : Nat × BitVec w} {ts : List (Nat × BitVec w)} (h : LinOK pool (t :: ts)) :
    LinOK pool ts := fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem LinOK.head {t : Nat × BitVec w} {ts : List (Nat × BitVec w)} (h : LinOK pool (t :: ts)) :
    t.1 < pool.size := h t (List.mem_cons_self ..)

theorem LinOK.append {A B : List (Nat × BitVec w)} (hA : LinOK pool A) (hB : LinOK pool B) :
    LinOK pool (A ++ B) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hA x hx
  · exact hB x hx

theorem LinOK.drop {A : List (Nat × BitVec w)} (hA : LinOK pool A) (k : Nat) :
    LinOK pool (A.drop k) := fun x hx => hA x (List.mem_of_mem_drop hx)

/-- A 64-bit number from its two words. -/
theorem pl_split (x : Nat) : x % 2 ^ 32 + 2 ^ 32 * (x / 2 ^ 32) = x := Nat.mod_add_div x _

theorem plTerms_inj (hw : w ≤ 64) :
    ∀ {A B : List (Nat × BitVec w)}, LinOK pool A → LinOK pool B →
      plTerms pool A = plTerms pool B → A = B
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [plTerms_cons] at h
  | _ :: _, [], _, _, h => by simp [plTerms_cons] at h
  | (a, x) :: A, (b, y) :: B, hA, hB, h => by
    simp only [plTerms_cons, List.cons.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hab : a = b := offs_inj (Nat.le_of_lt hA.head) (Nat.le_of_lt hB.head) h1
    have hxy : x = y := by
      apply BitVec.eq_of_toNat_eq
      rw [← pl_split x.toNat, ← pl_split y.toNat, h2, h3]
    rw [hab, hxy, plTerms_inj hw hA.tail hB.tail h4]

/-- The encoding is injective on forms whose atoms are nodes. -/
theorem plEnc_inj (hw : w ≤ 64) {L M : Lin w} (hL : LinOK pool L.terms) (hM : LinOK pool M.terms)
    (h : plEnc pool L = plEnc pool M) : L = M := by
  obtain ⟨lc, lt⟩ := L
  obtain ⟨mc, mt⟩ := M
  simp only [plEnc, plW, List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hc : lc = mc := by
    apply BitVec.eq_of_toNat_eq
    rw [← pl_split lc.toNat, ← pl_split mc.toNat, h1, h2]
  have ht := plTerms_inj hw hL hM h3
  subst hc; subst ht; rfl

end enc

/-! ## `mergeTerms` -/

section merge
variable {w : Nat}

theorem pl_merge_nil_left (ys : List (Nat × BitVec w)) : Lin.mergeTerms [] ys = ys := by
  simp [Lin.mergeTerms]

theorem pl_merge_nil_right (xs : List (Nat × BitVec w)) : Lin.mergeTerms xs [] = xs := by
  cases xs <;> simp [Lin.mergeTerms]

theorem pl_merge_lt {a b : Nat} {c d : BitVec w} {xs ys : List (Nat × BitVec w)} (h : a < b) :
    Lin.mergeTerms ((a, c) :: xs) ((b, d) :: ys) = (a, c) :: Lin.mergeTerms xs ((b, d) :: ys) := by
  rw [Lin.mergeTerms]; simp [h]

theorem pl_merge_gt {a b : Nat} {c d : BitVec w} {xs ys : List (Nat × BitVec w)} (h : b < a) :
    Lin.mergeTerms ((a, c) :: xs) ((b, d) :: ys) = (b, d) :: Lin.mergeTerms ((a, c) :: xs) ys := by
  rw [Lin.mergeTerms]; simp [h, Nat.not_lt.mpr (Nat.le_of_lt h)]

theorem pl_merge_eq {a : Nat} {c d : BitVec w} {xs ys : List (Nat × BitVec w)} :
    Lin.mergeTerms ((a, c) :: xs) ((a, d) :: ys) =
      if c + d = 0 then Lin.mergeTerms xs ys else (a, c + d) :: Lin.mergeTerms xs ys := by
  rw [Lin.mergeTerms]; simp

/-- When one side is exhausted the rest is the other side. -/
theorem pl_merge_rest {xs ys : List (Nat × BitVec w)} (h : xs = [] ∨ ys = []) :
    Lin.mergeTerms xs ys = xs ++ ys := by
  rcases h with rfl | rfl
  · simp [pl_merge_nil_left]
  · simp [pl_merge_nil_right]

theorem pl_merge_ok {pool : Pool} :
    ∀ (n : Nat) (xs ys : List (Nat × BitVec w)), xs.length + ys.length = n →
      LinOK pool xs → LinOK pool ys → LinOK pool (Lin.mergeTerms xs ys) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs ys hn hx hy
    match xs, ys with
    | [], ys => rw [pl_merge_nil_left]; exact hy
    | x :: xs, [] => rw [pl_merge_nil_right]; exact hx
    | (a, c) :: xs, (b, d) :: ys =>
      rcases Nat.lt_trichotomy a b with h | rfl | h
      · rw [pl_merge_lt h]
        exact LinOK.cons hx.head (ih _ (by simp at hn ⊢; omega) _ _ rfl hx.tail hy)
      · rw [pl_merge_eq]
        split
        · exact ih _ (by simp at hn ⊢; omega) _ _ rfl hx.tail hy.tail
        · exact LinOK.cons hx.head (ih _ (by simp at hn ⊢; omega) _ _ rfl hx.tail hy.tail)
      · rw [pl_merge_gt h]
        exact LinOK.cons hy.head (ih _ (by simp at hn ⊢; omega) _ _ rfl hx hy.tail)

theorem LinOK.merge {pool : Pool} {xs ys : List (Nat × BitVec w)} (hx : LinOK pool xs)
    (hy : LinOK pool ys) : LinOK pool (Lin.mergeTerms xs ys) := pl_merge_ok _ xs ys rfl hx hy

theorem LinOK.scale {pool : Pool} {k : BitVec w} {ts : List (Nat × BitVec w)} (h : LinOK pool ts) :
    LinOK pool ((ts.map (fun t => (t.1, k * t.2))).filter (fun t => t.2 ≠ 0)) := by
  intro x hx
  obtain ⟨hx, -⟩ := List.mem_filter.mp hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact h t ht

end merge

/-! ## `Bcf.linF` -/

section linf
variable {pool : Pool} {w : Nat}

theorem LinOK.add {p q : Lin w} (hp : LinOK pool p.terms) (hq : LinOK pool q.terms) :
    LinOK pool (Lin.add p q).terms := LinOK.merge hp hq

theorem LinOK.scaleL {k : BitVec w} {p : Lin w} (hp : LinOK pool p.terms) :
    LinOK pool (Lin.scale k p).terms := LinOK.scale hp

theorem LinOK.negL {p : Lin w} (hp : LinOK pool p.terms) : LinOK pool (Lin.neg p).terms :=
  LinOK.scale hp

theorem LinOK.atomL {a : Nat} (ha : a < pool.size) : LinOK pool (Lin.atom (w := w) a).terms :=
  LinOK.cons ha LinOK.nil

theorem LinOK.constL (x : BitVec w) : LinOK pool (Lin.ofConst x).terms := LinOK.nil

theorem LinOK.foldr {ps : List (Lin w)} (h : ∀ p ∈ ps, LinOK pool p.terms) :
    LinOK pool (ps.foldr Lin.add (Lin.ofConst 0)).terms := by
  induction ps with
  | nil => exact LinOK.nil
  | cons p ps ih =>
    simp only [List.foldr_cons]
    exact LinOK.add (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

/-- Every atom of `Bcf.linF` is a node, when every node's arguments are nodes. -/
theorem linF_ok (hargs : ∀ (i : Nat) (n : Node), pool[i]? = some n → ∀ a ∈ n.args, a < pool.size) :
    ∀ (f i : Nat), i < pool.size → LinOK pool (Bcf.linF pool w f i).terms := by
  intro f
  induction f with
  | zero => intro i hi; exact LinOK.atomL hi
  | succ f ih =>
    intro i hi
    have hat : LinOK pool (Lin.atom (w := w) i).terms := LinOK.atomL hi
    simp only [Bcf.linF]
    split
    · split
      · exact LinOK.constL _
      · exact hat
    · rename_i w' args hn
      split
      · apply LinOK.foldr
        intro p hp
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
        have hal : a < pool.size := hargs i _ hn a (by simpa using ha)
        split
        · exact ih a hal
        · exact LinOK.atomL hal
      · exact hat
    · rename_i w' args hn
      split
      · rename_i a b hab
        have ha : a < pool.size := hargs i _ hn a (by simp [← Array.mem_toList_iff, hab])
        have hb : b < pool.size := hargs i _ hn b (by simp [← Array.mem_toList_iff, hab])
        split
        · exact LinOK.add (ih a ha) (LinOK.negL (ih b hb))
        · exact hat
      · exact hat
    · rename_i w' args hn
      split
      · rename_i a hab
        have ha : a < pool.size := hargs i _ hn a (by simp [← Array.mem_toList_iff, hab])
        split
        · exact LinOK.negL (ih a ha)
        · exact hat
      · exact hat
    · rename_i w' args hn
      split
      · rename_i a b hab
        have ha : a < pool.size := hargs i _ hn a (by simp [← Array.mem_toList_iff, hab])
        have hb : b < pool.size := hargs i _ hn b (by simp [← Array.mem_toList_iff, hab])
        split
        · split
          · exact LinOK.scaleL (ih b hb)
          · exact LinOK.scaleL (ih a ha)
          · exact hat
        · exact hat
      · exact hat
    · exact hat

theorem lin_ok (hargs : ∀ (i : Nat) (n : Node), pool[i]? = some n → ∀ a ∈ n.args, a < pool.size) {i : Nat}
    (hi : i < pool.size) : LinOK pool (Bcf.lin pool w i).terms := linF_ok hargs _ i hi

/-- A child's form inside `Bcf.linF … (i + 1) i` is its own `lin`. -/
theorem pl_child {a i : Nat} (h : a < i) : Bcf.linF pool w i a = Bcf.lin pool w a :=
  linF_stable pool w a i (a + 1) h (Nat.lt_succ_self a)

theorem pl_lin_val {i w' v : Nat} {args : Array Nat} (hn : pool[i]? = some ⟨.bvVal w' v, args⟩) :
    Bcf.lin pool w i = if w' = w then Lin.ofConst (BitVec.ofNat w v) else Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]

theorem pl_lin_add {i w' : Nat} {args : Array Nat} (hn : pool[i]? = some ⟨.bvAdd w', args⟩) :
    Bcf.lin pool w i = if w' = w then
      (args.toList.map (fun a => if a < i then Bcf.lin pool w a else Lin.atom a)).foldr Lin.add
        (Lin.ofConst 0) else Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  split
  · congr 1
    apply List.map_congr_left
    intro a _
    split
    · rename_i h; rw [pl_child h]
    · rfl
  · rfl

theorem pl_lin_sub {i w' a b : Nat} (hn : pool[i]? = some ⟨.bvSub w', #[a, b]⟩) :
    Bcf.lin pool w i = if w' = w ∧ a < i ∧ b < i then
      Lin.add (Bcf.lin pool w a) (Lin.neg (Bcf.lin pool w b)) else Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  try simp only [List.toList_toArray]
  split
  · rename_i h; rw [pl_child h.2.1, pl_child h.2.2]
  · rfl

theorem pl_lin_neg {i w' a : Nat} (hn : pool[i]? = some ⟨.bvNeg w', #[a]⟩) :
    Bcf.lin pool w i = if w' = w ∧ a < i then Lin.neg (Bcf.lin pool w a) else Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  try simp only [List.toList_toArray]
  split
  · rename_i h; rw [pl_child h.2]
  · rfl

theorem pl_lin_mul_no {i w' a b : Nat} (hn : pool[i]? = some ⟨.bvMul w', #[a, b]⟩)
    (hc : ¬ (w' = w ∧ a < i ∧ b < i)) : Bcf.lin pool w i = Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  try simp only [List.toList_toArray]
  rw [ite_eq_right hc]

theorem pl_lin_mul_a {i w' a b : Nat} {k : BitVec w} (hn : pool[i]? = some ⟨.bvMul w', #[a, b]⟩)
    (hc : w' = w ∧ a < i ∧ b < i) (hk : Bcf.litVal pool w a = some k) :
    Bcf.lin pool w i = Lin.scale k (Bcf.lin pool w b) := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  try simp only [List.toList_toArray]
  rw [ite_eq_left hc, hk, pl_child hc.2.2]

theorem pl_lin_mul_b {i w' a b : Nat} {k : BitVec w} (hn : pool[i]? = some ⟨.bvMul w', #[a, b]⟩)
    (hc : w' = w ∧ a < i ∧ b < i) (ha : Bcf.litVal pool w a = none) (hk : Bcf.litVal pool w b = some k) :
    Bcf.lin pool w i = Lin.scale k (Bcf.lin pool w a) := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  try simp only [List.toList_toArray]
  rw [ite_eq_left hc, ha, hk, pl_child hc.2.1]

theorem pl_lin_mul_none {i w' a b : Nat} (hn : pool[i]? = some ⟨.bvMul w', #[a, b]⟩)
    (ha : Bcf.litVal pool w a = none) (hb : Bcf.litVal pool w b = none) :
    Bcf.lin pool w i = Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  try simp only [List.toList_toArray]
  rw [ha, hb]
  split <;> rfl

/-- A multiplication with an arity other than two. -/
theorem pl_lin_mul_other {i w' : Nat} {args : Array Nat}
    (hn : pool[i]? = some ⟨.bvMul w', args⟩) (hs : args.size ≠ 2) : Bcf.lin pool w i = Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  split
  · rename_i a b hab
    have := congrArg List.length hab
    simp at this; omega
  · rfl

theorem pl_lin_sub_other {i w' : Nat} {args : Array Nat}
    (hn : pool[i]? = some ⟨.bvSub w', args⟩) (hs : args.size ≠ 2) : Bcf.lin pool w i = Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  split
  · rename_i a b hab
    have := congrArg List.length hab
    simp at this; omega
  · rfl

theorem pl_lin_neg_other {i w' : Nat} {args : Array Nat}
    (hn : pool[i]? = some ⟨.bvNeg w', args⟩) (hs : args.size ≠ 1) : Bcf.lin pool w i = Lin.atom i := by
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  split
  · rename_i a hab
    have := congrArg List.length hab
    simp at this; omega
  · rfl

/-- Any other operator is an atom. -/
theorem pl_lin_other {i : Nat} {n : Node} (hn : pool[i]? = some n)
    (h8 : opC n.op ≠ 0x08) (h0 : opC n.op ≠ 0x00) (h10 : opC n.op ≠ 0x10) (h80 : opC n.op ≠ 0x80)
    (h20 : opC n.op ≠ 0x20) : Bcf.lin pool w i = Lin.atom i := by
  obtain ⟨op, args⟩ := n
  rw [Bcf.lin_unfold]; simp only [Bcf.linF, hn]
  cases op <;> simp_all [opC]

end linf

end Vbcf.Proof
