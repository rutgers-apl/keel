import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Goal1

/-!
# Vbcf proofs: `ck_goal`, part 2 (the sweep invariant, pure)

`ck_goal` keeps two scratch tables at the pool tail, from `B = plen`:

* `mark[t] = pool[B + t]` (`t ≤ G`, `G` the arena goal position): 0, or one more than
  the C id of the pool node arena node `t` must match;
* `vmap[p] = pool[B + G + 1 + p]` (`p < NE`, `NE = nexpr`): 0, or one more than the arena
  position matched with the proof variable at input position `p`.

The ghost state is a matching `μ` (arena position ↦ pool index) and `σP` (input
position ↦ arena position); `SweepOK … qN` says the tables encode them and every marked
position `≥ qN` is checked (`GLocal`).  The C sweeps `qN` from `G + 1` down to `0`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC
set_option autoImplicit false

/-- `mark[t]` for the matching `μ`. -/
def encM (pool : Pool) (μ : Nat → Option Nat) (t : Nat) : Nat :=
  match μ t with
  | none => 0
  | some i => offs pool i + 1

/-- `vmap[p]` for `σP`. -/
def encS (σP : Nat → Option Nat) (p : Nat) : Nat :=
  match σP p with
  | none => 0
  | some t => t + 1

/-- Point update. -/
def updF (f : Nat → Option Nat) (x v : Nat) : Nat → Option Nat := fun y =>
  if y = x then some v else f y

/-- The renaming of pool variables: through their input positions. -/
def sigOf (posOf : Nat → Nat) (σP : Nat → Option Nat) : Nat → Option Nat := fun d => σP (posOf d)

structure SweepOK (pool : Pool) (gws : Array (BitVec 32)) (posOf : Nat → Nat) (g B G NE : Nat)
    (cells : Array EmbC.Val) (μ σP : Nat → Option Nat) (qN : Nat) : Prop where
  mark : ∀ t, t ≤ G → U cells (B + t) (encM pool μ t)
  vmap : ∀ p, p < NE → U cells (B + G + 1 + p) (encS σP p)
  mdom : ∀ t i, μ t = some i → t ≤ G ∧ i < pool.size ∧ t + 1 + hdrVlen (wordFn gws t) ≤ gws.size
  sdom : ∀ p t, σP p = some t → t ≤ G
  root : μ G = some g
  done : ∀ t i, qN ≤ t → μ t = some i → GLocal pool (wordFn gws) μ (sigOf posOf σP) t i

/-! ## Cells -/

theorem U_set_self {cells : Array EmbC.Val} {i w : Nat} {x : BitVec 32} (hi : i < cells.size)
    (hx : x = BitVec.ofNat 32 w) : U (cells.setIfInBounds i (.u32 x)) i w := by
  unfold U; simp [hi, hx]

theorem U_set_ne {cells : Array EmbC.Val} {i j w : Nat} {x : BitVec 32} (h : U cells j w)
    (hne : i ≠ j) : U (cells.setIfInBounds i (.u32 x)) j w := by
  unfold U at h ⊢; simp [hne, h]

theorem U_lt_size {cells : Array EmbC.Val} {i w : Nat} (h : U cells i w) : i < cells.size :=
  lt_size_of_getElem? h

/-! ## Start and finish -/

section
variable {pool : Pool} {gws : Array (BitVec 32)} {posOf : Nat → Nat} {g B G NE : Nat}

/-- After the tables are zeroed and the root is marked. -/
theorem SweepOK.init {cells : Array EmbC.Val} (hg : g < pool.size)
    (hfit : G + 1 + hdrVlen (wordFn gws G) ≤ gws.size)
    (hz : ∀ t, t < G + 1 + NE → t ≠ G → U cells (B + t) 0)
    (hr : U cells (B + G) (offs pool g + 1)) :
    SweepOK pool gws posOf g B G NE cells (fun t => if t = G then some g else none)
      (fun _ => none) (G + 1) where
  mark := by
    intro t ht
    by_cases e : t = G
    · subst e; simp [encM, hr]
    · simp only [encM, e, ↓reduceIte]; exact hz t (by omega) e
  vmap := by
    intro p hp
    have := hz (G + 1 + p) (by omega) (by omega)
    rw [show B + (G + 1 + p) = B + G + 1 + p by omega] at this
    simpa [encS] using this
  mdom := by
    intro t i h
    by_cases e : t = G
    · subst e; simp at h; subst h; exact ⟨Nat.le_refl _, hg, hfit⟩
    · simp [e] at h
  sdom := by intro p t h; simp at h
  root := by simp
  done := by
    intro t i ht h
    have : t ≠ G := by omega
    simp [this] at h

/-- At the end of the sweep every marked position is checked. -/
theorem SweepOK.goalOK {cells : Array EmbC.Val} {μ σP : Nat → Option Nat}
    (h : SweepOK pool gws posOf g B G NE cells μ σP 0) : GoalOK pool (wordFn gws) g G :=
  ⟨μ, sigOf posOf σP, h.root, fun t i hm => h.done t i (Nat.zero_le _) hm⟩

/-! ## One position -/

/-- An unmarked position needs no check. -/
theorem SweepOK.skip {cells : Array EmbC.Val} {μ σP : Nat → Option Nat} {Q : Nat}
    (h : SweepOK pool gws posOf g B G NE cells μ σP (Q + 1)) (hm : μ Q = none) :
    SweepOK pool gws posOf g B G NE cells μ σP Q :=
  { h with
    done := by
      intro t i ht hti
      rcases Nat.lt_or_ge t (Q + 1) with h1 | h1
      · have : t = Q := by omega
        subst this; rw [hm] at hti; cases hti
      · exact h.done t i h1 hti }

/-- A checked position whose matching and renaming need nothing new. -/
theorem SweepOK.step {cells : Array EmbC.Val} {μ σP : Nat → Option Nat} {Q i : Nat}
    (h : SweepOK pool gws posOf g B G NE cells μ σP (Q + 1)) (hm : μ Q = some i)
    (hl : GLocal pool (wordFn gws) μ (sigOf posOf σP) Q i) :
    SweepOK pool gws posOf g B G NE cells μ σP Q :=
  { h with
    done := by
      intro t j ht htj
      rcases Nat.lt_or_ge t (Q + 1) with h1 | h1
      · have : t = Q := by omega
        subst this; rw [hm] at htj; cases htj; exact hl
      · exact h.done t j h1 htj }

/-- A variable position: `vmap[p] = Q + 1` is written (it was 0). -/
theorem SweepOK.var {cells : Array EmbC.Val} {μ σP : Nat → Option Nat} {Q i p : Nat}
    {n : Node} (h : SweepOK pool gws posOf g B G NE cells μ σP (Q + 1)) (hm : μ Q = some i)
    (hn : pool[i]? = some n) (hf : Fits posOf n) (hv : opC n.op = 0x18 ∨ opC n.op = 0x19)
    (hargs : n.args = #[])
    (hw : wordFn gws Q = hdrW n % 256 + hdrW n / 65536 * 65536)
    (hp : posOf (gvid n.op) = p) (hpl : p < NE) (hs : σP p = none) :
    SweepOK pool gws posOf g B G NE
      (cells.setIfInBounds (B + G + 1 + p) (.u32 (BitVec.ofNat 32 (Q + 1)))) μ (updF σP p Q) Q := by
  have hQ := (h.mdom Q i hm).1
  have hcell := h.vmap p hpl
  have hσ : ∀ d t, sigOf posOf σP d = some t → sigOf posOf (updF σP p Q) d = some t := by
    intro d t hd
    unfold sigOf updF at *
    by_cases e : posOf d = p
    · rw [e, hs] at hd; cases hd
    · simp [e, hd]
  refine
    { mark := fun t ht => U_set_ne (h.mark t ht) (by omega)
      vmap := ?_
      mdom := h.mdom
      sdom := ?_
      root := h.root
      done := ?_ }
  · intro p' hp'
    by_cases e : p' = p
    · subst e
      exact U_set_self (U_lt_size hcell) (by simp [encS, updF])
    · have : encS (updF σP p Q) p' = encS σP p' := by simp [encS, updF, e]
      rw [this]
      exact U_set_ne (h.vmap p' hp') (by omega)
  · intro p' t ht
    unfold updF at ht
    by_cases e : p' = p
    · simp [e] at ht; omega
    · simp [e] at ht; exact h.sdom p' t ht
  · intro t j ht htj
    rcases Nat.lt_or_ge t (Q + 1) with h1 | h1
    · have : t = Q := by omega
      subst this; rw [hm] at htj; cases htj
      refine glocal_var hn hf hv hargs hw ?_
      simp [sigOf, updF, hp]
    · exact (h.done t j h1 htj).mono (fun _ _ e => e) hσ

end

/-! ## The argument loop

`ArgsOK … μ' k`: the first `k` arguments of pool node `n` (matched at arena position `Q`)
are arena positions below `Q` whose marks are the node's arguments. -/

section
variable {pool : Pool} {gws : Array (BitVec 32)} {posOf : Nat → Nat} {g B G NE : Nat}

structure ArgsOK (pool : Pool) (gws : Array (BitVec 32)) (posOf : Nat → Nat) (g B G NE : Nat)
    (cells : Array EmbC.Val) (μ σP : Nat → Option Nat) (Q i : Nat) (n : Node) (k : Nat) : Prop where
  sw : SweepOK pool gws posOf g B G NE cells μ σP (Q + 1)
  self : μ Q = some i
  args : ∀ k' (_hk : k' < k) (hk' : k' < n.args.size),
    wordFn gws (Q + 1 + k') < Q ∧ μ (wordFn gws (Q + 1 + k')) = some n.args[k']

/-- An argument whose position is already marked with the same node. -/
theorem ArgsOK.same {cells : Array EmbC.Val} {μ σP : Nat → Option Nat} {Q i k : Nat} {n : Node}
    (h : ArgsOK pool gws posOf g B G NE cells μ σP Q i n k) (hk : k < n.args.size)
    (ha : wordFn gws (Q + 1 + k) < Q) (hm : μ (wordFn gws (Q + 1 + k)) = some n.args[k]) :
    ArgsOK pool gws posOf g B G NE cells μ σP Q i n (k + 1) := by
  refine ⟨h.sw, h.self, fun k' hk1 hk2 => ?_⟩
  rcases Nat.lt_or_ge k' k with e | e
  · exact h.args k' e hk2
  · have : k' = k := by omega
    subst this; exact ⟨ha, hm⟩

/-- An argument whose position was unmarked: mark it. -/
theorem ArgsOK.fresh {cells : Array EmbC.Val} {μ σP : Nat → Option Nat} {Q i k : Nat} {n : Node}
    (h : ArgsOK pool gws posOf g B G NE cells μ σP Q i n k) (hk : k < n.args.size)
    (hargl : n.args[k] < pool.size)
    (ha : wordFn gws (Q + 1 + k) < Q)
    (hfit : wordFn gws (Q + 1 + k) + 1 + hdrVlen (wordFn gws (wordFn gws (Q + 1 + k))) ≤ Q)
    (hQ : Q < gws.size) (hm : μ (wordFn gws (Q + 1 + k)) = none) :
    ArgsOK pool gws posOf g B G NE
      (cells.setIfInBounds (B + wordFn gws (Q + 1 + k))
        (.u32 (BitVec.ofNat 32 (offs pool n.args[k] + 1))))
      (updF μ (wordFn gws (Q + 1 + k)) n.args[k]) σP Q i n (k + 1) := by
  obtain ⟨sw, hself, hargs⟩ := h
  generalize hA : wordFn gws (Q + 1 + k) = A at *
  have hQG := (sw.mdom Q i hself).1
  have hext : ∀ t j, μ t = some j → updF μ A n.args[k] t = some j := by
    intro t j ht
    unfold updF
    by_cases e : t = A
    · subst e; rw [hm] at ht; cases ht
    · simp [e, ht]
  have hcell := sw.mark A (by omega)
  refine ⟨⟨?_, ?_, ?_, sw.sdom, ?_, ?_⟩, ?_, ?_⟩
  · intro t ht
    by_cases e : t = A
    · subst e; exact U_set_self (U_lt_size hcell) (by simp [encM, updF])
    · have : encM pool (updF μ A n.args[k]) t = encM pool μ t := by simp [encM, updF, e]
      rw [this]; exact U_set_ne (sw.mark t ht) (by omega)
  · intro p hp; exact U_set_ne (sw.vmap p hp) (by omega)
  · intro t j ht
    unfold updF at ht
    by_cases e : t = A
    · simp [e] at ht; subst ht; subst e
      exact ⟨by omega, hargl, by omega⟩
    · simp [e] at ht; exact sw.mdom t j ht
  · exact hext _ _ sw.root
  · intro t j ht htj
    have e : t ≠ A := by omega
    have htj' : μ t = some j := by simpa [updF, e] using htj
    exact (sw.done t j ht htj').mono hext (fun _ _ e => e)
  · exact hext _ _ hself
  · intro k' hk1 hk2
    rcases Nat.lt_or_ge k' k with e | e
    · obtain ⟨a1, a2⟩ := hargs k' e hk2
      exact ⟨a1, hext _ _ a2⟩
    · have : k' = k := by omega
      subst this
      rw [hA]
      exact ⟨ha, by simp [updF]⟩

/-- All arguments done: the position is checked. -/
theorem ArgsOK.finish {cells : Array EmbC.Val} {μ σP : Nat → Option Nat} {Q i : Nat} {n : Node}
    (h : ArgsOK pool gws posOf g B G NE cells μ σP Q i n n.args.size)
    (hn : pool[i]? = some n) (hf : Fits posOf n)
    (h18 : opC n.op ≠ 0x18) (h19 : opC n.op ≠ 0x19) (h08 : opC n.op ≠ 0x08)
    (hleaf : IsLeaf n.op → n.args = #[]) (hw : wordFn gws Q = hdrW n) :
    SweepOK pool gws posOf g B G NE cells μ σP Q :=
  h.sw.step h.self (glocal_inner hn hf h18 h19 h08 hleaf hw (fun k hk => h.args k hk hk))

end

end Vbcf.Proof
