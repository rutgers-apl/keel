import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact3

/-!
# Vbcf proofs: `ck_compact`, part 4 — marking the roots

The forwarding table during marking: cell `offs y - lo` is `NOID` for a
marked node `y ≥ nL`, every cell is `0` or `NOID`.  `MarkInv` is the marking
invariant: every marked node is on the scratch stack or has all its
children (at or above `nL`) marked.  The first loop marks the nodes of the
facts that a later step cites.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The value of `NOID`. -/
def noidN : Nat := 4294967295

/-- Node `y` is marked. -/
def Mk (pool : Pool) (nL : Nat) (fw : Array EmbC.Val) (y : Nat) : Prop :=
  U fw (offs pool y - offs pool nL) noidN

/-- Every child of `y` at or above `nL` is marked. -/
def Done (pool : Pool) (nL : Nat) (fw : Array EmbC.Val) (y : Nat) : Prop :=
  ∀ n, pool[y]? = some n → ∀ a ∈ n.args, nL ≤ a → Mk pool nL fw a

/-- The marking invariant.  `pend` is the node being expanded, if any. -/
structure MarkInv (cs : St) (nL : Nat) (c0 c : CMem) (fw : Array EmbC.Val) (pend : Nat → Prop) :
    Prop where
  fr : StkFrame c0 c
  stk : StkOK c
  size : fw.size = offs cs.pool cs.pool.size - offs cs.pool nL
  cells : ∀ k, k < fw.size → U fw k 0 ∨ U fw k noidN
  onStk : ∀ p, p < c.k.sp.toNat → ∃ y, nL ≤ y ∧ y < cs.pool.size ∧
    U c.stk p (offs cs.pool y) ∧ Mk cs.pool nL fw y
  todo : ∀ y, nL ≤ y → y < cs.pool.size → Mk cs.pool nL fw y →
    (∃ p, p < c.k.sp.toNat ∧ U c.stk p (offs cs.pool y)) ∨ Done cs.pool nL fw y ∨ pend y

/-- The facts below `j` that a later step cites have their node marked. -/
def RootsUpTo (c0 : CMem) (S : VSt) (nL : Nat) (fw : Array EmbC.Val) (j : Nat) : Prop :=
  ∀ j' f, j' < j → LiveFact c0 S j' f → nL ≤ S.σ f → Mk S.cs.pool nL fw (S.σ f)

/-! ## Marking one more node -/

theorem Mk.set {pool : Pool} {nL : Nat} {fw : Array EmbC.Val} {y k : Nat} (hk : k < fw.size)
    (h : Mk pool nL fw y) : Mk pool nL (fw.setIfInBounds k (.u32 (BitVec.ofNat 32 noidN))) y := by
  unfold Mk at *
  by_cases e : offs pool y - offs pool nL = k
  · rw [e]; exact U.set_self _ hk
  · exact (U.set_ne e).mpr h

theorem Mk.set_self {pool : Pool} {nL : Nat} {fw : Array EmbC.Val} {y : Nat}
    (hk : offs pool y - offs pool nL < fw.size) :
    Mk pool nL (fw.setIfInBounds (offs pool y - offs pool nL) (.u32 (BitVec.ofNat 32 noidN))) y :=
  U.set_self _ hk

theorem Done.set {pool : Pool} {nL : Nat} {fw : Array EmbC.Val} {y k : Nat} (hk : k < fw.size)
    (h : Done pool nL fw y) : Done pool nL (fw.setIfInBounds k (.u32 (BitVec.ofNat 32 noidN))) y :=
  fun n hn a ha hle => (h n hn a ha hle).set hk

/-- A marked cell is not zero. -/
theorem Mk.ne_zero {pool : Pool} {nL : Nat} {fw : Array EmbC.Val} {y : Nat} (h : Mk pool nL fw y)
    (h0 : U fw (offs pool y - offs pool nL) 0) : False := by
  have := U.inj32 h h0 (by decide) (by decide)
  simp [noidN] at this

/-- After `fw[offs y - lo] = NOID; push(st, offs y)` succeeded. -/
theorem MarkInv.push {cs : St} {nL : Nat} {c0 c c' : CMem} {fw : Array EmbC.Val} {y : Nat}
    {pend : Nat → Prop} (hM : MarkInv cs nL c0 c fw pend) (hy : nL ≤ y) (hys : y < cs.pool.size)
    (hk : offs cs.pool y - offs cs.pool nL < fw.size)
    (hok : StkOK c') (hfr : StkFrame c c') (hpre : ∀ i, i < c.k.sp.toNat → c'.stk[i]? = c.stk[i]?)
    (hsp : c'.k.sp.toNat = c.k.sp.toNat + 1)
    (htop : c'.stk[c.k.sp.toNat]? = some (.u32 (BitVec.ofNat 32 (offs cs.pool y)))) :
    MarkInv cs nL c0 c' (fw.setIfInBounds (offs cs.pool y - offs cs.pool nL)
      (.u32 (BitVec.ofNat 32 noidN))) pend := by
  have hU : ∀ p w, p < c.k.sp.toNat → U c.stk p w → U c'.stk p w := by
    intro p w hp hu; unfold U at *; rw [hpre p hp]; exact hu
  refine ⟨hM.fr.trans hfr, hok, by rw [Array.size_setIfInBounds]; exact hM.size, ?_, ?_, ?_⟩
  · intro k hk'
    rw [Array.size_setIfInBounds] at hk'
    by_cases e : k = offs cs.pool y - offs cs.pool nL
    · subst e; exact Or.inr (U.set_self _ hk')
    · rcases hM.cells k hk' with h0 | h1
      · exact Or.inl ((U.set_ne e).mpr h0)
      · exact Or.inr ((U.set_ne e).mpr h1)
  · intro p hp
    rw [hsp] at hp
    rcases Nat.lt_or_ge p c.k.sp.toNat with hp' | hp'
    · obtain ⟨z, h1, h2, h3, h4⟩ := hM.onStk p hp'
      exact ⟨z, h1, h2, hU p _ hp' h3, h4.set hk⟩
    · have : p = c.k.sp.toNat := by omega
      subst this
      exact ⟨y, hy, hys, htop, Mk.set_self hk⟩
  · intro z h1 h2 h3
    by_cases e : z = y
    · subst e
      exact Or.inl ⟨c.k.sp.toNat, by omega, htop⟩
    · have hz : Mk cs.pool nL fw z := by
        unfold Mk at h3 ⊢
        have hne : offs cs.pool z - offs cs.pool nL ≠ offs cs.pool y - offs cs.pool nL := by
          intro e'
          have o1 := offs_le_of_le (pool := cs.pool) h1
          have o2 := offs_le_of_le (pool := cs.pool) hy
          have o3 : offs cs.pool z = offs cs.pool y := by omega
          exact e (offs_inj (Nat.le_of_lt h2) (Nat.le_of_lt hys) o3)
        exact (U.set_ne hne).mp h3
      rcases hM.todo z h1 h2 hz with ⟨p, hp, hu⟩ | hd | hpd
      · exact Or.inl ⟨p, by omega, hU p _ hp hu⟩
      · exact Or.inr (Or.inl (hd.set hk))
      · exact Or.inr (Or.inr hpd)

/-! ## Writing the forwarding table -/

section
variable {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {W : World} {sb : Nat} {c : CMem}

/-- `fw[i] = e`. -/
theorem WP.aux_store {p i e : Expr} {fb : Nat} {cells : Array EmbC.Val} {m : Mem}
    (h : Holds (W.addAux fb ⟨.u32, cells⟩) m sb c) (hm : st.mem = m)
    (H : match evalE P env st.mem p, evalE P env st.mem i, evalE P env st.mem e with
      | some (.ptr b' off), some vi, some (.u32 x) =>
        b' = fb ∧
        match vi.toIdx with
        | none => False
        | some kx =>
          off + kx < cells.size ∧
          ∀ st', Holds (W.addAux fb ⟨.u32, cells.setIfInBounds (off + kx) (.u32 x)⟩) st'.mem sb c →
            Q .normal env st'
      | _, _, _ => False) :
    WP P (.store p i e) Q env st := by
  subst hm
  apply WP.store
  split at H
  · rename_i b' off vi x hp' hi he
    obtain ⟨rfl, H⟩ := H
    rw [hp', hi, he]; dsimp only
    split at H
    · exact H.elim
    · rename_i kx hk
      rw [hk]; dsimp only
      obtain ⟨hlt, H⟩ := H
      obtain ⟨hst, hh⟩ := h.storeAux hlt x
      rw [hst]; exact H _ hh
  · exact H.elim

end

end Vbcf.Proof
