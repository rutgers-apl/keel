import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact1

/-!
# Vbcf proofs: `ck_compact`, part 2 — the new view and the step invariant

`VSt.compact S keep`: the same Lean state, seen through the compacted C-side
state.  A Lean node stays live if its image is kept; its new image is the
kept node's new index.  `SInv.compact` re-establishes the step invariant for
the compacted view from what the C code guarantees about the new memory.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The view after compaction. -/
def VSt.compact (S : VSt) (keep : Nat → Bool) (hok : PoolOK S.cs) (hcl : KClosed keep S.cs.pool) :
    VSt where
  toSt := S.toSt
  σ := fun i => cntK keep (S.σ i)
  lv := fun i => S.lv i ∧ keep (S.σ i) = true
  cs := cst keep S.cs
  ok := S.ok
  lvLt := fun i h => S.lvLt i h.1
  img := fun i n h hn => by
    have := S.img i n h.1 hn
    show (cpool keep S.cs.pool)[cntK keep (S.σ i)]? = _
    rw [cpool_get' h.2 this, Node.ren_ren]
  ty := fun i h => by
    show (cst keep S.cs).tys[cntK keep (S.σ i)]? = _
    rw [cst_tys_get hok h.2 (S.σ_lt h.1)]
    exact S.ty i h.1
  closed := fun i n h hn a ha => by
    refine ⟨S.closed i n h.1 hn a ha, ?_⟩
    have himg := S.img i n h.1 hn
    exact hcl _ _ h.2 himg (S.σ a) (by simp only [Node.ren_args, Array.mem_map]; exact ⟨a, ha, rfl⟩)
  inj := fun i j hi hj e => S.inj i j hi.1 hj.1 (cntK_inj hi.2 hj.2 e)
  surj := fun x hx => by
    have hx' : x < (cpool keep S.cs.pool).size := hx
    obtain ⟨y, n, hk, hn, rfl, -⟩ := cpool_surj (Array.getElem?_eq_getElem hx')
    obtain ⟨i, hi, he⟩ := S.surj y (lt_size_of_getElem? hn)
    exact ⟨i, ⟨hi, by rw [he]; exact hk⟩, by show cntK keep (S.σ i) = _; rw [he]⟩

section
variable {S : VSt} {keep : Nat → Bool} {hok : PoolOK S.cs} {hcl : KClosed keep S.cs.pool}

@[simp] theorem VSt.compact_toSt : (S.compact keep hok hcl).toSt = S.toSt := rfl
@[simp] theorem VSt.compact_cs : (S.compact keep hok hcl).cs = cst keep S.cs := rfl
@[simp] theorem VSt.compact_lv (i : Nat) :
    (S.compact keep hok hcl).lv i ↔ S.lv i ∧ keep (S.σ i) = true := Iff.rfl
@[simp] theorem VSt.compact_σ (i : Nat) : (S.compact keep hok hcl).σ i = cntK keep (S.σ i) := rfl

/-- The new id of a live node: its kept node's new offset. -/
theorem VSt.compact_id {i : Nat} (hi : S.lv i) :
    (S.compact keep hok hcl).id i = offK keep S.cs.pool (S.σ i) := by
  show offs (cpool keep S.cs.pool) (cntK keep (S.σ i)) = _
  exact offs_cpool (Nat.le_of_lt (S.σ_lt hi))

/-- Below a kept prefix, ids do not change. -/
theorem VSt.compact_id_pre {nL : Nat} (hpre : ∀ y, y < nL → keep y = true)
    (hnL : nL ≤ S.cs.pool.size) {i : Nat} (hi : S.lv i) (hlt : S.σ i < nL) :
    (S.compact keep hok hcl).id i = S.id i := by
  rw [VSt.compact_id hi, offK_pre hpre hnL _ (Nat.le_of_lt hlt)]; rfl

end

/-- What `ck_compact` leaves unchanged. -/
structure CompactFr (c c' : CMem) : Prop where
  proof : c'.proof = c.proof
  prem : c'.prem = c.prem
  lr : c'.lr = c.lr
  factsSize : c'.facts.size = c.facts.size
  poolPtr : c'.k.pool = c.k.pool
  proofPtr : c'.k.proof = c.k.proof
  premPtr : c'.k.prem = c.k.prem
  factsPtr : c'.k.facts = c.k.facts
  lrPtr : c'.k.lr = c.k.lr
  nexpr : c'.k.nexpr = c.k.nexpr
  tt : c'.k.tt = c.k.tt
  ff : c'.k.ff = c.k.ff
  goal : c'.k.goal = c.k.goal
  flen : c'.k.flen = c.k.flen
  fcap : c'.k.fcap = c.k.fcap
  lo : c'.k.lo = c.k.lo

/-- The facts that must survive: those cited by a later step. -/
def LiveFact (c : CMem) (S : VSt) (j f : Nat) : Prop :=
  S.facts[j]? = some f ∧ ∃ w, w < 2 ^ 32 ∧ U c.lr j w ∧ c.k.flen.toNat ≤ w

/-- The step invariant for the compacted view. -/
theorem SInv.compact {W : World} {ws : Array (BitVec 32)} {X : Ctx} {c c' : CMem} {S : VSt}
    {off : Nat} {rest : List Step} (hS : SInv W ws X c S off rest) {keep : Nat → Bool}
    (hcl : KClosed keep S.cs.pool) (hpre : ∀ y, y < X.nL → keep y = true)
    (hroots : ∀ j f, LiveFact c S j f → keep (S.σ f) = true)
    (hfr : CompactFr c c') (hcore : CoreInv X.posOf c' (cst keep S.cs))
    (hfacts : ∀ j f, LiveFact c S j f → U c'.facts j (offK keep S.cs.pool (S.σ f)))
    (hcells : ∀ j, j < c'.facts.size → ∃ w, w < 2 ^ 32 ∧ U c'.facts j w) :
    SInv W ws X c' (S.compact keep hS.inv.core.cinv.ok hcl) off rest := by
  have hR := hS.inv
  have hnL := hS.nLcs
  have hld := hS.loaded
  -- live Lean nodes below `nL` keep their ids
  have hlow : ∀ i, i < X.nL → (S.compact keep hR.core.cinv.ok hcl).lv i ∧
      (S.compact keep hR.core.cinv.ok hcl).id i = S.id i := by
    intro i hi
    obtain ⟨hlv, hσ⟩ := hld i hi
    exact ⟨⟨hlv, hpre _ hσ⟩, VSt.compact_id_pre hpre hnL hlv hσ⟩
  refine ⟨?_, hS.noFloor, hS.wsz, by rw [hfr.nexpr]; exact hS.nexpr, hS.hlen,
    by rw [hfr.proof]; exact hS.proofSize, by rw [hfr.proof]; exact hS.words,
    by rw [hfr.factsPtr]; exact hS.factsPtr, by rw [hfr.flen]; exact hS.flen,
    by rw [hfr.factsSize]; exact hS.factsSize, by rw [hfr.fcap, hfr.factsSize]; exact hS.fcap,
    hcells, by rw [hfr.lrPtr]; exact hS.lrPtr, by rw [hfr.lr, hfr.factsSize]; exact hS.lrSize,
    by rw [hfr.lr]; exact hS.lrCells, ?_, ?_, ?_, ?_, hS.ttL, hS.ffL, hS.goalL, hS.eiL, hS.steps,
    hS.sound⟩
  · -- the rule invariant
    refine ⟨⟨hcore, hR.core.fitsAll⟩, by rw [hfr.poolPtr]; exact hR.poolPtr, hR.ttNode, hR.ffNode,
      ?_, ?_, ?_, by rw [hfr.proofPtr]; exact hR.proofPtr, by rw [hfr.nexpr, hfr.proof]; exact hR.nexpr,
      by rw [hfr.nexpr]; exact hR.nexprBound, ?_, by rw [hfr.nexpr]; exact hR.eiOut,
      by rw [hfr.premPtr]; exact hR.premPtr, by rw [hfr.prem]; exact hR.premSize,
      by rw [hfr.prem]; exact hR.premCells, fun S0 h => by rw [hS.noFloor] at h; cases h⟩
    · obtain ⟨h1, h2⟩ := hlow _ hS.ttL
      exact ⟨h1, by rw [hfr.tt, h2]; exact hR.tt.2⟩
    · obtain ⟨h1, h2⟩ := hlow _ hS.ffL
      exact ⟨h1, by rw [hfr.ff, h2]; exact hR.ff.2⟩
    · obtain ⟨h1, h2⟩ := hlow _ hS.goalL
      exact ⟨h1, by rw [hfr.goal, h2]; exact hR.goal.2⟩
    · intro p hp
      rw [hfr.nexpr] at hp
      obtain ⟨v, hv, hu, hm⟩ := hR.ei p hp
      refine ⟨v, hv, by rw [hfr.proof]; exact hu, ?_⟩
      cases he : X.ei p with
      | none => rw [he] at hm; exact hm
      | some i =>
        rw [he] at hm
        obtain ⟨h1, h2⟩ := hlow i (hS.eiL p i he)
        exact ⟨h1, by rw [h2]; exact hm.2⟩
  · -- the facts
    intro j f hf
    refine ⟨(hS.facts j f hf).1, fun w hw32 hw hle => ?_⟩
    rw [hfr.lr] at hw
    rw [hfr.flen] at hle
    have hL : LiveFact c S j f := ⟨hf, w, hw32, hw, hle⟩
    have hlv := ((hS.facts j f hf).2 w hw32 hw hle).1
    refine ⟨⟨hlv, hroots j f hL⟩, ?_⟩
    rw [VSt.compact_id hlv]
    exact hfacts j f hL
  · intro i hi
    obtain ⟨h1, -⟩ := hlow i hi
    obtain ⟨-, hσ⟩ := hld i hi
    refine ⟨h1, ?_⟩
    show cntK keep (S.σ i) < X.nL
    rw [cntK_pre hpre _ (Nat.le_of_lt hσ)]; exact hσ
  · show X.nL ≤ (cpool keep S.cs.pool).size
    rw [cpool_size]
    have := cntK_mono (keep := keep) hnL
    rw [cntK_pre hpre X.nL (Nat.le_refl _)] at this
    exact this
  · rw [hfr.lo, hS.lo]
    show offs S.cs.pool X.nL = offs (cpool keep S.cs.pool) X.nL
    have h1 := offs_cpool (keep := keep) hnL
    rw [cntK_pre hpre X.nL (Nat.le_refl _), offK_pre hpre hnL X.nL (Nat.le_refl _)] at h1
    exact h1.symm

/-! ## The new pool's words -/

/-- The words the C code writes for a kept node: header, and children as new offsets. -/
def newW (posOf : Nat → Nat) (keep : Nat → Bool) (pool : Pool) (n : Node) : List Nat :=
  hdrW n :: tailW posOf (offK keep pool) n

/-- The compacted pool is represented by cells holding each kept node's new words at its
new offset. -/
theorem PoolRep.compact {posOf : Nat → Nat} {cs : St} {keep : Nat → Bool} {cells : Array EmbC.Val}
    (hok : PoolOK cs) (_hcl : KClosed keep cs.pool)
    (hfits : ∀ (i : Nat) (n : Node), cs.pool[i]? = some n → Fits posOf n)
    (hw : ∀ x n, keep x = true → cs.pool[x]? = some n →
      WordsAt cells (offK keep cs.pool x) (newW posOf keep cs.pool n)) :
    PoolRep posOf (cpool keep cs.pool) cells (offK keep cs.pool cs.pool.size) where
  len := offs_cpool_end.symm
  fits := fun i m hm => by
    obtain ⟨x, n, -, hn, rfl, rfl⟩ := cpool_surj hm
    exact fits_ren.mpr (hfits x n hn)
  cell := fun i m hm => by
    obtain ⟨x, n, hk, hn, rfl, rfl⟩ := cpool_surj hm
    have hx := lt_size_of_getElem? hn
    rw [offs_cpool (Nat.le_of_lt hx)]
    have : nodeW posOf (cpool keep cs.pool) (n.ren (cntK keep)) = newW posOf keep cs.pool n := by
      simp only [nodeW, newW, hdrW_ren, tailW_ren]
      congr 1
      apply tailW_congr
      intro a ha
      exact offs_cpool (Nat.le_of_lt (Nat.lt_trans (hok.args_lt hn a ha) hx))
    rw [this]
    exact hw x n hk hn

end Vbcf.Proof
