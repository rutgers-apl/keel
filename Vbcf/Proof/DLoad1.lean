import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Load5

/-!
# Vbcf proofs: `ck_load`'s loop invariant, structural form

`DLoadState` is what holds at the head of `ck_load`'s loop, described without the
one-pass loader `specN`/`LoadInv`: the loop stands at position `p`, the position
of the `d`-th expression (`posOfW`); every position mapped so far names an existing
node of the ghost pool and nothing at or beyond `p` is mapped; the core invariant
holds for the ghost pool; and the input copy holds the position map before `p` and
the original words from `p` on.  `DLoadState.step` is one iteration, where the node
`ck_intern` returns is described by `Interned`; `DLoadState.done` the exit
(`DLoadDone`).
-/

set_option linter.unusedSimpArgs false

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The head of `ck_load`'s loop (structural form). -/
structure DLoadState (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat)
    (p d : Nat) (st : St) (pm : Nat → Option Nat) : Prop where
  pos : p = posOfW (wordFn ws) d
  pmLt : ∀ {a i : Nat}, pm a = some i → i < st.pool.size
  pmNone : ∀ {a : Nat}, p ≤ a → pm a = none
  ple : p ≤ wordFn ws 1
  core : CoreInv (posOfW (wordFn ws)) c st
  proofPtr : c.k.proof = some (W.pb, 0)
  nexpr : c.k.nexpr.toNat = wordFn ws 1
  proofSize : c.proof.size = ws.size
  map : ∀ q, q < p → U c.proof (3 + q) (mapW st.pool pm q)
  rest : ∀ q, (q < 3 ∨ 3 + p ≤ q) → q < ws.size → U c.proof q (wordFn ws q)
  ttNode : st.pool[tt]? = some ⟨.boolVal true, #[]⟩
  ffNode : st.pool[ff]? = some ⟨.boolVal false, #[]⟩
  tt : c.k.tt.toNat = offs st.pool tt
  ff : c.k.ff.toNat = offs st.pool ff
  prem : PremOK c
  factsNull : c.k.facts = none
  flen : c.k.flen = 0#32
  noFacts : st.facts = #[]
  lrNull : c.k.lr = none

section
variable {W : World} {ws : Array (BitVec 32)} {c c' : CMem} {tt ff : Nat} {st : St}
  {p d : Nat} {pm : Nat → Option Nat}

/-- Across a call that only touches the pool and the hash table. -/
theorem DLoadState.frame (hl : DLoadState W ws c tt ff p d st pm) (hf : PoolFrame c c')
    (hcore : CoreInv (posOfW (wordFn ws)) c' st) : DLoadState W ws c' tt ff p d st pm where
  pos := hl.pos
  pmLt := hl.pmLt
  pmNone := hl.pmNone
  ple := hl.ple
  core := hcore
  proofPtr := by rw [hf.proofPtr]; exact hl.proofPtr
  nexpr := by rw [hf.nexpr]; exact hl.nexpr
  proofSize := by rw [hf.proof]; exact hl.proofSize
  map := by rw [hf.proof]; exact hl.map
  rest := by rw [hf.proof]; exact hl.rest
  ttNode := hl.ttNode
  ffNode := hl.ffNode
  tt := by rw [hf.tt]; exact hl.tt
  ff := by rw [hf.ff]; exact hl.ff
  prem := ⟨by rw [hf.premPtr]; exact hl.prem.ptr, by rw [hf.prem]; exact hl.prem.size,
    by rw [hf.prem]; exact hl.prem.cells⟩
  factsNull := by rw [hf.factsPtr]; exact hl.factsNull
  flen := by rw [hf.flen]; exact hl.flen
  noFacts := hl.noFacts
  lrNull := by rw [hf.lrPtr]; exact hl.lrNull

theorem DLoadState.off_lt (hl : DLoadState W ws c tt ff p d st pm) {i : Nat}
    (hi : i < st.pool.size) : offs st.pool i < 2 ^ 30 := hl.core.off_lt hi

/-- The cell read for an argument position `a < p`: 0 exactly when nothing
was loaded there, else one more than the id of what was. -/
theorem DLoadState.ref (hl : DLoadState W ws c tt ff p d st pm) {a : Nat} (ha : a < p) :
    U c.proof (3 + a) (mapW st.pool pm a) ∧ mapW st.pool pm a < 2 ^ 32 ∧
    (mapW st.pool pm a = 0 ↔ pm a = none) ∧
    ∀ i, pm a = some i → i < st.pool.size ∧ mapW st.pool pm a = offs st.pool i + 1 := by
  refine ⟨hl.map a ha, ?_, ?_, ?_⟩
  · unfold mapW
    split
    · decide
    · rename_i i hi; have := hl.off_lt (hl.pmLt hi); omega
  · unfold mapW; split <;> simp_all
  · intro i hi
    exact ⟨hl.pmLt hi, by simp [mapW, hi]⟩

/-- One iteration of `ck_load`'s loop: the node `nd` interned at `r`. -/
theorem DLoadState.step {c3 : CMem} {P' : Array EmbC.Val} {nd : Node} {st' : St} {r : Nat}
    (hl : DLoadState W ws c tt ff p d st pm) (hint : Interned st nd st' r)
    (hfit : p + 1 + hdrVlen (wordFn ws (3 + p)) ≤ wordFn ws 1)
    (hf : PoolFrame c c3) (hcore : CoreInv (posOfW (wordFn ws)) c3 st')
    (hP : ProofOut c3.proof P' p (hdrVlen (wordFn ws (3 + p))) (offs st'.pool r + 1)) :
    DLoadState W ws { c3 with proof := P' } tt ff (p + 1 + hdrVlen (wordFn ws (3 + p))) (d + 1)
      st' (pmSet pm p r) := by
  have hpre := hint.prefix
  have httl := lt_size_of_getElem? hl.ttNode
  have hffl := lt_size_of_getElem? hl.ffNode
  have hproof := hf.proof
  have hsz := hint.size_le
  refine
    { pos := by rw [hl.pos]; rfl
      pmLt := ?_
      pmNone := ?_
      ple := hfit
      core := hcore.congr rfl rfl rfl rfl rfl hcore.poolNull hcore.poolSize hcore.poolCap
        (fun _ _ => rfl) ⟨hcore.stk.null, hcore.stk.size, hcore.stk.cap⟩
      proofPtr := by show c3.k.proof = _; rw [hf.proofPtr]; exact hl.proofPtr
      nexpr := by show c3.k.nexpr.toNat = _; rw [hf.nexpr]; exact hl.nexpr
      proofSize := by show P'.size = _; rw [hP.size, hproof]; exact hl.proofSize
      map := ?_
      rest := ?_
      ttNode := by rw [hpre tt httl]; exact hl.ttNode
      ffNode := by rw [hpre ff hffl]; exact hl.ffNode
      tt := by show c3.k.tt.toNat = _; rw [hf.tt, hint.offs (Nat.le_of_lt httl)]; exact hl.tt
      ff := by show c3.k.ff.toNat = _; rw [hf.ff, hint.offs (Nat.le_of_lt hffl)]; exact hl.ff
      prem := ⟨by show ∃ b, c3.k.prem = some (b, 0); rw [hf.premPtr]; exact hl.prem.ptr,
        by show c3.prem.size = _; rw [hf.prem]; exact hl.prem.size,
        by show ∀ j, j < 256 → ∃ w, w < 2 ^ 32 ∧ U c3.prem j w; rw [hf.prem]; exact hl.prem.cells⟩
      factsNull := by show c3.k.facts = _; rw [hf.factsPtr]; exact hl.factsNull
      flen := by show c3.k.flen = _; rw [hf.flen]; exact hl.flen
      noFacts := by rw [hint.facts]; exact hl.noFacts
      lrNull := by show c3.k.lr = _; rw [hf.lrPtr]; exact hl.lrNull }
  · intro a i hi
    unfold pmSet at hi
    split at hi
    · cases hi; exact hint.lt
    · exact Nat.lt_of_lt_of_le (hl.pmLt hi) hsz
  · intro a ha
    unfold pmSet
    simp only [show a ≠ p by omega, ↓reduceIte]
    exact hl.pmNone (by omega)
  · intro q hq
    show U P' (3 + q) _
    by_cases hqp : q < p
    · have hu := hl.map q hqp
      have hne : 3 + q ≠ 3 + p := by omega
      unfold U at hu ⊢
      rw [hP.other (3 + q) hne (by omega), hproof, hu]
      unfold mapW pmSet
      simp only [Nat.ne_of_lt hqp, ↓reduceIte]
      cases hq' : pm q with
      | none => rfl
      | some i => simp only; rw [hint.offs (Nat.le_of_lt (hl.pmLt hq'))]
    · by_cases hqe : q = p
      · subst hqe
        unfold mapW pmSet
        simp only [↓reduceIte]
        exact hP.hdr
      · have hk := hP.zero (q - p - 1) (by omega)
        rw [show 4 + p + (q - p - 1) = 3 + q by omega] at hk
        unfold mapW pmSet
        simp only [hqe, ↓reduceIte, hl.pmNone (show p ≤ q by omega)]
        exact hk
  · intro q hq hqs
    show U P' q _
    have hu := hl.rest q (by omega) hqs
    unfold U at hu ⊢
    rw [hP.other q (by omega) (by omega), hproof, hu]

/-- The exit of the loop. -/
theorem DLoadState.done (hl : DLoadState W ws c tt ff p d st pm) (hp : p = wordFn ws 1)
    (hsz : 3 ≤ ws.size) (hmagic : wordFn ws 0 = 0x0BCF) (hne : wordFn ws 1 ≠ 0)
    (hns : 2 ≤ wordFn ws 2) (hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size)
    (hws : ws.size ≤ 2 ^ 32) :
    DLoadDone W ws { c with k := { c.k with lo := c.k.plen } } tt ff st pm := by
  subst hp
  exact
    { hsz := hsz, hmagic := hmagic, hne := hne, hns := hns, hlen := hlen
      pmLt := hl.pmLt, pmNone := hl.pmNone
      core := hl.core.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      proofPtr := hl.proofPtr
      psize := by rw [hl.proofSize]; exact hws
      nexpr := hl.nexpr, proofSize := hl.proofSize
      map := fun q hq => hl.map q hq
      rest := fun q hq hqs => hl.rest q hq hqs
      ttNode := hl.ttNode, ffNode := hl.ffNode, tt := hl.tt, ff := hl.ff, prem := ⟨hl.prem.ptr, hl.prem.size, hl.prem.cells⟩
      factsNull := hl.factsNull, flen := hl.flen, noFacts := hl.noFacts
      lrNull := hl.lrNull, lo := rfl }

end

/-- `ck_load`'s loop head, the first time. -/
theorem DLoadState.init {W : World} {ws : Array (BitVec 32)} {c : CMem} {tt ff : Nat} {st1 : St}
    (hcore : CoreInv (posOfW (wordFn ws)) c st1)
    (hb : DBuiltin2 st1 tt ff) (htt : c.k.tt.toNat = offs st1.pool tt)
    (hff : c.k.ff.toNat = offs st1.pool ff) (hprem : PremOK c) (hfacts : c.k.facts = none)
    (hflen : c.k.flen = 0#32) (hproofPtr : c.k.proof = some (W.pb, 0))
    (hnexpr : c.k.nexpr.toNat = wordFn ws 1) (hproof : c.proof = ws.map EmbC.Val.u32)
    (hlr : c.k.lr = none) :
    DLoadState W ws c tt ff 0 0 st1 (fun _ => none) := by
  obtain ⟨h1, h2, h3⟩ := hb.nodes
  refine ⟨rfl, fun hi => by simp at hi, fun _ => rfl, Nat.zero_le _, hcore, hproofPtr, hnexpr,
    by rw [hproof]; simp, fun q hq => absurd hq (Nat.not_lt_zero _), ?_, h1, h2, htt, hff, hprem,
    hfacts, hflen, h3, hlr⟩
  intro q _ hqs
  unfold U
  rw [hproof, wordFn_eq ws q hqs]
  simp [hqs]

end Vbcf.Proof
