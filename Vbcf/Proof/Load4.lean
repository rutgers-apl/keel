import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Load3

/-!
# Vbcf proofs: the loading phase, part 4 — `ck_load`'s loop invariant

`LoadState` is what holds at the head of `ck_load`'s loop: the one-pass
loader's invariant `LoadInv` at position `p` after `d` expressions, the core
invariant for its state, and the input copy holding the position map before
`p` and the original words from `p` on.  `LoadState.step` is one iteration,
`LoadState.done` the exit (`LoadDone`).
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The cell of the input copy at `3 + q` for a loaded position `q`. -/
def mapW (pool : Pool) (pm : Nat → Option Nat) (q : Nat) : Nat :=
  match pm q with
  | none => 0
  | some i => offs pool i + 1

/-- The head of `ck_load`'s loop. -/
structure LoadState (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st1 : St)
    (p d : Nat) (st : St) (pm : Nat → Option Nat) : Prop where
  inv : LoadInv (wordFn ws) st1 p d st pm
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
variable {W : World} {ws : Array (BitVec 32)} {c c' : CMem} {tt ff : Nat} {st1 st : St}
  {p d : Nat} {pm : Nat → Option Nat}

/-- Across a call that only touches the pool and the hash table. -/
theorem LoadState.frame (hl : LoadState W ws c tt ff st1 p d st pm) (hf : PoolFrame c c')
    (hcore : CoreInv (posOfW (wordFn ws)) c' st) : LoadState W ws c' tt ff st1 p d st pm where
  inv := hl.inv
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

/-- Across stores into the pool at or beyond `plen`. -/
theorem LoadState.tail (hl : LoadState W ws c tt ff st1 p d st pm) (ht : TailEq c c') :
    LoadState W ws c' tt ff st1 p d st pm :=
  hl.frame ht.poolFrame (hl.core.tailEq ht)

theorem LoadState.p_lt (hl : LoadState W ws c tt ff st1 p d st pm) (hsz : ws.size ≤ 2 ^ 32)
    (hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size) : p < 2 ^ 32 := by
  have := hl.ple; omega

theorem LoadState.pm_lt (hl : LoadState W ws c tt ff st1 p d st pm) {a i : Nat}
    (hi : pm a = some i) : i < st.pool.size := hl.inv.pm_lt hi

theorem LoadState.off_lt (hl : LoadState W ws c tt ff st1 p d st pm) {i : Nat}
    (hi : i < st.pool.size) : offs st.pool i < 2 ^ 30 := hl.core.off_lt hi

/-- The cell read for an argument position `a < p`: 0 exactly when nothing
was loaded there, else one more than the id of what was. -/
theorem LoadState.ref (hl : LoadState W ws c tt ff st1 p d st pm) {a : Nat} (ha : a < p) :
    U c.proof (3 + a) (mapW st.pool pm a) ∧ mapW st.pool pm a < 2 ^ 32 ∧
    (mapW st.pool pm a = 0 ↔ pm a = none) ∧
    ∀ i, pm a = some i → i < st.pool.size ∧ mapW st.pool pm a = offs st.pool i + 1 := by
  refine ⟨hl.map a ha, ?_, ?_, ?_⟩
  · unfold mapW
    split
    · decide
    · rename_i i hi; have := hl.off_lt (hl.pm_lt hi); omega
  · unfold mapW; split <;> simp_all
  · intro i hi
    exact ⟨hl.pm_lt hi, by simp [mapW, hi]⟩

/-- How the iteration changes the input copy: the header cell becomes `v`,
the next `vlen` cells 0, the others are as before. -/
structure ProofOut (P P' : Array EmbC.Val) (p vlen v : Nat) : Prop where
  size : P'.size = P.size
  hdr : U P' (3 + p) v
  zero : ∀ k, k < vlen → U P' (4 + p + k) 0
  other : ∀ q, q ≠ 3 + p → (q < 4 + p ∨ 4 + p + vlen ≤ q) → P'[q]? = P[q]?

/-- One iteration of `ck_load`'s loop. -/
theorem LoadState.step {c3 : CMem} {P' : Array EmbC.Val} {nd : Node} {st' : St} {r : Nat}
    (hl : LoadState W ws c tt ff st1 p d st pm)
    (hn : loadNode (wordFn ws) p d pm = some nd) (hpush : pushNode st nd = some (st', r))
    (hfit : p + 1 + hdrVlen (wordFn ws (3 + p)) ≤ wordFn ws 1)
    (hf : PoolFrame c c3) (hcore : CoreInv (posOfW (wordFn ws)) c3 st')
    (hP : ProofOut c3.proof P' p (hdrVlen (wordFn ws (3 + p))) (offs st'.pool r + 1)) :
    LoadState W ws { c3 with proof := P' } tt ff st1 (p + 1 + hdrVlen (wordFn ws (3 + p))) (d + 1)
      st' (pmSet pm p r) := by
  have hpre := pushNode_prefix hpush
  have httl := lt_size_of_getElem? hl.ttNode
  have hffl := lt_size_of_getElem? hl.ffNode
  have hproof := hf.proof
  refine
    { inv := hl.inv.step hn hpush
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
      tt := by show c3.k.tt.toNat = _; rw [hf.tt, pushNode_offs hpush (Nat.le_of_lt httl)]; exact hl.tt
      ff := by show c3.k.ff.toNat = _; rw [hf.ff, pushNode_offs hpush (Nat.le_of_lt hffl)]; exact hl.ff
      prem := ⟨by show ∃ b, c3.k.prem = some (b, 0); rw [hf.premPtr]; exact hl.prem.ptr,
        by show c3.prem.size = _; rw [hf.prem]; exact hl.prem.size,
        by show ∀ j, j < 256 → ∃ w, w < 2 ^ 32 ∧ U c3.prem j w; rw [hf.prem]; exact hl.prem.cells⟩
      factsNull := by show c3.k.facts = _; rw [hf.factsPtr]; exact hl.factsNull
      flen := by show c3.k.flen = _; rw [hf.flen]; exact hl.flen
      noFacts := by rw [pushNode_facts hpush]; exact hl.noFacts
      lrNull := by show c3.k.lr = _; rw [hf.lrPtr]; exact hl.lrNull }
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
      | some i => simp only; rw [pushNode_offs hpush (Nat.le_of_lt (hl.pm_lt hq'))]
    · by_cases hqe : q = p
      · subst hqe
        unfold mapW pmSet
        simp only [↓reduceIte]
        exact hP.hdr
      · have hk := hP.zero (q - p - 1) (by omega)
        rw [show 4 + p + (q - p - 1) = 3 + q by omega] at hk
        unfold mapW pmSet
        simp only [hqe, ↓reduceIte, hl.inv.pm_none (show p ≤ q by omega)]
        exact hk
  · intro q hq hqs
    show U P' q _
    have hu := hl.rest q (by omega) hqs
    unfold U at hu ⊢
    rw [hP.other q (by omega) (by omega), hproof, hu]

/-- The exit of the loop. -/
theorem LoadState.done (hl : LoadState W ws c tt ff st1 p d st pm) (hp : p = wordFn ws 1)
    (hsz : 3 ≤ ws.size) (hmagic : wordFn ws 0 = 0x0BCF) (hne : wordFn ws 1 ≠ 0)
    (hns : 2 ≤ wordFn ws 2) (hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size)
    (hb : Builtin2 st1 tt ff) (hws : ws.size ≤ 2 ^ 32) :
    LoadDone W ws { c with k := { c.k with lo := c.k.plen } } tt ff st1 st pm d := by
  subst hp
  exact
    { hsz := hsz, hmagic := hmagic, hne := hne, hns := hns, hlen := hlen, b2 := hb
      load := hl.inv, core := hl.core.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      proofPtr := hl.proofPtr
      psize := by rw [hl.proofSize]; exact hws
      nexpr := hl.nexpr, proofSize := hl.proofSize
      map := fun q hq => hl.map q hq
      rest := fun q hq hqs => hl.rest q hq hqs
      ttNode := hl.ttNode, ffNode := hl.ffNode, tt := hl.tt, ff := hl.ff
      prem := ⟨hl.prem.ptr, hl.prem.size, hl.prem.cells⟩
      factsNull := hl.factsNull, flen := hl.flen, noFacts := hl.noFacts, lrNull := hl.lrNull
      lo := rfl }

end

/-- The built-in nodes are in the state the loader starts from. -/
theorem Builtin2.nodes {st1 : St} {tt ff : Nat} (hb : Builtin2 st1 tt ff) :
    st1.pool[tt]? = some ⟨.boolVal true, #[]⟩ ∧ st1.pool[ff]? = some ⟨.boolVal false, #[]⟩ ∧
    st1.facts = #[] := by
  obtain ⟨st0, h0, h1⟩ := hb
  have htt := pushNode_get h0
  refine ⟨?_, pushNode_get h1, ?_⟩
  · rw [pushNode_prefix h1 tt (lt_size_of_getElem? htt)]; exact htt
  · rw [pushNode_facts h1, pushNode_facts h0]; rfl

/-- `ck_load`'s loop head, the first time. -/
theorem LoadState.init {W : World} {ws : Array (BitVec 32)} {c : CMem} {tt ff : Nat} {st1 : St}
    (hcore : CoreInv (posOfW (wordFn ws)) c st1)
    (hb : Builtin2 st1 tt ff) (htt : c.k.tt.toNat = offs st1.pool tt)
    (hff : c.k.ff.toNat = offs st1.pool ff) (hprem : PremOK c) (hfacts : c.k.facts = none)
    (hflen : c.k.flen = 0#32) (hproofPtr : c.k.proof = some (W.pb, 0))
    (hnexpr : c.k.nexpr.toNat = wordFn ws 1) (hproof : c.proof = ws.map EmbC.Val.u32)
    (hlr : c.k.lr = none) :
    LoadState W ws c tt ff st1 0 0 st1 (fun _ => none) := by
  obtain ⟨h1, h2, h3⟩ := hb.nodes
  refine ⟨LoadInv.init _ st1, Nat.zero_le _, hcore, hproofPtr, hnexpr, by rw [hproof]; simp,
    fun q hq => absurd hq (Nat.not_lt_zero _), ?_, h1, h2, htt, hff, hprem, hfacts, hflen, h3, hlr⟩
  intro q _ hqs
  unfold U
  rw [hproof, wordFn_eq ws q hqs]
  simp [hqs]

/-! ## The candidate's words, with the header named -/

section
variable {w : Nat → Nat} {p : Nat} {pm : Nat → Option Nat} {pool : Pool} {x : Nat}

theorem ldArg_var (hx : w (3 + p) = x) (hv : VarHdr x) (k : Nat) : ldArg w p pm pool k = p := by
  subst hx; simp [ldArg, hv]

theorem ldArg_val (hx : w (3 + p) = x) (hv : ¬ VarHdr x) (h8 : hdrCode x = 0x08) (k : Nat) :
    ldArg w p pm pool k = w (4 + p + k) := by
  subst hx; simp [ldArg, hv, h8]

theorem ldArg_ref (hx : w (3 + p) = x) (hv : ¬ VarHdr x) (h8 : hdrCode x ≠ 0x08) {k i : Nat}
    (hi : pm (w (4 + p + k)) = some i) : ldArg w p pm pool k = offs pool i := by
  subst hx; simp [ldArg, hv, h8, hi]

theorem LoadWritten.of_hdr {st : St} {c : CMem} (hx : w (3 + p) = x)
    (hdr : U c.pool c.k.plen.toNat (ldHdr x))
    (args : ∀ k, k < ldLen x → U c.pool (c.k.plen.toNat + 1 + k) (ldArg w p pm st.pool k))
    (room : c.k.plen.toNat + 1 + ldLen x ≤ c.k.pcap.toNat)
    (var0 : VarHdr x → hdrVlen x = 0)
    (refs : ¬ VarHdr x → hdrCode x ≠ 0x08 → ∀ k, k < hdrVlen x →
      w (4 + p + k) < p ∧ ∃ i, pm (w (4 + p + k)) = some i ∧ i < st.pool.size) :
    LoadWritten w p pm st c := by
  subst hx; exact ⟨hdr, args, room, var0, refs⟩

end

theorem TailEq.wr2 {c : CMem} {i j : Nat} {x y : BitVec 32} (hi : c.k.plen.toNat ≤ i)
    (hj : c.k.plen.toNat ≤ j) : TailEq c (Vbcf.Proof.wr (Vbcf.Proof.wr c i x) j y) :=
  (TailEq.wr hi).trans (TailEq.wr (by simpa using hj))

/-! ## The input copy after one iteration -/

theorem ProofOut.init {P : Array EmbC.Val} {p v : Nat} (hp : 3 + p < P.size) :
    ProofOut P (P.setIfInBounds (3 + p) (.u32 (BitVec.ofNat 32 v))) p 0 v where
  size := by simp
  hdr := by unfold U; simp [hp]
  zero := fun k hk => absurd hk (Nat.not_lt_zero _)
  other := fun q hq _ => by simp [Ne.symm hq]

theorem ProofOut.step {P P' : Array EmbC.Val} {p k v : Nat} (h : ProofOut P P' p k v)
    (hk : 4 + p + k < P.size) :
    ProofOut P (P'.setIfInBounds (4 + p + k) (.u32 0#32)) p (k + 1) v where
  size := by simp [h.size]
  hdr := by
    have := h.hdr
    unfold U at this ⊢
    rw [Array.getElem?_setIfInBounds]
    simp only [show ¬ (4 + p + k = 3 + p) by omega, ↓reduceIte]
    exact this
  zero := by
    intro j hj
    unfold U
    rw [Array.getElem?_setIfInBounds]
    by_cases hjk : j = k
    · subst hjk
      have : 4 + p + j < P'.size := by rw [h.size]; exact hk
      simp [this]
    · have := h.zero j (by omega)
      unfold U at this
      simp only [show ¬ (4 + p + k = 4 + p + j) by omega, ↓reduceIte]
      exact this
  other := by
    intro q hq hq'
    rw [Array.getElem?_setIfInBounds]
    simp only [show ¬ (4 + p + k = q) by omega, ↓reduceIte]
    exact h.other q hq (by omega)

end Vbcf.Proof
