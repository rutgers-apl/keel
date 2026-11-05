import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay1
import Vbcf.Proof.Builders

/-!
# Vbcf proofs: the step loop's invariant (pure part)

Definitions and pure lemmas for `ck_step` and `ck_run`:

* `getFacts` on a list of in-range indices; `offs` under a pool extension;
* `RulesKeepFacts`: the Lean rules do not touch the fact array (a hypothesis
  about `Bcf.applyRule`, see the report);
* `SInv`, the invariant between steps: `RInv` plus the fact array, the proof
  block's step section, the remaining steps (`StepsAt`) and the soundness
  invariant `Inv` of the Lean checker (used to show the pool only grows);
* transfer lemmas for the stores `ck_step` and `ck_run` perform.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## `getFacts` -/

theorem getFacts_map (facts : Array Nat) :
    ∀ l : List Nat, (∀ k ∈ l, k < facts.size) →
      getFacts facts l = some (l.map (fun k => facts[k]!)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons k rest ih =>
    intro h
    have hk : k < facts.size := h k (List.mem_cons_self)
    have := ih (fun k' h' => h k' (List.mem_cons_of_mem _ h'))
    simp only [getFacts, this, Array.getElem?_eq_getElem hk, List.map_cons]
    rw [getElem!_pos facts k hk]

theorem getFacts_length {facts : Array Nat} {l prems : List Nat} (h : getFacts facts l = some prems) :
    prems.length = l.length := by
  induction l generalizing prems with
  | nil => simp [getFacts] at h; subst h; rfl
  | cons k rest ih =>
    simp only [getFacts] at h
    split at h
    · rename_i f fs hf hfs
      simp only [Option.some.injEq] at h; subst h
      simp [ih hfs]
    · simp at h

/-! ## `offs` under extension of the pool -/

theorem offs_prefix {p p' : Pool} (h : ∀ j, j < p.size → p'[j]? = p[j]?) {i : Nat}
    (hi : i ≤ p.size) : offs p' i = offs p i := by
  unfold offs
  have : p'.toList.take i = p.toList.take i := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_take, Array.getElem?_toList]
    by_cases hj : j < i
    · simp only [hj, ↓reduceIte]; exact h j (by omega)
    · simp [hj]
  rw [this]

theorem size_le_of_prefix {p p' : Pool} (h : ∀ j, j < p.size → p'[j]? = p[j]?) :
    p.size ≤ p'.size := by
  by_cases hz : p.size = 0
  · omega
  · have h1 := h (p.size - 1) (by omega)
    have h2 : p[p.size - 1]? = some p[p.size - 1] := Array.getElem?_eq_getElem (by omega)
    rw [h2] at h1
    have := lt_size_of_getElem? h1
    omega

/-! ## The rules keep the facts

The Lean rules only change the state through `pushNode`, which keeps `facts`;
but no lemma in `Bcf` states this for `applyRule`, and `RuleSpec` does not
carry it either.  It is needed by the step loop (the C fact array must stay the
image of the Lean fact array), so it is taken as a hypothesis here. -/

def RulesKeepFacts : Prop :=
  ∀ (g : Nat) (bi : Builtins) (ei : EI) (st : St) (r : Rule) (prems params : List Nat) (st' : St)
    (f : Nat), applyRule rwTable g bi ei st r prems params = some (st', f) → st'.facts = st.facts

/-! ## The invariant between steps -/

/-- The replay context of a loaded proof with `nL` loaded nodes (no floor). -/
def runCtx (ws : Array (BitVec 32)) (pm : Nat → Option Nat) (g tt ff nL : Nat) : Ctx :=
  ⟨posOfW (wordFn ws), pm, g, ⟨tt, ff⟩, nL, none⟩

/-- The context of a step started in view `S`: its rule must extend `S`. -/
def Ctx.flr (X : Ctx) (S : VSt) : Ctx := { X with fl := some S }

@[simp] theorem Ctx.flr_posOf (X : Ctx) (S : VSt) : (X.flr S).posOf = X.posOf := rfl
@[simp] theorem Ctx.flr_ei (X : Ctx) (S : VSt) : (X.flr S).ei = X.ei := rfl
@[simp] theorem Ctx.flr_goal (X : Ctx) (S : VSt) : (X.flr S).goal = X.goal := rfl
@[simp] theorem Ctx.flr_bi (X : Ctx) (S : VSt) : (X.flr S).bi = X.bi := rfl

/-- `RInv` only depends on the floor through `RInv.floor`. -/
theorem RInv.reFloor {W : World} {X X' : Ctx} {c : CMem} {S : VSt} (h : RInv W X c S)
    (e1 : X'.posOf = X.posOf) (e2 : X'.ei = X.ei) (e3 : X'.goal = X.goal) (e4 : X'.bi = X.bi)
    (hf : ∀ S0, X'.fl = some S0 → VExt S0 S) : RInv W X' c S := by
  obtain ⟨posOf, ei, goal, bi, nL, fl⟩ := X'
  obtain ⟨posOf', ei', goal', bi', nL', fl'⟩ := X
  simp only at e1 e2 e3 e4 hf
  subst e1 e2 e3 e4
  exact ⟨h.core, h.poolPtr, h.ttNode, h.ffNode, h.tt, h.ff, h.goal, h.proofPtr, h.nexpr,
    h.nexprBound, h.ei, h.eiOut, h.premPtr, h.premSize, h.premCells, hf⟩

/-- Between two steps of the replay loop: the C state at offset `off` of the step
section, with `rest` the steps still to replay, represents the view `st`.  A fact
whose last citing step (`lr`) is not yet past is live, with its id in `facts`;
the `nL` loaded nodes are live and stay in the C pool's prefix `[0, lo)`. -/
structure SInv (W : World) (ws : Array (BitVec 32)) (X : Ctx) (c : CMem) (st : VSt) (off : Nat)
    (rest : List Step) : Prop where
  inv : RInv W X c st
  noFloor : X.fl = none
  wsz : ws.size < 2 ^ 32
  nexpr : c.k.nexpr.toNat = wordFn ws 1
  hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size
  proofSize : c.proof.size = ws.size
  words : ∀ q, (q < 3 ∨ 3 + wordFn ws 1 ≤ q) → q < ws.size → U c.proof q (wordFn ws q)
  factsPtr : ∃ b, c.k.facts = some (b, 0)
  flen : c.k.flen.toNat = st.facts.size
  factsSize : st.facts.size + rest.length = c.facts.size
  fcap : c.k.fcap.toNat = c.facts.size
  factsCells : ∀ j, j < c.facts.size → ∃ w, w < 2 ^ 32 ∧ U c.facts j w
  lrPtr : ∃ b, c.k.lr = some (b, 0)
  lrSize : c.lr.size = c.facts.size
  lrCells : ∀ j, j < c.lr.size → ∃ w, w < 2 ^ 32 ∧ U c.lr j w
  facts : ∀ (j f : Nat), st.facts[j]? = some f → f < st.pool.size ∧
    ∀ w, w < 2 ^ 32 → U c.lr j w → c.k.flen.toNat ≤ w → st.lv f ∧ U c.facts j (st.id f)
  loaded : ∀ i, i < X.nL → st.lv i ∧ st.σ i < X.nL
  nLcs : X.nL ≤ st.cs.pool.size
  lo : c.k.lo.toNat = offs st.cs.pool X.nL
  ttL : X.bi.tt < X.nL
  ffL : X.bi.ff < X.nL
  goalL : X.goal < X.nL
  eiL : ∀ p i, X.ei p = some i → i < X.nL
  steps : StepsAt (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) off rest
  sound : ∀ ρ, holds st.pool ρ X.goal → ∀ (k f : Nat), st.facts[k]? = some f → holds st.pool ρ f

theorem SInv.factsLt {W : World} {ws : Array (BitVec 32)} {X : Ctx} {c : CMem} {st : VSt}
    {off : Nat} {rest : List Step} (h : SInv W ws X c st off rest) : c.facts.size < 2 ^ 32 := by
  rw [← h.fcap]; exact c.k.fcap.isLt

/-- The Lean checker's soundness invariant, from the step invariant. -/
theorem SInv.leanInv {W : World} {ws : Array (BitVec 32)} {X : Ctx} {c : CMem} {st : VSt}
    {off : Nat} {rest : List Step} (h : SInv W ws X c st off rest) : Inv st.pool X.goal X.bi st where
  tys := st.ok.tys
  ext := fun _ _ => rfl
  size := Nat.le_refl _
  goal := st.lt h.inv.goal.1
  tt := h.inv.ttNode
  ff := h.inv.ffNode
  facts := fun k f hf => (h.facts k f hf).1
  sound := h.sound

/-- What one step of the Lean replay yields, from the step invariant: the pool
only grows, the new fact is in range, and the soundness invariant is kept. -/
theorem SInv.leanStep {W : World} {ws : Array (BitVec 32)} {X : Ctx} {c : CMem} {st : VSt}
    {off : Nat} {rest : List Step} (h : SInv W ws X c st off rest) {idxs prems params : List Nat}
    {r : Rule} {st' : St} {f : Nat} (hp : getFacts st.facts idxs = some prems)
    (ha : applyRule rwTable X.goal X.bi X.ei st r prems params = some (st', f)) :
    (∀ j, j < st.pool.size → st'.pool[j]? = st.pool[j]?) ∧ st.pool.size ≤ st'.pool.size ∧
    f < st'.pool.size ∧
    (∀ ρ, holds st'.pool ρ X.goal → ∀ (k f' : Nat), (st'.facts.push f)[k]? = some f' →
      holds st'.pool ρ f') := by
  have hinv := h.leanInv
  obtain ⟨hinv', hent⟩ := applyRule_sound rwTable_sound ha hinv (getFacts_entails hinv hp)
  have hinv'' := hinv'.addFact hent
  exact ⟨hinv'.ext, hinv'.size, hent.1, hinv''.sound⟩

/-! ## Transfer of `RInv` across the stores of the step loop -/

section
variable {W : World} {X : Ctx} {c : CMem} {st : VSt}

/-- `CoreInv` for a C state that differs only in fields it does not mention. -/
theorem CoreInv.sameStep {posOf : Nat → Nat} {c' : CMem} {cs : St} (h : CoreInv posOf c cs)
    (hpool : c'.pool = c.pool) (hhtab : c'.htab = c.htab) (hstk : c'.stk = c.stk)
    (hk : c'.k.pool = c.k.pool ∧ c'.k.plen = c.k.plen ∧ c'.k.pcap = c.k.pcap ∧
      c'.k.htab = c.k.htab ∧ c'.k.hcap = c.k.hcap ∧ c'.k.hcnt = c.k.hcnt ∧
      c'.k.stk = c.k.stk ∧ c'.k.scap = c.k.scap) (hsp : c'.k.sp.toNat ≤ c'.k.scap.toNat) :
    CoreInv posOf c' cs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hk
  refine ⟨h.ok, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, h.posInj⟩
  · rw [h1, h3]; exact h.poolNull
  · rw [h1, h3, hpool]; exact h.poolSize
  · rw [h2, h3]; exact h.poolCap
  · rw [h2, hpool]; exact h.rep
  · rw [h4]; exact h.htabPtr
  · rw [hhtab, h5, h6]; exact h.htab
  · rw [h7, h8]; exact h.stk.null
  · rw [h7, h8, hstk]; exact h.stk.size
  · rw [h8]; exact ⟨by rw [← h8]; exact hsp, h.stk.cap.2⟩

/-- `RInv` for a C state that differs only in the fact array, `flen`, `fcap`, the
work counter, the error flag, `sp` (still within the stack), the parameter pointer
and the premise buffer (still 256 initialised cells). -/
theorem RInv.same {c' : CMem} (h : RInv W X c st)
    (hpool : c'.pool = c.pool) (hhtab : c'.htab = c.htab) (hstk : c'.stk = c.stk)
    (hproof : c'.proof = c.proof)
    (hk : c'.k.pool = c.k.pool ∧ c'.k.plen = c.k.plen ∧ c'.k.pcap = c.k.pcap ∧
      c'.k.htab = c.k.htab ∧ c'.k.hcap = c.k.hcap ∧ c'.k.hcnt = c.k.hcnt ∧
      c'.k.stk = c.k.stk ∧ c'.k.scap = c.k.scap)
    (hk2 : c'.k.tt = c.k.tt ∧ c'.k.ff = c.k.ff ∧ c'.k.goal = c.k.goal ∧
      c'.k.proof = c.k.proof ∧ c'.k.nexpr = c.k.nexpr ∧ c'.k.prem = c.k.prem)
    (hsp : c'.k.sp.toNat ≤ c'.k.scap.toNat)
    (hprem : c'.prem.size = 256 ∧ ∀ j, j < 256 → ∃ w, w < 2 ^ 32 ∧ U c'.prem j w) :
    RInv W X c' st := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hk2
  refine ⟨⟨h.core.cinv.sameStep hpool hhtab hstk hk hsp, h.core.fitsAll⟩, ?_, h.ttNode, h.ffNode,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hprem.1, hprem.2, h.floor⟩
  · rw [hk.1]; exact h.poolPtr
  · rw [e1]; exact h.tt
  · rw [e2]; exact h.ff
  · rw [e3]; exact h.goal
  · rw [e4]; exact h.proofPtr
  · rw [e5, hproof]; exact h.nexpr
  · rw [e5]; exact h.nexprBound
  · rw [e5, hproof]; exact h.ei
  · rw [e5]; exact h.eiOut
  · rw [e6]; exact h.premPtr

end

/-! ## The initial instance, from `ScanDone` -/

/-- `RInv` for the identity view of the loaded state. -/
theorem RInv0.toRInv {W : World} {X : Ctx} {c : CMem} {st : St} (h : RInv0 W X c st)
    (hfl : X.fl = none) : RInv W X c (VSt.init st h.core.ok) where
  core := ⟨h.core, fun i n hn => h.core.rep.fits i n hn⟩
  poolPtr := h.poolPtr
  ttNode := h.ttNode
  ffNode := h.ffNode
  tt := ⟨lt_size_of_getElem? h.ttNode, h.tt⟩
  ff := ⟨lt_size_of_getElem? h.ffNode, h.ff⟩
  goal := h.goal
  proofPtr := h.proofPtr
  nexpr := h.nexpr
  nexprBound := h.nexprBound
  ei := h.ei
  eiOut := h.eiOut
  premPtr := h.premPtr
  premSize := h.premSize
  premCells := h.premCells
  floor := fun S0 h0 => by rw [hfl] at h0; cases h0

/-- The step invariant's `RInv0` part, from `ScanDone`. -/
theorem RInv0.ofScan {W : World} {ws : Array (BitVec 32)} {c : CMem} {tt ff : Nat} {st1 st2 : St}
    {pm : Nat → Option Nat} {D : Nat} {steps : List Step} {gpos g : Nat} {m : Mem} {sb : Nat}
    (hS : ScanDone W ws c tt ff st1 st2 pm D steps gpos g) (h : Holds W m sb c) (nL : Nat) :
    RInv0 W (runCtx ws pm g tt ff nL) c st2 := by
  have hld := hS.ld
  have hg : g < st2.pool.size := hld.load.pm_lt hS.goal
  exact
    { core := hld.core
      poolPtr := hld.core.poolPtr_of_nonempty h (by have := lt_size_of_getElem? hld.ttNode; omega)
      ttNode := hld.ttNode
      ffNode := hld.ffNode
      tt := hld.tt
      ff := hld.ff
      goal := ⟨hg, hS.goalFld⟩
      proofPtr := hld.proofPtr
      nexpr := by rw [hld.nexpr, hld.proofSize]; have := hld.hlen; omega
      nexprBound := by rw [hld.nexpr]; have := hld.hlen; have := hld.psize; have := hld.proofSize; omega
      ei := by
        intro p hp
        rw [hld.nexpr] at hp
        have hm := hld.map p hp
        cases hpm : pm p with
        | none =>
          rw [hpm] at hm
          exact ⟨0, by omega, hm, by simp [runCtx, hpm]⟩
        | some i =>
          rw [hpm] at hm
          have := hld.core.off_lt (hld.load.pm_lt hpm)
          exact ⟨offs st2.pool i + 1, by omega, hm, by simp [runCtx, hpm]; exact hld.load.pm_lt hpm⟩
      eiOut := by
        intro p hp
        rw [hld.nexpr] at hp
        exact hld.load.pm_none hp
      premPtr := hld.prem.ptr
      premSize := hld.prem.size
      premCells := hld.prem.cells }

theorem SInv.ofScan {W : World} {ws : Array (BitVec 32)} {c : CMem} {tt ff : Nat} {st1 st2 : St}
    {pm : Nat → Option Nat} {D : Nat} {steps : List Step} {gpos g : Nat} {m : Mem} {sb : Nat}
    (hS : ScanDone W ws c tt ff st1 st2 pm D steps gpos g) (h : Holds W m sb c)
    (hwsz : ws.size < 2 ^ 32) :
    SInv W ws (runCtx ws pm g tt ff st2.pool.size) c (VSt.init st2 hS.ld.core.ok) 0 steps := by
  have hld := hS.ld
  have hinv0 := RInv0.ofScan hS h st2.pool.size
  have hg : g < st2.pool.size := hld.load.pm_lt hS.goal
  refine
    { inv := hinv0.toRInv rfl
      noFloor := rfl
      wsz := hwsz
      nexpr := hld.nexpr
      hlen := hld.hlen
      proofSize := hld.proofSize
      words := hld.rest
      factsPtr := hS.factsPtr
      flen := by simp only [VSt.init_toSt]; rw [hld.flen, hld.noFacts]; rfl
      factsSize := by simp only [VSt.init_toSt]; rw [hld.noFacts, hS.factsSize]; simp
      fcap := by rw [hS.fcap, hS.factsSize]
      factsCells := by rw [hS.factsSize]; exact hS.factsCells
      lrPtr := hS.lrPtr
      lrSize := by rw [hS.lrSize, hS.factsSize]
      lrCells := by rw [hS.lrSize]; exact hS.lrCells
      facts := by intro j f hf; simp only [VSt.init_toSt] at hf; rw [hld.noFacts] at hf; simp at hf
      loaded := fun i hi => ⟨hi, hi⟩
      nLcs := Nat.le_refl _
      lo := by rw [hld.lo, hld.core.rep.len]; rfl
      ttL := lt_size_of_getElem? hld.ttNode
      ffL := lt_size_of_getElem? hld.ffNode
      goalL := hg
      eiL := fun p i h => hld.load.pm_lt h
      steps := scanSteps_stepsAt _ _ _ _ _ _ _ hS.scan
      sound := by
        intro ρ _ k f hf; simp only [VSt.init_toSt] at hf; rw [hld.noFacts] at hf; simp at hf }

end Vbcf.Proof
