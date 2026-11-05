import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Goal2
import Vbcf.Proof.Intern
import Vbcf.Proof.RuleLib

/-!
# Vbcf proofs: `ck_goal`, part 3 (frames, reads, the environment, the sweep invariant `MInv`)
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC
set_option autoImplicit false

/-- `RInv0` for a C state that represents the same Lean state (same struct
fields that `RInv0` reads, same proof copy and premise buffer). -/
theorem RInv0.goalFrame {W : World} {X : Ctx} {m : Mem} {sb : Nat} {c c' : CMem} {st : St}
    (hinv : RInv0 W X c st) (h' : Holds W m sb c') (hf : PoolFrame c c')
    (hc' : CoreInv X.posOf c' st) : RInv0 W X c' st :=
  { core := hc'
    poolPtr := hc'.poolPtr_of_nonempty h' (by have := hinv.goal.1; omega)
    ttNode := hinv.ttNode
    ffNode := hinv.ffNode
    tt := by rw [hf.tt]; exact hinv.tt
    ff := by rw [hf.ff]; exact hinv.ff
    goal := by rw [hf.goal]; exact hinv.goal
    proofPtr := by rw [hf.proofPtr]; exact hinv.proofPtr
    nexpr := by rw [hf.nexpr, hf.proof]; exact hinv.nexpr
    nexprBound := by rw [hf.nexpr]; exact hinv.nexprBound
    ei := by rw [hf.nexpr, hf.proof]; exact hinv.ei
    eiOut := by rw [hf.nexpr]; exact hinv.eiOut
    premPtr := by rw [hf.premPtr]; exact hinv.premPtr
    premSize := by rw [hf.prem]; exact hinv.premSize
    premCells := by rw [hf.prem]; exact hinv.premCells }

/-- The arena block, in any state the checker reaches. -/
theorem Holds.arena {W : World} {m : Mem} {sb : Nat} {c : CMem} {gb : Nat}
    {gws : Array (BitVec 32)} {G : Nat} (h : Holds W m sb c) (ha : ArenaOK W gb gws G) :
    HasArr m gb (gws.map EmbC.Val.u32) := by
  unfold HasArr
  rw [h.out gb ha.old ha.notProof]
  exact ha.block

theorem arena_cell {gws : Array (BitVec 32)} {i : Nat} (hi : i < gws.size) :
    (gws.map EmbC.Val.u32)[i]? = some (.u32 gws[i]!) := by
  simp [hi]

theorem wordFn_toNat {gws : Array (BitVec 32)} (i : Nat) : (gws[i]!).toNat = wordFn gws i := rfl

/-- The postcondition of `ck_goal`, named. -/
def GoalPost (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : St) (gws : Array (BitVec 32))
    (goal : BitVec 32) : Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ RInv0 W X c' st ∧
    StepFrame c c' ∧ (r ≠ 0#32 → GoalOK st.pool (wordFn gws) X.goal goal.toNat)

/-- The local environment of `ck_goal`. -/
def genv (sb gb : Nat) (goal n base sbase j q m ci ah ph code vlen k a pa pv ok : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("gx", .ptr .u32, .ptr gb 0), ("goal", .u32, .u32 goal),
   ("n", .u32, .u32 n), ("base", .u32, .u32 base), ("sbase", .u32, .u32 sbase),
   ("j", .u32, .u32 j), ("q", .u32, .u32 q), ("m", .u32, .u32 m), ("ci", .u32, .u32 ci),
   ("ah", .u32, .u32 ah), ("ph", .u32, .u32 ph), ("code", .u32, .u32 code),
   ("vlen", .u32, .u32 vlen), ("k", .u32, .u32 k), ("a", .u32, .u32 a), ("pa", .u32, .u32 pa),
   ("pv", .u32, .u32 pv), ("ok", .u32, .u32 ok)]


/-- What is known after `ck_room` succeeded and the locals `n`, `base`, `sbase` are set. -/
structure GFacts (W : World) (sb gb pb : Nat) (c1 : CMem) (X : Ctx) (st : St)
    (gws : Array (BitVec 32)) (goal nv sbv : BitVec 32) : Prop where
  core : CoreInv X.posOf c1 st
  pool : c1.k.pool = some (pb, 0)
  psize : c1.pool.size = c1.k.pcap.toNat
  room : c1.k.plen.toNat + nv.toNat ≤ c1.k.pcap.toNat
  nv : nv.toNat = goal.toNat + 1 + c1.k.nexpr.toNat
  sbv : sbv.toNat = c1.k.plen.toNat + goal.toNat + 1
  arena : ArenaOK W gb gws goal.toNat
  gidx : X.goal < st.pool.size
  gfield : c1.k.goal.toNat = offs st.pool X.goal

/-- The invariant of the sweep loop. -/
def MInv (W : World) (sb gb : Nat) (c1 : CMem) (X : Ctx) (st : St) (gws : Array (BitVec 32))
    (goal nv sbv : BitVec 32) : Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c2 : CMem) (q m ci ah ph code vlen k a pa pv : BitVec 32) (μ σP : Nat → Option Nat),
    env = genv sb gb goal nv c1.k.plen sbv nv q m ci ah ph code vlen k a pa pv 1#32 ∧
    q.toNat ≤ goal.toNat + 1 ∧ Holds W s.mem sb c2 ∧ TailEq c1 c2 ∧
    SweepOK st.pool gws X.posOf X.goal c1.k.plen.toNat goal.toNat c1.k.nexpr.toNat c2.pool μ σP
      q.toNat


theorem var_tailW {posOf off : Nat → Nat} {n : Node} (hv : opC n.op = 0x18 ∨ opC n.op = 0x19) :
    tailW posOf off n = [posOf (gvid n.op)] := by
  rcases n with ⟨op, args⟩
  rcases hv with hv | hv
  · obtain ⟨w, d, e⟩ := opC_bvVar_iff.mp hv
    simp only at e; subst e; rfl
  · obtain ⟨d, e⟩ := opC_boolVar_iff.mp hv
    simp only at e; subst e; rfl

theorem var_isLeaf {op : Op} (hv : opC op = 0x18 ∨ opC op = 0x19) : IsLeaf op := by
  rcases hv with hv | hv
  · obtain ⟨w, d, e⟩ := opC_bvVar_iff.mp hv; subst e; rfl
  · obtain ⟨d, e⟩ := opC_boolVar_iff.mp hv; subst e; rfl

theorem CoreInv.args_nil {posOf : Nat → Nat} {c : CMem} {st : St} (hc : CoreInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) (hl : IsLeaf n.op) : n.args = #[] := by
  obtain ⟨argTys, t, -, ht, -, hlen⟩ := hc.ok.retype hn
  have := resultTy_leaf hl ht
  subst this
  simp at hlen
  exact Array.eq_empty_of_size_eq_zero hlen.symm

theorem bv_add_one_ofNat {x : BitVec 32} {N : Nat} (hx : x.toNat = N) (hN : N + 1 < 2 ^ 32) :
    x + 1#32 = BitVec.ofNat 32 (N + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, bv_toNat_ofNat hN]; simp; omega

end Vbcf.Proof
