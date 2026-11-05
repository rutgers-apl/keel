import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Specs

/-!
# Vbcf proofs: reading nodes

Small lemmas that turn the C's header tests and index arithmetic into facts
about the Lean node, in the shapes `simp` meets them.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- `(hdr & 0xff) == CODE` on the header of a node. -/
theorem code_eq_iff {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) (k : Nat) (hk : k < 256) :
    (BitVec.ofNat 32 (hdrW n) &&& 255#32 = BitVec.ofNat 32 k) ↔ opC n.op = k := by
  rw [← BitVec.toNat_inj, bv_and_ff, bv_toNat_ofNat (hdrW_lt hf), hdrW_code hf,
    bv_toNat_ofNat (by omega)]

/-- An index `n + k` computed in 32 bits. -/
theorem idx_add {n k : Nat} (h : n + k < 2 ^ 32) :
    (BitVec.ofNat 32 n + BitVec.ofNat 32 k).toNat = n + k := by
  rw [BitVec.toNat_add, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]
  exact Nat.mod_eq_of_lt h

/-- Comparing a computed id with a stored one. -/
theorem ofNat_eq_iff {n : Nat} {x : BitVec 32} (h : n < 2 ^ 32) :
    BitVec.ofNat 32 n = x ↔ n = x.toNat := by
  rw [← BitVec.toNat_inj, bv_toNat_ofNat h]

section
variable {W : World} {X : Ctx} {c : CMem} {st : St}

/-- Every node id is below `2^30`. -/
theorem CoreInv.off_lt {posOf : Nat → Nat} (hc : CoreInv posOf c st) {i : Nat} (hi : i < st.pool.size) :
    offs st.pool i < 2 ^ 30 := by
  have h1 := hc.rep.offs_lt hi
  have h2 := hc.poolCap
  simp only [maxPool] at h2
  omega

theorem CoreInv.node_end_lt {posOf : Nat → Nat} (hc : CoreInv posOf c st) {i : Nat} {n : Node}
    (hn : st.pool[i]? = some n) : offs st.pool i + nodeSize n ≤ 2 ^ 30 := by
  have h1 := hc.rep.node_end hn
  have h2 := hc.poolCap
  simp only [maxPool] at h2
  omega

/-- The node at a valid index. -/
theorem node_of_lt {i : Nat} (hi : i < st.pool.size) : ∃ n, st.pool[i]? = some n :=
  ⟨st.pool[i], by simp [hi]⟩

end

/-! ## Through a view -/

/-- Closes a liveness side condition `st.lv i` (used as an auto-parameter). -/
macro "vlv" : tactic =>
  `(tactic| first
    | assumption
    | fail "vlv: liveness side condition not closed")

/-- The node at a live index. -/
theorem node_of_lv {S : VSt} {i : Nat} (hi : S.lv i) : ∃ n, S.pool[i]? = some n :=
  S.node_of_lv hi

section
variable {posOf : Nat → Nat} {c : CMem} {S st : VSt}

/-- Every id of a live node is below `2^30`. -/
theorem VInv.off_lt (hc : VInv posOf c S) {i : Nat} (hi : S.lv i) : S.id i < 2 ^ 30 :=
  hc.cinv.off_lt (S.σ_lt hi)

theorem VInv.node_end_lt (hc : VInv posOf c S) {i : Nat} {n : Node} (hn : S.pool[i]? = some n)
    (hi : S.lv i := by vlv) : S.id i + nodeSize n ≤ 2 ^ 30 := by
  have := hc.cinv.node_end_lt (S.img i n hi hn)
  rwa [nodeSize_ren] at this

theorem VInv.ok (_hc : VInv posOf c st) : PoolOK st.toSt := st.ok

theorem VInv.stk (hc : VInv posOf c st) : StkOK c := hc.cinv.stk

/-- The node-level facts (`fits`, `hdr`, `tail`, `arg`). -/
theorem VInv.rep (hc : VInv posOf c st) : VInv posOf c st := hc

theorem VInv.fits (hc : VInv posOf c st) (i : Nat) (n : Node) (hn : st.pool[i]? = some n) :
    Fits posOf n := hc.fitsAll i n hn

theorem VInv.hdr (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    (hi : st.lv i := by vlv) : U c.pool (st.id i) (hdrW n) := by
  have := hc.cinv.rep.hdr (st.img i n hi hn)
  rwa [hdrW_ren] at this

/-- The general tail word. -/
theorem VInv.tail (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {k w : Nat} (hk : (tailW posOf st.id n)[k]? = some w) (hi : st.lv i := by vlv) :
    U c.pool (st.id i + 1 + k) w :=
  hc.cinv.rep.tail (st.img i n hi hn) (by rw [tailW_ren]; exact hk)

/-- The `k`-th argument word of a non-leaf node is the id of its `k`-th argument. -/
theorem VInv.arg (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    (hl : ¬ IsLeaf n.op) {k : Nat} (hk : k < n.args.size) (hi : st.lv i := by vlv) :
    U c.pool (st.id i + 1 + k) (st.id n.args[k]) :=
  hc.tail hn (tailW_getElem?_of_not_leaf hl hk) hi

end

end Vbcf.Proof
