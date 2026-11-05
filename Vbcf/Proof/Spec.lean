import EmbC.Kernel
import Vbcf.Prog
import Bcf.Check
import Vbcf.Enc
import Vbcf.Proof.Mem
import Vbcf.Proof.PushSpec

/-!
# Vbcf proofs: how the C state represents the Lean checker's state

The refinement relation, as definitions only.  `CoreInv` relates the C pool,
hash table and scratch stack to a Lean `Bcf.St`.  The C pool is a *function*
of the Lean pool: node `i` of the Lean pool occupies the words
`nodeW posOf pool n` starting at offset `offs pool i`.

Lemmas about these definitions are in `Vbcf/Proof/EncLemmas.lean`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ## Layout of the pool -/

/-- Words occupied by a node. -/
def nodeSize (n : Node) : Nat := 1 + tailLen n

/-- Offset of node `i`: the id the C checker uses for it. -/
def offs (pool : Pool) (i : Nat) : Nat := ((pool.toList.take i).map nodeSize).sum

/-- The words of node `n` in the C pool. -/
def nodeW (posOf : Nat → Nat) (pool : Pool) (n : Node) : List Nat :=
  hdrW n :: tailW posOf (offs pool) n

/-- The node's parameters and arity fit the 8-bit header fields, and its leaf
words (a variable's position, a literal's value words) fit 32 bits.  Child ids
are not constrained here (they are mapped to 0): what the C pool stores for a
child is an offset, bounded by the pool's size. -/
def Fits (posOf : Nat → Nat) (n : Node) : Prop :=
  opLo n.op < 256 ∧ opHi n.op < 256 ∧ tailLen n < 256 ∧
  ∀ w ∈ tailW posOf (fun _ => 0) n, w < 2 ^ 32

/-- Cell `i` holds the 32-bit word `w`. -/
def U (cells : Array EmbC.Val) (i : Nat) (w : Nat) : Prop :=
  cells[i]? = some (.u32 (BitVec.ofNat 32 w))

/-- The cells from `at` on hold exactly the words `ws`. -/
def WordsAt (cells : Array EmbC.Val) (start : Nat) (ws : List Nat) : Prop :=
  ∀ (k : Nat) (w : Nat), ws[k]? = some w → U cells (start + k) w

/-- `cells[0..plen)` is the C image of the Lean pool. -/
structure PoolRep (posOf : Nat → Nat) (pool : Pool) (cells : Array EmbC.Val) (plen : Nat) : Prop where
  len : plen = offs pool pool.size
  fits : ∀ (i : Nat) (n : Node), pool[i]? = some n → Fits posOf n
  cell : ∀ (i : Nat) (n : Node), pool[i]? = some n → WordsAt cells (offs pool i) (nodeW posOf pool n)

/-- The C encoding of a type, as computed by `ty_of`. -/
def tyW : Bcf.Ty → Nat
  | .bv w => w
  | .bool => 0x1000
  | .list e n => 0x2000 + (if e then 1 else 0) * 256 + n

/-- Position in the input of the raw node with dense index `d`.  Past the end
of the raw pool it keeps growing by one, so it is injective on all of `Nat`. -/
def posOfRaw (raw : Pool) (d : Nat) : Nat :=
  ((raw.toList.take d).map (fun n => 1 + (match n.op with
    | .bvVal w _ => (w + 31) / 32
    | _ => n.args.size))).sum + (d - raw.size)

/-! ## The hash table -/

/-- The C hash of a word sequence (`ck_hash`). -/
def hashW (ws : List (BitVec 32)) : BitVec 32 :=
  let h := ws.foldl (fun h w => (h ^^^ w) * 0x01000193#32) 0x811c9dc5#32
  let h := h ^^^ (h >>> 15)
  let h := h * 0x2c1b3c6d#32
  h ^^^ (h >>> 12)

def hashNode (posOf : Nat → Nat) (pool : Pool) (n : Node) : BitVec 32 :=
  hashW ((nodeW posOf pool n).map (BitVec.ofNat 32))

/-- Number of occupied slots of a table. -/
def nzCount (htab : Array EmbC.Val) : Nat := htab.toList.countP (fun v => v != EmbC.Val.u32 0#32)

/-- The open-addressing table: every slot is 0 or one more than a node's
offset, every node is reachable from its hash by stepping over occupied
slots only, and the count field is the number of occupied slots (which
`ck_hgrow` recomputes; without `nz` a node could sit in two slots). -/
structure HtabOK (posOf : Nat → Nat) (pool : Pool) (htab : Array EmbC.Val) (hcap hcnt : Nat) : Prop where
  size : htab.size = hcap
  pow : ∃ j, hcap = 2 ^ j ∧ j ≤ 30
  cnt : hcnt = pool.size
  nz : nzCount htab = hcnt
  load : 2 * pool.size ≤ hcap
  cell : ∀ s, s < hcap → ∃ e : Nat, U htab s e ∧ e < 2 ^ 32 ∧
    (e ≠ 0 → ∃ i, i < pool.size ∧ e = offs pool i + 1)
  find : ∀ (i : Nat) (n : Node), pool[i]? = some n →
    ∃ d, d < hcap ∧ U htab (((hashNode posOf pool n).toNat + d) % hcap) (offs pool i + 1) ∧
      ∀ d', d' < d → ¬ U htab (((hashNode posOf pool n).toNat + d') % hcap) 0

/-! ## The core invariant -/

def maxPool : Nat := 0x40000000

/-- The scratch stack is well-formed: not yet allocated and empty, or a
block of `scap` cells with `sp ≤ scap`. -/
structure StkOK (c : CMem) : Prop where
  null : c.k.stk = none → c.k.scap = 0
  size : ∀ b o, c.k.stk = some (b, o) → c.stk.size = c.k.scap.toNat
  cap : c.k.sp.toNat ≤ c.k.scap.toNat ∧ c.k.scap.toNat ≤ 2 * maxPool

/-- `c'` differs from `c` only in the scratch stack, the work counter and the
error flag. -/
structure StkFrame (c c' : CMem) : Prop where
  pool : c'.pool = c.pool
  htab : c'.htab = c.htab
  facts : c'.facts = c.facts
  prem : c'.prem = c.prem
  proof : c'.proof = c.proof
  poolPtr : c'.k.pool = c.k.pool
  plen : c'.k.plen = c.k.plen
  pcap : c'.k.pcap = c.k.pcap
  htabPtr : c'.k.htab = c.k.htab
  hcap : c'.k.hcap = c.k.hcap
  hcnt : c'.k.hcnt = c.k.hcnt
  factsPtr : c'.k.facts = c.k.facts
  flen : c'.k.flen = c.k.flen
  fcap : c'.k.fcap = c.k.fcap
  premPtr : c'.k.prem = c.k.prem
  par : c'.k.par = c.k.par
  proofPtr : c'.k.proof = c.k.proof
  nexpr : c'.k.nexpr = c.k.nexpr
  tt : c'.k.tt = c.k.tt
  ff : c'.k.ff = c.k.ff
  goal : c'.k.goal = c.k.goal
  val : c'.k.val = c.k.val
  lr : c'.lr = c.lr
  lrPtr : c'.k.lr = c.k.lr
  lo : c'.k.lo = c.k.lo
  live : c'.k.live = c.k.live

/-- The part of the invariant that the pool builders need and maintain. -/
structure CoreInv (posOf : Nat → Nat) (c : CMem) (st : St) : Prop where
  ok : PoolOK st
  poolNull : c.k.pool = none → c.k.pcap = 0
  poolSize : ∀ b o, c.k.pool = some (b, o) → c.pool.size = c.k.pcap.toNat
  poolCap : c.k.plen.toNat ≤ c.k.pcap.toNat ∧ c.k.pcap.toNat ≤ maxPool
  rep : PoolRep posOf st.pool c.pool c.k.plen.toNat
  htabPtr : ∃ b, c.k.htab = some (b, 0)
  htab : HtabOK posOf st.pool c.htab c.k.hcap.toNat c.k.hcnt.toNat
  stk : StkOK c
  posInj : ∀ a b, posOf a = posOf b → a = b

theorem CoreInv.wev {posOf : Nat → Nat} {c : CMem} {st : St} {wk er : BitVec 32} {vl : BitVec 64}
    (hc : CoreInv posOf c st) : CoreInv posOf (c.wev wk er vl) st :=
  ⟨hc.ok, hc.poolNull, hc.poolSize, hc.poolCap, hc.rep, hc.htabPtr, hc.htab,
    ⟨hc.stk.null, hc.stk.size, hc.stk.cap⟩, hc.posInj⟩

theorem CoreInv.setMem {posOf : Nat → Nat} {c : CMem} {st : St} {mm : BitVec 32}
    (hc : CoreInv posOf c st) : CoreInv posOf (c.setMem mm) st :=
  ⟨hc.ok, hc.poolNull, hc.poolSize, hc.poolCap, hc.rep, hc.htabPtr, hc.htab,
    ⟨hc.stk.null, hc.stk.size, hc.stk.cap⟩, hc.posInj⟩

/-- `c'` differs from `c` only in the pool, the hash table, the work counter
and the error flag. -/
structure PoolFrame (c c' : CMem) : Prop where
  stk : c'.stk = c.stk
  facts : c'.facts = c.facts
  prem : c'.prem = c.prem
  proof : c'.proof = c.proof
  stkPtr : c'.k.stk = c.k.stk
  sp : c'.k.sp = c.k.sp
  scap : c'.k.scap = c.k.scap
  factsPtr : c'.k.facts = c.k.facts
  flen : c'.k.flen = c.k.flen
  fcap : c'.k.fcap = c.k.fcap
  premPtr : c'.k.prem = c.k.prem
  par : c'.k.par = c.k.par
  proofPtr : c'.k.proof = c.k.proof
  nexpr : c'.k.nexpr = c.k.nexpr
  tt : c'.k.tt = c.k.tt
  ff : c'.k.ff = c.k.ff
  goal : c'.k.goal = c.k.goal
  val : c'.k.val = c.k.val
  lr : c'.lr = c.lr
  lrPtr : c'.k.lr = c.k.lr
  lo : c'.k.lo = c.k.lo
  live : c'.k.live = c.k.live

/-- A candidate node `n` has been written at the tail of the pool. -/
structure Cand (posOf : Nat → Nat) (c : CMem) (st : St) (n : Node) : Prop where
  fits : Fits posOf n
  room : c.k.plen.toNat + nodeSize n ≤ c.k.pcap.toNat
  words : WordsAt c.pool c.k.plen.toNat (nodeW posOf st.pool n)
  args : n.args.all (· < st.pool.size) = true

end Vbcf.Proof
