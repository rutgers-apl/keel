import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rules
import Vbcf.Proof.Spec
import Vbcf.Proof.EncLemmas
import Vbcf.Proof.View

/-!
# Vbcf proofs: the specification of each C function

Statements only.  Each `…Spec` is a proposition saying what one C function
does, in terms of the refinement relation of `Vbcf/Proof/Spec.lean`.  Proof
files prove these, assuming the specs of the functions they call; the final
assembly discharges the assumptions.

Shape of every specification: from a state satisfying the invariant, the
call never gets stuck (that is part of `FnSpec`), it returns a `u32`, `Holds`
is preserved (so memory ownership is intact even when the call fails), and
*if* it reports success then the Lean checker's corresponding function
succeeds with the corresponding result and the invariant holds again.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-- The `NOID` sentinel. -/
def noid : BitVec 32 := 0xffffffff#32

/-- `u32` value of a natural number. -/
abbrev uv (n : Nat) : EmbC.Val := .u32 (BitVec.ofNat 32 n)

/-! ## Core -/

/-- A candidate at the tail of the pool whose header may be arbitrary (it
may come from the input) but whose words are safe to inspect: the header and
its `vlen` words fit in the allocated pool; for a variable the identity word
is the position of some input variable; for a literal the value words are
there; for anything else the argument words are ids of existing nodes. -/
structure CandRaw (posOf : Nat → Nat) (c : CMem) (st : St) : Prop where
  hdr : ∃ h, h < 2 ^ 32 ∧ U c.pool c.k.plen.toNat h ∧
    c.k.plen.toNat + 1 + h / 256 % 256 ≤ c.k.pcap.toNat ∧
    (h % 256 = 0x18 ∨ h % 256 = 0x19 → h / 256 % 256 = 1 →
      ∃ id, posOf id < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 1) (posOf id)) ∧
    (h % 256 = 0x08 → ∀ k, k < h / 256 % 256 →
      ∃ w, w < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 1 + k) w) ∧
    (h % 256 ≠ 0x18 → h % 256 ≠ 0x19 → h % 256 ≠ 0x08 → h % 256 ≠ 0x09 →
      ∀ k, k < h / 256 % 256 →
        ∃ i, i < st.pool.size ∧ U c.pool (c.k.plen.toNat + 1 + k) (offs st.pool i))

/-- `ty_of(hdr)`: a pure function of the header. `tyOfW` is its model on 32-bit words. -/
def TyOfSpec (tyOfW : BitVec 32 → BitVec 32) : Prop :=
  ∀ (h : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "ty_of"
      (fun vs _ => vs = [.u32 h])
      (fun _ s rv s' => s' = s ∧ rv = some (.u32 (tyOfW h)))

/-- `ck_tyck(st)`: accepts only candidates that are the encoding of a
well-typed node.  Reads only. -/
def TyckSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_tyck"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧ CandRaw posOf c st)
      (fun _ s rv s' => s' = s ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ n, Cand posOf c st n ∧ Typed st n)))

/-- `ck_intern(st)` is `pushNode` on the candidate.  On failure the state
still represents `st`. -/
def InternSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_intern"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧ CandRaw posOf c st)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
        ((r = noid ∧ CoreInv posOf c' st) ∨
         (∃ n st' i, Cand posOf c st n ∧ pushNode st n = some (st', i) ∧
            CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid)))

/-- `ck_room(st, n)`: on success there are `n` free words after `plen`.
The represented pool does not change either way. -/
def RoomSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (n : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_room"
      (fun vs s => vs = [.ptr sb 0, .u32 n] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧ PoolFrame c c' ∧ CoreInv posOf c' st ∧
        c'.k.plen = c.k.plen ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ c.k.plen.toNat + n.toNat ≤ c'.k.pcap.toNat)))

/-- A node-building function called with header `h` (code and parameters,
arity bits zero) and arguments that are the ids of the Lean indices `is`:
on success, the Lean checker's `pushNode` of the node with that header and
those arguments succeeds with the corresponding index. -/
def MkPost (posOf : Nat → Nat) (W : World) (sb : Nat) (c : CMem) (st : St) (h : Nat) (is : List Nat) :
    Option EmbC.Val → (EmbC.KernelState prog State) → Prop := fun rv s' =>
  ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
    ((r = noid ∧ CoreInv posOf c' st) ∨
     (∃ n st' i, hdrW n = h + is.length * 256 ∧ Fits posOf n ∧ n.args = is.toArray ∧
        pushNode st n = some (st', i) ∧ CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid))

/-- Header `h` is the header of a non-leaf node with no arguments yet:
`code | params << 16` with a code other than the four leaf codes. -/
def NonLeafHdr (h : Nat) : Prop :=
  h < 2 ^ 32 ∧ h / 256 % 256 = 0 ∧
  h % 256 ≠ 0x18 ∧ h % 256 ≠ 0x19 ∧ h % 256 ≠ 0x08 ∧ h % 256 ≠ 0x09

def Mk1Spec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h a : BitVec 32) (ia : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk1"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 a] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        NonLeafHdr h.toNat ∧ ia < st.pool.size ∧ a.toNat = offs st.pool ia)
      (fun _ _ => MkPost posOf W sb c st h.toNat [ia])

def Mk2Spec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h a b : BitVec 32)
    (ia ib : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk2"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 a, .u32 b] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ NonLeafHdr h.toNat ∧
        ia < st.pool.size ∧ a.toNat = offs st.pool ia ∧ ib < st.pool.size ∧ b.toNat = offs st.pool ib)
      (fun _ _ => MkPost posOf W sb c st h.toNat [ia, ib])

def Mk3Spec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h a b d : BitVec 32)
    (ia ib id : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk3"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 a, .u32 b, .u32 d] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ NonLeafHdr h.toNat ∧
        ia < st.pool.size ∧ a.toNat = offs st.pool ia ∧ ib < st.pool.size ∧ b.toNat = offs st.pool ib ∧
        id < st.pool.size ∧ d.toNat = offs st.pool id)
      (fun _ _ => MkPost posOf W sb c st h.toNat [ia, ib, id])

/-- The scratch stack holds the ids of the C-side indices `is` from `base` on. -/
def StkIdsC (c : CMem) (st : St) (base : Nat) (is : List Nat) : Prop :=
  ∀ (j : Nat) (i : Nat), is[j]? = some i → i < st.pool.size ∧ U c.stk (base + j) (offs st.pool i)

/-- `mkn(st, hdr, base, n)`: the arguments are `stk[base..base+n)`. -/
def MknSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h base n : BitVec 32)
    (is : List Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mkn"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 base, .u32 n] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ NonLeafHdr h.toNat ∧ is.length = n.toNat ∧
        base.toNat + n.toNat ≤ c.k.sp.toNat ∧ StkIdsC c st base.toNat is)
      (fun _ _ => MkPost posOf W sb c st h.toNat is)

/-- `mk0(st, hdr)` for a boolean literal header (`HDR_TRUE` or `HDR_FALSE`). -/
def Mk0BoolSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (b : Bool),
    EmbC.FnSpec (State := State) Vbcf.prog "mk0"
      (fun vs s => vs = [.ptr sb 0, .u32 (if b then 0x10009#32 else 0x9#32)] ∧
        Holds W s.mem sb c ∧ CoreInv posOf c st)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
        ((r = noid ∧ CoreInv posOf c' st) ∨
         (∃ st' i, pushNode st ⟨.boolVal b, #[]⟩ = some (st', i) ∧
            CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid)))

/-- `mkval(st, w, v)` builds the literal `bvVal w v`.  A literal of width
`≤ 32` is stored in one word, so its value must fit one word (the C stores
the low word only; `MkvalSpec' (State := State)` in `Builders3` states the unconditional
behaviour). -/
def MkvalSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (w : BitVec 32) (v : BitVec 64),
    EmbC.FnSpec (State := State) Vbcf.prog "mkval"
      (fun vs s => vs = [.ptr sb 0, .u32 w, .u64 v] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        (w.toNat ≤ 32 → v.toNat < 2 ^ 32))
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
        ((r = noid ∧ CoreInv posOf c' st) ∨
         (∃ st' i, pushNode st ⟨.bvVal w.toNat v.toNat, #[]⟩ = some (st', i) ∧
            CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid)))

/-- `mk_eq(st, a, b)` is `mkEq`. -/
def MkEqSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (a b : BitVec 32) (ia ib : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk_eq"
      (fun vs s => vs = [.ptr sb 0, .u32 a, .u32 b] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        ia < st.pool.size ∧ a.toNat = offs st.pool ia ∧ ib < st.pool.size ∧ b.toNat = offs st.pool ib)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
        ((r = noid ∧ CoreInv posOf c' st) ∨
         (∃ st' i, Bcf.mkEq st ia ib = some (st', i) ∧
            CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid)))

/-- `mk_not(st, a)` is `mkNot`. -/
def MkNotSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (a : BitVec 32) (ia : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk_not"
      (fun vs s => vs = [.ptr sb 0, .u32 a] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        ia < st.pool.size ∧ a.toNat = offs st.pool ia)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
        ((r = noid ∧ CoreInv posOf c' st) ∨
         (∃ st' i, Bcf.mkNot st ia = some (st', i) ∧
            CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid)))

/-- `find_not(st, a)` is `findNode st ⟨.boolNot, #[ia]⟩`, exactly: it finds
the node if and only if it exists, unless the error flag is set (the work
budget ran out).  Changes only `work` and `err`. -/
def FindNotSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (a : BitVec 32) (ia : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "find_not"
      (fun vs s => vs = [.ptr sb 0, .u32 a] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        ia < st.pool.size ∧ a.toNat = offs st.pool ia)
      (fun _ _ rv s' => ∃ wk er r, rv = some (.u32 r) ∧ Holds W s'.mem sb (c.wev wk er c.k.val) ∧
        (er ≠ 0#32 ∨
         match findNode st ⟨.boolNot, #[ia]⟩ with
         | none => r = noid
         | some i => r.toNat = offs st.pool i ∧ r ≠ noid))

/-! ## Rules

A rule sees the Lean checker's state through a view (`VSt`, `View.lean`): the C
pool represents the view's C-side state, and the ids a rule handles are the
ids `VSt.id` of live Lean indices. -/

/-- What stays fixed while a step is replayed.  `nL` is the number of nodes
loaded from the input (they never move in the C pool).  `fl` is the view when
the step started, if any: a rule only extends it (`RInv.floor`), which is what
lets the step loop keep the facts' ids. -/
structure Ctx where
  posOf : Nat → Nat
  /-- The Lean checker's `ei`: input position to canonical index. -/
  ei : Nat → Option Nat
  goal : Nat
  bi : Builtins
  nL : Nat
  fl : Option VSt

/-- The C memory represents the view's C-side state, and every Lean node has
a header that fits (`Fits` does not look at children). -/
structure VInv (posOf : Nat → Nat) (c : CMem) (st : VSt) : Prop where
  cinv : CoreInv posOf c st.cs
  fitsAll : ∀ (i : Nat) (n : Node), st.pool[i]? = some n → Fits posOf n

/-- The invariant between steps: the core invariant, the built-in nodes and
the goal, the position map stored in the input copy, and the premise buffer. -/
structure RInv (W : World) (X : Ctx) (c : CMem) (st : VSt) : Prop where
  core : VInv X.posOf c st
  poolPtr : ∃ b, c.k.pool = some (b, 0)
  ttNode : st.pool[X.bi.tt]? = some ⟨.boolVal true, #[]⟩
  ffNode : st.pool[X.bi.ff]? = some ⟨.boolVal false, #[]⟩
  tt : st.lv X.bi.tt ∧ c.k.tt.toNat = st.id X.bi.tt
  ff : st.lv X.bi.ff ∧ c.k.ff.toNat = st.id X.bi.ff
  goal : st.lv X.goal ∧ c.k.goal.toNat = st.id X.goal
  proofPtr : c.k.proof = some (W.pb, 0)
  nexpr : 3 + c.k.nexpr.toNat ≤ c.proof.size
  nexprBound : 3 + c.k.nexpr.toNat ≤ 2 ^ 32
  ei : ∀ p, p < c.k.nexpr.toNat → ∃ v, v < 2 ^ 32 ∧ U c.proof (3 + p) v ∧
    match X.ei p with
    | none => v = 0
    | some i => st.lv i ∧ v = st.id i + 1
  eiOut : ∀ p, c.k.nexpr.toNat ≤ p → X.ei p = none
  premPtr : ∃ b, c.k.prem = some (b, 0)
  premSize : c.prem.size = 256
  premCells : ∀ j, j < 256 → ∃ w, w < 2 ^ 32 ∧ U c.prem j w
  floor : ∀ S0, X.fl = some S0 → VExt S0 st

/-- The premise buffer holds the ids of the premises. -/
def PremsAt (c : CMem) (st : VSt) (prems : List Nat) : Prop :=
  prems.length ≤ 255 ∧
  ∀ (j : Nat) (p : Nat), prems[j]? = some p → st.lv p ∧ U c.prem j (st.id p)

/-- `st->par` points at the parameter words of the current step. -/
def ParamsAt (W : World) (c : CMem) (params : List Nat) : Prop :=
  params.length ≤ 255 ∧
  ∃ o, c.k.par = some (W.pb, o) ∧ o + params.length ≤ c.proof.size ∧
    ∀ (j : Nat) (x : Nat), params[j]? = some x → x < 2 ^ 32 ∧ U c.proof (o + j) x

/-- What a rule must leave alone for the step loop. -/
structure StepFrame (c c' : CMem) : Prop where
  facts : c'.facts = c.facts
  factsPtr : c'.k.facts = c.k.facts
  flen : c'.k.flen = c.k.flen
  fcap : c'.k.fcap = c.k.fcap
  proof : c'.proof = c.proof
  nexpr : c'.k.nexpr = c.k.nexpr
  lr : c'.lr = c.lr
  lrPtr : c'.k.lr = c.k.lr
  lo : c'.k.lo = c.k.lo
  live : c'.k.live = c.k.live

/-- `expr_at(st, p)` is `ei p`.  Reads only. -/
def ExprAtSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : VSt) (p : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "expr_at"
      (fun vs s => vs = [.ptr sb 0, .u32 p] ∧ Holds W s.mem sb c ∧ RInv W X c st)
      (fun _ s rv s' => s' = s ∧ ∃ r, rv = some (.u32 r) ∧
        match X.ei p.toNat with
        | none => r = noid
        | some i => st.lv i ∧ r.toNat = st.id i ∧ r ≠ noid)

/-- The specification of a rule function `name`, mirroring the Lean rule
`rule`.  Premises and parameters are where `ck_step` put them; the scratch
stack is empty.  If the C function returns an id, the Lean rule succeeds
with the node that id denotes, and the invariant holds for the new state. -/
def RuleSpec (name : String) (rule : Ctx → St → List Nat → List Nat → Option (St × Nat)) : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : VSt) (prems params : List Nat),
    EmbC.FnSpec (State := State) Vbcf.prog name
      (fun vs s => vs = [.ptr sb 0, uv prems.length, uv params.length] ∧
        Holds W s.mem sb c ∧ RInv W X c st ∧ PremsAt c st prems ∧ ParamsAt W c params ∧
        c.k.sp = 0#32)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧
        (r ≠ noid → ∃ (st' : VSt) (f : Nat), rule X st prems params = some (st'.toSt, f) ∧
          RInv W X c' st' ∧ st'.lv f ∧ r.toNat = st'.id f ∧ StepFrame c c'))

/-! ## The invariant before any step

`ck_goal` runs before the first step, when the view is still the identity; its
proof is stated with the invariant in terms of the Lean state itself. -/

/-- `RInv` for the identity view, as a relation with the Lean state. -/
structure RInv0 (W : World) (X : Ctx) (c : CMem) (st : St) : Prop where
  core : CoreInv X.posOf c st
  poolPtr : ∃ b, c.k.pool = some (b, 0)
  ttNode : st.pool[X.bi.tt]? = some ⟨.boolVal true, #[]⟩
  ffNode : st.pool[X.bi.ff]? = some ⟨.boolVal false, #[]⟩
  tt : c.k.tt.toNat = offs st.pool X.bi.tt
  ff : c.k.ff.toNat = offs st.pool X.bi.ff
  goal : X.goal < st.pool.size ∧ c.k.goal.toNat = offs st.pool X.goal
  proofPtr : c.k.proof = some (W.pb, 0)
  nexpr : 3 + c.k.nexpr.toNat ≤ c.proof.size
  nexprBound : 3 + c.k.nexpr.toNat ≤ 2 ^ 32
  ei : ∀ p, p < c.k.nexpr.toNat → ∃ v, v < 2 ^ 32 ∧ U c.proof (3 + p) v ∧
    match X.ei p with
    | none => v = 0
    | some i => i < st.pool.size ∧ v = offs st.pool i + 1
  eiOut : ∀ p, c.k.nexpr.toNat ≤ p → X.ei p = none
  premPtr : ∃ b, c.k.prem = some (b, 0)
  premSize : c.prem.size = 256
  premCells : ∀ j, j < 256 → ∃ w, w < 2 ^ 32 ∧ U c.prem j w

end Vbcf.Proof
