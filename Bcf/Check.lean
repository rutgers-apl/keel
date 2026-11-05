import Bcf.Canon
import Bcf.Format
import Bcf.Rw.Pattern
import Std.Data.HashSet
import Bcf.Bitblast

/-!
# The checker: BCF rules over the canonical pool

Every rule is a function from the state, the premise facts, and the
step parameters to the new state and the derived fact index.  Node
construction goes through `pushNode`, so every fact is a well-typed
node and structural equality is index equality.
-/

namespace Bcf

/-! ## Node accessors -/

def St.node (st : St) (i : Nat) : Option Node := st.pool[i]?

def isEqNode : Node → Option (Nat × Nat)
  | ⟨.eq, args⟩ => if h : args.size = 2 then some (args[0], args[1]) else none
  | _ => none

def isNotNode : Node → Option Nat
  | ⟨.boolNot, args⟩ => if h : args.size = 1 then some args[0] else none
  | _ => none

def isImpliesNode : Node → Option (Nat × Nat)
  | ⟨.implies, args⟩ => if h : args.size = 2 then some (args[0], args[1]) else none
  | _ => none

def isConjNode : Node → Option (Array Nat)
  | ⟨.conj, args⟩ => some args
  | _ => none

def isDisjNode : Node → Option (Array Nat)
  | ⟨.disj, args⟩ => some args
  | _ => none

def isXor2Node : Node → Option (Nat × Nat)
  | ⟨.boolXor, args⟩ => if h : args.size = 2 then some (args[0], args[1]) else none
  | _ => none

def isBoolIteNode : Node → Option (Nat × Nat × Nat)
  | ⟨.boolIte, args⟩ => if h : args.size = 3 then some (args[0], args[1], args[2]) else none
  | _ => none

/-- Look a node up without creating it. -/
def findNode (st : St) (n : Node) : Option Nat :=
  match st.index[n]? with
  | some r => if st.pool[r]? = some n then some r else none
  | none => none

/-! ## Builders -/

def mkEq (st : St) (a b : Nat) : Option (St × Nat) := pushNode st ⟨.eq, #[a, b]⟩
def mkNot (st : St) (a : Nat) : Option (St × Nat) := pushNode st ⟨.boolNot, #[a]⟩
def mkConj (st : St) (args : Array Nat) : Option (St × Nat) := pushNode st ⟨.conj, args⟩
def mkDisj (st : St) (args : Array Nat) : Option (St × Nat) := pushNode st ⟨.disj, args⟩

/-! ## Constant evaluation -/

/-- The literal node denoting a scalar value. -/
def litOf : Val → Option Node
  | .bv w x => some ⟨.bvVal w x.toNat, #[]⟩
  | .bool b => some ⟨.boolVal b, #[]⟩
  | _ => none

/-! ## Rules

Each takes the premise facts (node indices) and the step parameters. -/

/-- `ei` translates an expression-valued step parameter (a node position
in the file) to its canonical index. -/
abbrev EI := Nat → Option Nat

def ruleAssume (goal : Nat) (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [p] =>
    match ei p with
    | some g => if g = goal ∧ g < st.pool.size ∧ st.tys[g]? = some .bool then some (st, g) else none
    | none => none
  | _, _ => none

def ruleRefl (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [p] =>
    match ei p with
    | some a =>
      match st.tys[a]? with
      | some t => if t.isScalar then mkEq st a a else none
      | none => none
    | none => none
  | _, _ => none

def ruleSymm (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] =>
    match st.node p with
    | some n =>
      match isEqNode n with
      | some (a, b) => mkEq st b a
      | none =>
        match isNotNode n with
        | some q =>
          match (st.node q).bind isEqNode with
          | some (a, b) =>
            match mkEq st b a with
            | some (st', e) => mkNot st' e
            | none => none
          | none => none
        | none => none
    | none => none
  | _, _ => none

/-- Chain: each premise `aᵢ = bᵢ` with `bᵢ = aᵢ₊₁`; conclude `a₁ = bₙ`. -/
def transChain (st : St) : List Nat → Nat → Nat → Option (Nat × Nat)
  | [], lhs, rhs => some (lhs, rhs)
  | p :: rest, lhs, rhs =>
    match (st.node p).bind isEqNode with
    | some (a, b) => if a = rhs then transChain st rest lhs b else none
    | none => none

def ruleTrans (st : St) : List Nat → List Nat → Option (St × Nat)
  | p :: rest, [] =>
    match (st.node p).bind isEqNode with
    | some (a, b) =>
      match transChain st rest a b with
      | some (lhs, rhs) => mkEq st lhs rhs
      | none => none
    | none => none
  | _, _ => none

/-- Collect `(aᵢ, bᵢ)` from premises `aᵢ = bᵢ`. -/
def eqSides (st : St) : List Nat → Option (List Nat × List Nat)
  | [] => some ([], [])
  | p :: rest =>
    match (st.node p).bind isEqNode, eqSides st rest with
    | some (a, b), some (as, bs) => some (a :: as, b :: bs)
    | _, _ => none

/-- Decode the operator carried in a CONG parameter (a raw node header
`code | vlen << 8 | params << 16`).  Values and variables are not
functions and are rejected. -/
def congOp (hdr : Nat) (vlen : Nat) : Option Op := do
  let code := hdr &&& 0xff
  let params := (hdr >>> 16) &&& 0xffff
  let n ← decodeNode 0 code vlen params (Array.replicate vlen 0)
  match n.op with
  | .bvVar _ _ => none
  | .bvVal _ _ => none
  | .boolVar _ => none
  | .boolVal _ => none
  | op => some op

def ruleCong (st : St) (prems : List Nat) : List Nat → Option (St × Nat)
  | [hdr] =>
    match eqSides st prems with
    | some (as, bs) =>
      match congOp hdr prems.length with
      | some op =>
        match pushNode st ⟨op, as.toArray⟩ with
        | some (st1, l) =>
          match pushNode st1 ⟨op, bs.toArray⟩ with
          | some (st2, r) => mkEq st2 l r
          | none => none
        | none => none
      | none => none
    | none => none
  | _ => none

def ruleTrueIntro (bi : Builtins) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] => mkEq st p bi.tt
  | _, _ => none

def ruleTrueElim (bi : Builtins) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] =>
    match (st.node p).bind isEqNode with
    | some (a, t) => if t = bi.tt then some (st, a) else none
    | none => none
  | _, _ => none

def ruleFalseIntro (bi : Builtins) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] =>
    match (st.node p).bind isNotNode with
    | some a => mkEq st a bi.ff
    | none => none
  | _, _ => none

def ruleFalseElim (bi : Builtins) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] =>
    match (st.node p).bind isEqNode with
    | some (a, f) => if f = bi.ff then mkNot st a else none
    | none => none
  | _, _ => none

def ruleEqResolve (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p, q], [] =>
    match (st.node q).bind isEqNode with
    | some (a, b) => if a = p then some (st, b) else none
    | none => none
  | _, _ => none

def ruleModusPonens (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p, q], [] =>
    match (st.node q).bind isImpliesNode with
    | some (a, b) => if a = p then some (st, b) else none
    | none => none
  | _, _ => none

def ruleNotNotElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] =>
    match (st.node p).bind isNotNode with
    | some q =>
      match (st.node q).bind isNotNode with
      | some a => some (st, a)
      | none => none
    | none => none
  | _, _ => none

def ruleContra (bi : Builtins) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p, q], [] =>
    match (st.node q).bind isNotNode with
    | some a => if a = p ∧ bi.ff < st.pool.size then some (st, bi.ff) else none
    | none => none
  | _, _ => none

def ruleAndElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [k] =>
    match (st.node p).bind isConjNode with
    | some args => match args[k]? with
      | some a => some (st, a)
      | none => none
    | none => none
  | _, _ => none

def ruleAndIntro (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] => some (st, p)
  | prems, [] => if 2 ≤ prems.length then mkConj st prems.toArray else none
  | _, _ => none

def ruleNotOrElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [k] =>
    match (st.node p).bind isNotNode with
    | some q =>
      match (st.node q).bind isDisjNode with
      | some args => match args[k]? with
        | some a => mkNot st a
        | none => none
      | none => none
    | none => none
  | _, _ => none

def ruleSplit (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [p] =>
    match ei p with
    | some a =>
      match mkNot st a with
      | some (st', na) => mkDisj st' #[a, na]
      | none => none
    | none => none
  | _, _ => none

/-- EVALUATE: `e = ⟦e⟧` for a closed scalar expression `e`. -/
def ruleEvaluate (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [p] =>
    match ei p with
    | none => none
    | some e =>
    match memoVal st e with
    | some v =>
      match litOf v with
      | some lit =>
        match pushNode st lit with
        | some (st', l) => mkEq st' e l
        | none => none
      | none => none
    | none => none
  | _, _ => none

/-! ## More boolean rules -/

def ruleImpliesElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] =>
    match (st.node p).bind isImpliesNode with
    | some (a, b) =>
      match mkNot st a with
      | some (st', na) => mkDisj st' #[na, b]
      | none => none
    | none => none
  | _, _ => none

def ruleNotImpliesElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [idx] =>
    match (st.node p).bind isNotNode with
    | some q =>
      match (st.node q).bind isImpliesNode with
      | some (a, b) => if idx = 0 then some (st, a) else if idx = 1 then mkNot st b else none
      | none => none
    | none => none
  | _, _ => none

/-- `(¬a ∨ b)` for form 0, `(a ∨ ¬b)` for form 1. -/
def equivElimClause (st : St) (a b form : Nat) : Option (St × Nat) :=
  if form = 0 then
    match mkNot st a with
    | some (st', na) => mkDisj st' #[na, b]
    | none => none
  else if form = 1 then
    match mkNot st b with
    | some (st', nb) => mkDisj st' #[a, nb]
    | none => none
  else none

/-- `(a ∨ b)` for form 0, `(¬a ∨ ¬b)` for form 1. -/
def notEquivElimClause (st : St) (a b form : Nat) : Option (St × Nat) :=
  if form = 0 then mkDisj st #[a, b]
  else if form = 1 then
    match mkNot st a with
    | some (st1, na) =>
      match mkNot st1 b with
      | some (st2, nb) => mkDisj st2 #[na, nb]
      | none => none
    | none => none
  else none

def ruleEquivElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [form] =>
    match (st.node p).bind isEqNode with
    | some (a, b) => equivElimClause st a b form
    | none => none
  | _, _ => none

def ruleNotEquivElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [form] =>
    match (st.node p).bind isNotNode with
    | some q =>
      match (st.node q).bind isEqNode with
      | some (a, b) => notEquivElimClause st a b form
      | none => none
    | none => none
  | _, _ => none

def ruleXorElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [form] =>
    match (st.node p).bind isXor2Node with
    | some (a, b) => notEquivElimClause st a b form
    | none => none
  | _, _ => none

def ruleNotXorElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [lit] =>
    match (st.node p).bind isNotNode with
    | some q =>
      match (st.node q).bind isXor2Node with
      | some (a, b) => equivElimClause st a b (if lit = 0 then 1 else if lit = 1 then 0 else 2)
      | none => none
    | none => none
  | _, _ => none

def ruleIteElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [lit] =>
    match (st.node p).bind isBoolIteNode with
    | some (c, a, b) =>
      if lit = 1 then mkDisj st #[c, b]
      else if lit = 0 then
        match mkNot st c with
        | some (st', nc) => mkDisj st' #[nc, a]
        | none => none
      else none
    | none => none
  | _, _ => none

def ruleNotIteElim (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [lit] =>
    match (st.node p).bind isNotNode with
    | some q =>
      match (st.node q).bind isBoolIteNode with
      | some (c, a, b) =>
        if lit = 1 then
          match mkNot st b with
          | some (st', nb) => mkDisj st' #[c, nb]
          | none => none
        else if lit = 0 then
          match mkNot st c with
          | some (st1, nc) =>
            match mkNot st1 a with
            | some (st2, na) => mkDisj st2 #[nc, na]
            | none => none
          | none => none
        else none
      | none => none
    | none => none
  | _, _ => none

/-- Negate every element, threading the state. -/
def mkNots (st : St) : List Nat → Option (St × List Nat)
  | [] => some (st, [])
  | a :: rest =>
    match mkNot st a with
    | some (st1, na) =>
      match mkNots st1 rest with
      | some (st2, nas) => some (st2, na :: nas)
      | none => none
    | none => none

def ruleNotAnd (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], _ =>
    match (st.node p).bind isNotNode with
    | some q =>
      match (st.node q).bind isConjNode with
      | some args =>
        match mkNots st args.toList with
        | some (st', nas) => mkDisj st' nas.toArray
        | none => none
      | none => none
    | none => none
  | _, _ => none

/-! ### CNF tautologies (no premises) -/

def ruleCnfAndPos (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, lit] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isConjNode with
      | some args =>
        match args[lit]? with
        | some a =>
          match mkNot st e with
          | some (st', ne) => mkDisj st' #[ne, a]
          | none => none
        | none => none
      | none => none
    | none => none
  | _, _ => none

def ruleCnfAndNeg (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isConjNode with
      | some args =>
        match mkNots st args.toList with
        | some (st', nas) => mkDisj st' (e :: nas).toArray
        | none => none
      | none => none
    | none => none
  | _, _ => none

def ruleCnfOrPos (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isDisjNode with
      | some args =>
        match mkNot st e with
        | some (st', ne) => mkDisj st' (ne :: args.toList).toArray
        | none => none
      | none => none
    | none => none
  | _, _ => none

def ruleCnfOrNeg (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, lit] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isDisjNode with
      | some args =>
        match args[lit]? with
        | some a =>
          match mkNot st a with
          | some (st', na) => mkDisj st' #[e, na]
          | none => none
        | none => none
      | none => none
    | none => none
  | _, _ => none

def ruleCnfImpliesPos (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isImpliesNode with
      | some (a, b) =>
        match mkNot st e with
        | some (st1, ne) =>
          match mkNot st1 a with
          | some (st2, na) => mkDisj st2 #[ne, na, b]
          | none => none
        | none => none
      | none => none
    | none => none
  | _, _ => none

def ruleCnfImpliesNeg (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, lit] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isImpliesNode with
      | some (a, b) =>
        if lit = 0 then mkDisj st #[e, a]
        else if lit = 1 then
          match mkNot st b with
          | some (st', nb) => mkDisj st' #[e, nb]
          | none => none
        else none
      | none => none
    | none => none
  | _, _ => none

/-- The head literal of a CNF clause: `¬e` or `e`. -/
def headOf (st : St) (e : Nat) (negE : Bool) : Option (St × Nat) :=
  if negE then mkNot st e else some (st, e)

/-- `¬e ∨ ¬a ∨ b` (form 0) or `¬e ∨ a ∨ ¬b` (form 1), for `e` an
equivalence or (with `negE = false`) an xor. -/
def cnfPosClause (st : St) (e a b form : Nat) (negE : Bool) : Option (St × Nat) :=
  match headOf st e negE with
  | some (st1, h) =>
    if form = 0 then
      match mkNot st1 a with
      | some (st2, na) => mkDisj st2 #[h, na, b]
      | none => none
    else if form = 1 then
      match mkNot st1 b with
      | some (st2, nb) => mkDisj st2 #[h, a, nb]
      | none => none
    else none
  | none => none

/-- `h ∨ a ∨ b` (lit 0) or `h ∨ ¬a ∨ ¬b` (lit 1), with `h = e` or `¬e`. -/
def cnfNegClause (st : St) (e a b lit : Nat) (negE : Bool) : Option (St × Nat) :=
  match headOf st e negE with
  | some (st1, h) =>
    if lit = 0 then mkDisj st1 #[h, a, b]
    else if lit = 1 then
      match mkNot st1 a with
      | some (st2, na) =>
        match mkNot st2 b with
        | some (st3, nb) => mkDisj st3 #[h, na, nb]
        | none => none
      | none => none
    else none
  | none => none

def ruleCnfEquivPos (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, form] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isEqNode with
      | some (a, b) => cnfPosClause st e a b form true
      | none => none
    | none => none
  | _, _ => none

def ruleCnfEquivNeg (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, lit] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isEqNode with
      | some (a, b) => cnfNegClause st e a b lit false
      | none => none
    | none => none
  | _, _ => none

def ruleCnfXorPos (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, lit] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isXor2Node with
      | some (a, b) => cnfNegClause st e a b lit true
      | none => none
    | none => none
  | _, _ => none

def ruleCnfXorNeg (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, form] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isXor2Node with
      | some (a, b) => cnfPosClause st e a b form false
      | none => none
    | none => none
  | _, _ => none

def ruleCnfItePos (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, lit] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isBoolIteNode with
      | some (c, a, b) =>
        match mkNot st e with
        | some (st1, ne) =>
          if lit = 0 then
            match mkNot st1 c with
            | some (st2, nc) => mkDisj st2 #[ne, nc, a]
            | none => none
          else if lit = 1 then mkDisj st1 #[ne, c, b]
          else if lit = 2 then mkDisj st1 #[ne, a, b]
          else none
        | none => none
      | none => none
    | none => none
  | _, _ => none

def ruleCnfIteNeg (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe, lit] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isBoolIteNode with
      | some (c, a, b) =>
        if lit = 0 then
          match mkNot st c with
          | some (st1, nc) =>
            match mkNot st1 a with
            | some (st2, na) => mkDisj st2 #[e, nc, na]
            | none => none
          | none => none
        else if lit = 1 then
          match mkNot st b with
          | some (st1, nb) => mkDisj st1 #[e, c, nb]
          | none => none
        else if lit = 2 then
          match mkNot st a with
          | some (st1, na) =>
            match mkNot st1 b with
            | some (st2, nb) => mkDisj st2 #[e, na, nb]
            | none => none
          | none => none
        else none
      | none => none
    | none => none
  | _, _ => none

/-- `ite c (e = a) (e = b)` for `e = ite c a b`. -/
def iteEqBody (st : St) (e c a b : Nat) : Option (St × Nat) :=
  match mkEq st e a with
  | some (st1, e1) =>
    match mkEq st1 e b with
    | some (st2, e2) => pushNode st2 ⟨.boolIte, #[c, e1, e2]⟩
    | none => none
  | none => none

/-- The three children of a node, if it has exactly three. -/
def three (args : Array Nat) : Option (Nat × Nat × Nat) :=
  match args[0]?, args[1]?, args[2]? with
  | some c, some a, some b => if args.size = 3 then some (c, a, b) else none
  | _, _, _ => none

def ruleIteEq (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match st.node e with
      | some ⟨.boolIte, args⟩ =>
        match three args with
        | some (c, a, b) => iteEqBody st e c a b
        | none => none
      | some ⟨.bvIte _, args⟩ =>
        match three args with
        | some (c, a, b) => iteEqBody st e c a b
        | none => none
      | _ => none
    | none => none
  | _, _ => none

def ruleDistinctValues (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [p0, p1] =>
    match ei p0, ei p1 with
    | some v0, some v1 =>
      match st.node v0, st.node v1 with
      | some ⟨.bvVal w a, _⟩, some ⟨.bvVal w' b, _⟩ =>
        if w = w' ∧ a ≠ b then
          match mkEq st v0 v1 with
          | some (st', e) => mkNot st' e
          | none => none
        else none
      | some ⟨.boolVal a, _⟩, some ⟨.boolVal b, _⟩ =>
        if a ≠ b then
          match mkEq st v0 v1 with
          | some (st', e) => mkNot st' e
          | none => none
        else none
      | _, _ => none
    | _, _ => none
  | _, _ => none

/-! ### Resolution, factoring, reordering -/

/-- The literals of a premise viewed as a clause: the disjuncts of a
disjunction, unless the whole premise is the pivot; else the premise
itself. -/
def litsOf (st : St) (p : Nat) (pivot : Option Nat) : List Nat :=
  match (st.node p).bind isDisjNode with
  | some args => if some p = pivot then [p] else args.toList
  | none => [p]

def eraseOpt (l : List Nat) : Option Nat → List Nat
  | some x => l.erase x
  | none => l

/-- A clause as a fact: `false` for the empty clause, the literal for a
singleton, else a disjunction. -/
def mkClause (bi : Builtins) (st : St) : List Nat → Option (St × Nat)
  | [] => if bi.ff < st.pool.size then some (st, bi.ff) else none
  | [l] => some (st, l)
  | lits => mkDisj st lits.toArray

def testPol (pols : List Nat) (i : Nat) : Bool :=
  ((pols.getD (i / 32) 0) >>> (i % 32)) &&& 1 = 1

/-- Chain resolution over the remaining premises and pivots, following
`chain_resolution` in `bcf_checker.c`. -/
def resolveChain (st : St) (pols : List Nat) : List Nat → List Nat → Nat → List Nat → Option (List Nat)
  | [], [], _, lhs => some lhs
  | rhsPm :: rest, lit :: lits, i, lhs =>
    let notLit := findNode st ⟨.boolNot, #[lit]⟩
    let pol := testPol pols i
    let piv0 : Option Nat := if pol then some lit else notLit
    let piv1 : Option Nat := if pol then notLit else some lit
    let lhs' := eraseOpt lhs piv0
    let rhs := eraseOpt (litsOf st rhsPm piv1) piv1
    resolveChain st pols rest lits (i + 1) (lhs' ++ rhs)
  | _, _, _, _ => none

/-- Number of polarity words for `n` pivots. -/
def polWords (n : Nat) : Nat := (n + 31) / 32

def ruleResolution (bi : Builtins) (ei : EI) (st : St) (prems params : List Nat) : Option (St × Nat) :=
  match prems with
  | p0 :: rest =>
    if rest.length = 0 then none else
    if params.length ≠ polWords rest.length + rest.length then none else
    match mapOpt ei (params.drop (polWords rest.length)) with
    | some (lit0 :: lits) =>
      match resolveChain st (params.take (polWords rest.length)) rest (lit0 :: lits) 0
          (litsOf st p0 (if testPol (params.take (polWords rest.length)) 0 then some lit0
                         else findNode st ⟨.boolNot, #[lit0]⟩)) with
      | some res => mkClause bi st res
      | none => none
    | _ => none
  | [] => none

/-- Byte `k` of the parameter words, little-endian. -/
def paramByte (params : List Nat) (k : Nat) : Nat :=
  ((params.getD (k / 4) 0) >>> (8 * (k % 4))) &&& 0xff

/-- Parse `[pair_len, uniq, dup...]` entries; returns the set of
duplicate positions (as a list) if well-formed. -/
def parseDupPairs (args : Array Nat) (params : List Nat) : Option (List Nat) := Id.run do
  let vlen := params.length * 4
  let mut idx := 0
  let mut dups : List Nat := []
  let mut preUniq : Option Nat := none
  while idx < vlen do
    let pairLen := paramByte params idx
    idx := idx + 1
    if pairLen = 0 then break
    if pairLen < 2 ∨ idx + pairLen > vlen then return none
    let uniq := paramByte params idx
    if uniq ≥ args.size then return none
    match preUniq with
    | some pu => if uniq ≤ pu then return none
    | none => pure ()
    preUniq := some uniq
    for j in [1:pairLen] do
      let d := paramByte params (idx + j)
      if d ≥ args.size ∨ d ≤ uniq then return none
      if args[uniq]? ≠ args[d]? then return none
      dups := d :: dups
    idx := idx + pairLen
  if dups.isEmpty then return none
  -- trailing bytes must be zero
  for k in [idx:vlen] do
    if paramByte params k ≠ 0 then return none
  return some dups

/-- `l ⊆ m` in linear time, through a hash set (`subsetB_eq` gives its meaning). -/
def subsetB (l m : List Nat) : Bool :=
  let hs := Std.HashSet.ofList m
  l.all (fun a => hs.contains a)

/-- The literals that survive factoring: those not at a duplicate position. -/
def keptLits (args : Array Nat) (dups : List Nat) : List Nat :=
  (List.range args.size).filter (fun i => !dups.contains i) |>.filterMap (fun i => args[i]?)

def ruleFactoring (st : St) (prems params : List Nat) : Option (St × Nat) :=
  match prems with
  | [p] =>
    match (st.node p).bind isDisjNode with
    | some args =>
      if params.isEmpty then none else
      match parseDupPairs args params with
      | some dups =>
        -- every original literal must survive (soundness needs nothing more)
        if subsetB args.toList (keptLits args dups) then
          match keptLits args dups with
          | [l] => some (st, l)
          | _ => mkDisj st (keptLits args dups).toArray
        else none
      | none => none
    | none => none
  | _ => none

/-- Apply the swap vector of REORDERING. -/
def applySwaps (params : List Nat) (args : Array Nat) : Option (Array Nat) := Id.run do
  let u16 := fun (t : Nat) => ((params.getD (t / 2) 0) >>> (16 * (t % 2))) &&& 0xffff
  let cnt := u16 0
  if cnt > args.size then return none
  let vecSz := (cnt + 1) * 2
  if (vecSz + 3) / 4 ≠ params.length then return none
  if vecSz % 4 ≠ 0 ∧ u16 (cnt + 1) ≠ 0 then return none   -- padding half-word must be zero
  let mut a := args
  for t in [1:cnt+1] do
    let sw := u16 t
    let j := sw &&& 0xff
    let k := (sw >>> 8) &&& 0xff
    if j ≥ a.size ∨ k ≥ a.size then return none
    a := a.swapIfInBounds j k
  return some a

def ruleReordering (st : St) (prems params : List Nat) : Option (St × Nat) :=
  match prems with
  | [p] =>
    match (st.node p).bind isDisjNode with
    | some args =>
      if params.isEmpty then some (st, p) else
      match applySwaps params args with
      | some args' =>
        -- both directions of membership (a permutation satisfies both; soundness needs nothing more)
        if subsetB args.toList args'.toList ∧ subsetB args'.toList args.toList then mkDisj st args' else none
      | none => none
    | none => some (st, p)
  | _ => none

/-! ### ABSORB and ACI_NORM -/

/-- The absorbing element of an operator, as a node (`is_zero_elem`). -/
def isZeroElem (root : Op) (n : Node) : Bool :=
  match root with
  | .disj => n.op == .boolVal true
  | .conj => n.op == .boolVal false
  | .bvAnd w => n.op == .bvVal w 0
  | .bvOr w => n.op == .bvVal w (2 ^ w - 1)
  | _ => false

/-- Search nested same-operator children for an absorbing element. -/
def absorbF (pool : Pool) (root : Op) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, i =>
    match pool[i]? with
    | none => false
    | some n => isZeroElem root n || (n.op == root && n.args.any (fun a => a < i && absorbF pool root f a))

def ruleAbsorb (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isEqNode with
      | some (r, z) =>
        match st.node r, st.node z with
        | some rn, some zn =>
          if isZeroElem rn.op zn ∧ absorbF st.pool rn.op (r + 1) r then some (st, e) else none
        | _, _ => none
      | none => none
    | none => none
  | _, _ => none

/-- Associative operators handled by ACI normalisation (`is_assoc`). -/
def isAssocOp : Op → Bool
  | .conj | .disj | .bvAnd _ | .bvOr _ | .bvXor _ | .bvConcat _ => true
  | _ => false

/-- The associative but non-commutative one. -/
def isConcatOp : Op → Bool
  | .bvConcat _ => true
  | _ => false

/-- The idempotent ones among them. -/
def isIdemOp : Op → Bool
  | .conj | .disj | .bvAnd _ | .bvOr _ => true
  | _ => false

/-- The identity element of an operator, as a node (`is_nil_elem`). -/
def isNilElem (root : Op) (n : Node) : Bool :=
  match root with
  | .disj => n.op == .boolVal false
  | .conj => n.op == .boolVal true
  | .bvAnd w => n.op == .bvVal w (2 ^ w - 1)
  | .bvOr w => n.op == .bvVal w 0
  | .bvXor w => n.op == .bvVal w 0
  | _ => false

/-- Same operator code ignoring bit-widths, as BCF's `arg->code == root->code`.
Only concatenations nest with differing widths in a well-typed pool. -/
def sameAssoc (op o : Op) : Bool :=
  if isConcatOp op then isConcatOp o else op == o

/-- Leaves of the maximal same-operator tree below `i`, identity elements dropped. -/
def flattenF (pool : Pool) (op : Op) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, i =>
    match pool[i]? with
    | none => []
    | some n =>
      if sameAssoc op n.op then n.args.toList.flatMap (fun a => if a < i then flattenF pool op f a else [])
      else if isNilElem op n then [] else [i]

def flatten (pool : Pool) (op : Op) (i : Nat) : List Nat := flattenF pool op (i + 1) i

def dedupNat : List Nat → List Nat
  | [] => []
  | x :: rest => if x ∈ rest then dedupNat rest else x :: dedupNat rest

def sortNat (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

/-- Canonical leaf list of an assoc-op node: flattened; deduplicated when
idempotent; sorted when commutative. -/
def aciLeaves (pool : Pool) (op : Op) (i : Nat) : List Nat :=
  if isConcatOp op then flatten pool op i
  else sortNat (if isIdemOp op then dedupNat (flatten pool op i) else flatten pool op i)

def aciNF (pool : Pool) (i : Nat) : Option (Op × List Nat) :=
  match pool[i]? with
  | some n => if isAssocOp n.op then some (n.op, aciLeaves pool n.op i) else none
  | none => none

/-- `a` normalises to the single leaf `b`, or to the empty list while `b` is the identity. -/
def aciReduces (st : St) (a b : Nat) : Bool :=
  match aciNF st.pool a with
  | some (_, [x]) => x == b
  | some (op, []) => match st.node b with
    | some bn => isNilElem op bn
    | none => false
  | _ => false

def aciEq (st : St) (a b : Nat) : Bool :=
  a == b ||
  (match aciNF st.pool a, aciNF st.pool b with
   | some (op, la), some (op', lb) => op == op' && la == lb
   | _, _ => false) ||
  aciReduces st a b || aciReduces st b a

def ruleAciNorm (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isEqNode with
      | some (a, b) => if aciEq st a b then some (st, e) else none
      | none => none
    | none => none
  | _, _ => none

/-! ### POLY_NORM: linear normal forms over bit-vectors -/

/-- A linear form: a constant plus a coefficient per atom (a node index). -/
structure Lin (w : Nat) where
  const : BitVec w
  terms : List (Nat × BitVec w)
  deriving DecidableEq, Repr

namespace Lin

def mergeTerms {w : Nat} : List (Nat × BitVec w) → List (Nat × BitVec w) → List (Nat × BitVec w)
  | [], ys => ys
  | xs, [] => xs
  | (a, c) :: xs, (b, d) :: ys =>
    if a < b then (a, c) :: mergeTerms xs ((b, d) :: ys)
    else if b < a then (b, d) :: mergeTerms ((a, c) :: xs) ys
    else if c + d = 0 then mergeTerms xs ys else (a, c + d) :: mergeTerms xs ys
termination_by xs ys => xs.length + ys.length

def add {w : Nat} (p q : Lin w) : Lin w := ⟨p.const + q.const, mergeTerms p.terms q.terms⟩

def scale {w : Nat} (k : BitVec w) (p : Lin w) : Lin w :=
  ⟨k * p.const, (p.terms.map (fun t => (t.1, k * t.2))).filter (fun t => t.2 ≠ 0)⟩

def neg {w : Nat} (p : Lin w) : Lin w := scale (-1) p

def ofConst {w : Nat} (c : BitVec w) : Lin w := ⟨c, []⟩

def atom {w : Nat} (a : Nat) : Lin w := ⟨0, [(a, 1)]⟩

end Lin

/-- The literal value of a node, if it is a bit-vector literal of width `w`. -/
def litVal (pool : Pool) (w : Nat) (i : Nat) : Option (BitVec w) :=
  match pool[i]? with
  | some ⟨.bvVal w' v, _⟩ => if w' = w then some (BitVec.ofNat w v) else none
  | _ => none

/-- Linear normal form of a width-`w` node (fuel-bounded). -/
def linF (pool : Pool) (w : Nat) : Nat → Nat → Lin w
  | 0, i => Lin.atom i
  | f + 1, i =>
    match pool[i]? with
    | some ⟨.bvVal w' v, _⟩ => if w' = w then Lin.ofConst (BitVec.ofNat w v) else Lin.atom i
    | some ⟨.bvAdd w', args⟩ =>
      if w' = w then (args.toList.map (fun a => if a < i then linF pool w f a else Lin.atom a)).foldr Lin.add (Lin.ofConst 0)
      else Lin.atom i
    | some ⟨.bvSub w', args⟩ =>
      match args.toList with
      | [a, b] => if w' = w ∧ a < i ∧ b < i then Lin.add (linF pool w f a) (Lin.neg (linF pool w f b)) else Lin.atom i
      | _ => Lin.atom i
    | some ⟨.bvNeg w', args⟩ =>
      match args.toList with
      | [a] => if w' = w ∧ a < i then Lin.neg (linF pool w f a) else Lin.atom i
      | _ => Lin.atom i
    | some ⟨.bvMul w', args⟩ =>
      match args.toList with
      | [a, b] =>
        if w' = w ∧ a < i ∧ b < i then
          match litVal pool w a, litVal pool w b with
          | some k, _ => Lin.scale k (linF pool w f b)
          | none, some k => Lin.scale k (linF pool w f a)
          | none, none => Lin.atom i
        else Lin.atom i
      | _ => Lin.atom i
    | _ => Lin.atom i

def lin (pool : Pool) (w : Nat) (i : Nat) : Lin w := linF pool w (i + 1) i

def rulePolyNorm (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match (st.node e).bind isEqNode with
      | some (a, b) =>
        match st.tys[a]? with
        | some (.bv w) => if lin st.pool w a = lin st.pool w b then some (st, e) else none
        | _ => none
      | none => none
    | none => none
  | _, _ => none

/-- `c * (x0 - x1)` with `c` an odd literal: returns `(w, x0, x1)`. -/
def oddMulSub (st : St) (m : Nat) : Option (Nat × Nat × Nat) :=
  match st.node m with
  | some ⟨.bvMul w, args⟩ =>
    match args.toList with
    | [c, s] =>
      match litVal st.pool w c, st.node s with
      | some k, some ⟨.bvSub _, sargs⟩ =>
        match sargs.toList with
        | [x0, x1] => if k.toNat % 2 = 1 then some (w, x0, x1) else none
        | _ => none
      | _, _ => none
    | _ => none
  | _ => none

/-- POLY_NORM_EQ: from `c0 * (x0 - x1) = c1 * (y0 - y1)` with odd `c0, c1`
conclude `(x0 = x1) = (y0 = y1)`. -/
def rulePolyNormEq (st : St) : List Nat → List Nat → Option (St × Nat)
  | [p], [] =>
    match (st.node p).bind isEqNode with
    | some (m0, m1) =>
      match oddMulSub st m0, oddMulSub st m1 with
      | some (_, x0, x1), some (_, y0, y1) =>
        match mkEq st x0 x1 with
        | some (st1, e0) =>
          match mkEq st1 y0 y1 with
          | some (st2, e1) => mkEq st2 e0 e1
          | none => none
        | none => none
      | _, _ => none
    | none => none
  | _, _ => none

/-! ### REWRITE -/

/-- `rw_cond_match`: the premise is the condition, or `condition = true`. -/
def condMatch (bi : Builtins) (st : St) (c p : Nat) : Bool :=
  p == c ||
  (match st.node p with
   | some ⟨.eq, args⟩ =>
     match args.toList with
     | [x, t] => t == bi.tt && x == c
     | _ => false
   | _ => false)

/-- The conjuncts `cs` of an instantiated side condition against the premises
`ps`: each conjunct is matched by the premise in its position, and a conjunct
past the last premise must be a closed constant that evaluates to `true`. -/
def condsOK (bi : Builtins) (st : St) : List Nat → List Nat → Bool
  | [], [] => true
  | c :: cs, p :: ps => condMatch bi st c p && condsOK bi st cs ps
  | c :: cs, [] =>
    match cval st c with
    | some (.bool true) => condsOK bi st cs []
    | _ => false
  | [], _ :: _ => false

/-- The instantiated side condition, a conjunction or a single fact, holds. -/
def checkCond (bi : Builtins) (st : St) (c : Nat) (prems : List Nat) : Bool :=
  match st.node c with
  | some ⟨.conj, cs⟩ => condsOK bi st cs.toList prems
  | _ => condsOK bi st [c] prems

def rwConclude (bi : Builtins) (args : Array Nat) (r : RwRule) (st : St) : Option (St × Nat) :=
  match instE bi args r.lhs st with
  | some (st1, m) =>
    match instE bi args r.rhs st1 with
    | some (st2, t) => mkEq st2 m t
    | none => none
  | none => none

/-- `extract hi lo a`. -/
def extractOf (st : St) (i : Nat) : Option (Nat × Nat × Nat) :=
  match st.node i with
  | some ⟨.bvExtract hi lo, args⟩ =>
    match args.toList with
    | [a] => some (hi, lo, a)
    | _ => none
  | _ => none

/-- `bvAnd w [p, q]`. -/
def and2Of (st : St) (i : Nat) : Option (Nat × Nat × Nat) :=
  match st.node i with
  | some ⟨.bvAnd w, args⟩ =>
    match args.toList with
    | [p, q] => some (w, p, q)
    | _ => none
  | _ => none

/-- Half of an and-split: `bvAnd [extract hi lo x, extract hi lo y]` in
either order. -/
def andHalf (st : St) (h x y hi lo : Nat) : Bool :=
  match and2Of st h with
  | some (_, p, q) =>
    match extractOf st p, extractOf st q with
    | some (h1, l1, a), some (h2, l2, b) =>
      h1 == hi && h2 == hi && l1 == lo && l2 == lo && ((a == x && b == y) || (a == y && b == x))
    | _, _ => false
  | none => false

/-- The low bit of an and-split piece `bvAnd [extract hi lo p, _]`: the `lo`
of its first extract. -/
def pieceLo (st : St) (h : Nat) : Option Nat :=
  match and2Of st h with
  | some (_, p, _) =>
    match extractOf st p with
    | some (_, lo, _) => some lo
    | none => none
  | none => none

/-- The pieces of an and-split, high to low, the first ending at bit `hi`:
each piece is `x[hi_i:lo_i] & y[hi_i:lo_i]` (`andHalf`, with `lo_i` read from
the piece), the next piece ends at `lo_i - 1`, and the last ends at bit 0. -/
def andPieces (st : St) (x y hi : Nat) : List Nat → Bool
  | [] => false
  | h :: rest =>
    match pieceLo st h with
    | some lo =>
      andHalf st h x y hi lo &&
        (if rest.isEmpty then lo == 0 else 1 ≤ lo && andPieces st x y (lo - 1) rest)
    | none => false

/-- Trusted rewrite shape 1: `x & y = (x[w-1:k_1] & y[w-1:k_1]) ++ … ++ (x[k_{n-1}-1:0] & y[k_{n-1}-1:0])`
for `n ≥ 2` contiguous non-empty pieces covering the width (in each piece the
operands may be swapped). -/
def rw0AndSplit (st : St) (a b : Nat) : Bool :=
  match and2Of st a, st.node b with
  | some (w, x, y), some ⟨.bvConcat w', hs⟩ =>
    w == w' && 2 ≤ hs.size && andPieces st x y (w - 1) hs.toList
  | _, _ => false

/-- Trusted rewrite shape 2: `repeat k y = y ++ ... ++ y`. -/
def rw0Repeat (st : St) (a b : Nat) : Bool :=
  match st.node a with
  | some ⟨.bvRepeat w k, args⟩ =>
    match args.toList with
    | [y] =>
      if k == 1 then b == y
      else match st.node b with
        | some ⟨.bvConcat w', ys⟩ => w == w' && ys.toList == List.replicate k y
        | _ => false
    | _ => false
  | _ => false

/-- Trusted rewrite shape 3: `distinct a b = not (eq a b)`. -/
def rw0Distinct (st : St) (a b : Nat) : Bool :=
  match st.node a, st.node b with
  | some ⟨.distinct, xs⟩, some ⟨.boolNot, ns⟩ =>
    match ns.toList with
    | [e] =>
      match st.node e with
      | some ⟨.eq, ys⟩ => xs == ys
      | _ => false
    | _ => false
  | _, _ => false

/-- REWRITE with id 0 is a trusted step in BCF; here it is accepted only
for the three equation shapes that occur, each verified. -/
def ruleRewrite0 (st : St) (e : Nat) : Bool :=
  match (st.node e).bind isEqNode with
  | some (a, b) => rw0AndSplit st a b || rw0Repeat st a b || rw0Distinct st a b
  | none => false

def ruleRewrite (tbl : Nat → Option RwRule) (bi : Builtins) (ei : EI) (st : St) (prems : List Nat) :
    List Nat → Option (St × Nat)
  | [] => none
  | rid :: ps =>
    if rid = 0 then
      match prems, ps with
      | [], [p] =>
        match ei p with
        | some e => if ruleRewrite0 st e then some (st, e) else none
        | none => none
      | _, _ => none
    else
      match tbl rid with
      | none => none
      | some r =>
        match mapOpt ei ps with
        | none => none
        | some args =>
          if paramsOK st r.params args then
            match r.cond with
            | none =>
              match prems with
              | [] => rwConclude bi args.toArray r st
              | _ :: _ => none
            | some c =>
              match instE bi args.toArray c st with
              | some (st1, ci) => if checkCond bi st1 ci prems then rwConclude bi args.toArray r st1 else none
              | none => none
          else none

/-! ### BITBLAST -/

def ruleBitblast (bi : Builtins) (ei : EI) (st : St) : List Nat → List Nat → Option (St × Nat)
  | [], [pe] =>
    match ei pe with
    | some e =>
      match (st.pool[e]?).bind isEqNode with
      | some (a, b) =>
        match st.tys[a]? with
        | some (.bv _) =>
          match bitsOf st b with
          | some bs => if bbTerm st bi a bs then some (st, e) else none
          | none => none
        | some .bool => if bbAtom st a b then some (st, e) else none
        | _ => none
      | none => none
    | none => none
  | _, _ => none

/-! ## Dispatch -/

def applyRule (tbl : Nat → Option RwRule) (goal : Nat) (bi : Builtins) (ei : EI) (st : St) (r : Rule)
    (prems params : List Nat) :
    Option (St × Nat) :=
  match r with
  | .assume         => ruleAssume goal ei st prems params
  | .refl           => ruleRefl ei st prems params
  | .symm           => ruleSymm st prems params
  | .trans          => ruleTrans st prems params
  | .cong           => ruleCong st prems params
  | .trueIntro      => ruleTrueIntro bi st prems params
  | .trueElim       => ruleTrueElim bi st prems params
  | .falseIntro     => ruleFalseIntro bi st prems params
  | .falseElim      => ruleFalseElim bi st prems params
  | .eqResolve      => ruleEqResolve st prems params
  | .modusPonens    => ruleModusPonens st prems params
  | .notNotElim     => ruleNotNotElim st prems params
  | .contra         => ruleContra bi st prems params
  | .andElim        => ruleAndElim st prems params
  | .andIntro       => ruleAndIntro st prems params
  | .notOrElim      => ruleNotOrElim st prems params
  | .split          => ruleSplit ei st prems params
  | .evaluate       => ruleEvaluate ei st prems params
  | .impliesElim    => ruleImpliesElim st prems params
  | .notImpliesElim => ruleNotImpliesElim st prems params
  | .equivElim      => ruleEquivElim st prems params
  | .notEquivElim   => ruleNotEquivElim st prems params
  | .xorElim        => ruleXorElim st prems params
  | .notXorElim     => ruleNotXorElim st prems params
  | .iteElim        => ruleIteElim st prems params
  | .notIteElim     => ruleNotIteElim st prems params
  | .notAnd         => ruleNotAnd st prems params
  | .cnfAndPos      => ruleCnfAndPos ei st prems params
  | .cnfAndNeg      => ruleCnfAndNeg ei st prems params
  | .cnfOrPos       => ruleCnfOrPos ei st prems params
  | .cnfOrNeg       => ruleCnfOrNeg ei st prems params
  | .cnfImpliesPos  => ruleCnfImpliesPos ei st prems params
  | .cnfImpliesNeg  => ruleCnfImpliesNeg ei st prems params
  | .cnfEquivPos    => ruleCnfEquivPos ei st prems params
  | .cnfEquivNeg    => ruleCnfEquivNeg ei st prems params
  | .cnfXorPos      => ruleCnfXorPos ei st prems params
  | .cnfXorNeg      => ruleCnfXorNeg ei st prems params
  | .cnfItePos      => ruleCnfItePos ei st prems params
  | .cnfIteNeg      => ruleCnfIteNeg ei st prems params
  | .iteEq          => ruleIteEq ei st prems params
  | .distinctValues => ruleDistinctValues ei st prems params
  | .resolution     => ruleResolution bi ei st prems params
  | .factoring      => ruleFactoring st prems params
  | .reordering     => ruleReordering st prems params
  | .absorb         => ruleAbsorb ei st prems params
  | .aciNorm        => ruleAciNorm ei st prems params
  | .polyNorm       => rulePolyNorm ei st prems params
  | .polyNormEq     => rulePolyNormEq st prems params
  | .rewrite        => ruleRewrite tbl bi ei st prems params
  | .bitblast       => ruleBitblast bi ei st prems params
  | _               => none

/-- Premise step numbers to fact indices. -/
def getFacts (facts : Array Nat) : List Nat → Option (List Nat)
  | [] => some []
  | k :: rest =>
    match facts[k]?, getFacts facts rest with
    | some f, some fs => some (f :: fs)
    | _, _ => none

/-- An expression-valued step parameter is a node *position* in the
file; translate it to a dense index, then to its canonical index. -/
def exprIdx (posmap : Std.HashMap Nat Nat) (remap : Array Nat) (p : Nat) : Option Nat :=
  (posmap[p]?).bind (fun d => remap[d]?)

def replay (tbl : Nat → Option RwRule) (goal : Nat) (bi : Builtins) (ei : EI) : List Step → St → Option St
  | [], st => some st
  | s :: rest, st =>
    match getFacts st.facts s.premises.toList with
    | some prems =>
      match applyRule tbl goal bi ei st s.rule prems s.params.toList with
      | some (st', f) => replay tbl goal bi ei rest (st'.addFact f)
      | none => none
    | none => none

/-- The one ASSUME step's expression (raw index), if there is exactly one. -/
def findGoal (steps : Array Step) : Option Nat :=
  let assumes := steps.toList.filter (·.rule = .assume)
  match assumes with
  | [s] => match s.params.toList with
    | [g] => some g
    | _ => none
  | _ => none

def initSt : St := { pool := #[], tys := #[], index := {}, facts := #[] }

/-- The checker, given the position map of the raw pool. -/
def checkWith (tbl : Nat → Option RwRule) (p : RawProof) (posmap : Std.HashMap Nat Nat) : Option Nat :=
  match pushNode initSt ⟨.boolVal true, #[]⟩ with
  | none => none
  | some (st0, tt) =>
    match pushNode st0 ⟨.boolVal false, #[]⟩ with
    | none => none
    | some (st1, ff) =>
      match canonicalize p.pool st1 with
      | none => none
      | some (st2, remap) =>
        match findGoal p.steps with
        | none => none
        | some gpos =>
          match posmap[gpos]? with
          | none => none
          | some graw =>
            match remap[graw]? with
            | none => none
            | some g =>
              match replay tbl g ⟨tt, ff⟩ (exprIdx posmap remap) p.steps.toList st2 with
              | none => none
              | some st3 =>
                match st3.facts[st3.facts.size - 1]? with
                | some last => if last = ff then some graw else none
                | none => none

/-- **The checker**, parametric in the rewrite table.  Returns the
(dense) index in `p.pool` of the refuted goal. -/
def check (tbl : Nat → Option RwRule) (p : RawProof) : Option Nat := checkWith tbl p (positionMap p.pool)

end Bcf
