import Bcf.Syntax

/-!
# BCF semantics

The stated meaning of every operator (`Op.eval`), lifted to pool nodes
by `eval`.  A variable of width `w` reads its assigned natural number
modulo `2^w`; every assignment is therefore well-typed and no runtime
state is excluded.

Division, remainder, and shifts follow SMT-LIB (the semantics cvc5's
rules are stated for): `bvudiv x 0 = ~0`, `bvurem x 0 = x`, and a
shift by at least the width gives 0 (or the sign fill for `bvashr`).
-/

namespace Bcf

inductive Val where
  | bv   (w : Nat) (v : BitVec w)
  | bool (b : Bool)
  | list (elemBool : Bool) (vs : List Val)
  | bad
  deriving Repr, Inhabited

abbrev Assign := Nat → Nat

namespace Val

def ty : Val → Option Ty
  | .bv w _ => some (.bv w)
  | .bool _ => some .bool
  | .list e vs => some (.list e vs.length)
  | .bad => none

def asBv (w : Nat) : Val → Option (BitVec w)
  | .bv w' v => if h : w' = w then some (v.cast h) else none
  | _ => none

def asBool : Val → Option Bool
  | .bool b => some b
  | _ => none

/-- Interpret an if-then-else condition: a boolean, or a 1-bit vector. -/
def asCond : Val → Option Bool
  | .bool b => some b
  | .bv n v => if n = 1 then some (v.getLsbD 0) else none
  | _ => none

def bvs (w : Nat) : List Val → Option (List (BitVec w))
  | [] => some []
  | v :: rest =>
    match asBv w v, bvs w rest with
    | some x, some xs => some (x :: xs)
    | _, _ => none

def bools : List Val → Option (List Bool)
  | [] => some []
  | v :: rest =>
    match asBool v, bools rest with
    | some x, some xs => some (x :: xs)
    | _, _ => none

def tys : List Val → Option (List Ty)
  | [] => some []
  | v :: rest =>
    match v.ty, tys rest with
    | some t, some ts => some (t :: ts)
    | _, _ => none

@[simp] theorem ty_bv (w : Nat) (x : BitVec w) : (Val.bv w x).ty = some (.bv w) := rfl
@[simp] theorem ty_bool (b : Bool) : (Val.bool b).ty = some .bool := rfl
@[simp] theorem ty_list (e : Bool) (vs : List Val) : (Val.list e vs).ty = some (.list e vs.length) := rfl
@[simp] theorem ty_bad : Val.bad.ty = none := rfl
@[simp] theorem ty_ite (p : Prop) [Decidable p] (a b : Val) :
    (if p then a else b).ty = if p then a.ty else b.ty := by split <;> rfl
@[simp] theorem ty_dite (p : Prop) [Decidable p] (a : p → Val) (b : ¬p → Val) :
    (dite p a b).ty = dite p (fun h => (a h).ty) (fun h => (b h).ty) := by split <;> rfl
@[simp] theorem asBv_bv (w w' : Nat) (x : BitVec w') :
    asBv w (.bv w' x) = if h : w' = w then some (x.cast h) else none := rfl
@[simp] theorem asBv_bool (w : Nat) (b : Bool) : asBv w (.bool b) = none := rfl
@[simp] theorem asBv_list (w : Nat) (e : Bool) (vs : List Val) : asBv w (.list e vs) = none := rfl
@[simp] theorem asBv_bad (w : Nat) : asBv w .bad = none := rfl
@[simp] theorem asBool_bv (w : Nat) (x : BitVec w) : asBool (.bv w x) = none := rfl
@[simp] theorem asBool_bool (b : Bool) : asBool (.bool b) = some b := rfl
@[simp] theorem asBool_list (e : Bool) (vs : List Val) : asBool (.list e vs) = none := rfl
@[simp] theorem asBool_bad : asBool .bad = none := rfl
@[simp] theorem tys_nil : tys [] = some [] := rfl
@[simp] theorem tys_cons (v : Val) (vs : List Val) :
    tys (v :: vs) = match v.ty, tys vs with
      | some t, some ts => some (t :: ts)
      | _, _ => none := rfl

/-- Concatenation of a non-empty list of bit-vectors, first argument
most significant. -/
def concatVals : List Val → Option Val
  | [] => none
  | [.bv n x] => some (.bv n x)
  | .bv n x :: rest =>
    match concatVals rest with
    | some (.bv m y) => some (.bv (n + m) (x ++ y))
    | _ => none
  | _ => none

end Val

/-! ## Operator semantics

One evaluator per typing combinator.  Each evaluator returns `bad`
exactly when the corresponding typing combinator returns `none`
(`Typing.lean` proves this). -/

def bvVarEval (ρ : Assign) (w id : Nat) : List Val → Val
  | [] => if w ≠ 0 then .bv w (BitVec.ofNat w (ρ id)) else .bad
  | _ => .bad

def bvValEval (w v : Nat) : List Val → Val
  | [] => if w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w then .bv w (BitVec.ofNat w v) else .bad
  | _ => .bad

def bvIteEval (w : Nat) : List Val → Val
  | [c, a, b] =>
    match Val.asCond c, Val.asBv w a, Val.asBv w b with
    | some cb, some x, some y => if w ≠ 0 then .bv w (if cb then x else y) else .bad
    | _, _, _ => .bad
  | _ => .bad

def bvUn (w : Nat) (f : BitVec w → BitVec w) : List Val → Val
  | [a] => match Val.asBv w a with
    | some x => if w ≠ 0 then .bv w (f x) else .bad
    | none => .bad
  | _ => .bad

def bvExtractEval (hi lo : Nat) : List Val → Val
  | [.bv n x] => if lo ≤ hi ∧ hi < n then .bv (hi - lo + 1) (x.extractLsb hi lo) else .bad
  | _ => .bad

def bvExtEval (signed : Bool) (w e : Nat) : List Val → Val
  | [.bv n x] => if w ≠ 0 ∧ n + e = w then .bv w (if signed then x.signExtend w else x.setWidth w) else .bad
  | _ => .bad

def bvSizeEval (w : Nat) : List Val → Val
  | [.bv n _] => if w ≠ 0 ∧ n < 2 ^ w then .bv w (BitVec.ofNat w n) else .bad
  | _ => .bad

def bvRepeatEval (w k : Nat) : List Val → Val
  | [.bv m x] => if h : w ≠ 0 ∧ m * k = w then .bv w ((x.replicate k).cast h.2) else .bad
  | _ => .bad

def bvBin (w : Nat) (f : BitVec w → BitVec w → BitVec w) : List Val → Val
  | [a, b] => match Val.asBv w a, Val.asBv w b with
    | some x, some y => if w ≠ 0 then .bv w (f x y) else .bad
    | _, _ => .bad
  | _ => .bad

/-- Same-width n-ary bit-vector operator. -/
def bvN (w : Nat) (f : List (BitVec w) → BitVec w) (vs : List Val) : Val :=
  match Val.bvs w vs with
  | some xs => if w ≠ 0 ∧ 2 ≤ xs.length then .bv w (f xs) else .bad
  | none => .bad

def bvConcatEval (w : Nat) (vs : List Val) : Val :=
  match Val.concatVals vs with
  | some (.bv n x) => if h : w ≠ 0 ∧ n = w ∧ 2 ≤ vs.length then .bv w (x.cast h.2.1) else .bad
  | _ => .bad

def bvFromBoolEval (vs : List Val) : Val :=
  match Val.bools vs with
  | some bs => if 1 ≤ bs.length then .bv bs.length (BitVec.ofBoolListLE bs) else .bad
  | none => .bad

def boolConstEval (b : Bool) : List Val → Val
  | [] => .bool b
  | _ => .bad

def boolNotEval : List Val → Val
  | [.bool a] => .bool (!a)
  | _ => .bad

def bitofEval (i : Nat) : List Val → Val
  | [.bv n x] => if i < n then .bool (x.getLsbD i) else .bad
  | _ => .bad

def Val.eqv : Val → Val → Val
  | .bool a, .bool b => .bool (decide (a = b))
  | .bv n x, .bv m y => if h : m = n then .bool (decide (x = y.cast h)) else .bad
  | _, _ => .bad

def eqEval (neg : Bool) : List Val → Val
  | [a, b] => match Val.eqv a b with
    | .bool r => .bool (if neg then !r else r)
    | _ => .bad
  | _ => .bad

def bvCmp (f : {w : Nat} → BitVec w → BitVec w → Bool) : List Val → Val
  | [.bv n x, .bv m y] => if h : m = n then .bool (f x (y.cast h)) else .bad
  | _ => .bad

def impliesEval : List Val → Val
  | [.bool a, .bool b] => .bool (!a || b)
  | _ => .bad

def boolIteEval : List Val → Val
  | [.bool c, .bool a, .bool b] => .bool (if c then a else b)
  | _ => .bad

def boolN (f : List Bool → Bool) (vs : List Val) : Val :=
  match Val.bools vs with
  | some bs => if 2 ≤ bs.length then .bool (f bs) else .bad
  | none => .bad

def listEval (e : Bool) (vs : List Val) : Val :=
  match Val.tys vs with
  | some tys => if tys.all (Ty.inClass e) then .list e vs else .bad
  | none => .bad

def Op.eval (ρ : Assign) : Op → List Val → Val
  | .bvVar w id       => bvVarEval ρ w id
  | .bvVal w v        => bvValEval w v
  | .bvIte w          => bvIteEval w
  | .bvNeg w          => bvUn w (- ·)
  | .bvNot w          => bvUn w (~~~ ·)
  | .bvExtract hi lo  => bvExtractEval hi lo
  | .bvSignExtend w e => bvExtEval true w e
  | .bvZeroExtend w e => bvExtEval false w e
  | .bvSize w         => bvSizeEval w
  | .bvRepeat w k     => bvRepeatEval w k
  | .bvSub w          => bvBin w (· - ·)
  | .bvShl w          => bvBin w (fun x y => x <<< y)
  | .bvLshr w         => bvBin w (fun x y => x >>> y)
  | .bvAshr w         => bvBin w (fun x y => x.sshiftRight y.toNat)
  | .bvUdiv w         => bvBin w BitVec.smtUDiv
  | .bvUrem w         => bvBin w BitVec.umod
  | .bvSdiv w         => bvBin w BitVec.smtSDiv
  | .bvSmod w         => bvBin w BitVec.smod
  | .bvAdd w          => bvN w (List.foldl (· + ·) 0)
  | .bvMul w          => bvN w (List.foldl (· * ·) 1)
  | .bvOr w           => bvN w (List.foldl (· ||| ·) 0)
  | .bvAnd w          => bvN w (List.foldl (· &&& ·) (BitVec.allOnes w))
  | .bvXor w          => bvN w (List.foldl (· ^^^ ·) 0)
  | .bvConcat w       => bvConcatEval w
  | .bvFromBool       => bvFromBoolEval
  | .boolVal b        => boolConstEval b
  | .boolVar id       => boolConstEval (ρ id != 0)
  | .boolNot          => boolNotEval
  | .boolBitof i      => bitofEval i
  | .eq               => eqEval false
  | .distinct         => eqEval true
  | .ugt              => bvCmp (fun x y => y.ult x)
  | .uge              => bvCmp (fun x y => y.ule x)
  | .sgt              => bvCmp (fun x y => y.slt x)
  | .sge              => bvCmp (fun x y => y.sle x)
  | .ult              => bvCmp BitVec.ult
  | .ule              => bvCmp BitVec.ule
  | .slt              => bvCmp BitVec.slt
  | .sle              => bvCmp BitVec.sle
  | .implies          => impliesEval
  | .boolIte          => boolIteEval
  | .conj             => boolN (List.all · id)
  | .disj             => boolN (List.any · id)
  | .boolXor          => boolN (List.foldl (fun acc b => acc ^^ b) false)
  | .listVal e        => listEval e

/-! ## Pool evaluation -/

def evalF (pool : Pool) (ρ : Assign) : Nat → Nat → Val
  | 0, _ => .bad
  | fuel + 1, i =>
    match pool[i]? with
    | none => .bad
    | some n =>
      n.op.eval ρ (n.args.toList.map (fun a => if a < i then evalF pool ρ fuel a else .bad))

def eval (pool : Pool) (ρ : Assign) (i : Nat) : Val := evalF pool ρ (i + 1) i

/-- "Node `i` is true in state `ρ`." -/
def holds (pool : Pool) (ρ : Assign) (i : Nat) : Prop := eval pool ρ i = .bool true

theorem evalF_stable (pool : Pool) (ρ : Assign) (i : Nat) :
    ∀ f f', i < f → i < f' → evalF pool ρ f i = evalF pool ρ f' i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f f' hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [evalF]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      congr 1
      apply List.map_congr_left
      intro a _
      split
      · exact ih a (by assumption) g g' (by omega) (by omega)
      · rfl

theorem eval_unfold (pool : Pool) (ρ : Assign) (i : Nat) :
    eval pool ρ i =
      match pool[i]? with
      | none => .bad
      | some n => n.op.eval ρ (n.args.toList.map (fun a => if a < i then eval pool ρ a else .bad)) := by
  unfold eval
  conv => lhs; rw [evalF]
  cases pool[i]? with
  | none => rfl
  | some n =>
    simp only
    congr 1
    apply List.map_congr_left
    intro a _
    split
    · exact evalF_stable pool ρ a _ _ (by assumption) (by omega)
    · rfl

/-- In a well-formed pool the guards are redundant. -/
theorem eval_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {i : Nat} {n : Node}
    (h : pool[i]? = some n) :
    eval pool ρ i = n.op.eval ρ (n.args.toList.map (eval pool ρ)) := by
  rw [eval_unfold, h]
  simp only
  congr 1
  apply List.map_congr_left
  intro a ha
  have := (hwf i n h).1 a (by simpa using ha)
  simp [this]

/-- Evaluation of existing nodes is unchanged when the pool grows. -/
theorem eval_extend {pool pool' : Pool} (ρ : Assign)
    (hpre : ∀ j, j < pool.size → pool'[j]? = pool[j]?) :
    ∀ i, i < pool.size → eval pool' ρ i = eval pool ρ i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    rw [eval_unfold, eval_unfold, hpre i hi]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      congr 1
      apply List.map_congr_left
      intro a _
      split
      · exact ih a (by assumption) (by omega)
      · rfl

theorem eval_push {pool : Pool} (ρ : Assign) (n : Node) {i : Nat} (hi : i < pool.size) :
    eval (pool.push n) ρ i = eval pool ρ i :=
  eval_extend ρ (fun j hj => by rw [Array.getElem?_push]; simp [Nat.ne_of_lt hj]) i hi

theorem holds_push {pool : Pool} (ρ : Assign) (n : Node) {i : Nat} (hi : i < pool.size) :
    holds (pool.push n) ρ i ↔ holds pool ρ i := by
  unfold holds; rw [eval_push ρ n hi]

end Bcf
