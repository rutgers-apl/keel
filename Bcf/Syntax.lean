/-!
# BCF syntax: typed nodes in an expression pool

This mirrors `struct bcf_expr` from the kernel's BCF checker.  A proof
carries a pool of expression nodes; each node names an operator and the
pool indices of its children, which must be *earlier* nodes.  Operators
carry the parameters the binary format encodes in `params` (bit width,
extract range, extension size, ...).  Variables carry their pool index
as an identity, because BCF identifies a variable by node identity.

`Op.resultTy` is the type checker of `type_check_bv`/`type_check_bool`/
`type_check_list` from `bcf_checker.c`, one case per operator.
-/

namespace Bcf

inductive Ty where
  | bool
  | bv (w : Nat)
  /-- A list of `n` booleans (`elemBool = true`) or of `n` bit-vectors of any widths. -/
  | list (elemBool : Bool) (n : Nat)
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Membership of a type in a list element class. -/
def Ty.inClass (elemBool : Bool) : Ty → Bool
  | .bool => elemBool
  | .bv _ => !elemBool
  | .list _ _ => false

def Ty.isScalar : Ty → Bool
  | .bool => true
  | .bv _ => true
  | .list _ _ => false

/-- Both are bit-vectors of the same width. -/
def Ty.sameBv : Ty → Ty → Bool
  | .bv w, .bv w' => w == w'
  | _, _ => false

inductive Op where
  -- bit-vector operators (w is the result width)
  | bvVar (w : Nat) (id : Nat)
  | bvVal (w : Nat) (v : Nat)
  | bvIte (w : Nat)
  | bvNeg (w : Nat)
  | bvNot (w : Nat)
  | bvExtract (hi lo : Nat)
  | bvSignExtend (w ext : Nat)
  | bvZeroExtend (w ext : Nat)
  | bvSize (w : Nat)
  | bvRepeat (w k : Nat)
  | bvSub (w : Nat)
  | bvShl (w : Nat)
  | bvLshr (w : Nat)
  | bvAshr (w : Nat)
  | bvUdiv (w : Nat)
  | bvUrem (w : Nat)
  | bvSdiv (w : Nat)
  | bvSmod (w : Nat)
  | bvAdd (w : Nat)
  | bvMul (w : Nat)
  | bvOr (w : Nat)
  | bvAnd (w : Nat)
  | bvXor (w : Nat)
  | bvConcat (w : Nat)
  | bvFromBool
  -- boolean operators
  | boolVal (b : Bool)
  | boolVar (id : Nat)
  | boolNot
  | boolBitof (i : Nat)
  | eq
  | distinct
  | ugt | uge | sgt | sge | ult | ule | slt | sle
  | implies
  | boolIte
  | conj
  | disj
  | boolXor
  -- lists (only used as rule parameters)
  | listVal (elemBool : Bool)
  deriving DecidableEq, Repr, Hashable, Inhabited

structure Node where
  op   : Op
  args : Array Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

abbrev Pool := Array Node

/-! ## Typing -/

def allBv (w : Nat) : List Ty → Bool
  | [] => true
  | .bv w' :: rest => w' == w && allBv w rest
  | _ => false

def allBool : List Ty → Bool
  | [] => true
  | .bool :: rest => allBool rest
  | _ => false

/-- Sum of the widths of a non-empty list of bit-vector types. -/
def bvWidths : List Ty → Option Nat
  | [.bv n] => some n
  | .bv n :: rest => (bvWidths rest).map (n + ·)
  | _ => none

/-- `tyGuard p t` is `some t` when `p` holds. -/
def tyGuard (p : Prop) [Decidable p] (t : Ty) : Option Ty := if p then some t else none

/-! Typing combinators, one per operator shape.  `Op.resultTy` maps each
operator to one of these; `Op.eval` maps it to the matching evaluator. -/

def bvVarTy (w : Nat) : List Ty → Option Ty
  | [] => tyGuard (w ≠ 0) (.bv w)
  | _ => none

def bvValTy (w v : Nat) : List Ty → Option Ty
  | [] => tyGuard (w ≠ 0 ∧ w ≤ 64 ∧ v < 2 ^ w) (.bv w)
  | _ => none

def bvIteTy (w : Nat) : List Ty → Option Ty
  | [c, a, b] => tyGuard (w ≠ 0 ∧ (c = .bool ∨ c = .bv 1) ∧ a = .bv w ∧ b = .bv w) (.bv w)
  | _ => none

def bvUnTy (w : Nat) : List Ty → Option Ty
  | [a] => tyGuard (w ≠ 0 ∧ a = .bv w) (.bv w)
  | _ => none

def bvExtractTy (hi lo : Nat) : List Ty → Option Ty
  | [.bv n] => tyGuard (lo ≤ hi ∧ hi < n) (.bv (hi - lo + 1))
  | _ => none

def bvExtTy (w e : Nat) : List Ty → Option Ty
  | [.bv n] => tyGuard (w ≠ 0 ∧ n + e = w) (.bv w)
  | _ => none

def bvSizeTy (w : Nat) : List Ty → Option Ty
  | [.bv n] => tyGuard (w ≠ 0 ∧ n < 2 ^ w) (.bv w)
  | _ => none

def bvRepeatTy (w k : Nat) : List Ty → Option Ty
  | [.bv m] => tyGuard (w ≠ 0 ∧ m * k = w) (.bv w)
  | _ => none

def bvBinTy (w : Nat) : List Ty → Option Ty
  | [a, b] => tyGuard (w ≠ 0 ∧ a = .bv w ∧ b = .bv w) (.bv w)
  | _ => none

def bvNTy (w : Nat) (tys : List Ty) : Option Ty :=
  tyGuard (w ≠ 0 ∧ allBv w tys ∧ 2 ≤ tys.length) (.bv w)

def bvConcatTy (w : Nat) (tys : List Ty) : Option Ty :=
  tyGuard (w ≠ 0 ∧ bvWidths tys = some w ∧ 2 ≤ tys.length) (.bv w)

def bvFromBoolTy (tys : List Ty) : Option Ty :=
  tyGuard (allBool tys ∧ 1 ≤ tys.length) (.bv tys.length)

def boolNullTy : List Ty → Option Ty
  | [] => some .bool
  | _ => none

def boolNotTy : List Ty → Option Ty
  | [a] => tyGuard (a = .bool) .bool
  | _ => none

def bitofTy (i : Nat) : List Ty → Option Ty
  | [.bv n] => tyGuard (i < n) .bool
  | _ => none

def eqTy : List Ty → Option Ty
  | [a, b] => tyGuard (a = b ∧ a.isScalar) .bool
  | _ => none

def cmpTy : List Ty → Option Ty
  | [a, b] => tyGuard (a.sameBv b) .bool
  | _ => none

def impliesTy : List Ty → Option Ty
  | [a, b] => tyGuard (a = .bool ∧ b = .bool) .bool
  | _ => none

def boolIteTy : List Ty → Option Ty
  | [c, a, b] => tyGuard (c = .bool ∧ a = .bool ∧ b = .bool) .bool
  | _ => none

def boolNTy (tys : List Ty) : Option Ty :=
  tyGuard (allBool tys ∧ 2 ≤ tys.length) .bool

def listTy (e : Bool) (tys : List Ty) : Option Ty :=
  tyGuard (tys.all (Ty.inClass e)) (.list e tys.length)

/-- The result type of an operator applied to arguments of the given
types, or `none` if ill-typed, following `type_check_*` in
`bcf_checker.c`. -/
def Op.resultTy : Op → List Ty → Option Ty
  | .bvVar w _        => bvVarTy w
  | .bvVal w v        => bvValTy w v
  | .bvIte w          => bvIteTy w
  | .bvNeg w          => bvUnTy w
  | .bvNot w          => bvUnTy w
  | .bvExtract hi lo  => bvExtractTy hi lo
  | .bvSignExtend w e => bvExtTy w e
  | .bvZeroExtend w e => bvExtTy w e
  | .bvSize w         => bvSizeTy w
  | .bvRepeat w k     => bvRepeatTy w k
  | .bvSub w          => bvBinTy w
  | .bvShl w          => bvBinTy w
  | .bvLshr w         => bvBinTy w
  | .bvAshr w         => bvBinTy w
  | .bvUdiv w         => bvBinTy w
  | .bvUrem w         => bvBinTy w
  | .bvSdiv w         => bvBinTy w
  | .bvSmod w         => bvBinTy w
  | .bvAdd w          => bvNTy w
  | .bvMul w          => bvNTy w
  | .bvOr w           => bvNTy w
  | .bvAnd w          => bvNTy w
  | .bvXor w          => bvNTy w
  | .bvConcat w       => bvConcatTy w
  | .bvFromBool       => bvFromBoolTy
  | .boolVal _        => boolNullTy
  | .boolVar _        => boolNullTy
  | .boolNot          => boolNotTy
  | .boolBitof i      => bitofTy i
  | .eq               => eqTy
  | .distinct         => eqTy
  | .ugt | .uge | .sgt | .sge | .ult | .ule | .slt | .sle => cmpTy
  | .implies          => impliesTy
  | .boolIte          => boolIteTy
  | .conj             => boolNTy
  | .disj             => boolNTy
  | .boolXor          => boolNTy
  | .listVal e        => listTy e

/-! ## Types of pool nodes

`typeOfF` uses fuel so that the recursion is structural; a child may
only be consulted when its index is smaller than the parent's, which
is what makes the result independent of the fuel once it exceeds the
index (`typeOfF_stable`). -/

/-- Map an option-valued function over a list, failing if any element fails. -/
def mapOpt (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: rest =>
    match f a, mapOpt f rest with
    | some b, some bs => some (b :: bs)
    | _, _ => none

def typeOfF (pool : Pool) : Nat → Nat → Option Ty
  | 0, _ => none
  | fuel + 1, i =>
    match pool[i]? with
    | none => none
    | some n =>
      match mapOpt (fun a => if a < i then typeOfF pool fuel a else none) n.args.toList with
      | some tys => n.op.resultTy tys
      | none => none

def typeOf (pool : Pool) (i : Nat) : Option Ty := typeOfF pool (i + 1) i

/-- Well-formed pool: every child index is smaller than its parent's,
and every node type-checks. -/
def WF (pool : Pool) : Prop :=
  ∀ i n, pool[i]? = some n → (∀ a ∈ n.args, a < i) ∧ (typeOf pool i).isSome

/-- Executable well-formedness check. -/
def wfNode (pool : Pool) (i : Nat) : Bool :=
  match pool[i]? with
  | some n => n.args.all (· < i) && (typeOf pool i).isSome
  | none => true

def wf (pool : Pool) : Bool := (List.range pool.size).all (wfNode pool)

theorem mapOpt_congr {f g : α → Option β} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    mapOpt f l = mapOpt g l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [mapOpt]
    rw [h a (by simp), ih (fun a' ha' => h a' (by simp [ha']))]

theorem typeOfF_stable (pool : Pool) (i : Nat) :
    ∀ f f', i < f → i < f' → typeOfF pool f i = typeOfF pool f' i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f f' hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [typeOfF]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      have : mapOpt (fun a => if a < i then typeOfF pool g a else none) n.args.toList =
             mapOpt (fun a => if a < i then typeOfF pool g' a else none) n.args.toList := by
        apply mapOpt_congr
        intro a _
        split
        · exact ih a (by assumption) g g' (by omega) (by omega)
        · rfl
      rw [this]

theorem typeOf_unfold (pool : Pool) (i : Nat) :
    typeOf pool i =
      match pool[i]? with
      | none => none
      | some n =>
        match mapOpt (fun a => if a < i then typeOf pool a else none) n.args.toList with
        | some tys => n.op.resultTy tys
        | none => none := by
  unfold typeOf
  conv => lhs; rw [typeOfF]
  cases pool[i]? with
  | none => rfl
  | some n =>
    simp only
    have : mapOpt (fun a => if a < i then typeOfF pool i a else none) n.args.toList =
           mapOpt (fun a => if a < i then typeOfF pool (a + 1) a else none) n.args.toList := by
      apply mapOpt_congr
      intro a _
      split
      · exact typeOfF_stable pool a _ _ (by assumption) (by omega)
      · rfl
    rw [this]

/-- Types of existing nodes are unchanged when the pool grows. -/
theorem typeOf_extend {pool pool' : Pool}
    (hpre : ∀ j, j < pool.size → pool'[j]? = pool[j]?) :
    ∀ i, i < pool.size → typeOf pool' i = typeOf pool i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    rw [typeOf_unfold, typeOf_unfold, hpre i hi]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      have : mapOpt (fun a => if a < i then typeOf pool' a else none) n.args.toList =
             mapOpt (fun a => if a < i then typeOf pool a else none) n.args.toList := by
        apply mapOpt_congr
        intro a _
        split
        · exact ih a (by assumption) (by omega)
        · rfl
      rw [this]

theorem wf_iff (pool : Pool) : wf pool = true ↔ WF pool := by
  unfold wf WF wfNode
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h i n hn
    have hi : i < pool.size := by
      rcases Nat.lt_or_ge i pool.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hn; cases hn
    have := h i hi
    rw [hn] at this
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] at this
    exact this
  · intro h i hi
    cases hn : pool[i]? with
    | none => rfl
    | some n =>
      obtain ⟨h1, h2⟩ := h i n hn
      simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, decide_eq_true_eq]
      exact ⟨h1, h2⟩

theorem WF.extend {pool pool' : Pool} (hwf : WF pool)
    (hpre : ∀ j, j < pool.size → pool'[j]? = pool[j]?) :
    ∀ i n, i < pool.size → pool'[i]? = some n → (∀ a ∈ n.args, a < i) ∧ (typeOf pool' i).isSome := by
  intro i n hi hn
  rw [hpre i hi] at hn
  rw [typeOf_extend hpre i hi]
  exact hwf i n hn

end Bcf
