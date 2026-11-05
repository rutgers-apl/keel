import EmbC.Syntax

/-!
# EmbC: values and the block memory model

Memory is a growing sequence of *blocks*, as in CompCert.  A pointer is a
block number plus a cell offset; arithmetic never leaves its block.  Block
numbers are never reused, so a pointer into a freed block is recognisably
dead and any use of it is a stuck state.

Cells hold whole values rather than bytes: every block has one element type
(or is a single struct) and is only ever read and written at that type.
-/

namespace EmbC

inductive Val where
  | u32 (v : BitVec 32)
  | u64 (v : BitVec 64)
  | ptr (b off : Nat)
  | null
  /-- An opaque `bpfptr_t` handle. -/
  | uptr
  /-- Contents of memory the kernel has not initialised.  Reading it is stuck. -/
  | undef
  deriving DecidableEq, Repr, Inhabited

def Val.ofBool (b : Bool) : Val := .u32 (if b then 1 else 0)

/-- An integer value used as an array index or element count. -/
def Val.toIdx : Val → Option Nat
  | .u32 v => some v.toNat
  | .u64 v => some v.toNat
  | _ => none

/-- The all-zero-bytes value of a type. -/
def Ty.zero : Ty → Val
  | .u32 => .u32 0
  | .u64 => .u64 0
  | .ptr _ => .null
  | .struct _ => .undef
  | .bpfptr => .undef

structure Block where
  /-- Element type of an array block, or `struct s` for a single struct. -/
  elem : Ty
  cells : Array Val
  deriving DecidableEq, Repr, Inhabited

/-- `none` marks a freed block. -/
structure Mem where
  blocks : Array (Option Block)
  deriving Repr, Inhabited

def Mem.empty : Mem := ⟨#[]⟩

/-- The live block with this number, if any. -/
def Mem.block? (m : Mem) (b : Nat) : Option Block :=
  match m.blocks[b]? with
  | some (some blk) => some blk
  | _ => none

/-- Does a value inhabit a C type?  A non-null pointer must point into a
live block of the right element type. -/
def Mem.hasTy (m : Mem) : Val → Ty → Bool
  | .u32 _, .u32 => true
  | .u64 _, .u64 => true
  | .null, .ptr _ => true
  | .uptr, .bpfptr => true
  | .ptr b _, .ptr t =>
    match m.block? b with
    | some blk => blk.elem == t
    | none => false
  | _, _ => false

def Ty.isStruct : Ty → Bool
  | .struct _ => true
  | _ => false

/-- Read cell `i` of array block `b`. -/
def Mem.loadArr (m : Mem) (b i : Nat) : Option Val :=
  match m.block? b with
  | none => none
  | some blk =>
    if blk.elem.isStruct then none else
    match blk.cells[i]? with
    | none => none
    | some .undef => none
    | some v => some v

/-- Overwrite cell `i` of live block `b` (no type check).  Written with
`Array.modify` so that the interpreter updates large blocks in place. -/
def Mem.setCell (m : Mem) (b i : Nat) (v : Val) : Mem :=
  ⟨m.blocks.modify b (fun ob =>
    match ob with
    | some blk => some ⟨blk.elem, blk.cells.setIfInBounds i v⟩
    | none => none)⟩

/-- Write cell `i` of array block `b`. -/
def Mem.storeArr (m : Mem) (b i : Nat) (v : Val) : Option Mem :=
  match m.block? b with
  | none => none
  | some blk =>
    if blk.elem.isStruct then none else
    if m.hasTy v blk.elem ∧ i < blk.cells.size then some (m.setCell b i v) else none

/-- Resolve field `f` of the struct stored in block `b`: its cell index and type. -/
def Mem.fieldSlot (P : Prog) (m : Mem) (b : Nat) (f : String) : Option (Block × Nat × Ty) :=
  match m.block? b with
  | none => none
  | some blk =>
    match blk.elem with
    | .struct s =>
      match P.findStruct s with
      | none => none
      | some d =>
        match d.field? f with
        | none => none
        | some (i, t) => some (blk, i, t)
    | _ => none

def Mem.loadField (P : Prog) (m : Mem) (b : Nat) (f : String) : Option Val :=
  match m.fieldSlot P b f with
  | none => none
  | some (blk, i, _) =>
    match blk.cells[i]? with
    | none => none
    | some .undef => none
    | some v => some v

def Mem.storeField (P : Prog) (m : Mem) (b : Nat) (f : String) (v : Val) : Option Mem :=
  match m.fieldSlot P b f with
  | none => none
  | some (blk, i, t) =>
    if m.hasTy v t ∧ i < blk.cells.size then some (m.setCell b i v) else none

/-- Overwrite cells `off, off+1, …` of block `b` with `vs`. -/
def Mem.fill (m : Mem) (b off : Nat) (vs : List Val) : Mem :=
  ⟨m.blocks.modify b (fun ob =>
    match ob with
    | some blk => some ⟨blk.elem, (vs.zipIdx).foldl (fun cells (v, k) => cells.setIfInBounds (off + k) v) blk.cells⟩
    | none => none)⟩

/-- Add a fresh block; its number is the old block count. -/
def Mem.alloc (m : Mem) (t : Ty) (cells : Array Val) : Nat × Mem :=
  (m.blocks.size, ⟨m.blocks.push (some ⟨t, cells⟩)⟩)

def Mem.free (m : Mem) (b : Nat) : Mem := ⟨m.blocks.setIfInBounds b none⟩

end EmbC
