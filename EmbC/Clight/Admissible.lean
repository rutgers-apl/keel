import EmbC.Clight.Representation

/-!
# Admissibility for the EmbC-to-Clight refinement statement

The source interpreter uses natural numbers for cell offsets.  Clight uses
machine pointer offsets, so the refinement is restricted to executions whose
intermediate memories and pointer values fit that representation.  These are
definitions of the theorem's side conditions, not additional assumed proofs.
-/

namespace EmbC.Clight

/-- All named structs occurring in a type have a source definition. -/
def validType (P : Prog) : Ty → Prop
  | .struct s => (P.findStruct s).isSome = true
  | .ptr t => validType P t
  | _ => True

/-- Types stored in fields, parameters, locals, and return values. -/
def scalarType (P : Prog) (t : Ty) : Prop :=
  t.isStruct = false ∧ validType P t

/-- Source declaration hygiene and a successfully constructed Clight layout. -/
def wellFormed (P : Prog) : Prop :=
  (P.structs.map (·.name)).Nodup ∧
  ((P.fns.map (·.name)) ++ P.consts.map (·.name)).Nodup ∧
  (∀ table ∈ P.consts,
    (table.words.size : Int) * 4 ≤ CC.Integers.Ptrofs.max_unsigned) ∧
  (∀ d ∈ P.structs,
    (d.fields.map (·.1)).Nodup ∧ ∀ field ∈ d.fields, scalarType P field.2) ∧
  (∀ fn ∈ P.fns,
    ((fn.params ++ fn.locals).map (·.1)).Nodup ∧
    (∀ decl ∈ fn.params ++ fn.locals, scalarType P decl.2) ∧
    ∀ t ∈ fn.ret.toList, scalarType P t) ∧
  (∃ ce, CC.buildCompositeEnv (composites P) = .OK ce)

/-- A live source pointer's byte offset can be represented without wrapping.
For dead blocks only the raw offset is available here; the representation
relation checks its byte offset using the injection's historical stride. -/
def valueFits (P : Prog) (m : Mem) : Val → Prop
  | .ptr b off =>
    match m.block? b with
    | some blk =>
      (if blk.elem.isStruct then off = 0 else off ≤ blk.cells.size) ∧
      0 ≤ byteSize P blk.elem ∧
      (off : Int) * byteSize P blk.elem ≤ CC.Integers.Ptrofs.max_unsigned
    | none => (off : Int) ≤ CC.Integers.Ptrofs.max_unsigned
  | _ => True

/-- All live block extents and stored pointer offsets fit machine pointers. -/
def memoryFits (P : Prog) (m : Mem) : Prop :=
  Representable P m ∧
  ∀ b blk, m.block? b = some blk →
    0 < blockByteSize P blk ∧
    blockByteSize P blk ≤ CC.Integers.Ptrofs.max_unsigned ∧
    ∀ v ∈ blk.cells.toList, valueFits P m v

def envFits (P : Prog) (m : Mem) (env : Env) : Prop :=
  ∀ binding ∈ env, valueFits P m binding.2.2

def argsFits (P : Prog) (m : Mem) (vs : List Val) : Prop :=
  ∀ v ∈ vs, valueFits P m v

end EmbC.Clight
