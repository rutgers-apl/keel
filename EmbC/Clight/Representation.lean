import EmbC.Semantics
import CCLib.Clight

/-! Concrete representation of EmbC's typed cells in CLight's byte memory.
    The dependency fixes CompCert's 64-bit target architecture. -/

namespace EmbC.Clight

def type : EmbC.Ty → CC.Ty
  | .u32 => CC.tuint
  | .u64 => CC.tulong
  | .ptr t => CC.tptr (type t)
  | .struct s => .Tstruct (CC.identOfString s) CC.noattr
  | .bpfptr => CC.tptr .Tvoid

def members (d : EmbC.StructDef) : List CC.Member :=
  d.fields.map fun (f, t) => .Member_plain (CC.identOfString f) (type t)

def composites (P : EmbC.Prog) : List CC.CompositeDef :=
  P.structs.map fun d => .Composite (CC.identOfString d.name) .Struct (members d) CC.noattr

/-- Failed layouts use the empty environment; related memories require success. -/
def compositeEnv (P : EmbC.Prog) : CC.CompositeEnv :=
  match CC.buildCompositeEnv (composites P) with
  | .OK env => env
  | .Error _ => CC.PTree.empty

def byteSize (P : EmbC.Prog) (t : EmbC.Ty) : CC.Z :=
  CC.sizeof (compositeEnv P) (type t)

def blockByteSize (P : EmbC.Prog) (blk : EmbC.Block) : CC.Z :=
  if blk.elem.isStruct then byteSize P blk.elem
  else (blk.cells.size : CC.Z) * byteSize P blk.elem

/-- Block names can change for new allocations, while existing names stay fixed.
    The opaque input handle is a pointer whose contents are governed by the
    external-call contract rather than by the source heap. -/
structure MemoryInjection where
  block : Nat → CC.Block
  injective : ∀ a b, block a = block b → a = b
  /-- Retained after a source block is freed, whose element type is then lost. -/
  stride : Nat → Nat
  stride_positive : ∀ b, 0 < stride b
  opaqueBlock : CC.Block
  opaqueOffset : CC.Integers.Ptrofs

def MemoryInjection.opaqueHandle (j : MemoryInjection) : CC.Val :=
  .Vptr j.opaqueBlock j.opaqueOffset

def MemoryInjection.Extends (old new : MemoryInjection) (m : EmbC.Mem) : Prop :=
  new.opaqueHandle = old.opaqueHandle ∧
  ∀ b, b < m.blocks.size → new.block b = old.block b ∧ new.stride b = old.stride b

def valRel (_P : EmbC.Prog) (m : EmbC.Mem) (j : MemoryInjection) :
    EmbC.Val → CC.Val → Prop
  | .u32 v, w => w = .Vint v
  | .u64 v, w => w = .Vlong v
  | .null, w => w = CC.Val.Vnullptr
  | .uptr, w => w = j.opaqueHandle
  | .undef, w => w = .Vundef
  | .ptr b off, w => b < m.blocks.size ∧ off * j.stride b < 2 ^ 64 ∧
      w = .Vptr (j.block b) (CC.Integers.Ptrofs.repr ((off * j.stride b : Nat) : CC.Z))

def retRel (P : EmbC.Prog) (m : EmbC.Mem) (j : MemoryInjection) :
    Option EmbC.Val → CC.Val → Prop
  | none, w => w = .Vundef
  | some v, w => valRel P m j v w

/-- Uninitialised source cells represent an uninitialised target load. -/
def cellRel (P : EmbC.Prog) (m : EmbC.Mem) (j : MemoryInjection)
    (cm : CC.Mem) (b : Nat) (off : CC.Z) (t : EmbC.Ty) (v : EmbC.Val) : Prop :=
  ∃ chunk w, CC.accessMode (type t) = .By_value chunk ∧
    CC.Mem.load chunk cm (j.block b) off = some w ∧ valRel P m j v w

/-- Dangling pointers retain their representation but cannot be dereferenced.
    EmbC erases a freed block's type, so only live pointers can be type-checked. -/
def cellTyped (m : EmbC.Mem) (v : EmbC.Val) (t : EmbC.Ty) : Prop :=
  v = .undef ∨ m.hasTy v t = true ∨
  ∃ b off elem, v = .ptr b off ∧ t = .ptr elem ∧
    b < m.blocks.size ∧ m.block? b = none

/-- Source cell types and dimensions admitted by the byte representation. -/
def Representable (P : EmbC.Prog) (m : EmbC.Mem) : Prop :=
  CC.buildCompositeEnv (composites P) = .OK (compositeEnv P) ∧
  ∀ b blk, m.block? b = some blk →
    0 < blockByteSize P blk ∧ blockByteSize P blk < (2 : CC.Z) ^ 64 ∧
    match blk.elem with
    | .struct s => ∃ d, P.findStruct s = some d ∧ blk.cells.size = d.fields.length ∧
        ∀ (i : Nat) f t v, d.fields[i]? = some (f, t) → blk.cells[i]? = some v →
          cellTyped m v t
    | t => ∀ (i : Nat) v, blk.cells[i]? = some v → cellTyped m v t

/-- A struct uses its actual CLight layout; an array uses scaled cell offsets.
    Freed source blocks have no current target permissions. Other target blocks
    (globals, frames, and external storage) are unconstrained. -/
def memoryRel (P : EmbC.Prog) (j : MemoryInjection)
    (m : EmbC.Mem) (cm : CC.Mem) : Prop :=
  Representable P m ∧
  (∀ b, b < m.blocks.size → CC.Mem.validBlock cm (j.block b) = true) ∧
  (∀ b blk, m.block? b = some blk →
    CC.Mem.validBlock cm (j.block b) = true ∧
    (j.stride b : CC.Z) = byteSize P blk.elem ∧
    CC.Mem.rangePerm cm (j.block b) 0 (blockByteSize P blk) .Cur .Freeable = true ∧
    match blk.elem with
    | .struct s => ∃ d co, P.findStruct s = some d ∧
        (compositeEnv P).get (CC.identOfString s) = some co ∧
        co.co_su = .Struct ∧ co.co_members = members d ∧
        ∀ (i : Nat) f t v, d.fields[i]? = some (f, t) → blk.cells[i]? = some v →
          ∃ off, CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members =
            .OK (off, .Full) ∧ cellRel P m j cm b off t v
    | t => ∀ (i : Nat) v, blk.cells[i]? = some v →
        cellRel P m j cm b ((i : CC.Z) * byteSize P t) t v) ∧
  (∀ b, m.blocks[b]? = some none →
    ∀ off, CC.Mem.perm cm (j.block b) off .Cur .Nonempty = false)

end EmbC.Clight
