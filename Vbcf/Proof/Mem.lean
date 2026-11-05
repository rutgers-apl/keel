import EmbC.Kernel
import Vbcf.Prog
import EmbC.Logic
import Vbcf.Defs

/-!
# Vbcf proofs: the checker's memory, viewed as plain data

Every Vbcf function reaches memory through one `struct ck` and the arrays it
points to.  `CMem` is that memory as plain Lean data, and `Holds m sb c` says
memory `m` contains it, with the struct in block `sb`.  The lemmas here turn
field and array accesses of the EmbC semantics into operations on `CMem`, so
proofs about Vbcf functions never look at blocks directly, except in the few
functions that allocate.

Nothing here is trusted.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

/-- A pointer field: `NULL`, or a block and an offset. -/
abbrev Ptr := Option (Nat × Nat)

def Ptr.val : Ptr → Val
  | none => .null
  | some (b, o) => .ptr b o

@[simp] theorem Ptr.val_none : Ptr.val none = .null := rfl
@[simp] theorem Ptr.val_some (b o : Nat) : Ptr.val (some (b, o)) = .ptr b o := rfl

/-- The field values of a `struct ck`, in declaration order. -/
structure CK where
  pool : Ptr
  plen : BitVec 32
  pcap : BitVec 32
  htab : Ptr
  hcap : BitVec 32
  hcnt : BitVec 32
  facts : Ptr
  flen : BitVec 32
  fcap : BitVec 32
  nexpr : BitVec 32
  stk : Ptr
  sp : BitVec 32
  scap : BitVec 32
  prem : Ptr
  par : Ptr
  proof : Ptr
  tt : BitVec 32
  ff : BitVec 32
  goal : BitVec 32
  err : BitVec 32
  work : BitVec 32
  val : BitVec 64
  mem : BitVec 32
  lr : Ptr
  lo : BitVec 32
  live : BitVec 32

def CK.cells (k : CK) : Array Val :=
  #[k.pool.val, .u32 k.plen, .u32 k.pcap, k.htab.val, .u32 k.hcap, .u32 k.hcnt,
    k.facts.val, .u32 k.flen, .u32 k.fcap, .u32 k.nexpr, k.stk.val, .u32 k.sp, .u32 k.scap,
    k.prem.val, k.par.val, k.proof.val, .u32 k.tt, .u32 k.ff, .u32 k.goal, .u32 k.err,
    .u32 k.work, .u64 k.val, .u32 k.mem, k.lr.val, .u32 k.lo, .u32 k.live]

/-- The struct in block `sb` has field values `k`. -/
def HasCK (m : Mem) (sb : Nat) (k : CK) : Prop :=
  m.block? sb = some ⟨.struct "ck", k.cells⟩

/-- Block `b` is a live `u32` array with these cells. -/
def HasArr (m : Mem) (b : Nat) (cells : Array Val) : Prop :=
  m.block? b = some ⟨.u32, cells⟩

section
variable {P : Prog} {m : Mem} {sb : Nat} {k : CK}

theorem ck_slot (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) (f : String) :
    m.fieldSlot P sb f =
      match fieldIn ckS.fields f with
      | some (i, t) => some (⟨.struct "ck", k.cells⟩, i, t)
      | none => none := by
  unfold Mem.fieldSlot
  rw [h]
  simp only [hs, StructDef.field?]
  cases fieldIn ckS.fields f with
  | none => rfl
  | some it => rfl

end


/-! ## Field lookups (generated: one lemma per field) -/

theorem fi_pool : fieldIn ckS.fields "pool" = some (0, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_plen : fieldIn ckS.fields "plen" = some (1, .u32) := by simp [ckS, fieldIn]
theorem fi_pcap : fieldIn ckS.fields "pcap" = some (2, .u32) := by simp [ckS, fieldIn]
theorem fi_htab : fieldIn ckS.fields "htab" = some (3, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_hcap : fieldIn ckS.fields "hcap" = some (4, .u32) := by simp [ckS, fieldIn]
theorem fi_hcnt : fieldIn ckS.fields "hcnt" = some (5, .u32) := by simp [ckS, fieldIn]
theorem fi_facts : fieldIn ckS.fields "facts" = some (6, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_flen : fieldIn ckS.fields "flen" = some (7, .u32) := by simp [ckS, fieldIn]
theorem fi_fcap : fieldIn ckS.fields "fcap" = some (8, .u32) := by simp [ckS, fieldIn]
theorem fi_nexpr : fieldIn ckS.fields "nexpr" = some (9, .u32) := by simp [ckS, fieldIn]
theorem fi_stk : fieldIn ckS.fields "stk" = some (10, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_sp : fieldIn ckS.fields "sp" = some (11, .u32) := by simp [ckS, fieldIn]
theorem fi_scap : fieldIn ckS.fields "scap" = some (12, .u32) := by simp [ckS, fieldIn]
theorem fi_prem : fieldIn ckS.fields "prem" = some (13, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_par : fieldIn ckS.fields "par" = some (14, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_proof : fieldIn ckS.fields "proof" = some (15, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_tt : fieldIn ckS.fields "tt" = some (16, .u32) := by simp [ckS, fieldIn]
theorem fi_ff : fieldIn ckS.fields "ff" = some (17, .u32) := by simp [ckS, fieldIn]
theorem fi_goal : fieldIn ckS.fields "goal" = some (18, .u32) := by simp [ckS, fieldIn]
theorem fi_err : fieldIn ckS.fields "err" = some (19, .u32) := by simp [ckS, fieldIn]
theorem fi_work : fieldIn ckS.fields "work" = some (20, .u32) := by simp [ckS, fieldIn]
theorem fi_val : fieldIn ckS.fields "val" = some (21, .u64) := by simp [ckS, fieldIn]
theorem fi_mem : fieldIn ckS.fields "mem" = some (22, .u32) := by simp [ckS, fieldIn]
theorem fi_lr : fieldIn ckS.fields "lr" = some (23, .ptr .u32) := by simp [ckS, fieldIn]
theorem fi_lo : fieldIn ckS.fields "lo" = some (24, .u32) := by simp [ckS, fieldIn]
theorem fi_live : fieldIn ckS.fields "live" = some (25, .u32) := by simp [ckS, fieldIn]

section
variable {P : Prog} {m : Mem} {sb : Nat} {k : CK}

theorem Ptr.val_ne_undef (p : Ptr) : p.val ≠ .undef := by
  cases p with
  | none => simp [Ptr.val]
  | some bo => simp [Ptr.val]

theorem HasCK.load (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) {f : String} {i : Nat}
    {t : Ty} {v : Val} (hf : fieldIn ckS.fields f = some (i, t)) (hc : k.cells[i]? = some v)
    (hv : v ≠ .undef) : m.loadField P sb f = some v :=
  Mem.loadField_eq (by rw [ck_slot hs h, hf]) hc hv

theorem HasCK.ld_pool (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "pool" = some (k.pool.val) :=
  h.load hs fi_pool (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_plen (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "plen" = some (.u32 k.plen) :=
  h.load hs fi_plen (by simp [CK.cells]) (by simp)
theorem HasCK.ld_pcap (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "pcap" = some (.u32 k.pcap) :=
  h.load hs fi_pcap (by simp [CK.cells]) (by simp)
theorem HasCK.ld_htab (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "htab" = some (k.htab.val) :=
  h.load hs fi_htab (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_hcap (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "hcap" = some (.u32 k.hcap) :=
  h.load hs fi_hcap (by simp [CK.cells]) (by simp)
theorem HasCK.ld_hcnt (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "hcnt" = some (.u32 k.hcnt) :=
  h.load hs fi_hcnt (by simp [CK.cells]) (by simp)
theorem HasCK.ld_facts (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "facts" = some (k.facts.val) :=
  h.load hs fi_facts (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_flen (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "flen" = some (.u32 k.flen) :=
  h.load hs fi_flen (by simp [CK.cells]) (by simp)
theorem HasCK.ld_fcap (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "fcap" = some (.u32 k.fcap) :=
  h.load hs fi_fcap (by simp [CK.cells]) (by simp)
theorem HasCK.ld_nexpr (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "nexpr" = some (.u32 k.nexpr) :=
  h.load hs fi_nexpr (by simp [CK.cells]) (by simp)
theorem HasCK.ld_stk (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "stk" = some (k.stk.val) :=
  h.load hs fi_stk (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_sp (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "sp" = some (.u32 k.sp) :=
  h.load hs fi_sp (by simp [CK.cells]) (by simp)
theorem HasCK.ld_scap (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "scap" = some (.u32 k.scap) :=
  h.load hs fi_scap (by simp [CK.cells]) (by simp)
theorem HasCK.ld_prem (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "prem" = some (k.prem.val) :=
  h.load hs fi_prem (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_par (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "par" = some (k.par.val) :=
  h.load hs fi_par (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_proof (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "proof" = some (k.proof.val) :=
  h.load hs fi_proof (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_tt (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "tt" = some (.u32 k.tt) :=
  h.load hs fi_tt (by simp [CK.cells]) (by simp)
theorem HasCK.ld_ff (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "ff" = some (.u32 k.ff) :=
  h.load hs fi_ff (by simp [CK.cells]) (by simp)
theorem HasCK.ld_goal (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "goal" = some (.u32 k.goal) :=
  h.load hs fi_goal (by simp [CK.cells]) (by simp)
theorem HasCK.ld_err (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "err" = some (.u32 k.err) :=
  h.load hs fi_err (by simp [CK.cells]) (by simp)
theorem HasCK.ld_work (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "work" = some (.u32 k.work) :=
  h.load hs fi_work (by simp [CK.cells]) (by simp)
theorem HasCK.ld_val (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "val" = some (.u64 k.val) :=
  h.load hs fi_val (by simp [CK.cells]) (by simp)
theorem HasCK.ld_mem (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "mem" = some (.u32 k.mem) :=
  h.load hs fi_mem (by simp [CK.cells]) (by simp)
theorem HasCK.ld_lr (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "lr" = some (k.lr.val) :=
  h.load hs fi_lr (by simp [CK.cells]) (Ptr.val_ne_undef _)
theorem HasCK.ld_lo (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "lo" = some (.u32 k.lo) :=
  h.load hs fi_lo (by simp [CK.cells]) (by simp)
theorem HasCK.ld_live (hs : P.findStruct "ck" = some ckS) (h : HasCK m sb k) :
    m.loadField P sb "live" = some (.u32 k.live) :=
  h.load hs fi_live (by simp [CK.cells]) (by simp)

end

/-! ## Scalar field updates -/

/-- Set the `u32` field named `f`; also gives the field's index. -/
def CK.setU32 (k : CK) (f : String) (x : BitVec 32) : Option (Nat × CK) :=
  if f = "plen" then some (1, { k with plen := x }) else
  if f = "pcap" then some (2, { k with pcap := x }) else
  if f = "hcap" then some (4, { k with hcap := x }) else
  if f = "hcnt" then some (5, { k with hcnt := x }) else
  if f = "flen" then some (7, { k with flen := x }) else
  if f = "fcap" then some (8, { k with fcap := x }) else
  if f = "nexpr" then some (9, { k with nexpr := x }) else
  if f = "sp" then some (11, { k with sp := x }) else
  if f = "scap" then some (12, { k with scap := x }) else
  if f = "tt" then some (16, { k with tt := x }) else
  if f = "ff" then some (17, { k with ff := x }) else
  if f = "goal" then some (18, { k with goal := x }) else
  if f = "err" then some (19, { k with err := x }) else
  if f = "work" then some (20, { k with work := x }) else
  if f = "mem" then some (22, { k with mem := x }) else
  if f = "lo" then some (24, { k with lo := x }) else
  if f = "live" then some (25, { k with live := x }) else
  none

def CK.ptr4 (k : CK) : List Ptr := [k.pool, k.htab, k.facts, k.stk, k.prem, k.par, k.proof, k.lr]

theorem CK.setU32_ok {k k' : CK} {f : String} {x : BitVec 32} {i : Nat}
    (h : k.setU32 f x = some (i, k')) :
    fieldIn ckS.fields f = some (i, .u32) ∧ k'.cells = k.cells.setIfInBounds i (.u32 x) ∧
    k'.ptr4 = k.ptr4 ∧ i < 26 := by
  unfold CK.setU32 at h
  by_cases h1 : f = "plen"
  · subst h1; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_plen, by simp [CK.cells], rfl, by omega⟩
  simp only [h1, ↓reduceIte] at h
  by_cases h2 : f = "pcap"
  · subst h2; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_pcap, by simp [CK.cells], rfl, by omega⟩
  simp only [h2, ↓reduceIte] at h
  by_cases h4 : f = "hcap"
  · subst h4; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_hcap, by simp [CK.cells], rfl, by omega⟩
  simp only [h4, ↓reduceIte] at h
  by_cases h5 : f = "hcnt"
  · subst h5; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_hcnt, by simp [CK.cells], rfl, by omega⟩
  simp only [h5, ↓reduceIte] at h
  by_cases h7 : f = "flen"
  · subst h7; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_flen, by simp [CK.cells], rfl, by omega⟩
  simp only [h7, ↓reduceIte] at h
  by_cases h8 : f = "fcap"
  · subst h8; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_fcap, by simp [CK.cells], rfl, by omega⟩
  simp only [h8, ↓reduceIte] at h
  by_cases h9 : f = "nexpr"
  · subst h9; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_nexpr, by simp [CK.cells], rfl, by omega⟩
  simp only [h9, ↓reduceIte] at h
  by_cases h11 : f = "sp"
  · subst h11; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_sp, by simp [CK.cells], rfl, by omega⟩
  simp only [h11, ↓reduceIte] at h
  by_cases h12 : f = "scap"
  · subst h12; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_scap, by simp [CK.cells], rfl, by omega⟩
  simp only [h12, ↓reduceIte] at h
  by_cases h16 : f = "tt"
  · subst h16; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_tt, by simp [CK.cells], rfl, by omega⟩
  simp only [h16, ↓reduceIte] at h
  by_cases h17 : f = "ff"
  · subst h17; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_ff, by simp [CK.cells], rfl, by omega⟩
  simp only [h17, ↓reduceIte] at h
  by_cases h18 : f = "goal"
  · subst h18; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_goal, by simp [CK.cells], rfl, by omega⟩
  simp only [h18, ↓reduceIte] at h
  by_cases h19 : f = "err"
  · subst h19; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_err, by simp [CK.cells], rfl, by omega⟩
  simp only [h19, ↓reduceIte] at h
  by_cases h20 : f = "work"
  · subst h20; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_work, by simp [CK.cells], rfl, by omega⟩
  simp only [h20, ↓reduceIte] at h
  by_cases h22 : f = "mem"
  · subst h22; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_mem, by simp [CK.cells], rfl, by omega⟩
  simp only [h22, ↓reduceIte] at h
  by_cases h24 : f = "lo"
  · subst h24; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_lo, by simp [CK.cells], rfl, by omega⟩
  simp only [h24, ↓reduceIte] at h
  by_cases h25 : f = "live"
  · subst h25; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fi_live, by simp [CK.cells], rfl, by omega⟩
  simp only [h25, ↓reduceIte] at h
  cases h

/-! ## The whole checker memory -/

/-- The arrays the checker allocates. -/
inductive Arr where
  | pool | htab | facts | stk | prem | lr
  deriving DecidableEq, Repr

/-- The checker's memory as plain data: the struct's fields and the contents
of each array (meaningful only while the corresponding pointer is not `NULL`). -/
structure CMem where
  k : CK
  pool : Array Val
  htab : Array Val
  facts : Array Val
  stk : Array Val
  prem : Array Val
  proof : Array Val
  lr : Array Val

def CK.ptr (k : CK) : Arr → Ptr
  | .pool => k.pool
  | .htab => k.htab
  | .facts => k.facts
  | .stk => k.stk
  | .prem => k.prem
  | .lr => k.lr

def CMem.arr (c : CMem) : Arr → Array Val
  | .pool => c.pool
  | .htab => c.htab
  | .facts => c.facts
  | .stk => c.stk
  | .prem => c.prem
  | .lr => c.lr

def CMem.setArr (c : CMem) : Arr → Array Val → CMem
  | .pool, x => { c with pool := x }
  | .htab, x => { c with htab := x }
  | .facts, x => { c with facts := x }
  | .stk, x => { c with stk := x }
  | .prem, x => { c with prem := x }
  | .lr, x => { c with lr := x }

/-- What the checker found when it was entered: the memory at that moment,
and the block holding its copy of the proof. -/
structure World where
  base : Mem
  pb : Nat
  /-- Blocks allocated by the running function itself and held in local variables
  (only `ck_compact`'s forwarding table): not part of the checker state. -/
  aux : Nat → Option Block

/-- Memory `m` holds checker state `c` with its struct in block `sb`.  Besides
the contents, this pins down ownership exactly: every block that existed at
entry is untouched (except the proof block, which the checker may write), and
the only blocks created since are the struct and the arrays it points to. -/
structure Holds (W : World) (m : Mem) (sb : Nat) (c : CMem) : Prop where
  ck : HasCK m sb c.k
  sbNew : W.base.blocks.size ≤ sb
  pbOld : W.pb < W.base.blocks.size
  proof : HasArr m W.pb c.proof
  proofPtr : c.k.proof = none ∨ c.k.proof = some (W.pb, 0)
  parPtr : c.k.par = none ∨ ∃ o, c.k.par = some (W.pb, o)
  arr : ∀ a b o, c.k.ptr a = some (b, o) →
    o = 0 ∧ b ≠ sb ∧ W.base.blocks.size ≤ b ∧ HasArr m b (c.arr a)
  sep : ∀ a a' b b' o o', a ≠ a' → c.k.ptr a = some (b, o) → c.k.ptr a' = some (b', o') → b ≠ b'
  out : ∀ b, b < W.base.blocks.size → b ≠ W.pb → m.block? b = W.base.block? b
  exact : ∀ b, W.base.blocks.size ≤ b → b ≠ sb → (∀ a o, c.k.ptr a ≠ some (b, o)) →
    m.block? b = W.aux b
  auxNew : ∀ b, W.aux b ≠ none → W.base.blocks.size ≤ b ∧ b ≠ sb ∧ ∀ a o, c.k.ptr a ≠ some (b, o)

/-- Naming the current state together with a fact about it. -/
theorem Holds.named {W : World} {m : Mem} {sb : Nat} {c : CMem} (h : Holds W m sb c)
    {P : CMem → Prop} (hp : P c) : ∃ c', Holds W m sb c' ∧ P c' := ⟨c, h, hp⟩

/-- Reading a cell: uninitialised cells cannot be read. -/
def rd (cells : Array Val) (i : Nat) : Option Val :=
  match cells[i]? with
  | some .undef => none
  | some v => some v
  | none => none

theorem rd_u32 {cells : Array Val} {i : Nat} {w : BitVec 32} (h : cells[i]? = some (.u32 w)) :
    rd cells i = some (.u32 w) := by
  simp [rd, h]

theorem HasArr.loadArr {m : Mem} {b : Nat} {cells : Array Val} (h : HasArr m b cells) (i : Nat) :
    m.loadArr b i = rd cells i := by
  unfold Mem.loadArr rd
  rw [h]
  simp only [Ty.isStruct]
  cases hc : cells[i]? with
  | none => simp
  | some v => cases v <;> simp

section
variable {P : Prog} {W : World} {m : Mem} {sb : Nat} {c : CMem}

theorem Holds.pb_ne_sb (h : Holds W m sb c) : W.pb ≠ sb := by
  have := h.sbNew; have := h.pbOld; omega

theorem Holds.loadArr (h : Holds W m sb c) {a : Arr} {b o : Nat} (hp : c.k.ptr a = some (b, o))
    (i : Nat) : m.loadArr b i = rd (c.arr a) i :=
  (h.arr a b o hp).2.2.2.loadArr i

theorem Holds.loadProof (h : Holds W m sb c) (i : Nat) : m.loadArr W.pb i = rd c.proof i :=
  h.proof.loadArr i

/-- Changing the struct's fields without touching any pointer keeps the rest. -/
theorem Holds.setCK (h : Holds W m sb c) {k' : CK} {i : Nat} {v : Val}
    (hc : k'.cells = c.k.cells.setIfInBounds i v) (hp : k'.ptr4 = c.k.ptr4) :
    Holds W (m.setCell sb i v) sb { c with k := k' } := by
  have hb := fun b' => Mem.block?_setCell (i := i) (v := v) b' h.ck
  simp only [CK.ptr4, List.cons.injEq, and_true] at hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
  have hptr : ∀ a, k'.ptr a = c.k.ptr a := by
    intro a; cases a <;> simp [CK.ptr, *]
  refine ⟨?_, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (m.setCell sb i v).block? sb = _
    rw [hb]; simp [hc]
  · show (m.setCell sb i v).block? W.pb = _
    rw [hb]; simp [h.pb_ne_sb]; exact h.proof
  · show k'.proof = none ∨ _
    rw [h7]; exact h.proofPtr
  · show k'.par = none ∨ _
    rw [h6]; exact h.parPtr
  · intro a b o hpa
    rw [hptr] at hpa
    obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a b o hpa
    refine ⟨ho, hbs, hbb, ?_⟩
    show (m.setCell sb i v).block? b = _
    rw [hb]; simp [hbs]
    cases a <;> exact harr
  · intro a a' b b' o o' hne hpa hpa'
    rw [hptr] at hpa hpa'
    exact h.sep a a' b b' o o' hne hpa hpa'
  · intro b hlt hne
    rw [hb]
    have : b ≠ sb := by have := h.sbNew; omega
    simp [this]; exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]; simp [hne]
    exact h.exact b hge hne (fun a o => by rw [← hptr]; exact hno a o)
  · intro b hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b hb'
    exact ⟨h1, h2, fun a o => by rw [hptr]; exact h3 a o⟩

theorem Holds.setU32 (hs : P.findStruct "ck" = some ckS) (h : Holds W m sb c) {f : String}
    {x : BitVec 32} {i : Nat} {k' : CK} (hk : c.k.setU32 f x = some (i, k')) :
    m.storeField P sb f (.u32 x) = some (m.setCell sb i (.u32 x)) ∧
    Holds W (m.setCell sb i (.u32 x)) sb { c with k := k' } := by
  obtain ⟨hf, hc, hp, hi⟩ := CK.setU32_ok hk
  refine ⟨?_, h.setCK hc hp⟩
  have hlt : i < c.k.cells.size := by simpa [CK.cells] using hi
  exact Mem.storeField_eq (by rw [ck_slot hs h.ck, hf]) (by simp) hlt

/-- Writing a cell of an owned array. -/
theorem Holds.storeArr (h : Holds W m sb c) {a : Arr} {b o : Nat} (hp : c.k.ptr a = some (b, o))
    {i : Nat} (hi : i < (c.arr a).size) (x : BitVec 32) :
    m.storeArr b i (.u32 x) = some (m.setCell b i (.u32 x)) ∧
    Holds W (m.setCell b i (.u32 x)) sb (c.setArr a ((c.arr a).setIfInBounds i (.u32 x))) := by
  obtain ⟨_, hbs, hbb, harr⟩ := h.arr a b o hp
  have hb := fun b' => Mem.block?_setCell (i := i) (v := .u32 x) b' harr
  have hptr : ∀ a', (c.setArr a ((c.arr a).setIfInBounds i (.u32 x))).k.ptr a' = c.k.ptr a' := by
    intro a'; cases a <;> rfl
  have hpbne : W.pb ≠ b := by have := h.pbOld; omega
  refine ⟨Mem.storeArr_eq harr rfl (by simp) hi, ?_, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (m.setCell b i (.u32 x)).block? sb = _
    rw [hb]; simp [Ne.symm hbs]
    cases a <;> exact h.ck
  · show (m.setCell b i (.u32 x)).block? W.pb = _
    rw [hb]; simp [hpbne]
    cases a <;> exact h.proof
  · cases a <;> exact h.proofPtr
  · cases a <;> exact h.parPtr
  · intro a' b' o' hpa
    rw [hptr] at hpa
    obtain ⟨ho, hbs', hbb', harr'⟩ := h.arr a' b' o' hpa
    refine ⟨ho, hbs', hbb', ?_⟩
    show (m.setCell b i (.u32 x)).block? b' = _
    rw [hb]
    by_cases haa : a' = a
    · subst haa
      have : b' = b := by rw [hp] at hpa; cases hpa; rfl
      subst this
      cases a' <;> simp [CMem.setArr, CMem.arr]
    · have : b' ≠ b := h.sep a' a b' b o' o haa hpa hp
      simp [this]
      cases a <;> cases a' <;> first | exact absurd rfl haa | exact harr'
  · intro a1 a2 b1 b2 o1 o2 hne h1 h2
    rw [hptr] at h1 h2
    exact h.sep a1 a2 b1 b2 o1 o2 hne h1 h2
  · intro b' hlt hne
    rw [hb]
    have : b' ≠ b := by omega
    simp [this]; exact h.out b' hlt hne
  · intro b' hge hne hno
    rw [hb]
    have : b' ≠ b := fun e => hno a o (by rw [hptr, e]; exact hp)
    simp [this]
    exact h.exact b' hge hne (fun a' o' => by rw [← hptr]; exact hno a' o')
  · intro b' hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b' hb'
    exact ⟨h1, h2, fun a' o' => by rw [hptr]; exact h3 a' o'⟩

/-- Writing a cell of the proof block. -/
theorem Holds.storeProof (h : Holds W m sb c) {i : Nat} (hi : i < c.proof.size) (x : BitVec 32) :
    m.storeArr W.pb i (.u32 x) = some (m.setCell W.pb i (.u32 x)) ∧
    Holds W (m.setCell W.pb i (.u32 x)) sb { c with proof := c.proof.setIfInBounds i (.u32 x) } := by
  have hb := fun b' => Mem.block?_setCell (i := i) (v := .u32 x) b' h.proof
  refine ⟨Mem.storeArr_eq h.proof rfl (by simp) hi, ?_, h.sbNew, h.pbOld, ?_, h.proofPtr, h.parPtr,
    ?_, h.sep, ?_, ?_, h.auxNew⟩
  · show (m.setCell W.pb i (.u32 x)).block? sb = _
    rw [hb]; simp [Ne.symm h.pb_ne_sb]; exact h.ck
  · show (m.setCell W.pb i (.u32 x)).block? W.pb = _
    rw [hb]; simp
  · intro a b o hpa
    obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a b o hpa
    refine ⟨ho, hbs, hbb, ?_⟩
    show (m.setCell W.pb i (.u32 x)).block? b = _
    rw [hb]
    have : b ≠ W.pb := by have := h.pbOld; omega
    simp [this]; exact harr
  · intro b hlt hne
    rw [hb]; simp [hne]; exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]
    have : b ≠ W.pb := by have := h.pbOld; omega
    simp [this]; exact h.exact b hge hne hno

end

/-! ## The state with only `work`, `err` and `val` changed -/

/-- `c` with the fields `work`, `err`, `val` replaced. -/
def CMem.wev (c : CMem) (wk er : BitVec 32) (vl : BitVec 64) : CMem :=
  { c with k := { c.k with work := wk, err := er, val := vl } }

section wev
variable (c : CMem) (wk er : BitVec 32) (vl : BitVec 64)

@[simp] theorem wev_pool : (c.wev wk er vl).pool = c.pool := rfl
@[simp] theorem wev_htab : (c.wev wk er vl).htab = c.htab := rfl
@[simp] theorem wev_facts : (c.wev wk er vl).facts = c.facts := rfl
@[simp] theorem wev_stk : (c.wev wk er vl).stk = c.stk := rfl
@[simp] theorem wev_prem : (c.wev wk er vl).prem = c.prem := rfl
@[simp] theorem wev_proof : (c.wev wk er vl).proof = c.proof := rfl
@[simp] theorem wev_lr : (c.wev wk er vl).lr = c.lr := rfl
@[simp] theorem wev_k_lr : (c.wev wk er vl).k.lr = c.k.lr := rfl
@[simp] theorem wev_k_lo : (c.wev wk er vl).k.lo = c.k.lo := rfl
@[simp] theorem wev_k_live : (c.wev wk er vl).k.live = c.k.live := rfl
@[simp] theorem wev_k_pool : (c.wev wk er vl).k.pool = c.k.pool := rfl
@[simp] theorem wev_k_plen : (c.wev wk er vl).k.plen = c.k.plen := rfl
@[simp] theorem wev_k_pcap : (c.wev wk er vl).k.pcap = c.k.pcap := rfl
@[simp] theorem wev_k_htab : (c.wev wk er vl).k.htab = c.k.htab := rfl
@[simp] theorem wev_k_hcap : (c.wev wk er vl).k.hcap = c.k.hcap := rfl
@[simp] theorem wev_k_hcnt : (c.wev wk er vl).k.hcnt = c.k.hcnt := rfl
@[simp] theorem wev_k_facts : (c.wev wk er vl).k.facts = c.k.facts := rfl
@[simp] theorem wev_k_flen : (c.wev wk er vl).k.flen = c.k.flen := rfl
@[simp] theorem wev_k_fcap : (c.wev wk er vl).k.fcap = c.k.fcap := rfl
@[simp] theorem wev_k_nexpr : (c.wev wk er vl).k.nexpr = c.k.nexpr := rfl
@[simp] theorem wev_k_stk : (c.wev wk er vl).k.stk = c.k.stk := rfl
@[simp] theorem wev_k_sp : (c.wev wk er vl).k.sp = c.k.sp := rfl
@[simp] theorem wev_k_scap : (c.wev wk er vl).k.scap = c.k.scap := rfl
@[simp] theorem wev_k_prem : (c.wev wk er vl).k.prem = c.k.prem := rfl
@[simp] theorem wev_k_par : (c.wev wk er vl).k.par = c.k.par := rfl
@[simp] theorem wev_k_proof : (c.wev wk er vl).k.proof = c.k.proof := rfl
@[simp] theorem wev_k_tt : (c.wev wk er vl).k.tt = c.k.tt := rfl
@[simp] theorem wev_k_ff : (c.wev wk er vl).k.ff = c.k.ff := rfl
@[simp] theorem wev_k_goal : (c.wev wk er vl).k.goal = c.k.goal := rfl
@[simp] theorem wev_k_err : (c.wev wk er vl).k.err = er := rfl
@[simp] theorem wev_k_work : (c.wev wk er vl).k.work = wk := rfl
@[simp] theorem wev_k_val : (c.wev wk er vl).k.val = vl := rfl
@[simp] theorem wev_k_mem : (c.wev wk er vl).k.mem = c.k.mem := rfl

@[simp] theorem wev_wev (wk' er' : BitVec 32) (vl' : BitVec 64) :
    (c.wev wk er vl).wev wk' er' vl' = c.wev wk' er' vl' := rfl

theorem wev_self : c.wev c.k.work c.k.err c.k.val = c := by
  obtain ⟨k, _, _, _, _, _, _, _⟩ := c
  rfl

end wev

/-! ## The state with only `mem` changed -/

/-- `c` with the memory budget `mem` replaced. -/
def CMem.setMem (c : CMem) (mm : BitVec 32) : CMem := { c with k := { c.k with mem := mm } }

section setMem
variable (c : CMem) (mm : BitVec 32)

@[simp] theorem setMem_pool : (c.setMem mm).pool = c.pool := rfl
@[simp] theorem setMem_htab : (c.setMem mm).htab = c.htab := rfl
@[simp] theorem setMem_facts : (c.setMem mm).facts = c.facts := rfl
@[simp] theorem setMem_stk : (c.setMem mm).stk = c.stk := rfl
@[simp] theorem setMem_prem : (c.setMem mm).prem = c.prem := rfl
@[simp] theorem setMem_proof : (c.setMem mm).proof = c.proof := rfl
@[simp] theorem setMem_lr : (c.setMem mm).lr = c.lr := rfl
@[simp] theorem setMem_k_lr : (c.setMem mm).k.lr = c.k.lr := rfl
@[simp] theorem setMem_k_lo : (c.setMem mm).k.lo = c.k.lo := rfl
@[simp] theorem setMem_k_live : (c.setMem mm).k.live = c.k.live := rfl
@[simp] theorem setMem_k_pool : (c.setMem mm).k.pool = c.k.pool := rfl
@[simp] theorem setMem_k_plen : (c.setMem mm).k.plen = c.k.plen := rfl
@[simp] theorem setMem_k_pcap : (c.setMem mm).k.pcap = c.k.pcap := rfl
@[simp] theorem setMem_k_htab : (c.setMem mm).k.htab = c.k.htab := rfl
@[simp] theorem setMem_k_hcap : (c.setMem mm).k.hcap = c.k.hcap := rfl
@[simp] theorem setMem_k_hcnt : (c.setMem mm).k.hcnt = c.k.hcnt := rfl
@[simp] theorem setMem_k_facts : (c.setMem mm).k.facts = c.k.facts := rfl
@[simp] theorem setMem_k_flen : (c.setMem mm).k.flen = c.k.flen := rfl
@[simp] theorem setMem_k_fcap : (c.setMem mm).k.fcap = c.k.fcap := rfl
@[simp] theorem setMem_k_nexpr : (c.setMem mm).k.nexpr = c.k.nexpr := rfl
@[simp] theorem setMem_k_stk : (c.setMem mm).k.stk = c.k.stk := rfl
@[simp] theorem setMem_k_sp : (c.setMem mm).k.sp = c.k.sp := rfl
@[simp] theorem setMem_k_scap : (c.setMem mm).k.scap = c.k.scap := rfl
@[simp] theorem setMem_k_prem : (c.setMem mm).k.prem = c.k.prem := rfl
@[simp] theorem setMem_k_par : (c.setMem mm).k.par = c.k.par := rfl
@[simp] theorem setMem_k_proof : (c.setMem mm).k.proof = c.k.proof := rfl
@[simp] theorem setMem_k_tt : (c.setMem mm).k.tt = c.k.tt := rfl
@[simp] theorem setMem_k_ff : (c.setMem mm).k.ff = c.k.ff := rfl
@[simp] theorem setMem_k_goal : (c.setMem mm).k.goal = c.k.goal := rfl
@[simp] theorem setMem_k_err : (c.setMem mm).k.err = c.k.err := rfl
@[simp] theorem setMem_k_work : (c.setMem mm).k.work = c.k.work := rfl
@[simp] theorem setMem_k_val : (c.setMem mm).k.val = c.k.val := rfl
@[simp] theorem setMem_k_mem : (c.setMem mm).k.mem = mm := rfl
@[simp] theorem setMem_k_ptr (a : Arr) : (c.setMem mm).k.ptr a = c.k.ptr a := by cases a <;> rfl
@[simp] theorem setMem_arr (a : Arr) : (c.setMem mm).arr a = c.arr a := by cases a <;> rfl

@[simp] theorem setMem_setMem (mm' : BitVec 32) : (c.setMem mm).setMem mm' = c.setMem mm' := rfl

@[simp] theorem wev_setMem (wk er : BitVec 32) (vl : BitVec 64) :
    (c.setMem mm).wev wk er vl = (c.wev wk er vl).setMem mm := rfl

theorem setMem_self : c.setMem c.k.mem = c := by
  obtain ⟨k, _, _, _, _, _, _, _⟩ := c
  rfl

end setMem

end Vbcf.Proof
