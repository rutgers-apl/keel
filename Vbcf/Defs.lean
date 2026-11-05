import EmbC.DSL

/-!
# Vbcf: the BCF checker written in EmbC — shared definitions

`Vbcf` is the C checker, written as an EmbC program that mirrors the
verified Lean checker `Bcf.checkBcf` step for step.  The intended theorem
(stage 3) is that whenever `vbcf_check` accepts, `checkBcf` accepts.

## Data layout

* **Pool.**  One flat `u32` array.  A node is a header word followed by its
  argument words, in the BCF wire format: `code | vlen << 8 | params << 16`.
  A node's *id* is the offset of its header.  Every node in the pool has been
  type-checked and interned, so two nodes are structurally equal exactly when
  their ids are equal.
* **Leaves.**  The words after the header are child ids, except for
  - `BV_VAL`: one or two value words (low word first);
  - `BV_VAR` / `BOOL_VAR`: one word, the position of the variable in the
    input, which is its identity (the wire format has no such word; it is
    added when the input is loaded);
  - `BOOL_VAL`: no words; the value is bit 0 of `params`.
* **Types** are computed from the header alone (`ty_of`): a bit-vector type
  is its width (1..256), `TY_BOOL` is boolean, `TY_LIST | e << 8 | n` is a list.
* **Input.**  `proof` is the checker's own copy of the proof.  While the
  expression section is loaded, each expression's header word is overwritten
  with one more than the id of its canonical node, and its other words with 0,
  so afterwards `proof[3 + p]` maps input position `p` to a node (`expr_at`).
* **Facts.**  `facts[k]` is the id of the formula concluded by step `k`.
* **Scratch stack.**  `stk[0..sp)` holds temporary lists of ids.
* **Work budget.**  `work` is set once, in `ck_init`, to `WORK_PER_WORD`
  units per word of input (the proof's words plus the goal's position in the
  verifier's arena) plus `WORK_BASE`, which is what a single step was allowed
  before the budget became global.  It is spent (`spend`, `tick`) wherever the
  checker does work proportional to data: every scratch-stack push, every
  recursive visit of a term, the size of every node interned and of every node
  compared in a hash probe, the copies and the rehash when the pool, the
  scratch stack or the hash table grows, the operands of a step as it is read,
  and the scans in resolution, factoring, ACI sorting and polynomial
  normalisation.  A proof that runs out is rejected, so the checker's time is
  linear in its input whatever the proof contains.
* **Memory budget.**  `mem` is set in `ck_init` to `MEM_PER_WORD` words per
  input word plus `MEM_BASE`, and every allocation after that pays its size
  from it, so the words the checker ever allocates are linear in its input.
* **Reclamation.**  `lr[k]` is the index of the last step that cites fact
  `k` (0 if none); `ck_scan` computes it from the step section before any
  step runs.  Nodes loaded from the input occupy `pool[0..lo)` and never
  move.  Between steps, once the pool has grown past twice its live size
  plus `COMPACT_GAP` words, `ck_compact` keeps only the nodes reachable from
  the facts a later step still cites, slides them down in place (ids are
  renumbered, order preserved), remaps `facts[]` (a dead fact becomes
  `NOID`) and rebuilds the hash table.  `live` is the number of words kept
  by the last compaction.

`NOID` is returned wherever an id is expected and none can be produced; the
proof is then rejected.
-/

namespace Vbcf
open EmbC

c_const% NOID := 0xffffffff

/-! Types -/
c_const% TY_BOOL := 0x1000
c_const% TY_LIST := 0x2000

/-! Node codes: `type | op` as in `uapi/linux/bcf.h`. -/
c_const% BV_ADD := 0x00
c_const% BV_VAL := 0x08
c_const% BV_SUB := 0x10
c_const% BV_VAR := 0x18
c_const% BV_MUL := 0x20
c_const% BV_ITE := 0x28
c_const% BV_UDIV := 0x30
c_const% BV_EXTRACT := 0x38
c_const% BV_OR := 0x40
c_const% BV_SEXT := 0x48
c_const% BV_AND := 0x50
c_const% BV_ZEXT := 0x58
c_const% BV_SHL := 0x60
c_const% BV_SIZE := 0x68
c_const% BV_LSHR := 0x70
c_const% BV_NOT := 0x78
c_const% BV_NEG := 0x80
c_const% BV_FROM_BOOL := 0x88
c_const% BV_UREM := 0x90
c_const% BV_CONCAT := 0x98
c_const% BV_XOR := 0xa0
c_const% BV_REPEAT := 0xa8
c_const% BV_SDIV := 0xb0
c_const% BV_ASHR := 0xc0
c_const% BV_SMOD := 0xd0

c_const% BOOL_CONJ := 0x01
c_const% BOOL_VAL := 0x09
c_const% BOOL_EQ := 0x11
c_const% BOOL_VAR := 0x19
c_const% BOOL_UGT := 0x21
c_const% BOOL_ITE := 0x29
c_const% BOOL_UGE := 0x31
c_const% BOOL_XOR := 0x39
c_const% BOOL_DISJ := 0x41
c_const% BOOL_BITOF := 0x49
c_const% BOOL_DISTINCT := 0x51
c_const% BOOL_SGT := 0x61
c_const% BOOL_SGE := 0x71
c_const% BOOL_NOT := 0x81
c_const% BOOL_IMPLIES := 0x91
c_const% BOOL_ULT := 0xa1
c_const% BOOL_ULE := 0xb1
c_const% BOOL_SLT := 0xc1
c_const% BOOL_SLE := 0xd1

c_const% LIST_VAL := 0x0a

/-! `BOOL_VAL` headers of the two truth values. -/
c_const% HDR_TRUE := 0x10009
c_const% HDR_FALSE := 0x00009

/-! Limits.  Exceeding one rejects the proof. -/
c_const% MAX_POOL := 0x40000000
c_const% MAX_DEPTH := 32
c_const% WORK_PER_WORD := 128
c_const% WORK_BASE := 0x100000
c_const% MEM_PER_WORD := 32
c_const% MEM_BASE := 0x40000
c_const% MAX_SORT := 1024
c_const% COMPACT_GAP := 0x10000

/-! Error classes recorded in `st->err`. -/
c_const% ERR_NOMEM := 1
c_const% ERR_LIMIT := 2

def ckS : StructDef := c_struct% ck {
  u32 *pool; u32 plen; u32 pcap;
  u32 *htab; u32 hcap; u32 hcnt;
  u32 *facts; u32 flen; u32 fcap;
  u32 nexpr;
  u32 *stk; u32 sp; u32 scap;
  u32 *prem;
  u32 *par;
  u32 *proof;
  u32 tt; u32 ff; u32 goal;
  u32 err;
  u32 work;
  u64 val;
  u32 mem;
  u32 *lr; u32 lo; u32 live;
}

end Vbcf
