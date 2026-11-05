import Vbcf.Proof.Compact13

/-!
# Vbcf proofs: `ck_compact`

`ck_compact_spec : CkCompactSpec` (stated in `Replay5`): compaction between
two steps keeps `Holds`, and on success re-establishes the step invariant
`SInv` for a new view (`VSt.compact`) of the same Lean state.

* `Compact1`: the compacted pool as pure data (`cntK`, `offK`, `cpool`,
  `cst`, `cst_ok`).
* `Compact2`: the new view `VSt.compact` and `SInv.compact`.
* `Compact3`: the forwarding table as an auxiliary block of the world
  (`World.addAux`), the locals (`cpEnv`), the postcondition (`CpPost`), and
  the program text of the seven loops.
* `Compact4`–`Compact7`: marking (`MarkInv`; the roots loop `cp_roots`, the
  worklist loop `cp_mark`).
* `Compact8`–`Compact9`: the slide (`SlideCells`, `SlideFw`, `cp_slide`).
* `Compact10`: remapping the facts (`cp_remap`).
* `Compact11`: counting the nodes and sizing the table (`cp_count`, `cp_grow`).
* `Compact12`: refilling the table (`cp_refill`, `Holds.ofHView`, `Holds.dropArr`).
* `Compact13`: the function, `ck_compact_spec`.
-/
