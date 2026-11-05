# Vbcf/Proof: proving the C checker against the Lean checker

Goal: whenever the EmbC program `Vbcf.prog` accepts a proof, `Bcf.checkBcf`
accepts it; every run is memory safe; every block is freed.  Composed with
`Bcf.checkBcf_sound`, that is soundness of the printed C, relative to the
EmbC semantics, printer and kernel specifications.

## Result

`Final.lean` states the two unconditional entry theorems (`#print axioms`:
`propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `native_decide`):

* `vbcf_check_proof_sound' ga goal size`: `vbcf_check_proof(goal_exprs, goal,
  p, size)` never gets stuck, leaves every memory block as it found it, and if
  it returns 0 then the words it copied from user space decode to a proof whose
  goal holds under no assignment (`Bcf.checkBcf_sound` composed with the
  refinement), as does the verifier's goal if one is passed.
* `vbcf_check_sound' pb ws n ga goal`: the same for the in-kernel entry on a
  buffer block `pb`, which is the only block that may change (`OnlyBlockChanged`).

Trusted base: the EmbC semantics (`EmbC/Semantics.lean`), the kernel
specifications (`EmbC/Kernel.lean`: `kvcalloc`, `kzalloc`, `kvrealloc`,
`kvfree`, `copy_from_bpfptr`, `signal_pending`, `cond_resched`), the printer
(`EmbC/Print.lean`), and the Lean checker's own trusted base (with
`Bcf/Goal.lean` for the verifier's goal).  Two facts about
the rewrite table's data (`Rewrite1`: fewer than 2^16 words; variable numbers
< 256 and literals < 2^32) are checked by `decide`.

`CostFinal.lean` adds the cost theorem `vbcf_check_proof_sound_bounded`: every
run finishes, with the verdict above, within `rateA * (128 * (n + g) + 2^20) +
16003 * n + 7850 * g + stepAllow + 28960` machine transitions plus kernel-call work and
`33 * n + 32 * g + 2^18 + 1306` allocated words, for `n = proof_size / 4` proof
words and `g` goal words (`rateA = stepAllow + 40`, `stepAllow = ruleAllowC + 4000`,
`ruleAllowC = 5411000 + 500*255 + 80*255`; same axioms).  See "The cost proofs" below.

What is not proved: a bound on the C stack depth.

## Files

| File | Contents |
| --- | --- |
| `Mem.lean` | `CK` (the struct's fields), `CMem` (struct + array contents), `Holds W m sb c` (memory `m` holds checker state `c`, with exact ownership), read and write lemmas |
| `Rules.lean` | store rules over `Holds`, the `ck_simp` and `bv_norm` tactics, `FnSpec.intro'` |
| `Alloc.lean` | re-establishing `Holds` after `kvrealloc` (`Holds.grow`) |
| `PushSpec.lean` | Lean side: `pushNode`/`findNode` described without the hash index (`PoolOK`) |
| `Spec.lean` | the refinement relation: `offs`, `nodeW`, `PoolRep`, `HtabOK` (with the slot count `nz`), `StkOK`, `CoreInv`, frames, `Cand` |
| `View.lean` | `VSt`: the Lean state seen through the C-side state the pool represents (live nodes `lv`, renaming `σ`, C id `VSt.id`), `VExt`, `VSt.push` |
| `PolyRen.lean` | `lin_ren`: linear forms computed on the C-side state agree with the Lean ones |
| `EncLemmas*.lean`, `Access.lean`, `DecodeEnc.lean` | lemmas about the encoding: offsets, header fields, operator codes, typing, injectivity, `decodeNode` of a header |
| `LoadSpec*.lean` | Lean side: a one-pass loader over words, proved to imply `decode` + `canonicalize` (`load_bridge`, `check_of_load`) |
| `Specs.lean`, `Specs2.lean` | the specification (`…Spec : Prop`) of each core C function and of a rule (`RuleSpec`, `RInv`) |
| `ReplaySpecs.lean` | `RuleSpecs`, `InitSpec`/`LoadSpec`/`ScanSpec` with `InitDone`/`LoadDone`/`LoadDone'`/`ScanDone`, `VbcfCheckSpec`, `BcfCheckUserSpec` |
| `Core1.lean`, `Push.lean` | `tick`, `push` |
| `Tyck*.lean` | `ty_of`, `ck_tyck` |
| `Hash*.lean` | `words_eq`, `ck_hash`, `find_not`, `ck_hput`, `ck_hgrow`, `ck_intern` |
| `Builders*.lean`, `Intern.lean` | `ck_room`, `mk0..mk3`, `mkn`, `mkval`, `mk_eq`, `mk_not`, `expr_at`, `push_args`; `Intern.lean` = the unconditional forms |
| `RuleLib.lean` | the rule library: `RCtx`, `rule_begin/arity/guard/assign/ret` macros, `WP.rule_*` call rules, `Built`, `StkTop` |
| `RulesBasic*.lean`, `Basic.lean` | the 17 basic rules |
| `Bool*.lean`, `Eval*.lean`, `Clause*.lean`, `Aci*.lean`, `Poly*.lean`, `Rewrite*.lean`, `Bitblast*.lean` | the rule families (each `<Family>.lean` imports its parts) |
| `Load*.lean` | `ck_init`, `ck_load`, `ck_scan` |
| `Goal*.lean` | `ck_goal`, the comparison with the verifier's goal |
| `Replay*.lean` | `ck_rule` (dispatch), `ck_step`, `ck_run`, `ck_free`, `vbcf_check`, `vbcf_check_proof`, and the corollaries with `checkBcf_sound` |
| `Compact*.lean` | `ck_compact` (`Compact.lean` lists the parts): the compacted pool, the new view, and one lemma per loop |
| `KeepFacts*.lean` | pure Lean: no rule changes the fact array (`RulesKeepFacts`) |
| `Final.lean` | `ruleSpecs : RuleSpecs` and the unconditional entry theorems |
| `CostBase.lean`, `CostReg.lean`, `CostAuto.lean` | the cost proofs' infrastructure: the budget cells (`Budget`, `Fld`), the lemma registry (`fncost_register`), the amortised specification (`Amort`) and the tactics (`wpc_auto`, `wpc_call`, `wpc_finish`, …) |
| `CostCore.lean`, `CostCore2.lean`, `CostAci.lean`, `CostLeaf.lean`, `CostBool.lean`, `CostBool2.lean`, `CostMid.lean`, `CostEvalRw.lean`, `CostRules.lean`, `CostReplay.lean`, `CostRule.lean`, `CostTop.lean` | one cost lemma per C function (173), by family |
| `CostCompact.lean`, `CostCompact2.lean`, `CostLive.lean` | `ck_compact_cost` (`CompactPre` is the trigger; a `5000·sp` potential pays each pop) and `TypedU32`, the invariant that every `u32` field of the struct holds a 32-bit value, which the trigger's 64-bit sum needs |
| `CostFinal.lean`, `Cost.lean` | the cost theorem and its combination with soundness; `Cost.lean` imports everything (`lake build Vbcf.Proof.Cost`) |

## The method

A specification is an `EmbC.FnSpec prog "name" pre post`: from any state and
arguments satisfying `pre`, the call does not get stuck, and if it returns,
`post` holds.  "Not stuck" is memory safety and absence of every undefined
behaviour the semantics models.

A proof is symbolic execution.  The memory is never inspected directly;
instead there is one hypothesis `h : Holds W st.mem sb c` describing the
current state by a `CMem` value `c`, and each store produces a fresh state
with `Holds` for the updated `c`.

Skeleton (see `tick_spec` in `Core1.lean` for the smallest complete example,
`push_spec` in `Push.lean` for a long one):

```lean
theorem foo_spec … : FnSpec Vbcf.prog "foo" (fun vs s => vs = [.ptr sb 0, .u32 x] ∧ Holds W s.mem sb c ∧ …) (…) := by
  have hs := prog_ck
  apply FnSpec.intro' (fn := foo) rfl
  rintro vs st ⟨rfl, h, …⟩
  simp [foo, bindParams, Mem.hasTy_ptr h.ck rfl]   -- binds the parameters
  simp only [Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]
  -- then, statement by statement:
  apply WP.seq                     -- when the statement is followed by more
  apply WP.assign; ck_simp [facts] -- x = e;
  apply WP.ite;    ck_simp [facts] -- if: leaves (cond → WP then) ∧ (¬cond → WP else)
  apply WP.ck_setField hs h (by rfl); ck_simp; intro st h          -- st->f = e;   (u32 field)
  apply WP.ck_store .stk h (by rfl) hptr; ck_simp [..]; refine ⟨bound, ?_⟩; intro st h   -- st->stk[i] = e;
  apply WP.call (callee_spec args); ck_simp; refine ⟨pre, ?_⟩; intro rv st' hpost   -- x = f(..);
  apply WP.while (I := Inv) …      -- loops need an invariant
  apply WP.ret; ck_simp [retPost]  -- return e;
  apply WP.skip                    -- the empty else branch
```

Things learned the hard way:

* **Name the current state `h` and the struct lookup `hs`.**  `ck_simp` uses
  those two names to evaluate every `st->field`.
* **Array reads need cell facts.**  `st->pool[e]` evaluates to
  `m.loadArr b i`; give `ck_simp` the pointer fact (`hpool : c.k.pool = some (b, 0)`),
  `h.rd_pool hpool`, and `rd_u32 hcell` for the cell
  (`hcell : c.pool[i]? = some (.u32 w)`).
* **Index arithmetic.**  A C index like `p + 1` is a `BitVec 32`; to use a
  cell fact stated with `Nat` indices, first prove
  `(p + 1#32).toNat = p.toNat + 1` (`bv_norm`, or `rw [bv_add_toNat (by omega)]`)
  and pass it to `ck_simp`.
* **Write literals as `1#32`.**  After `simp`, goals contain `1#32`, not `1`;
  a hypothesis mentioning `1` will not match.
* **Intermediate assertions must be named `def`s.**  `ck_simp` simplifies
  everything in the goal, including a postcondition written inline; a named
  definition (like `PushMid`) is left alone.  Join the branches of an `if`
  with `WP.mono (Q := Named …)`.
* **Applying a store rule right after a call or a kernel call:** the state
  in the goal is then a structure literal, so the memory equation must be
  delayed: `apply WP.ck_setField hs h (by rfl)`.
* **Anonymous-constructor goals may have been reshaped by `simp`** (for
  example an `∃` moved inward).  If `exact ⟨…⟩` misbehaves, use
  `trace_state` to look.
* **Allocation** (`kvrealloc`, `kvcalloc`, `kvfree`) is the only place blocks
  appear.  Use `Holds.realloc_run`, `Holds.grow_blocks`, `Holds.grow` as in
  `push_spec`.
* Check a file with `lake env lean File.lean`; build only your own module.
  No `sorry`, no `native_decide`; only the three standard axioms.

## The cost proofs

The authoritative cost runner `Prog.runC` (`EmbC/Cost/Machine.lean`)
instruments the transitions of `EmbC.Semantics.next`, counting a `Cost` pair:
machine transitions plus kernel-call work (`t`) and allocator-requested words
(`m`).  Every actual transition, including administrative control, costs one.  `runC_erase` proves
that erasing these counters gives `Prog.run` at exactly the same machine-step
fuel, including timeout and stuck results.

The compositional rules reason directly about this operational machine.
`WPC` describes a statement under its actual continuation, and `FnCost`
requires a finite `Prog.runC` execution.  Their rules compose machine steps
and add costs for sequencing, loops and function calls.  They allow a stuck
result; on return, the postcondition bounds its cost.  `FnCost.run` uses
`runC_erase` and `FnSpec` to exclude stuck results and obtain one operational
run satisfying both specifications.

A cost proof never sees the representation invariant.  It tracks only the two
budget cells of the struct (`Budget st.mem sb w mm`: work at cell 20, memory
at cell 22), and every function's lemma is an `Amort sb A B Bm S`:

    c.t + A * w' + S rv ≤ A * w + B rv      and     c.m + mm' ≤ mm + Bm

for the budgets `w, mm` on entry and `w', mm'` on exit, the rate `A` (time per
unit of work), an allowance `B` and a slack `S` handed back to the caller
(a function that spent work gives back what it did not use, so a caller's loop
of such calls needs no trip count).  Loops are budget-paid (the C `spend`s
before them), counted over an 8-bit argument count, or paid by a callee's
slack; the few loops whose bound depended on a fact the cost proof cannot see
got a never-taken check in the C instead.  `wpc_auto` proves the straight-line
parts and the registered calls automatically; loops get an invariant by hand.
`ck_init` and the driver (`CostReplay.lean`, `CostTop.lean`) have custom
postconditions, and `CostFinal.lean` instantiates the rate (`rateA`) and adds
the allowances up.
