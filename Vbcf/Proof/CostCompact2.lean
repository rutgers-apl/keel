import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostLive

/-!
# Vbcf cost proofs: `ck_compact` (`Vbcf/Replay.lean`)

`ck_compact` reclaims the pool between steps.  Its cost lemma is an `Amort`
like the others, but its loops are bounded by struct cells that the budget
alone does not describe, so the proof tracks more cells (`CostCompact.lean`):

* `flen` (cell 7): the mark loop and the remap loop run to `st->flen`, and the
  first `spend` paid for `flen` iterations of each; `spend` and `push` keep the
  cell.
* `sp` (cell 11): the worklist loop pops until `st->sp` is 0; every `push`
  that succeeds adds one, and its slack pays `5000` for the pop to come (a pop
  and its at most 255 children cost less).  The worklist's measure is
  `2 * work + sp`.
* `lo`, `plen` (cells 24 and 1) at entry, with `2 lo + flen + 65536 < plen`
  (the trigger in `ck_run`) and a memory budget of at most `2^30` words: the
  charge of `n = plen - lo` words then shows that `n + lo + flen = plen + flen`
  does not wrap, so the first `spend` paid for every word walked, and
  `plen < 2^31` (the refill's `o + 1 + ar` does not wrap).

The precondition is `CompactPre`.  The work: `spend(plen + flen)` pays the
array `fw` (2 per word), the slide (`≤ 40` per word of `pool[lo, plen)`), the
walk over `pool[0, lo)` (`≤ 20` per word), the refill (`≤ 80` per word of
`pool[0, cur)` plus one node of overshoot, `ck_hput`'s allowance included),
and the two loops over the facts (`≤ 60` and `≤ 20` per fact), with `A` left
over for the slack (`cmp_pay`: `plen + flen > 65536`); the worklist is paid by
the pushes; the table-size doubling by its `tick`s (measure: the work
budget); the fresh table by `spend(hc)`.  Memory: `n + hc` words, each charged
to the memory budget before it is allocated (`Bm = 0`).  The loop invariants
are named definitions (`cmpI1` … `cmpI7`) so that `embc_simp` leaves them
alone.

| function     | A ≥  | B   | S                    | lines | how |
|--------------|------|-----|----------------------|-------|-----|
| `ck_compact` | 6000 | 200 | `slackUnless 0#32 A` | 571   | manual: 9 loops (two nested), `CS` across `spend`/`push` |

`WPC.ite_trigger` turns `ck_run`'s trigger into `CompactPre`: the four cells
it reads hold `u32`s (`TypedU32`, `CostLive.lean`), so the `u64` sum does not
wrap.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

/-- The locals of `ck_compact`. -/
def cmpEnv (sb : Nat) (lo plen n : BitVec 32) (fw : Val) (j r o hdr code ar i c cur nodes ok : BitVec 32)
    (nt : Val) (hc : BitVec 64) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("lo", .u32, .u32 lo), ("plen", .u32, .u32 plen),
    ("n", .u32, .u32 n), ("fw", Ty.u32.ptr, fw), ("j", .u32, .u32 j), ("r", .u32, .u32 r),
    ("o", .u32, .u32 o), ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 code), ("ar", .u32, .u32 ar),
    ("i", .u32, .u32 i), ("c", .u32, .u32 c), ("cur", .u32, .u32 cur), ("nodes", .u32, .u32 nodes),
    ("ok", .u32, .u32 ok), ("nt", Ty.u32.ptr, nt), ("hc", .u64, .u64 hc)]

/-- What `ck_run` knows when it calls `ck_compact`: the cells `lo`, `plen`, `flen`, the
trigger (more than `2 lo + flen + COMPACT_GAP` words in the pool), and a memory budget
of at most `2^30` words (as `ck_init` set it). -/
def CompactPre (sb : Nat) (L P F : BitVec 32) : List Val → (KernelState prog State) → Prop := fun vs st =>
  vs = [.ptr sb 0] ∧ Fld st.mem sb 24 (.u32 L) ∧ Fld st.mem sb 1 (.u32 P) ∧ Fld st.mem sb 7 (.u32 F) ∧
    2 * L.toNat + F.toNat + 65536 < P.toNat ∧
    ∃ w mm : BitVec 32, Budget st.mem sb w mm ∧ mm.toNat ≤ 2 ^ 30

theorem assignDst_some_set' {env env' : Env} {m : Mem} {x : Var} {rv : Option Val}
    (h : assignDst env m (some x) rv = some env') : ∃ v, rv = some v ∧ env' = env.set x v := by
  cases rv with
  | none => simp [assignDst] at h
  | some v => exact ⟨v, rfl, Env.assign_some' h⟩

theorem cmp_sub {L P : BitVec 32} (h : L.toNat ≤ P.toNat) : (P - L).toNat = P.toNat - L.toNat := by
  rw [BitVec.toNat_sub]; omega

theorem cmp_spend_arg {L P F : BitVec 32} (h : P.toNat + F.toNat < 2 ^ 32) :
    (P - L + L + F).toNat = P.toNat + F.toNat := by
  rw [BitVec.sub_add_cancel, BitVec.toNat_add]; omega

/-- The first `spend` pays for everything: `A * N ≥ A + 200 N + 200000` once `N ≥ 65537`. -/
theorem cmp_pay {A N : Nat} (hA : 6000 ≤ A) (hN : 65537 ≤ N) : A + 200 * N + 200000 ≤ A * N := by
  have h1 : A * N = A * (N - 1) + A := by
    rw [← Nat.mul_succ]; congr 1; omega
  have h2 : 6000 * (N - 1) ≤ A * (N - 1) := Nat.mul_le_mul_right _ hA
  omega

/-- From an amortised call that handed back `A`: the work budget dropped. -/
theorem cmp_lt_of_slack {A a b c t : Nat} (h : t + A * a + A ≤ A * b + c) (hc : c < A) : a < b := by
  rcases Nat.lt_or_ge a b with hab | hab
  · exact hab
  · have := Nat.mul_le_mul_left A hab
    omega

/-- The invariant of the mark loop (a named definition, so that `embc_simp` leaves it alone). -/
def cmpI1 (sb A : Nat) (L P F : BitVec 32) (fwv : Val) (w1 : BitVec 32) (M : Nat) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ j r ok w' mm' s : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv j r 0 0 0 0 0 0 0 0 ok .null 0 ∧ j.toNat ≤ F.toNat ∧
    CS st'.mem sb w' mm' F s ∧ k.t + A * w'.toNat + 5000 * s.toNat ≤ A * w1.toNat + 60 * j.toNat ∧
    k.m + mm'.toNat ≤ M

/-- The invariant of the worklist loop: each entry on the stack is worth `5000`. -/
def cmpI2 (sb A : Nat) (L P F : BitVec 32) (fwv : Val) (jF w2 s2 : BitVec 32) (M : Nat) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ r o hdr code ar i c ok w' mm' s : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv jF r o hdr code ar i c 0 0 ok .null 0 ∧
    CS st'.mem sb w' mm' F s ∧ k.t + A * w'.toNat + 5000 * s.toNat ≤ A * w2.toNat + 5000 * s2.toNat ∧
    k.m + mm'.toNat ≤ M

/-- The invariant of the loop over a popped node's children (at most 255): `15` per child,
a push paid by its own slack and `5000` for its pop; the work budget drops by one per push. -/
def cmpI2b (sb A : Nat) (L P F : BitVec 32) (fwv : Val) (jF r o hdr code ar wp sp : BitVec 32) (M : Nat) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ i c ok w' mm' s : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv jF r o hdr code ar i c 0 0 ok .null 0 ∧ i.toNat ≤ ar.toNat ∧
    CS st'.mem sb w' mm' F s ∧ k.t + A * w'.toNat + 5000 * s.toNat ≤ A * wp.toNat + 5000 * sp.toNat + 15 * i.toNat ∧
    2 * w'.toNat + s.toNat ≤ 2 * wp.toNat + sp.toNat ∧ k.m + mm'.toNat ≤ M

/-- The invariant of the slide over `pool[lo, plen)`: `40` per word walked; `cur ≤ o`. -/
def cmpI3 (sb : Nat) (L P F : BitVec 32) (fwv : Val) (jF w3 mm3 : BitVec 32) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ r o hdr code ar i c cur nodes ok : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv jF r o hdr code ar i c cur nodes ok .null 0 ∧
    L.toNat ≤ o.toNat ∧ o.toNat ≤ P.toNat ∧ cur.toNat ≤ o.toNat ∧
    CS st'.mem sb w3 mm3 F 0 ∧ k.t ≤ 40 * (o.toNat - L.toNat) ∧ k.m = 0

/-- The invariant of the copy of one node's arguments (at most 255). -/
def cmpI3b (sb : Nat) (L P F : BitVec 32) (fwv : Val) (jF r o hdr code ar cur nodes ok w3 mm3 : BitVec 32) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ i c : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv jF r o hdr code ar i c cur nodes ok .null 0 ∧ i.toNat ≤ ar.toNat ∧
    CS st'.mem sb w3 mm3 F 0 ∧ k.t ≤ 15 * i.toNat ∧ k.m = 0

/-- The invariant of the remap of the facts: `20` per fact. -/
def cmpI4 (sb : Nat) (L P F : BitVec 32) (fwv : Val) (o hdr code ar i cur nodes ok w3 mm3 : BitVec 32) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ j r c : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv j r o hdr code ar i c cur nodes ok .null 0 ∧ j.toNat ≤ F.toNat ∧
    CS st'.mem sb w3 mm3 F 0 ∧ k.t ≤ 20 * j.toNat ∧ k.m = 0

/-- The invariant of the walk over `pool[0, lo)`: `20` per word. -/
def cmpI5 (sb : Nat) (L P : BitVec 32) (fwv : Val) (j r hdr code i c cur ok w3 mm3 : BitVec 32) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ o ar nodes : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv j r o hdr code ar i c cur nodes ok .null 0 ∧ o.toNat ≤ L.toNat ∧
    Budget st'.mem sb w3 mm3 ∧ k.t ≤ 20 * o.toNat ∧ k.m = 0

/-- The invariant of the table-size doubling: each iteration paid by its `tick`. -/
def cmpI6 (sb A : Nat) (L P : BitVec 32) (fwv : Val) (j r o hdr code ar i c cur nodes w5 : BitVec 32)
    (mm5 : Nat) : Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ (ok w' mm' : BitVec 32) (hc : BitVec 64),
    env' = cmpEnv sb L P (P - L) fwv j r o hdr code ar i c cur nodes ok .null hc ∧
    Budget st'.mem sb w' mm' ∧ k.t + A * w'.toNat ≤ A * w5.toNat ∧ k.m + mm'.toNat ≤ mm5

/-- The invariant of the refill of the table: `80` per word of `pool[0, cur)` (one `ck_hput`
per node); `o` overshoots `cur` by at most one node. -/
def cmpI7 (sb A : Nat) (L P : BitVec 32) (fwv : Val) (j r hdr code ar i c cur nodes : BitVec 32)
    (ntv : Val) (hc : BitVec 64) (w8 : BitVec 32) (mm8 : Nat) : Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ o ok w' mm' : BitVec 32,
    env' = cmpEnv sb L P (P - L) fwv j r o hdr code ar i c cur nodes ok ntv hc ∧
    o.toNat ≤ cur.toNat + 256 ∧ Budget st'.mem sb w' mm' ∧ k.t + A * w'.toNat ≤ A * w8.toNat + 80 * o.toNat ∧
    k.m + mm'.toNat ≤ mm8

/-- A call `x = f(args)` whose arguments evaluate to `vs`, with an `Amort` cost lemma
given as a term. -/
theorem cmp_call {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {x : Var} {f : String} {args : List Expr}
    {sb A B : Nat} {S : Option Val → Nat} {vs : List Val} {w mm : BitVec 32}
    (hb : Budget st.mem sb w mm)
    (hspec : FnCost (State := State) prog f (BudPre sb vs) (Amort sb A (allow B) 0 S))
    (hargs : evalArgs prog env st.mem args = some vs) (hx : env.ty x = some .u32)
    (h : ∀ (r : BitVec 32) (st' : (KernelState prog State)) (c : Cost) (w' mm' : BitVec 32), Budget st'.mem sb w' mm' →
      c.t + A * w'.toNat + S (some (.u32 r)) ≤ A * w.toNat + B → c.m + mm'.toNat ≤ mm.toNat →
      Q .normal (env.set x (.u32 r)) st' (c + 2)) :
    WPC prog (.call (some x) f args) Q env st := by
  apply WPC.call hspec
  rw [hargs]
  refine ⟨⟨rfl, _, _, hb⟩, ?_⟩
  rintro rv st' c ⟨w', mm', hb', ht, hm⟩
  rw [hb.wk] at ht
  rw [hb.mk] at hm
  split
  · trivial
  rename_i env' hasg
  obtain ⟨r, rfl, rfl⟩ := assignDst_u32' hasg hx
  exact h r st' c w' mm' hb' (by simpa using ht) (by simpa using hm)

/-- `x = e1 + (e & k)` with `e1` evaluating to `a`: the value is `a + n` for some `n ≤ k`. -/
theorem WPC.assign_add_band {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x : Var} {e1 e : Expr}
    {a k : BitVec 32} (hx : env.ty x = some .u32) (h1 : evalE P env st.mem e1 = some (.u32 a))
    (h : ∀ n : BitVec 32, n.toNat ≤ k.toNat → Q .normal (env.set x (.u32 (a + n))) st 1) :
    WPC P (.assign x (.bin .add e1 (.bin .band e (.lit32 k)))) Q env st := by
  apply WPC.assign
  simp only [evalE, h1]
  cases evalE P env st.mem e with
  | none => trivial
  | some v =>
    cases v with
    | u32 b =>
      simp only [evalBin, evalArith, Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
      refine h _ ?_
      rw [BitVec.toNat_and]; exact Nat.and_le_right
    | _ => simp [evalBin]

/-- The last assignment of a loop body (`x = x + …`), whose value is computed from locals;
then the loop-next goal with the measure read off the locals (`h` gives the new value). -/
macro "cmp_assign" h:ident : tactic => `(tactic| (
  apply WPC.assign_eval
  intro _v _hv
  simp only [evalE, evalBin, evalArith, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at _hv
  subst _hv
  simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u32, Env.set, CPost.shift_apply,
    envU32, Env.get, $h:ident]))

theorem ck_compact_cost (sb A : Nat) (hA : 6000 ≤ A) (L P F : BitVec 32) :
    FnCost (State := State) prog "ck_compact" (CompactPre sb L P F) (Amort sb A (allow 200) 0 (slackUnless 0#32 A)) := by
  apply FnCost.intro (fn := ckCompact) rfl
  rintro vs st ⟨rfl, hlo, hpl, hfl, hrel, w, mm, hb, hmm⟩
  fncost_body ckCompact
  have hA6 : 6 ≤ A := by omega
  -- lo = st->lo; plen = st->plen; n = plen - lo;
  apply WPC.seq; apply WPC.assign_eval; intro v hv
  simp [evalE, Env.get, hlo.load cfi_lo (by simp)] at hv; subst hv
  simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u32]; wpc_simp
  apply WPC.seq; apply WPC.assign_eval; intro v hv
  simp [evalE, Env.get, hpl.load fi_plen (by simp)] at hv; subst hv
  simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u32]; wpc_simp
  apply WPC.seq; wpc_step
  have hLP : L.toNat ≤ P.toNat := by omega
  have hn : (P - L).toNat = P.toNat - L.toNat := cmp_sub hLP
  -- ok = spend(st, n + lo + st->flen);
  apply WPC.seq
  refine WPC.spend_fl (k := P + F) hA6 hb hfl (by simp [evalArgs, evalE, Env.get, hfl.load fi_flen (by simp), evalBin,
    evalArith, BitVec.sub_add_cancel]) rfl ?_
  intro r1 st1 c1 w1 mm1 hb1 hfl1 ht1 hm1
  wpc_simp
  -- if (ok == 0) return 0;
  apply WPC.seq; apply WPC.ite; embc_simp
  by_cases hr1 : r1 = 0#32
  · subst hr1
    simp only [↓reduceIte, Nat.add_zero] at ht1
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    wpc_auto
    wpc_done
  simp only [hr1, ↓reduceIte] at ht1
  refine ⟨fun h => absurd h hr1, fun _ => ?_⟩
  apply WPC.skip; wpc_simp
  -- if (st->mem < n) { st->err = ERR_LIMIT; return 0; } st->mem = st->mem - n;
  apply WPC.charge_mem_fld (k := P - L) hb1 hfl1 (fieldIn_ne_of_idx fi_mem (by decide)) (by rfl)
    (by simp [evalE, Env.get])
  · intro m' hb'
    wpc_finish
  intro hle m2 hb2 hfl2
  have hle' : (P - L).toNat ≤ mm1.toNat := BitVec.le_def.mp hle
  have hm2 : (mm1 - (P - L)).toNat = mm1.toNat - (P - L).toNat := bv_sub_toNat_of_le hle
  have hPF : P.toNat + F.toNat < 2 ^ 32 := by omega
  have hPFv : (P + F).toNat = P.toNat + F.toNat := by rw [BitVec.toNat_add]; omega
  rw [hPFv] at ht1
  have hpay := cmp_pay (N := P.toNat + F.toNat) hA (by omega)
  -- fw = kvcalloc((u64)n, sizeof(u32));
  apply WPC.seq
  apply WPC.ecall
  simp only [evalArgs, evalE, evalCast, Env.get, String.reduceEq, ↓reduceIte]
  split
  · trivial
  rename_i rv st3 hrun
  have hfree : ∀ b, [Val.u64 ((P - L).setWidth 64)] = [.ptr b 0] → Ext.kvcalloc .u32 = Ext.kvfree → b ≠ sb :=
    fun _ _ h => by cases h
  have hb3 := hb2.ext hrun hfree
  have hfl3 := hfl2.ext hrun hfree
  have hfw : ∀ b, rv = some (.ptr b 0) → b ≠ sb := fun b h => kvcalloc_fresh hb2 (h ▸ hrun)
  have hcost : Ext.costC prog (.kvcalloc .u32) [.u64 ((P - L).setWidth 64)] =
      ⟨2 * (P - L).toNat, (P - L).toNat⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]; have := (P - L).isLt; omega
  rw [hcost, hn]
  split
  · trivial
  rename_i env3 hasg
  obtain ⟨fwv, rfl, rfl⟩ := assignDst_some_set' hasg
  have hfw' : ∀ b, fwv = .ptr b 0 → b ≠ sb := fun b h => hfw b (by rw [h])
  clear hfw hasg hrun hfree
  wpc_simp
  -- if (fw == NULL) { st->err = ERR_NOMEM; return 0; }
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto
    wpc_done
  apply WPC.skip; wpc_simp
  -- st->sp = 0;
  obtain ⟨sp0, hsp0⟩ := hb3.fld_lt (i := 11) (by decide)
  apply WPC.seq
  refine WPC.setSp_cs (y := 0#32) hb3 hfl3 hsp0 (by simp [Env.get]) (by simp [evalE]) ?_
  intro m4 hcs4
  wpc_simp
  -- the mark loop over the facts: `60` per fact, a push paid by its own slack and `cmpD` for its pop
  apply WPC.seq
  apply WPC.while
    (I := cmpI1 sb A L P F fwv w1 (mm1 - (P - L)).toNat)
    (μ := fun env' _ => F.toNat - envU32 env' "j")
  · exact ⟨0#32, 0#32, r1, w1, mm1 - (P - L), 0#32, rfl, by simp, hcs4, by simp, by simp⟩
  rintro env' st' k ⟨j, r, ok, w', mm', s, rfl, hjF, hcs, hk, hkm⟩
  simp only [cmpEnv]
  embc_simp [hcs.2.1.load fi_flen (by simp)]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt' : j.toNat < F.toNat := by simpa [BitVec.lt_def] using hlt
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    have hs1 : (s + 1#32).toNat ≤ s.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq
    apply WPC.ite_any
    · apply WPC.seq; apply WPC.assign_u32 rfl; intro r'; wpc_simp
      apply WPC.ite_any
      · apply WPC.ite_any
        · apply WPC.seq; apply WPC.store_cs hcs; intro m5 hcs5; wpc_simp
          apply WPC.seq
          refine WPC.push_cs (v := r') hA6 hcs5 (by simp [evalArgs, evalE, Env.get]) rfl ?_
          intro r2 st6 c6 w6 mm6 hb6 hfl6 hsp6 ht6 hm6
          wpc_simp
          apply WPC.ite; embc_simp
          by_cases hr2 : r2 = 0#32
          · subst hr2
            simp only [↓reduceIte, Nat.add_zero] at ht6
            refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
            apply WPC.seq
            refine WPC.kvfree_bud hb6 (by simp [evalE, Env.get]) hfw' ?_
            intro st7 hb7
            wpc_simp
            wpc_auto
            wpc_done
          simp only [hr2, ↓reduceIte] at ht6
          have hcs6 : CS st6.mem sb w6 mm6 F (s + 1#32) := ⟨hb6, hfl6, hsp6 hr2⟩
          refine ⟨fun h => absurd h hr2, fun _ => ?_⟩
          apply WPC.skip; wpc_simp
          cmp_assign hj1
          refine ⟨by omega, ?_⟩; simp only [cmpI1]
          refine ⟨_, _, _, _, _, _, rfl, by omega, hcs6, ?_, ?_⟩ <;> cost_arith
        · apply WPC.skip; wpc_simp
          cmp_assign hj1
          refine ⟨by omega, ?_⟩; simp only [cmpI1]
          refine ⟨_, _, _, _, _, _, rfl, by omega, hcs, ?_, ?_⟩ <;> cost_arith
      · apply WPC.skip; wpc_simp
        cmp_assign hj1
        refine ⟨by omega, ?_⟩; simp only [cmpI1]
        refine ⟨_, _, _, _, _, _, rfl, by omega, hcs, ?_, ?_⟩ <;> cost_arith
    · apply WPC.skip; wpc_simp
      cmp_assign hj1
      refine ⟨by omega, ?_⟩; simp only [cmpI1]
      refine ⟨_, _, _, _, _, _, rfl, by omega, hcs, ?_, ?_⟩ <;> cost_arith
  have hjF' : j.toNat = F.toNat := by have := BitVec.le_def.mp hge; omega
  clear hge
  -- the worklist: every pop paid by the push that put the node there
  apply WPC.seq
  apply WPC.while (I := cmpI2 sb A L P F fwv j w' s mm'.toNat)
    (μ := fun _ st' => 2 * wk st'.mem sb + spOf st'.mem sb)
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, hcs, by simp, by simp⟩
  rintro env2 st2 k2 ⟨r2, o2, hdr2, code2, ar2, i2, c2, ok2, w2, mm2, s2, rfl, hcs2, hk2, hkm2⟩
  simp only [cmpEnv]
  embc_simp [hcs2.2.2.load fi_sp (by simp)]
  refine ⟨fun hs0 => ?_, fun hs0 => ?_⟩
  rotate_left
  · have hs0' : s2 ≠ 0#32 := by intro h; subst h; simp at hs0
    have hsd := bv_sub_one_toNat hs0'
    have hsp := bv_pos_of_ne hs0'
    -- st->sp = st->sp - 1;
    apply WPC.seq
    refine WPC.setSp_cs (y := s2 - 1#32) hcs2.1 hcs2.2.1 hcs2.2.2 (by simp [Env.get])
      (by simp [evalE, Env.get, hcs2.2.2.load fi_sp (by simp), evalBin, evalArith]) ?_
    intro m3 hcs3
    wpc_simp
    apply WPC.seq; apply WPC.assign_u32 rfl; intro o3; wpc_simp
    apply WPC.seq; apply WPC.assign_u32 rfl; intro hdr3; wpc_simp
    apply WPC.seq; apply WPC.assign_band rfl; intro code3 _; wpc_simp
    apply WPC.ite_any
    rotate_left
    · apply WPC.skip
      try simp only [CPost.shift_apply]
      refine ⟨?_, ?_⟩
      · simp only [hcs3.1.wk, hcs3.2.2.spOf, hcs2.1.wk, hcs2.2.2.spOf]; omega
      simp only [cmpI2]
      refine ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, hcs3, ?_, ?_⟩ <;> cost_arith
    apply WPC.seq; apply WPC.assign_band rfl; intro ar3 har3; wpc_simp
    have har3' : ar3.toNat ≤ 255 := by simpa using har3
    apply WPC.seq; apply WPC.ite_any
    · apply WPC.seq
      refine WPC.setField_cs hcs3 (by decide) (by decide) (fieldIn_ne_of_idx fi_err (by decide))
        (fieldIn_ne_of_idx fi_err (by decide)) ?_
      intro m4 hcs4
      wpc_simp
      apply WPC.seq
      refine WPC.kvfree_cs hcs4 (by simp [evalE, Env.get]) hfw' ?_
      intro st5 hcs5
      have hb5 := hcs5.1
      wpc_simp
      wpc_auto
      wpc_done
    apply WPC.skip; wpc_simp
    apply WPC.seq; wpc_step
    apply WPC.while (I := cmpI2b sb A L P F fwv j r2 o3 hdr3 code3 ar3 w2 (s2 - 1#32) mm2.toNat)
      (μ := fun env' _ => ar3.toNat - envU32 env' "i")
    · exact ⟨_, _, _, _, _, _, rfl, by simp, hcs3, by simp, by simp, by simp⟩
    rintro env4 st4 k4 ⟨i4, c4, ok4, w4, mm4, s4, rfl, hi4, hcs4, hk4, hws4, hkm4⟩
    simp only [cmpEnv]
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · -- the children are done: the pop is paid
      try simp only [CPost.shift_apply]
      refine ⟨?_, ?_⟩
      · simp only [hcs4.1.wk, hcs4.2.2.spOf, hcs2.1.wk, hcs2.2.2.spOf]; omega
      simp only [cmpI2]
      refine ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, hcs4, ?_, ?_⟩ <;> cost_arith
    have hlt' : i4.toNat < ar3.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i4 + 1#32).toNat = i4.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    have hs41 : (s4 + 1#32).toNat ≤ s4.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq; apply WPC.assign_u32 rfl; intro c5; wpc_simp
    apply WPC.seq
    apply WPC.ite_any
    · apply WPC.ite_any
      · apply WPC.seq; apply WPC.store_cs hcs4; intro m6 hcs6; wpc_simp
        apply WPC.seq
        refine WPC.push_cs (v := c5) hA6 hcs6 (by simp [evalArgs, evalE, Env.get]) rfl ?_
        intro r7 st7 c7 w7 mm7 hb7 hfl7 hsp7 ht7 hm7
        wpc_simp
        apply WPC.ite; embc_simp
        by_cases hr7 : r7 = 0#32
        · subst hr7
          simp only [↓reduceIte, Nat.add_zero] at ht7
          refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
          apply WPC.seq
          refine WPC.kvfree_bud hb7 (by simp [evalE, Env.get]) hfw' ?_
          intro st8 hb8
          wpc_simp
          wpc_auto
          wpc_done
        simp only [hr7, ↓reduceIte] at ht7
        have hcs7 : CS st7.mem sb w7 mm7 F (s4 + 1#32) := ⟨hb7, hfl7, hsp7 hr7⟩
        have hw7 : w7.toNat < w4.toNat := cmp_lt_of_slack ht7 (by omega)
        refine ⟨fun h => absurd h hr7, fun _ => ?_⟩
        apply WPC.skip; wpc_simp
        cmp_assign hi1
        refine ⟨by omega, ?_⟩; simp only [cmpI2b]
        refine ⟨_, _, _, _, _, _, rfl, by omega, hcs7, ?_, by omega, ?_⟩ <;> cost_arith
      · apply WPC.skip; wpc_simp
        cmp_assign hi1
        refine ⟨by omega, ?_⟩; simp only [cmpI2b]
        refine ⟨_, _, _, _, _, _, rfl, by omega, hcs4, ?_, by omega, ?_⟩ <;> cost_arith
    · apply WPC.skip; wpc_simp
      cmp_assign hi1
      refine ⟨by omega, ?_⟩; simp only [cmpI2b]
      refine ⟨_, _, _, _, _, _, rfl, by omega, hcs4, ?_, by omega, ?_⟩ <;> cost_arith
  have hs20 : s2 = 0#32 := by simpa using hs0
  subst hs20
  clear hs0
  -- the slide: `cur = lo; o = lo;`, then every node of `pool[lo, plen)` once
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq
  apply WPC.while (I := cmpI3 sb L P F fwv j w2 mm2) (μ := fun env' _ => P.toNat - envU32 env' "o")
  · exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, Nat.le_refl _, hLP, Nat.le_refl _, hcs2, by simp, by simp⟩
  rintro env3 st3 k3 ⟨r3, o3, hdr3, code3, ar3, i3, c3, cur3, nodes3, ok3, rfl, hLo3, ho3, hco3, hcs3, hk3, hkm3⟩
  simp only [cmpEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt' : o3.toNat < P.toNat := by simpa [BitVec.lt_def] using hlt
    apply WPC.seq; apply WPC.assign_u32 rfl; intro hdr4; wpc_simp
    apply WPC.seq; apply WPC.assign_band rfl; intro ar4 har4; wpc_simp
    have har4' : ar4.toNat ≤ 255 := by simpa using har4
    apply WPC.seq; apply WPC.ite; embc_simp
    constructor
    · intro _
      apply WPC.seq
      refine WPC.setField_cs hcs3 (by decide) (by decide) (fieldIn_ne_of_idx fi_err (by decide))
        (fieldIn_ne_of_idx fi_err (by decide)) ?_
      intro m4 hcs4
      wpc_simp
      apply WPC.seq
      refine WPC.kvfree_cs hcs4 (by simp [evalE, Env.get]) hfw' ?_
      intro st5 hcs5
      have hb5 := hcs5.1
      wpc_simp
      wpc_auto
      wpc_done
    intro hle
    obtain ⟨hs1, hs2⟩ := replay_load_step hlt' har4' hle
    apply WPC.skip; wpc_simp
    apply WPC.seq
    apply WPC.ite_any
    rotate_left
    · apply WPC.skip; wpc_simp
      cmp_assign hs1
      refine ⟨by omega, ?_⟩; simp only [cmpI3]
      refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, by omega, by omega, by omega, hcs3, ?_, ?_⟩ <;> cost_arith
    apply WPC.seq; apply WPC.store_cs hcs3; intro m5 hcs5; wpc_simp
    apply WPC.seq; apply WPC.assign_band rfl; intro code5 _; wpc_simp
    apply WPC.seq; wpc_step
    apply WPC.seq
    apply WPC.while (I := cmpI3b sb L P F fwv j r3 o3 hdr4 code5 ar4 cur3 nodes3 ok3 w2 mm2)
      (μ := fun env' _ => ar4.toNat - envU32 env' "i")
    · exact ⟨_, _, rfl, by simp, hcs5, by simp, by simp⟩
    rintro env6 st6 k6 ⟨i6, c6, rfl, hi6, hcs6, hk6, hkm6⟩
    simp only [cmpEnv]
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    rotate_left
    · have hlt6 : i6.toNat < ar4.toNat := by simpa [BitVec.lt_def] using hlt
      have hi1 : (i6 + 1#32).toNat = i6.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      apply WPC.seq; apply WPC.assign_u32 rfl; intro c7; wpc_simp
      apply WPC.seq
      apply WPC.ite_any
      · apply WPC.assign_u32 rfl; intro c8; wpc_simp
        apply WPC.seq; apply WPC.store_cs hcs6; intro m9 hcs9; wpc_simp
        cmp_assign hi1
        refine ⟨by omega, ?_⟩; simp only [cmpI3b]
        refine ⟨_, _, rfl, by omega, hcs9, ?_, ?_⟩ <;> cost_arith
      apply WPC.skip; wpc_simp
      apply WPC.seq; apply WPC.store_cs hcs6; intro m9 hcs9; wpc_simp
      cmp_assign hi1
      refine ⟨by omega, ?_⟩; simp only [cmpI3b]
      refine ⟨_, _, rfl, by omega, hcs9, ?_, ?_⟩ <;> cost_arith
    have hie : i6.toNat = ar4.toNat := by have := BitVec.le_def.mp hge; omega
    have hc1 : (cur3 + 1#32 + ar4).toNat = cur3.toNat + 1 + ar4.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    apply WPC.seq; apply WPC.store_cs hcs6; intro m10 hcs10; wpc_simp
    apply WPC.seq; wpc_step
    wpc_step
    cmp_assign hs1
    refine ⟨by omega, ?_⟩; simp only [cmpI3]
    refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, by omega, by omega, by omega, hcs10, ?_, ?_⟩ <;> cost_arith
  have hoP : o3.toNat = P.toNat := by have := BitVec.le_def.mp hge; omega
  clear hge
  -- st->plen = cur; st->live = cur - lo; j = 0;
  apply WPC.seq
  refine WPC.setField_cs hcs3 (by decide) (by decide) (fieldIn_ne_of_idx fi_plen (by decide))
    (fieldIn_ne_of_idx fi_plen (by decide)) ?_
  intro m4 hcs4; wpc_simp
  apply WPC.seq
  refine WPC.setField_cs hcs4 (by decide) (by decide) (fieldIn_ne_of_idx cfi_live (by decide))
    (fieldIn_ne_of_idx cfi_live (by decide)) ?_
  intro m5 hcs5; wpc_simp
  apply WPC.seq; wpc_step
  -- the remap of the facts
  apply WPC.seq
  apply WPC.while (I := cmpI4 sb L P F fwv o3 hdr3 code3 ar3 i3 cur3 nodes3 ok3 w2 mm2)
    (μ := fun env' _ => F.toNat - envU32 env' "j")
  · exact ⟨_, _, _, rfl, by simp, hcs5, by simp, by simp⟩
  rintro env6 st6 k6 ⟨j6, r6, c6, rfl, hj6, hcs6, hk6, hkm6⟩
  simp only [cmpEnv]
  embc_simp [hcs6.2.1.load fi_flen (by simp)]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt6 : j6.toNat < F.toNat := by simpa [BitVec.lt_def] using hlt
    have hj1 : (j6 + 1#32).toNat = j6.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq; apply WPC.assign_u32 rfl; intro r7; wpc_simp
    apply WPC.seq
    apply WPC.ite_any
    · apply WPC.seq; apply WPC.assign_u32 rfl; intro c7; wpc_simp
      apply WPC.seq
      apply WPC.ite_any
      · apply WPC.assign_u32 rfl; intro c8; wpc_simp
        apply WPC.store_cs hcs6; intro m9 hcs9; wpc_simp
        cmp_assign hj1
        refine ⟨by omega, ?_⟩; simp only [cmpI4]
        refine ⟨_, _, _, rfl, by omega, hcs9, ?_, ?_⟩ <;> cost_arith
      apply WPC.skip; wpc_simp
      apply WPC.store_cs hcs6; intro m9 hcs9; wpc_simp
      cmp_assign hj1
      refine ⟨by omega, ?_⟩; simp only [cmpI4]
      refine ⟨_, _, _, rfl, by omega, hcs9, ?_, ?_⟩ <;> cost_arith
    apply WPC.skip; wpc_simp
    cmp_assign hj1
    refine ⟨by omega, ?_⟩; simp only [cmpI4]
    refine ⟨_, _, _, rfl, by omega, hcs6, ?_, ?_⟩ <;> cost_arith
  have hjF6 : j6.toNat = F.toNat := by have := BitVec.le_def.mp hge; omega
  clear hge
  -- the walk over `pool[0, lo)`, counting its nodes
  apply WPC.seq; wpc_step
  apply WPC.seq
  apply WPC.while (I := cmpI5 sb L P fwv j6 r6 hdr3 code3 i3 c6 cur3 ok3 w2 mm2)
    (μ := fun env' _ => L.toNat - envU32 env' "o")
  · exact ⟨_, _, _, rfl, by simp, hcs6.1, by simp, by simp⟩
  rintro env7 st7 k7 ⟨o7, ar7, nodes7, rfl, ho7, hb7, hk7, hkm7⟩
  simp only [cmpEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt7 : o7.toNat < L.toNat := by simpa [BitVec.lt_def] using hlt
    apply WPC.seq; apply WPC.assign_band rfl; intro ar8 har8; wpc_simp
    have har8' : ar8.toNat ≤ 255 := by simpa using har8
    apply WPC.seq; apply WPC.ite; embc_simp
    constructor
    · intro _
      wpc_auto
      refine WPC.kvfree_bud ‹Budget _ _ _ _› (by simp [evalE, Env.get]) hfw' ?_
      intro st9 hb9
      wpc_simp
      wpc_auto
      wpc_done
    intro hle
    obtain ⟨hs1, hs2⟩ := replay_load_step hlt7 har8' hle
    apply WPC.skip; wpc_simp
    apply WPC.seq; wpc_step
    cmp_assign hs1
    refine ⟨by omega, ?_⟩; simp only [cmpI5]
    refine ⟨_, _, _, rfl, by omega, hb7, ?_, ?_⟩ <;> cost_arith
  have hoL : o7.toNat = L.toNat := by have := BitVec.le_def.mp hge; omega
  clear hge
  -- the table size: doubled until it is four times the nodes, one `tick` each
  apply WPC.seq; wpc_step
  apply WPC.seq
  apply WPC.while (I := cmpI6 sb A L P fwv j6 r6 o7 hdr3 code3 ar7 i3 c6 cur3 nodes7 w2 mm2.toNat)
    (μ := fun _ st' => wk st'.mem sb)
  · exact ⟨_, _, _, _, rfl, hb7, by simp, by simp⟩
  rintro env8 st8 k8 ⟨ok8, w8, mm8, hc8, rfl, hb8, hk8, hkm8⟩
  simp only [cmpEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · apply WPC.seq
    refine cmp_call hb8 (tick_cost sb A hA6) (by simp [evalArgs, evalE, Env.get]) rfl ?_
    intro r9 st9 c9 w9 mm9 hb9 ht9 hm9
    wpc_simp
    apply WPC.seq; apply WPC.ite; embc_simp
    by_cases hr9 : r9 = 0#32
    · subst hr9
      simp only [slackUnless_apply, ↓reduceIte, Nat.add_zero] at ht9
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      apply WPC.seq
      refine WPC.kvfree_bud hb9 (by simp [evalE, Env.get]) hfw' ?_
      intro st10 hb10
      wpc_simp
      wpc_auto
      wpc_done
    simp only [slackUnless_apply, Option.some.injEq, Val.u32.injEq, hr9, ↓reduceIte] at ht9
    have hw9 : w9.toNat < w8.toNat := cmp_lt_of_slack ht9 (by omega)
    refine ⟨fun h => absurd h hr9, fun _ => ?_⟩
    apply WPC.skip; wpc_simp
    apply WPC.assign_u64 rfl; intro hc9
    simp only [CPost.shift_apply]
    refine ⟨by rw [hb9.wk, hb8.wk]; exact hw9, ?_⟩
    simp only [cmpI6]
    refine ⟨_, _, _, _, rfl, hb9, ?_, ?_⟩ <;> cost_arith
  clear hge
  -- if (hc > (u64)MAX_POOL) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
  apply WPC.seq; apply WPC.ite; embc_simp
  constructor
  · intro _
    wpc_auto
    refine WPC.kvfree_bud ‹Budget _ _ _ _› (by simp [evalE, Env.get]) hfw' ?_
    intro st10 hb10
    wpc_simp
    wpc_auto
    wpc_done
  intro hhc
  have hhc' : hc8.toNat ≤ 1073741824 := by
    have := BitVec.le_def.mp hhc; simpa using this
  clear hhc
  have hhc32 : (hc8.setWidth 32).toNat = hc8.toNat := by
    rw [BitVec.toNat_setWidth]; omega
  have hAhc : 2 * hc8.toNat ≤ A * hc8.toNat := Nat.mul_le_mul_right _ (by omega)
  apply WPC.skip; wpc_simp
  -- ok = spend(st, (u32)hc); if (ok == 0) { kvfree(fw); return 0; }
  apply WPC.seq
  refine cmp_call hb8 (spend_cost sb A hA6 (hc8.setWidth 32)) (by simp [evalArgs, evalE, Env.get, evalCast]) rfl ?_
  intro r10 st10 c10 w10 mm10 hb10 ht10 hm10
  wpc_simp
  apply WPC.seq; apply WPC.ite; embc_simp
  by_cases hr10 : r10 = 0#32
  · subst hr10
    simp only [slackUnless_apply, ↓reduceIte, Nat.add_zero] at ht10
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply WPC.seq
    refine WPC.kvfree_bud hb10 (by simp [evalE, Env.get]) hfw' ?_
    intro st11 hb11
    wpc_simp
    wpc_auto
    wpc_done
  simp only [slackUnless_apply, Option.some.injEq, Val.u32.injEq, hr10, ↓reduceIte, hhc32] at ht10
  refine ⟨fun h => absurd h hr10, fun _ => ?_⟩
  apply WPC.skip; wpc_simp
  -- if (st->mem < (u32)hc) { st->err = ERR_LIMIT; kvfree(fw); return 0; } st->mem = st->mem - (u32)hc;
  apply WPC.seq; apply WPC.ite; embc_simp [hb10.ld_mem]
  constructor
  · intro _
    wpc_auto
    refine WPC.kvfree_bud ‹Budget _ _ _ _› (by simp [evalE, Env.get]) hfw' ?_
    intro st11 hb11
    wpc_simp
    wpc_auto
    wpc_done
  intro hmh
  have hmh' : hc8.toNat ≤ mm10.toNat := by
    have := BitVec.le_def.mp hmh; rw [hhc32] at this; exact this
  have hm11 : (mm10 - hc8.setWidth 32).toNat = mm10.toNat - hc8.toNat := by
    rw [BitVec.toNat_sub, hhc32]; omega
  clear hmh
  apply WPC.skip; wpc_simp
  apply WPC.seq
  refine WPC.setMem (x := mm10 - hc8.setWidth 32) hb10 (by simp [evalE, Env.get])
    (by simp [evalE, Env.get, hb10.ld_mem, evalCast, evalBin, evalArith]) ?_
  intro m11 hb11
  wpc_simp
  -- kvfree(st->htab): the struct survives, or the next store gets stuck
  apply WPC.seq
  apply WPC.kvfree_bud_or hb11
  intro st12 hor
  wpc_simp
  rcases hor with hb12 | hgone
  rotate_left
  · apply WPC.seq
    exact WPC.setField_gone hgone (by simp [Env.get])
  apply WPC.seq; apply WPC.setField_bud hb12 (by decide) (by decide); intro m13 hb13; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb13 (by decide) (by decide); intro m14 hb14; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb14 (by decide) (by decide); intro m15 hb15; wpc_simp
  -- nt = kvcalloc(hc, sizeof(u32));
  apply WPC.seq
  apply WPC.ecall
  simp only [evalArgs, evalE, Env.get, String.reduceEq, ↓reduceIte]
  split
  · trivial
  rename_i rv st16 hrun
  have hb16 := hb15.ext hrun (fun _ _ h => by cases h)
  have hcost2 : Ext.costC prog (.kvcalloc .u32) [.u64 hc8] = ⟨2 * hc8.toNat, hc8.toNat⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]
  rw [hcost2]
  split
  · trivial
  rename_i env16 hasg
  obtain ⟨ntv, rfl, rfl⟩ := assignDst_some_set' hasg
  clear hasg hrun
  wpc_simp
  -- if (nt == NULL) { st->err = ERR_NOMEM; kvfree(fw); return 0; }
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto
    refine WPC.kvfree_bud ‹Budget _ _ _ _› (by simp [evalE, Env.get]) hfw' ?_
    intro st17 hb17
    wpc_simp
    wpc_auto
    wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb16 (by decide) (by decide); intro m17 hb17; wpc_simp
  apply WPC.seq; apply WPC.setField_bud hb17 (by decide) (by decide); intro m18 hb18; wpc_simp
  apply WPC.seq; wpc_step
  -- the refill: one `ck_hput` per node of `pool[0, cur)`
  have hP31 : P.toNat < 2 ^ 31 := by omega
  apply WPC.seq
  apply WPC.while (I := cmpI7 sb A L P fwv j6 r6 hdr3 code3 ar7 i3 c6 cur3 nodes7 ntv hc8 w10
      (mm10 - hc8.setWidth 32).toNat)
    (μ := fun env' _ => cur3.toNat - envU32 env' "o")
  · exact ⟨_, _, _, _, rfl, by simp, hb18, by simp, by simp⟩
  rintro env19 st19 k19 ⟨o19, ok19, w19, mm19, rfl, ho19, hb19, hk19, hkm19⟩
  simp only [cmpEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt19 : o19.toNat < cur3.toNat := by simpa [BitVec.lt_def] using hlt
    apply WPC.seq
    refine cmp_call hb19 (ck_hput_cost sb A (by omega) o19) (by simp [evalArgs, evalE, Env.get]) rfl ?_
    intro r20 st20 c20 w20 mm20 hb20 ht20 hm20
    wpc_simp
    apply WPC.seq; apply WPC.ite_any
    · apply WPC.seq
      refine WPC.kvfree_bud hb20 (by simp [evalE, Env.get]) hfw' ?_
      intro st21 hb21
      wpc_simp
      wpc_auto
      wpc_done
    apply WPC.skip; wpc_simp
    refine WPC.assign_add_band (k := 255#32) (a := o19 + 1#32) rfl (by simp [evalE, Env.get, evalBin, evalArith]) ?_
    intro nn hnn
    have hnn' : nn.toNat ≤ 255 := by simpa using hnn
    have hoN : (o19 + 1#32 + nn).toNat = o19.toNat + 1 + nn.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    simp only [CPost.shift_apply, envU32, Env.get, String.reduceEq, ↓reduceIte, Env.set, hoN]
    refine ⟨by omega, ?_⟩
    simp only [cmpI7]
    refine ⟨_, _, _, _, rfl, by omega, hb20, ?_, ?_⟩ <;> cost_arith
  have hoc : cur3.toNat ≤ o19.toNat := by have := BitVec.le_def.mp hge; omega
  clear hge
  -- kvfree(fw); return 1;
  apply WPC.seq
  refine WPC.kvfree_bud hb19 (by simp [evalE, Env.get]) hfw' ?_
  intro st22 hb22
  wpc_simp
  wpc_auto
  wpc_done

/-- `ck_run`'s trigger: `(u64)plen > 2 lo + 2 live + flen + COMPACT_GAP`. -/
abbrev trigE : Expr :=
  .bin .gt (.cast .u64 (.field (.var "st") "plen"))
    (.bin .add (.bin .add (.bin .add (.bin .mul (.lit64 2#64) (.cast .u64 (.field (.var "st") "lo")))
      (.bin .mul (.lit64 2#64) (.cast .u64 (.field (.var "st") "live"))))
      (.cast .u64 (.field (.var "st") "flen"))) (.cast .u64 (.named "COMPACT_GAP" 65536#32)))

theorem WPC.ite_trigger {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm : BitVec 32} {a b : Stmt}
    (hb : Budget st.mem sb w mm) (htu : TypedU32 st.mem sb) (hst : env.get "st" = some (.ptr sb 0))
    (ha : ∀ L P F : BitVec 32, Fld st.mem sb 24 (.u32 L) → Fld st.mem sb 1 (.u32 P) →
      Fld st.mem sb 7 (.u32 F) → 2 * L.toNat + F.toNat + 65536 < P.toNat → WPC prog a (Q.shift 1) env st)
    (hb' : WPC prog b (Q.shift 1) env st) :
    WPC prog (.ite trigE a b) Q env st := by
  apply WPC.ite
  simp only [evalE, hst, ite_true]
  cases hP : st.mem.loadField prog sb "plen" with
  | none => simp
  | some xP =>
  obtain ⟨P, rfl, hfP⟩ := htu.load hb fi_plen hP
  cases hL : st.mem.loadField prog sb "lo" with
  | none => simp
  | some xL =>
  obtain ⟨L, rfl, hfL⟩ := htu.load hb cfi_lo hL
  cases hV : st.mem.loadField prog sb "live" with
  | none => simp
  | some xV =>
  obtain ⟨V, rfl, hfV⟩ := htu.load hb cfi_live hV
  cases hF : st.mem.loadField prog sb "flen" with
  | none => simp
  | some xF =>
  obtain ⟨F, rfl, hfF⟩ := htu.load hb fi_flen hF
  simp only [evalCast, evalBin, evalArith, Val.ofBool]
  refine ⟨fun h0 => ?_, fun _ => hb'⟩
  refine ha L P F hfL hfP hfF ?_
  split at h0
  · rename_i hlt
    simp only [decide_eq_true_eq, BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat] at hlt
    have := L.isLt; have := P.isLt; have := F.isLt; have := V.isLt
    omega
  · exact absurd rfl h0

end Vbcf.Proof
