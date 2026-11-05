import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCompact2

/-!
# Vbcf cost proofs: the top level (`ck_step`, `ck_run`, `vbcf_check`, `vbcf_check_proof`)

Facts about the kernel calls the driver makes around the checker: a fresh
struct from `kzalloc` has zero budgets (and its `u32` fields hold `u32`s,
`TypedU32.of_kzalloc`), and `ck_free` costs at most thirty transitions whatever the fields
hold (the budget is not needed afterwards, so no `FreeOk`).

The four driver lemmas take their callees' cost lemmas as hypotheses (`ck_rule` is
not proved yet; the final theorem instantiates them), so none is registered.
Lines include the statement; none is automatic.

| function           | constants                                                        | lines | how |
|--------------------|------------------------------------------------------------------|-------|-----|
| `ck_step`          | A ≥ 100, B = BR + 4000, S = `slackUnless NOID A`                 | 79    | prem loop `k.t ≤ 15·i` (`pc ≤ 255`, two reject checks); `spend`'s slack `A·(1+pc+ac) ≥ A` pays the slack; `ck_rule` by `WPC.call_shape` |
| `ck_run`           | A ≥ BStep + 40, A ≥ 6000; pre also `TypedU32`; `c.t + A·w' ≤ A·workBudget + 20000 + BL + BS + BG + BStep + 400`, `c.m + mm' ≤ memBudget + 1280` | 199 | `ck_init_cost` by hand, callees by `top_callT`, `gx` branch by `WPC.seq_join`, loop (`top_runI`) paid by the step's slack `A`; `ck_compact` under `WPC.ite_trigger` (its `CompactPre` from the trigger, the memory bound `2^30` from `ck_init`), paid by its own slack `A` |
| `vbcf_check`       | `c.t ≤ A·workBudget + BRun + 120`, `c.m ≤ memBudget + 1280 + 26` | 83    | raw `WPC.ecall` for `kzalloc` (`⟨52, 26⟩`), `Budget.of_kzalloc`, `TypedU32.of_kzalloc`, `ck_free_cost'`, `WPC.kvfree_any` |
| `vbcf_check_proof` | `c.t ≤ A·workBudget(n) + BV n + 3n + 40` (`BV` may depend on `n`), `c.m ≤ memBudget(n) + 1306 + n`, `n = size / 4` | 132 | size check kept (`size < 2^25`, so `n < 2^30`); raw `WPC.ecall` for `kvcalloc`/`copy_from_bpfptr` |

Helpers: `top_finish` (`wpc_finish` with a `split` for a slack on an unknown
return value), `top_callT` (`cmp_call` keeping `TypedU32`), `WPC.ecall_budT`,
`WPC.store_budT`, `WPC.setField_budT` (the same for kernel calls and stores),
`top_off_step` (`ck_run`'s offset step does not wrap), `top_runEnv`, `top_runI`,
`top_kzalloc`, `top_kvcalloc` (the allocators return `NULL` or a block).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000

/-- A fresh `struct ck` from `kzalloc` has both budget cells zero. -/
theorem Budget.of_kzalloc {st st' : (KernelState prog State)} {b : Nat}
    (h : Ext.run prog (.kzalloc "ck") [] st = some (some (.ptr b 0), st')) :
    Budget st'.mem b 0#32 0#32 := by
  obtain ⟨d, hd, hout⟩ := (Ext.run_spec h).kzalloc
  have hdEq : d = ckS := Option.some.inj (hd.symm.trans prog_ck)
  subst d
  rcases hout with ⟨hbad, _⟩ | ⟨hptr, hmem⟩
  · cases hbad
  · have hb : b = st.mem.blocks.size := (Val.ptr.inj (Option.some.inj hptr)).1
    subst b
    rw [hmem]
    refine ⟨⟨ckS.zeroCells, ?_, by decide⟩, ⟨ckS.zeroCells, ?_, by decide⟩⟩ <;>
      (show (st.mem.alloc (.struct "ck") ckS.zeroCells).2.block? st.mem.blocks.size = _;
       rw [Mem.block?_alloc]; simp)

/-- `kvfree` of anything costs three transitions and allocates nothing; the state afterwards
is arbitrary (the block, possibly the struct, is gone). -/
theorem WPC.kvfree_any {env : Env} {st : (KernelState prog State)} {Q : (CPost prog State)} {e : Expr}
    (h : ∀ st' : (KernelState prog State), Q .normal env st' 3) :
    WPC prog (.ecall none .kvfree [e]) Q env st := by
  apply WPC.ecall
  split
  · trivial
  rename_i vs _
  split
  · trivial
  rename_i r _
  have hc : Ext.costC prog .kvfree vs = ⟨0, 0⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]
  simp only [assignDst, hc]
  exact h _

/-- `ck_free` costs at most thirty transitions, whatever the pointer fields hold (it may free the
struct itself, in which case the run gets stuck later; the budget is not kept). -/
theorem ck_free_cost' (sb : Nat) :
    FnCost (State := State) prog "ck_free" (fun vs _ => vs = [.ptr sb 0])
      (fun _ _ _ _ c => c.t ≤ 30 ∧ c.m = 0) := by
  apply FnCost.intro (fn := ckFree) rfl
  rintro vs st rfl
  simp [ckFree, bindParams]
  split
  · trivial
  simp only [Stmt.block, initLocals, List.map]
  apply WPC.seq
  apply WPC.kvfree_any
  intro st1
  wpc_simp
  apply WPC.seq
  apply WPC.kvfree_any
  intro st2
  wpc_simp
  apply WPC.seq
  apply WPC.kvfree_any
  intro st3
  wpc_simp
  apply WPC.seq
  apply WPC.kvfree_any
  intro st4
  wpc_simp
  apply WPC.seq
  apply WPC.kvfree_any
  intro st5
  wpc_simp
  apply WPC.kvfree_any
  intro st6
  simp only [CPost.shift_apply, retPostC]
  constructor <;> simp [Cost.add_t, Cost.add_m, Cost.one_t, Cost.one_m]

open Lean in
/-- `wpc_finish` that also splits an `if` left by a slack whose value is not a literal
(`slackUnless r s (some (.u32 v))` with `v` unknown). -/
macro "top_finish" : tactic => do
  let hwk := mkIdent `hwk
  let hmk := mkIdent `hmk
  `(tactic| ((try simp only [retPostC]); (try intro _); simp only [CPost.shift_apply, Amort, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply]; refine ⟨_, _, ‹Budget _ _ _ _›, ?_, ?_⟩ <;> ((try simp only [Cost.add_t, Cost.add_m, Cost.zero_t, Cost.zero_m, Cost.one_t, Cost.one_m, Cost.mk_t, Cost.mk_m, reduceCostT, reduceCostM, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply, Option.some.injEq, Val.u32.injEq, ↓reduceIte, BitVec.reduceEq, or_false, false_or, or_true, true_or, $hwk:ident, $hmk:ident] at *); (try split) <;> ((try simp +arith only) <;> omega))))

theorem ck_step_cost (sb A BR : Nat) (hA : 100 ≤ A)
    (hRule : ∀ rule np na : BitVec 32, np.toNat ≤ 255 → na.toNat ≤ 255 → FnCost (State := State) prog "ck_rule"
      (BudPre sb [.ptr sb 0, .u32 rule, .u32 np, .u32 na]) (Amort sb A (allow BR) 0 noSlack))
    (off : BitVec 32) :
    FnCost (State := State) prog "ck_step" (BudPre sb [.ptr sb 0, .u32 off])
      (Amort sb A (allow (BR + 4000)) 0 (slackUnless 0xffffffff#32 A)) := by
  apply FnCost.intro (fn := ckStep) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body ckStep
  have hA6 : 6 ≤ A := by omega
  wpc_auto
  rename_i base hdr pc hpc ac hac
  have hpc' : pc.toNat ≤ 255 := by simpa using hpc
  have hac' : ac.toNat < 256 := by simpa using hac
  clear hpc hac
  apply WPC.while
    (I := fun env' st' k => ∃ i kk : BitVec 32,
      env' = [("st", (Ty.struct "ck").ptr, Val.ptr sb 0), ("off", Ty.u32, Val.u32 off),
        ("base", Ty.u32, Val.u32 base), ("hdr", Ty.u32, Val.u32 hdr), ("pc", Ty.u32, Val.u32 pc),
        ("ac", Ty.u32, Val.u32 ac), ("i", Ty.u32, Val.u32 i), ("k", Ty.u32, Val.u32 kk),
        ("r", Ty.u32, Val.u32 0)] ∧
      i.toNat ≤ pc.toNat ∧ Budget st'.mem sb w mm ∧ k.t ≤ 15 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => pc.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, rfl, by simp, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, kk, rfl, hip, hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hlt' : i.toNat < pc.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals loop_nextB hi1
  have hie : i.toNat = pc.toNat := by have := BitVec.le_def.mp hge; omega
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_call; cost_args
  name_bud st1 w1 mm1 hb1
  apply WPC.seq
  wpc_ite_case
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  have hk1 : (1#32 + pc + ac).toNat = 1 + pc.toNat + ac.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have hAk : A + 100 * pc.toNat ≤ A * (1#32 + pc + ac).toNat := by
    rw [hk1, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have := Nat.mul_le_mul_right pc.toNat hA
    omega
  cost_clean
  apply WPC.seq
  refine WPC.call_shape (fn := ckRule) (hf := rfl) (hps := rfl) ?_
  intro vs1 hargs _hbp
  obtain ⟨v0, vs2, h0, hargs1, rfl⟩ := evalArgs_cons' hargs
  obtain ⟨v1, vs3, h1, hargs2, rfl⟩ := evalArgs_cons' hargs1
  obtain ⟨v2, vs4, h2, hargs3, rfl⟩ := evalArgs_cons' hargs2
  obtain ⟨v3, vs5, h3, hargs4, rfl⟩ := evalArgs_cons' hargs3
  simp only [evalArgs, Option.some.injEq] at hargs4
  subst hargs4
  simp only [evalE, evalBin, evalArith, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at h0 h1 h2 h3
  subst h0 h1 h2 h3
  refine ⟨_, _, hRule _ pc ac (by omega) (by omega), ⟨rfl, _, _, hb1⟩, ?_⟩
  rintro _rv _st' _c ⟨_w', _mm', _hb', _ht, _hm⟩
  rw [Budget.wk hb1] at _ht
  rw [Budget.mk hb1] at _hm
  split
  · trivial
  rename_i env2 hasg
  obtain ⟨r2, h1, h2⟩ := assignDst_u32' hasg rfl
  subst h1
  subst h2
  wpc_simp
  cost_clean
  wpc_auto
  top_finish

/-- One step of `ck_run`'s loop: `off + 1 + pc + ac` does not wrap. -/
theorem top_off_step {off hdr : BitVec 32} (h : off.toNat < 2 ^ 31) :
    (off + 1#32 + (hdr >>> 16 &&& 255#32) + hdr >>> 24).toNat =
      off.toNat + 1 + (hdr >>> 16 &&& 255#32).toNat + (hdr >>> 24).toNat ∧
    (hdr >>> 16 &&& 255#32).toNat ≤ 255 ∧ (hdr >>> 24).toNat < 256 := by
  have ha : (hdr >>> 16 &&& 255#32).toNat ≤ 255 := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  have hb : (hdr >>> 24).toNat < 256 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := hdr.isLt
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  refine ⟨?_, ha, hb⟩
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The locals of `ck_run`. -/
def top_runEnv (sb pb : Nat) (n : BitVec 32) (gx : Val) (g ok off ns f hdr sig : BitVec 32) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("proof", Ty.u32.ptr, .ptr pb 0), ("nwords", .u32, .u32 n),
    ("gx", Ty.u32.ptr, gx), ("goal", .u32, .u32 g), ("ok", .u32, .u32 ok), ("off", .u32, .u32 off),
    ("ns", .u32, .u32 ns), ("f", .u32, .u32 f), ("hdr", .u32, .u32 hdr), ("sig", .u32, .u32 sig)]

/-- `cmp_call` (a call with an `Amort` lemma given as a term) that also keeps `TypedU32`
(every call does). -/
theorem top_callT {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {x : Var} {f : String} {args : List Expr}
    {sb A B : Nat} {S : Option Val → Nat} {vs : List Val} {w mm : BitVec 32}
    (hb : Budget st.mem sb w mm) (htu : TypedU32 st.mem sb)
    (hspec : FnCost (State := State) prog f (BudPre sb vs) (Amort sb A (allow B) 0 S))
    (hargs : evalArgs prog env st.mem args = some vs) (hx : env.ty x = some .u32)
    (h : ∀ (r : BitVec 32) (st' : (KernelState prog State)) (c : Cost) (w' mm' : BitVec 32), Budget st'.mem sb w' mm' →
      TypedU32 st'.mem sb →
      c.t + A * w'.toNat + S (some (.u32 r)) ≤ A * w.toNat + B → c.m + mm'.toNat ≤ mm.toNat →
      Q .normal (env.set x (.u32 r)) st' (c + 2)) :
    WPC prog (.call (some x) f args) Q env st := by
  apply WPC.call (FnCost.typed sb hspec)
  rw [hargs]
  refine ⟨⟨⟨rfl, _, _, hb⟩, htu⟩, ?_⟩
  rintro rv st' c ⟨⟨w', mm', hb', ht, hm⟩, htu'⟩
  rw [hb.wk] at ht
  rw [hb.mk] at hm
  split
  · trivial
  rename_i env' hasg
  obtain ⟨r, rfl, rfl⟩ := assignDst_u32' hasg hx
  exact h r st' c w' mm' hb' htu' (by simpa using ht) (by simpa using hm)

/-- A kernel call other than freeing the struct keeps the budget and `TypedU32`. -/
theorem WPC.ecall_budT {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm : BitVec 32}
    {dst : Option Var} {f : Ext} {args : List Expr} (hb : Budget st.mem sb w mm) (htu : TypedU32 st.mem sb)
    (h : ∀ vs, evalArgs Vbcf.prog env st.mem args = some vs →
      (∀ b, vs = [.ptr b 0] → f = .kvfree → b ≠ sb) ∧
      ∀ rv st', Budget st'.mem sb w mm → TypedU32 st'.mem sb →
        match assignDst env st'.mem dst rv with
        | none => True
        | some env' => Q .normal env' st' (Ext.costC Vbcf.prog f vs + 3)) :
    WPC Vbcf.prog (.ecall dst f args) Q env st := by
  apply WPC.ecall
  cases hv : evalArgs Vbcf.prog env st.mem args with
  | none => trivial
  | some vs =>
    obtain ⟨hfree, h⟩ := h vs hv
    simp only []
    cases hr : Ext.run Vbcf.prog f vs st with
    | none => trivial
    | some r =>
      obtain ⟨rv, st'⟩ := r
      exact h rv st' (hb.ext hr hfree) (htu.ext hr)

theorem WPC.store_budT {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm : BitVec 32} {p j e : Expr}
    (hb : Budget st.mem sb w mm) (htu : TypedU32 st.mem sb)
    (h : ∀ m', Budget m' sb w mm → TypedU32 m' sb → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.store p j e) Q env st := by
  apply WPC.store
  split
  · split
    · trivial
    · split
      · trivial
      · rename_i m' hs; exact h m' (hb.storeArr hs) (htu.storeArr hs)
  · trivial

theorem WPC.setField_budT {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm : BitVec 32} {p e : Expr}
    {f : String} (hb : Budget st.mem sb w mm) (htu : TypedU32 st.mem sb) (h1 : f ≠ "work") (h2 : f ≠ "mem")
    (h : ∀ m', Budget m' sb w mm → TypedU32 m' sb → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.setField p f e) Q env st := by
  apply WPC.setField
  split
  · intro _
    split
    · trivial
    · rename_i m' hs; exact h m' (hb.storeField hs h1 h2) (htu.storeField hs)
  · trivial

/-- The invariant of `ck_run`'s loop (a named definition, so that `simp` leaves it alone). -/
def top_runI (sb A pb : Nat) (n : BitVec 32) (gx : Val) (g ns w4 : BitVec 32) (mm4 : Nat) :
    Env → (KernelState prog State) → Cost → Prop := fun env' st' k =>
  ∃ ok off f hdr sig : BitVec 32,
    env' = top_runEnv sb pb n gx g ok off ns f hdr sig ∧ off.toNat ≤ ns.toNat + 512 ∧
    ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧ TypedU32 st'.mem sb ∧
      k.t + A * w'.toNat ≤ A * w4.toNat ∧ k.m + mm'.toNat ≤ mm4

theorem ck_run_cost (sb A BL BS BG BStep : Nat) (hA : BStep + 40 ≤ A) (hA6000 : 6000 ≤ A) (pb gb : Nat)
    (n g : BitVec 32) (hn : n.toNat < 2 ^ 30)
    (hL : FnCost (State := State) prog "ck_load" (BudPre sb [.ptr sb 0, .ptr pb 0, .u32 n]) (Amort sb A (allow BL) 0 noSlack))
    (hS : FnCost (State := State) prog "ck_scan" (BudPre sb [.ptr sb 0]) (Amort sb A (allow BS) 0 noSlack))
    (hG : FnCost (State := State) prog "ck_goal" (BudPre sb [.ptr sb 0, .ptr gb 0, .u32 g]) (Amort sb A (allow BG) 0 noSlack))
    (hStep : ∀ off : BitVec 32, FnCost (State := State) prog "ck_step" (BudPre sb [.ptr sb 0, .u32 off])
      (Amort sb A (allow BStep) 0 (slackUnless 0xffffffff#32 A)))
    (gx : Val) (hgx : gx = .null ∨ gx = .ptr gb 0) :
    FnCost (State := State) prog "ck_run"
      (fun vs st => vs = [.ptr sb 0, .ptr pb 0, .u32 n, gx, .u32 g] ∧ Budget st.mem sb 0#32 0#32 ∧
        TypedU32 st.mem sb)
      (fun _ _ _ st' c => ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        c.t + A * w'.toNat ≤ A * workBudget n g + (20000 + BL + BS + BG + BStep + 400) ∧
        c.m + mm'.toNat ≤ memBudget n g + 1280) := by
  have hA100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := ckRun) rfl
  rintro vs st ⟨rfl, hb, htu⟩
  fncost_body ckRun
  by_cases hpf : st.mem.hasTy (.ptr pb 0) (.ptr .u32) = true
  rotate_left
  · simp [hpf]
  by_cases hgt : st.mem.hasTy gx (.ptr .u32) = true
  rotate_left
  · simp [hgt]
  simp only [hpf, hgt, ↓reduceIte, List.cons_append, List.nil_append]
  clear hpf hgt
  -- ok = ck_init(st, nwords, goal); if (ok == 0) return 0;
  apply WPC.seq
  apply WPC.call (FnCost.typed sb (ck_init_cost sb A hA100 n g))
  simp only [evalArgs, evalE, Env.get, String.reduceEq, ↓reduceIte]
  refine ⟨⟨⟨trivial, hb⟩, htu⟩, ?_⟩
  rintro rv st1 c1 ⟨⟨w1, mm1, hb1, ht1, hm1, hmm1⟩, htu1⟩
  split
  · trivial
  rename_i env1 hasg
  obtain ⟨ok1, rfl, rfl⟩ := assignDst_u32' hasg rfl
  wpc_simp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; init_finish
  apply WPC.skip; wpc_simp
  -- ok = ck_load(st, proof, nwords); if (ok == 0) return 0;
  apply WPC.seq
  refine top_callT hb1 htu1 hL (by simp [evalArgs, evalE, Env.get]) rfl ?_
  intro ok2 st2 c2 w2 mm2 hb2 htu2 ht2 hm2
  wpc_simp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; init_finish
  apply WPC.skip; wpc_simp
  -- ok = ck_scan(st); if (ok == 0) return 0;
  apply WPC.seq
  refine top_callT hb2 htu2 hS (by simp [evalArgs, evalE, Env.get]) rfl ?_
  intro ok3 st3 c3 w3 mm3 hb3 htu3 ht3 hm3
  wpc_simp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; init_finish
  apply WPC.skip; wpc_simp
  clear hasg
  simp only [noSlack_apply, Nat.add_zero] at ht2 ht3
  -- if (gx != NULL) { ok = ck_goal(st, gx, goal); if (ok == 0) return 0; }
  apply WPC.seq_join (J := fun env' st' k => ∃ ok' : BitVec 32, env' = top_runEnv sb pb n gx g ok' 0 0 0 0 0 ∧
    ∃ w4 mm4 : BitVec 32, Budget st'.mem sb w4 mm4 ∧ TypedU32 st'.mem sb ∧
      k.t + A * w4.toNat ≤ A * w3.toNat + BG + 10 ∧ k.m + mm4.toNat ≤ mm3.toNat)
  · rcases hgx with rfl | rfl
    · apply WPC.ite
      embc_simp
      apply WPC.skip
      simp only [CPost.shift_apply]
      exact ⟨⟨ok3, rfl⟩, w3, mm3, hb3, htu3, by cost_arith, by cost_arith⟩
    apply WPC.ite_any
    · apply WPC.seq
      refine top_callT hb3 htu3 hG (by simp [evalArgs, evalE, Env.get]) rfl ?_
      intro ok4 st4 c4 w4 mm4 hb4 htu4 ht4 hm4
      wpc_simp
      simp only [noSlack_apply, Nat.add_zero] at ht4
      apply WPC.ite_any
      · wpc_auto; init_finish
      apply WPC.skip
      exact ⟨ok4, rfl, w4, mm4, hb4, htu4, by cost_arith, by cost_arith⟩
    apply WPC.skip
    exact ⟨ok3, rfl, w3, mm3, hb3, htu3, by cost_arith, by cost_arith⟩
  rintro env' st4 k4 ⟨ok4, rfl, w4, mm4, hb4, htu4, ht4, hm4⟩
  simp only [top_runEnv]
  have hmm4 : mm4.toNat ≤ 2 ^ 30 := by omega
  -- ns = proof[2]; if (ns >= nwords) return 0;
  apply WPC.seq; refine WPC.assign_u32 rfl ?_; intro ns; wpc_simp
  apply WPC.seq; apply WPC.ite; embc_simp
  refine ⟨fun _ => ?_, fun hns => ?_⟩
  · wpc_auto; init_finish
  apply WPC.skip; wpc_simp
  have hns' : ns.toNat < n.toNat := BitVec.lt_def.mp hns
  clear hns
  -- the replay loop: each iteration paid by the step's slack
  apply WPC.seq
  apply WPC.while (I := top_runI sb A pb n gx g ns w4 mm4.toNat)
    (μ := fun env' _ => ns.toNat - envU32 env' "off")
  · exact ⟨ok4, 0#32, 0#32, 0#32, 0#32, rfl, by simp, w4, mm4, hb4, htu4, by simp, by simp⟩
  rintro env' st' k ⟨ok, off, f, hdr, sig, rfl, hoff, w', mm', hb', htu', hk, hkm⟩
  simp only [top_runEnv]
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    all_goals init_finish
  have hlt' : off.toNat < ns.toNat := by simpa [BitVec.lt_def] using hlt
  clear hlt
  -- cond_resched();
  apply WPC.seq
  apply WPC.ecall_budT hb' htu'
  intro vs hvs
  simp [evalArgs] at hvs
  subst hvs
  refine ⟨by simp, ?_⟩
  intro rv st5 hb5 htu5
  have hc0 : Ext.costC prog .condResched [] = ⟨0, 0⟩ := by simp [Ext.costC, Ext.cost, Ext.words]
  rw [hc0]
  simp only [assignDst_none]
  wpc_simp
  -- sig = signal_pending();
  apply WPC.seq
  apply WPC.ecall_budT hb5 htu5
  intro vs hvs
  simp [evalArgs] at hvs
  subst hvs
  refine ⟨by simp, ?_⟩
  intro rv st6 hb6 htu6
  have hc1 : Ext.costC prog .signalPending [] = ⟨0, 0⟩ := by simp [Ext.costC, Ext.cost, Ext.words]
  rw [hc1]
  split
  · trivial
  rename_i env6 hasg
  obtain ⟨sig', rfl, rfl⟩ := assignDst_u32' hasg rfl
  wpc_simp
  clear hasg
  -- if (sig != 0) { st->err = ERR_INTR; return 0; }
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; init_finish
  apply WPC.skip; wpc_simp
  -- f = ck_step(st, off); if (f == NOID) return 0;
  apply WPC.seq
  refine top_callT hb6 htu6 (hStep off) (by simp [evalArgs, evalE, Env.get]) rfl ?_
  intro f' st7 c7 w7 mm7 hb7 htu7 ht7 hm7
  wpc_simp
  apply WPC.seq
  wpc_ite_case
  · wpc_auto; init_finish
  apply WPC.skip; wpc_simp
  -- st->facts[st->flen] = f; st->flen = st->flen + 1; hdr = proof[...];
  apply WPC.seq; apply WPC.store_budT hb7 htu7; intro m8 hb8 htu8; wpc_simp
  apply WPC.seq; apply WPC.setField_budT hb8 htu8 (by decide) (by decide); intro m9 hb9 htu9; wpc_simp
  apply WPC.seq; refine WPC.assign_u32 rfl ?_; intro hdr'; wpc_simp
  -- off = off + 1 + ((hdr >> 16) & 0xff) + (hdr >> 24);
  apply WPC.seq
  apply WPC.assign
  simp only [evalE, evalBin, evalArith, Env.get, String.reduceEq, ↓reduceIte, BitVec.toNat_ofNat,
    Nat.reduceMod, Nat.reduceLT, Nat.reducePow]
  obtain ⟨hs1, hs2, hs3⟩ := top_off_step (off := off) (hdr := hdr') (by omega)
  generalize off + 1#32 + (hdr' >>> 16 &&& 255#32) + hdr' >>> 24 = off' at hs1 ⊢
  simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u32, Env.set]
  have hmm9 : mm7.toNat ≤ 2 ^ 30 := by omega
  -- if (off < ns) { if (trigger) { ok = ck_compact(st); if (ok == 0) return 0; } }
  apply WPC.ite_any
  rotate_left
  · apply WPC.skip
    simp only [CPost.shift_apply, envU32, Env.get, String.reduceEq, ↓reduceIte]
    refine ⟨by omega, ?_⟩; simp only [top_runI]
    refine ⟨ok, off', f', hdr', sig', rfl, by omega, w7, mm7, hb9, htu9, ?_, ?_⟩ <;> cost_arith
  refine WPC.ite_trigger hb9 htu9 (by simp [Env.get]) ?_ ?_
  rotate_left
  · apply WPC.skip
    simp only [CPost.shift_apply, envU32, Env.get, String.reduceEq, ↓reduceIte]
    refine ⟨by omega, ?_⟩; simp only [top_runI]
    refine ⟨ok, off', f', hdr', sig', rfl, by omega, w7, mm7, hb9, htu9, ?_, ?_⟩ <;> cost_arith
  intro L P F hfL hfP hfF hrel
  apply WPC.seq
  apply WPC.call (FnCost.typed sb (ck_compact_cost sb A hA6000 L P F))
  simp only [evalArgs, evalE, Env.get, ↓reduceIte]
  refine ⟨⟨⟨rfl, hfL, hfP, hfF, hrel, w7, mm7, hb9, hmm9⟩, htu9⟩, ?_⟩
  rintro rv st10 c10 ⟨⟨w10, mm10, hb10, ht10, hm10⟩, htu10⟩
  rw [hb9.wk] at ht10
  rw [hb9.mk] at hm10
  split
  · trivial
  rename_i env10 hasg
  obtain ⟨r10, rfl, rfl⟩ := assignDst_u32' hasg rfl
  wpc_simp
  clear hasg
  apply WPC.ite; embc_simp
  by_cases hr10 : r10 = 0#32
  · subst hr10
    simp only [slackUnless_apply, allow_apply, ↓reduceIte, Nat.add_zero] at ht10
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    wpc_auto
    init_finish
  simp only [slackUnless_apply, allow_apply, Option.some.injEq, Val.u32.injEq, hr10, ↓reduceIte] at ht10
  refine ⟨fun h => absurd h hr10, fun _ => ?_⟩
  apply WPC.skip
  simp only [CPost.shift_apply, envU32, Env.get, String.reduceEq, ↓reduceIte]
  refine ⟨by omega, ?_⟩; simp only [top_runI]
  refine ⟨r10, off', f', hdr', sig', rfl, by omega, w10, mm10, hb10, htu10, ?_, ?_⟩ <;> cost_arith

/-- What `kzalloc` returns: `NULL` or a fresh block. -/
theorem top_kzalloc {st st' : (KernelState prog State)} {rv : Option Val}
    (h : Ext.run prog (.kzalloc "ck") [] st = some (rv, st')) :
    rv = some .null ∨ ∃ b, rv = some (.ptr b 0) := by
  obtain ⟨_, _, hout⟩ := (Ext.run_spec h).kzalloc
  rcases hout with ⟨hnull, _⟩ | ⟨hptr, _⟩
  · exact Or.inl hnull
  · exact Or.inr ⟨_, hptr⟩

theorem vbcf_check_cost (A BRun : Nat) (pb gb : Nat) (n g : BitVec 32)
    (_hn : n.toNat < 2 ^ 30) (gx : Val) (_hgx : gx = .null ∨ gx = .ptr gb 0)
    (hRun : ∀ sb, FnCost (State := State) prog "ck_run" (fun vs st => vs = [.ptr sb 0, .ptr pb 0, .u32 n, gx, .u32 g] ∧
      Budget st.mem sb 0#32 0#32 ∧ TypedU32 st.mem sb) (fun _ _ _ st' c => ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * workBudget n g + BRun ∧ c.m + mm'.toNat ≤ memBudget n g + 1280)) :
    FnCost (State := State) prog "vbcf_check" (fun vs _ => vs = [gx, .u32 g, .ptr pb 0, .u32 n])
      (fun _ _ _ _ c => c.t ≤ A * workBudget n g + (BRun + 120) ∧ c.m ≤ memBudget n g + 1306) := by
  apply FnCost.intro (fn := vbcfCheck) rfl
  rintro vs st rfl
  simp [vbcfCheck, bindParams]
  by_cases hgt : st.mem.hasTy gx (.ptr .u32) = true
  rotate_left
  · simp [hgt]
  by_cases hpf : st.mem.hasTy (.ptr pb 0) (.ptr .u32) = true
  rotate_left
  · simp [hpf]
  simp only [hpf, hgt, ↓reduceIte, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]
  clear hpf hgt
  -- st = kzalloc(sizeof(struct ck)); if (st == NULL) return E_NOMEM;
  apply WPC.seq
  apply WPC.ecall
  simp only [evalArgs]
  split
  · trivial
  rename_i rv st1 hrun
  have hcost : Ext.costC prog (.kzalloc "ck") [] = ⟨52, 26⟩ := by
    simp only [Ext.costC, Ext.cost, Ext.words, prog_ck]; rfl
  rw [hcost]
  rcases top_kzalloc hrun with rfl | ⟨b, rfl⟩
  · simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
    by_cases hty : st1.mem.hasTy Val.null (Ty.struct "ck").ptr = true
    rotate_left
    · simp [hty]
    simp only [hty, ↓reduceIte]
    wpc_simp
    apply WPC.seq; apply WPC.ite; embc_simp
    wpc_auto
    simp only [retPostC]
    intro _
    cost_simp
    omega
  have hb1 := Budget.of_kzalloc hrun
  have htu1 := TypedU32.of_kzalloc hrun
  simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
  by_cases hty : st1.mem.hasTy (Val.ptr b 0) (Ty.struct "ck").ptr = true
  rotate_left
  · simp [hty]
  simp only [hty, ↓reduceIte]
  wpc_simp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto
    simp only [retPostC]
    intro _
    cost_simp
    omega
  apply WPC.skip; wpc_simp
  -- ok = ck_run(st, proof, nwords, goal_exprs, goal); err = st->err;
  apply WPC.seq
  apply WPC.call (hRun b)
  simp only [evalArgs, evalE, Env.get, String.reduceEq, ↓reduceIte]
  refine ⟨⟨by first | rfl | trivial, hb1, htu1⟩, ?_⟩
  rintro rv st2 c2 ⟨w2, mm2, hb2, ht2, hm2⟩
  split
  · trivial
  rename_i env2 hasg
  obtain ⟨ok, rfl, rfl⟩ := assignDst_u32' hasg rfl
  wpc_simp
  clear hasg
  apply WPC.seq; refine WPC.assign_u32 rfl ?_; intro err; wpc_simp
  -- ck_free(st); kvfree(st);
  apply WPC.seq
  apply WPC.call (ck_free_cost' b)
  simp only [evalArgs, evalE, Env.get, String.reduceEq, ↓reduceIte]
  refine ⟨by first | rfl | trivial, ?_⟩
  rintro rv st3 c3 ⟨ht3, hm3⟩
  simp only [assignDst_none]
  wpc_simp
  apply WPC.seq
  apply WPC.kvfree_any
  intro st4
  wpc_simp
  wpc_auto
  all_goals (simp only [retPostC]; intro _; cost_simp; omega)

/-- What `kvcalloc` of `u32` words returns: `NULL` or a fresh block. -/
theorem top_kvcalloc {st st' : (KernelState prog State)} {rv : Option Val} {x : BitVec 64}
    (h : Ext.run prog (.kvcalloc .u32) [.u64 x] st = some (rv, st')) :
    rv = some .null ∨ ∃ b, rv = some (.ptr b 0) := by
  rcases (Ext.run_spec h).kvcalloc with ⟨hnull, _⟩ | ⟨hptr, _⟩
  · exact Or.inl hnull
  · exact Or.inr ⟨_, hptr⟩

theorem vbcf_check_proof_cost (A : Nat) (BV : BitVec 32 → Nat) (gb : Nat) (g size : BitVec 32) (gx : Val)
    (_hgx : gx = .null ∨ gx = .ptr gb 0)
    (hV : ∀ (pb : Nat) (n : BitVec 32), n.toNat < 2 ^ 30 → FnCost (State := State) prog "vbcf_check"
      (fun vs _ => vs = [gx, .u32 g, .ptr pb 0, .u32 n])
      (fun _ _ _ _ c => c.t ≤ A * workBudget n g + BV n ∧ c.m ≤ memBudget n g + 1306)) :
    FnCost (State := State) prog "vbcf_check_proof" (fun vs _ => vs = [gx, .u32 g, .uptr, .u32 size])
      (fun _ _ _ _ c => c.t ≤ A * workBudget (size / 4#32) g + BV (size / 4#32) + 3 * (size / 4#32).toNat + 40 ∧
        c.m ≤ memBudget (size / 4#32) g + 1306 + (size / 4#32).toNat) := by
  apply FnCost.intro (fn := vbcfCheckProof) rfl
  rintro vs st rfl
  simp [vbcfCheckProof, bindParams]
  by_cases hgt : st.mem.hasTy gx (.ptr .u32) = true
  rotate_left
  · simp [hgt]
  simp only [hgt, ↓reduceIte, Stmt.block, initLocals, List.map, Ty.zero]
  clear hgt
  apply WPC.seq; apply WPC.ite; embc_simp
  split
  rotate_left
  · trivial
  rename_i v heq
  refine ⟨fun _ => ?_, fun hv0 => ?_⟩
  · wpc_auto
    simp only [retPostC]
    intro _
    cost_simp
    omega
  have hsz : size.toNat < 33554432 := by
    subst hv0
    by_cases hbig : 33554432#32 ≤ size
    · exfalso
      revert heq
      split <;> simp [hbig]
    · simp only [BitVec.le_def] at hbig
      simpa using hbig
  clear heq hv0
  apply WPC.skip; wpc_simp
  have hnw : (size / 4#32).toNat < 2 ^ 30 := by
    rw [BitVec.toNat_udiv]; simp; omega
  -- nwords = proof_size / 4;
  apply WPC.seq
  apply WPC.assign
  simp only [evalE, evalBin, evalArith, Env.get, String.reduceEq, ↓reduceIte, BitVec.reduceEq,
    Env.assign, Env.ty, Mem.hasTy_u32]
  wpc_simp
  rw [show size.toNat / 4 = (size / 4#32).toNat by simp]
  generalize size / 4#32 = nw at hnw ⊢
  -- buf = kvcalloc((u64)nwords, sizeof(u32)); if (buf == NULL) return E_NOMEM;
  apply WPC.seq
  apply WPC.ecall
  simp only [evalArgs, evalE, evalCast, Env.get, String.reduceEq, ↓reduceIte]
  split
  · trivial
  rename_i rv st1 hrun
  have hcost : Ext.costC prog (.kvcalloc .u32) [.u64 (nw.setWidth 64)] = ⟨2 * nw.toNat, nw.toNat⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]; have := nw.isLt; omega
  rw [hcost]
  rcases top_kvcalloc hrun with rfl | ⟨b, rfl⟩
  · simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
    by_cases hty : st1.mem.hasTy Val.null Ty.u32.ptr = true
    rotate_left
    · simp [hty]
    simp only [hty, ↓reduceIte]
    wpc_simp
    apply WPC.seq; apply WPC.ite; embc_simp
    wpc_auto
    simp only [retPostC]
    intro _
    cost_simp
    omega
  simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
  by_cases hty : st1.mem.hasTy (Val.ptr b 0) Ty.u32.ptr = true
  rotate_left
  · simp [hty]
  simp only [hty, ↓reduceIte]
  wpc_simp
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto
    simp only [retPostC]
    intro _
    cost_simp
    omega
  apply WPC.skip; wpc_simp
  -- r = copy_from_bpfptr(buf, proof, (u64)nwords); if (r != 0) { kvfree(buf); return E_FAULT; }
  apply WPC.seq
  apply WPC.ecall
  simp only [evalArgs, evalE, evalCast, Env.get, String.reduceEq, ↓reduceIte]
  split
  · trivial
  rename_i rv st2 hrun2
  have hcost2 : Ext.costC prog .copyFromBpfptr [.ptr b 0, .uptr, .u64 (nw.setWidth 64)] = ⟨nw.toNat, 0⟩ := by
    simp [Ext.costC, Ext.cost, Ext.words]; have := nw.isLt; omega
  rw [hcost2]
  split
  · trivial
  rename_i env2 hasg
  obtain ⟨r, rfl, rfl⟩ := assignDst_u32' hasg rfl
  wpc_simp
  clear hasg
  apply WPC.seq; apply WPC.ite_any
  · apply WPC.seq
    apply WPC.kvfree_any
    intro st3
    wpc_simp
    wpc_auto
    simp only [retPostC]
    intro _
    cost_simp
    omega
  apply WPC.skip; wpc_simp
  -- r = vbcf_check(goal_exprs, goal, buf, nwords); kvfree(buf); return r;
  apply WPC.seq
  apply WPC.call (hV b nw hnw)
  simp only [evalArgs, evalE, Env.get, String.reduceEq, ↓reduceIte]
  refine ⟨by first | rfl | trivial, ?_⟩
  rintro rv st3 c3 ⟨ht3, hm3⟩
  split
  · trivial
  rename_i env3 hasg
  obtain ⟨r3, rfl, rfl⟩ := assignDst_u32' hasg rfl
  wpc_simp
  clear hasg
  apply WPC.seq
  apply WPC.kvfree_any
  intro st4
  wpc_simp
  wpc_auto
  simp only [retPostC]
  intro _
  cost_simp
  omega

end Vbcf.Proof
