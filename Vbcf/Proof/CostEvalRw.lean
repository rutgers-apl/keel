import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostMid
import Vbcf.Proof.CostBool2
import Vbcf.Proof.CostAci
import Vbcf.Proof.Rewrite8

/-!
# Vbcf cost proofs: constant evaluation (`cval`, `EVALUATE`) and the rewrite engine

Per function `(A ≥, B, S)`, lines of proof, `auto` when `fncost_body; wpc_auto; wpc_done`
did it alone.  All have `Bm = 0`.

* `cval` (2000, 100, `slackUnless NOID 200`; 75 + helpers): recursive (`FnCost.rec` on the
  depth, as `aci_absorb`).  Every entry ticks; the tick pays for the node's own work and each
  recursive call that returns neither 0 nor `NOID` hands back 200, which pays for its caller's
  loop iteration (`BV_ADD`... loop) or its allowance.  **The rate has to be large:** the
  `BV_REPEAT` case runs a loop of up to 255 iterations (`hi ≤ 255`) between two ticks.
  Its six transitions per iteration must be covered by the rate as well as the node's
  remaining transitions; a constant allowance cannot cover repeated `REPEAT` nodes.  The 4 copies
  of the body made by `wpc_auto` (`w == TY_BOOL`, `w <= 64`, and the `acc` initialisations) are
  handled uniformly: the recursive calls by `rw_cv_call`, the loops by invariants over the whole
  environment (`rwCvEnv`).
* `r_evaluate` (2000, 17500, noSlack; 6, auto).
* `rw_zero` (–, 18000, noSlack; 5, auto).
* `rw_const` (2000, 120, noSlack; 5, auto).
* `rw_ext` (2000, 8800, noSlack; 6, auto), `rw_extract` (2000, 9000; 6, auto),
  `rw_max` (2000, 8800; 6, auto), `rw_sym` (2000, 9000; 6, auto).
* `rw_inst` (2000, `20000 · |encE e| - 200`, noSlack; 280 + helpers): recursive on the depth,
  for a pattern `e` of the table (`RwAt pos (encE e)`, `wfE e`, the facts of the correctness
  proof): the cost is linear in the size of the pattern.  Its precondition is not `BudPre`
  (it needs the pattern), so `rw_inst_cost` takes `e` and the two table facts; it is
  registered, but every call is made by hand (`rw_inst_call`, `rw_inst_rec`).  Without the
  table facts the `RW_APP` loop need not end (`p` advances by a table word).
* `rw_cond_one` (2000, 150, noSlack; 5, auto): one `rw_cond_match` or one `cval`.
* `rw_check_cond` (2000, 180·255+40, noSlack; 30): a counted loop over `n ≤ 255` conjuncts
  (a mask), each an `rw_cond_one` call.
* `r_rewrite` (2000, 1600000, noSlack; 200): the patterns of a rule are at most 71 words in
  all (`rw_tbl_len_all`, by `decide`), so the three `rw_inst` calls cost at most
  `20000 · 71`; the `push` loop is paid by `push`'s slack and also saves 100 per argument for
  `rw_params` (`60 · n + 30`).  The `if (c == 0)` block is joined (`rw_seq_join`).

Helpers (prefixed `rw_`): `rw_cv_finish`/`rw_cv_done` (`wpc_finish` that also splits an `if`
in the slack), `rw_cv_call`, `rw_cv_next`, `rw_assign_shr_var`, `rwCvEnv`, `rwLen`,
`rw_len_eq`, `rw_eval_tbl`, `rw_assign_tbl`, `rw_assign_tbl_e`, `rw_assign_add1`,
`rw_assign_next`, `rw_while`, `rw_seq_join`, `rw_tag_skip`, `rw_tag_take`, `rw_inst_rec`,
`rw_child`, `rw_inst_call`, `rw_tbl_len_all`, `rw_tbl_len`, `rw_encOpt_some`/`none`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC
open Vbcf.RwEnc

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

/-! ## Helpers -/

theorem rw_cv_dec {d : BitVec 32} (hd : ¬ d = 0#32) : (d - 1#32).toNat < d.toNat := by
  rw [bv_sub_one_toNat hd]
  have : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
  omega

open Lean in
/-- `wpc_finish`, which also splits an `if` left in the goal (a slack `slackUnless r s` of a
returned value that is not a literal). -/
macro "rw_cv_finish" : tactic => do
  let hwk := mkIdent `hwk
  let hmk := mkIdent `hmk
  `(tactic| ((try simp only [retPostC]); (try intro _); simp only [CPost.shift_apply, Amort, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply]; refine ⟨_, _, ‹Budget _ _ _ _›, ?_, ?_⟩ <;> ((try simp only [Cost.add_t, Cost.add_m, Cost.zero_t, Cost.zero_m, Cost.one_t, Cost.one_m, Cost.mk_t, Cost.mk_m, reduceCostT, reduceCostM, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply, Option.some.injEq, Val.u32.injEq, ↓reduceIte, BitVec.reduceEq, or_false, false_or, or_true, true_or, $hwk:ident, $hmk:ident] at *); ((try simp +arith only) <;> (try split) <;> omega))))

/-- `rw_cv_finish` on every open goal it can close, after `cost_clean`. -/
macro "rw_cv_done" : tactic => `(tactic| all_goals (try (cost_clean; rw_cv_finish)))

/-! ## `cval` -/

/-- `cval`'s arguments; the node may be any word. -/
def rwCvArgs (sb : Nat) (vs : List Val) : Prop :=
  ∃ (id d : BitVec 32), vs = [.ptr sb 0, .u32 id, .u32 d]

/-- The measure of the recursion: the depth argument. -/
def rwCvDepth : List Val → Nat
  | [_, _, .u32 d] => d.toNat
  | _ => 0

open Lean in
/-- A recursive call `cw = cval(st, st->pool[...], depth - 1)` (by the induction hypothesis
`IH`), then `if (cw == 0 || cw == NOID) return cw;`: a call that returned `NOID` has no slack and
returns at once; otherwise its slack (200) is known in the rest. -/
macro "rw_cv_call" : tactic => do
  let IH := mkIdent `IH
  let hd := mkIdent `hd
  `(tactic| (
    have _hbc := ‹Budget _ _ _ _›
    refine WPC.call_shape (fn := cval) (hf := rfl) (hps := rfl) ?_
    intro _vs _hargs _hbp
    obtain ⟨_v0, _vs0, _h0, _hargs0, _e0⟩ := evalArgs_cons' _hargs
    subst _e0
    simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at _h0
    subst _h0
    obtain ⟨_v1, _vs1, -, _hargs1, _e1⟩ := evalArgs_cons' _hargs0
    subst _e1
    obtain ⟨_v2, _vs2, _h2, _hargs2, _e2⟩ := evalArgs_cons' _hargs1
    subst _e2
    simp only [evalArgs, Option.some.injEq] at _hargs2
    subst _hargs2
    simp only [evalE, evalBin, evalArith, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at _h2
    subst _h2
    obtain ⟨_, _, _e3, -, _hbp1⟩ := bindParams_ne_none_cons _hbp
    simp only [List.cons.injEq] at _e3
    obtain ⟨_e3a, _e3b⟩ := _e3
    subst _e3b
    obtain ⟨_, _, _e4, _ht4, _hbp2⟩ := bindParams_ne_none_cons _hbp1
    simp only [List.cons.injEq] at _e4
    obtain ⟨_e4a, _e4b⟩ := _e4
    subst _e4a
    subst _e4b
    obtain ⟨_x, _ex⟩ := Mem.hasTy_u32_inv _ht4
    subst _ex
    refine ⟨_, _, $IH, ⟨⟨⟨_x, _, rfl⟩, _, _, _hbc⟩, by simp only [rwCvDepth]; have := rw_cv_dec $hd; omega⟩, ?_⟩
    rintro _rv _st' _c ⟨_w', _mm', _hb', _ht, _hm⟩
    rw [Budget.wk _hbc] at _ht
    rw [Budget.mk _hbc] at _hm
    split
    · trivial
    rename_i _env' _hasg
    obtain ⟨_r, _h1, _h2⟩ := assignDst_u32' _hasg rfl
    subst _h1
    subst _h2
    wpc_simp
    apply WPC.seq
    by_cases _hN : _r = 4294967295#32
    · subst _hN
      apply WPC.ite
      embc_simp
      wpc_auto
      rw_cv_done
    simp only [slackUnless_apply, Option.some.injEq, Val.u32.injEq, _hN, ↓reduceIte] at _ht
    apply WPC.ite_any
    · wpc_auto
      rw_cv_done
    apply WPC.skip
    wpc_simp))

/-- `x = y >> k` for a local `y`: the value is `y / 2^k`. -/
theorem rw_assign_shr_var {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x y : Var}
    {p k : BitVec 32} (hx : env.ty x = some .u32) (hy : env.get y = some (.u32 p))
    (h : ∀ n : BitVec 32, n.toNat = p.toNat / 2 ^ k.toNat → Q .normal (env.set x (.u32 n)) st 1) :
    WPC P (.assign x (.bin .shr (.var y) (.lit32 k))) Q env st := by
  apply WPC.assign
  simp only [evalE, hy]
  by_cases hk : k.toNat < 32
  · simp only [evalBin, evalArith, hk, ↓reduceIte, Env.assign, hx, Mem.hasTy_u32]
    exact h _ (by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow])
  · simp [evalBin, evalArith, hk]

/-- The locals of `cval`. -/
def rwCvEnv (sb : Nat) (id d hdr code n par lo hi w cw i : BitVec 32) (x y z m sbv acc : BitVec 64) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, .u32 id), ("depth", .u32, .u32 d),
    ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 code), ("n", .u32, .u32 n), ("par", .u32, .u32 par),
    ("lo", .u32, .u32 lo), ("hi", .u32, .u32 hi), ("w", .u32, .u32 w), ("cw", .u32, .u32 cw),
    ("i", .u32, .u32 i), ("x", .u64, .u64 x), ("y", .u64, .u64 y), ("z", .u64, .u64 z),
    ("m", .u64, .u64 m), ("sb", .u64, .u64 sbv), ("acc", .u64, .u64 acc)]

/-- The next-iteration goal of a loop of `cval` (`h : (i + 1#32).toNat = i.toNat + 1`). -/
macro "rw_cv_next" h:ident : tactic => `(tactic| ((try simp only [allow_apply, noSlack_apply,
  allowFail_apply, slackUnless_apply, slackOr_apply] at *); simp only [rwCvEnv, envU32, Env.get, String.reduceEq,
  ↓reduceIte, List.cons.injEq, Prod.mk.injEq, Val.u32.injEq, Val.u64.injEq, and_assoc, true_and, and_true,
  exists_eq', exists_eq_left, exists_and_left, exists_and_right, exists_const, exists_eq_left', Cost.add_t,
  Cost.add_m, reduceCostT, reduceCostM, $h:ident]; (repeat' (first | (refine ⟨_, _, ‹Budget _ _ _ _›, ?_⟩) | apply And.intro)); all_goals (first | assumption | rfl | omega | (simp +arith only at *; omega))))

set_option maxHeartbeats 4000000 in
/-- `cval` for any arguments (the 4 copies of its body need more than the default heartbeats). -/
theorem cval_cost_gen (sb A : Nat) (hA : 2000 ≤ A) :
    FnCost (State := State) prog "cval" (fun vs st => rwCvArgs sb vs ∧ ∃ w mm : BitVec 32, Budget st.mem sb w mm)
      (Amort sb A (allow 100) 0 (slackUnless 4294967295#32 200)) := by
  apply FnCost.rec (fun vs _ => rwCvDepth vs)
  intro m IH
  apply FnCost.intro (fn := cval) rfl
  rintro vs st ⟨⟨⟨id, d, rfl⟩, w, mm, hb⟩, hm⟩
  simp only [rwCvDepth] at hm
  have hA6 : 6 ≤ A := by omega
  fncost_body cval
  -- if (depth == 0) return NOID;
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro hd; wpc_auto; wpc_done
  intro hd; apply WPC.skip; wpc_simp
  -- cw = tick(st); if (cw == 0) return NOID;
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_ite_case
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  -- the header: `hi` is a byte
  apply WPC.seq; refine WPC.assign_u32 (by rfl) ?_; intro hdrv; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; refine rw_assign_shr_var (by rfl) (by rfl) ?_; intro parv hpar; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; refine rw_assign_shr_var (by rfl) (by rfl) ?_; intro hiv hhi; wpc_simp
  have hhi255 : hiv.toNat ≤ 255 := by
    have := hdrv.isLt
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hpar hhi
    omega
  clear hpar hhi
  wpc_auto
  rw_cv_done
  repeat (any_goals (rw_cv_call; wpc_auto; rw_cv_done))
  -- Check each completed loop branch separately so the outer recursive proof
  -- reuses an opaque theorem instead of repeating its continuation conversions.
  all_goals
    as_aux_lemma =>
      first
      | (show WPC _ (.while (.bin .lt (.var "i") (.var "hi")) _) _ _ _
         name_bud st2 w2 mm2 hb2
         apply WPC.while
           (I := fun env' st' k => ∃ (hdr code n par lo w cw i : BitVec 32) (x y z mv sbv acc : BitVec 64),
             env' = rwCvEnv sb id d hdr code n par lo hiv w cw i x y z mv sbv acc ∧ i.toNat ≤ hiv.toNat ∧
             st' = st2 ∧ k.t ≤ 6 * i.toNat ∧ k.m = 0)
           (μ := fun env' _ => hiv.toNat - envU32 env' "i")
         · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp, rfl, by simp, by simp⟩
         rintro env' st' k ⟨hdr, code, n, par, lo, w, cw, i, x, y, z, mv, sbv, acc, rfl, hih, rfl, hk, hkm⟩
         simp only [rwCvEnv]
         embc_simp
         refine ⟨fun hge => ?_, fun hlt => ?_⟩
         · wpc_auto
           rw_cv_done
         have hlt' : i.toNat < hiv.toNat := by simpa [BitVec.lt_def] using hlt
         have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
         wpc_auto
         all_goals rw_cv_next hi1)
      | (show WPC _ (.while (.bin .lt (.var "i") (.var "n")) _) _ _ _
         name_bud st1 w1 mm1 hb1
         apply WPC.while
           (I := fun env' st' k => ∃ (hdr code n par lo hi w cw i : BitVec 32) (x y z mv sbv acc : BitVec 64),
             env' = rwCvEnv sb id d hdr code n par lo hi w cw i x y z mv sbv acc ∧ i.toNat ≤ n.toNat ∧
             ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
               k.t + A * w'.toNat ≤ A * w1.toNat ∧ k.m + mm'.toNat ≤ mm1.toNat)
           (μ := fun env' _ => envU32 env' "n" - envU32 env' "i")
         · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp, w1, mm1, hb1, by simp, by simp⟩
         rintro env' st' k ⟨hdr, code, n, par, lo, hi, w, cw, i, x, y, z, mv, sbv, acc, rfl, hin, w', mm', hb', hk, hkm⟩
         simp only [rwCvEnv]
         embc_simp
         refine ⟨fun hge => ?_, fun hlt => ?_⟩
         · wpc_auto
           rw_cv_done
         have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
         have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
         apply WPC.seq
         rw_cv_call
         wpc_auto
         rw_cv_done
         all_goals rw_cv_next hi1)

theorem cval_cost (sb A : Nat) (hA : 2000 ≤ A) (id d : BitVec 32) :
    FnCost (State := State) prog "cval" (BudPre sb [.ptr sb 0, .u32 id, .u32 d])
      (Amort sb A (allow 100) 0 (slackUnless 4294967295#32 200)) :=
  FnCost.mono (cval_cost_gen sb A hA) (fun _ _ ⟨h1, h2⟩ => ⟨⟨id, d, h1⟩, h2⟩) (fun _ _ _ _ _ _ h => h)

fncost_register "cval" cval cval_cost

/-! ## `EVALUATE`, and the leaves of the rewrite engine -/

theorem r_evaluate_cost (sb A : Nat) (hA : 2000 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_evaluate" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 17500) 0 noSlack) := by
  have h100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := rEvaluate) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rEvaluate
  wpc_auto
  wpc_done

fncost_register "r_evaluate" rEvaluate r_evaluate_cost

theorem rw_zero_cost (sb A : Nat) (e : BitVec 32) :
    FnCost (State := State) prog "rw_zero" (BudPre sb [.ptr sb 0, .u32 e])
      (Amort sb A (allow 18000) 0 noSlack) := by
  apply FnCost.intro (fn := rwZero) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwZero
  wpc_auto
  wpc_done

fncost_register "rw_zero" rwZero rw_zero_cost

theorem rw_const_cost (sb A : Nat) (hA : 2000 ≤ A) (id : BitVec 32) :
    FnCost (State := State) prog "rw_const" (BudPre sb [.ptr sb 0, .u32 id])
      (Amort sb A (allow 120) 0 noSlack) := by
  apply FnCost.intro (fn := rwConst) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwConst
  wpc_auto
  wpc_done

fncost_register "rw_const" rwConst rw_const_cost

theorem rw_ext_cost (sb A : Nat) (hA : 2000 ≤ A) (tag a b : BitVec 32) :
    FnCost (State := State) prog "rw_ext" (BudPre sb [.ptr sb 0, .u32 tag, .u32 a, .u32 b])
      (Amort sb A (allow 8800) 0 noSlack) := by
  have h100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := rwExt) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwExt
  wpc_auto
  wpc_done

fncost_register "rw_ext" rwExt rw_ext_cost

theorem rw_extract_cost (sb A : Nat) (hA : 2000 ≤ A) (a b c : BitVec 32) :
    FnCost (State := State) prog "rw_extract" (BudPre sb [.ptr sb 0, .u32 a, .u32 b, .u32 c])
      (Amort sb A (allow 9000) 0 noSlack) := by
  have h100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := rwExtract) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwExtract
  wpc_auto
  wpc_done

fncost_register "rw_extract" rwExtract rw_extract_cost

theorem rw_max_cost (sb A : Nat) (hA : 2000 ≤ A) (a : BitVec 32) :
    FnCost (State := State) prog "rw_max" (BudPre sb [.ptr sb 0, .u32 a])
      (Amort sb A (allow 8800) 0 noSlack) := by
  have h100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := rwMax) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwMax
  wpc_auto
  wpc_done

fncost_register "rw_max" rwMax rw_max_cost

theorem rw_sym_cost (sb A : Nat) (hA : 2000 ≤ A) (a b : BitVec 32) :
    FnCost (State := State) prog "rw_sym" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow 9000) 0 noSlack) := by
  have h100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := rwSym) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwSym
  wpc_auto
  wpc_done

fncost_register "rw_sym" rwSym rw_sym_cost

/-! ## `rw_inst`: the cost is linear in the size of the pattern -/

/-- The length field of the header word at `p` of `rw_tbl`. -/
def rwLen (p : Nat) : Nat := RwEnc.words.getD p 0 / 65536

theorem rw_len_eq {p : Nat} {e : Bcf.RwExpr} (h : RwAt p (encE e)) (hw : wfE e = true) :
    rwLen p = (encE e).length := by
  obtain ⟨h1, -, -⟩ := rw_head h hw
  have htg := rw_tagE_lt e
  have hax := rw_auxE_lt hw
  unfold rwLen
  rw [List.getD_eq_getElem?_getD, h1, Option.getD_some]
  omega

def rwInstPre (sb : Nat) (vs : List Val) : Prop :=
  ∃ (p ab na d : BitVec 32) (e : Bcf.RwExpr), vs = [.ptr sb 0, .u32 p, .u32 ab, .u32 na, .u32 d] ∧
    RwAt p.toNat (encE e) ∧ wfE e = true

def rwInstDepth : List Val → Nat
  | [_, _, _, _, .u32 d] => d.toNat
  | _ => 0

def rwInstPos : List Val → Nat
  | [_, .u32 p, _, _, _] => p.toNat
  | _ => 0

theorem rw_eval_tbl {env : Env} {m : Mem} {i : Expr} {q : BitVec 32} {H : Nat}
    (he : evalE prog env m i = some (.u32 q)) (hw : RwEnc.words[q.toNat]? = some H) :
    evalE prog env m (.cload "rw_tbl" i) = some (.u32 (BitVec.ofNat 32 H)) := by
  exact rw_eval_cload rw_findConst he rfl (rw_tbl_get hw)

theorem rw_assign_tbl {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {x y : Var} {p : BitVec 32} {H : Nat}
    (hx : env.ty x = some .u32) (hy : env.get y = some (.u32 p))
    (hw : RwEnc.words[p.toNat]? = some H)
    (h : Q .normal (env.set x (.u32 (BitVec.ofNat 32 H))) st 1) :
    WPC prog (.assign x (.cload "rw_tbl" (.var y))) Q env st := by
  apply WPC.assign
  rw [rw_eval_tbl (by rw [evalE, hy]) hw]
  simp only [Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
  exact h

/-- `p = q + 1`, without wrapping. -/
theorem rw_assign_add1 {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x y : Var} {v : BitVec 32}
    (hx : env.ty x = some .u32) (hy : env.get y = some (.u32 v)) (hv : v.toNat + 1 < 2 ^ 32)
    (h : ∀ q : BitVec 32, q.toNat = v.toNat + 1 → Q .normal (env.set x (.u32 q)) st 1) :
    WPC P (.assign x (.bin .add (.var y) (.lit32 1#32))) Q env st := by
  apply WPC.assign
  simp only [evalE, hy, evalBin, evalArith, Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
  exact h _ (by rw [BitVec.toNat_add]; simp; omega)

/-- `p = p + (@rw_tbl[p] >> 16)` at the header of a pattern: `p` moves past it. -/
theorem rw_assign_next {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {v : BitVec 32} {e : Bcf.RwExpr}
    (hx : env.ty "p" = some .u32) (hy : env.get "p" = some (.u32 v))
    (hat : RwAt v.toNat (encE e)) (hwf : wfE e = true)
    (h : ∀ q : BitVec 32, q.toNat = v.toNat + (encE e).length → Q .normal (env.set "p" (.u32 q)) st 1) :
    WPC prog (.assign "p" (.bin .add (.var "p") (.bin .shr (.cload "rw_tbl" (.var "p")) (.lit32 16#32))))
      Q env st := by
  obtain ⟨hw, hl, hpl⟩ := rw_head hat hwf
  have htg := rw_tagE_lt e
  have hax := rw_auxE_lt hwf
  apply WPC.assign
  have he : evalE prog env st.mem (.bin .add (.var "p") (.bin .shr (.cload "rw_tbl" (.var "p")) (.lit32 16#32))) =
      some (.u32 (v + BitVec.ofNat 32 (encE e).length)) := by
    rw [rw_eval_next_u32 rw_findConst hy (rw_tbl_get hw)]
    simp only [rw_hdr_len (show tagE e < 256 by omega) hax hl]
  rw [he]
  simp only [Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
  refine h _ ?_
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- An `if` on the decoded tag whose condition is true: enter its branch. -/
macro "rw_tag_take" : tactic => `(tactic| (
  apply WPC.seq
  apply WPC.ite
  simp [evalE, evalBin, evalArith, Env.get, Val.ofBool, RW_VAR, RW_TT, RW_FF, RW_LIT, RW_SYMVAL, RW_BVMAX,
    RW_APP, RW_ITE, RW_EXTRACT, RW_ZEXT, RW_SEXT, RW_REPEAT, tagE, tVar, tTT, tFF, tLit, tSymVal, tBvmax,
    tApp, tIte, tExtract, tZext, tSext, tRepeat]))

open Lean in
/-- A recursive call `x = rw_inst(st, p, ab, na, depth - 1)` on the pattern at `p` (`hat`, `hwf`). -/
macro "rw_inst_rec" hat:ident hwf:ident : tactic => do
  let IH := mkIdent `IH
  let hd := mkIdent `hd
  `(tactic| (
    have _hbc := ‹Budget _ _ _ _›
    refine WPC.call_shape (fn := rwInst) (hf := rfl) (hps := rfl) ?_
    intro _vs _hargs _hbp
    simp only [evalArgs, evalE, evalBin, evalArith, Env.get, String.reduceEq, ↓reduceIte,
      Option.some.injEq] at _hargs
    subst _hargs
    refine ⟨_, _, $IH, ⟨⟨⟨_, _, _, _, _, rfl, $hat, $hwf⟩, _, _, _hbc⟩,
      by simp only [rwInstDepth]; have := rw_cv_dec $hd; omega⟩, ?_⟩
    rintro _rv _st' _c ⟨_w', _mm', _hb', _ht, _hm⟩
    rw [Budget.wk _hbc] at _ht
    rw [Budget.mk _hbc] at _hm
    simp only [rwInstPos, rw_len_eq $hat $hwf] at _ht
    split
    · trivial
    rename_i _env' _hasg
    obtain ⟨_r, _h1, _h2⟩ := assignDst_u32' _hasg rfl
    subst _h1
    subst _h2
    wpc_simp))

/-- A recursive call on the pattern at `p`, then `if (x == NOID) return NOID;`. -/
macro "rw_child" hat:ident hwf:ident : tactic => `(tactic| (
  apply WPC.seq
  rw_inst_rec $hat $hwf
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto
    rw_cv_done
  apply WPC.skip
  wpc_simp))

/-- `WPC.while` with the invariant also given the state at the loop. -/
theorem rw_while {P : Prog} {c : Expr} {body : Stmt} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)}
    (I : Env → (KernelState P State) → Env → (KernelState P State) → Cost → Prop) (μ : Env → (KernelState P State) → Nat) (h0 : I env st env st 0)
    (hstep : ∀ env' st' k, I env st env' st' k →
      match evalE P env' st'.mem c with
      | some (.u32 v) =>
        (v = 0 → Q .normal env' st' (k + 1)) ∧
        (v ≠ 0 → WPC P body (fun o env'' st'' cb =>
          match o with
          | .normal => μ env'' st'' < μ env' st' ∧ I env st env'' st'' (k + cb + 2)
          | .brk => Q .normal env'' st'' (k + cb + 2)
          | .ret r => Q (.ret r) env'' st'' (k + cb + 1)) env' st')
      | _ => True) :
    WPC P (.while c body) Q env st :=
  WPC.while (I env st) μ h0 hstep

/-- An `if` on the decoded tag whose condition is false: skip it. -/
macro "rw_tag_skip" : tactic => `(tactic| (
  apply WPC.seq
  apply WPC.ite
  simp [evalE, evalBin, evalArith, Env.get, Val.ofBool, RW_VAR, RW_TT, RW_FF, RW_LIT, RW_SYMVAL, RW_BVMAX,
    RW_APP, RW_ITE, RW_EXTRACT, RW_ZEXT, RW_SEXT, RW_REPEAT, tagE, tVar, tTT, tFF, tLit, tSymVal, tBvmax,
    tApp, tIte, tExtract, tZext, tSext, tRepeat]
  apply WPC.skip
  wpc_simp))

theorem rw_inst_cost_gen (sb A : Nat) (hA : 2000 ≤ A) :
    FnCost (State := State) prog "rw_inst" (fun vs st => rwInstPre sb vs ∧ ∃ w mm : BitVec 32, Budget st.mem sb w mm)
      (fun vs => Amort sb A (allow (20000 * rwLen (rwInstPos vs) - 200)) 0 noSlack vs) := by
  apply FnCost.rec (fun vs _ => rwInstDepth vs)
  intro m IH
  apply FnCost.intro (fn := rwInst) rfl
  rintro vs st ⟨⟨⟨p, ab, na, d, e, rfl, hat, hwf⟩, w, mm, hb⟩, hm⟩
  simp only [rwInstDepth] at hm
  simp only [rwInstPos, rw_len_eq hat hwf]
  have h100 : 100 ≤ A := by omega
  have hlen := rw_encE_len_pos e
  obtain ⟨hw, hl, hpl⟩ := rw_head hat hwf
  fncost_body rwInst
  -- if (depth == 0) return NOID;
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro hd; wpc_auto; wpc_done
  intro hd; apply WPC.skip; wpc_simp
  -- hdr = @rw_tbl[pos];
  apply WPC.seq; refine rw_assign_tbl (by rfl) (by rfl) hw ?_; wpc_simp
  have htg := rw_tagE_lt e
  have hax := rw_auxE_lt hwf
  apply WPC.seq; apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty, Mem.hasTy_u32,
    rw_hdr_tag (show tagE e < 256 by omega) hax hl]
  wpc_simp
  apply WPC.seq; apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty, Mem.hasTy_u32,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT, rw_hdr_aux (show tagE e < 256 by omega) hax hl]
  wpc_simp
  apply WPC.seq; apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty, Mem.hasTy_u32,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT, rw_hdr_len (show tagE e < 256 by omega) hax hl]
  wpc_simp
  cases e
  all_goals repeat rw_tag_skip
  case bvmax e1 =>
    simp only [wfE] at hwf
    simp only [encE, List.length_cons] at hat hlen hl hpl ⊢
    have hat1 : RwAt (p.toNat + 1) (encE e1) := hat.tail
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    rw [← hq1] at hat1
    apply WPC.seq; rw_inst_rec hat1 hwf
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; rw_cv_done
    apply WPC.skip; wpc_simp
    rw_tag_take
    wpc_auto
    rw_cv_done
  case var i =>
    simp only [encE, List.length_cons, List.length_nil] at hlen hl hpl ⊢
    rw_tag_take
    wpc_auto
    rw_cv_done
  case tt =>
    simp only [encE, List.length_cons, List.length_nil] at hlen hl hpl ⊢
    rw_tag_take
    wpc_auto
    rw_cv_done
  case ff =>
    simp only [encE, List.length_cons, List.length_nil] at hlen hl hpl ⊢
    rw_tag_take
    wpc_auto
    rw_cv_done
  case lit v =>
    simp only [encE, List.length_cons, List.length_nil] at hlen hl hpl ⊢
    rw_tag_take
    apply WPC.seq
    have hbc := ‹Budget _ _ _ _›
    refine WPC.call_shape (fn := mkval) (hf := rfl) (hps := rfl) ?_
    intro vs1 hargs hbp
    obtain ⟨v0, vs2, h0, -, rfl⟩ := evalArgs_cons' hargs
    simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at h0
    subst h0
    obtain ⟨v1, vs3, e1, -, hbp1⟩ := bindParams_ne_none_cons hbp
    simp only [List.cons.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨v2, vs4, rfl, ht2, hbp2⟩ := bindParams_ne_none_cons hbp1
    obtain ⟨w2, rfl⟩ := Mem.hasTy_u32_inv ht2
    obtain ⟨v3, vs5, rfl, ht3, hbp3⟩ := bindParams_ne_none_cons hbp2
    obtain ⟨x3, rfl⟩ := Mem.hasTy_u64_inv ht3
    obtain rfl := bindParams_ne_none_nil hbp3
    clear hargs
    refine ⟨_, _, mkval_cost sb A h100 w2 x3, ⟨rfl, _, _, hbc⟩, ?_⟩
    rintro _rv _st' _c ⟨_w', _mm', _hb', _ht, _hm⟩
    rw [Budget.wk hbc] at _ht
    rw [Budget.mk hbc] at _hm
    split
    · trivial
    rename_i env2 hasg
    obtain ⟨r2, h1, h2⟩ := assignDst_u32' hasg rfl
    subst h1
    subst h2
    wpc_simp
    cost_clean
    wpc_auto
    rw_cv_done
  case symVal e1 e2 =>
    simp only [wfE, Bool.and_eq_true] at hwf
    obtain ⟨hwf1, hwf2⟩ := hwf
    simp only [encE, List.length_cons, List.length_append] at hat hlen hl hpl ⊢
    have hl1 := rw_encE_len_pos e1
    have hl2 := rw_encE_len_pos e2
    have hat1 : RwAt (p.toNat + 1) (encE e1) := hat.tail.left
    have hat2 : RwAt (p.toNat + 1 + (encE e1).length) (encE e2) := hat.tail.right
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    rw [← hq1] at hat1 hat2
    rw_child hat1 hwf1
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat1 hwf1 ?_; intro q2 hq2; wpc_simp
    rw [← hq2] at hat2
    rw_child hat2 hwf2
    rw_tag_take
    wpc_auto
    rw_cv_done
  case zext e1 e2 =>
    simp only [wfE, Bool.and_eq_true] at hwf
    obtain ⟨hwf1, hwf2⟩ := hwf
    simp only [encE, List.length_cons, List.length_append] at hat hlen hl hpl ⊢
    have hl1 := rw_encE_len_pos e1
    have hl2 := rw_encE_len_pos e2
    have hat1 : RwAt (p.toNat + 1) (encE e1) := hat.tail.left
    have hat2 : RwAt (p.toNat + 1 + (encE e1).length) (encE e2) := hat.tail.right
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    rw [← hq1] at hat1 hat2
    rw_child hat1 hwf1
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat1 hwf1 ?_; intro q2 hq2; wpc_simp
    rw [← hq2] at hat2
    rw_child hat2 hwf2
    rw_tag_skip
    rw_tag_take
    wpc_auto
    rw_cv_done
  case sext e1 e2 =>
    simp only [wfE, Bool.and_eq_true] at hwf
    obtain ⟨hwf1, hwf2⟩ := hwf
    simp only [encE, List.length_cons, List.length_append] at hat hlen hl hpl ⊢
    have hl1 := rw_encE_len_pos e1
    have hl2 := rw_encE_len_pos e2
    have hat1 : RwAt (p.toNat + 1) (encE e1) := hat.tail.left
    have hat2 : RwAt (p.toNat + 1 + (encE e1).length) (encE e2) := hat.tail.right
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    rw [← hq1] at hat1 hat2
    rw_child hat1 hwf1
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat1 hwf1 ?_; intro q2 hq2; wpc_simp
    rw [← hq2] at hat2
    rw_child hat2 hwf2
    rw_tag_skip
    rw_tag_take
    wpc_auto
    rw_cv_done
  case «repeat» e1 e2 =>
    simp only [wfE, Bool.and_eq_true] at hwf
    obtain ⟨hwf1, hwf2⟩ := hwf
    simp only [encE, List.length_cons, List.length_append] at hat hlen hl hpl ⊢
    have hl1 := rw_encE_len_pos e1
    have hl2 := rw_encE_len_pos e2
    have hat1 : RwAt (p.toNat + 1) (encE e1) := hat.tail.left
    have hat2 : RwAt (p.toNat + 1 + (encE e1).length) (encE e2) := hat.tail.right
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    rw [← hq1] at hat1 hat2
    rw_child hat1 hwf1
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat1 hwf1 ?_; intro q2 hq2; wpc_simp
    rw [← hq2] at hat2
    rw_child hat2 hwf2
    rw_tag_skip
    rw_tag_take
    wpc_auto
    rw_cv_done
  case ite e1 e2 e3 =>
    simp only [wfE, Bool.and_eq_true] at hwf
    obtain ⟨⟨hwf1, hwf2⟩, hwf3⟩ := hwf
    simp only [encE, List.length_cons, List.length_append] at hat hlen hl hpl ⊢
    have hl1 := rw_encE_len_pos e1
    have hl2 := rw_encE_len_pos e2
    have hl3 := rw_encE_len_pos e3
    have hat1 : RwAt (p.toNat + 1) (encE e1) := hat.tail.left.left
    have hat2 : RwAt (p.toNat + 1 + (encE e1).length) (encE e2) := hat.tail.left.right
    have hat3 : RwAt (p.toNat + 1 + (encE e1).length + (encE e2).length) (encE e3) := by
      have := hat.tail.right; simp only [List.length_append, ← Nat.add_assoc] at this; exact this
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    rw [← hq1] at hat1 hat2 hat3
    rw_child hat1 hwf1
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat1 hwf1 ?_; intro q2 hq2; wpc_simp
    rw [← hq2] at hat2 hat3
    rw_child hat2 hwf2
    rw_tag_skip
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat2 hwf2 ?_; intro q3 hq3; wpc_simp
    rw [← hq3] at hat3
    rw_child hat3 hwf3
    rw_tag_take
    wpc_auto
    rw_cv_done
  case extract e1 e2 e3 =>
    simp only [wfE, Bool.and_eq_true] at hwf
    obtain ⟨⟨hwf1, hwf2⟩, hwf3⟩ := hwf
    simp only [encE, List.length_cons, List.length_append] at hat hlen hl hpl ⊢
    have hl1 := rw_encE_len_pos e1
    have hl2 := rw_encE_len_pos e2
    have hl3 := rw_encE_len_pos e3
    have hat1 : RwAt (p.toNat + 1) (encE e1) := hat.tail.left.left
    have hat2 : RwAt (p.toNat + 1 + (encE e1).length) (encE e2) := hat.tail.left.right
    have hat3 : RwAt (p.toNat + 1 + (encE e1).length + (encE e2).length) (encE e3) := by
      have := hat.tail.right; simp only [List.length_append, ← Nat.add_assoc] at this; exact this
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    rw [← hq1] at hat1 hat2 hat3
    rw_child hat1 hwf1
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat1 hwf1 ?_; intro q2 hq2; wpc_simp
    rw [← hq2] at hat2 hat3
    rw_child hat2 hwf2
    rw_tag_skip
    rw_tag_skip
    apply WPC.seq; refine rw_assign_next (by rfl) (by rfl) hat2 hwf2 ?_; intro q3 hq3; wpc_simp
    rw [← hq3] at hat3
    rw_child hat3 hwf3
    rw_tag_skip
    rw_tag_take
    wpc_auto
    rw_cv_done
  case app op as =>
    simp only [wfE] at hwf
    simp only [encE, List.length_cons] at hat hlen hl hpl ⊢
    rw_tag_take
    apply WPC.seq; wpc_step
    apply WPC.seq; refine rw_assign_add1 (by rfl) (by rfl) (by omega) ?_; intro q1 hq1; wpc_simp
    have hend : (p + BitVec.ofNat 32 ((encA as).length + 1)).toNat = p.toNat + (encA as).length + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hat1 : RwAt q1.toNat (encA as) := by rw [hq1]; exact hat.tail
    name_bud st1 w1 mm1 hb1
    apply WPC.seq
    refine rw_while (fun env0 _ env' st' k => ∃ (pv av okv : BitVec 32) (rest : Bcf.RwArgs),
        env' = ((env0.set "p" (.u32 pv)).set "a" (.u32 av)).set "ok" (.u32 okv) ∧
        RwAt pv.toNat (encA rest) ∧ wfA rest = true ∧
        pv.toNat + (encA rest).length = p.toNat + (encA as).length + 1 ∧ q1.toNat ≤ pv.toNat ∧
        ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
          k.t + A * w'.toNat ≤ A * w1.toNat + 20000 * (pv.toNat - q1.toNat) ∧ k.m + mm'.toNat ≤ mm1.toNat)
      (fun env' _ => p.toNat + (encA as).length + 1 - envU32 env' "p") ?_ ?_
    · exact ⟨q1, 0#32, 0#32, as, by simp [Env.set], hat1, hwf, by omega, Nat.le_refl _, w1, mm1, hb1,
        by simp, by simp⟩
    rintro env' st' k ⟨pv, av, okv, rest, rfl, hatr, hwfr, hpv, hq1pv, w', mm', hb', hk, hkm⟩
    simp only [Env.set, String.reduceEq, ↓reduceIte]
    simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool]
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · have hge' : ¬ pv.toNat < p.toNat + (encA as).length + 1 := by
        intro h
        have h2 : pv < p + BitVec.ofNat 32 ((encA as).length + 1) := by rw [BitVec.lt_def, hend]; exact h
        simp [h2] at hge
      wpc_auto
      rw_cv_done
    have hlt' : pv.toNat < p.toNat + (encA as).length + 1 := by
      have h2 : pv < p + BitVec.ofNat 32 ((encA as).length + 1) := by
        by_cases h3 : pv < p + BitVec.ofNat 32 ((encA as).length + 1)
        · exact h3
        · exact absurd (by simp [h3]) hlt
      rw [BitVec.lt_def, hend] at h2; exact h2
    cases rest with
    | nil => simp [encA] at hpv; omega
    | cons e1 r1 =>
      simp only [encA, wfA, Bool.and_eq_true] at hatr hwfr hpv
      obtain ⟨hwf1, hwfr1⟩ := hwfr
      simp only [List.length_append] at hpv
      have hl1 := rw_encE_len_pos e1
      have hat1' := hatr.left
      have hatr' := hatr.right
      rw_child hat1' hwf1
      apply WPC.seq; wpc_step
      apply WPC.seq; apply WPC.ite_any
      · wpc_auto
        rw_cv_done
      apply WPC.skip; wpc_simp
      refine rw_assign_next (by rfl) (by rfl) hat1' hwf1 ?_; intro q2 hq2
      rw [← hq2] at hatr'
      simp only [CPost.shift_apply, Env.set, String.reduceEq, ↓reduceIte, envU32, Env.get]
      refine ⟨by omega, q2, _, _, r1, rfl, hatr', hwfr1, by omega, by omega, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
      · cost_clean
        cost_arith
      · cost_clean
        cost_arith

theorem rw_inst_cost (sb A : Nat) (hA : 2000 ≤ A) (pos ab na depth : BitVec 32) (e : Bcf.RwExpr)
    (hat : RwAt pos.toNat (encE e)) (hwf : wfE e = true) :
    FnCost (State := State) prog "rw_inst" (BudPre sb [.ptr sb 0, .u32 pos, .u32 ab, .u32 na, .u32 depth])
      (Amort sb A (allow (20000 * (encE e).length - 200)) 0 noSlack) := by
  refine FnCost.mono (rw_inst_cost_gen sb A hA) (fun _ _ ⟨h1, h2⟩ => ⟨⟨pos, ab, na, depth, e, h1, hat, hwf⟩, h2⟩) ?_
  rintro vs st rv st' c ⟨rfl, -⟩ h
  simpa only [rwInstPos, rw_len_eq hat hwf] using h

fncost_register "rw_inst" rwInst rw_inst_cost

/-! ## `rw_cond_one`, `rw_check_cond` -/

theorem rw_cond_one_cost (sb A : Nat) (hA : 2000 ≤ A) (ci i np : BitVec 32) :
    FnCost (State := State) prog "rw_cond_one" (BudPre sb [.ptr sb 0, .u32 ci, .u32 i, .u32 np])
      (Amort sb A (allow 150) 0 noSlack) := by
  apply FnCost.intro (fn := rwCondOne) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwCondOne
  wpc_auto
  wpc_done

fncost_register "rw_cond_one" rwCondOne rw_cond_one_cost

theorem rw_check_cond_cost (sb A : Nat) (hA : 2000 ≤ A) (c np : BitVec 32) :
    FnCost (State := State) prog "rw_check_cond" (BudPre sb [.ptr sb 0, .u32 c, .u32 np])
      (Amort sb A (allow (180 * 255 + 40)) 0 noSlack) := by
  apply FnCost.intro (fn := rwCheckCond) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rwCheckCond
  apply WPC.seq
  apply WPC.ite_any
  case hb =>
    wpc_auto
    wpc_done
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  wpc_auto
  wpc_done
  all_goals
    apply WPC.while
      (I := fun env' st' k => ∃ i ok : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("c", .u32, .u32 c), ("np", .u32, .u32 np),
          ("n", .u32, .u32 n), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧
        i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w0.toNat + 180 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
      (μ := fun env' _ => n.toNat - envU32 env' "i")
    · exact ⟨0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
    rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1

fncost_register "rw_check_cond" rwCheckCond rw_check_cond_cost

/-! ## `r_rewrite` -/

theorem rw_inst_call {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb A : Nat} (hA : 2000 ≤ A)
    {w mm pos : BitVec 32} {e : Bcf.RwExpr} (hat : RwAt pos.toNat (encE e)) (hwf : wfE e = true)
    {x : Var} {a1 a2 a3 a4 : Expr} (hb : Budget st.mem sb w mm) (hst : env.get "st" = some (.ptr sb 0))
    (h1 : evalE prog env st.mem a1 = some (.u32 pos)) (hx : env.ty x = some .u32)
    (h : ∀ (r : BitVec 32) (st' : (KernelState prog State)) (c : Cost) (w' mm' : BitVec 32), Budget st'.mem sb w' mm' →
      c.t + A * w'.toNat ≤ A * w.toNat + (20000 * (encE e).length - 200) → c.m + mm'.toNat ≤ mm.toNat →
      Q .normal (env.set x (.u32 r)) st' (c + 2)) :
    WPC prog (.call (some x) "rw_inst" [.var "st", a1, a2, a3, a4]) Q env st := by
  apply WPC.call_shape (fn := rwInst) (hf := rfl) (hps := rfl)
  intro vs hargs hbp
  obtain ⟨v0, vs0, h0, hargs0, rfl⟩ := evalArgs_cons' hargs
  rw [evalE, hst] at h0
  cases h0
  obtain ⟨v1, vs1, h1', -, rfl⟩ := evalArgs_cons' hargs0
  rw [h1] at h1'
  cases h1'
  obtain ⟨_, _, e1, -, hbp1⟩ := bindParams_ne_none_cons hbp
  simp only [List.cons.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨_, _, e2, -, hbp2⟩ := bindParams_ne_none_cons hbp1
  simp only [List.cons.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  obtain ⟨v3, vs3, rfl, ht3, hbp3⟩ := bindParams_ne_none_cons hbp2
  obtain ⟨ab', rfl⟩ := Mem.hasTy_u32_inv ht3
  obtain ⟨v4, vs4, rfl, ht4, hbp4⟩ := bindParams_ne_none_cons hbp3
  obtain ⟨na', rfl⟩ := Mem.hasTy_u32_inv ht4
  obtain ⟨v5, vs5, rfl, ht5, hbp5⟩ := bindParams_ne_none_cons hbp4
  obtain ⟨d', rfl⟩ := Mem.hasTy_u32_inv ht5
  obtain rfl := bindParams_ne_none_nil hbp5
  refine ⟨_, _, rw_inst_cost sb A hA pos ab' na' d' e hat hwf, ⟨rfl, _, _, hb⟩, ?_⟩
  rintro rv st' c ⟨w', mm', hb', ht, hm⟩
  rw [hb.wk] at ht
  rw [hb.mk] at hm
  split
  · trivial
  rename_i env' hasg
  obtain ⟨r, rfl, rfl⟩ := assignDst_u32' hasg hx
  simp only [allow_apply, noSlack_apply] at ht
  exact h r st' c w' mm' hb' (by omega) (by omega)

set_option maxRecDepth 100000 in
theorem rw_tbl_len_all :
    (List.range Vbcf.RwEnc.bound).all (fun i => match Bcf.rwTable i with
      | some r => decide ((encOpt r.cond).length + (encE r.lhs).length + (encE r.rhs).length ≤ 71)
      | none => true) = true := by decide

theorem rw_tbl_len {rid : Nat} (hr : rid < Vbcf.RwEnc.bound) {r : Bcf.RwRule} (h : Bcf.rwTable rid = some r) :
    (encOpt r.cond).length + (encE r.lhs).length + (encE r.rhs).length ≤ 71 := by
  have := List.all_eq_true.mp rw_tbl_len_all rid (List.mem_range.mpr hr)
  simpa [h] using this

theorem rw_assign_tbl_e {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {x : Var} {i : Expr} {q : BitVec 32} {H : Nat}
    (hx : env.ty x = some .u32) (he : evalE prog env st.mem i = some (.u32 q))
    (hw : RwEnc.words[q.toNat]? = some H)
    (h : Q .normal (env.set x (.u32 (BitVec.ofNat 32 H))) st 1) :
    WPC prog (.assign x (.cload "rw_tbl" i)) Q env st := by
  apply WPC.assign
  rw [rw_eval_tbl he hw]
  simp only [Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
  exact h

/-- `a; b` through a join condition that also sees the state before `a`. -/
theorem rw_seq_join {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {a b : Stmt}
    (J : Env → (KernelState P State) → Env → (KernelState P State) → Cost → Prop)
    (ha : WPC P a (fun o env' st' k => match o with
      | .normal => J env st env' st' k
      | .brk => Q .brk env' st' (k + 2)
      | .ret rv => Q (.ret rv) env' st' (k + 1)) env st)
    (hb : ∀ env' st' k, J env st env' st' k → WPC P b (Q.shift (k + 2)) env' st') :
    WPC P (.seq a b) Q env st :=
  WPC.seq_join (J env st) ha hb

theorem rw_encOpt_some (e : Bcf.RwExpr) : encOpt (some e) = encE e := rfl
theorem rw_encOpt_none : encOpt none = [] := rfl

theorem r_rewrite_cost (sb A : Nat) (hA : 2000 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_rewrite" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 1600000) 0 noSlack) := by
  have h100 : 100 ≤ A := by omega
  have hA6 : 6 ≤ A := by omega
  apply FnCost.intro (fn := rRewrite) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rRewrite
  -- if (na == 0) return NOID;
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro hna; wpc_auto; rw_cv_done
  intro hna; apply WPC.skip; wpc_simp
  -- rid = st->par[0];
  apply WPC.seq; refine WPC.assign_u32 (by rfl) ?_; intro rid; wpc_simp
  -- if (rid == 0) { ... }
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rw_cv_done
  apply WPC.skip; wpc_simp
  -- if (rid >= RW_NRULES) return NOID;
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; rw_cv_done
  intro hr; apply WPC.skip; wpc_simp
  have hr' : rid.toNat < Vbcf.RwEnc.bound := by
    have := BitVec.lt_def.mp hr; simpa [Vbcf.RwEnc.bound] using this
  have hn1 : (na - 1#32).toNat = na.toNat - 1 := bv_sub_one_toNat hna
  have hna1 : 1 ≤ na.toNat := by
    have : na.toNat ≠ 0 := fun e => hna (BitVec.eq_of_toNat_eq (by simpa using e))
    omega
  obtain ⟨hidx0, hidx1⟩ := rw_tbl_index hr'
  cases hrid : Bcf.rwTable rid.toNat with
  | none =>
    apply WPC.seq; refine rw_assign_tbl (by rfl) (by rfl) (hidx0 hrid) ?_; wpc_simp
    apply WPC.seq; apply WPC.ite; embc_simp
    wpc_auto; rw_cv_done
  | some r =>
  obtain ⟨off, hoffw, hoffb, hrec⟩ := hidx1 r hrid
  have hR := rw_rec (by simp [Vbcf.RwEnc.bound] at hoffb; omega) hrec
  have hoff64 : off + 3 < 65536 := by
    obtain ⟨G, hG, -⟩ := hR.rhs
    have := lt_length_of_getElem? hG
    have := rw_words_len
    omega
  have hwfr := rw_tbl_wf hr' hrid
  have hlen71 := rw_tbl_len hr' hrid
  simp only [wfRule, Bool.and_eq_true] at hwfr
  obtain ⟨⟨⟨-, hwfc⟩, hwfl⟩, hwfrh⟩ := hwfr
  apply WPC.seq; refine rw_assign_tbl (by rfl) (by rfl) hoffw ?_; wpc_simp
  apply WPC.seq; apply WPC.ite
  have hoffne : ¬ BitVec.ofNat 32 off = 0#32 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; simp [Vbcf.RwEnc.bound] at hoffb; omega
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool, hoffne, decide_false]
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  apply WPC.skip; wpc_simp
  apply WPC.seq; refine WPC.assign_u32 (by rfl) ?_; intro abv; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  name_bud st1 w1 mm1 hb1
  apply WPC.seq
  refine rw_while (fun env0 _ env' st' k => ∃ (i a ok : BitVec 32),
      env' = ((env0.set "i" (.u32 i)).set "a" (.u32 a)).set "ok" (.u32 ok) ∧ 1 ≤ i.toNat ∧ i.toNat ≤ na.toNat ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat + 100 * (i.toNat - 1) ≤ A * w1.toNat ∧ k.m + mm'.toNat ≤ mm1.toNat)
    (fun env' _ => na.toNat - envU32 env' "i") ?_ ?_
  · exact ⟨1#32, 0#32, 0#32, by simp [Env.set], by simp, by simpa using hna1, w1, mm1, hb1, by simp, by simp⟩
  rintro env' st' k ⟨i, a, ok, rfl, hi1, hin, w', mm', hb', hk, hkm⟩
  simp only [Env.set, String.reduceEq, ↓reduceIte]
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hge' : ¬ i.toNat < na.toNat := by
      intro h
      have h2 : i < na := BitVec.lt_def.mpr h
      simp [h2] at hge
    have hieq : i.toNat = na.toNat := by omega
    -- ok = rw_params(st, off, ab, n); if (ok == 0) return NOID;
    apply WPC.seq; wpc_step
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; rw_cv_done
    apply WPC.skip; wpc_simp
    have hoffk : ∀ k : Nat, k ≤ 3 → (BitVec.ofNat 32 off + BitVec.ofNat 32 k).toNat = off + k := by
      intro k hk; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    -- c = @rw_tbl[off + 1];
    obtain ⟨C, hC, hCm⟩ := hR.cond
    apply WPC.seq
    refine rw_assign_tbl_e (q := BitVec.ofNat 32 off + 1#32) (by rfl)
      (by simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith])
      (by rw [hoffk 1 (by omega)]; exact hC) ?_
    wpc_simp
    name_bud st3 w3 mm3 hb3
    -- if (c == 0) { if (np != 0) return NOID; } else { ... }: joined
    refine rw_seq_join (fun env0 _ env' st' k => ∃ cv okv : BitVec 32,
        env' = (env0.set "c" (.u32 cv)).set "ok" (.u32 okv) ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w3.toNat + (20000 * (encOpt r.cond).length + 54000) ∧
        k.m + mm'.toNat ≤ mm3.toNat) ?_ ?_
    · cases hc : r.cond with
      | none =>
        simp only [hc] at hCm
        subst hCm
        apply WPC.ite
        simp [evalE, Env.get, evalBin, evalArith, Val.ofBool]
        apply WPC.ite_any
        · wpc_auto
          rw_cv_done
        apply WPC.skip
        simp only [CPost.shift_apply, Env.set, String.reduceEq, ↓reduceIte]
        exact ⟨⟨0#32, _, rfl⟩, w3, mm3, hb3, by simp [rw_encOpt_none]; omega, by simp⟩
      | some ce =>
        simp only [hc] at hCm hwfc
        obtain ⟨hC0, hatc⟩ := hCm
        have hC64 : C < 65536 := by
          have := hatc.le (rw_encE_len_pos ce); have := rw_words_len; omega
        have hatc' : RwAt (BitVec.ofNat 32 C).toNat (encE ce) := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hatc
        have hlc := rw_encE_len_pos ce
        rw [hc] at hlen71
        rw [rw_encOpt_some] at hlen71
        apply WPC.ite
        have hCne : ¬ BitVec.ofNat 32 C = 0#32 := by
          intro h; have := congrArg BitVec.toNat h; simp at this; omega
        simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool, hCne,
          decide_false]
        refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
        apply WPC.seq
        refine rw_inst_call hA hatc' hwfc hb3 (by simp [Env.get]) (by simp [evalE, Env.get]) (by rfl) ?_
        intro r1 st4 c4 w4 mm4 hb4 hc4 hm4
        wpc_simp
        wpc_auto
        rw_cv_done
        all_goals (refine ⟨_, _, rfl, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩ <;> ((try simp only [rw_encOpt_some] at *); cost_clean; cost_arith))
    rintro env4 st4 k4 ⟨cv, okv, rfl, w4, mm4, hb4, hk4, hkm4⟩
    simp only [Env.set, String.reduceEq, ↓reduceIte]
    -- l = rw_inst(st, @rw_tbl[off + 2], ...); r = rw_inst(st, @rw_tbl[off + 3], ...);
    obtain ⟨L, hL, hatl⟩ := hR.lhs
    obtain ⟨R, hRr, hatr⟩ := hR.rhs
    have hll := rw_encE_len_pos r.lhs
    have hlr := rw_encE_len_pos r.rhs
    have hL64 : L < 65536 := by have := hatl.le hll; have := rw_words_len; omega
    have hR64 : R < 65536 := by have := hatr.le hlr; have := rw_words_len; omega
    have hatl' : RwAt (BitVec.ofNat 32 L).toNat (encE r.lhs) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hatl
    have hatr' : RwAt (BitVec.ofNat 32 R).toNat (encE r.rhs) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hatr
    apply WPC.seq
    refine rw_inst_call hA hatl' hwfl hb4 (by simp [Env.get])
      (rw_eval_tbl (q := BitVec.ofNat 32 off + 2#32)
        (by simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith])
        (by rw [hoffk 2 (by omega)]; exact hL)) (by rfl) ?_
    intro l1 st5 c5 w5 mm5 hb5 hc5 hm5
    wpc_simp
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto
      rw_cv_done
    apply WPC.skip; wpc_simp
    apply WPC.seq
    refine rw_inst_call hA hatr' hwfrh hb5 (by simp [Env.get])
      (rw_eval_tbl (q := BitVec.ofNat 32 off + 3#32)
        (by simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith])
        (by rw [hoffk 3 (by omega)]; exact hRr)) (by rfl) ?_
    intro r2 st6 c6 w6 mm6 hb6 hc6 hm6
    wpc_simp
    wpc_auto
    rw_cv_done
  have hlt' : i.toNat < na.toNat := by
    have h2 : i < na := by
      by_cases h3 : i < na
      · exact h3
      · exact absurd (by simp [h3]) hlt
    exact BitVec.lt_def.mp h2
  have hi1' : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rw_cv_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_ite_case
  · wpc_auto; rw_cv_done
  apply WPC.skip; wpc_simp
  wpc_auto
  refine ⟨by simp only [envU32, Env.get, String.reduceEq, ↓reduceIte]; omega, i + 1#32, _, _, rfl, by omega,
    by omega, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
  · cost_clean; cost_arith
  · cost_clean; cost_arith


fncost_register "r_rewrite" rRewrite r_rewrite_cost

end Vbcf.Proof
