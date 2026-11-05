import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast9

/-!
# Vbcf proofs: the Bitblast family, part 10 — `bb_shift`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Lean side -/

theorem bb_mapIdx_length {f : Nat → Nat → Option Nat} :
    ∀ {j : Nat} {xs L : List Nat}, bbMapIdx f j xs = some L → L.length = xs.length
  | _, [], L, h => by simp [bbMapIdx] at h; simp [← h]
  | j, x :: xs, L, h => by
    simp only [bbMapIdx] at h
    split at h
    · rename_i y ys hy hys
      simp only [Option.some.injEq] at h
      subst h
      simp [bb_mapIdx_length hys]
    · cases h

theorem bb_lsh_length {st : St} {b T : Nat} {res L : List Nat}
    (h : Bcf.bbLshStage st b T res = some L) : L.length = res.length := by
  unfold Bcf.bbLshStage at h
  split at h
  · rename_i pre hm
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact bb_mapIdx_length hm
    · cases h
  · cases h

theorem bb_rsh_length {st : St} {isFill : Nat → Bool} {b T : Nat} {res L : List Nat}
    (h : Bcf.bbRshStage st isFill b T res = some L) : L.length = res.length := by
  unfold Bcf.bbRshStage at h
  split at h
  · rename_i pre hm
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact bb_mapIdx_length hm
    · cases h
  · cases h

theorem bb_shiftLimit_length {st : St} {cond : Nat} {isFill : Nat → Bool} :
    ∀ {bs L : List Nat}, Bcf.bbShiftLimit st cond isFill bs = some L → L.length = bs.length
  | [], L, h => by simp [Bcf.bbShiftLimit] at h; simp [← h]
  | b :: bs, L, h => by
    simp only [Bcf.bbShiftLimit] at h
    split at h
    · split at h
      · cases e : Bcf.bbShiftLimit st cond isFill bs with
        | none => rw [e] at h; cases h
        | some L' =>
          rw [e] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
          simp [bb_shiftLimit_length e]
      · cases h
    · cases h

theorem bb_stages_succ {stage : Nat → Nat → List Nat → Option (List Nat)} {ys : List Nat}
    {i : Nat} {R R' : List Nat} (hi : i < ys.length) (hs : stage ys[i] (2 ^ i) R = some R') :
    bbStages stage ys (i + 1) R = bbStages stage ys i R' := by
  simp [bbStages, List.getElem?_eq_getElem hi, hs]

theorem bb_log2_le {n : Nat} (h : n ≤ 256) : Bcf.bbLog2 n ≤ 8 := by
  unfold Bcf.bbLog2
  split
  · omega
  · have := (Nat.log2_lt (n := n - 1) (k := 8) (by omega)).mpr (by simp; omega)
    omega

/-- The three shifts of `bbTerm`, selected by the word `kind`. -/
def BbShiftKind (st : St) (xs : List Nat) (kind : Nat) (isFill : Nat → Bool)
    (stage : Nat → Nat → List Nat → Option (List Nat)) : Prop :=
  (kind = 0 ∧ isFill = isFalseNode st ∧ stage = Bcf.bbLshStage st) ∨
  (kind = 1 ∧ isFill = isFalseNode st ∧ stage = Bcf.bbRshStage st (isFalseNode st)) ∨
  (kind = 2 ∧ isFill = isLastOf xs ∧ stage = Bcf.bbRshStage st (isLastOf xs))

theorem BbShiftKind.length {st : St} {xs : List Nat} {kind : Nat} {isFill : Nat → Bool}
    {stage : Nat → Nat → List Nat → Option (List Nat)} (hk : BbShiftKind st xs kind isFill stage)
    {b T : Nat} {res L : List Nat} (h : stage b T res = some L) : L.length = res.length := by
  rcases hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact bb_lsh_length h
  · exact bb_rsh_length h
  · exact bb_rsh_length h

/-- `x = f(args);` as the last statement of a block, for a helper with a `u32` result. -/
theorem WP.bb_call_last {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {x : Var} {f : String}
    {es : List Expr} {vs : List EmbC.Val} {pre : List EmbC.Val → (KernelState P State) → Prop}
    {R : BitVec 32 → (KernelState P State) → Prop}
    (hspec : FnSpec (State := State) P f pre (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ R r s'))
    (hargs : evalArgs P env s.mem es = some vs) (hpre : pre vs s)
    (H : ∀ s' r, R r s' →
      match env.assign s'.mem x (.u32 r) with
      | none => False
      | some env' => Q .normal env' s') :
    WP P (.call (some x) f es) Q env s := by
  apply WP.call hspec
  rw [hargs]
  refine ⟨hpre, ?_⟩
  rintro rv s' ⟨r, rfl, hr⟩
  exact H s' r hr

/-! ## `bb_shift` -/

/-- What is left of a barrel shifter after the stages below `i`. -/
def bbStagesOK (stage : Nat → Nat → List Nat → Option (List Nat)) (ys xs : List Nat) (i : Nat)
    (R : List Nat) : Bool :=
  match bbStages stage ys i R with
  | some fin => fin == xs
  | none => false

theorem bb_shift_of {st : VSt} {bi : Builtins} {isFill : Nat → Bool}
    {stage : Nat → Nat → List Nat → Option (List Nat)} {xs ys bs L0 : List Nat} {cond t0 e0 : Nat}
    (hb : 0 < bs.length) (hn0 : st.pool[bs[0]]? = some ⟨.boolIte, #[cond, t0, e0]⟩)
    (hult : ultGo st false ys.reverse (bbWidthBits bi xs.length ys.length).reverse cond = true)
    (hsl : Bcf.bbShiftLimit st cond isFill bs = some L0)
    (hst : bbStagesOK stage ys xs (Bcf.bbLog2 xs.length) L0 = true) :
    Bcf.bbShift st bi isFill stage xs ys bs = true := by
  rcases bs with _ | ⟨b0, bs⟩
  · simp at hb
  simp only [List.getElem_cons_zero] at hn0
  unfold bbStagesOK at hst
  simp only [Bcf.bbShift, bb_iteArgs hn0, hult, hsl, Bool.true_and]
  exact hst

/-- Loop invariant of the stage loop of `bb_shift`. -/
def BbShInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (c : CMem) (stage : Nat → Nat → List Nat → Option (List Nat)) (xs ys bs L0 : List Nat)
    (env0 : Env) : Env → (KernelState prog State) → Prop := fun env s3 =>
  ∃ (c3 : CMem) (i resN : Nat) (R : List Nat) (wb' wo' : BitVec 32),
    env = (((env0.set "i" (uv i)).set "bit" (.u32 wb')).set "res" (uv resN)).set "ok" (.u32 wo') ∧
    Holds W s3.mem sb c3 ∧ RCtx W X c0 prems params c3 st ∧
    (∀ j, j < c.k.sp.toNat → c3.stk[j]? = c.stk[j]?) ∧ c.k.sp.toNat ≤ c3.k.sp.toNat ∧
    i ≤ 8 ∧ R.length = bs.length ∧ BbRange c3 st resN R ∧
    (bbStagesOK stage ys xs i R = true → bbStagesOK stage ys xs (Bcf.bbLog2 xs.length) L0 = true)

def BbShiftSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (kind xb yb bsb : Nat) (xs ys bs : List Nat) (isFill : Nat → Bool)
    (stage : Nat → Nat → List Nat → Option (List Nat)),
    FnSpec (State := State) Vbcf.prog "bb_shift"
      (fun vs s => vs = [.ptr sb 0, uv kind, uv xb, uv xs.length, uv yb, uv ys.length, uv bsb,
          uv bs.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st xb xs ∧
        BbRange c st yb ys ∧ BbRange c st bsb bs ∧ xs.length ≤ 255 ∧
        BbShiftKind st xs kind isFill stage)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        BbChk W sb X c0 prems params st c (Bcf.bbShift st X.bi isFill stage xs ys bs = true) r s')

theorem bb_shift_spec : BbShiftSpec (State := State) := by
  intro W sb X c0 c prems params st kind xb yb bsb xs ys bs isFill stage
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbShift) rfl
  rintro vs s ⟨rfl, h, hR, hx, hy, hb, hx255, hkind⟩
  simp [bbShift, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbShift) rfl
  simp only [bbShift, Stmt.block, initLocals, List.map, Ty.zero]
  have hxb := hx.bound hR
  have hyb := hy.bound hR
  have hbb := hb.bound hR
  have hk2 : kind ≤ 2 := by rcases hkind with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  -- arith
  apply WP.seq_mid_env (fun env0 env' s' => s' = s ∧
    env' = env0.set "arith" (uv (if kind = 2 then 1 else 0)))
  · apply WP.ite
    rule_simp
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · apply WP.assign; rule_simp [LoopQ, hk]
    · apply WP.skip; rule_simp [LoopQ, hk]
  rintro env1 s1 ⟨rfl, rfl⟩
  have hfill : BbFill st (if kind = 2 then 1 else 0) xs isFill := by
    rcases hkind with ⟨rfl, hf, -⟩ | ⟨rfl, hf, -⟩ | ⟨rfl, hf, -⟩
    · exact Or.inl ⟨rfl, hf⟩
    · exact Or.inl ⟨rfl, hf⟩
    · exact Or.inr ⟨rfl, hf⟩
  generalize harith : (if kind = 2 then 1 else 0) = arith at hfill ⊢
  have har : arith ≤ 1 := by rw [← harith]; split <;> omega
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp only [RetQ]; exact BbChk.zero h hR, fun hb0 => ?_⟩
  have hb1 : 0 < bs.length := by
    rcases bs with _ | _
    · exact absurd rfl hb0
    · simp
  clear hb0
  have hstk0 := hb.stk hR h hb1
  have eb0 := hb.rd hb1
  simp only [Nat.add_zero] at eb0
  have hb0l := hb.lt hb1
  rule_assign [hstk0, eb0]
  obtain ⟨n0, hn0⟩ := node_of_lv hb0l
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hn0]
  refine ⟨fun _ => by simp only [RetQ]; exact BbChk.zero h hR, fun hh => ?_⟩
  obtain ⟨cond, t0, e0, rfl, hcond, ht0, he0⟩ := hR.core.bb_hdr3 hn0 (op := .boolIte) (by decide)
    (by decide) (by decide) (by decide) hh
  rule_assign [hR.core.rd3 hn0]
  rule_assign
  have htt := hR.tt_lt
  have hff := hR.ff_lt
  have hWl : (bbWidthBits X.bi xs.length ys.length).length = ys.length := by simp [bbWidthBits]
  have hWk : ∀ k (hk : k < ys.length), (bbWidthBits X.bi xs.length ys.length)[k]'(by omega) =
      if xs.length.testBit k then X.bi.tt else X.bi.ff := by
    intro k hk; simp [bbWidthBits]
  apply WP.bb_loop (fun env0 => BbPushInv W sb X c0 prems params st c env0 "i" ["bit", "ok"]
    ys.length (fun k L => L = (bbWidthBits X.bi xs.length ys.length).take k))
  · exact ⟨c, 0, [], [0#32, 0#32], rfl, by simp [bbSets, Env.set], h, hR,
      fun _ _ => rfl, Nat.le_refl _, by omega, by simp, StkTop.nil rfl⟩
  clear h hR
  rintro env s' ⟨c', k, L, ws, hws, rfl, h, hR, hpre, hsp, hk, rfl, htop⟩
  obtain ⟨wbit, wok, rfl⟩ := len_shape 2 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkn : k = ys.length := by omega
    subst hkn
    rw [List.take_of_length_le (by omega)] at htop
    have hy' := hy.frame hpre hsp
    have hx' := hx.frame hpre hsp
    have hb' := hb.frame hpre hsp
    refine WP.bb_call (bb_ult_spec W sb X c0 c' prems params st false yb c.k.sp.toNat cond ys
      (bbWidthBits X.bi xs.length ys.length)) ?_ ⟨rfl, h, hR, hy', htop.bbRange, hcond⟩ ?_
    · rule_simp [hWl]
    intro r1 hr1
    rule_simp
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp only [RetQ]; exact BbChk.zero h hR, fun hr10 => ?_⟩
    refine WP.pl_call (bb_shift_limit_spec W sb X c0 c' prems params st cond arith xb bsb xs bs
      isFill) ?_ ⟨rfl, h, hR, hcond, hx', hb', hfill⟩ ?_
    · rule_simp
    rintro s2 r2 ⟨c2, h2, hR2, hcase2⟩
    bb_swap h2 hR2
    rcases hcase2 with rfl | ⟨rfl, hpre2, hsp2, L0, hL0, htL0⟩
    · rule_simp
      apply WP.guard_lit
      rule_simp [noid]
      exact BbChk.zero h hR
    rule_simp
    apply WP.guard_lit
    rule_simp [hR.bb_ne_noid hsp2]
    apply WP.bb_pure (bb_log2_spec xs.length) (by rule_simp) ⟨rfl, hx255⟩
    rule_simp
    have hlog := bb_log2_le (n := xs.length) (by omega)
    have hpre02 := bb_pre_trans hpre hsp hpre2
    have hk' := hkind
    apply WP.bb_loop (BbShInv W sb X c0 prems params st c stage xs ys bs L0)
    · exact ⟨c2, Bcf.bbLog2 xs.length, c'.k.sp.toNat, L0, wbit, r1, by simp [Env.set], h, hR,
        hpre02, by omega, hlog, bb_shiftLimit_length hL0, htL0.bbRange, id⟩
    rintro env s3 ⟨c3, i, resN, R, wb', wo', rfl, h3, hR3, hpre3, hsp3, hi8, hRl, hRr, hres⟩
    bb_swap h3 hR3
    have hx3 := hx.frame hpre3 hsp3
    have hy3 := hy.frame hpre3 hsp3
    have hRb := hRr.bound hR
    rule_simp
    refine ⟨fun hi0 => ?_, fun hi0 => ?_⟩
    · subst hi0
      refine WP.bb_call (bb_list_eq_spec W sb X c0 c3 prems params st resN xb R xs) ?_
        ⟨rfl, h, hR, hRr, hx3⟩ ?_
      · rule_simp [hRl]
      intro r5 hr5
      rule_simp
      apply WP.rule_ret
      rule_simp
      refine ⟨c3, h, hR, fun hne => ⟨hpre3, hsp3, ?_⟩⟩
      refine bb_shift_of hb1 hn0 (hr1 hr10) hL0 (hres ?_)
      simp [bbStagesOK, bbStages, hr5 hne]
    rule_assign [bb_uv_sub (show i < 2 ^ 32 by omega) (show 1 ≤ i by omega)]
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbChk.zero h hR, fun hiy => ?_⟩
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbChk.zero h hR, fun hi31 => ?_⟩
    have hstky := hy3.stk hR h hiy
    have hyi := hy3.lt hiy
    have hT : 2 ^ (i - 1) < 2147483648 := Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide)
      (show i - 1 < 31 by omega)) (by decide)
    apply WP.seq
    apply WP.ite
    rcases hkind with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rule_simp
    refine WP.bb_call_last (bb_lsh_stage_spec W sb X c0 c3 prems params st ys[i - 1] (2 ^ (i - 1))
      resN R) ?_ ⟨rfl, h, hR, hyi, hT, hRr⟩ ?_
    · rule_simp [hstky, hy3.rd hiy, bb_shl1 (show i - 1 < 31 by omega), hRl, show i - 1 < 32 by omega]
    rotate_left
    refine WP.bb_call_last (bb_rsh_stage_spec W sb X c0 c3 prems params st arith xb ys[i - 1]
      (2 ^ (i - 1)) resN xs R (isFalseNode st)) ?_ ⟨rfl, h, hR, hyi, hT, hx3, hRr, hfill⟩ ?_
    · rule_simp [hstky, hy3.rd hiy, bb_shl1 (show i - 1 < 31 by omega), hRl, show i - 1 < 32 by omega]
    rotate_left
    refine WP.bb_call_last (bb_rsh_stage_spec W sb X c0 c3 prems params st arith xb ys[i - 1]
      (2 ^ (i - 1)) resN xs R (isLastOf xs)) ?_ ⟨rfl, h, hR, hyi, hT, hx3, hRr, hfill⟩ ?_
    · rule_simp [hstky, hy3.rd hiy, bb_shl1 (show i - 1 < 31 by omega), hRl, show i - 1 < 32 by omega]
    all_goals
      rintro s4 r4 ⟨c4, h4, hR4, hcase4⟩
      bb_swap h4 hR4
      rule_simp
      apply WP.ite
      rcases hcase4 with rfl | ⟨rfl, hpre4, hsp4, L, hL, htL⟩
      · rule_simp [noid]
        apply WP.ret
        simp only [evalE, LoopQ, RetQ]
        exact BbChk.zero h hR
      rule_simp [hR.bb_ne_noid hsp4]
      apply WP.skip
      simp only [LoopQ]
      refine ⟨c4, i - 1, c3.k.sp.toNat, L, wb', wo', by simp [Env.set], h, hR,
        bb_pre_trans hpre3 hsp3 hpre4, by omega, by omega, by rw [hk'.length hL, hRl],
        htL.bbRange, fun H => hres ?_⟩
      have e := bb_stages_succ (stage := _) (ys := ys) (i := i - 1) (R := R) hiy hL
      rw [show i - 1 + 1 = i by omega] at e
      unfold bbStagesOK at H ⊢
      rw [e]; exact H
  rule_assign
  apply WP.seq_mid_env (fun env0 env' s'' => s'' = s' ∧
    env' = env0.set "bit" (.u32 (if xs.length.testBit k then 1#32 else 0#32)))
  · apply WP.ite
    rule_simp
    refine ⟨fun hk32 => ?_, fun hk32 => ?_⟩
    · apply WP.assign
      rule_simp [bb_bit_word (show xs.length < 2 ^ 32 by omega) hk32, LoopQ, hk32]
    · apply WP.skip
      rule_simp [LoopQ, bb_testBit_big (v := xs.length) (k := k) (w := 8) (by omega) (by omega)]
  rintro env' s'' ⟨rfl, rfl⟩
  have key : ∀ (p : Nat), st.lv p → p = (if xs.length.testBit k then X.bi.tt else X.bi.ff) →
      ∀ (s2 : KernelState prog State) c2 ok, Holds W s2.mem sb c2 →
      Pushed W X c0 prems params st c' (BitVec.ofNat 32 (st.id p)) c2 ok →
      WP Vbcf.prog (.seq (.ite (.bin .eq (.var "ok") (.lit32 0#32)) (.ret (some (.lit32 0#32))) .skip)
          (.assign "i" (.bin .add (.var "i") (.lit32 1#32))))
        (LoopQ (BbPushInv W sb X c0 prems params st c
          [("st", (Ty.struct "ck").ptr, Val.ptr sb 0), ("kind", Ty.u32, uv kind), ("xb", Ty.u32, uv xb),
            ("nx", Ty.u32, uv xs.length), ("yb", Ty.u32, uv yb), ("ny", Ty.u32, uv ys.length),
            ("bsb", Ty.u32, uv bsb), ("nb", Ty.u32, uv bs.length), ("arith", Ty.u32, uv arith),
            ("b0", Ty.u32, uv (st.id bs[0])), ("cond", Ty.u32, uv (st.id cond)),
            ("wb", Ty.u32, Val.u32 c.k.sp), ("i", Ty.u32, Val.u32 0#32), ("bit", Ty.u32, Val.u32 0#32),
            ("res", Ty.u32, Val.u32 0#32), ("ok", Ty.u32, Val.u32 0#32)]
          "i" ["bit", "ok"] ys.length (fun k L => L = (bbWidthBits X.bi xs.length ys.length).take k))
          (RetQ (BbChk W sb X c0 prems params st c (Bcf.bbShift st X.bi isFill stage xs ys bs = true))))
        [("st", (Ty.struct "ck").ptr, Val.ptr sb 0), ("kind", Ty.u32, uv kind), ("xb", Ty.u32, uv xb),
          ("nx", Ty.u32, uv xs.length), ("yb", Ty.u32, uv yb), ("ny", Ty.u32, uv ys.length),
          ("bsb", Ty.u32, uv bsb), ("nb", Ty.u32, uv bs.length), ("arith", Ty.u32, uv arith),
          ("b0", Ty.u32, uv (st.id bs[0])), ("cond", Ty.u32, uv (st.id cond)),
          ("wb", Ty.u32, Val.u32 c.k.sp), ("i", Ty.u32, uv k),
          ("bit", Ty.u32, Val.u32 (if xs.length.testBit k then 1#32 else 0#32)),
          ("res", Ty.u32, Val.u32 0#32), ("ok", Ty.u32, Val.u32 ok)] s2 := by
    intro p hp hpv s2 c2 ok hh2 hP
    obtain ⟨hpre2, hsp2⟩ := hP.bb_pre
    have hpre' : ∀ j, j < c.k.sp.toNat → c2.stk[j]? = c.stk[j]? := fun j hj => by
      rw [hpre2 j (by omega), hpre j hj]
    have h := hh2
    have hR := hP.1
    apply WP.guard_lit
    rule_simp
    refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbChk.zero h hR, fun hok => ?_⟩
    obtain ⟨htop2, -⟩ := hP.bb hok htop hp
    apply WP.assign_loop
    rule_simp
    refine ⟨c2, k + 1, _, [if xs.length.testBit k then 1#32 else 0#32, ok], rfl,
      by simp [bbSets, Env.set], h, hR, hpre', by omega, by omega, rfl, ?_⟩
    rw [List.take_succ_eq_append_getElem (by omega), hWk k hlt, ← hpv]
    exact htop2
  apply WP.seq
  apply WP.ite
  by_cases hbit : xs.length.testBit k
  · rule_simp [hbit]
    apply WP.bb_push_last h hR
    rule_simp
    intro s2 c2 ok hh2 hP
    have := key X.bi.tt htt (by simp [hbit]) s2 c2 ok hh2 hP
    simpa [hbit] using this
  · rule_simp [hbit]
    apply WP.bb_push_last h hR
    rule_simp
    intro s2 c2 ok hh2 hP
    have := key X.bi.ff hff (by simp [hbit]) s2 c2 ok hh2 hP
    simpa [hbit] using this

end Vbcf.Proof
