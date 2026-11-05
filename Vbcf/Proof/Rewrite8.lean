import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite7

/-!
# Vbcf proofs: the Rewrite family, part 8 — `rw_inst`: the `RW_APP` case, and `rw_inst_spec`

The arguments of an operator are instantiated one by one (`instA`), each spliced onto the
scratch stack above the entry `sp`, and the node is built by `rw_app`; `sp` is then restored.
The loop invariant `RwAppInv` keeps the arguments still to do (`rest`), the list on the stack
(`acc`), and the continuation property: whatever `instA` makes of `rest`, `instA` of the whole
argument list is `acc` followed by it.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-- Read a constant through lookup evidence, without reducing the encoded table. -/
theorem rw_eval_cload {P : Prog} {env : Env} {m : Mem} {g : String}
    {tbl : ConstDef} {i : Expr} {q : BitVec 32} {k : Nat} {w : BitVec 32}
    (hfind : P.findConst g = some tbl) (hi : evalE P env m i = some (.u32 q))
    (hk : q.toNat = k) (hw : tbl.words[k]? = some w) :
    evalE P env m (.cload g i) = some (.u32 w) := by
  rw [evalE, hfind, hi]
  simp only [Val.toIdx, hk]
  rw [hw]

/-- Compose argument evaluation from individual expression evaluations. -/
theorem rw_evalArgs_cons {P : Prog} {env : Env} {m : Mem} {e : Expr} {es : List Expr}
    {v : EmbC.Val} {vs : List EmbC.Val} (he : evalE P env m e = some v)
    (hes : evalArgs P env m es = some vs) :
    evalArgs P env m (e :: es) = some (v :: vs) := by
  rw [evalArgs, he, hes]

theorem rw_encA_len_pos (a : RwExpr) (rest : RwArgs) : 0 < (encA (.cons a rest)).length := by
  simp only [encA, List.length_append]
  have := rw_encE_len_pos a
  omega

/-- The loop invariant of the `RW_APP` case. -/
def RwAppInv (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (pos ab : Nat) (args : List Nat) (d : BitVec 32) (op : RwOp) (as : RwArgs) : Env → (KernelState prog State) → Prop :=
  fun env' s' => ∃ (rest : RwArgs) (acc : List Nat) (c' : CMem) (st' : VSt) (pv : Nat)
      (a ok : BitVec 32),
    env' = rwInstEnv sb pos ab args.length d (.app op as) (BitVec.ofNat 32 pv) a 0#32 0#32 c.k.sp ok
      0#32 ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st' ∧ VExt st st' ∧
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧ StkTop c' st' c.k.sp.toNat acc ∧
    RwAt pv (encA rest) ∧ wfA rest = true ∧ pv + (encA rest).length = pos + (encE (.app op as)).length ∧
    (∀ st2 is, instA X.bi args.toArray rest st' = some (st2, is) →
      instA X.bi args.toArray as st = some (st2, acc ++ is))

theorem rw_inst_app (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (op : RwOp) (as : RwArgs) :
    RwInstCase (State := State) d (.app op as) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  have hpl := (rw_head hat hwf).2.2
  simp only [wfE] at hwf
  simp only [encE] at hat hpl
  have hat1 := hat.tail
  have hsp := hR.sp_lt
  simp only [maxPool] at hsp
  apply WP.ite_seq
  rule_simp [tagE, tVar, tApp]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tApp]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tApp]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tApp]
  apply WP.ite_seq
  rule_simp [tagE, tApp]
  rule_assign
  rule_assign
  simp only [List.length_cons] at hpl
  apply WP.loop_seq (RwAppInv W sb X c0 c prems params st pos ab args d op as)
  · refine ⟨as, [], c, st, pos + 1, 0#32, 0#32, rfl, h, hR, VExt.refl st, fun _ _ => rfl,
      StkTop.nil rfl, hat1, hwf, by simp [encE]; omega, fun st2 is h2 => by simpa using h2⟩
  clear h hR
  rintro env s1 ⟨rest, acc, c1, st1, pv, a, ok, rfl, h, hR, hext, hpre, htop, hatr, hwfr, hpv, hcont⟩
  simp only [rwInstEnv]
  have hpv' : pv ≤ pos + (encE (.app op as)).length := by omega
  simp only [encE, List.length_cons] at hpv hpv'
  rule_simp
  have hspc := htop.1
  have hsp1 := hR.sp_lt
  simp only [maxPool] at hsp1
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · simp only [encE, List.length_cons] at hge
    rw [Nat.mod_eq_of_lt (by omega)] at hge
    cases rest with
    | cons e1 r1 =>
      have := rw_encA_len_pos e1 r1
      omega
    | nil =>
    have hA := hcont st1 [] (rw_instA_nil _ _ _)
    simp only [List.append_nil] at hA
    have e3 : c1.k.sp - c.k.sp = BitVec.ofNat 32 acc.length := by
      apply BitVec.eq_of_toNat_eq
      rw [bv_sub_toNat (by omega), bv_toNat_ofNat (by omega)]; omega
    apply WP.rule_hcall (rw_app_spec W sb X c0 c1 prems params st1 op c.k.sp.toNat acc)
      (by rule_simp [e3, auxE, opCode, bv_ofNat_toNat]) ⟨rfl, h, hR, htop⟩
    intro s2 c2 r h2 hB
    rule_simp
    apply WP.seq
    apply WP.ck_setField hs h2 (by rfl)
    ck_simp
    intro s3 h3
    apply WP.ret
    rule_simp [LoopQ, RetQ]
    refine ⟨_, h3, ?_⟩
    rcases hB with rfl | ⟨st2, i, hP, hR2, hext2, hs2, hi, rfl⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨st2, i, ?_, hR2.set_sp c.k.sp (by rw [hs2.2]; omega), hext.trans hext2, rfl,
        fun j hj => ?_, hi, rfl⟩
      · rw [rw_instE_app, hA]; exact hP
      · simp only; rw [hs2.1]; exact hpre j hj
  · simp only [encE, List.length_cons] at hlt
    rw [Nat.mod_eq_of_lt (by omega)] at hlt
    cases rest with
    | nil => simp [encA] at hpv; omega
    | cons e1 r1 =>
    simp only [encA, wfA, Bool.and_eq_true] at hatr hwfr hpv
    obtain ⟨hw1, hwr⟩ := hwfr
    have hat1' := hatr.left
    have hatr' := hatr.right
    simp only [List.length_append] at hpv
    obtain ⟨H1, hH1, hH1', -⟩ := rw_next hat1' hw1
    have hargs1 : RwArgsAt c1 st1 ab args := hargs.frame hext (by omega) hpre
    apply WP.call_seq (IH W sb X c0 c1 prems params st1 e1 pv ab args) (by rule_simp)
      ⟨rfl, h, hR, hat1', hw1, hargs1⟩
    rintro rv s2 ⟨r2, rfl, c2, h2, hB2⟩
    rule_simp
    apply WP.rw_guard (RwInstR.fail h2)
    rule_simp
    intro hne
    obtain ⟨st2, i2, hP2, hR2, hext2, hsp2, hpre2, hi2, rfl⟩ := hB2.resolve_left hne
    clear h hR
    have h := h2
    have hR := hR2
    apply WP.call_seq (rw_splice_spec W sb X c0 c2 prems params st2 i2) (by rule_simp)
      ⟨rfl, h, hR, hi2⟩
    rintro rv s3 ⟨ok3, rfl, c3, h3, hR3, hpre3, hok3⟩
    clear h hR
    have h := h3
    have hR := hR3
    rule_simp
    apply WP.rw_guard (RwInstR.fail h)
    rule_simp
    intro hok
    obtain ⟨items, hsplice, hsp3, hids3⟩ := hok3 hok
    apply WP.assign_loop
    rw [rw_eval_next_u32 rw_findConst (by rfl) (by
      rw [bv_toNat_ofNat (by omega)]
      exact hH1)]
    rule_simp [hH1']
    have htop2 : StkTop c2 st2 c.k.sp.toNat acc :=
      ⟨by rw [hsp2]; exact htop.1,
        (htop.2.frame (fun j hj => hpre2 j (by rw [htop.1]; omega))).ext hext2 rfl⟩
    have htop3 := htop2.append hpre3 hsp3 (by rw [hsp2] at hids3 ⊢; exact hids3)
    refine ⟨r1, acc ++ items, c3, st2, pv + (encE e1).length, _, _, rfl, h, hR, hext.trans hext2,
      fun j hj => ?_, htop3, hatr', hwr, by simp [encE]; omega, fun st4 is h4 => ?_⟩
    · rw [hpre3 j (by rw [hsp2]; omega), hpre2 j (by omega), hpre j hj]
    · have := hcont st4 (items ++ is) (by rw [rw_instA_cons, hP2]; simp only; rw [hsplice]; simp only; rw [h4])
      rw [this, List.append_assoc]

/-! ## `rw_inst` -/

theorem rw_inst_specD (d : BitVec 32) (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → RwInstSpecD (State := State) d') :
    RwInstSpecD (State := State) d := by
  apply rw_inst_of_cases d
  intro hd e
  have hd1 : (d - 1#32).toNat < d.toNat := by
    have : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [bv_sub_toNat (by simp; omega)]; simp; omega
  have IH' := IH _ hd1
  cases e with
  | var i => exact rw_inst_var d i
  | tt => exact rw_inst_tt d
  | ff => exact rw_inst_ff d
  | lit v => exact rw_inst_lit d v
  | symVal a b => exact rw_inst_symVal d IH' a b
  | bvmax a => exact rw_inst_bvmax d IH' a
  | app op as => exact rw_inst_app d IH' op as
  | ite a b c => exact rw_inst_ite d IH' a b c
  | extract a b c => exact rw_inst_extract d IH' a b c
  | zext a b => exact rw_inst_zext d IH' a b
  | sext a b => exact rw_inst_sext d IH' a b
  | «repeat» a b => exact rw_inst_repeat d IH' a b

/-- **`rw_inst` is `instE`** (for a pattern of the table, any depth). -/
theorem rw_inst_spec : RwInstSpec (State := State) := by
  intro d
  induction h : d.toNat using Nat.strongRecOn generalizing d with
  | _ n ih => exact rw_inst_specD d (fun d' hd' => ih d'.toNat (h ▸ hd') d' rfl)

end Vbcf.Proof
