import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite6

/-!
# Vbcf proofs: the Rewrite family, part 7 — `rw_inst`: the cases with sub-patterns

`bvmax`, `symVal`, `zext`/`sext`/`repeat`, `ite`, `extract`: the sub-patterns are
instantiated by recursive calls (at depth `d - 1`), then a helper of `Rewrite4` builds the node.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-- Evaluate a rewrite-table advance through lookup evidence, keeping the table
abstract so the kernel does not normalize the complete encoded array. -/
theorem rw_eval_next_u32 {P : Prog} {env : Env} {m : Mem} {tbl : ConstDef}
    {v H : BitVec 32} (hfind : P.findConst "rw_tbl" = some tbl)
    (hy : env.get "p" = some (.u32 v)) (hw : tbl.words[v.toNat]? = some H) :
    evalE P env m (.bin .add (.var "p")
      (.bin .shr (.cload "rw_tbl" (.var "p")) (.lit32 16#32))) =
        some (.u32 (v + (H >>> 16))) := by
  have hread : evalE P env m (.cload "rw_tbl" (.var "p")) = some (.u32 H) := by
    rw [evalE, hfind, evalE, hy]
    simp only [Val.toIdx]
    rw [hw]
  rw [evalE, evalE, hy, evalE, hread, evalE]
  rfl

/-- The header word of the sub-pattern at `p`, and its length field. -/
theorem rw_next {p : Nat} {e : RwExpr} (hat : RwAt p (encE e)) (hwf : wfE e = true) :
    ∃ H, rwTblDef.words[p]? = some (BitVec.ofNat 32 H) ∧
      BitVec.ofNat 32 H >>> 16 = BitVec.ofNat 32 (encE e).length ∧ p + (encE e).length < 65536 := by
  obtain ⟨hw, hl, hpl⟩ := rw_head hat hwf
  have htg := rw_tagE_lt e
  have hax := rw_auxE_lt hwf
  exact ⟨_, rw_tbl_get hw, rw_hdr_len (show tagE e < 256 by omega) hax hl, hpl⟩

theorem rw_instE_zext (bi : Builtins) (args : Array Nat) (st : VSt) (e x : RwExpr) :
    instE bi args (.zext e x) st = match instE bi args e st with
      | some (st1, k) =>
        match instE bi args x st1 with
        | some (st2, xi) => rwExtTail st2 9 k xi
        | none => none
      | none => none := rw_instE_ext bi args st 9 e x (by decide)

theorem rw_instE_sext (bi : Builtins) (args : Array Nat) (st : VSt) (e x : RwExpr) :
    instE bi args (.sext e x) st = match instE bi args e st with
      | some (st1, k) =>
        match instE bi args x st1 with
        | some (st2, xi) => rwExtTail st2 10 k xi
        | none => none
      | none => none := rw_instE_ext bi args st 10 e x (by decide)

theorem rw_instE_repeat (bi : Builtins) (args : Array Nat) (st : VSt) (e x : RwExpr) :
    instE bi args (.repeat e x) st = match instE bi args e st with
      | some (st1, k) =>
        match instE bi args x st1 with
        | some (st2, xi) => rwExtTail st2 11 k xi
        | none => none
      | none => none := rw_instE_ext bi args st 11 e x (by decide)

theorem rw_inst_bvmax (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (sz : RwExpr) :
    RwInstCase (State := State) d (.bvmax sz) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  simp only [wfE] at hwf
  have hwf1 := hwf
  have hpl := (rw_head hat (by simp [wfE, hwf1])).2.2
  simp only [encE] at hat hpl
  have hat1 := hat.tail
  simp only [List.length_cons] at hpl
  apply WP.ite_seq
  rule_simp [tagE, tVar, tBvmax]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tBvmax]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tBvmax]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tBvmax]
  apply WP.ite_seq
  rule_simp [tagE, tApp, tBvmax]
  rule_assign
  apply WP.call_seq (IH W sb X c0 c prems params st _ (pos + 1) ab args) (by rule_simp)
    ⟨rfl, h, hR, hat1, hwf1, hargs⟩
  rintro rv s1 ⟨r1, rfl, c1, h1, hB1⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h1)
  rule_simp
  intro hne1
  obtain ⟨st1, i1, hP1, hR1, hext1, hsp1, hpre1, hi1, rfl⟩ := hB1.resolve_left hne1
  clear h hR
  have h := h1
  have hR := hR1
  apply WP.ite_seq
  rule_simp [tagE, tBvmax]
  apply WP.rule_hcall (rw_max_spec W sb X c0 c1 prems params st1 i1) (by rule_simp) ⟨rfl, h, hR, hi1⟩
  intro s3 c3 r h3 hB3
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  refine ⟨c3, h3, RwB.trans hext1 hsp1 hpre1 hB3.rwB (fun st' i hP => ?_)⟩
  rw [rw_instE_bvmax, hP1]
  exact hP

theorem rw_inst_symVal (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (val sz : RwExpr) :
    RwInstCase (State := State) d (.symVal val sz) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  simp only [wfE, Bool.and_eq_true] at hwf
  obtain ⟨hwf1, hwf2⟩ := hwf
  have hpl := (rw_head hat (by simp [wfE, hwf1, hwf2])).2.2
  simp only [encE] at hat hpl
  have hat1 := hat.tail.left
  have hat2 := hat.tail.right
  simp only [List.length_cons, List.length_append] at hpl
  obtain ⟨H1, hH1, hH1', -⟩ := rw_next hat1 hwf1
  apply WP.ite_seq
  rule_simp [tagE, tVar, tSymVal]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tSymVal]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tSymVal]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tSymVal]
  apply WP.ite_seq
  rule_simp [tagE, tApp, tSymVal]
  rule_assign
  apply WP.call_seq (IH W sb X c0 c prems params st _ (pos + 1) ab args) (by rule_simp)
    ⟨rfl, h, hR, hat1, hwf1, hargs⟩
  rintro rv s1 ⟨r1, rfl, c1, h1, hB1⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h1)
  rule_simp
  intro hne1
  obtain ⟨st1, i1, hP1, hR1, hext1, hsp1, hpre1, hi1, rfl⟩ := hB1.resolve_left hne1
  clear h hR
  have h := h1
  have hR := hR1
  apply WP.ite_seq
  rule_simp [tagE, tBvmax, tSymVal]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH1)]
  rule_simp [hH1']
  have hargs1 := hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1
  apply WP.call_seq (IH W sb X c0 c1 prems params st1 _ (pos + 1 + (encE _).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat2, hwf2, hargs1⟩
  rintro rv s2 ⟨r2, rfl, c2, h2, hB2⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h2)
  rule_simp
  intro hne2
  obtain ⟨st2, i2, hP2, hR2, hext2, hsp2, hpre2, hi2, rfl⟩ := hB2.resolve_left hne2
  clear h hR
  have h := h2
  have hR := hR2
  have hi1' := hext2.lt hi1
  rw [← hext2.id hi1]
  apply WP.ite_seq
  rule_simp [tagE, tSymVal]
  apply WP.rule_hcall (rw_sym_spec W sb X c0 c2 prems params st2 i1 i2) (by rule_simp)
    ⟨rfl, h, hR, hi1', hi2⟩
  intro s3 c3 r h3 hB3
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  refine ⟨c3, h3, RwB.trans hext1 hsp1 hpre1 (RwB.trans hext2 hsp2 hpre2 hB3.rwB (fun st' i hP => hP))
    (fun st' i hP => ?_)⟩
  rw [rw_instE_symVal, hP1]
  simp only
  rw [hP2]
  exact hP

theorem rw_inst_zext (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (e x : RwExpr) :
    RwInstCase (State := State) d (.zext e x) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  simp only [wfE, Bool.and_eq_true] at hwf
  obtain ⟨hwf1, hwf2⟩ := hwf
  have hpl := (rw_head hat (by simp [wfE, hwf1, hwf2])).2.2
  simp only [encE] at hat hpl
  have hat1 := hat.tail.left
  have hat2 := hat.tail.right
  simp only [List.length_cons, List.length_append] at hpl
  obtain ⟨H1, hH1, hH1', -⟩ := rw_next hat1 hwf1
  apply WP.ite_seq
  rule_simp [tagE, tVar, tZext]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tZext]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tZext]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tZext]
  apply WP.ite_seq
  rule_simp [tagE, tApp, tZext]
  rule_assign
  apply WP.call_seq (IH W sb X c0 c prems params st _ (pos + 1) ab args) (by rule_simp)
    ⟨rfl, h, hR, hat1, hwf1, hargs⟩
  rintro rv s1 ⟨r1, rfl, c1, h1, hB1⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h1)
  rule_simp
  intro hne1
  obtain ⟨st1, i1, hP1, hR1, hext1, hsp1, hpre1, hi1, rfl⟩ := hB1.resolve_left hne1
  clear h hR
  have h := h1
  have hR := hR1
  apply WP.ite_seq
  rule_simp [tagE, tBvmax, tZext]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH1)]
  rule_simp [hH1']
  have hargs1 := hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1
  apply WP.call_seq (IH W sb X c0 c1 prems params st1 _ (pos + 1 + (encE _).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat2, hwf2, hargs1⟩
  rintro rv s2 ⟨r2, rfl, c2, h2, hB2⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h2)
  rule_simp
  intro hne2
  obtain ⟨st2, i2, hP2, hR2, hext2, hsp2, hpre2, hi2, rfl⟩ := hB2.resolve_left hne2
  clear h hR
  have h := h2
  have hR := hR2
  have hi1' := hext2.lt hi1
  rw [← hext2.id hi1]
  apply WP.ite_seq
  rule_simp [tagE, tSymVal, tZext]
  apply WP.ite_seq
  rule_simp [tagE, tZext, tSext, tRepeat]
  apply WP.rule_hcall (rw_ext_spec W sb X c0 c2 prems params st2 9 i1 i2) (by rule_simp [tagE, tZext])
    ⟨rfl, h, hR, hi1', hi2, by decide⟩
  intro s3 c3 r h3 hB3
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  refine ⟨c3, h3, RwB.trans hext1 hsp1 hpre1 (RwB.trans hext2 hsp2 hpre2 hB3.rwB (fun st' i hP => hP))
    (fun st' i hP => ?_)⟩
  have e0 := rw_instE_zext X.bi args.toArray st e x
  rw [e0, hP1]
  simp only
  rw [hP2]
  exact hP

theorem rw_inst_sext (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (e x : RwExpr) :
    RwInstCase (State := State) d (.sext e x) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  simp only [wfE, Bool.and_eq_true] at hwf
  obtain ⟨hwf1, hwf2⟩ := hwf
  have hpl := (rw_head hat (by simp [wfE, hwf1, hwf2])).2.2
  simp only [encE] at hat hpl
  have hat1 := hat.tail.left
  have hat2 := hat.tail.right
  simp only [List.length_cons, List.length_append] at hpl
  obtain ⟨H1, hH1, hH1', -⟩ := rw_next hat1 hwf1
  apply WP.ite_seq
  rule_simp [tagE, tVar, tSext]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tSext]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tSext]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tSext]
  apply WP.ite_seq
  rule_simp [tagE, tApp, tSext]
  rule_assign
  apply WP.call_seq (IH W sb X c0 c prems params st _ (pos + 1) ab args) (by rule_simp)
    ⟨rfl, h, hR, hat1, hwf1, hargs⟩
  rintro rv s1 ⟨r1, rfl, c1, h1, hB1⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h1)
  rule_simp
  intro hne1
  obtain ⟨st1, i1, hP1, hR1, hext1, hsp1, hpre1, hi1, rfl⟩ := hB1.resolve_left hne1
  clear h hR
  have h := h1
  have hR := hR1
  apply WP.ite_seq
  rule_simp [tagE, tBvmax, tSext]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH1)]
  rule_simp [hH1']
  have hargs1 := hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1
  apply WP.call_seq (IH W sb X c0 c1 prems params st1 _ (pos + 1 + (encE _).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat2, hwf2, hargs1⟩
  rintro rv s2 ⟨r2, rfl, c2, h2, hB2⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h2)
  rule_simp
  intro hne2
  obtain ⟨st2, i2, hP2, hR2, hext2, hsp2, hpre2, hi2, rfl⟩ := hB2.resolve_left hne2
  clear h hR
  have h := h2
  have hR := hR2
  have hi1' := hext2.lt hi1
  rw [← hext2.id hi1]
  apply WP.ite_seq
  rule_simp [tagE, tSymVal, tSext]
  apply WP.ite_seq
  rule_simp [tagE, tZext, tSext, tRepeat]
  apply WP.rule_hcall (rw_ext_spec W sb X c0 c2 prems params st2 10 i1 i2) (by rule_simp [tagE, tSext])
    ⟨rfl, h, hR, hi1', hi2, by decide⟩
  intro s3 c3 r h3 hB3
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  refine ⟨c3, h3, RwB.trans hext1 hsp1 hpre1 (RwB.trans hext2 hsp2 hpre2 hB3.rwB (fun st' i hP => hP))
    (fun st' i hP => ?_)⟩
  have e0 := rw_instE_sext X.bi args.toArray st e x
  rw [e0, hP1]
  simp only
  rw [hP2]
  exact hP

theorem rw_inst_repeat (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (e x : RwExpr) :
    RwInstCase (State := State) d (.repeat e x) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  simp only [wfE, Bool.and_eq_true] at hwf
  obtain ⟨hwf1, hwf2⟩ := hwf
  have hpl := (rw_head hat (by simp [wfE, hwf1, hwf2])).2.2
  simp only [encE] at hat hpl
  have hat1 := hat.tail.left
  have hat2 := hat.tail.right
  simp only [List.length_cons, List.length_append] at hpl
  obtain ⟨H1, hH1, hH1', -⟩ := rw_next hat1 hwf1
  apply WP.ite_seq
  rule_simp [tagE, tVar, tRepeat]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tRepeat]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tRepeat]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tRepeat]
  apply WP.ite_seq
  rule_simp [tagE, tApp, tRepeat]
  rule_assign
  apply WP.call_seq (IH W sb X c0 c prems params st _ (pos + 1) ab args) (by rule_simp)
    ⟨rfl, h, hR, hat1, hwf1, hargs⟩
  rintro rv s1 ⟨r1, rfl, c1, h1, hB1⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h1)
  rule_simp
  intro hne1
  obtain ⟨st1, i1, hP1, hR1, hext1, hsp1, hpre1, hi1, rfl⟩ := hB1.resolve_left hne1
  clear h hR
  have h := h1
  have hR := hR1
  apply WP.ite_seq
  rule_simp [tagE, tBvmax, tRepeat]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH1)]
  rule_simp [hH1']
  have hargs1 := hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1
  apply WP.call_seq (IH W sb X c0 c1 prems params st1 _ (pos + 1 + (encE _).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat2, hwf2, hargs1⟩
  rintro rv s2 ⟨r2, rfl, c2, h2, hB2⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h2)
  rule_simp
  intro hne2
  obtain ⟨st2, i2, hP2, hR2, hext2, hsp2, hpre2, hi2, rfl⟩ := hB2.resolve_left hne2
  clear h hR
  have h := h2
  have hR := hR2
  have hi1' := hext2.lt hi1
  rw [← hext2.id hi1]
  apply WP.ite_seq
  rule_simp [tagE, tSymVal, tRepeat]
  apply WP.ite_seq
  rule_simp [tagE, tZext, tSext, tRepeat]
  apply WP.rule_hcall (rw_ext_spec W sb X c0 c2 prems params st2 11 i1 i2) (by rule_simp [tagE, tRepeat])
    ⟨rfl, h, hR, hi1', hi2, by decide⟩
  intro s3 c3 r h3 hB3
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  refine ⟨c3, h3, RwB.trans hext1 hsp1 hpre1 (RwB.trans hext2 hsp2 hpre2 hB3.rwB (fun st' i hP => hP))
    (fun st' i hP => ?_)⟩
  have e0 := rw_instE_repeat X.bi args.toArray st e x
  rw [e0, hP1]
  simp only
  rw [hP2]
  exact hP

theorem rw_inst_ite (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (e1 e2 e3 : RwExpr) :
    RwInstCase (State := State) d (.ite e1 e2 e3) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  simp only [wfE, Bool.and_eq_true] at hwf
  obtain ⟨⟨hwf1, hwf2⟩, hwf3⟩ := hwf
  have hpl := (rw_head hat (by simp [wfE, hwf1, hwf2, hwf3])).2.2
  simp only [encE] at hat hpl
  have hat1 := hat.tail.left.left
  have hat2 := hat.tail.left.right
  have hat3 : RwAt (pos + 1 + (encE e1).length + (encE e2).length) (encE e3) := by
    have := hat.tail.right; simp only [List.length_append, ← Nat.add_assoc] at this; exact this
  simp only [List.length_cons, List.length_append] at hpl
  obtain ⟨H1, hH1, hH1', -⟩ := rw_next hat1 hwf1
  obtain ⟨H2, hH2, hH2', -⟩ := rw_next hat2 hwf2
  apply WP.ite_seq
  rule_simp [tagE, tVar, tIte]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tIte]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tIte]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tIte]
  apply WP.ite_seq
  rule_simp [tagE, tApp, tIte]
  rule_assign
  apply WP.call_seq (IH W sb X c0 c prems params st _ (pos + 1) ab args) (by rule_simp)
    ⟨rfl, h, hR, hat1, hwf1, hargs⟩
  rintro rv s1 ⟨r1, rfl, c1, h1, hB1⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h1)
  rule_simp
  intro hne1
  obtain ⟨st1, i1, hP1, hR1, hext1, hsp1, hpre1, hi1, rfl⟩ := hB1.resolve_left hne1
  clear h hR
  have h := h1
  have hR := hR1
  apply WP.ite_seq
  rule_simp [tagE, tBvmax, tIte]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH1)]
  rule_simp [hH1']
  have hargs1 := hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1
  apply WP.call_seq (IH W sb X c0 c1 prems params st1 _ (pos + 1 + (encE _).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat2, hwf2, hargs1⟩
  rintro rv s2 ⟨r2, rfl, c2, h2, hB2⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h2)
  rule_simp
  intro hne2
  obtain ⟨st2, i2, hP2, hR2, hext2, hsp2, hpre2, hi2, rfl⟩ := hB2.resolve_left hne2
  clear h hR
  have h := h2
  have hR := hR2
  have hi1' := hext2.lt hi1
  rw [← hext2.id hi1]
  apply WP.ite_seq
  rule_simp [tagE, tSymVal, tIte]
  apply WP.ite_seq
  rule_simp [tagE, tZext, tSext, tRepeat, tIte]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH2)]
  rule_simp [hH2']
  have hargs2 := (hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1).frame hext2
    (by rw [hsp2]; exact Nat.le_refl _) hpre2
  apply WP.call_seq (IH W sb X c0 c2 prems params st2 e3
    (pos + 1 + (encE e1).length + (encE e2).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat3, hwf3, hargs2⟩
  rintro rv s3 ⟨r3, rfl, c3, h3, hB3⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h3)
  rule_simp
  intro hne3
  obtain ⟨st3, i3, hP3, hR3, hext3, hsp3, hpre3, hi3, rfl⟩ := hB3.resolve_left hne3
  clear h hR
  have h := h3
  have hR := hR3
  have hi1'' := hext3.lt hi1'
  have hi2' := hext3.lt hi2
  rw [← hext3.id hi1', ← hext3.id hi2]
  apply WP.ite_seq
  rule_simp [tagE, tIte, tIte]
  apply WP.rule_hcall (rw_ite_spec W sb X c0 c3 prems params st3 i1 i2 i3) (by rule_simp)
    ⟨rfl, h, hR, hi1'', hi2', hi3⟩
  intro s4 c4 r h4 hB4
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  refine ⟨c4, h4, RwB.trans hext1 hsp1 hpre1 (RwB.trans hext2 hsp2 hpre2
    (RwB.trans hext3 hsp3 hpre3 hB4.rwB (fun st' i hP => hP)) (fun st' i hP => hP))
    (fun st' i hP => ?_)⟩
  rw [rw_instE_ite, hP1]
  simp only
  rw [hP2]
  simp only
  rw [hP3]
  exact hP

theorem rw_inst_extract (d : BitVec 32) (IH : RwInstSpecD (State := State) (d - 1#32)) (e1 e2 e3 : RwExpr) :
    RwInstCase (State := State) d (.extract e1 e2 e3) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  simp only [wfE, Bool.and_eq_true] at hwf
  obtain ⟨⟨hwf1, hwf2⟩, hwf3⟩ := hwf
  have hpl := (rw_head hat (by simp [wfE, hwf1, hwf2, hwf3])).2.2
  simp only [encE] at hat hpl
  have hat1 := hat.tail.left.left
  have hat2 := hat.tail.left.right
  have hat3 : RwAt (pos + 1 + (encE e1).length + (encE e2).length) (encE e3) := by
    have := hat.tail.right; simp only [List.length_append, ← Nat.add_assoc] at this; exact this
  simp only [List.length_cons, List.length_append] at hpl
  obtain ⟨H1, hH1, hH1', -⟩ := rw_next hat1 hwf1
  obtain ⟨H2, hH2, hH2', -⟩ := rw_next hat2 hwf2
  apply WP.ite_seq
  rule_simp [tagE, tVar, tExtract]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tExtract]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tExtract]
  apply WP.ite_seq
  rule_simp [tagE, tLit, tExtract]
  apply WP.ite_seq
  rule_simp [tagE, tApp, tExtract]
  rule_assign
  apply WP.call_seq (IH W sb X c0 c prems params st _ (pos + 1) ab args) (by rule_simp)
    ⟨rfl, h, hR, hat1, hwf1, hargs⟩
  rintro rv s1 ⟨r1, rfl, c1, h1, hB1⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h1)
  rule_simp
  intro hne1
  obtain ⟨st1, i1, hP1, hR1, hext1, hsp1, hpre1, hi1, rfl⟩ := hB1.resolve_left hne1
  clear h hR
  have h := h1
  have hR := hR1
  apply WP.ite_seq
  rule_simp [tagE, tBvmax, tExtract]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH1)]
  rule_simp [hH1']
  have hargs1 := hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1
  apply WP.call_seq (IH W sb X c0 c1 prems params st1 _ (pos + 1 + (encE _).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat2, hwf2, hargs1⟩
  rintro rv s2 ⟨r2, rfl, c2, h2, hB2⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h2)
  rule_simp
  intro hne2
  obtain ⟨st2, i2, hP2, hR2, hext2, hsp2, hpre2, hi2, rfl⟩ := hB2.resolve_left hne2
  clear h hR
  have h := h2
  have hR := hR2
  have hi1' := hext2.lt hi1
  rw [← hext2.id hi1]
  apply WP.ite_seq
  rule_simp [tagE, tSymVal, tExtract]
  apply WP.ite_seq
  rule_simp [tagE, tZext, tSext, tRepeat, tExtract]
  apply WP.assign_seq
  rw [rw_eval_next_u32 rw_findConst (by rfl) (by
    rw [bv_toNat_ofNat (by omega)]
    exact hH2)]
  rule_simp [hH2']
  have hargs2 := (hargs.frame hext1 (by rw [hsp1]; exact Nat.le_refl _) hpre1).frame hext2
    (by rw [hsp2]; exact Nat.le_refl _) hpre2
  apply WP.call_seq (IH W sb X c0 c2 prems params st2 e3
    (pos + 1 + (encE e1).length + (encE e2).length) ab args)
    (by rule_simp) ⟨rfl, h, hR, hat3, hwf3, hargs2⟩
  rintro rv s3 ⟨r3, rfl, c3, h3, hB3⟩
  rule_simp
  apply WP.rw_guard (RwInstR.fail h3)
  rule_simp
  intro hne3
  obtain ⟨st3, i3, hP3, hR3, hext3, hsp3, hpre3, hi3, rfl⟩ := hB3.resolve_left hne3
  clear h hR
  have h := h3
  have hR := hR3
  have hi1'' := hext3.lt hi1'
  have hi2' := hext3.lt hi2
  rw [← hext3.id hi1', ← hext3.id hi2]
  apply WP.ite_seq
  rule_simp [tagE, tIte, tExtract]
  apply WP.ite_seq
  rule_simp [tagE, tExtract]
  apply WP.rule_hcall (rw_extract_spec W sb X c0 c3 prems params st3 i1 i2 i3) (by rule_simp)
    ⟨rfl, h, hR, hi1'', hi2', hi3⟩
  intro s4 c4 r h4 hB4
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  refine ⟨c4, h4, RwB.trans hext1 hsp1 hpre1 (RwB.trans hext2 hsp2 hpre2
    (RwB.trans hext3 hsp3 hpre3 hB4.rwB (fun st' i hP => hP)) (fun st' i hP => hP))
    (fun st' i hP => ?_)⟩
  rw [rw_instE_extract, hP1]
  simp only
  rw [hP2]
  simp only
  rw [hP3]
  exact hP

end Vbcf.Proof
