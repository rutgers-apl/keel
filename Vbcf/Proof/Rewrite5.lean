import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite4

/-!
# Vbcf proofs: the Rewrite family, part 5 — `rw_inst`: statement and infrastructure

`rw_inst(st, pos, ab, na, depth)` instantiates the pattern encoded at offset `pos` of `rw_tbl`
(`RwAt pos (encE e)`), the rule's arguments being `stk[ab .. ab+na)`.  It recurses in C with
a depth counter; `RwInstSpecD d` is indexed by the depth and proved by strong induction
(`Rewrite7`).  On success it returns `instE` of the pattern; the stack above `sp` may have
been used (by the `RW_APP` case), but `sp` and the cells below it are as on entry (`RwB`).
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-- The outcome of a node-building call that may use the stack above `sp`: `NOID`, or the
Lean function `P` succeeded, the rule context holds for the new states, the pool was only
extended, and `sp` and the cells below it are unchanged. -/
def RwB (W : World) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem) (st : VSt)
    (P : St → Nat → Prop) (c' : CMem) (r : BitVec 32) : Prop :=
  r = 4294967295#32 ∨
  ∃ (st' : VSt) (i : Nat), P st'.toSt i ∧ RCtx W X c0 prems params c' st' ∧ VExt st st' ∧ c'.k.sp = c.k.sp ∧
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧ st'.lv i ∧
    r = BitVec.ofNat 32 (st'.id i)

/-- What `rw_inst` returns. -/
def RwInstR (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem)
    (st : VSt) (args : List Nat) (e : RwExpr) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧
    RwB W X c0 prems params c st (fun st' i => instE X.bi args.toArray e st = some (st', i)) c' r

/-- The arguments of the rule are on the stack below `sp`. -/
def RwArgsAt (c : CMem) (st : VSt) (ab : Nat) (args : List Nat) : Prop :=
  StkIds c st ab args ∧ ab + args.length ≤ c.k.sp.toNat

def RwInstSpecD (d : BitVec 32) : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (e : RwExpr) (pos ab : Nat) (args : List Nat),
    FnSpec (State := State) Vbcf.prog "rw_inst"
      (fun vs s => vs = [.ptr sb 0, uv pos, uv ab, uv args.length, .u32 d] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ RwAt pos (encE e) ∧ wfE e = true ∧ RwArgsAt c st ab args)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ RwInstR W sb X c0 prems params c st args e r s')

def RwInstSpec : Prop := ∀ d, RwInstSpecD (State := State) d

/-! ## Outcomes -/

section outcomes
variable {W : World} {X : Ctx} {c0 c c1 c2 : CMem} {prems params : List Nat} {st st1 : VSt}
  {P P' : St → Nat → Prop} {r : BitVec 32}

theorem Built.rwB (hB : Built W X c0 prems params c st P c' r) : RwB W X c0 prems params c st P c' r := by
  rcases hB with h | ⟨st', i, hP, hR, hext, hs, hi, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨st', i, hP, hR, hext, hs.2, fun j _ => by rw [hs.1], hi, hr⟩

theorem RwB.mono (hB : RwB W X c0 prems params c st P c' r) (himp : ∀ st' i, P st' i → P' st' i) :
    RwB W X c0 prems params c st P' c' r := by
  rcases hB with h | ⟨st', i, hP, hR, hext, hs, hpre, hi, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨st', i, himp st' i hP, hR, hext, hs, hpre, hi, hr⟩

/-- An outcome seen from an earlier state. -/
theorem RwB.trans (hext : VExt st st1) (hsp : c1.k.sp = c.k.sp)
    (hpre : ∀ j, j < c.k.sp.toNat → c1.stk[j]? = c.stk[j]?)
    (hB : RwB W X c0 prems params c1 st1 P c2 r) (himp : ∀ st' i, P st' i → P' st' i) :
    RwB W X c0 prems params c st P' c2 r := by
  rcases hB with h | ⟨st', i, hP, hR, hext', hs, hpre', hi, hr⟩
  · exact Or.inl h
  · refine Or.inr ⟨st', i, himp st' i hP, hR, hext.trans hext', hs.trans hsp, fun j hj => ?_, hi, hr⟩
    rw [hpre' j (by rw [hsp]; exact hj), hpre j hj]

end outcomes

theorem RwArgsAt.frame {c c' : CMem} {st st' : VSt} {ab : Nat} {args : List Nat}
    (ha : RwArgsAt c st ab args) (hext : VExt st st') (hsp : c.k.sp.toNat ≤ c'.k.sp.toNat)
    (hpre : ∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) : RwArgsAt c' st' ab args := by
  refine ⟨fun j i hj => ?_, by have := ha.2; omega⟩
  obtain ⟨hi, hU⟩ := ha.1 j i hj
  have := lt_length_of_getElem? hj
  refine ⟨hext.lt hi, ?_⟩
  unfold U at hU ⊢
  rw [hpre _ (by have := ha.2; omega), hext.id hi]
  exact hU

/-! ## Statement rules -/

section stmts
variable {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)}

/-- `if (cond) { return NOID; } rest` for any postcondition that allows `NOID`. -/
theorem WP.rw_guard {R : BitVec 32 → (KernelState P State) → Prop} [RetsTo Q R] {cond : Expr} {rest : Stmt}
    {nm : String} (hfail : R 4294967295#32 s)
    (H : match evalE P env s.mem cond with
      | some (.u32 v) => v = 0 → WP P rest Q env s
      | _ => False) :
    WP P (.seq (.ite cond (.ret (some (.named nm 4294967295#32))) .skip) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun _ => ?_, fun he => ?_⟩
    · apply WP.ret
      simp only [evalE]
      exact RetsTo.ret _ _ _ hfail
    · apply WP.skip
      exact H he
  · exact H.elim

/-- `return NOID;` for any postcondition that allows `NOID`. -/
theorem WP.rw_fail {R : BitVec 32 → (KernelState P State) → Prop} [RetsTo Q R] {nm : String}
    (hfail : R 4294967295#32 s) :
    WP P (.ret (some (.named nm 4294967295#32))) Q env s := by
  apply WP.ret
  simp only [evalE]
  exact RetsTo.ret _ _ _ hfail

end stmts

theorem RwInstR.fail {W : World} {sb : Nat} {X : Ctx} {c0 c c' : CMem} {prems params : List Nat}
    {st : VSt} {args : List Nat} {e : RwExpr} {s : (KernelState prog State)} (h : Holds W s.mem sb c') :
    RwInstR W sb X c0 prems params c st args e 4294967295#32 s := ⟨c', h, Or.inl rfl⟩

/-! ## `instE`, one case at a time -/

section inst
variable (bi : Builtins) (args : Array Nat) (st : St)

theorem rw_instE_app (op : RwOp) (as : RwArgs) :
    instE bi args (.app op as) st = match instA bi args as st with
      | some (st1, is) => pushApp st1 op is
      | none => none := by
  simp [instE]; rfl

theorem rw_instA_cons (a : RwExpr) (rest : RwArgs) :
    instA bi args (.cons a rest) st = match instE bi args a st with
      | some (st1, i) =>
        match spliceIdx st1 i with
        | some items =>
          match instA bi args rest st1 with
          | some (st2, is) => some (st2, items ++ is)
          | none => none
        | none => none
      | none => none := by
  simp [instA]; rfl

theorem rw_instA_nil : instA bi args .nil st = some (st, []) := by simp [instA]

theorem rw_instE_bvmax (sz : RwExpr) :
    instE bi args (.bvmax sz) st = match instE bi args sz st with
      | some (st1, s) => rwMaxTail st1 s
      | none => none := by
  simp only [instE, rwMaxTail]; rfl

theorem rw_instE_symVal (val sz : RwExpr) :
    instE bi args (.symVal val sz) st = match instE bi args val st with
      | some (st1, v) =>
        match instE bi args sz st1 with
        | some (st2, s) => rwSymTail st2 v s
        | none => none
      | none => none := by
  simp only [instE, rwSymTail]; rfl

theorem rw_instE_ext (tag : Nat) (e x : RwExpr) (htag : tag = 9 ∨ tag = 10 ∨ tag = 11) :
    instE bi args (if tag = 9 then .zext e x else if tag = 10 then .sext e x else .repeat e x) st =
      match instE bi args e st with
      | some (st1, k) =>
        match instE bi args x st1 with
        | some (st2, xi) => rwExtTail st2 tag k xi
        | none => none
      | none => none := by
  rcases htag with rfl | rfl | rfl <;> simp only [rwExtTail, rwExtOp] <;> rfl

theorem rw_instE_ite (c t e : RwExpr) :
    instE bi args (.ite c t e) st = match instE bi args c st with
      | some (st1, ci) =>
        match instE bi args t st1 with
        | some (st2, ti) =>
          match instE bi args e st2 with
          | some (st3, ei) => rwIteTail st3 ci ti ei
          | none => none
        | none => none
      | none => none := by
  simp only [instE, rwIteTail]; rfl

theorem rw_instE_extract (hi lo x : RwExpr) :
    instE bi args (.extract hi lo x) st = match instE bi args hi st with
      | some (st1, h) =>
        match instE bi args lo st1 with
        | some (st2, l) =>
          match instE bi args x st2 with
          | some (st3, xi) => rwExtractTail st3 h l xi
          | none => none
        | none => none
      | none => none := by
  simp only [instE, rwExtractTail]; rfl

end inst

/-! ## After the header has been decoded -/

/-- The locals of `rw_inst` once `hdr`, `tag`, `aux`, `endp` are set. -/
def rwInstEnv (sb pos ab na : Nat) (d : BitVec 32) (e : RwExpr) (p a b c base ok r : BitVec 32) :
    Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("pos", .u32, uv pos), ("ab", .u32, uv ab),
    ("na", .u32, uv na), ("depth", .u32, .u32 d),
    ("hdr", .u32, uv (tagE e + auxE e * 256 + (encE e).length * 65536)),
    ("tag", .u32, uv (tagE e)), ("aux", .u32, uv (auxE e)),
    ("endp", .u32, uv (pos + (encE e).length)), ("p", .u32, .u32 p), ("a", .u32, .u32 a),
    ("b", .u32, .u32 b), ("c", .u32, .u32 c), ("base", .u32, .u32 base), ("ok", .u32, .u32 ok),
    ("r", .u32, .u32 r)]

/-- The body of `rw_inst` after the header has been decoded: one `if` per tag. -/
def rwInstTail : Stmt :=
  match rwInst.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ t))))) => t
  | _ => .skip

/-- The case of `rw_inst` for the pattern `e`, from the decoded header on. -/
def RwInstCase (d : BitVec 32) (e : RwExpr) : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (pos ab : Nat) (args : List Nat) (s : (KernelState prog State)),
    Holds W s.mem sb c → RCtx W X c0 prems params c st → RwAt pos (encE e) → wfE e = true →
    RwArgsAt c st ab args →
    WP Vbcf.prog rwInstTail (RetQ (RwInstR W sb X c0 prems params c st args e))
      (rwInstEnv sb pos ab args.length d e 0#32 0#32 0#32 0#32 0#32 0#32 0#32) s

/-- `rw_inst` from its cases. -/
theorem rw_inst_of_cases (d : BitVec 32) (H : d ≠ 0#32 → ∀ e, RwInstCase (State := State) d e) : RwInstSpecD (State := State) d := by
  intro W sb X c0 c prems params st e pos ab args
  have hs := prog_ck
  apply FnSpec.intro' (fn := rwInst) rfl
  rintro vs s ⟨rfl, h, hR, hat, hwf, hargs⟩
  simp [rwInst, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := rwInst) rfl
  simp only [rwInst, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hw, hl, hpl⟩ := rw_head hat hwf
  have hsp := hR.sp_lt
  have hal := hargs.2
  simp only [maxPool] at hsp
  apply WP.rw_guard (RwInstR.fail h)
  rule_simp
  intro hd
  apply WP.assign_seq
  rule_simp [rw_findConst, rw_tbl_get hw]
  have htg := rw_tagE_lt e
  have hax := rw_auxE_lt hwf
  have e1 : (tagE e + auxE e * 256 + (encE e).length * 65536) % 256 = tagE e := by omega
  have e2 := rw_hdr_aux (show tagE e < 256 by omega) hax hl
  have e3 := rw_hdr_len (show tagE e < 256 by omega) hax hl
  apply WP.assign_seq
  rule_simp [e1]
  apply WP.assign_seq
  rule_simp [e2]
  apply WP.assign_seq
  rule_simp [e3]
  apply WP.rw_guard (RwInstR.fail h)
  rule_simp
  intro _
  exact H hd e W sb X c0 c prems params st pos ab args s h hR hat hwf hargs

end Vbcf.Proof
