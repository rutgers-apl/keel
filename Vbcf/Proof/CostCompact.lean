import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostReplay

/-!
# Vbcf cost proofs: tools for `ck_compact`

`ck_compact`'s loops are bounded by struct cells beyond the two budget cells,
so its cost proof (`CostCompact2.lean`) tracks `flen` (cell 7) and `sp`
(cell 11) across the calls it makes.  Here:

* `FnCost.and`: two cost facts about one function hold of the same run.
* `spend_frame`, `push_frame`: `spend` and `push` keep every cell they do not
  write; `push_sp`: a `push` that succeeds adds one to `sp`.  `fr_step` walks
  a body keeping one `Fld`.  `spend_costF`, `push_costF` combine them with the
  registered cost lemmas.
* `CS m sb w mm F s`: the budget, `flen = F`, `sp = s`; the statement rules
  `WPC.store_cs`, `WPC.setField_cs`, `WPC.setSp_cs`, `WPC.kvfree_cs`, and the
  calls `WPC.push_cs`, `WPC.spend_fl`.
* `WPC.kvfree_bud_or`/`WPC.setField_gone`: `kvfree(st->htab)` of a value the
  proof cannot see either keeps the struct or frees it, and then the next
  store to it gets stuck.
* `Fld.of_load`, `Budget.fld_of_load`, `Budget.fld_lt`: cells from loads;
  `kvcalloc_fresh`: a fresh block is not the struct.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

/-! ## Two cost facts about one call -/

/-- Two `FnCost` facts about the same function hold of the same run. -/
theorem FnCost.and {P : Prog} {f : String} {pre1 pre2 : List Val → (KernelState P State) → Prop}
    {post1 post2 : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (h1 : FnCost (State := State) P f pre1 post1) (h2 : FnCost (State := State) P f pre2 post2) :
    FnCost (State := State) P f (fun vs st => pre1 vs st ∧ pre2 vs st)
      (fun vs st rv st' c => post1 vs st rv st' c ∧ post2 vs st rv st' c) := by
  intro vs st ⟨hp1, hp2⟩
  obtain ⟨f1, hf1⟩ := h1 vs st hp1
  obtain ⟨f2, hf2⟩ := h2 vs st hp2
  refine ⟨max f1 f2, ?_⟩
  have e1 := runC_mono P (CallResC.sat_ne hf1) (max f1 f2) (Nat.le_max_left _ _)
  have e2 := runC_mono P (CallResC.sat_ne hf2) (max f1 f2) (Nat.le_max_right _ _)
  rw [e1]
  revert hf1 hf2
  rw [← e1, e2]
  cases P.runC f2 f vs st with
  | timeout => intro _ h; exact h
  | stuck => intro _ _; trivial
  | ok r => obtain ⟨rv, st', c⟩ := r; intro h1 h2; exact ⟨h1, h2⟩

/-! ## The cells beyond the budget -/

/-- A field `f` at another cell than `i`. -/
theorem fieldIn_ne_of_idx {f : String} {j i : Nat} {u : Ty} (hf : fieldIn ckS.fields f = some (j, u))
    (h : i ≠ j) : ∀ t, fieldIn ckS.fields f ≠ some (i, t) := by
  intro t h'
  rw [hf] at h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  exact h h'.1.symm

/-- A field that loads gives the cell's value. -/
theorem Fld.of_load {m : Mem} {sb i : Nat} {f : String} {t : Ty} {v x : Val} (h : Fld m sb i x)
    (hf : fieldIn ckS.fields f = some (i, t)) (hl : m.loadField Vbcf.prog sb f = some v) : v = x := by
  obtain ⟨cells, hb, hc⟩ := h
  have hslot : m.fieldSlot Vbcf.prog sb f = some (⟨.struct "ck", cells⟩, i, t) := by
    unfold Mem.fieldSlot; rw [hb]; simp [prog_ck, StructDef.field?, hf]
  unfold Mem.loadField at hl
  rw [hslot] at hl
  simp only [hc] at hl
  cases x <;> simp_all

/-- A field that loads, in a struct with a budget: its cell holds the value. -/
theorem Budget.fld_of_load {m : Mem} {sb i : Nat} {w mm : BitVec 32} {f : String} {t : Ty} {v : Val}
    (hb : Budget m sb w mm) (hf : fieldIn ckS.fields f = some (i, t))
    (hl : m.loadField Vbcf.prog sb f = some v) : Fld m sb i v := by
  obtain ⟨cells, hblk, -⟩ := hb.1
  have hslot : m.fieldSlot Vbcf.prog sb f = some (⟨.struct "ck", cells⟩, i, t) := by
    unfold Mem.fieldSlot; rw [hblk]; simp [prog_ck, StructDef.field?, hf]
  unfold Mem.loadField at hl
  rw [hslot] at hl
  refine ⟨cells, hblk, ?_⟩
  cases hc : cells[i]? with
  | none => simp [hc] at hl
  | some v' =>
    simp only [hc] at hl
    cases v' <;> simp_all

/-- The struct has every cell up to the memory budget's. -/
theorem Budget.fld_lt {m : Mem} {sb : Nat} {w mm : BitVec 32} (hb : Budget m sb w mm) {i : Nat}
    (hi : i ≤ 22) : ∃ v, Fld m sb i v := by
  obtain ⟨cells, hblk, hc⟩ := hb.2
  have h22 : 22 < cells.size := by
    rcases Nat.lt_or_ge 22 cells.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hc; simp at hc
  exact ⟨cells[i]'(by omega), cells, hblk, Array.getElem?_eq_getElem _⟩

/-- A block from `kvcalloc` is fresh: not the struct. -/
theorem kvcalloc_fresh {st st' : (KernelState prog State)} {t : Ty} {x : BitVec 64} {b off sb : Nat} {w mm : BitVec 32}
    (hb : Budget st.mem sb w mm) (h : Ext.run prog (.kvcalloc t) [.u64 x] st = some (some (.ptr b off), st')) :
    b ≠ sb := by
  obtain ⟨cells, hblk, -⟩ := hb.1
  have hlt := Mem.block?_lt hblk
  have ha := (Ext.run_spec h).kvcalloc
  rcases ha with hnull | hsuccess
  · have he := hnull.1
    simp at he
  · have he := hsuccess.1
    simp only [Option.some.injEq, Val.ptr.injEq] at he
    rw [he.1]
    omega

/-! ## A frame walk: statements that keep one struct cell -/

theorem Env.assign_some' {env env' : Env} {m : Mem} {x : Var} {v : Val} (h : env.assign m x v = some env') :
    env' = env.set x v := by
  unfold Env.assign at h
  split at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq] at h; exact h.symm
    · simp at h

theorem assignDst_some_set {env env' : Env} {m : Mem} {x : Var} {rv : Option Val}
    (h : assignDst env m (some x) rv = some env') : ∃ v, env' = env.set x v := by
  cases rv with
  | none => simp [assignDst] at h
  | some v => exact ⟨v, Env.assign_some' h⟩

/-- One statement of a walk that keeps the most recent `Fld` (no budget, no cost). -/
syntax "fr_step" : tactic
macro_rules | `(tactic| fr_step) => `(tactic| first
  | apply WPC.seq
  | (apply WPC.skip; wpc_simp)
  | apply WPC.ite_any
  | (apply WPC.assign_any; intro _v _env' _henv; have _he := Env.assign_some' _henv; subst _he; wpc_simp)
  | (apply WPC.store_fld ‹Fld _ _ _ _›; intro _m' _hf; wpc_simp)
  | (refine WPC.setField_fld ‹Fld _ _ _ _› ?_ ?_;
     (intro _t _h; simp [ckS, fieldIn] at _h <;> omega); intro _m' _hf; wpc_simp)
  | (apply WPC.ecall_fld ‹Fld _ _ _ _›; intro _vs _hvs;
     refine ⟨fun _ _ h => (by cases h), fun _rv _st' _hf => ?_⟩; split; trivial;
     rename_i _env2 _hasg;
     first | (obtain ⟨_, _he⟩ := assignDst_some_set _hasg; subst _he) | (have _he := assignDst_none' _hasg; subst _he);
     wpc_simp))

theorem spend_frame (sb i : Nat) (x : Val) (k : BitVec 32) (hi19 : i ≠ 19) (hi20 : i ≠ 20) :
    FnCost (State := State) Vbcf.prog "spend" (fun vs st => vs = [.ptr sb 0, .u32 k] ∧ Fld st.mem sb i x)
      (fun _ _ _ st' _ => Fld st'.mem sb i x) := by
  apply FnCost.intro (fn := spend) rfl
  rintro vs st ⟨rfl, hf⟩
  simp [spend, bindParams, hf.hasTy]
  simp only [Stmt.block, initLocals, List.map]
  repeat (any_goals fr_step)
  all_goals (apply WPC.ret_any; intro _v; simp only [CPost.shift_apply, retPostC]; intro _; assumption)

theorem push_frame (sb i : Nat) (x : Val) (v : BitVec 32) (hi10 : i ≠ 10) (hi11 : i ≠ 11)
    (hi12 : i ≠ 12) (hi19 : i ≠ 19) (hi20 : i ≠ 20) (hi22 : i ≠ 22) :
    FnCost (State := State) Vbcf.prog "push" (fun vs st => vs = [.ptr sb 0, .u32 v] ∧ Fld st.mem sb i x)
      (fun _ _ _ st' _ => Fld st'.mem sb i x) := by
  apply FnCost.intro (fn := push) rfl
  rintro vs st ⟨rfl, hf⟩
  simp [push, bindParams, hf.hasTy]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  repeat (any_goals fr_step)
  all_goals (apply WPC.ret_any; intro _v; simp only [CPost.shift_apply, retPostC]; intro _; assumption)

/-- A `push` that succeeds has added one to `sp`. -/
theorem push_sp (sb : Nat) (s v : BitVec 32) :
    FnCost (State := State) Vbcf.prog "push" (fun vs st => vs = [.ptr sb 0, .u32 v] ∧ Fld st.mem sb 11 (.u32 s))
      (fun _ _ rv st' _ => rv ≠ some (.u32 0#32) → Fld st'.mem sb 11 (.u32 (s + 1#32))) := by
  apply FnCost.intro (fn := push) rfl
  rintro vs st ⟨rfl, hf⟩
  simp [push, bindParams, hf.hasTy]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  repeat (any_goals fr_step)
  all_goals (try (apply WPC.ret; simp [evalE, retPostC]; done))
  all_goals
    apply WPC.setField
    have hl := (‹Fld _ _ _ _›).load fi_sp (by simp)
    simp only [evalE, Env.get, ↓reduceIte, evalBin, evalArith] at hl ⊢
    simp only [hl]
    (try intro _)
    split
    · trivial
    rename_i m' hs
    have h' := (‹Fld _ _ _ _›).storeField_same hs fi_sp
    wpc_simp
    apply WPC.ret
    simp only [evalE, CPost.shift_apply, retPostC]
    intro _ _
    exact h'

/-! ## `spend` and `push` with their frames -/

theorem spend_costF (sb A : Nat) (hA : 6 ≤ A) (k : BitVec 32) (i : Nat) (x : Val) (hi19 : i ≠ 19)
    (hi20 : i ≠ 20) :
    FnCost (State := State) Vbcf.prog "spend"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 k] vs st ∧ (vs = [.ptr sb 0, .u32 k] ∧ Fld st.mem sb i x))
      (fun vs st rv st' c => Amort sb A (allow 8) 0 (slackUnless 0#32 (A * k.toNat)) vs st rv st' c ∧
        Fld st'.mem sb i x) :=
  FnCost.and (spend_cost sb A hA k) (spend_frame sb i x k hi19 hi20)

theorem push_costF (sb A : Nat) (hA : 6 ≤ A) (v s : BitVec 32) (x : Val) :
    FnCost (State := State) Vbcf.prog "push"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 v] vs st ∧
        ((vs = [.ptr sb 0, .u32 v] ∧ Fld st.mem sb 7 x) ∧ (vs = [.ptr sb 0, .u32 v] ∧ Fld st.mem sb 11 (.u32 s))))
      (fun vs st rv st' c => Amort sb A (allow 56) 0 (slackUnless 0#32 A) vs st rv st' c ∧
        (Fld st'.mem sb 7 x ∧ (rv ≠ some (.u32 0#32) → Fld st'.mem sb 11 (.u32 (s + 1#32))))) :=
  FnCost.and (push_cost sb A hA v)
    (FnCost.and (push_frame sb 7 x v (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (push_sp sb s v))

/-! ## The state `ck_compact`'s loops track -/

/-- The budget, `flen = F` and `sp = s`. -/
def CS (m : Mem) (sb : Nat) (w mm F s : BitVec 32) : Prop :=
  Budget m sb w mm ∧ Fld m sb 7 (.u32 F) ∧ Fld m sb 11 (.u32 s)

/-- `sp` as a number (0 if there is no such cell). -/
def spOf (m : Mem) (sb : Nat) : Nat :=
  match m.block? sb with
  | some blk => match blk.cells[11]? with
    | some (Val.u32 s) => s.toNat
    | _ => 0
  | none => 0

theorem Fld.spOf {m : Mem} {sb : Nat} {s : BitVec 32} (h : Fld m sb 11 (.u32 s)) : spOf m sb = s.toNat := by
  obtain ⟨cells, hb, hc⟩ := h
  simp [Vbcf.Proof.spOf, hb, hc]

section
variable {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm F s : BitVec 32}

theorem WPC.store_cs {p j e : Expr} (h0 : CS st.mem sb w mm F s)
    (h : ∀ m', CS m' sb w mm F s → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.store p j e) Q env st := by
  apply WPC.store
  split
  · split
    · trivial
    · split
      · trivial
      · rename_i m' hs; exact h m' ⟨h0.1.storeArr hs, h0.2.1.storeArr hs, h0.2.2.storeArr hs⟩
  · trivial

theorem WPC.setField_cs {p e : Expr} {f : String} (h0 : CS st.mem sb w mm F s)
    (h1 : f ≠ "work") (h2 : f ≠ "mem") (h3 : ∀ t, fieldIn ckS.fields f ≠ some (7, t))
    (h4 : ∀ t, fieldIn ckS.fields f ≠ some (11, t))
    (h : ∀ m', CS m' sb w mm F s → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.setField p f e) Q env st := by
  apply WPC.setField
  split
  · intro _
    split
    · trivial
    · rename_i m' hs
      exact h m' ⟨h0.1.storeField hs h1 h2, h0.2.1.storeField hs h3, h0.2.2.storeField hs h4⟩
  · trivial

/-- `st->sp = e;` where `e` evaluates to `y`. -/
theorem WPC.setSp_cs {e : Expr} {y : BitVec 32} {v0 : Val} (hb : Budget st.mem sb w mm)
    (hf : Fld st.mem sb 7 (.u32 F)) (hs : Fld st.mem sb 11 v0) (hst : env.get "st" = some (.ptr sb 0))
    (he : evalE Vbcf.prog env st.mem e = some (.u32 y))
    (h : ∀ m', CS m' sb w mm F y → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.setField (.var "st") "sp" e) Q env st := by
  apply WPC.setField
  simp only [evalE, hst, he]
  intro _
  cases hst' : st.mem.storeField Vbcf.prog sb "sp" (.u32 y) with
  | none => trivial
  | some m' =>
    exact h m' ⟨hb.storeField hst' (by decide) (by decide),
      hf.storeField hst' (fieldIn_ne_of_idx fi_sp (by decide)), hs.storeField_same hst' fi_sp⟩

/-- `kvfree(e)` of a value that is not the struct. -/
theorem WPC.kvfree_cs {e : Expr} {v : Val} (h0 : CS st.mem sb w mm F s)
    (he : evalE Vbcf.prog env st.mem e = some v) (hv : ∀ b, v = .ptr b 0 → b ≠ sb)
    (h : ∀ st', CS st'.mem sb w mm F s → Q .normal env st' 3) :
    WPC Vbcf.prog (.ecall none .kvfree [e]) Q env st := by
  apply WPC.ecall
  simp only [evalArgs, he]
  cases hr : Ext.run Vbcf.prog .kvfree [v] st with
  | none => trivial
  | some r =>
    obtain ⟨rv, st'⟩ := r
    have hfree : ∀ b, [v] = [.ptr b 0] → Ext.kvfree = Ext.kvfree → b ≠ sb :=
      fun b hb _ => hv b (by simpa using hb)
    simp only [assignDst_none, costC_kvfree]
    exact CPost.cost_eq (h st' ⟨h0.1.ext hr hfree, h0.2.1.ext hr hfree, h0.2.2.ext hr hfree⟩)
      (by simp [Cost.add_t]) (by simp [Cost.add_m])

/-- `kvfree(e)` of a value that is not the struct, keeping the budget. -/
theorem WPC.kvfree_bud {e : Expr} {v : Val} (hb : Budget st.mem sb w mm)
    (he : evalE Vbcf.prog env st.mem e = some v) (hv : ∀ b, v = .ptr b 0 → b ≠ sb)
    (h : ∀ st', Budget st'.mem sb w mm → Q .normal env st' 3) :
    WPC Vbcf.prog (.ecall none .kvfree [e]) Q env st := by
  apply WPC.ecall
  simp only [evalArgs, he]
  cases hr : Ext.run Vbcf.prog .kvfree [v] st with
  | none => trivial
  | some r =>
    obtain ⟨rv, st'⟩ := r
    have hfree : ∀ b, [v] = [.ptr b 0] → Ext.kvfree = Ext.kvfree → b ≠ sb :=
      fun b hb _ => hv b (by simpa using hb)
    simp only [assignDst_none, costC_kvfree]
    exact CPost.cost_eq (h st' (hb.ext hr hfree)) (by simp [Cost.add_t]) (by simp [Cost.add_m])

/-- `kvfree(e)` of anything: the budget is kept, or the struct is gone. -/
theorem WPC.kvfree_bud_or {e : Expr} (hb : Budget st.mem sb w mm)
    (h : ∀ st', (Budget st'.mem sb w mm ∨ st'.mem.block? sb = none) → Q .normal env st' 3) :
    WPC Vbcf.prog (.ecall none .kvfree [e]) Q env st := by
  apply WPC.ecall
  cases hv : evalArgs Vbcf.prog env st.mem [e] with
  | none => trivial
  | some vs =>
    simp only []
    cases hr : Ext.run Vbcf.prog .kvfree vs st with
    | none => trivial
    | some r =>
      obtain ⟨rv, st'⟩ := r
      have hc : Ext.costC Vbcf.prog .kvfree vs = ⟨0, 0⟩ := by simp [Ext.costC, Ext.cost, Ext.words]
      simp only [assignDst_none, hc]
      refine CPost.cost_eq (h st' ?_) (by simp [Cost.add_t]) (by simp [Cost.add_m])
      by_cases hsb : vs = [.ptr sb 0]
      · subst hsb
        right
        have he := (Ext.run_spec hr).kvfree_ptr.2
        rw [he, Mem.block?_free]
        simp
      · left
        exact hb.ext hr (fun b hb' _ => by rintro rfl; exact hsb hb')

/-- A store to a field of a struct that is gone gets stuck. -/
theorem WPC.setField_gone {e : Expr} {f : String} (hg : st.mem.block? sb = none)
    (hst : env.get "st" = some (.ptr sb 0)) : WPC Vbcf.prog (.setField (.var "st") f e) Q env st := by
  apply WPC.setField
  simp only [evalE, hst]
  cases evalE Vbcf.prog env st.mem e with
  | none => trivial
  | some v =>
    simp only []
    intro _
    have : st.mem.storeField Vbcf.prog sb f v = none := by
      unfold Mem.storeField Mem.fieldSlot; rw [hg]
    rw [this]; trivial

end

/-- `x = push(st, e)` keeping `flen` and counting `sp`. -/
theorem WPC.push_cs {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb A : Nat} (hA : 6 ≤ A)
    {w mm F s v : BitVec 32} {x : Var} {args : List Expr}
    (h0 : CS st.mem sb w mm F s)
    (hargs : evalArgs Vbcf.prog env st.mem args = some [.ptr sb 0, .u32 v]) (hx : env.ty x = some .u32)
    (h : ∀ (r : BitVec 32) (st' : (KernelState prog State)) (c : Cost) (w' mm' : BitVec 32), Budget st'.mem sb w' mm' →
      Fld st'.mem sb 7 (.u32 F) → (r ≠ 0#32 → Fld st'.mem sb 11 (.u32 (s + 1#32))) →
      c.t + A * w'.toNat + (if r = 0#32 then 0 else A) ≤ A * w.toNat + 56 → c.m + mm'.toNat ≤ mm.toNat →
      Q .normal (env.set x (.u32 r)) st' (c + 2)) :
    WPC Vbcf.prog (.call (some x) "push" args) Q env st := by
  apply WPC.call (push_costF sb A hA v s (.u32 F))
  rw [hargs]
  refine ⟨⟨⟨rfl, _, _, h0.1⟩, ⟨rfl, h0.2.1⟩, ⟨rfl, h0.2.2⟩⟩, ?_⟩
  rintro rv st' c ⟨⟨w', mm', hb', ht, hm⟩, hf', hs'⟩
  rw [h0.1.wk] at ht
  rw [h0.1.mk] at hm
  split
  · trivial
  rename_i env' hasg
  obtain ⟨r, rfl, rfl⟩ := assignDst_u32' hasg hx
  refine h r st' c w' mm' hb' hf' (fun hr => hs' (by simpa using hr)) ?_ (by simpa using hm)
  by_cases hr : r = 0#32
  · subst hr; simpa using ht
  · simpa [hr] using ht

/-- `x = spend(st, e)` keeping `flen`. -/
theorem WPC.spend_fl {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb A : Nat} (hA : 6 ≤ A)
    {w mm F k : BitVec 32} {x : Var} {args : List Expr}
    (hb : Budget st.mem sb w mm) (hf : Fld st.mem sb 7 (.u32 F))
    (hargs : evalArgs Vbcf.prog env st.mem args = some [.ptr sb 0, .u32 k]) (hx : env.ty x = some .u32)
    (h : ∀ (r : BitVec 32) (st' : (KernelState prog State)) (c : Cost) (w' mm' : BitVec 32), Budget st'.mem sb w' mm' →
      Fld st'.mem sb 7 (.u32 F) →
      c.t + A * w'.toNat + (if r = 0#32 then 0 else A * k.toNat) ≤ A * w.toNat + 8 →
      c.m + mm'.toNat ≤ mm.toNat →
      Q .normal (env.set x (.u32 r)) st' (c + 2)) :
    WPC Vbcf.prog (.call (some x) "spend" args) Q env st := by
  apply WPC.call (spend_costF sb A hA k 7 (.u32 F) (by decide) (by decide))
  rw [hargs]
  refine ⟨⟨⟨rfl, _, _, hb⟩, ⟨rfl, hf⟩⟩, ?_⟩
  rintro rv st' c ⟨⟨w', mm', hb', ht, hm⟩, hf'⟩
  rw [hb.wk] at ht
  rw [hb.mk] at hm
  split
  · trivial
  rename_i env' hasg
  obtain ⟨r, rfl, rfl⟩ := assignDst_u32' hasg hx
  refine h r st' c w' mm' hb' hf' ?_ (by simpa using hm)
  by_cases hr : r = 0#32
  · subst hr; simpa using ht
  · simpa [hr] using ht

end Vbcf.Proof
