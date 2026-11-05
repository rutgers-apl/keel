import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostAuto

/-!
# Vbcf cost proofs: `tick`, `spend`, `words_eq`, `push`

The first cost proofs, which fix the shape the others follow (`Amort`,
`CostAuto`).

* `tick` and `spend` turn work into time: when they succeed (return 1) they
  hand back `A` per unit spent (`slackUnless 0#32 …`), minus nothing, so the
  caller's own statements are paid by the work it spends.
* `push` does the same for its unit, and pays the words of a growth from the
  memory budget.
* `words_eq` spends nothing: its cost is linear in its length argument.

None of them needs the representation invariant: the preconditions only say
where the budget cells are.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000

theorem bv_sub_one_toNat {w : BitVec 32} (hz : ¬ w = 0#32) : (w - 1#32).toNat = w.toNat - 1 := by
  have : w.toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [BitVec.toNat_sub]; simp; omega

theorem bv_pos_of_ne {w : BitVec 32} (hz : ¬ w = 0#32) : 1 ≤ w.toNat := by
  have : w.toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by simpa using e))
  omega

theorem bv_sub_toNat_of_le {w k : BitVec 32} (h : k ≤ w) : (w - k).toNat = w.toNat - k.toNat := by
  rw [BitVec.le_def] at h
  rw [BitVec.toNat_sub]; omega

/-- `A` units per unit of work: spending `k` of `w`. -/
theorem mul_sub_add {A w k : Nat} (h : k ≤ w) : A * (w - k) + A * k = A * w := by
  rw [← Nat.mul_add, Nat.sub_add_cancel h]

/-! ## `tick` -/

theorem tick_cost (sb A : Nat) (_hA : 6 ≤ A) :
    FnCost (State := State) Vbcf.prog "tick" (BudPre sb [.ptr sb 0]) (Amort sb A (allow 8) 0 (slackUnless 0#32 A)) := by
  apply FnCost.intro (fn := tick) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body tick
  apply WPC.seq
  apply WPC.ite
  embc_simp [hb.ld_work]
  constructor
  · intro hz
    apply WPC.seq
    apply WPC.setField_bud hb (by decide) (by decide)
    intro m' hb'
    wpc_auto
    wpc_finish
  · intro hz
    apply WPC.skip
    wpc_simp
    apply WPC.seq
    apply WPC.setWork (x := w - 1#32) hb (by embc_simp) (by embc_simp [hb.ld_work])
    intro m' hb'
    have h1 := bv_sub_one_toNat hz
    have h2 := bv_pos_of_ne hz
    have h3 : A * (w - 1#32).toNat + A = A * w.toNat := by
      rw [h1]; simpa using mul_sub_add (A := A) h2
    wpc_auto
    wpc_finish

fncost_register "tick" tick tick_cost

/-! ## `spend` -/

theorem spend_cost (sb A : Nat) (_hA : 6 ≤ A) (k : BitVec 32) :
    FnCost (State := State) Vbcf.prog "spend" (BudPre sb [.ptr sb 0, .u32 k])
      (Amort sb A (allow 8) 0 (slackUnless 0#32 (A * k.toNat))) := by
  apply FnCost.intro (fn := spend) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body spend
  apply WPC.seq
  apply WPC.ite
  embc_simp [hb.ld_work]
  constructor
  · intro hlt
    apply WPC.seq
    apply WPC.setField_bud hb (by decide) (by decide)
    intro m' hb'
    wpc_auto
    wpc_finish
  · intro hge
    apply WPC.skip
    wpc_simp
    apply WPC.seq
    apply WPC.setWork (x := w - k) hb (by embc_simp) (by embc_simp [hb.ld_work])
    intro m' hb'
    have h1 := bv_sub_toNat_of_le hge
    have h2 : k.toNat ≤ w.toNat := BitVec.le_def.mp hge
    have h3 : A * (w - k).toNat + A * k.toNat = A * w.toNat := by rw [h1]; exact mul_sub_add h2
    wpc_auto
    wpc_finish

fncost_register "spend" spend spend_cost

/-! ## `words_eq` -/

theorem words_eq_cost (sb A : Nat) (va vb : Val) (n : BitVec 32) :
    FnCost (State := State) Vbcf.prog "words_eq" (BudPre sb [va, vb, .u32 n])
      (Amort sb A (allow (6 * n.toNat + 8)) 0 noSlack) := by
  apply FnCost.intro (fn := wordsEq) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  have hwk := hb.wk
  have hmk := hb.mk
  simp only [wordsEq, bindParams]
  by_cases ha : st.mem.hasTy va (.ptr .u32) = true
  · by_cases hb' : st.mem.hasTy vb (.ptr .u32) = true
    · simp only [ha, hb', Mem.hasTy_u32, ↓reduceIte]
      simp only [Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]
      apply WPC.seq
      apply WPC.while
        (I := fun env' st' k => st' = st ∧ ∃ i : BitVec 32,
          env' = [("a", .ptr .u32, va), ("b", .ptr .u32, vb), ("n", .u32, .u32 n), ("i", .u32, .u32 i)] ∧
          i.toNat ≤ n.toNat ∧ k.t ≤ 6 * i.toNat ∧ k.m = 0)
        (μ := fun env' _ => n.toNat - envU32 env' "i")
      · exact ⟨rfl, 0#32, rfl, by simp, by simp, by simp⟩
      rintro env' st' k ⟨rfl, i, rfl, hin, hk, hkm⟩
      embc_simp
      refine ⟨fun hge => ?_, fun hlt => ?_⟩
      · -- the loop is done
        have : i.toNat = n.toNat := by
          have := BitVec.not_lt.mp (by simpa using hge); rw [BitVec.le_def] at this; omega
        wpc_auto
        wpc_finish
      · have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
          rw [BitVec.toNat_add]; simp; omega
        apply WPC.seq
        apply WPC.ite_any
        · wpc_auto
          wpc_finish
        · apply WPC.skip
          wpc_simp
          apply WPC.assign
          embc_simp
          have hmod : (i.toNat + 1) % 4294967296 = i.toNat + 1 := by omega
          simp only [envU32, Env.get, hmod]
          simp only [String.reduceEq, ↓reduceIte, hi1]
          refine ⟨by omega, by omega, ?_, ?_⟩ <;> cost_arith
    · simp [hb']
  · simp [ha]

fncost_register "words_eq" wordsEq words_eq_cost

/-! ## `push` -/

theorem evalArgs_two {P : Prog} {env : Env} {m : Mem} {e1 e2 : Expr} {vs : List Val}
    (h : evalArgs P env m [e1, e2] = some vs) :
    ∃ x y, evalE P env m e1 = some x ∧ evalE P env m e2 = some y ∧ vs = [x, y] := by
  cases h1 : evalE P env m e1 <;> cases h2 : evalE P env m e2 <;> simp [evalArgs, h1, h2] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-- Where `push` stands after making room: either on its way to the store, or
failed; `w1` is the work after the unit for the push itself, `m0` the memory
budget at entry. -/
def PushMidC (sb : Nat) (v w1 m0 : BitVec 32) (A : Nat) : (CPost prog State) := fun o env st c =>
  match o with
  | .normal => (∃ ns nc, env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("v", .u32, .u32 v),
      ("ns", .ptr .u32, ns), ("ncap", .u32, .u32 nc)]) ∧
      ∃ w' mm' : BitVec 32, Budget st.mem sb w' mm' ∧ c.t + A * w'.toNat ≤ A * w1.toNat + 40 ∧
        c.m + mm'.toNat ≤ m0.toNat
  | .ret rv => rv = some (.u32 0#32) ∧ ∃ w' mm' : BitVec 32, Budget st.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * w1.toNat + 40 ∧ c.m + mm'.toNat ≤ m0.toNat
  | .brk => False

theorem PushMidC.mono {sb : Nat} {v w1 m0 : BitVec 32} {A : Nat} {o : Outcome} {env : Env}
    {st : (KernelState prog State)} {c c' : Cost} (h : PushMidC sb v w1 m0 A o env st c) (hc : c'.t ≤ c.t)
    (hm : c'.m ≤ c.m) : PushMidC sb v w1 m0 A o env st c' := by
  cases o with
  | normal => obtain ⟨he, w', mm', hb, hk, hkm⟩ := h; exact ⟨he, w', mm', hb, by omega, by omega⟩
  | brk => exact h
  | ret rv => obtain ⟨hr, w', mm', hb, hk, hkm⟩ := h; exact ⟨hr, w', mm', hb, by omega, by omega⟩

theorem push_cost (sb A : Nat) (hA : 6 ≤ A) (v : BitVec 32) :
    FnCost (State := State) Vbcf.prog "push" (BudPre sb [.ptr sb 0, .u32 v]) (Amort sb A (allow 56) 0 (slackUnless 0#32 A)) := by
  apply FnCost.intro (fn := push) rfl
  rintro vs st ⟨rfl, w, mm, hb⟩
  fncost_body push
  apply WPC.seq
  apply WPC.ite
  embc_simp [hb.ld_work]
  constructor
  · intro hz
    apply WPC.seq
    apply WPC.setField_bud hb (by decide) (by decide)
    intro m' hb'
    wpc_auto
    wpc_finish
  intro hz
  apply WPC.skip
  wpc_simp
  have hw1n := bv_sub_one_toNat hz
  have hwpos := bv_pos_of_ne hz
  have hpw : A * (w - 1#32).toNat + A = A * w.toNat := by
    rw [hw1n]; simpa using mul_sub_add (A := A) hwpos
  apply WPC.seq
  apply WPC.setWork (x := w - 1#32) hb (by embc_simp) (by embc_simp [hb.ld_work])
  intro m1 hb1
  wpc_simp
  apply WPC.seq
  apply WPC.mono (Q := PushMidC sb v (w - 1#32) mm A)
  · apply WPC.ite_any
    · -- the stack is full: grow it
      -- what follows the choice of the new capacity, for any capacity `nc`
      have key : ∀ (nc : BitVec 32) (Q' : (CPost prog State)),
          (∀ o env' st' c, PushMidC sb v (w - 1#32) mm A o env' st' (c + 11) → Q' o env' st' c) →
          WPC prog [cstms|
              if (st->work < ncap) { st->err = ERR_LIMIT; return 0; }
              st->work = st->work - ncap;
              if (st->mem < ncap) { st->err = ERR_LIMIT; return 0; }
              st->mem = st->mem - ncap;
              ns = kvrealloc(st->stk, array_size((u64)ncap, sizeof(u32)));
              if (ns == NULL) { st->err = ERR_NOMEM; return 0; }
              st->stk = ns;
              st->scap = ncap;]
            Q' [("st", .ptr (.struct "ck"), .ptr sb 0), ("v", .u32, .u32 v),
              ("ns", .ptr .u32, .null), ("ncap", .u32, .u32 nc)] { st with mem := m1 } := by
        intro nc Q' hQ
        simp only [Stmt.block]
        apply WPC.seq
        apply WPC.ite
        embc_simp [hb1.ld_work]
        constructor
        · intro _
          apply WPC.seq
          apply WPC.setField_bud hb1 (by decide) (by decide)
          intro m' hb'
          apply WPC.ret
          embc_simp
          apply hQ
          exact ⟨rfl, w - 1#32, mm, hb', by cost_arith, by cost_arith⟩
        intro hge
        have hge' : nc.toNat ≤ (w - 1#32).toNat := BitVec.le_def.mp hge
        apply WPC.skip
        wpc_simp
        apply WPC.seq
        apply WPC.setWork (x := w - 1#32 - nc) hb1 (by embc_simp) (by embc_simp [hb1.ld_work])
        intro m2 hb2
        have hw2n : (w - 1#32 - nc).toNat = (w - 1#32).toNat - nc.toNat := bv_sub_toNat_of_le hge
        have hpot : A * ((w - 1#32).toNat - nc.toNat) + A * nc.toNat = A * (w - 1#32).toNat :=
          mul_sub_add hge'
        wpc_simp
        -- pay for it from the memory budget
        apply WPC.seq
        apply WPC.ite
        embc_simp [hb2.ld_mem]
        constructor
        · intro _
          apply WPC.seq
          apply WPC.setField_bud hb2 (by decide) (by decide)
          intro m' hb'
          apply WPC.ret
          embc_simp
          apply hQ
          exact ⟨rfl, w - 1#32 - nc, mm, hb', by cost_simp; rw [hw2n]; omega, by cost_arith⟩
        intro hmge
        have hmge' : nc.toNat ≤ mm.toNat := BitVec.le_def.mp hmge
        apply WPC.skip
        wpc_simp
        apply WPC.seq
        apply WPC.setMem (x := mm - nc) hb2 (by embc_simp) (by embc_simp [hb2.ld_mem])
        intro m3 hb3
        have hm3n : (mm - nc).toNat = mm.toNat - nc.toNat := bv_sub_toNat_of_le hmge
        wpc_simp
        apply WPC.seq
        apply WPC.ecall_bud hb3
        intro vs hvs
        obtain ⟨x, y, -, hy, rfl⟩ := evalArgs_two hvs
        simp [evalE, evalCast, Env.get] at hy
        subst hy
        have hcost : Ext.costC prog (.kvrealloc .u32) [x, .u64 (nc.setWidth 64)] =
            ⟨2 * nc.toNat, nc.toNat⟩ := by
          simp [Ext.costC, Ext.cost, Ext.words]; have := nc.isLt; omega
        refine ⟨by simp, ?_⟩
        intro rv st3 hb4
        rw [hcost]
        have hAnc : 2 * nc.toNat ≤ A * nc.toNat := Nat.mul_le_mul_right _ (by omega)
        cases rv with
        | none => simp [assignDst]
        | some ns =>
          simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]
          by_cases hty : st3.mem.hasTy ns (.ptr .u32) = true
          · simp only [hty, ↓reduceIte, Env.set, String.reduceEq]
            apply WPC.seq
            apply WPC.ite_any
            · apply WPC.seq
              apply WPC.setField_bud hb4 (by decide) (by decide)
              intro m' hb'
              apply WPC.ret
              embc_simp
              apply hQ
              refine ⟨rfl, w - 1#32 - nc, mm - nc, hb', ?_, ?_⟩
              · cost_simp; rw [hw2n]; omega
              · cost_simp; rw [hm3n]; omega
            · apply WPC.skip
              wpc_simp
              apply WPC.seq
              apply WPC.setField_bud hb4 (by decide) (by decide)
              intro m4 hb5
              wpc_simp
              apply WPC.setField_bud hb5 (by decide) (by decide)
              intro m5 hb6
              wpc_simp
              apply hQ
              refine ⟨⟨_, _, rfl⟩, w - 1#32 - nc, mm - nc, hb6, ?_, ?_⟩
              · cost_simp; rw [hw2n]; omega
              · cost_simp; rw [hm3n]; omega
          · simp [hty]
      apply WPC.seq
      apply WPC.ite_any
      · -- the stack cannot grow any more
        apply WPC.seq
        apply WPC.setField_bud hb1 (by decide) (by decide)
        intro m' hb'
        apply WPC.ret
        embc_simp
        exact ⟨rfl, w - 1#32, mm, hb', by cost_arith, by cost_arith⟩
      apply WPC.skip
      wpc_simp
      apply WPC.seq
      apply WPC.assign_u32 (by rfl)
      intro nc
      wpc_simp
      apply WPC.seq
      apply WPC.ite_any
      · apply WPC.assign
        embc_simp
        apply key 256#32
        intro o e s c h; exact PushMidC.mono h (by cost_arith) (by cost_arith)
      · apply WPC.skip
        wpc_simp
        apply key nc
        intro o e s c h; exact PushMidC.mono h (by cost_arith) (by cost_arith)
    · apply WPC.skip
      wpc_simp
      exact ⟨⟨_, _, rfl⟩, w - 1#32, mm, hb1, by cost_arith, by cost_arith⟩
  · intro o env' st' c hmid
    cases o with
    | normal =>
      obtain ⟨⟨ns, nc, rfl⟩, w', mm', hb', hc, hcm⟩ := hmid
      wpc_auto
      wpc_finish
    | brk => exact hmid.elim
    | ret rv =>
      obtain ⟨rfl, w', mm', hb', hc, hcm⟩ := hmid
      wpc_finish

fncost_register "push" push push_cost

end Vbcf.Proof
