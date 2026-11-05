import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Aci1
import Vbcf.Proof.Core1

/-!
# Vbcf proofs: the Aci family, part 2 — `aci_absorb` and `r_absorb`

`aci_absorb` recurses in C with a depth counter; its specification `AciAbsorbSpecD d` is
indexed by the depth and proved by strong induction on it.  When it returns 1, the Lean
`absorbF` answers `true` for every fuel above the node's index.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- What a helper that builds nothing guarantees when it returns `r`: the rule context
still holds (for the same Lean state) and `R r c'` for the final C state. -/
def AciRet (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (R : BitVec 32 → CMem → Prop) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ R r c'

section
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}

/-- `tick` keeps the rule context. -/
theorem RCtx.aci_tick (hR : RCtx W X c0 prems params c st) :
    RCtx W X c0 prems params (tickM c).2 st := by
  have hok := hR.core.stk
  unfold tickM
  split
  · exact hR.after_push (by constructor <;> rfl) ⟨hok.null, hok.size, hok.cap⟩
  · exact hR.after_push (by constructor <;> rfl) ⟨hok.null, hok.size, hok.cap⟩

/-- Setting the error flag keeps the rule context. -/
theorem RCtx.aci_err (hR : RCtx W X c0 prems params c st) (e : BitVec 32) :
    RCtx W X c0 prems params { c with k := { c.k with err := e } } st := by
  have hok := hR.core.stk
  exact hR.after_push (by constructor <;> rfl) ⟨hok.null, hok.size, hok.cap⟩

end

theorem aci_tick_cases (c : CMem) : (tickM c).1 = 0#32 ∨ (tickM c).1 = 1#32 := by
  unfold tickM; split <;> simp

/-! ## Lean side: `absorbF` -/

theorem aci_absorbF_zero {pool : Pool} {op : Op} {i : Nat} {n : Node} (hn : pool[i]? = some n)
    (hz : isZeroElem op n = true) : ∀ f, i < f → absorbF pool op f i = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp [absorbF, hn, hz]

theorem aci_absorbF_child {pool : Pool} {op : Op} {i : Nat} {args : Array Nat}
    (hn : pool[i]? = some ⟨op, args⟩) {k : Nat} (hk : k < args.size) (hlt : args[k] < i)
    (hc : ∀ f, args[k] < f → absorbF pool op f args[k] = true) :
    ∀ f, i < f → absorbF pool op f i = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp only [absorbF, hn, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, Array.any_eq_true]
  right
  exact ⟨k, hk, by simp [hlt, hc g (by omega)]⟩

/-! ## `aci_absorb` -/

def AciAbsorbSpecD (d : BitVec 32) : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (op : Op) (i : Nat),
    FnSpec (State := State) Vbcf.prog "aci_absorb"
      (fun vs s => vs = [.ptr sb 0, uv (opHdr op), uv (st.id i), .u32 d] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv i ∧
        ¬ IsLeaf op ∧ opLo op < 256 ∧ opHi op < 256)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ AciRet W sb X c0 prems params st
        (fun r _ => r = 1#32 → ∀ f, i < f → absorbF st.pool op f i = true) r s')

/-- Loop invariant of `aci_absorb`: the first `k` children have been searched. -/
def AciAbsInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (op : Op) (i : Nat) (d : BitVec 32) (args : Array Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (r : BitVec 32), env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("rop", .u32, uv (opHdr op)),
      ("i", .u32, uv (st.id i)), ("depth", .u32, .u32 d), ("r", .u32, .u32 r),
      ("n", .u32, uv args.size), ("k", .u32, uv k)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ k ≤ args.size

def AciAbsorbSpec : Prop := ∀ d, AciAbsorbSpecD (State := State) d

theorem aci_absorb_specD (d : BitVec 32) (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → AciAbsorbSpecD (State := State) d') :
    AciAbsorbSpecD (State := State) d := by
  intro W sb X c0 c prems params st op i
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciAbsorb) rfl
  rintro vs s ⟨rfl, h, hR, hi, hl, hlo, hhi⟩
  simp [aciAbsorb, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := aciAbsorb) rfl
  simp only [aciAbsorb, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨n, hn⟩ := node_of_lv hi
  have hf := hR.core.rep.fits i n hn
  apply WP.ifRet
  rule_simp
  refine ⟨fun hd => ⟨c, h, hR, by simp⟩, fun hd => ?_⟩
  apply WP.call_seq (tick_spec W sb c) (by rule_simp) ⟨rfl, h⟩
  rintro rv s1 ⟨rfl, h1⟩
  have hR1 := hR.aci_tick
  clear h hR
  have hlt := aci_tick_cases c
  generalize (tickM c).1 = t at hlt ⊢
  generalize (tickM c).2 = c1 at h1 hR1
  have h := h1
  have hR := hR1
  clear h1 hR1
  rule_simp
  apply WP.ifRet
  rule_simp
  refine ⟨fun ht => ⟨c1, h, hR, by simp⟩, fun ht => ?_⟩
  apply WP.call_seq (aci_zero_spec W sb X c0 c1 prems params st op i n) (by rule_simp)
    ⟨rfl, h, hR, hn, by vlv, hlo, hhi⟩
  rintro rv s2 ⟨rfl, rfl⟩
  rule_simp
  apply WP.ifRet
  by_cases hz : isZeroElem op n = true
  · rule_simp [hz]
    exact ⟨c1, h, hR, fun _ => aci_absorbF_zero hn hz⟩
  rule_simp [hz]
  apply WP.ifRet
  rule_simp [hR.core.rdHdr hn, aci_hdr_mask hf, aci_opHdr_inj hl hf.lo hf.hi hlo hhi]
  refine ⟨fun hop => ⟨c1, h, hR, by simp⟩, fun hop => ?_⟩
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop hl
  rule_assign [hR.core.rdN hn hl]
  apply WP.loop_seq (AciAbsInv W sb X c0 prems params st op i d args)
  · exact ⟨c1, 0, _, rfl, h, hR, by omega⟩
  clear h hR
  rintro env s' ⟨c', k, r, rfl, h, hR, hk⟩
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.ret
    rule_simp [RetQ]
    exact ⟨c', h, hR, by simp⟩
  have hak := hargs k hlt
  have hd1 : (d - 1#32).toNat < d.toNat := by
    have : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [bv_sub_toNat (by simp; omega)]; simp; omega
  apply WP.call_seq (IH (d - 1#32) hd1 W sb X c0 c' prems params st op args[k])
    (by rule_simp [hR.core.rdN hn hl]) ⟨rfl, h, hR, hak, hl, hlo, hhi⟩
  rintro rv s3 ⟨r2, rfl, c3, h3, hR3, hr2⟩
  clear h hR
  have h := h3
  have hR := hR3
  clear h3 hR3
  rule_simp
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hne => ?_, fun he => ?_⟩
  · apply WP.ret
    rule_simp [LoopQ, RetQ]
    refine ⟨c3, h, hR, fun e => ?_⟩
    exact aci_absorbF_child hn hlt (hR.core.ok.args_lt hn _ (Array.getElem_mem hlt)) (hr2 e)
  apply WP.assign_loop
  rule_simp
  exact ⟨c3, k + 1, r2, by simp, h, hR, by omega⟩

end Vbcf.Proof

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem aci_absorb_spec : AciAbsorbSpec (State := State) := by
  intro d
  induction h : d.toNat using Nat.strongRecOn generalizing d with
  | _ n ih => exact aci_absorb_specD d (fun d' hd' => ih d'.toNat (h ▸ hd') d' rfl)

theorem aci_zero_not_leaf {op : Op} {n : Node} (h : isZeroElem op n = true) : ¬ IsLeaf op := by
  unfold isZeroElem at h
  split at h <;> simp_all [IsLeaf, isLeaf]

theorem r_absorb_spec :
    RuleSpec (State := State) "r_absorb" (fun X st pr pa => ruleAbsorb X.ei st pr pa) := by
  rule_begin rAbsorb
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  rule_assign [hR.core.rd2 hn]
  rule_assign [hR.core.rd2 hn]
  obtain ⟨na, hna⟩ := node_of_lv ha
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  have hfa := hR.core.rep.fits a na hna
  rule_assign [hR.core.rdHdr hna, aci_hdr_mask hfa]
  apply WP.call_seq (aci_zero_spec W sb X c c [] [x] st na.op b nb) (by rule_simp)
    ⟨rfl, h, hR, hnb, by vlv, hfa.lo, hfa.hi⟩
  rintro rv s2 ⟨rfl, rfl⟩
  rule_simp
  rule_guard
  intro hz
  have hz' : isZeroElem na.op nb = true := by
    cases hc : isZeroElem na.op nb
    · simp [hc] at hz
    · rfl
  have hl := aci_zero_not_leaf hz'
  apply WP.call_seq (aci_absorb_spec 32#32 W sb X c c [] [x] st na.op a) (by rule_simp)
    ⟨rfl, h, hR, ha, hl, hfa.lo, hfa.hi⟩
  rintro rv s3 ⟨r3, rfl, c3, h3, hR3, hr3⟩
  clear h hR
  have h := h3
  have hR := hR3
  clear h3 hR3
  rule_simp
  rule_guard
  intro h1
  rule_ret
  exact hR.ret h he (by
    simp [ruleAbsorb, hee, St.node, hn, isEqNode, hna, hnb, hz', hr3 h1 (a + 1) (by omega)])

end Vbcf.Proof
