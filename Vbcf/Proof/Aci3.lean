import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Aci2

/-!
# Vbcf proofs: the Aci family, part 3 — `aci_flat`

`aci_flat` pushes the leaves of the same-operator tree below a node, in order, dropping
identity elements; it recurses in C with a depth counter, so its specification
`AciFlatSpecD d` is indexed by the depth and proved by strong induction.  On success the
pushed list is the Lean `flatten pool op i`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


theorem aci_tick_stk (c : CMem) : (tickM c).2.stk = c.stk ∧ (tickM c).2.k.sp = c.k.sp := by
  unfold tickM; split <;> exact ⟨rfl, rfl⟩

theorem StkTop.aci_frame {c c' : CMem} {st : VSt} {base : Nat} {is : List Nat}
    (ht : StkTop c st base is) (hs : c'.stk = c.stk ∧ c'.k.sp = c.k.sp) : StkTop c' st base is :=
  StkTop.built ht (VExt.refl st) hs

/-- The flattening of a same-operator node, child by child. -/
theorem aci_flatten_node {pool : Pool} {op : Op} {i : Nat} {n : Node} (hn : pool[i]? = some n)
    (hs : sameAssoc op n.op = true) (hlt : ∀ a ∈ n.args, a < i) :
    flatten pool op i = n.args.toList.flatMap (flatten pool op) := by
  rw [flatten_node' hn hs]
  have : ∀ l : List Nat, (∀ a ∈ l, a < i) →
      l.flatMap (childLeaves pool op i) = l.flatMap (flatten pool op) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons]
      rw [ih (fun b hb => hl b (by simp [hb]))]
      unfold childLeaves
      rw [ite_eq_left (hl a (by simp))]
  exact this _ (fun a ha => hlt a (by simpa using ha))

/-- The first `k + 1` children. -/
theorem aci_flatMap_take_succ {f : Nat → List Nat} {l : List Nat} {k : Nat} (hk : k < l.length) :
    (l.take (k + 1)).flatMap f = (l.take k).flatMap f ++ f l[k] := by
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
  simp

def AciFlatSpecD (d : BitVec 32) : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (op : Op) (i base : Nat) (is : List Nat),
    FnSpec (State := State) Vbcf.prog "aci_flat"
      (fun vs s => vs = [.ptr sb 0, uv (opHdr op), uv (st.id i), .u32 d] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv i ∧
        ¬ IsLeaf op ∧ opLo op < 256 ∧ opHi op < 256 ∧ StkTop c st base is)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ AciRet W sb X c0 prems params st
        (fun r c' => r ≠ 0#32 → StkTop c' st base (is ++ flatten st.pool op i)) r s')

def AciFlatSpec : Prop := ∀ d, AciFlatSpecD (State := State) d

/-- Loop invariant of `aci_flat`: the leaves of the first `k` children are on the stack. -/
def AciFlatInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (op : Op) (i : Nat) (d : BitVec 32) (args : Array Nat) (base : Nat) (is : List Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (r : BitVec 32), env = [("st", .ptr (.struct "ck"), .ptr sb 0),
      ("rop", .u32, uv (opHdr op)), ("i", .u32, uv (st.id i)), ("depth", .u32, .u32 d),
      ("r", .u32, .u32 r), ("n", .u32, uv args.size), ("k", .u32, uv k)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ k ≤ args.size ∧
    StkTop c' st base (is ++ (args.toList.take k).flatMap (flatten st.pool op))

theorem aci_flat_specD (d : BitVec 32) (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → AciFlatSpecD (State := State) d') :
    AciFlatSpecD (State := State) d := by
  intro W sb X c0 c prems params st op i base is
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciFlat) rfl
  rintro vs s ⟨rfl, h, hR, hi, hl, hlo, hhi, htop⟩
  simp [aciFlat, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := aciFlat) rfl
  simp only [aciFlat, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨n, hn⟩ := node_of_lv hi
  have hf := hR.core.rep.fits i n hn
  apply WP.guard_lit
  rule_simp
  refine ⟨fun hd => ⟨c, h, hR, by simp⟩, fun hd => ?_⟩
  apply WP.call_seq (tick_spec W sb c) (by rule_simp) ⟨rfl, h⟩
  rintro rv s1 ⟨rfl, h1⟩
  have hR1 := hR.aci_tick
  have htop1 := htop.aci_frame (aci_tick_stk c)
  clear h hR htop
  have hlt := aci_tick_cases c
  generalize (tickM c).1 = t at hlt ⊢
  generalize (tickM c).2 = c1 at h1 hR1 htop1
  have h := h1
  have hR := hR1
  have htop := htop1
  clear h1 hR1 htop1
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun ht => ⟨c1, h, hR, by simp⟩, fun ht => ?_⟩
  apply WP.call_seq (aci_same_spec X.posOf op n) (by rule_simp [hR.core.rdHdr hn])
    ⟨rfl, hl, hlo, hhi, hf⟩
  rintro rv s2 ⟨rfl, rfl⟩
  rule_simp
  apply WP.ite_seq
  by_cases hsa : sameAssoc op n.op = true
  · rule_simp [hsa]
    have hl' : ¬ IsLeaf n.op := by
      by_cases hc : isConcatOp op = true
      · obtain ⟨w, rfl⟩ := (isConcatOp_iff _).mp hc
        rw [sameAssoc_concat] at hsa
        obtain ⟨w', e⟩ := (isConcatOp_iff _).mp hsa
        rw [e]; simp [IsLeaf, isLeaf]
      · rw [sameAssoc_of_not_concat (by simpa using hc)] at hsa
        rw [beq_iff_eq.mp hsa]; exact hl
    obtain ⟨args, e, hsz, -, hargs⟩ := hR.core.argsN hn rfl hl'
    rw [e] at hn hsa
    clear e
    simp only at hsa
    rule_assign [hR.core.rdN hn hl']
    apply WP.loop_seq (AciFlatInv W sb X c0 prems params st op i d args base is)
    · exact ⟨c1, 0, _, rfl, h, hR, by omega, by simpa using htop⟩
    clear h hR htop
    rintro env s' ⟨c', k, r, rfl, h, hR, hk, htop⟩
    rule_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · apply WP.ret
      rule_simp [LoopQ, RetQ]
      refine ⟨c', h, hR, fun _ => ?_⟩
      rw [aci_flatten_node hn hsa (fun a ha => hR.core.ok.args_lt hn a ha)]
      have : k = args.size := by omega
      subst this
      rw [List.take_of_length_le (by simp)] at htop
      exact htop
    have hak := hargs k hlt
    have hd1 : (d - 1#32).toNat < d.toNat := by
      have : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
      rw [bv_sub_toNat (by simp; omega)]; simp; omega
    apply WP.call_seq (IH (d - 1#32) hd1 W sb X c0 c' prems params st op args[k] base _)
      (by rule_simp [hR.core.rdN hn hl']) ⟨rfl, h, hR, hak, hl, hlo, hhi, htop⟩
    rintro rv s3 ⟨r2, rfl, c3, h3, hR3, hr2⟩
    clear h hR
    have h := h3
    have hR := hR3
    clear h3 hR3
    rule_simp
    apply WP.guard_lit
    rule_simp
    refine ⟨fun he => ⟨c3, h, hR, by simp⟩, fun hne => ?_⟩
    apply WP.assign_loop
    rule_simp
    refine ⟨c3, k + 1, r2, by simp, h, hR, by omega, ?_⟩
    rw [aci_flatMap_take_succ (by simpa using hlt)]
    simpa using hr2 hne
  rule_simp [hsa]
  have hfl := flatten_leaf hn (by simpa using hsa)
  apply WP.call_seq (aci_nil_spec W sb X c0 c1 prems params st op i n) (by rule_simp)
    ⟨rfl, h, hR, hn, by vlv, hlo, hhi⟩
  rintro rv s3 ⟨rfl, rfl⟩
  rule_simp
  apply WP.guard_lit
  by_cases hnil : isNilElem op n = true
  · rule_simp [hnil]
    refine ⟨c1, h, hR, fun _ => ?_⟩
    rw [hfl, ite_eq_left hnil]; simpa using htop
  rule_simp [hnil]
  rw [hfl, ite_eq_right hnil]
  apply WP.rule_push h hR
  rule_simp
  intro s4 c4 ok h4 hP
  apply WP.ret
  rule_simp [RetQ]
  exact ⟨c4, h4, hP.1, fun hok => StkTop.push htop hP hok hi⟩

theorem aci_flat_spec : AciFlatSpec (State := State) := by
  intro d
  induction h : d.toNat using Nat.strongRecOn generalizing d with
  | _ n ih => exact aci_flat_specD d (fun d' hd' => ih d'.toNat (h ▸ hd') d' rfl)

end Vbcf.Proof
