import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.ReplaySpecs

/-!
# Vbcf proofs: `ck_rule`, the rule dispatcher

`ck_rule(st, rule, np, na)` is a chain of fifty `if (rule == CODE) r = r_xxx(st, np, na);`
tests, falling through to `NOID`.  Its specification is `RuleSpec` for
`applyRule rwTable … (Rule.ofCode code)`, with the code as an extra argument.

The chain is proved once, generically, for any table of (code, function) pairs
whose functions meet the corresponding entry specification (`dispatch_wp`);
the fifty entries are then discharged from `RuleSpecs`, one `decide` per code.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- `WP.call` with the argument values given explicitly, so that the continuation's
hypothesis is not simplified. -/
theorem WP.call' {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {dst : Option Var} {f : String}
    {args : List Expr} {vs : List EmbC.Val}
    {pre : List EmbC.Val → (KernelState P State) → Prop} {post : List EmbC.Val → (KernelState P State) → Option EmbC.Val → (KernelState P State) → Prop}
    (hspec : FnSpec (State := State) P f pre post) (hargs : evalArgs P env st.mem args = some vs)
    (hpre : pre vs st)
    (hk : ∀ rv st', post vs st rv st' →
      match assignDst env st'.mem dst rv with
      | none => False
      | some env' => Q .normal env' st') :
    WP P (.call dst f args) Q env st := by
  apply WP.call hspec
  rw [hargs]
  exact ⟨hpre, hk⟩

/-- The dispatcher's specification: `RuleSpec` for `applyRule` at the given code. -/
def CkRuleSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : VSt) (code : BitVec 32)
    (prems params : List Nat),
    FnSpec (State := State) Vbcf.prog "ck_rule"
      (fun vs s => vs = [.ptr sb 0, .u32 code, uv prems.length, uv params.length] ∧
        Holds W s.mem sb c ∧ RInv W X c st ∧ PremsAt c st prems ∧ ParamsAt W c params ∧
        c.k.sp = 0#32)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧
        (r ≠ noid → ∃ (st' : VSt) (f : Nat),
          applyRule rwTable X.goal X.bi X.ei st (Rule.ofCode code.toNat) prems params =
            some (st'.toSt, f) ∧
          RInv W X c' st' ∧ st'.lv f ∧ r.toNat = st'.id f ∧ StepFrame c c'))

/-- One entry of the dispatch table meets `RuleSpec (State := State)` for its code. -/
def EntrySpec (k : BitVec 32) (f : String) : Prop :=
  RuleSpec (State := State) f (fun X st pr pa => applyRule rwTable X.goal X.bi X.ei st (Rule.ofCode k.toNat) pr pa)

/-- The `if … else if …` chain for a table. -/
def dispatch : List (BitVec 32 × String) → Stmt
  | [] => .skip
  | (k, f) :: rest =>
    .ite (.bin .eq (.var "rule") (.lit32 k))
      (Stmt.block [.call (some "r") f [.var "st", .var "np", .var "na"]])
      (dispatch rest)

def ruleTable : List (BitVec 32 × String) :=
  [(0x0001, "r_assume"), (0x0002, "r_evaluate"), (0x0003, "r_distinct_values"),
   (0x0004, "r_aci_norm"), (0x0005, "r_absorb"), (0x0006, "r_rewrite"), (0x0007, "r_refl"),
   (0x0008, "r_symm"), (0x0009, "r_trans"), (0x000a, "r_cong"), (0x000b, "r_true_intro"),
   (0x000c, "r_true_elim"), (0x000d, "r_false_intro"), (0x000e, "r_false_elim"),
   (0x2001, "r_resolution"), (0x2002, "r_factoring"), (0x2003, "r_reordering"),
   (0x2004, "r_split"), (0x2005, "r_eq_resolve"), (0x2006, "r_modus_ponens"),
   (0x2007, "r_not_not_elim"), (0x2008, "r_contra"), (0x2009, "r_and_elim"),
   (0x200a, "r_and_intro"), (0x200b, "r_not_or_elim"), (0x200c, "r_implies_elim"),
   (0x200d, "r_not_implies_elim"), (0x200e, "r_equiv_elim"), (0x200f, "r_not_equiv_elim"),
   (0x2010, "r_xor_elim"), (0x2011, "r_not_xor_elim"), (0x2012, "r_ite_elim"),
   (0x2013, "r_not_ite_elim"), (0x2014, "r_not_and"), (0x2015, "r_cnf_and_pos"),
   (0x2016, "r_cnf_and_neg"), (0x2017, "r_cnf_or_pos"), (0x2018, "r_cnf_or_neg"),
   (0x2019, "r_cnf_implies_pos"), (0x201a, "r_cnf_implies_neg"), (0x201b, "r_cnf_equiv_pos"),
   (0x201c, "r_cnf_equiv_neg"), (0x201d, "r_cnf_xor_pos"), (0x201e, "r_cnf_xor_neg"),
   (0x201f, "r_cnf_ite_pos"), (0x2020, "r_cnf_ite_neg"), (0x2021, "r_ite_eq"),
   (0x4001, "r_bitblast"), (0x4002, "r_poly_norm"), (0x4003, "r_poly_norm_eq")]

theorem ckRule_body :
    ckRule.body = .seq (.assign "r" NOID) (.seq (dispatch ruleTable) (.ret (some (.var "r")))) := rfl

/-- What holds after the chain: `r` is `NOID` or the result of the rule for the code. -/
def DispatchRet (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : VSt) (prems params : List Nat)
    (code : BitVec 32) : (Post prog State) := fun o env s' =>
  o = .normal ∧ ∃ r, env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("rule", .u32, .u32 code),
      ("np", .u32, uv prems.length), ("na", .u32, uv params.length), ("r", .u32, .u32 r)] ∧
    ∃ c', Holds W s'.mem sb c' ∧ (r ≠ noid → ∃ (st' : VSt) (f : Nat),
      applyRule rwTable X.goal X.bi X.ei st (Rule.ofCode code.toNat) prems params =
        some (st'.toSt, f) ∧
      RInv W X c' st' ∧ st'.lv f ∧ r.toNat = st'.id f ∧ StepFrame c c')

theorem dispatch_wp (tbl : List (BitVec 32 × String)) (hall : ∀ k f, (k, f) ∈ tbl → EntrySpec (State := State) k f)
    (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : VSt) (prems params : List Nat)
    (code : BitVec 32) (s : (KernelState prog State)) (h : Holds W s.mem sb c) (hinv : RInv W X c st)
    (hprem : PremsAt c st prems) (hpar : ParamsAt W c params) (hsp : c.k.sp = 0#32) :
    WP Vbcf.prog (dispatch tbl) (DispatchRet W sb c X st prems params code)
      [("st", .ptr (.struct "ck"), .ptr sb 0), ("rule", .u32, .u32 code),
       ("np", .u32, uv prems.length), ("na", .u32, uv params.length), ("r", .u32, .u32 noid)] s := by
  induction tbl with
  | nil =>
    apply WP.skip
    exact ⟨rfl, noid, rfl, c, h, fun hne => absurd rfl hne⟩
  | cons kf rest ih =>
    obtain ⟨k, f⟩ := kf
    simp only [dispatch]
    apply WP.ite
    embc_simp
    constructor
    · intro hk
      subst hk
      simp only [Stmt.block]
      have hspec := hall code f List.mem_cons_self W sb c X st prems params
      apply WP.call' hspec (vs := [.ptr sb 0, uv prems.length, uv params.length]) (by embc_simp)
        ⟨rfl, h, hinv, hprem, hpar, hsp⟩
      intro rv s' hpost
      obtain ⟨c', hpost⟩ := hpost
      obtain ⟨r, rfl, h', hr⟩ := hpost
      embc_simp
      exact ⟨rfl, r, rfl, c', h', hr⟩
    · intro _
      exact ih (fun k' f' hm => hall k' f' (List.mem_cons_of_mem _ hm))

/-! ## The table entries -/

theorem ofCode_0001 : Rule.ofCode (0x0001 : BitVec 32).toNat = .assume := by decide
theorem ofCode_0002 : Rule.ofCode (0x0002 : BitVec 32).toNat = .evaluate := by decide
theorem ofCode_0003 : Rule.ofCode (0x0003 : BitVec 32).toNat = .distinctValues := by decide
theorem ofCode_0004 : Rule.ofCode (0x0004 : BitVec 32).toNat = .aciNorm := by decide
theorem ofCode_0005 : Rule.ofCode (0x0005 : BitVec 32).toNat = .absorb := by decide
theorem ofCode_0006 : Rule.ofCode (0x0006 : BitVec 32).toNat = .rewrite := by decide
theorem ofCode_0007 : Rule.ofCode (0x0007 : BitVec 32).toNat = .refl := by decide
theorem ofCode_0008 : Rule.ofCode (0x0008 : BitVec 32).toNat = .symm := by decide
theorem ofCode_0009 : Rule.ofCode (0x0009 : BitVec 32).toNat = .trans := by decide
theorem ofCode_000a : Rule.ofCode (0x000a : BitVec 32).toNat = .cong := by decide
theorem ofCode_000b : Rule.ofCode (0x000b : BitVec 32).toNat = .trueIntro := by decide
theorem ofCode_000c : Rule.ofCode (0x000c : BitVec 32).toNat = .trueElim := by decide
theorem ofCode_000d : Rule.ofCode (0x000d : BitVec 32).toNat = .falseIntro := by decide
theorem ofCode_000e : Rule.ofCode (0x000e : BitVec 32).toNat = .falseElim := by decide
theorem ofCode_2001 : Rule.ofCode (0x2001 : BitVec 32).toNat = .resolution := by decide
theorem ofCode_2002 : Rule.ofCode (0x2002 : BitVec 32).toNat = .factoring := by decide
theorem ofCode_2003 : Rule.ofCode (0x2003 : BitVec 32).toNat = .reordering := by decide
theorem ofCode_2004 : Rule.ofCode (0x2004 : BitVec 32).toNat = .split := by decide
theorem ofCode_2005 : Rule.ofCode (0x2005 : BitVec 32).toNat = .eqResolve := by decide
theorem ofCode_2006 : Rule.ofCode (0x2006 : BitVec 32).toNat = .modusPonens := by decide
theorem ofCode_2007 : Rule.ofCode (0x2007 : BitVec 32).toNat = .notNotElim := by decide
theorem ofCode_2008 : Rule.ofCode (0x2008 : BitVec 32).toNat = .contra := by decide
theorem ofCode_2009 : Rule.ofCode (0x2009 : BitVec 32).toNat = .andElim := by decide
theorem ofCode_200a : Rule.ofCode (0x200a : BitVec 32).toNat = .andIntro := by decide
theorem ofCode_200b : Rule.ofCode (0x200b : BitVec 32).toNat = .notOrElim := by decide
theorem ofCode_200c : Rule.ofCode (0x200c : BitVec 32).toNat = .impliesElim := by decide
theorem ofCode_200d : Rule.ofCode (0x200d : BitVec 32).toNat = .notImpliesElim := by decide
theorem ofCode_200e : Rule.ofCode (0x200e : BitVec 32).toNat = .equivElim := by decide
theorem ofCode_200f : Rule.ofCode (0x200f : BitVec 32).toNat = .notEquivElim := by decide
theorem ofCode_2010 : Rule.ofCode (0x2010 : BitVec 32).toNat = .xorElim := by decide
theorem ofCode_2011 : Rule.ofCode (0x2011 : BitVec 32).toNat = .notXorElim := by decide
theorem ofCode_2012 : Rule.ofCode (0x2012 : BitVec 32).toNat = .iteElim := by decide
theorem ofCode_2013 : Rule.ofCode (0x2013 : BitVec 32).toNat = .notIteElim := by decide
theorem ofCode_2014 : Rule.ofCode (0x2014 : BitVec 32).toNat = .notAnd := by decide
theorem ofCode_2015 : Rule.ofCode (0x2015 : BitVec 32).toNat = .cnfAndPos := by decide
theorem ofCode_2016 : Rule.ofCode (0x2016 : BitVec 32).toNat = .cnfAndNeg := by decide
theorem ofCode_2017 : Rule.ofCode (0x2017 : BitVec 32).toNat = .cnfOrPos := by decide
theorem ofCode_2018 : Rule.ofCode (0x2018 : BitVec 32).toNat = .cnfOrNeg := by decide
theorem ofCode_2019 : Rule.ofCode (0x2019 : BitVec 32).toNat = .cnfImpliesPos := by decide
theorem ofCode_201a : Rule.ofCode (0x201a : BitVec 32).toNat = .cnfImpliesNeg := by decide
theorem ofCode_201b : Rule.ofCode (0x201b : BitVec 32).toNat = .cnfEquivPos := by decide
theorem ofCode_201c : Rule.ofCode (0x201c : BitVec 32).toNat = .cnfEquivNeg := by decide
theorem ofCode_201d : Rule.ofCode (0x201d : BitVec 32).toNat = .cnfXorPos := by decide
theorem ofCode_201e : Rule.ofCode (0x201e : BitVec 32).toNat = .cnfXorNeg := by decide
theorem ofCode_201f : Rule.ofCode (0x201f : BitVec 32).toNat = .cnfItePos := by decide
theorem ofCode_2020 : Rule.ofCode (0x2020 : BitVec 32).toNat = .cnfIteNeg := by decide
theorem ofCode_2021 : Rule.ofCode (0x2021 : BitVec 32).toNat = .iteEq := by decide
theorem ofCode_4001 : Rule.ofCode (0x4001 : BitVec 32).toNat = .bitblast := by decide
theorem ofCode_4002 : Rule.ofCode (0x4002 : BitVec 32).toNat = .polyNorm := by decide
theorem ofCode_4003 : Rule.ofCode (0x4003 : BitVec 32).toNat = .polyNormEq := by decide

theorem ruleTable_specs (hR : RuleSpecs (State := State)) : ∀ k f, (k, f) ∈ ruleTable → EntrySpec (State := State) k f := by
  intro k f hm
  simp only [ruleTable, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  unfold EntrySpec
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [ofCode_0001]; exact hR.assume
  · rw [ofCode_0002]; exact hR.evaluate
  · rw [ofCode_0003]; exact hR.distinctValues
  · rw [ofCode_0004]; exact hR.aciNorm
  · rw [ofCode_0005]; exact hR.absorb
  · rw [ofCode_0006]; exact hR.rewrite
  · rw [ofCode_0007]; exact hR.refl
  · rw [ofCode_0008]; exact hR.symm
  · rw [ofCode_0009]; exact hR.trans
  · rw [ofCode_000a]; exact hR.cong
  · rw [ofCode_000b]; exact hR.trueIntro
  · rw [ofCode_000c]; exact hR.trueElim
  · rw [ofCode_000d]; exact hR.falseIntro
  · rw [ofCode_000e]; exact hR.falseElim
  · rw [ofCode_2001]; exact hR.resolution
  · rw [ofCode_2002]; exact hR.factoring
  · rw [ofCode_2003]; exact hR.reordering
  · rw [ofCode_2004]; exact hR.split
  · rw [ofCode_2005]; exact hR.eqResolve
  · rw [ofCode_2006]; exact hR.modusPonens
  · rw [ofCode_2007]; exact hR.notNotElim
  · rw [ofCode_2008]; exact hR.contra
  · rw [ofCode_2009]; exact hR.andElim
  · rw [ofCode_200a]; exact hR.andIntro
  · rw [ofCode_200b]; exact hR.notOrElim
  · rw [ofCode_200c]; exact hR.impliesElim
  · rw [ofCode_200d]; exact hR.notImpliesElim
  · rw [ofCode_200e]; exact hR.equivElim
  · rw [ofCode_200f]; exact hR.notEquivElim
  · rw [ofCode_2010]; exact hR.xorElim
  · rw [ofCode_2011]; exact hR.notXorElim
  · rw [ofCode_2012]; exact hR.iteElim
  · rw [ofCode_2013]; exact hR.notIteElim
  · rw [ofCode_2014]; exact hR.notAnd
  · rw [ofCode_2015]; exact hR.cnfAndPos
  · rw [ofCode_2016]; exact hR.cnfAndNeg
  · rw [ofCode_2017]; exact hR.cnfOrPos
  · rw [ofCode_2018]; exact hR.cnfOrNeg
  · rw [ofCode_2019]; exact hR.cnfImpliesPos
  · rw [ofCode_201a]; exact hR.cnfImpliesNeg
  · rw [ofCode_201b]; exact hR.cnfEquivPos
  · rw [ofCode_201c]; exact hR.cnfEquivNeg
  · rw [ofCode_201d]; exact hR.cnfXorPos
  · rw [ofCode_201e]; exact hR.cnfXorNeg
  · rw [ofCode_201f]; exact hR.cnfItePos
  · rw [ofCode_2020]; exact hR.cnfIteNeg
  · rw [ofCode_2021]; exact hR.iteEq
  · rw [ofCode_4001]; exact hR.bitblast
  · rw [ofCode_4002]; exact hR.polyNorm
  · rw [ofCode_4003]; exact hR.polyNormEq

/-- **`ck_rule`** dispatches to the rule of the code. -/
theorem ck_rule_spec (hR : RuleSpecs (State := State)) : CkRuleSpec (State := State) := by
  intro W sb c X st code prems params
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckRule) rfl
  rintro vs s ⟨rfl, h, hinv, hprem, hpar, hsp⟩
  simp [ckRule, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [initLocals, List.map, Ty.zero]
  change WP Vbcf.prog (.seq (.assign "r" NOID) (.seq (dispatch ruleTable) (.ret (some (.var "r"))))) _ _ _
  apply WP.seq
  apply WP.assign
  embc_simp
  apply WP.seq
  refine WP.mono (dispatch_wp ruleTable (ruleTable_specs hR) W sb c X st prems params code s
    h hinv hprem hpar hsp) ?_
  intro o env' s' hq
  obtain ⟨rfl, r, rfl, c', h', hr⟩ := hq
  apply WP.ret
  embc_simp [retPost]
  exact ⟨c', h', hr⟩

end Vbcf.Proof
