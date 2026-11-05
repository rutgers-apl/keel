import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay2
import Vbcf.Proof.Core1
import Vbcf.Proof.RuleLib

/-!
# Vbcf proofs: `ck_step`

One iteration of `Bcf.replay`: read the step header, copy the premises' facts
into the premise buffer (`getFacts`), point `st->par` at the parameters, and
dispatch (`ck_rule`).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## Storing the parameter pointer -/

section
variable {P : Prog} {W : World} {m : Mem} {sb : Nat} {c : CMem}

/-- `st->par = proof + o`: the only pointer-field store of the replay phase. -/
theorem Holds.setPar (hs : P.findStruct "ck" = some ckS) (h : Holds W m sb c) (o : Nat) :
    m.storeField P sb "par" (.ptr W.pb o) = some (m.setCell sb 14 (.ptr W.pb o)) ∧
    Holds W (m.setCell sb 14 (.ptr W.pb o)) sb { c with k := { c.k with par := some (W.pb, o) } } := by
  have hb := fun b' => Mem.block?_setCell (i := 14) (v := .ptr W.pb o) b' h.ck
  have hptr : ∀ a, ({ c.k with par := some (W.pb, o) } : CK).ptr a = c.k.ptr a := by
    intro a; cases a <;> rfl
  refine ⟨Mem.storeField_eq (by rw [ck_slot hs h.ck, fi_par]) (Mem.hasTy_ptr h.proof rfl)
    (by simp [CK.cells]), ?_, h.sbNew, h.pbOld, ?_, h.proofPtr, Or.inr ⟨o, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (m.setCell sb 14 _).block? sb = _
    rw [hb]; simp [CK.cells]
  · show (m.setCell sb 14 _).block? W.pb = _
    rw [hb]; simp [h.pb_ne_sb]; exact h.proof
  · intro a b o' hpa
    rw [hptr] at hpa
    obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a b o' hpa
    refine ⟨ho, hbs, hbb, ?_⟩
    show (m.setCell sb 14 _).block? b = _
    rw [hb]; simp [hbs]
    cases a <;> exact harr
  · intro a a' b b' o1 o2 hne hpa hpa'
    rw [hptr] at hpa hpa'
    exact h.sep a a' b b' o1 o2 hne hpa hpa'
  · intro b hlt hne
    rw [hb]
    have : b ≠ sb := by have := h.sbNew; omega
    simp [this]; exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]; simp [hne]
    exact h.exact b hge hne (fun a o' => by rw [← hptr]; exact hno a o')
  · intro b hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b hb'
    exact ⟨h1, h2, fun a o' => by rw [hptr]; exact h3 a o'⟩

end

section
variable {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {W : World} {sb : Nat} {c : CMem}

/-- `st->par = e` where `e` evaluates to a pointer into the proof block. -/
theorem WP.ck_setPar {p e : Expr}
    (hs : P.findStruct "ck" = some ckS) {m : Mem} (h : Holds W m sb c) (hm : st.mem = m)
    (H : match evalE P env st.mem p, evalE P env st.mem e with
      | some (.ptr b off), some (.ptr b2 o) =>
        b = sb ∧ off = 0 ∧ b2 = W.pb ∧
        ∀ st', Holds W st'.mem sb { c with k := { c.k with par := some (W.pb, o) } } →
          Q .normal env st'
      | _, _ => False) :
    WP P (.setField p "par" e) Q env st := by
  subst hm
  apply WP.setField
  split at H
  · rename_i b off b2 o hp he
    obtain ⟨rfl, rfl, rfl, H⟩ := H
    rw [hp, he]; dsimp only
    refine ⟨rfl, ?_⟩
    obtain ⟨hst, hh⟩ := h.setPar hs o
    rw [hst]; exact H _ hh
  · exact H.elim

end

/-! ## 32-bit arithmetic on the step header -/

theorem bv_stepPc (h : Nat) (hh : h < 2 ^ 32) :
    (BitVec.ofNat 32 h >>> 16) &&& 255#32 = BitVec.ofNat 32 (stepPc h) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_shr_16, bv_toNat_ofNat hh, bv_toNat_ofNat (by unfold stepPc; omega)]
  rfl

theorem bv_stepAc (h : Nat) (hh : h < 2 ^ 32) :
    BitVec.ofNat 32 h >>> 24 = BitVec.ofNat 32 (stepAc h) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_24, bv_toNat_ofNat hh, bv_toNat_ofNat (by unfold stepAc; omega)]
  rfl

theorem bv_stepRule (h : Nat) (hh : h < 2 ^ 32) :
    BitVec.ofNat 32 h &&& 65535#32 = BitVec.ofNat 32 (stepRule h) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, bv_toNat_ofNat hh, bv_toNat_ofNat (show stepRule h < 2 ^ 32 by unfold stepRule; omega)]
  exact LoadSpec.and_ffff h

theorem stepPc_lt (h : Nat) : stepPc h < 256 := by unfold stepPc; omega
theorem stepAc_lt (h : Nat) (hh : h < 2 ^ 32) : stepAc h < 256 := by unfold stepAc; omega

theorem uv_lt_iff {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a < BitVec.ofNat 32 b ↔ a < b := by
  rw [BitVec.lt_def, bv_toNat_ofNat ha, bv_toNat_ofNat hb]

theorem le_uv_iff {x : BitVec 32} {n : Nat} (h : n < 2 ^ 32) :
    x ≤ BitVec.ofNat 32 n ↔ x.toNat ≤ n := by
  rw [BitVec.le_def, bv_toNat_ofNat h]

/-- A comparison of two words, as numbers. -/
theorem lt_uv_iff' {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 b < BitVec.ofNat 32 a ↔ b < a := by
  rw [BitVec.lt_def, bv_toNat_ofNat ha, bv_toNat_ofNat hb]

theorem uv_succ {i : Nat} (h : i + 1 < 2 ^ 32) :
    BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [idx_add h, bv_toNat_ofNat h]

theorem uv_add3 {a b k : Nat} (h : a + b + k < 2 ^ 32) :
    (BitVec.ofNat 32 a + BitVec.ofNat 32 b + BitVec.ofNat 32 k).toNat = a + b + k := by
  rw [BitVec.toNat_add, idx_add (by omega), bv_toNat_ofNat (by omega)]
  exact Nat.mod_eq_of_lt h

theorem uv_eq_of_toNat {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, bv_toNat_ofNat (h ▸ x.isLt)]

theorem getElem?_map_range {α : Type} {n : Nat} {g : Nat → α} {j : Nat} {x : α}
    (h : ((List.range n).map g)[j]? = some x) : j < n ∧ x = g j := by
  by_cases hj : j < n
  · simp [hj] at h
    exact ⟨hj, h.symm⟩
  · simp [hj] at h

theorem getElem?_map_map_range {α β : Type} {n : Nat} {g : Nat → α} {f : α → β} {j : Nat} {x : β}
    (h : (((List.range n).map g).map f)[j]? = some x) : j < n ∧ x = f (g j) := by
  rw [List.map_map] at h
  exact getElem?_map_range h

/-! ## The specification -/

/-- `ck_step(st, off)` is one iteration of `replay`: if it returns an id, the Lean
rule for the step at `off` succeeds with the node that id denotes. -/
def CkStepSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (X : Ctx) (st : VSt)
    (off : BitVec 32) (s : Step) (rest : List Step),
    FnSpec (State := State) Vbcf.prog "ck_step"
      (fun vs s0 => vs = [.ptr sb 0, .u32 off] ∧ Holds W s0.mem sb c ∧
        SInv W ws X c st off.toNat (s :: rest))
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧
        (r ≠ noid → ∃ (prems : List Nat) (st' : VSt) (f : Nat),
          getFacts st.facts s.premises.toList = some prems ∧
          applyRule rwTable X.goal X.bi X.ei st s.rule prems s.params.toList = some (st'.toSt, f) ∧
          RInv W X c' st' ∧ st'.lv f ∧ r.toNat = st'.id f ∧ StepFrame c c' ∧ VExt st st'))

/-- The C state when `ck_rule` is called: premise buffer `P`, parameters at `o`. -/
def stepMem (W : World) (c : CMem) (P : Array EmbC.Val) (o : Nat) : CMem :=
  { c with prem := P, k := { c.k with sp := 0#32, par := some (W.pb, o) } }

/-- The premise-copying loop's invariant: `i` premises copied so far. -/
def PremLoop (W : World) (sb : Nat) (c : CMem) (st : VSt) (w : Nat → Nat) (off : BitVec 32)
    (q : Nat) : Env → (KernelState prog State) → Prop := fun env s1 =>
  ∃ (i : Nat) (kv : BitVec 32) (P : Array EmbC.Val),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("off", .u32, .u32 off), ("base", .u32, uv q),
      ("hdr", .u32, uv (w q)), ("pc", .u32, uv (stepPc (w q))), ("ac", .u32, uv (stepAc (w q))),
      ("i", .u32, uv i), ("k", .u32, .u32 kv), ("r", .u32, .u32 0)] ∧
    i ≤ stepPc (w q) ∧ Holds W s1.mem sb { c with prem := P } ∧ P.size = 256 ∧
    (∀ j, j < 256 → ∃ v, v < 2 ^ 32 ∧ U P j v) ∧
    (∀ j, j < i → w (q + 1 + j) < st.facts.size ∧ st.lv st.facts[w (q + 1 + j)]! ∧
      U P j (st.id st.facts[w (q + 1 + j)]!))

theorem ck_step_spec (hRule : CkRuleSpec (State := State)) : CkStepSpec (State := State) := by
  intro W sb c ws X st off s rest
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckStep) rfl
  rintro vs s0 ⟨rfl, h, hS⟩
  simp [ckStep, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  -- the step
  obtain ⟨hlt, hle, rfl, hrest⟩ := hS.steps
  have hwsz := hS.wsz
  have hlen := hS.hlen
  have hne := hS.nexpr
  have hw := fun i => wordFn_lt ws i
  -- `base`
  have hqlt : 3 + wordFn ws 1 + off.toNat < ws.size := by omega
  have hbase : 3#32 + c.k.nexpr + off = BitVec.ofNat 32 (3 + wordFn ws 1 + off.toNat) := by
    apply uv_eq_of_toNat
    rw [BitVec.toNat_add, BitVec.toNat_add, hne]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hpcw := stepPc_lt (wordFn ws (3 + wordFn ws 1 + off.toNat))
  have hacw := stepAc_lt (wordFn ws (3 + wordFn ws 1 + off.toNat)) (hw _)
  have hhdr : U c.proof (3 + wordFn ws 1 + off.toNat) (wordFn ws (3 + wordFn ws 1 + off.toNat)) :=
    hS.words _ (by omega) hqlt
  have hproofp : c.k.proof.val = .ptr W.pb 0 := by rw [hS.inv.proofPtr]; rfl
  apply WP.seq
  apply WP.assign
  ck_simp [hbase]
  apply WP.seq
  apply WP.assign
  ck_simp [hproofp, h.loadProof, bv_toNat_ofNat (show 3 + wordFn ws 1 + off.toNat < 2 ^ 32 by omega),
    rd_u32 hhdr]
  apply WP.seq
  apply WP.assign
  ck_simp [bv_stepPc _ (hw _)]
  apply WP.seq
  apply WP.assign
  ck_simp [bv_stepAc _ (hw _)]
  apply WP.seq
  apply WP.while (I := PremLoop W sb c st (wordFn ws) off (3 + wordFn ws 1 + off.toNat))
  · exact ⟨0, 0, c.prem, rfl, Nat.zero_le _, h, hS.inv.premSize, hS.inv.premCells,
      fun j hj => absurd hj (by omega)⟩
  intro env s1 hI
  obtain ⟨i, kv, P, rfl, hi, h, hP, hPc, hfacts⟩ := hI
  ck_simp [uv_lt_iff (show i < 2 ^ 32 by omega)
    (show stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) < 2 ^ 32 by omega)]
  constructor
  · -- loop exit: `i = pc`
    intro hge
    have hipc : i = stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) := by omega
    subst hipc
    have hpb : s1.mem.block? W.pb = some ⟨.u32, c.proof⟩ := h.proof
    have hidx2 : (BitVec.ofNat 32 (3 + wordFn ws 1 + off.toNat) + 1#32 +
        BitVec.ofNat 32 (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).toNat =
        3 + wordFn ws 1 + off.toNat + 1 + stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) :=
      uv_add3 (by omega)
    have hpsz := hS.proofSize
    have hle2 : 3 + wordFn ws 1 + off.toNat + 1 + stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) ≤
        c.proof.size := by omega
    apply WP.seq
    apply WP.ck_setPar hs h (by rfl)
    ck_simp [hproofp, hpb, hidx2, Ty.isStruct, hle2]
    intro s2 h
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s4 h
    -- the premises and parameters
    have hq32 : 3 + wordFn ws 1 + off.toNat < 2 ^ 32 := by omega
    have hpcs : ∀ k ∈ (List.range (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).map
        (fun k => wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + k)), k < st.facts.size := by
      intro k hk
      simp only [List.mem_map, List.mem_range] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      exact (hfacts j hj).1
    have hget := getFacts_map st.facts _ hpcs
    have hpl : (((List.range (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).map
        (fun k => wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + k))).map
        (fun k => st.facts[k]!)).length = stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) := by simp
    have hal : (((List.range (stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).map
        (fun k => wordFn ws (3 + wordFn ws 1 + off.toNat + 1 +
          stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) + k)))).length =
        stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat)) := by simp
    have hinv4' : RInv W X (stepMem W c P (3 + wordFn ws 1 + off.toNat + 1 +
        stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))) st :=
      hS.inv.same rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (by simp [stepMem]) ⟨hP, hPc⟩
    have hinv4 : RInv W (X.flr st) (stepMem W c P (3 + wordFn ws 1 + off.toNat + 1 +
        stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))) st :=
      hinv4'.reFloor rfl rfl rfl rfl
        (fun S0 h0 => by have := Option.some.inj h0; subst this; exact VExt.refl _)
    have hprems : PremsAt (stepMem W c P (3 + wordFn ws 1 + off.toNat + 1 +
        stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))) st (((List.range (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).map
        (fun k => wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + k))).map (fun k => st.facts[k]!)) := by
      refine ⟨by rw [hpl]; omega, ?_⟩
      intro j p hjp
      obtain ⟨hj, rfl⟩ := getElem?_map_map_range hjp
      obtain ⟨hk1, hlv, hu⟩ := hfacts j hj
      exact ⟨hlv, hu⟩
    have hpar : ParamsAt W (stepMem W c P (3 + wordFn ws 1 + off.toNat + 1 +
        stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))) ((List.range (stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).map
        (fun k => wordFn ws (3 + wordFn ws 1 + off.toNat + 1 +
          stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) + k))) := by
      refine ⟨by rw [hal]; omega, 3 + wordFn ws 1 + off.toNat + 1 +
        stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)), rfl,
        by rw [hal]; show _ ≤ c.proof.size; omega, ?_⟩
      intro j x hjx
      obtain ⟨hj, rfl⟩ := getElem?_map_range hjx
      exact ⟨hw _, hS.words _ (by omega) (by omega)⟩
    -- pay for the step's words
    apply WP.seq
    apply WP.call' (spend_spec W sb _ (1#32 + BitVec.ofNat 32 (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat))) +
        BitVec.ofNat 32 (stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat)))))
      (vs := [.ptr sb 0, .u32 (1#32 + BitVec.ofNat 32 (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat))) +
        BitVec.ofNat 32 (stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat))))])
      (by ck_simp) ⟨rfl, h⟩
    intro rv s4' hsp
    obtain ⟨rfl, h4⟩ := hsp
    rw [spendM_wev] at h4
    clear h
    have h := h4
    clear h4
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    constructor
    · intro _
      apply WP.ret
      ck_simp [retPost]
      exact ⟨_, h, fun hne => absurd rfl hne⟩
    intro _
    apply WP.skip
    apply WP.seq
    apply WP.call' (hRule W sb _ (X.flr st) st (BitVec.ofNat 32 (stepRule (wordFn ws (3 + wordFn ws 1 + off.toNat)))) _ _)
      (vs := [.ptr sb 0, .u32 (BitVec.ofNat 32 (stepRule (wordFn ws (3 + wordFn ws 1 + off.toNat)))),
        uv (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat))),
        uv (stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat)))])
      (by ck_simp [bv_stepRule _ (hw _)])
      ⟨by rw [hpl, hal], h, hinv4.wev, hprems, hpar, rfl⟩
    intro rv s5 hpost
    obtain ⟨c', hpost⟩ := hpost
    obtain ⟨r, rfl, h', hr⟩ := hpost
    embc_simp
    apply WP.ret
    embc_simp [retPost]
    refine ⟨c', h', ?_⟩
    intro hne
    obtain ⟨st', f, happ, hinv', hflt, hoff, hfr⟩ := hr hne
    have hext : VExt st st' := hinv'.floor st rfl
    have hinv'' : RInv W X c' st' := hinv'.reFloor rfl rfl rfl rfl
      (fun S0 h0 => by rw [hS.noFloor] at h0; cases h0)
    refine ⟨_, hget, st', f, ?_, hinv'', hflt, hoff, ?_, hext⟩
    · rw [bv_toNat_ofNat (by have := stepRule_lt (wordFn ws (3 + wordFn ws 1 + off.toNat)); omega)] at happ
      simpa [stepAt] using happ
    · exact StepFrame.trans (c' := (stepMem W c P (3 + wordFn ws 1 + off.toNat + 1 +
        stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).wev _ _ _)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hfr
  · -- loop body
    intro hilt
    have hidx : (BitVec.ofNat 32 (3 + wordFn ws 1 + off.toNat) + 1#32 + BitVec.ofNat 32 i).toNat =
        3 + wordFn ws 1 + off.toNat + 1 + i := uv_add3 (by omega)
    have hkcell : U c.proof (3 + wordFn ws 1 + off.toNat + 1 + i)
        (wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + i)) := hS.words _ (by omega) (by omega)
    apply WP.seq
    apply WP.assign
    ck_simp [hproofp, h.loadProof, hidx, rd_u32 hkcell]
    apply WP.seq
    apply WP.ite
    ck_simp [le_uv_iff (hw _), hS.flen]
    constructor
    · -- a premise index out of range: `NOID`
      intro hbig
      apply WP.ret
      ck_simp [retPost]
      exact ⟨_, h, fun hne => absurd rfl hne⟩
    · intro hsmall
      apply WP.skip
      have hklt : wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + i) < st.facts.size := by omega
      obtain ⟨f, hf⟩ : ∃ f, st.facts[wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + i)]? = some f :=
        ⟨_, Array.getElem?_eq_getElem hklt⟩
      -- `if (st->lr[k] < st->flen) { return NOID; }`
      have hfsz := hS.factsSize
      simp only [List.length_cons] at hfsz
      have hfl32 : st.facts.size < 2 ^ 32 := by have := hS.factsLt; omega
      obtain ⟨lb, hlrp⟩ := hS.lrPtr
      obtain ⟨lw, hlw, hlu⟩ := hS.lrCells (wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + i))
        (by rw [hS.lrSize]; omega)
      apply WP.seq
      apply WP.ite
      ck_simp [hlrp, h.rd_lr hlrp, bv_toNat_ofNat (hw _), rd_u32 hlu, hS.flen,
        lt_uv_iff' hfl32 hlw]
      constructor
      · intro _
        apply WP.ret
        ck_simp [retPost]
        exact ⟨_, h, fun hne => absurd rfl hne⟩
      intro hlrge
      apply WP.skip
      obtain ⟨hflt, hfcs⟩ := hS.facts _ _ hf
      obtain ⟨hflv, hfc⟩ := hfcs lw hlw hlu (by rw [BitVec.le_def, bv_toNat_ofNat hlw] at hlrge; exact hlrge)
      obtain ⟨fb, hfactsp⟩ := hS.factsPtr
      obtain ⟨qb, hpremp⟩ := hS.inv.premPtr
      apply WP.seq
      apply WP.ck_store .prem h (by rfl) hpremp
      ck_simp [hpremp, hfactsp, h.rd_facts hfactsp, bv_toNat_ofNat (hw _), rd_u32 hfc,
        bv_toNat_ofNat (show i < 2 ^ 32 by omega)]
      refine ⟨by omega, ?_⟩
      intro s2 h
      apply WP.assign
      ck_simp [uv_succ (show i + 1 < 2 ^ 32 by omega)]
      refine ⟨i + 1, _, _, rfl, by omega, h, by simp [hP], ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst hji
          refine ⟨st.id f, ?_, ?_⟩
          · have := hS.inv.core.off_lt hflv; omega
          · simp [U, hP, hj]
        · obtain ⟨v, hv, hu⟩ := hPc j hj
          refine ⟨v, hv, ?_⟩
          simp [U, Ne.symm hji]; exact hu
      · intro j hj
        by_cases hji : j = i
        · subst hji
          refine ⟨hklt, ?_⟩
          rw [getElem!_pos st.facts _ hklt]
          have : st.facts[wordFn ws (3 + wordFn ws 1 + off.toNat + 1 + j)] = f := by
            rw [Array.getElem?_eq_getElem hklt] at hf; exact Option.some.inj hf
          rw [this]
          refine ⟨hflv, ?_⟩
          simp [U, Array.getElem?_setIfInBounds, hP]; omega
        · obtain ⟨hk, hlv, hu⟩ := hfacts j (by omega)
          refine ⟨hk, hlv, ?_⟩
          simp [U, Ne.symm hji]; exact hu

end Vbcf.Proof
