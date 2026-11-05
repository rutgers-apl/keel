import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.DLoad2

/-!
# Vbcf proofs: `ck_scan` against its structural contract

`ck_scan_dspec : DScanSpec` follows the C scanner's budget checks,
allocations and last-reference pass. Its structural result records `StepsAt`
and the initialized arrays, independently of the functional loader and scanner.
`expr_at` is specified directly from `DLoadDone` (`expr_at_dload`).
-/

set_option linter.unusedSimpArgs false

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## The scanner's invariant gives the step layout -/

/-- The steps passed so far, followed by any layout of the rest of the section,
lay out the section from offset 0. -/
theorem ScanInv.stepsAt_append {w : Nat → Nat} {base ns p nassume : Nat} {bad : Bool} {gpos : Nat}
    {pre : List Step} (h : ScanInv w base ns p nassume bad gpos pre) :
    ∀ rest, StepsAt w base ns p rest → StepsAt w base ns 0 (pre ++ rest) := by
  induction h with
  | init => intro rest hr; simpa using hr
  | @step p na bad g pre _ hlt hb ih =>
    intro rest hr
    have := ih (stepAt w (base + p) :: rest) ⟨hlt, hb, rfl, hr⟩
    simpa using this

/-- At the end of the section, the steps passed are its layout. -/
theorem ScanInv.stepsAt {w : Nat → Nat} {base ns nassume : Nat} {bad : Bool} {gpos : Nat}
    {steps : List Step} (h : ScanInv w base ns ns nassume bad gpos steps) :
    StepsAt w base ns 0 steps := by
  simpa using h.stepsAt_append [] rfl

/-! ## `DLoadDone` across `ck_scan`'s allocation -/

theorem DLoadDone.dweaken {W : World} {ws : Array (BitVec 32)} {c : CMem} {tt ff : Nat} {st2 : St}
    {pm : Nat → Option Nat} (h : DLoadDone W ws c tt ff st2 pm) : DLoadDone' W ws c tt ff st2 pm :=
  ⟨h.hsz, h.hmagic, h.hne, h.hns, h.hlen, h.pmLt, h.pmNone, h.core, h.proofPtr, h.psize, h.nexpr,
    h.proofSize, h.map, h.rest, h.ttNode, h.ffNode, h.tt, h.ff, h.prem, h.flen, h.noFacts, h.lo⟩

/-- The structural loading result survives the scanner's work payment. -/
theorem DLoadDone.wev {W : World} {ws : Array (BitVec 32)} {c : CMem} {tt ff : Nat} {st2 : St}
    {pm : Nat → Option Nat} (h : DLoadDone W ws c tt ff st2 pm) (wk er : BitVec 32) :
    DLoadDone W ws (c.wev wk er c.k.val) tt ff st2 pm :=
  ⟨h.hsz, h.hmagic, h.hne, h.hns, h.hlen, h.pmLt, h.pmNone, h.core.wev, h.proofPtr, h.psize,
    h.nexpr, h.proofSize, h.map, h.rest, h.ttNode, h.ffNode, h.tt, h.ff,
    ⟨h.prem.ptr, h.prem.size, h.prem.cells⟩, h.factsNull, h.flen, h.noFacts, h.lrNull, h.lo⟩

/-- `DLoadDone'` for a C state that agrees on everything it looks at. -/
theorem DLoadDone'.same {W : World} {ws : Array (BitVec 32)} {c c' : CMem} {tt ff : Nat} {st2 : St}
    {pm : Nat → Option Nat} (h : DLoadDone' W ws c tt ff st2 pm)
    (hpool : c'.k.pool = c.k.pool) (hplen : c'.k.plen = c.k.plen) (hpcap : c'.k.pcap = c.k.pcap)
    (hpoolc : c'.pool = c.pool) (hhtab : c'.htab = c.htab) (hhp : c'.k.htab = c.k.htab)
    (hhcap : c'.k.hcap = c.k.hcap) (hhcnt : c'.k.hcnt = c.k.hcnt) (hstk : c'.k.stk = c.k.stk)
    (hsp : c'.k.sp = c.k.sp) (hscap : c'.k.scap = c.k.scap) (hstkc : c'.stk = c.stk)
    (hproof : c'.k.proof = c.k.proof) (hproofc : c'.proof = c.proof) (hnexpr : c'.k.nexpr = c.k.nexpr)
    (htt : c'.k.tt = c.k.tt) (hff : c'.k.ff = c.k.ff) (hprem : c'.k.prem = c.k.prem)
    (hpremc : c'.prem = c.prem) (hflen : c'.k.flen = c.k.flen) (hlo : c'.k.lo = c.k.lo) :
    DLoadDone' W ws c' tt ff st2 pm where
  hsz := h.hsz
  hmagic := h.hmagic
  hne := h.hne
  hns := h.hns
  hlen := h.hlen
  pmLt := h.pmLt
  pmNone := h.pmNone
  core := h.core.same hpool hplen hpcap hpoolc hhtab hhp hhcap hhcnt hstk hsp hscap hstkc
  proofPtr := by rw [hproof]; exact h.proofPtr
  psize := by rw [hproofc]; exact h.psize
  nexpr := by rw [hnexpr]; exact h.nexpr
  proofSize := by rw [hproofc]; exact h.proofSize
  map := by rw [hproofc]; exact h.map
  rest := by rw [hproofc]; exact h.rest
  ttNode := h.ttNode
  ffNode := h.ffNode
  tt := by rw [htt]; exact h.tt
  ff := by rw [hff]; exact h.ff
  prem := ⟨by rw [hprem]; exact h.prem.ptr, by rw [hpremc]; exact h.prem.size,
    by rw [hpremc]; exact h.prem.cells⟩
  flen := by rw [hflen]; exact h.flen
  noFacts := h.noFacts
  lo := by rw [hlo, hplen]; exact h.lo

/-! ## `expr_at` from `DLoadDone` -/

/-- The postcondition of `expr_at`, in terms of the loader's position map. -/
def DExprAtLoadPost (st2 : St) (pm : Nat → Option Nat) (p : BitVec 32) (s : (KernelState prog State)) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  s' = s ∧ ∃ r, rv = some (.u32 r) ∧
    match pm p.toNat with
    | none => r = noid
    | some i => i < st2.pool.size ∧ r.toNat = offs st2.pool i ∧ r ≠ noid

theorem expr_at_dload (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (st2 : St)
    (tt ff : Nat) (pm : Nat → Option Nat) (p : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "expr_at"
      (fun vs s => vs = [.ptr sb 0, .u32 p] ∧ Holds W s.mem sb c ∧ DLoadDone W ws c tt ff st2 pm)
      (fun _ s => DExprAtLoadPost st2 pm p s) := by
  have hs := prog_ck
  apply FnSpec.intro' (fn := exprAt) rfl
  rintro vs s ⟨rfl, h, hld⟩
  simp [exprAt, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hne := hld.nexpr
  have hbound : 3 + c.k.nexpr.toNat ≤ 2 ^ 32 := by
    have := hld.hlen; have := hld.psize; have := hld.proofSize; omega
  apply WP.seq
  apply WP.ite
  ck_simp
  constructor
  · intro hge
    have hge' : c.k.nexpr.toNat ≤ p.toNat := by simpa [BitVec.le_def] using hge
    apply WP.ret
    ck_simp [retPost, NOID]
    refine ⟨rfl, _, rfl, ?_⟩
    rw [hld.pmNone (by omega)]; rfl
  · intro hlt
    have hlt' : p.toNat < c.k.nexpr.toNat := by simpa [BitVec.lt_def] using hlt
    apply WP.skip
    have hu := hld.map p.toNat (by omega)
    have h3p : (3#32 + p).toNat = 3 + p.toNat := by
      rw [bv_add_toNat] <;> simp <;> omega
    apply WP.seq
    apply WP.assign
    ck_simp [hld.proofPtr, h.loadProof, h3p, rd_u32 hu]
    apply WP.seq
    apply WP.ite
    ck_simp
    cases he : pm p.toNat with
    | none =>
      simp only [he] at hu ⊢
      constructor
      · intro hz
        apply WP.ret
        ck_simp [retPost, NOID]
        exact ⟨rfl, _, rfl, by rw [he]; rfl⟩
      · intro hnz; exact absurd trivial hnz
    | some i =>
      simp only [he] at hu ⊢
      have hi := hld.pmLt he
      have hoff := hld.core.off_lt hi
      constructor
      · intro hz
        have := congrArg BitVec.toNat hz
        rw [bv_toNat_ofNat (by omega)] at this
        simp at this
      · intro hnz
        apply WP.skip
        apply WP.ret
        ck_simp [retPost]
        refine ⟨rfl, _, rfl, ?_⟩
        rw [he]
        have hr : (BitVec.ofNat 32 (offs st2.pool i + 1) - 1#32).toNat = offs st2.pool i := by
          rw [bv_sub_toNat] <;> rw [bv_toNat_ofNat (by omega)] <;> simp <;> omega
        refine ⟨hi, hr, ?_⟩
        intro e
        have := congrArg BitVec.toNat e
        rw [hr] at this
        simp [noid] at this
        omega

/-! ## `ck_scan` -/

/-! ## The second pass: the last-reference array -/

/-- `DScanDone` before the `lr` array is allocated. -/
structure DScanMid (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st2 : St)
    (pm : Nat → Option Nat) (steps : List Step) (gpos g : Nat) : Prop where
  ld : DLoadDone' W ws c tt ff st2 pm
  layout : StepsAt (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) 0 steps
  goal : pm gpos = some g
  goalFld : c.k.goal.toNat = offs st2.pool g
  factsPtr : ∃ b, c.k.facts = some (b, 0)
  factsSize : c.facts.size = steps.length
  fcap : c.k.fcap.toNat = steps.length
  factsCells : ∀ j, j < steps.length → ∃ w, w < 2 ^ 32 ∧ U c.facts j w

section scanMid
variable {W : World} {ws : Array (BitVec 32)} {c c' : CMem} {tt ff : Nat} {st2 : St}
  {pm : Nat → Option Nat} {steps : List Step} {gpos g : Nat}

/-- `DScanMid` for a state that agrees on everything it looks at. -/
theorem DScanMid.same (h : DScanMid W ws c tt ff st2 pm steps gpos g)
    (hpool : c'.k.pool = c.k.pool) (hplen : c'.k.plen = c.k.plen) (hpcap : c'.k.pcap = c.k.pcap)
    (hpoolc : c'.pool = c.pool) (hhtab : c'.htab = c.htab) (hhp : c'.k.htab = c.k.htab)
    (hhcap : c'.k.hcap = c.k.hcap) (hhcnt : c'.k.hcnt = c.k.hcnt) (hstk : c'.k.stk = c.k.stk)
    (hsp : c'.k.sp = c.k.sp) (hscap : c'.k.scap = c.k.scap) (hstkc : c'.stk = c.stk)
    (hproof : c'.k.proof = c.k.proof) (hproofc : c'.proof = c.proof) (hnexpr : c'.k.nexpr = c.k.nexpr)
    (htt : c'.k.tt = c.k.tt) (hff : c'.k.ff = c.k.ff) (hprem : c'.k.prem = c.k.prem)
    (hpremc : c'.prem = c.prem) (hflen : c'.k.flen = c.k.flen) (hlo : c'.k.lo = c.k.lo)
    (hgoal : c'.k.goal = c.k.goal) (hfp : c'.k.facts = c.k.facts) (hfc : c'.facts = c.facts)
    (hfcap : c'.k.fcap = c.k.fcap) : DScanMid W ws c' tt ff st2 pm steps gpos g where
  ld := h.ld.same hpool hplen hpcap hpoolc hhtab hhp hhcap hhcnt hstk hsp hscap hstkc hproof hproofc
    hnexpr htt hff hprem hpremc hflen hlo
  layout := h.layout
  goal := h.goal
  goalFld := by rw [hgoal]; exact h.goalFld
  factsPtr := by rw [hfp]; exact h.factsPtr
  factsSize := by rw [hfc]; exact h.factsSize
  fcap := by rw [hfcap]; exact h.fcap
  factsCells := by rw [hfc]; exact h.factsCells

theorem DScanMid.done (h : DScanMid W ws c tt ff st2 pm steps gpos g)
    (hb : ∃ b, c.k.lr = some (b, 0)) (hsz : c.lr.size = steps.length)
    (hcells : ∀ j, j < steps.length → ∃ w, w < 2 ^ 32 ∧ U c.lr j w) :
    DScanDone W ws c tt ff st2 pm steps gpos g :=
  ⟨h.ld, h.layout, h.goal, h.goalFld, h.factsPtr, h.factsSize, h.fcap, h.factsCells, hb, hsz, hcells⟩

theorem DScanDone.mid (h : DScanDone W ws c tt ff st2 pm steps gpos g) :
    DScanMid W ws c tt ff st2 pm steps gpos g :=
  ⟨h.ld, h.layout, h.goal, h.goalFld, h.factsPtr, h.factsSize, h.fcap, h.factsCells⟩

/-- `DScanDone` survives a change of the work counter and error flag. -/
theorem DScanDone.wev (h : DScanDone W ws c tt ff st2 pm steps gpos g) (wk er : BitVec 32) :
    DScanDone W ws (c.wev wk er c.k.val) tt ff st2 pm steps gpos g := by
  refine DScanMid.done ?_ h.lrPtr h.lrSize h.lrCells
  apply h.mid.same <;> rfl

/-- `DScanDone` survives a store of a word into the `lr` array. -/
theorem DScanDone.storeLr (h : DScanDone W ws c tt ff st2 pm steps gpos g) {j : Nat}
    (x : BitVec 32) :
    DScanDone W ws (c.setArr .lr (c.lr.setIfInBounds j (.u32 x))) tt ff st2 pm steps gpos g := by
  refine DScanMid.done ?_ h.lrPtr (by simp [CMem.setArr, h.lrSize]) ?_
  · apply h.mid.same <;> rfl
  intro i hi
  obtain ⟨w0, hw0, hu⟩ := h.lrCells i hi
  by_cases hij : j = i
  · subst hij
    refine ⟨x.toNat, x.isLt, ?_⟩
    unfold U
    have : j < c.lr.size := by rw [h.lrSize]; exact hi
    simp [CMem.setArr, this]
  · refine ⟨w0, hw0, ?_⟩
    unfold U at hu ⊢
    simp only [CMem.setArr]
    rw [Array.getElem?_setIfInBounds_ne hij]; exact hu

end scanMid

/-- The invariant of the second pass: `DScanDone` holds throughout. -/
def DScan2Inv (W : World) (sb : Nat) (ws : Array (BitVec 32)) (tt ff : Nat) (st2 : St)
    (pm : Nat → Option Nat) (steps : List Step) (gp gi : Nat) (ne ns : Nat)
    (cnt nassume bad gpos g : BitVec 32) (f l : EmbC.Val) : Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c : CMem) (p hdr pc ac k i q : BitVec 32),
    env = scanEnv2 sb ne ns cnt nassume bad gpos g f l p hdr pc ac k i q ∧
    Holds W s.mem sb c ∧ DScanDone W ws c tt ff st2 pm steps gp gi ∧ p.toNat ≤ ns

/-- The invariant of the inner loop of the second pass. -/
def DScan2InnerInv (W : World) (sb : Nat) (ws : Array (BitVec 32)) (tt ff : Nat) (st2 : St)
    (pm : Nat → Option Nat) (steps : List Step) (gp gi : Nat) (ne ns : Nat)
    (cnt nassume bad gpos g : BitVec 32) (f l : EmbC.Val) (p hdr pc ac k : BitVec 32) :
    Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c : CMem) (i q : BitVec 32),
    env = scanEnv2 sb ne ns cnt nassume bad gpos g f l p hdr pc ac k i q ∧
    Holds W s.mem sb c ∧ DScanDone W ws c tt ff st2 pm steps gp gi ∧ i.toNat ≤ pc.toNat

/-- The tail of the second pass's loop body: `k = k + 1; p = p + 1 + pc + ac;`. -/
theorem dscan2_tail {Qb : Env → (KernelState prog State) → Prop} {Qr : Option EmbC.Val → Env → (KernelState prog State) → Prop}
    {W : World} {sb : Nat} {ws : Array (BitVec 32)} {tt ff : Nat} {st2 : St}
    {pm : Nat → Option Nat} {steps : List Step} {gp gi ne ns : Nat}
    {cnt nassume bad gpos g : BitVec 32} {f l : EmbC.Val} {s : (KernelState prog State)}
    (p hdr pc ac k i q : BitVec 32)
    (hI : DScan2Inv W sb ws tt ff st2 pm steps gp gi ne ns cnt nassume bad gpos g f l
      (scanEnv2 sb ne ns cnt nassume bad gpos g f l (p + 1#32 + pc + ac) hdr pc ac (k + 1#32) i q) s) :
    WP Vbcf.prog
      ((Stmt.assign "k" (Expr.bin BinOp.add (Expr.var "k") (Expr.lit32 1#32))).seq
        (Stmt.assign "p" (Expr.bin BinOp.add
          (Expr.bin BinOp.add (Expr.bin BinOp.add (Expr.var "p") (Expr.lit32 1#32)) (Expr.var "pc"))
          (Expr.var "ac"))))
      (fun o env' st' => match o with
        | .normal => DScan2Inv W sb ws tt ff st2 pm steps gp gi ne ns cnt nassume bad gpos g f l
            env' st'
        | .brk => Qb env' st'
        | .ret r => Qr r env' st')
      (scanEnv2 sb ne ns cnt nassume bad gpos g f l p hdr pc ac k i q) s := by
  apply WP.seq
  apply WP.assign
  embc_simp [scanEnv2]
  apply WP.assign
  embc_simp
  exact hI

/-- The postcondition of `ck_scan`, structural form. -/
def DScanPost (W : World) (sb : Nat) (ws : Array (BitVec 32)) (tt ff : Nat) (st2 : St)
    (pm : Nat → Option Nat) : Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c', Holds W s'.mem sb c' ∧
    (rv = some (.u32 0#32) ∨
     (rv = some (.u32 1#32) ∧ ∃ steps gpos g, DScanDone W ws c' tt ff st2 pm steps gpos g))

theorem ck_scan_dspec : DScanSpec (State := State) := by
  intro W sb c ws st2 tt ff pm
  show FnSpec (State := State) Vbcf.prog "ck_scan" _ (fun _ _ => DScanPost W sb ws tt ff st2 pm)
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckScan) rfl
  rintro vs s ⟨rfl, h, hld⟩
  simp [ckScan, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  -- names and bounds
  obtain ⟨w, hw⟩ : ∃ w, w = wordFn ws := ⟨_, rfl⟩
  have hwlt : ∀ i, w i < 2 ^ 32 := by rw [hw]; exact wordFn_lt ws
  obtain ⟨ne, hne⟩ : ∃ ne, ne = wordFn ws 1 := ⟨_, rfl⟩
  obtain ⟨ns, hns⟩ : ∃ ns, ns = wordFn ws 2 := ⟨_, rfl⟩
  have hlen : 3 + ne + ns = ws.size := by rw [hne, hns]; exact hld.hlen
  have hsz : ws.size ≤ 2 ^ 32 := by rw [← hld.proofSize]; exact hld.psize
  have hns2 : 2 ≤ ns := by rw [hns]; exact hld.hns
  have hnexpr : c.k.nexpr.toNat = ne := by rw [hne]; exact hld.nexpr
  have hproof := hld.proofPtr
  have hpsz : c.proof.size = ws.size := hld.proofSize
  have hrest : ∀ q, 3 + ne ≤ q → q < ws.size → U c.proof q (w q) := by
    intro q h1 h2; rw [hw]; exact hld.rest q (Or.inr (hne ▸ h1)) h2
  have h2 : U c.proof 2 ns := by rw [hns]; exact hld.rest 2 (Or.inl (by omega)) (by omega)
  have hbase : (3#32 + c.k.nexpr).toNat = 3 + ne := by
    rw [bv_add_toNat] <;> simp <;> omega
  -- base = 3 + st->nexpr; ns = st->proof[2];
  apply WP.seq
  apply WP.assign
  ck_simp
  apply WP.seq
  apply WP.assign
  ck_simp [hproof, h.loadProof, rd_u32 h2]
  rw [show 3#32 + c.k.nexpr = BitVec.ofNat 32 (3 + ne) from
    BitVec.eq_of_toNat_eq (by rw [hbase, bv_toNat_ofNat (by omega)])]
  -- g = spend(st, ns); if (g == 0) { return 0; }
  apply WP.seq
  apply WP.call (spend_spec W sb c (BitVec.ofNat 32 ns))
  ck_simp
  refine ⟨h, ?_⟩
  rintro rv s2 rfl hsp2
  rw [spendM_wev] at hsp2
  ck_simp
  apply WP.ifRet
  ck_simp
  refine ⟨fun _ => ?_, fun hnz => ?_⟩
  · first | exact ⟨_, hsp2, Or.inl rfl⟩ | exact ⟨rfl, _, hsp2, Or.inl rfl⟩
  obtain h1 : (spendM c (BitVec.ofNat 32 ns)).1 = 1#32 := (spendM_fst _ _).resolve_left hnz
  rw [h1]
  generalize (spendM c (BitVec.ofNat 32 ns)).2.k.work = wk at hsp2
  generalize (spendM c (BitVec.ofNat 32 ns)).2.k.err = er at hsp2
  have hld' := hld.wev wk er
  clear h hld hnexpr hproof hpsz hrest h2 hbase h1 hnz
  generalize c.wev wk er c.k.val = c at hsp2 hld'
  have h := hsp2
  have hld := hld'
  clear hsp2 hld'
  have hnexpr : c.k.nexpr.toNat = ne := by rw [hne]; exact hld.nexpr
  have hproof := hld.proofPtr
  have hpsz : c.proof.size = ws.size := hld.proofSize
  have hrest : ∀ q, 3 + ne ≤ q → q < ws.size → U c.proof q (w q) := by
    intro q h1 h2; rw [hw]; exact hld.rest q (Or.inr (hne ▸ h1)) h2
  have h2 : U c.proof 2 ns := by rw [hns]; exact hld.rest 2 (Or.inl (by omega)) (by omega)
  -- the loop
  apply WP.seq
  apply WP.while (I := ScanLoopInv sb s2 w ne ns)
  · exact ⟨rfl, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, false, [], rfl, ScanInv.init, rfl⟩
  · rintro env s' ⟨rfl, p, hdr, pc, ac, cnt, nassume, gpos, b, pre, rfl, hinv, hcnt⟩
    have hple := hinv.le
    obtain ⟨hlenp, hna, hnil⟩ := hinv.length_le
    ck_simp
    constructor
    · -- loop exit: p = ns
      intro hge
      have hpns : p.toNat = ns := by
        have : ns ≤ p.toNat := by simpa [BitVec.le_def, bv_toNat_ofNat (show ns < 2 ^ 32 by omega)] using hge
        omega
      have hnil' : pre ≠ [] := fun e => by have := hnil e; omega
      apply WP.ifRet
      ck_simp
      by_cases hna1 : nassume = 1#32
      · cases b
        · simp only [hna1, badW, ↓reduceIte]
          refine ⟨by simp, fun _ => ?_⟩
          -- the scanner succeeded
          have hinv' : ScanInv w (3 + ne) ns ns 1 false gpos.toNat pre := by
            rw [hpns, hna1] at hinv; exact hinv
          have hscan := hinv'.stepsAt
          -- g = expr_at(st, gpos);
          apply WP.seq
          apply WP.call (expr_at_dload W sb c ws st2 tt ff pm gpos)
          ck_simp
          refine ⟨⟨h, hld⟩, ?_⟩
          rintro rv s2 ⟨rfl, r, rfl, hr⟩
          ck_simp
          have hcntpos : 1 ≤ cnt.toNat := by
            rw [hcnt]; cases pre with
            | nil => exact absurd rfl hnil'
            | cons _ _ => simp
          cases hpg : pm gpos.toNat with
          | none =>
            rw [hpg] at hr
            subst hr
            apply WP.ifRet
            ck_simp [noid]
            apply retPost_u32
            unfold DScanPost
            exact ⟨c, h, Or.inl rfl⟩
          | some gi =>
            rw [hpg] at hr
            obtain ⟨hgi, hroff, hrne⟩ := hr
            apply WP.ifRet
            ck_simp
            have hrne' : ¬ r = 4294967295#32 := hrne
            refine ⟨fun e => absurd e hrne', fun _ => ?_⟩
            apply WP.seq
            apply WP.ck_setField hs h (by rfl)
            ck_simp
            clear h
            intro s3 h
            have hcnt32 := cnt.isLt
            have hmod : cnt.toNat % 18446744073709551616 = cnt.toNat := Nat.mod_eq_of_lt (by omega)
            have hn64 : (BitVec.setWidth 64 cnt).toNat = cnt.toNat := by simp; omega
            have hn0 : BitVec.setWidth 64 cnt ≠ 0#64 := by
              intro e; have := congrArg BitVec.toNat e; rw [hn64] at this; simp at this; omega
            -- pay for the facts array from the memory budget
            apply WP.seq
            apply WP.ite
            ck_simp
            constructor
            · intro _
              apply WP.seq
              apply WP.ck_setField hs h (by rfl)
              ck_simp
              clear h
              intro s4 h
              apply WP.ret
              ck_simp [retPost]
              unfold DScanPost
              exact ⟨_, h, Or.inl rfl⟩
            intro _
            apply WP.skip
            apply WP.seq
            apply WP.ck_setField hs h (by rfl)
            ck_simp
            clear h
            intro s3 h
            apply WP.seq
            apply WP.ecall
            ck_simp [kvcalloc_run hn0, hmod]
            by_cases horc : (callocResponse (P := Vbcf.prog) hn0 s3).1 ≠ some .null
            · simp only [ne_eq, Classical.not_not] at horc
              simp only [horc, ↓reduceIte]
              obtain ⟨hnew, hck, hst, hH⟩ := h.calloc hs .facts
                (by show c.k.facts = none; exact hld.factsNull)
                (Array.replicate cnt.toNat (.u32 0#32))
              simp only [Arr.field] at hst hH
              embc_simp [Mem.hasTy_ptr hnew rfl]
              apply WP.seq
              apply WP.ite
              embc_simp [hnew]
              apply WP.skip
              apply WP.seq
              apply WP.setField
              embc_simp [hst]
              clear h
              have h := hH
              simp only [CMem.setArr, CK.setPtr] at h
              apply WP.seq
              apply WP.ck_setField hs h (by rfl)
              ck_simp
              clear h
              intro s5 h
              obtain ⟨c5, h, hM, hlr5⟩ : ∃ c5, Holds W s5.mem sb c5 ∧
                  DScanMid W ws c5 tt ff st2 pm pre gpos.toNat gi ∧ c5.k.lr = none :=
                ⟨_, h,
                  { ld := hld.dweaken.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                      rfl rfl rfl rfl rfl
                    layout := by
                      rw [← hw, show w 1 = ne by rw [hw, hne], show w 2 = ns by rw [hw, hns]]; exact hscan
                    goal := hpg
                    goalFld := hroff
                    factsPtr := ⟨_, rfl⟩
                    factsSize := by simp [hcnt]
                    fcap := hcnt
                    factsCells := fun j hj => ⟨0, by decide, by
                      unfold U; simp [hcnt, hj]⟩ }, hld.lrNull⟩
              -- pay for the `lr` array from the memory budget
              apply WP.seq
              apply WP.ite
              ck_simp
              constructor
              · intro _
                apply WP.seq
                apply WP.ck_setField hs h (by rfl)
                ck_simp
                clear h
                intro s6 h
                apply WP.ret
                ck_simp [retPost]
                unfold DScanPost
                exact ⟨_, h, Or.inl rfl⟩
              intro _
              apply WP.skip
              apply WP.seq
              apply WP.ck_setField hs h (by rfl)
              ck_simp
              clear h
              intro s6 h
              have hM6 := hM.same (c' := c5.setMem (c5.k.mem - cnt)) rfl rfl rfl rfl rfl rfl rfl rfl rfl
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              apply WP.seq
              apply WP.ecall
              ck_simp [kvcalloc_run hn0, hmod]
              by_cases horc2 : (callocResponse (P := Vbcf.prog) hn0 s6).1 ≠ some .null
              · simp only [ne_eq, Classical.not_not] at horc2
                simp only [horc2, ↓reduceIte]
                obtain ⟨hnew2, hck2, hst2, hH2⟩ := h.calloc hs .lr (c := c5.setMem (c5.k.mem - cnt))
                  hlr5 (Array.replicate cnt.toNat (.u32 0#32))
                simp only [Arr.field] at hst2 hH2
                embc_simp [Mem.hasTy_ptr hnew2 rfl]
                apply WP.seq
                apply WP.ite
                embc_simp [hnew2]
                apply WP.skip
                apply WP.seq
                apply WP.setField
                embc_simp [hst2]
                clear h
                have h := hH2
                simp only [CMem.setArr, CK.setPtr] at h
                obtain ⟨c7, h, hD7⟩ := Holds.named h
                  (P := fun c7 => DScanDone W ws c7 tt ff st2 pm pre gpos.toNat gi) (by
                    refine DScanMid.done ?_ ⟨_, rfl⟩ (by simp [hcnt])
                      (fun j hj => ⟨0, by decide, by
                        unfold U; simp [hcnt, hj]⟩)
                    apply hM6.same <;> rfl)
                -- g = spend(st, ns); if (g == 0) { return 0; }
                apply WP.seq
                apply WP.call (spend_spec W sb c7 (BitVec.ofNat 32 ns))
                ck_simp
                refine ⟨h, ?_⟩
                rintro rv s8 rfl hsp8
                rw [spendM_wev] at hsp8
                ck_simp
                apply WP.ifRet
                ck_simp
                refine ⟨fun _ => ?_, fun hnz8 => ?_⟩
                · first | exact ⟨_, hsp8, Or.inl rfl⟩ | exact ⟨rfl, _, hsp8, Or.inl rfl⟩
                have hD8 := hD7.wev (spendM c7 (BitVec.ofNat 32 ns)).2.k.work
                  (spendM c7 (BitVec.ofNat 32 ns)).2.k.err
                obtain h18 : (spendM c7 (BitVec.ofNat 32 ns)).1 = 1#32 :=
                  (spendM_fst _ _).resolve_left hnz8
                rw [h18]
                generalize (spendM c7 (BitVec.ofNat 32 ns)).2.k.work = wk8 at hsp8 hD8
                generalize (spendM c7 (BitVec.ofNat 32 ns)).2.k.err = er8 at hsp8 hD8
                generalize c7.wev wk8 er8 c7.k.val = c8 at hsp8 hD8
                clear h hH2 hM6 hM hlr5 hD7
                have h := hsp8
                clear hsp8
                -- the second pass
                apply WP.seq
                apply WP.assign
                ck_simp
                apply WP.seq
                apply WP.while (I := DScan2Inv W sb ws tt ff st2 pm pre gpos.toNat gi ne ns cnt
                  1#32 (badW false) gpos 1#32 (.ptr s3.mem.blocks.size 0) (.ptr s6.mem.blocks.size 0))
                · exact ⟨c8, 0#32, hdr, pc, ac, 0#32, 0#32, 0#32, by simp [scanEnv2, badW], h, hD8,
                    by simp⟩
                · rintro env s9 ⟨c9, p9, hdr9, pc9, ac9, k9, i9, q9, rfl, h, hD9, hp9⟩
                  have hnsN : (BitVec.ofNat 32 ns).toNat = ns := bv_toNat_ofNat (by omega)
                  ck_simp [scanEnv2]
                  constructor
                  · intro _
                    apply WP.ret
                    ck_simp [retPost]
                    unfold DScanPost
                    exact ⟨c9, h, Or.inr ⟨rfl, pre, gpos.toNat, gi, hD9⟩⟩
                  intro hlt
                  have hlt' : p9.toNat < ns := by
                    simpa [BitVec.lt_def, hnsN] using hlt
                  have hrest9 : ∀ q, 3 + ne ≤ q → q < ws.size → U c9.proof q (w q) := by
                    intro q h1 h2; rw [hw]; exact hD9.ld.rest q (Or.inr (hne ▸ h1)) h2
                  obtain ⟨q, hq⟩ : ∃ q, q = 3 + ne + p9.toNat := ⟨_, rfl⟩
                  have hqlt : q < ws.size := by omega
                  have hbp : (BitVec.ofNat 32 (3 + ne) + p9).toNat = q := by
                    rw [bv_add_toNat] <;> rw [bv_toNat_ofNat (by omega)] <;> omega
                  obtain ⟨hv, hhv⟩ : ∃ hv, hv = BitVec.ofNat 32 (w q) := ⟨_, rfl⟩
                  have hhdr : c9.proof[q]? = some (.u32 hv) := by rw [hhv]; exact hrest9 q (by omega) hqlt
                  have hpc : ((hv >>> 16) &&& 255#32).toNat = stepPc (w q) := by
                    rw [hhv]; exact scan_pc _ (hwlt q)
                  have hac : (hv >>> 24).toNat = stepAc (w q) := by rw [hhv]; exact scan_ac _ (hwlt q)
                  have hpclt := stepPc_lt (w q)
                  have haclt := stepAc_lt (w q) (hwlt q)
                  apply WP.seq
                  apply WP.assign
                  ck_simp [hD9.ld.proofPtr, h.loadProof, hbp, rd_u32 hhdr]
                  apply WP.seq
                  apply WP.assign
                  ck_simp
                  apply WP.seq
                  apply WP.assign
                  ck_simp
                  apply WP.ifRet
                  ck_simp
                  generalize hpcv : (hv >>> 16 &&& 255#32) = pcv at hpc ⊢
                  generalize hacv : hv >>> 24 = acv at hac ⊢
                  have hsub : (BitVec.ofNat 32 ns - p9 - 1#32).toNat = ns - p9.toNat - 1 := by
                    have h1 : (BitVec.ofNat 32 ns - p9).toNat = ns - p9.toNat := by
                      rw [bv_sub_toNat (by rw [hnsN]; omega), hnsN]
                    rw [bv_sub_toNat (by rw [h1]; simp; omega), h1]; simp
                  have hadd : (pcv + acv).toNat = stepPc (w q) + stepAc (w q) := by
                    rw [bv_add_toNat] <;> rw [hpc, hac]; omega
                  constructor
                  · intro _
                    apply retPost_u32
                    unfold DScanPost
                    exact ⟨c9, h, Or.inl rfl⟩
                  intro hle
                  have hle' : p9.toNat + 1 + stepPc (w q) + stepAc (w q) ≤ ns := by
                    have := hle; rw [BitVec.le_def, hadd, hsub] at this; omega
                  have hpnew : (p9 + 1#32 + pcv + acv).toNat = p9.toNat + 1 + stepPc (w q) + stepAc (w q) := by
                    rw [bv_add_toNat, bv_add_toNat, bv_add_toNat] <;> simp [hpc, hac] <;> omega
                  have hcntL : cnt.toNat = c9.lr.size := by rw [hD9.lrSize, hcnt]
                  obtain ⟨lb, hlb⟩ := hD9.lrPtr
                  apply WP.seq
                  apply WP.ite
                  ck_simp
                  constructor
                  · intro hk
                    have hk' : k9.toNat < cnt.toNat := by simpa [BitVec.lt_def] using hk
                    apply WP.seq
                    apply WP.assign
                    ck_simp
                    apply WP.while (I := DScan2InnerInv W sb ws tt ff st2 pm pre gpos.toNat gi ne ns
                      cnt 1#32 (badW false) gpos 1#32 (.ptr s3.mem.blocks.size 0)
                      (.ptr s6.mem.blocks.size 0) p9 hv pcv acv k9)
                    · exact ⟨c9, 0#32, q9, by simp [scanEnv2], h, hD9, by simp⟩
                    rintro env s10 ⟨c10, i10, q10, rfl, h, hD10, hi10⟩
                    ck_simp [scanEnv2]
                    constructor
                    · intro _
                      exact dscan2_tail p9 hv pcv acv k9 i10 q10
                        ⟨c10, _, _, _, _, _, _, _, rfl, h, hD10, by rw [hpnew]; exact hle'⟩
                    intro hilt
                    have hilt' : i10.toNat < pcv.toNat := by simpa [BitVec.lt_def] using hilt
                    have hqi : (BitVec.ofNat 32 (3 + ne) + p9 + 1#32 + i10).toNat = q + 1 + i10.toNat := by
                      rw [bv_add_toNat, bv_add_toNat, bv_add_toNat] <;>
                        simp [bv_toNat_ofNat (show 3 + ne < 2 ^ 32 by omega)] <;> omega
                    have hrest10 : ∀ q, 3 + ne ≤ q → q < ws.size → U c10.proof q (w q) := by
                      intro q h1 h2; rw [hw]; exact hD10.ld.rest q (Or.inr (hne ▸ h1)) h2
                    have hqcell := hrest10 (q + 1 + i10.toNat) (by omega) (by omega)
                    have hcntL10 : cnt.toNat = c10.lr.size := by rw [hD10.lrSize, hcnt]
                    obtain ⟨lb10, hlb10⟩ := hD10.lrPtr
                    apply WP.seq
                    apply WP.assign
                    ck_simp [hD10.ld.proofPtr, h.loadProof, hqi, rd_u32 hqcell]
                    have hi1 : (i10 + 1#32).toNat = i10.toNat + 1 := by
                      rw [bv_add_toNat] <;> simp <;> omega
                    apply WP.seq
                    apply WP.ite
                    ck_simp
                    constructor
                    · intro hqk
                      have hqk' : (BitVec.ofNat 32 (w (q + 1 + i10.toNat))).toNat < k9.toNat := by
                        simpa [BitVec.lt_def] using hqk
                      have hwq := hwlt (q + 1 + i10.toNat)
                      have hwq' : (BitVec.ofNat 32 (w (q + 1 + i10.toNat))).toNat = w (q + 1 + i10.toNat) :=
                        bv_toNat_ofNat hwq
                      have hwmod : w (q + 1 + i10.toNat) % 4294967296 = w (q + 1 + i10.toNat) :=
                        Nat.mod_eq_of_lt hwq
                      apply WP.ck_store .lr h (by rfl) hlb10
                      ck_simp [hlb10]
                      refine ⟨by omega, ?_⟩
                      intro s11 h
                      apply WP.assign
                      ck_simp
                      exact ⟨_, _, _, rfl, h, hD10.storeLr _, by rw [hi1]; omega⟩
                    · intro _
                      apply WP.skip
                      apply WP.assign
                      ck_simp
                      exact ⟨c10, _, _, rfl, h, hD10, by rw [hi1]; omega⟩
                  · intro _
                    apply WP.skip
                    exact dscan2_tail p9 hv pcv acv k9 i9 q9
                      ⟨c9, _, _, _, _, _, _, _, rfl, h, hD9, by rw [hpnew]; exact hle'⟩
              · simp only [ne_eq, Classical.not_not] at horc2
                simp only [horc2, ↓reduceIte]
                embc_simp
                apply WP.seq
                apply WP.ite
                embc_simp
                apply WP.seq
                apply WP.ck_setField hs h (by rfl)
                ck_simp
                clear h
                intro s7 h
                apply WP.ret
                ck_simp [retPost]
                unfold DScanPost
                exact ⟨_, h, Or.inl rfl⟩
            · simp only [ne_eq, Classical.not_not] at horc
              simp only [horc, ↓reduceIte]
              embc_simp
              apply WP.seq
              apply WP.ite
              embc_simp
              apply WP.seq
              apply WP.ck_setField hs h (by rfl)
              ck_simp
              clear h
              intro s4 h
              apply WP.ret
              ck_simp [retPost]
              unfold DScanPost
              exact ⟨_, h, Or.inl rfl⟩
        · simp only [hna1, badW, ↓reduceIte]
          refine ⟨fun _ => ?_, by simp⟩
          apply retPost_u32
          unfold DScanPost
          exact ⟨c, h, Or.inl rfl⟩
      · simp only [hna1, ↓reduceIte]
        refine ⟨fun _ => ?_, by simp⟩
        apply retPost_u32
        unfold DScanPost
        exact ⟨c, h, Or.inl rfl⟩
    · intro hlt
      have hlt' : p.toNat < ns := by
        simpa [BitVec.lt_def, bv_toNat_ofNat (show ns < 2 ^ 32 by omega)] using hlt
      -- hdr = st->proof[base + p]; pc = …; ac = …;
      obtain ⟨q, hq⟩ : ∃ q, q = 3 + ne + p.toNat := ⟨_, rfl⟩
      have hqlt : q < ws.size := by omega
      have hbp : (BitVec.ofNat 32 (3 + ne) + p).toNat = q := by
        rw [bv_add_toNat] <;> rw [bv_toNat_ofNat (by omega)] <;> omega
      obtain ⟨hv, hhv⟩ : ∃ hv, hv = BitVec.ofNat 32 (w q) := ⟨_, rfl⟩
      have hhdr : c.proof[q]? = some (.u32 hv) := by rw [hhv]; exact hrest q (by omega) hqlt
      have hpc : ((hv >>> 16) &&& 255#32).toNat = stepPc (w q) := by rw [hhv]; exact scan_pc _ (hwlt q)
      have hac : (hv >>> 24).toNat = stepAc (w q) := by rw [hhv]; exact scan_ac _ (hwlt q)
      have hrule : (hv &&& 65535#32 = 1#32) ↔ stepRule (w q) = 1 := by rw [hhv]; exact scan_rule _ (hwlt q)
      have hpclt := stepPc_lt (w q)
      have haclt := stepAc_lt (w q) (hwlt q)
      apply WP.seq
      apply WP.assign
      ck_simp [hproof, h.loadProof, hbp, rd_u32 hhdr]
      apply WP.seq
      apply WP.assign
      ck_simp
      apply WP.seq
      apply WP.assign
      ck_simp
      apply WP.ifRet
      ck_simp
      generalize hpcv : (hv >>> 16 &&& 255#32) = pcv at hpc ⊢
      generalize hacv : hv >>> 24 = acv at hac ⊢
      have hnsN : (BitVec.ofNat 32 ns).toNat = ns := bv_toNat_ofNat (by omega)
      have hsub : (BitVec.ofNat 32 ns - p - 1#32).toNat = ns - p.toNat - 1 := by
        have h1 : (BitVec.ofNat 32 ns - p).toNat = ns - p.toNat := by
          rw [bv_sub_toNat (by rw [hnsN]; omega), hnsN]
        rw [bv_sub_toNat (by rw [h1]; simp; omega), h1]; simp
      have hadd : (pcv + acv).toNat = stepPc (w q) + stepAc (w q) := by
        rw [bv_add_toNat] <;> rw [hpc, hac]; omega
      constructor
      · intro hgt
        apply retPost_u32
        unfold DScanPost
        exact ⟨c, h, Or.inl rfl⟩
      · intro hle
        have hle' : p.toNat + 1 + stepPc (w q) + stepAc (w q) ≤ ns := by
          have := hle; rw [BitVec.le_def, hadd, hsub] at this; omega
        have hb : p.toNat + 1 + stepPc (w (3 + ne + p.toNat)) + stepAc (w (3 + ne + p.toNat)) ≤ ns := by
          rw [← hq]; exact hle'
        have hpnew : (p + 1#32 + pcv + acv).toNat = p.toNat + 1 + stepPc (w q) + stepAc (w q) := by
          rw [bv_add_toNat, bv_add_toNat, bv_add_toNat] <;> simp [hpc, hac] <;> omega
        have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by
          rw [bv_add_toNat] <;> simp <;> omega
        have hna1 : (nassume + 1#32).toNat = nassume.toNat + 1 := by
          rw [bv_add_toNat] <;> simp <;> omega
        have hac1 : (acv = 1#32) ↔ stepAc (w q) = 1 := by
          rw [← BitVec.toNat_inj, hac]; rfl
        apply WP.seq
        apply WP.ite
        ck_simp [hrule]
        by_cases hR : stepRule (w q) = 1
        · simp only [hR]
          refine ⟨fun _ => ?_, by simp⟩
          apply WP.seq
          apply WP.assign
          ck_simp
          apply WP.ite
          ck_simp [hac1]
          by_cases hA : stepAc (w q) = 1
          · simp only [hA]
            refine ⟨fun _ => ?_, by simp⟩
            -- gpos = st->proof[base + p + 1 + pc];
            have hgi : (BitVec.ofNat 32 (3 + ne) + p + 1#32 + pcv).toNat = q + 1 + stepPc (w q) := by
              rw [bv_add_toNat, bv_add_toNat, bv_add_toNat] <;> simp [hpc, bv_toNat_ofNat (show 3 + ne < 2 ^ 32 by omega)] <;> omega
            have hgcell := hrest (q + 1 + stepPc (w q)) (by omega) (by omega)
            apply WP.assign
            ck_simp [hproof, h.loadProof, hgi, rd_u32 hgcell]
            apply scan_tail
            refine ⟨rfl, _, _, _, _, _, _, _, b, pre ++ [stepAt w (3 + ne + p.toNat)], rfl, ?_, ?_⟩
            · rw [hpnew, hna1, bv_toNat_ofNat (hwlt _), hq]
              refine hinv.step' hlt' hb rfl ?_ ?_ ?_
              · rw [← hq, hR]; simp
              · rw [← hq, hR, hA]; simp
              · rw [← hq, hR, hA]; simp
            · rw [hcnt1, hcnt]; simp
          · simp only [hA]
            refine ⟨by simp, fun _ => ?_⟩
            apply WP.assign
            ck_simp
            apply scan_tail
            refine ⟨rfl, _, _, _, _, _, _, _, true, pre ++ [stepAt w (3 + ne + p.toNat)], rfl, ?_, ?_⟩
            · rw [hpnew, hna1, hq]
              refine hinv.step' hlt' hb rfl ?_ ?_ ?_
              · rw [← hq, hR]; simp
              · rw [← hq, hR]; simp [hA]
              · rw [← hq, hR]; simp [hA]
            · rw [hcnt1, hcnt]; simp
        · simp only [hR]
          refine ⟨by simp, fun _ => ?_⟩
          apply WP.skip
          dsimp only
          apply scan_tail
          refine ⟨rfl, _, _, _, _, _, _, _, b, pre ++ [stepAt w (3 + ne + p.toNat)], rfl, ?_, ?_⟩
          · rw [hpnew, hq]
            refine hinv.step' hlt' hb rfl ?_ ?_ ?_
            · rw [← hq]; simp [hR]
            · rw [← hq]; simp [hR]
            · rw [← hq]; simp [hR]
          · rw [hcnt1, hcnt]; simp

end Vbcf.Proof
