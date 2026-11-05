import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay5
import Vbcf.Proof.GoalSem

/-!
# Vbcf proofs: `ck_run`

Init, load, scan, the goal comparison (their specifications are hypotheses),
then the step loop with invariant `RunInv`, then the final comparison of the
last fact with `false`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The step invariant survives a call that keeps `RInv` for the same Lean
state and changes nothing a step relies on. -/
theorem SInv.frame {W : World} {ws : Array (BitVec 32)} {X : Ctx} {c c' : CMem} {st : VSt}
    {off : Nat} {rest : List Step} (h : SInv W ws X c st off rest) (hinv : RInv W X c' st)
    (hfr : StepFrame c c') : SInv W ws X c' st off rest where
  inv := hinv
  noFloor := h.noFloor
  wsz := h.wsz
  nexpr := by rw [hfr.nexpr]; exact h.nexpr
  hlen := h.hlen
  proofSize := by rw [hfr.proof]; exact h.proofSize
  words := by rw [hfr.proof]; exact h.words
  factsPtr := by rw [hfr.factsPtr]; exact h.factsPtr
  flen := by rw [hfr.flen]; exact h.flen
  factsSize := by rw [hfr.facts]; exact h.factsSize
  fcap := by rw [hfr.fcap, hfr.facts]; exact h.fcap
  factsCells := by rw [hfr.facts]; exact h.factsCells
  lrPtr := by rw [hfr.lrPtr]; exact h.lrPtr
  lrSize := by rw [hfr.lr, hfr.facts]; exact h.lrSize
  lrCells := by rw [hfr.lr]; exact h.lrCells
  facts := by rw [hfr.facts, hfr.lr, hfr.flen]; exact h.facts
  loaded := h.loaded
  nLcs := h.nLcs
  lo := by rw [hfr.lo]; exact h.lo
  ttL := h.ttL
  ffL := h.ffL
  goalL := h.goalL
  eiL := h.eiL
  steps := h.steps
  sound := h.sound

/-- The arena pointer has the type `u32 *` (it is `NULL`, or a live `u32` block). -/
theorem hasTy_gxVal {W : World} {m : Mem} {sb : Nat} {c : CMem} {goal : Nat} {ga : GArg}
    (h : Holds W m sb c) (hga : ArenaW W goal ga) : m.hasTy (gxVal ga) (.ptr .u32) = true := by
  cases ga with
  | none => rfl
  | some p =>
    obtain ⟨gb, gws⟩ := p
    have hb : m.block? gb = some ⟨.u32, gws.map EmbC.Val.u32⟩ := by
      rw [h.out gb hga.old hga.notProof]; exact hga.block
    exact Mem.hasTy_ptr hb rfl

/-- The verifier's goal is refuted, from the bridge, the Lean checker's
acceptance, and the comparison's result. -/
theorem goalRefuted_of {ws : Array (BitVec 32)} {st0 st1 st2 : St} {tt ff : Nat}
    {pm : Nat → Option Nat} {steps : List Step} {gpos D g : Nat} {P : RawProof}
    {remap : Array Nat} {goal : Nat} {ga : GArg}
    (htt : pushNode initSt ⟨.boolVal true, #[]⟩ = some (st0, tt))
    (hff : pushNode st0 ⟨.boolVal false, #[]⟩ = some (st1, ff))
    (hb : LoadBridge ws st1 st2 pm steps gpos D P remap) (hgoal : pm gpos = some g)
    (hacc : Accepts ws) (hp : GoalPend st2 g goal ga) : GoalRefuted goal ga := by
  cases ga with
  | none => trivial
  | some p =>
    obtain ⟨_, gws⟩ := p
    obtain ⟨P', graw, hd, hc⟩ := hacc
    have : P' = P := by
      have e := hb.decode_ok; rw [hd] at e; cases e; rfl
    subst this
    exact arena_refuted htt hff hb hgoal hc hp

theorem ck_run_spec (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hI : InitSpec (State := State)) (hL : LoadSpec (State := State))
    (hSc : ScanSpec (State := State)) (hG : GoalSpec (State := State)) (hC : CkCompactSpec (State := State)) : CkRunSpec (State := State) := by
  intro W sb c ws n ga goal
  have hs := prog_ck
  have hStep := ck_step_spec (ck_rule_spec hR)
  apply FnSpec.intro' (fn := ckRun) rfl
  rintro vs s ⟨rfl, h, hk, hpr, hn, hga⟩
  simp [ckRun, bindParams, Mem.hasTy_ptr h.ck rfl, Mem.hasTy_ptr h.proof rfl, hasTy_gxVal h hga]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  -- ok = ck_init(st, nwords, goal);
  apply WP.seq
  apply WP.call' (hI W sb c n goal) (vs := [.ptr sb 0, .u32 n, .u32 goal]) (by embc_simp)
    ⟨rfl, h, hk⟩
  intro rv s1 hpost
  obtain ⟨c1, h1, hp1, hrv⟩ := hpost
  rcases hrv with rfl | ⟨rfl, st1, tt, ff, hID⟩
  · embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.ret
    embc_simp [retPost]
    exact ⟨c1, 0, rfl, h1, fun h => absurd rfl h⟩
  embc_simp
  apply WP.seq
  apply WP.ite
  embc_simp
  apply WP.skip
  -- ok = ck_load(st, proof, nwords);
  apply WP.seq
  apply WP.call' (hL W sb c1 ws n st1 tt ff) (vs := [.ptr sb 0, .ptr W.pb 0, .u32 n]) (by embc_simp)
    ⟨rfl, h1, hID, by rw [hp1, hpr], hn⟩
  intro rv s2 hpost
  obtain ⟨c2, h2, hrv⟩ := hpost
  rcases hrv with rfl | ⟨rfl, st2, pm, D, hLD⟩
  · embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.ret
    embc_simp [retPost]
    exact ⟨c2, 0, rfl, h2, fun h => absurd rfl h⟩
  embc_simp
  apply WP.seq
  apply WP.ite
  embc_simp
  apply WP.skip
  -- ok = ck_scan(st);
  apply WP.seq
  apply WP.call' (hSc W sb c2 ws st1 st2 tt ff pm D) (vs := [.ptr sb 0]) (by embc_simp) ⟨rfl, h2, hLD⟩
  intro rv s3 hpost
  obtain ⟨c3, h3, hrv⟩ := hpost
  rcases hrv with rfl | ⟨rfl, steps, gpos, g, hSD⟩
  · embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.ret
    embc_simp [retPost]
    exact ⟨c3, 0, rfl, h3, fun h => absurd rfl h⟩
  embc_simp
  apply WP.seq
  apply WP.ite
  embc_simp
  apply WP.skip
  -- the bridge
  have hld := hSD.ld
  obtain ⟨st0, htt, hff⟩ := hld.b2
  obtain ⟨P, remap, hb⟩ := load_bridge_inv hld.hsz hld.hmagic hld.hne hld.hns hld.hlen hld.load hSD.scan
  have hwsz : ws.size < 2 ^ 32 := by rw [← hn]; exact n.isLt
  have hS0 := SInv.ofScan hSD h3 hwsz
  have hR0 := RInv0.ofScan hSD h3 st2.pool.size
  -- if (gx != NULL) { ok = ck_goal(st, gx, goal); if (ok == 0) { return 0; } }
  apply WP.seq
  apply WP.mono (Q := GoalMid W sb ws n ga goal (runCtx ws pm g tt ff st2.pool.size) steps st2)
  · apply WP.ite
    cases ga with
    | none =>
      embc_simp [gxVal]
      apply WP.skip
      exact ⟨c3, 1#32, rfl, h3, ⟨_, rfl, hS0⟩, trivial⟩
    | some p =>
      obtain ⟨gb, gws⟩ := p
      have hgb : s3.mem.block? gb = some ⟨.u32, gws.map EmbC.Val.u32⟩ := by
        rw [h3.out gb hga.old hga.notProof]; exact hga.block
      embc_simp [gxVal, hgb]
      apply WP.seq
      refine WP.call' (hG W sb c3 (runCtx ws pm g tt ff st2.pool.size) st2 gb gws goal)
        (vs := [.ptr sb 0, .ptr gb 0, .u32 goal]) (by embc_simp) ?_ ?_
      · exact ⟨rfl, h3, hR0, hga⟩
      intro rv s4 hpost
      obtain ⟨c4, r, rfl, h4, hinv4, hfr4, hok4⟩ := hpost
      embc_simp
      apply WP.ite
      embc_simp
      constructor
      · intro hr0
        apply WP.ret
        embc_simp [GoalMid, RunPost]
        exact ⟨c4, h4⟩
      · intro hr
        apply WP.skip
        exact ⟨c4, r, rfl, h4, ⟨_, rfl, SInv.frame hS0 (hinv4.toRInv rfl) hfr4⟩, hok4 hr⟩
  intro o env3 s3' hmid
  cases o with
  | brk => exact hmid.elim
  | ret rv =>
    cases rv with
    | none => exact hmid.elim
    | some v => exact hmid
  | normal =>
  obtain ⟨c3', okv, rfl, h3', ⟨S2, hS2, hS0'⟩, hpend⟩ := hmid
  simp only [runEnv]
  clear h
  have h := h3'
  -- ns = proof[2];
  have hns2 : U c3'.proof 2 (wordFn ws 2) := by
    rw [← hS0'.proofSize] at hwsz
    exact hS0'.words 2 (Or.inl (by omega)) (by have := hld.hsz; omega)
  apply WP.seq
  apply WP.assign
  ck_simp [h.loadProof, rd_u32 hns2]
  -- if (ns >= nwords) { return 0; }  (never taken: 3 + ne + ns = nwords; checked for the cost proof)
  apply WP.seq
  apply WP.ite
  embc_simp
  refine ⟨fun hge => absurd hge ?_, fun _ => ?_⟩
  · have hns' : wordFn ws 2 < 2 ^ 32 := wordFn_lt ws 2
    have := hld.hlen
    rw [BitVec.not_le, BitVec.lt_def, bv_toNat_ofNat hns']
    omega
  apply WP.skip
  -- the loop
  apply WP.seq
  apply WP.while (I := RunInv W sb ws n ga goal (runCtx ws pm g tt ff st2.pool.size) steps st2)
  · refine ⟨c3', S2, 0#32, steps, okv, 0#32, 0#32, 0#32, rfl, h, hS0', ?_, by rw [hS2]⟩
    intro hnil hpos
    rw [hS0'.flen.symm.trans (by rw [hS0'.flen])] at hpos
    have := hS0'.factsSize
    exfalso
    have h0 : S2.facts.size = 0 := by rw [hS2, hld.noFacts]; rfl
    omega
  intro env s4 hI
  obtain ⟨c4, st, off, rest, okv, fv, hdrv, sigv, rfl, h4, hS, hlast, hrep⟩ := hI
  simp only [runEnv]
  clear h
  have h := h4
  have hns : wordFn ws 2 < 2 ^ 32 := wordFn_lt ws 2
  ck_simp [lt_uv_iff hns]
  constructor
  · intro hge
    have hrest : rest = [] := by
      cases rest with
      | nil => rfl
      | cons s' rest' => exact absurd hS.steps.1 (by omega)
    subst hrest
    have hrep' : replay rwTable g ⟨tt, ff⟩ pm steps st2 = some st.toSt := hrep
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro hz
      apply WP.ret
      ck_simp [retPost]
      exact ⟨c4, 0, rfl, h, fun h => absurd rfl h⟩
    · intro hnz
      apply WP.skip
      apply WP.ret
      have hfl := hS.flen
      have hnz' : st.facts.size ≠ 0 := by
        intro h0; apply hnz; apply BitVec.eq_of_toNat_eq; rw [hfl, h0]; rfl
      obtain ⟨fb, hfp⟩ := hS.factsPtr
      obtain ⟨last, hlast, hll, hcell⟩ := hlast rfl (by omega)
      have hidx : (c4.k.flen - 1#32).toNat = st.facts.size - 1 := by
        rw [bv_sub_toNat (by rw [hfl]; simp; omega), hfl]; rfl
      ck_simp [hfp, h.rd_facts hfp, hidx, rd_u32 hcell, retPost]
      refine ⟨c4, _, rfl, h, fun hne => ?_⟩
      have heq : BitVec.ofNat 32 (st.id last) = c4.k.ff := by
        by_cases e : BitVec.ofNat 32 (st.id last) = c4.k.ff
        · exact e
        · simp [e] at hne
      have hlo := hS.inv.core.off_lt hll
      have hffn := hS.inv.ff.2
      have hffl : st.lv ff := hS.inv.ff.1
      have hoeq : st.id last = st.id ff := by
        have := congrArg BitVec.toNat heq
        rw [bv_toNat_ofNat (by omega)] at this
        rw [this]; exact hffn
      have hlf : last = ff := st.id_inj hll hffl hoeq
      subst hlf
      have hacc := accepts_of_replay htt hff hb hSD.goal hrep' hlast
      exact ⟨hacc, goalRefuted_of htt hff hb hSD.goal hacc hpend⟩
  · intro hlt
    obtain ⟨s', rest', rfl⟩ : ∃ s' rest', rest = s' :: rest' := by
      cases rest with
      | nil => have := hS.steps; simp only [StepsAt] at this; omega
      | cons s' rest' => exact ⟨s', rest', rfl⟩
    -- cond_resched();
    apply WP.seq
    refine WP.ecall_spec (vs := []) (by embc_simp) (by trivial) ?_
    intro rv yielded hyield
    have he := hyield.condResched
    rcases yielded with ⟨yieldMem, yieldWorld⟩
    simp only at he
    rcases he with ⟨rfl, rfl⟩
    embc_simp
    -- sig = signal_pending();
    apply WP.seq
    refine WP.ecall_spec (vs := []) (by embc_simp) (by trivial) ?_
    intro rv checked hsignal
    obtain ⟨signal, hrv, hmem⟩ :
        ∃ signal : BitVec 32, rv = some (.u32 signal) ∧ checked.mem = s4.mem := by
      rcases hsignal.signalPending with ⟨hzero | hone, hmem⟩
      · exact ⟨0, hzero, hmem⟩
      · exact ⟨1, hone, hmem⟩
    subst rv
    rcases checked with ⟨checkMem, checkWorld⟩
    dsimp only at hmem
    subst checkMem
    embc_simp
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro hsig
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      intro s5 h5
      apply WP.ret
      embc_simp [retPost]
      exact ⟨_, 0, rfl, h5, fun h => absurd rfl h⟩
    intro hsig
    apply WP.skip
    -- f = ck_step(st, off);
    apply WP.seq
    refine WP.call' (hStep W sb c4 ws (runCtx ws pm g tt ff st2.pool.size) st off s' rest')
      (vs := [.ptr sb 0, .u32 off]) (by embc_simp) ?_ ?_
    · exact ⟨rfl, h, hS⟩
    intro rv s5 hpost
    obtain ⟨c5, r, rfl, h5, hr⟩ := hpost
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    constructor
    · intro hnoid
      apply WP.ret
      embc_simp [retPost]
      exact ⟨c5, 0, rfl, h5, fun h => absurd rfl h⟩
    intro hnoid
    apply WP.skip
    obtain ⟨prems, st', f, hget, happ, hinv', hflv, hoff, hfr, hext⟩ := hr hnoid
    clear h
    have h := h5
    obtain ⟨fb, hfp⟩ := hS.factsPtr
    have hfp' : c5.k.facts = some (fb, 0) := by rw [hfr.factsPtr]; exact hfp
    have hfl5 : c5.k.flen.toNat = st.facts.size := by rw [hfr.flen]; exact hS.flen
    have hfsz := hS.factsSize
    simp only [List.length_cons] at hfsz
    -- st->facts[st->flen] = f;
    apply WP.seq
    apply WP.ck_store .facts h (by rfl) hfp'
    ck_simp [hfp']
    refine ⟨by rw [hfl5, hfr.facts]; omega, ?_⟩
    intro s6 h6
    clear h
    have h := h6
    -- st->flen = st->flen + 1;
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s7 h7
    clear h
    have h := h7
    -- hdr = proof[3 + st->nexpr + off];
    have hne := hS.nexpr
    have hn5 : c5.k.nexpr = c4.k.nexpr := hfr.nexpr
    have hlen := hS.hlen
    have hwsz' := hS.wsz
    obtain ⟨hlt', hle', hseq, hrest⟩ := hS.steps
    have hwq := wordFn_lt ws (3 + wordFn ws 1 + off.toNat)
    have hbase : 3#32 + c5.k.nexpr + off = BitVec.ofNat 32 (3 + wordFn ws 1 + off.toNat) := by
      apply uv_eq_of_toNat
      rw [BitVec.toNat_add, BitVec.toNat_add, hn5, hne]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hcell : U c5.proof (3 + wordFn ws 1 + off.toNat) (wordFn ws (3 + wordFn ws 1 + off.toNat)) := by
      rw [hfr.proof]; exact hS.words _ (Or.inr (by omega)) (by omega)
    apply WP.seq
    apply WP.assign
    ck_simp [h.loadProof, hbase, bv_toNat_ofNat (show 3 + wordFn ws 1 + off.toNat < 2 ^ 32 by omega),
      rd_u32 hcell]
    -- off = off + 1 + ((hdr >> 16) & 0xff) + (hdr >> 24);
    apply WP.seq
    apply WP.assign
    ck_simp [bv_stepPc _ hwq, bv_stepAc _ hwq]
    obtain rfl : r = BitVec.ofNat 32 (st'.id f) := uv_eq_of_toNat hoff
    have hpc := stepPc_lt (wordFn ws (3 + wordFn ws 1 + off.toNat))
    have hac := stepAc_lt (wordFn ws (3 + wordFn ws 1 + off.toNat)) hwq
    have hoff' : (off + 1#32 + BitVec.ofNat 32 (stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat))) +
        BitVec.ofNat 32 (stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat)))).toNat =
        off.toNat + 1 + stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) +
          stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat)) := by
      have hb2 := wordFn_lt ws 2
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      rw [Nat.mod_eq_of_lt (a := stepPc _) (by omega), Nat.mod_eq_of_lt (a := stepAc _) (by omega)]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hlastf : (st'.withFact f).facts.size = st.facts.size + 1 ∧
        (st'.withFact f).facts[st.facts.size]? = some f := by
      simp only [VSt.withFact_toSt]
      rw [St.addFact_eq, hK _ _ _ _ _ _ _ _ _ happ]
      simp
    obtain ⟨c7, h, hS7, hlast7⟩ := Holds.named h (P := fun c7 =>
      SInv W ws (runCtx ws pm g tt ff st2.pool.size) c7 (st'.withFact f)
        (off.toNat + 1 + stepPc (wordFn ws (3 + wordFn ws 1 + off.toNat)) +
          stepAc (wordFn ws (3 + wordFn ws 1 + off.toNat))) rest' ∧ LastOK c7 (st'.withFact f)) (by
      refine ⟨?_, ?_⟩
      · apply SInv.next hK hS hget happ hinv' hflv hfr hext <;> rfl
      · intro _
        refine ⟨f, by rw [hlastf.1]; simpa using hlastf.2, hflv, ?_⟩
        rw [hlastf.1]
        simp only [Nat.add_sub_cancel]
        unfold U
        rw [Array.getElem?_setIfInBounds, hfl5]
        simp only [↓reduceIte]
        rw [hfr.facts]
        simp [show st.facts.size < c4.facts.size by omega])
    rw [← hoff'] at hS7
    have hrep7 : replay rwTable (runCtx ws pm g tt ff st2.pool.size).goal
        (runCtx ws pm g tt ff st2.pool.size).bi (runCtx ws pm g tt ff st2.pool.size).ei steps st2 =
        replay rwTable (runCtx ws pm g tt ff st2.pool.size).goal (runCtx ws pm g tt ff st2.pool.size).bi
          (runCtx ws pm g tt ff st2.pool.size).ei rest' (st'.withFact f).toSt := by
      rw [hrep]
      simp only [replay, hget, happ, VSt.withFact_toSt]
    -- if (off < ns) { if (plen > …) { ok = ck_compact(st); if (ok == 0) { return 0; } } }
    apply WP.ite
    ck_simp
    refine ⟨fun hmore => ?_, fun hdone => ?_⟩
    · apply WP.ite
      ck_simp
      refine ⟨fun hbig => ?_, fun _ => ?_⟩
      · have hlo : c7.k.lo.toNat < c7.k.plen.toNat := by
          have h1 := c7.k.lo.isLt; have h2 := c7.k.live.isLt; have h3 := c7.k.flen.isLt
          have h4 := c7.k.plen.isLt
          bv_omega
        apply WP.seq
        refine WP.call' (hC W sb _ ws (runCtx ws pm g tt ff st2.pool.size) (st'.withFact f) _ rest')
          (vs := [.ptr sb 0]) (by embc_simp) ⟨rfl, h, hS7, hlo⟩ ?_
        intro rv s8 hpost
        obtain ⟨c8, r8, rfl, h8, hr8⟩ := hpost
        embc_simp
        apply WP.ite
        embc_simp
        refine ⟨fun h0 => ?_, fun hn0 => ?_⟩
        · apply WP.ret
          embc_simp [retPost]
          exact ⟨c8, 0, rfl, h8, fun h => absurd rfl h⟩
        · apply WP.skip
          obtain ⟨st8, hst8, hS8⟩ := hr8 hn0
          refine ⟨_, st8, _, rest', r8, _, _, _, rfl, h8, hS8, ?_, by rw [hst8]; exact hrep7⟩
          intro hnil
          subst hnil
          exfalso
          have := hS7.steps
          simp only [StepsAt] at this
          rw [BitVec.lt_def, bv_toNat_ofNat (wordFn_lt ws 2), this] at hmore
          exact Nat.lt_irrefl _ hmore
      · apply WP.skip
        exact ⟨_, st'.withFact f, _, rest', okv, _, _, _, rfl, h, hS7, fun _ => hlast7, hrep7⟩
    · apply WP.skip
      exact ⟨_, st'.withFact f, _, rest', okv, _, _, _, rfl, h, hS7, fun _ => hlast7, hrep7⟩

end Vbcf.Proof
