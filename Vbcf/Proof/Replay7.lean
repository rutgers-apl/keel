import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay6

/-!
# Vbcf proofs: `vbcf_check`

`kzalloc` the struct, `ck_run`, read the error flag, `ck_free`, `kvfree` the
struct, and map the result to an error number.  The size clause of
`OnlyBlockChanged` comes from `FnSpec.withShape`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem kvfree_ptr_run {P : Prog}
    {st : KernelState P State} {b : Nat} {blk : Block}
    (hb : st.mem.block? b = some blk) :
    Ext.run P .kvfree [.ptr b 0] st = some (none,
      ⟨st.mem.free b, (Ext.answer P .kvfree [.ptr b 0] st).2.oracle⟩) := by
  have hd : Kernel.Defined P ⟨.kvfree, [.ptr b 0], st.mem⟩ := ⟨rfl, blk, hb⟩
  rw [Ext.run_answer hd]
  have ha := (Ext.answer_spec hd).kvfree_ptr
  generalize he : Ext.answer P .kvfree [.ptr b 0] st = reply at *
  rcases reply with ⟨rv, ⟨mem, world⟩⟩
  rcases ha with ⟨rfl, rfl⟩
  rfl

/-- The checker's struct right after `kzalloc`, in the world `⟨m, pb⟩`. -/
def initCMem (cells : Array EmbC.Val) : CMem := ⟨zeroCK, #[], #[], #[], #[], #[], cells, #[]⟩

theorem zeroCells_ck : ckS.zeroCells = zeroCK.cells := rfl

theorem holds_init {m : Mem} {pb : Nat} {cells : Array EmbC.Val} (hpb : m.block? pb = some ⟨.u32, cells⟩) :
    Holds ⟨m, pb, fun _ => none⟩ (m.alloc (.struct "ck") ckS.zeroCells).2 m.blocks.size (initCMem cells) := by
  have hb := fun b' => Mem.block?_alloc (m := m) (t := .struct "ck") (cells := ckS.zeroCells) b'
  have hlt := Mem.block?_lt hpb
  have hnull : ∀ a, (initCMem cells).k.ptr a = none := by intro a; cases a <;> rfl
  refine ⟨?_, Nat.le_refl _, hlt, ?_, Or.inl rfl, Or.inl rfl, ?_, ?_, ?_, ?_,
    fun _ hb => absurd rfl hb⟩
  · show (m.alloc _ _).2.block? m.blocks.size = _
    rw [hb]; simp only [↓reduceIte]; rfl
  · show (m.alloc _ _).2.block? pb = _
    rw [hb]; simp only [Nat.ne_of_lt hlt, ↓reduceIte]; exact hpb
  · intro a b o hp; rw [hnull] at hp; cases hp
  · intro a a' b b' o o' _ hp; rw [hnull] at hp; cases hp
  · intro b hb' _
    rw [hb]; simp only [Nat.ne_of_lt hb', ↓reduceIte]
  · intro b hge hne _
    rw [hb]; simp only [hne, ↓reduceIte]
    unfold Mem.block?
    rw [Array.getElem?_eq_none hge]

/-- What `vbcf_check` leaves in memory: every block but `pb` as before, `pb`
still a live `u32` array. -/
def MemKept (pb : Nat) (m m' : Mem) : Prop :=
  (∀ b, b ≠ pb → m'.block? b = m.block? b) ∧ ∃ cells', m'.block? pb = some ⟨.u32, cells'⟩

/-- After `ck_free` and `kvfree(st)`. -/
theorem Freed.final {m0 m : Mem} {pb : Nat} {c : CMem} (h : Freed ⟨m0, pb, fun _ => none⟩ m0.blocks.size c m) :
    MemKept pb m0 (m.free m0.blocks.size) := by
  have hf := fun b' => Mem.block?_free (m := m) (b := m0.blocks.size) b'
  refine ⟨?_, c.proof, ?_⟩
  · intro b hne
    rw [hf]
    by_cases e : b = m0.blocks.size
    · simp only [e, ↓reduceIte]
      unfold Mem.block?
      rw [Array.getElem?_eq_none (Nat.le_refl _)]
    · simp only [e, ↓reduceIte]
      rcases Nat.lt_or_ge b m0.blocks.size with hlt | hge
      · exact h.out b hlt hne
      · rw [h.exact b hge e]
        unfold Mem.block?
        rw [Array.getElem?_eq_none hge]
  · rw [hf]
    have : pb ≠ m0.blocks.size := by have := h.pbOld; simp at this; omega
    simp only [this, ↓reduceIte]
    exact h.proof

def KPost (pb : Nat) (ws : Array (BitVec 32)) (ga : GArg) (goal : Nat) (s : (KernelState prog State)) :
    Option EmbC.Val → (KernelState prog State) → Prop :=
  fun rv s' => MemKept pb s.mem s'.mem ∧ ∃ r, rv = some (.u32 r) ∧
    (r = 0#32 → Accepts ws ∧ GoalRefuted goal ga)

/-- The arena pointer has the type `u32 *`. -/
theorem hasTy_gxVal_in {m : Mem} {goal : Nat} {ga : GArg} (hga : ArenaIn m goal ga) :
    m.hasTy (gxVal ga) (.ptr .u32) = true := by
  cases ga with
  | none => rfl
  | some p => obtain ⟨gb, gws⟩ := p; exact Mem.hasTy_ptr hga.1 rfl

/-- An arena in the memory at entry, other than the proof block, is an arena of
the world `⟨m, pb⟩`. -/
theorem arenaW_of_in {m : Mem} {pb goal : Nat} {ga : GArg} (hga : ArenaIn m goal ga)
    (hne : ArenaNot pb ga) : ArenaW ⟨m, pb, fun _ => none⟩ goal ga := by
  cases ga with
  | none => trivial
  | some p =>
    obtain ⟨gb, gws⟩ := p
    obtain ⟨hb, hin, hfit⟩ := hga
    refine ⟨?_, hne, hb, hin, hfit⟩
    show gb < m.blocks.size
    unfold Mem.block? at hb
    rcases Nat.lt_or_ge gb m.blocks.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hb; cases hb

theorem kzalloc_ck_run (hs : prog.findStruct "ck" = some ckS)
    (st : KernelState prog State) :
    Ext.run prog (.kzalloc "ck") [] st =
      if (Ext.answer prog (.kzalloc "ck") [] st).1 ≠ some .null then
        some (some (.ptr st.mem.blocks.size 0),
          ⟨(st.mem.alloc (.struct "ck") ckS.zeroCells).2,
            (Ext.answer prog (.kzalloc "ck") [] st).2.oracle⟩)
      else some (some .null, ⟨st.mem, (Ext.answer prog (.kzalloc "ck") [] st).2.oracle⟩) := by
  have hd : Kernel.Defined prog ⟨.kzalloc "ck", [], st.mem⟩ := ⟨ckS, hs⟩
  obtain ⟨d, hfind, ha⟩ := (Ext.answer_spec hd).kzalloc
  have heq : d = ckS := Option.some.inj (hfind.symm.trans hs)
  subst d
  rw [Ext.run_answer hd]
  generalize he : Ext.answer prog (.kzalloc "ck") [] st = reply at *
  rcases reply with ⟨rv, ⟨mem, world⟩⟩
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem vbcf_check_spec' (hRun : CkRunSpec (State := State)) :
    ∀ (pb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg) (goal : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "vbcf_check"
      (fun vs s => vs = [gxVal ga, .u32 goal, .ptr pb 0, .u32 n] ∧
        s.mem.block? pb = some ⟨.u32, ws.map EmbC.Val.u32⟩ ∧ n.toNat = ws.size ∧
        ArenaIn s.mem goal.toNat ga ∧ ArenaNot pb ga)
      (fun _ s => KPost pb ws ga goal.toNat s) := by
  intro pb ws n ga goal
  have hs := prog_ck
  apply FnSpec.intro' (fn := vbcfCheck) rfl
  rintro vs s ⟨rfl, hpb, hn, hga, hne⟩
  simp [vbcfCheck, bindParams, Mem.hasTy_ptr hpb rfl, hasTy_gxVal_in hga]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  -- st = kzalloc(sizeof(struct ck));
  apply WP.seq
  apply WP.ecall
  embc_simp [kzalloc_ck_run hs]
  by_cases hc : (Ext.answer prog (.kzalloc "ck") [] s).1 ≠ some .null
  case neg =>
    simp only [ne_eq, Classical.not_not] at hc
    -- allocation failure
    simp only [hc, ↓reduceIte]
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.ret
    embc_simp [retPost]
    exact ⟨⟨fun b _ => rfl, _, hpb⟩, _, rfl, fun h => absurd h (by decide)⟩
  simp only [hc, ↓reduceIte]
  have h := holds_init hpb
  have hsb : (s.mem.alloc (.struct "ck") ckS.zeroCells).2.block? s.mem.blocks.size =
      some ⟨.struct "ck", zeroCK.cells⟩ := h.ck
  embc_simp [Mem.hasTy_ptr hsb rfl]
  apply WP.seq
  apply WP.ite
  embc_simp [hsb]
  apply WP.skip
  -- ok = ck_run(st, proof, nwords, goal_exprs, goal);
  apply WP.seq
  refine WP.call' (hRun ⟨s.mem, pb, fun _ => none⟩ s.mem.blocks.size (initCMem (ws.map EmbC.Val.u32)) ws n ga goal)
    (vs := [.ptr s.mem.blocks.size 0, .ptr pb 0, .u32 n, gxVal ga, .u32 goal]) (by embc_simp) ?_ ?_
  · exact ⟨rfl, h, rfl, rfl, hn, arenaW_of_in hga hne⟩
  intro rv s2 hpost
  obtain ⟨c2, r, rfl, h2, hacc⟩ := hpost
  embc_simp
  -- err = st->err;
  apply WP.seq
  apply WP.assign
  clear h
  have h := h2
  ck_simp
  -- ck_free(st);
  apply WP.seq
  refine WP.call' (ck_free_spec ⟨s.mem, pb, fun _ => none⟩ s.mem.blocks.size c2)
    (vs := [.ptr s.mem.blocks.size 0]) (by embc_simp) ?_ ?_
  · exact ⟨rfl, h⟩
  intro rv s3 hpost
  obtain ⟨rfl, hF⟩ := hpost
  embc_simp
  -- kvfree(st);
  have hck3 : s3.mem.block? s.mem.blocks.size = some ⟨.struct "ck", c2.k.cells⟩ := hF.ck
  have hm := hF.final
  apply WP.seq
  apply WP.ecall
  embc_simp [kvfree_ptr_run (st := s3) hck3]
  apply WP.seq
  apply WP.ite
  embc_simp
  constructor
  · intro hr
    apply WP.ret
    embc_simp [retPost]
    exact ⟨hm, 0, rfl, fun _ => hacc hr⟩
  intro _
  apply WP.skip
  apply WP.seq
  apply WP.ite
  embc_simp
  constructor
  · intro _
    apply WP.ret
    embc_simp [retPost]
    exact ⟨hm, _, rfl, fun h => absurd h (by decide)⟩
  intro _
  apply WP.skip
  apply WP.seq
  apply WP.ite
  embc_simp
  constructor
  · intro _
    apply WP.ret
    embc_simp [retPost]
    exact ⟨hm, _, rfl, fun h => absurd h (by decide)⟩
  intro _
  apply WP.skip
  apply WP.ret
  embc_simp [retPost]
  exact ⟨hm, _, rfl, fun h => absurd h (by decide)⟩

/-- **`vbcf_check`**, from the specification of `ck_run`. -/
theorem vbcf_check_of_run (hRun : CkRunSpec (State := State)) : VbcfCheckSpec (State := State) := by
  intro pb ws n ga goal
  apply FnSpec.mono (FnSpec.withShape (vbcf_check_spec' hRun pb ws n ga goal))
  rintro vs s rv s' ⟨_, hpb, _⟩ ⟨⟨⟨hout, cells', hpb'⟩, r, hr, hacc⟩, hsh⟩
  refine ⟨⟨hout, _, cells', hpb, hpb', ?_⟩, r, hr, fun h0 => ?_⟩
  · exact hsh.cells pb _ _ hpb hpb'
  · obtain ⟨⟨P, g, hd, hc⟩, hg⟩ := hacc h0
    exact ⟨⟨P, g, hd, hc⟩, hg⟩

/-- **`vbcf_check`** (`VbcfCheckSpec`), given the loading-phase specifications,
the goal comparison, and the rules. -/
theorem vbcf_check_spec (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hI : InitSpec (State := State)) (hL : LoadSpec (State := State))
    (hSc : ScanSpec (State := State)) (hG : GoalSpec (State := State)) (hC : CkCompactSpec (State := State)) : VbcfCheckSpec (State := State) :=
  vbcf_check_of_run (ck_run_spec hR hK hI hL hSc hG hC)

end Vbcf.Proof
