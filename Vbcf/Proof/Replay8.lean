import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay7
import Vbcf.Proof.Hash5

/-!
# Vbcf proofs: `vbcf_check_proof`

Validate the size, `kvcalloc` a buffer, `copy_from_bpfptr` into it, run
`vbcf_check` on the copy (with the verifier's goal argument), `kvfree` the
buffer.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The wrapper uses the actual allocation reply, including its private world. -/
theorem inputAllocation_run {n : Nat} {st : KernelState prog State}
    (hn : BitVec.ofNat 64 n ≠ 0) :
    Ext.run prog (.kvcalloc .u32) [.u64 (BitVec.ofNat 64 n)] st =
      if (inputAllocation st n).1 ≠ some .null then
        some (some (.ptr st.mem.blocks.size 0),
          ⟨(st.mem.alloc .u32 (Array.replicate (BitVec.ofNat 64 n).toNat (.u32 0#32))).2,
            (inputAllocation st n).2.oracle⟩)
      else some (some .null, ⟨st.mem, (inputAllocation st n).2.oracle⟩) :=
  kvcalloc_run hn

theorem Mem.block?_fill_ne {m : Mem} {b off : Nat} {vs : List EmbC.Val} {b' : Nat} (h : b' ≠ b) :
    (m.fill b off vs).block? b' = m.block? b' := by
  unfold Mem.fill Mem.block?
  rw [Array.getElem?_modify]
  simp [Ne.symm h]

/-- Reading the actual returned copy heap recovers precisely its typed words. -/
theorem copiedWords_eq {st allocated copied : KernelState prog State} {n b : Nat}
    {words : List (BitVec 32)}
    (ha : inputAllocation st n = (some (.ptr b 0), allocated))
    (hc : inputCopy st n = (some (.u32 0), copied))
    (hb : copied.mem.block? b = some ⟨.u32, (words.map EmbC.Val.u32).toArray⟩) :
    copiedWords st n = words.toArray := by
  simp [copiedWords, ha, hc, hb, List.map_toArray, Function.comp_def]

/-- Freeing the one block allocated since `m` restores `m`. -/
theorem mem_restore {m m2 : Mem} (h : ∀ b', b' ≠ m.blocks.size → m2.block? b' = m.block? b') :
    ∀ b', (m2.free m.blocks.size).block? b' = m.block? b' := by
  intro b'
  rw [Mem.block?_free]
  by_cases e : b' = m.blocks.size
  · simp only [e, ↓reduceIte]; unfold Mem.block?; rw [Array.getElem?_eq_none (Nat.le_refl _)]
  · simp only [e, ↓reduceIte]; exact h b' e

/-- The in-kernel checker contract, abstract in the meaning of acceptance. -/
def InputCheckSpec (Q : Array (BitVec 32) → GArg → Nat → Prop) : Prop :=
  ∀ (pb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg) (goal : BitVec 32),
    FnSpec (State := State) Vbcf.prog "vbcf_check"
      (fun vs s => vs = [gxVal ga, .u32 goal, .ptr pb 0, .u32 n] ∧
        s.mem.block? pb = some ⟨.u32, ws.map EmbC.Val.u32⟩ ∧ n.toNat = ws.size ∧
        ArenaIn s.mem goal.toNat ga ∧ ArenaNot pb ga)
      (fun _ s rv s' => OnlyBlockChanged s.mem s'.mem pb ∧ ∃ r, rv = some (.u32 r) ∧
        (r = 0#32 → Q ws ga goal.toNat))

def InputPost (Q : Array (BitVec 32) → GArg → Nat → Prop)
    (size : BitVec 32) (ga : GArg) (goal : Nat) (s : KernelState prog State) :
    Option EmbC.Val → KernelState prog State → Prop := fun rv s' =>
  (∀ b, s'.mem.block? b = s.mem.block? b) ∧ ∃ r, rv = some (.u32 r) ∧
    (r = 0#32 → Q (copiedWords s (size.toNat / 4)) ga goal)

def InputProofSpec (Q : Array (BitVec 32) → GArg → Nat → Prop) : Prop :=
  ∀ (ga : GArg) (goal size : BitVec 32),
    FnSpec (State := State) Vbcf.prog "vbcf_check_proof"
      (fun vs s => vs = [gxVal ga, .u32 goal, .uptr, .u32 size] ∧ ArenaIn s.mem goal.toNat ga)
      (fun _ s => InputPost Q size ga goal.toNat s)

/-- The arena survives an allocation and a fill of the new block. -/
theorem ArenaIn.keep {m m' : Mem} {goal : Nat} {ga : GArg} (hga : ArenaIn m goal ga)
    (hkeep : ∀ b', b' ≠ m.blocks.size → m'.block? b' = m.block? b') :
    ArenaIn m' goal ga ∧ ArenaNot m.blocks.size ga := by
  cases ga with
  | none => exact ⟨trivial, trivial⟩
  | some p =>
    obtain ⟨gb, gws⟩ := p
    obtain ⟨hb, hin, hfit⟩ := hga
    have hlt : gb < m.blocks.size := by
      unfold Mem.block? at hb
      rcases Nat.lt_or_ge gb m.blocks.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hb; cases hb
    have hne : gb ≠ m.blocks.size := by omega
    exact ⟨⟨by rw [hkeep gb hne]; exact hb, hin, hfit⟩, hne⟩

theorem vbcf_check_proof_general {Q : Array (BitVec 32) → GArg → Nat → Prop}
    (hK : InputCheckSpec (State := State) Q) : InputProofSpec (State := State) Q := by
  intro ga goal size
  show FnSpec _ _ _ (fun _ s => InputPost Q size ga goal.toNat s)
  apply FnSpec.intro' (fn := vbcfCheckProof) rfl
  rintro vs s ⟨rfl, hga⟩
  simp [vbcfCheckProof, bindParams, hasTy_gxVal_in hga]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.ite
  embc_simp
  by_cases h1 : size < 12#32
  · simp only [h1, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply WP.ret
    embc_simp [retPost]
    exact ⟨fun b => rfl, _, rfl, fun h => absurd h (by decide)⟩
  by_cases h2 : size &&& 3#32 = 0#32
  case neg =>
    simp only [h1, h2, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply WP.ret
    embc_simp [retPost]
    exact ⟨fun b => rfl, _, rfl, fun h => absurd h (by decide)⟩
  by_cases h3 : 33554432#32 ≤ size
  · simp only [h1, h2, h3, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply WP.ret
    embc_simp [retPost]
    exact ⟨fun b => rfl, _, rfl, fun h => absurd h (by decide)⟩
  simp only [h1, h2, h3, ↓reduceIte]
  refine ⟨fun h => absurd trivial h, fun _ => ?_⟩
  apply WP.skip
  have h12 : 12 ≤ size.toNat := by rw [BitVec.lt_def] at h1; simp at h1; omega
  have hmax : size.toNat < 33554432 := by rw [BitVec.le_def] at h3; simp at h3; omega
  -- nwords = proof_size / 4;
  apply WP.seq
  apply WP.assign
  embc_simp
  have hq : (size / 4#32).toNat = size.toNat / 4 := by rw [BitVec.toNat_udiv]; rfl
  have hNt : ((size / 4#32).setWidth 64).toNat = size.toNat / 4 := by
    rw [BitVec.toNat_setWidth, hq]; omega
  have hN : (size / 4#32).setWidth 64 ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hNt] at this; simp at this; omega
  -- buf = kvcalloc(nwords, sizeof(u32));
  have hmod : size.toNat / 4 % 18446744073709551616 = size.toNat / 4 := by omega
  have hbits : (size / 4#32).setWidth 64 = BitVec.ofNat 64 (size.toNat / 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [hNt, BitVec.toNat_ofNat, hmod]
  have hN' : BitVec.ofNat 64 (size.toNat / 4) ≠ 0 := hbits ▸ hN
  apply WP.seq
  apply WP.ecall
  embc_simp [hbits, inputAllocation_run hN', hmod]
  by_cases hc : (inputAllocation s (size.toNat / 4)).1 ≠ some .null
  case neg =>
    have hc' : (inputAllocation s (size.toNat / 4)).1 = some .null :=
      Classical.byContradiction hc
    simp only [hc', ↓reduceIte]
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.ret
    embc_simp [retPost]
    exact ⟨fun b => rfl, _, rfl, fun h => absurd h (by decide)⟩
  simp only [hc, ↓reduceIte]
  let allocated : KernelState prog State :=
    ⟨(s.mem.alloc .u32 (Array.replicate (size.toNat / 4) (.u32 0#32))).2,
      (inputAllocation s (size.toNat / 4)).2.oracle⟩
  have ha : inputAllocation s (size.toNat / 4) =
      (some (.ptr s.mem.blocks.size 0), allocated) := by
    have hd : Kernel.Defined prog
        ⟨.kvcalloc .u32, [.u64 (BitVec.ofNat 64 (size.toNat / 4))], s.mem⟩ := ⟨hN', rfl⟩
    apply Option.some.inj
    exact (Ext.run_answer hd).symm.trans (by simp [inputAllocation_run hN', hc, hmod, allocated])
  have hbuf : (s.mem.alloc .u32
      (Array.replicate (size.toNat / 4) (.u32 0#32))).2.block? s.mem.blocks.size =
      some ⟨.u32, Array.replicate (size.toNat / 4) (.u32 0#32)⟩ := by
    simp [Mem.block?_alloc]
  embc_simp [Mem.hasTy_ptr hbuf rfl]
  apply WP.seq
  apply WP.ite
  embc_simp [hbuf]
  apply WP.skip
  -- The copy reply supplies both the actual words and the updated private world.
  apply WP.seq
  apply WP.ecall
  have hcopyDefined : Kernel.Defined prog
      ⟨.copyFromBpfptr, [.ptr s.mem.blocks.size 0, .uptr,
        .u64 (BitVec.ofNat 64 (size.toNat / 4))], allocated.mem⟩ := by
    exact ⟨_, hbuf, rfl, by simp [hmod]⟩
  have hcopyRun := Ext.run_answer hcopyDefined
  have hcopyAllowed := (Ext.answer_spec hcopyDefined).copyFromBpfptr
  generalize hcReply : Ext.answer prog .copyFromBpfptr
      [.ptr s.mem.blocks.size 0, .uptr, .u64 (BitVec.ofNat 64 (size.toNat / 4))] allocated =
        copied at hcopyRun hcopyAllowed
  rcases copied with ⟨copyResult, ⟨copyMem, copyWorld⟩⟩
  have hM1 : ∀ b', b' ≠ s.mem.blocks.size → allocated.mem.block? b' = s.mem.block? b' := by
    intro b' hb
    dsimp [allocated]
    rw [Mem.block?_alloc]
    simp [hb]
  dsimp only [allocated] at hcopyRun
  rcases hcopyAllowed with ⟨rfl, rfl⟩ | ⟨words, hwords, rfl, rfl⟩
  · -- A failed copy is freed and rejected.
    embc_simp [hbits, hcopyRun, hmod]
    have hfill := Mem.block?_fill_full
      (vs := List.replicate (size.toNat / 4) EmbC.Val.undef) hbuf (by simp)
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.seq
    apply WP.ecall
    have hfb := hfill s.mem.blocks.size
    simp only [↓reduceIte] at hfb
    embc_simp [kvfree_ptr_run
      (st := ⟨allocated.mem.fill s.mem.blocks.size 0
        (List.replicate (size.toNat / 4) EmbC.Val.undef), copyWorld⟩) hfb]
    apply WP.ret
    embc_simp [retPost]
    refine ⟨mem_restore (fun b' hb => ?_), _, rfl, fun h => absurd h (by decide)⟩
    rw [hfill b', ite_eq_right (fun e => absurd e hb), hM1 b' hb]
  · have hwords' : words.length = size.toNat / 4 := by simpa [hmod] using hwords
    have hfill := Mem.block?_fill_full (vs := words.map EmbC.Val.u32) hbuf
      (by simp [hwords'])
    have hfb := hfill s.mem.blocks.size
    simp only [↓reduceIte] at hfb
    have hcopy : inputCopy s (size.toNat / 4) =
        (some (.u32 0), ⟨allocated.mem.fill s.mem.blocks.size 0 (words.map EmbC.Val.u32), copyWorld⟩) := by
      simpa [inputCopy, ha] using hcReply
    have hws : copiedWords s (size.toNat / 4) = words.toArray :=
      copiedWords_eq ha hcopy hfb
    obtain ⟨hga2, hne2⟩ := hga.keep
      (m' := allocated.mem.fill s.mem.blocks.size 0 (words.map EmbC.Val.u32))
      (fun b' hb => by rw [Mem.block?_fill_ne hb, hM1 b' hb])
    embc_simp [hbits, hcopyRun, hmod]
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.skip
    -- The checked payload is precisely the words in the actual copy reply.
    apply WP.seq
    refine WP.call' (hK s.mem.blocks.size (copiedWords s (size.toNat / 4))
        (size / 4#32) ga goal)
      (vs := [gxVal ga, .u32 goal, .ptr s.mem.blocks.size 0, .u32 (size / 4#32)])
      (by embc_simp) ?_ ?_
    · exact ⟨rfl, by simpa [hws, List.map_toArray] using hfb,
        by simp [hq, hws, hwords'], hga2, hne2⟩
    intro rv s3 hpost
    obtain ⟨⟨hout, cells, cells', _, hc3, _⟩, r, rfl, hacc⟩ := hpost
    embc_simp
    apply WP.seq
    apply WP.ecall
    embc_simp [kvfree_ptr_run (st := s3) hc3]
    apply WP.ret
    embc_simp [retPost]
    refine ⟨mem_restore (fun b' hb => ?_), r, rfl, hacc⟩
    rw [hout b' hb, hfill b', ite_eq_right (fun e => absurd e hb), hM1 b' hb]

/-- The checker accepts only the payload actually returned by the copy call. -/
theorem vbcf_check_proof_spec (hK : VbcfCheckSpec (State := State)) : VbcfCheckProofSpec (State := State) :=
  vbcf_check_proof_general (Q := fun ws ga goal =>
    (∃ P g, Bcf.decode (wordsToBytes ws) = .ok P ∧ checkBcf P = some g) ∧
      GoalRefuted goal ga) hK

end Vbcf.Proof
