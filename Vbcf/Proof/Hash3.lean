import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Hash2
import Vbcf.Proof.Core1

/-!
# Vbcf proofs: `find_not`
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem ofNat_succ_sub_one (x : Nat) : BitVec.ofNat 32 (x + 1) - 1#32 = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem array_eq_singleton {α : Type} {a : Array α} (h : a.size = 1) : a = #[a[0]] := by
  apply Array.ext
  · simp [h]
  · intro i h1 h2
    have : i = 0 := by omega
    subst this; simp

theorem ofNat_ne_noid {x : Nat} (h : x ≤ 2 ^ 30) : BitVec.ofNat 32 x ≠ noid := by
  intro e
  have := congrArg BitVec.toNat e
  rw [bv_toNat_ofNat (by omega)] at this
  simp [noid] at this
  omega

/-- The node `not ia`. -/
abbrev notNode (ia : Nat) : Node := ⟨.boolNot, #[ia]⟩

theorem hashNode_not (posOf : Nat → Nat) (pool : Pool) (ia : Nat) (a : BitVec 32)
    (ha : a.toNat = offs pool ia) :
    hashNode posOf pool (notNode ia) = hashW [385#32, a] := by
  simp [hashNode, nodeW, hdrW, tailW, tailLen, opC, opLo, opHi, ← ha]

/-- A pool node with the header of `not` and argument word `offs ia` is `not ia`. -/
theorem eq_notNode {posOf : Nat → Nat} {n0 : Node} (hf : Fits posOf n0) (hh : hdrW n0 = 385) :
    n0.op = .boolNot ∧ n0.args.size = 1 := by
  have h1 := hdrW_code hf
  have h2 := hdrW_len hf
  rw [hh] at h1 h2
  have hop : n0.op = .boolNot := opC_boolNot_iff.mp h1.symm
  refine ⟨hop, ?_⟩
  have hl : ¬ IsLeaf n0.op := by rw [hop]; decide
  rw [← tailLen_of_not_leaf hl, ← h2]

/-- The pool pointer is not `NULL` once there is room for a word. -/
theorem pool_ptr_of_pos {W : World} {m : Mem} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : St}
    (h : Holds W m sb c) (hinv : CoreInv posOf c st) (hpos : 0 < c.k.pcap.toNat) :
    ∃ pb, c.k.pool = some (pb, 0) := by
  cases hp : c.k.pool with
  | none => have := hinv.poolNull hp; rw [this] at hpos; simp at hpos
  | some bo =>
    obtain ⟨b, o⟩ := bo
    obtain ⟨rfl, -⟩ := h.arr .pool b o hp
    exact ⟨b, rfl⟩

/-- The loop invariant of `find_not`: only `work` and `err` have changed. -/
def FindNotInv (W : World) (sb : Nat) (c : CMem) (st : St) (a hv : BitVec 32) (ia : Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (wk er i e ok : BitVec 32) (d : Nat),
    Holds W s'.mem sb (c.wev wk er c.k.val) ∧
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("h", .u32, .u32 hv),
      ("i", .u32, .u32 i), ("mask", .u32, .u32 (c.k.hcap - 1#32)), ("e", .u32, .u32 e),
      ("ok", .u32, .u32 ok)] ∧
    i.toNat = (hv.toNat + d) % c.k.hcap.toNat ∧
    Probed st.pool c.htab c.k.hcap.toNat hv (notNode ia) d

/-- The postcondition of `find_not`, named so that `simp` leaves it alone. -/
def FindNotPost (W : World) (sb : Nat) (c : CMem) (st : St) (ia : Nat) (rv : Option EmbC.Val)
    (s' : (KernelState prog State)) : Prop :=
  ∃ wk er r, rv = some (.u32 r) ∧ Holds W s'.mem sb (c.wev wk er c.k.val) ∧
    (er ≠ 0#32 ∨
     match findNode st ⟨.boolNot, #[ia]⟩ with
     | none => r = noid
     | some i => r.toNat = offs st.pool i ∧ r ≠ noid)

theorem find_not_spec : FindNotSpec (State := State) := by
  intro W sb c posOf st a ia
  show FnSpec _ _ _ (fun _ _ rv s' => FindNotPost W sb c st ia rv s')
  have hs := prog_ck
  apply FnSpec.intro' (fn := findNot) rfl
  rintro vs s ⟨rfl, h, hinv, hia, ha⟩
  simp [findNot, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hhv := hashNode_not posOf st.pool ia a ha
  obtain ⟨hb, hhtab⟩ := hinv.htabPtr
  have hpart := hinv.htab.part
  obtain ⟨j, hj, hj30⟩ := hinv.htab.pow
  have hrep := hinv.rep
  have hplen : offs st.pool st.pool.size ≤ 2 ^ 30 := by
    have h1 := hrep.len; have h2 := hinv.poolCap; simp only [maxPool] at h2; omega
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq
  apply WP.while (I := FindNotInv W sb c st a (hashNode posOf st.pool (notNode ia)) ia)
  · refine ⟨c.k.work, c.k.err, hashNode posOf st.pool (notNode ia) &&& (c.k.hcap - 1#32), 0#32,
      0#32, 0, by rw [wev_self]; exact h, ?_, probe_start _ hj, Probed.zero _ _ _ _ _⟩
    rw [hhv]; simp [hashW]
  · rintro env s' ⟨wk, er, i, e, ok, d, h', rfl, hi, hpr⟩
    clear h
    have h := h'
    clear h'
    obtain ⟨e0, hu, he32, hnode⟩ := hpart.slot ((hashNode posOf st.pool (notNode ia)).toNat + d)
    rw [← hi] at hu
    ck_simp [hhtab, h.rd_htab hhtab, rd_u32 hu, ofNat32_eq_zero_iff he32]
    constructor
    · -- an empty slot: the node is not in the pool
      intro he0
      subst he0
      rw [hi] at hu
      have hmiss := hpart.miss (by omega) hpr hu
      have hnone : findNode st ⟨.boolNot, #[ia]⟩ = none :=
        (findNode_eq_none_iff hinv.ok).mpr (fun r => hmiss r trivial)
      apply WP.ret
      ck_simp [retPost]
      exact ⟨_, _, _, rfl, h, Or.inr (by rw [hnone]; rfl)⟩
    · intro he0
      obtain ⟨i0, hi0, rfl⟩ := hnode he0
      obtain ⟨n0, hn0⟩ := node_of_lt (st := st) hi0
      have hoff := hinv.off_lt hi0
      obtain ⟨pb, hpool⟩ : ∃ pb, c.k.pool = some (pb, 0) := by
        have h1 := hrep.offs_lt hi0; have h2 := hinv.poolCap
        exact pool_ptr_of_pos (c := c.wev wk er c.k.val) h hinv.wev (by show 0 < c.k.pcap.toNat; omega)
      have hfit := hrep.fits i0 n0 hn0
      -- one unit of work per probe
      apply WP.seq
      apply WP.call (tick_spec W sb (c.wev wk er c.k.val))
      ck_simp
      refine ⟨h, ?_⟩
      rintro rv s1 rfl h1
      rw [tickM_wev, wev_wev] at h1
      clear h
      have h := h1
      clear h1
      apply WP.seq
      apply WP.ite
      ck_simp
      constructor
      · intro ht
        apply WP.ret
        ck_simp [retPost]
        exact ⟨_, _, _, rfl, h, Or.inl (by rw [tickM_err _ ht]; decide)⟩
      intro ht
      apply WP.skip
      apply WP.seq
      apply WP.assign
      ck_simp [hhtab, h.rd_htab hhtab, rd_u32 hu, ofNat_succ_sub_one]
      apply WP.seq
      apply WP.ite
      by_cases hh : hdrW n0 = 385
      · obtain ⟨hop, hsz⟩ := eq_notNode hfit hh
        obtain ⟨op, args⟩ := n0
        simp only at hop hsz
        subst hop
        have harg : U c.pool (offs st.pool i0 + 1) (offs st.pool args[0]) :=
          hrep.arg hn0 (by decide : ¬ IsLeaf Op.boolNot) (k := 0) (by show 0 < args.size; omega)
        have hlt0 : args[0] < st.pool.size := (hinv.ok.typed hn0).args_lt _ (by simp)
        have ho0 := hinv.off_lt hlt0
        ck_simp [hpool, h.rd_pool hpool, bv_toNat_ofNat (show offs st.pool i0 < 2 ^ 32 by omega),
          rd_u32 (hrep.hdr hn0), hh, idx_add (show offs st.pool i0 + 1 < 2 ^ 32 by omega),
          rd_u32 harg, ofNat_eq_iff (show offs st.pool args[0] < 2 ^ 32 by omega), ha]
        have hstep : ∀ (hne : st.pool[i0]? ≠ some (notNode ia)),
            Probed st.pool c.htab c.k.hcap.toNat (hashNode posOf st.pool (notNode ia))
              (notNode ia) (d + 1) := fun hne =>
          hpr.step (by omega) (hi ▸ hu) he0 he32 (fun i' hi' he => by
            have : i0 = i' := offs_inj (Nat.le_of_lt hi0) (Nat.le_of_lt hi') (by omega)
            subst this; exact hne)
        constructor
        · intro heq
          have hia' : args[0] = ia := offs_inj (Nat.le_of_lt hlt0) (Nat.le_of_lt hia) heq
          have hargs : args = #[ia] := by rw [array_eq_singleton hsz, hia']
          subst hargs
          have hfind : findNode st ⟨.boolNot, #[ia]⟩ = some i0 :=
            (findNode_eq_some_iff hinv.ok).mpr hn0
          apply WP.ret
          ck_simp [retPost, FindNotPost, hfind]
          exact ⟨_, _, h, Or.inr ⟨by omega, ofNat_ne_noid (by omega)⟩⟩
        · intro hne
          have hnn : st.pool[i0]? ≠ some (notNode ia) := by
            rw [hn0]; intro e
            simp only [Option.some.injEq, Node.mk.injEq, true_and] at e
            subst e
            exact hne rfl
          apply WP.skip
          apply WP.assign
          ck_simp
          exact ⟨_, _, _, _, _, d + 1, h, rfl, probe_next hj (by omega) hi, hstep hnn⟩
      · have hnn : st.pool[i0]? ≠ some (notNode ia) := by
          rw [hn0]; intro e
          simp only [Option.some.injEq] at e
          subst e
          exact hh (by simp [hdrW, tailLen, opC, opLo, opHi])
        have hhdr : ¬ BitVec.ofNat 32 (hdrW n0) = 385#32 := by
          intro e
          exact hh ((ofNat_eq_iff (hdrW_lt hfit)).mp e)
        ck_simp [hpool, h.rd_pool hpool, bv_toNat_ofNat (show offs st.pool i0 < 2 ^ 32 by omega),
          rd_u32 (hrep.hdr hn0), hhdr]
        apply WP.skip
        apply WP.assign
        ck_simp
        refine ⟨_, _, _, _, _, d + 1, h, rfl, probe_next hj (by omega) hi, ?_⟩
        exact hpr.step (by omega) (hi ▸ hu) he0 he32 (fun i' hi' he => by
          have : i0 = i' := offs_inj (Nat.le_of_lt hi0) (Nat.le_of_lt hi') (by omega)
          subst this; exact hnn)

end Vbcf.Proof
