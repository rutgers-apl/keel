import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Builders2

/-!
# Vbcf proofs: the node builders, part 3 (`mkn`, `mkval`)
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## `mkn` -/

/-- Loop invariant of `mkn`: the header and the first `i` arguments are written. -/
def MknInv (W : World) (sb : Nat) (c1 : CMem) (st : St) (hd base n : BitVec 32) (is : List Nat) :
    Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c2 : CMem) (i : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("hdr", .u32, .u32 hd),
      ("base", .u32, .u32 base), ("n", .u32, .u32 n), ("r", .u32, .u32 1#32),
      ("i", .u32, .u32 i)] ∧
    i.toNat ≤ n.toNat ∧ Holds W s.mem sb c2 ∧ TailEq c1 c2 ∧
    U c2.pool c1.k.plen.toNat (hd.toNat + is.length * 256) ∧
    ∀ j x, j < i.toNat → is[j]? = some x →
      U c2.pool (c1.k.plen.toNat + 1 + j) (offs st.pool x)

theorem mkn_spec_d (hI : InternSpecD (State := State)) (hR : RoomSpec (State := State)) : DMknSpec (State := State) := by
  intro W sb c posOf st hd base n is
  have hs := prog_ck
  apply FnSpec.intro' (fn := mkn) rfl
  rintro vs s ⟨rfl, h, hinv, hnl, hlen, hsp, hstk⟩
  simp [mkn, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.ite
  ck_simp
  constructor
  · intro hbig
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    clear h
    intro s h
    apply WP.ret
    ck_simp [retPost, MkPostD, BuildPost, noid]
    exact ⟨_, h, PoolFrame.setErr c _, hinv.setErr _⟩
  · intro hsmall
    apply WP.skip
    have hn : n.toNat ≤ 255 := by simpa [BitVec.le_def] using hsmall
    apply WP.seq
    apply WP.call (hR W sb c posOf st (1#32 + n))
    ck_simp
    refine ⟨⟨h, hinv⟩, ?_⟩
    clear h
    intro rv s c1 h hf1 hinv1 hpl hres
    rcases hres with rfl | ⟨rfl, hroom⟩
    · ck_simp
      apply WP.seq
      apply WP.ite
      ck_simp
      apply WP.ret
      ck_simp [retPost, MkPostD, BuildPost, noid]
      exact ⟨c1, h, hf1, hinv1⟩
    · ck_simp
      apply WP.seq
      apply WP.ite
      ck_simp
      apply WP.skip
      replace hroom : c1.k.plen.toNat + 1 + n.toNat ≤ c1.k.pcap.toNat := by
        rw [← hpl] at hroom; omega
      obtain ⟨pb, hpool⟩ := hinv1.poolPtr_of_pcap h (by omega)
      have hsz := hinv1.poolSize pb 0 hpool
      have hpmax := hinv1.poolCap.2
      simp only [maxPool] at hpmax
      apply WP.seq
      apply WP.ck_store .pool h (by rfl) hpool
      ck_simp [hpool]
      refine ⟨by omega, ?_⟩
      clear h
      intro s h
      have h : Holds W s.mem sb (wr c1 c1.k.plen.toNat (hd ||| n <<< 8)) := h
      apply WP.seq
      apply WP.while (I := MknInv W sb c1 st hd base n is)
      · refine ⟨_, 0#32, rfl, by simp, h, TailEq.wr (Nat.le_refl _), ?_, ?_⟩
        · rw [hlen]; exact U_wr_self (by omega) (bv_or_arity hnl.2.1 (by omega))
        · intro j x hj; simp at hj
      · clear h
        rintro env s ⟨c2, i, rfl, hile, h, ht, hu, hargs⟩
        have hk := ht.k
        have hinv2 := hinv1.tailEq ht
        ck_simp
        constructor
        · intro hge
          have hin : i.toNat = n.toNat := by
            have : n.toNat ≤ i.toNat := by simpa [BitVec.le_def] using hge
            omega
          have hw : Written c2 st hd.toNat is := by
            refine ⟨by rw [hk]; exact hu, ?_, by rw [hk, hlen]; exact hroom, by omega⟩
            intro j x hj
            have hjl := lt_length_of_getElem? hj
            refine ⟨(hstk j x hj).1, ?_⟩
            rw [hk]; exact hargs j x (by omega) hj
          exact wp_intern_ret hI rfl rfl h hinv2 (hw.candRaw hnl)
            (fun rv s' hp => mk_finish (hf1.trans ht.poolFrame) hw hnl hinv2 hp)
        · intro hlt
          have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
          obtain ⟨x, hx⟩ : ∃ x, is[i.toNat]? = some x :=
            ⟨is[i.toNat]'(by omega), by simp⟩
          obtain ⟨hxl, hxu⟩ := hstk _ x hx
          have hscap : 0 < c2.k.scap.toNat := by
            have := hinv.stk.cap.1
            rw [hk, hf1.scap]; omega
          obtain ⟨kb, hstkp⟩ := hinv2.stk.stkPtr h hscap
          have hcell : c2.stk[base.toNat + i.toNat]? =
              some (.u32 (BitVec.ofNat 32 (offs st.pool x))) := by
            rw [ht.stk, hf1.stk]; exact hxu
          have hbi : (base + i).toNat = base.toNat + i.toNat := by
            have := c.k.sp.isLt
            rw [bv_add_toNat]; omega
          have hpi : (c2.k.plen + 1#32 + i).toNat = c1.k.plen.toNat + 1 + i.toNat := by
            rw [hk, bv_add_toNat, bv_add_toNat] <;> simp <;> omega
          have hpool2 : c2.k.pool = some (pb, 0) := by rw [hk]; exact hpool
          have hsz2 := ht.size
          apply WP.seq
          apply WP.ck_store .pool h (by rfl) hpool2
          ck_simp [hpool2, hstkp, h.rd_stk hstkp, hbi, rd_u32 hcell, hpi]
          refine ⟨by omega, ?_⟩
          clear h
          intro s h
          have h : Holds W s.mem sb (wr c2 (c1.k.plen.toNat + 1 + i.toNat)
            (BitVec.ofNat 32 (offs st.pool x))) := h
          apply WP.assign
          ck_simp
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
            rw [bv_add_toNat] <;> simp <;> omega
          refine ⟨_, i + 1#32, rfl, by omega, h, ht.trans (TailEq.wr (by rw [hk]; omega)),
            U_wr_ne hu (by omega), ?_⟩
          intro j y hj hy
          by_cases hji : j < i.toNat
          · exact U_wr_ne (hargs j y hji hy) (by omega)
          · have : j = i.toNat := by omega
            subst this
            rw [hx] at hy
            simp only [Option.some.injEq] at hy
            subst hy
            exact U_wr_self (by omega) rfl

/-! ## `mkval`

`MkvalSpec` in `Specs.lean` is not provable: for `w ≤ 32` the C stores only `(u32)v`, so a
value `v ≥ 2^32` whose low word fits `w` bits is accepted as the literal of its low word.
`MkvalSpec'` states what the C does; `MkvalSpecLt` is the original statement under the
precondition every caller establishes. -/

/-- `mkval(st, w, v)` builds the literal `bvVal w v`, with `v` truncated to its low word
when `w ≤ 32`. -/
def MkvalSpec' : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (w : BitVec 32) (v : BitVec 64),
    EmbC.FnSpec (State := State) Vbcf.prog "mkval"
      (fun vs s => vs = [.ptr sb 0, .u32 w, .u64 v] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
        ((r = noid ∧ CoreInv posOf c' st) ∨
         (∃ st' i, pushNode st ⟨.bvVal w.toNat
              (if w.toNat ≤ 32 then v.toNat % 2 ^ 32 else v.toNat), #[]⟩ = some (st', i) ∧
            CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid)))

/-- Historical name: `MkvalSpec (State := State)` now carries the fits-one-word precondition. -/
abbrev MkvalSpecLt : Prop := MkvalSpec (State := State)

theorem bv_valhdr {w : BitVec 32} (hw : w.toNat ≤ 64) :
    8#32 ||| ((w + 31#32) / 32#32) <<< 8 ||| w <<< 16 =
      BitVec.ofNat 32 (8 + (w.toNat + 31) / 32 * 256 + w.toNat * 65536) := by
  have hq : ((w + 31#32) / 32#32).toNat = (w.toNat + 31) / 32 := by
    rw [BitVec.toNat_udiv, bv_add_toNat] <;> simp; omega
  have h8 : (8#32).toNat = 8 := rfl
  have hsh : w.toNat <<< 16 % 2 ^ 32 = w.toNat <<< 16 := by
    rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, bv_or_arity (h := 8#32) (by decide) (by rw [hq]; omega), hq, h8,
    bv_toNat_ofNat (by omega), BitVec.toNat_shiftLeft, hsh, bv_toNat_ofNat (by omega)]
  exact nat_or_par (by omega)

theorem bv_low (v : BitVec 64) : v.setWidth 32 = BitVec.ofNat 32 (v.toNat % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv_toNat_ofNat (Nat.mod_lt _ (by decide))]

theorem bv_high (v : BitVec 64) : (v >>> 32).setWidth 32 = BitVec.ofNat 32 (v.toNat / 2 ^ 32) := by
  have := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    bv_toNat_ofNat (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem candRaw_bvVal {posOf : Nat → Nat} {c : CMem} {st : St} {w : Nat}
    (hw1 : 1 ≤ w) (hw2 : w ≤ 64)
    (hu : U c.pool c.k.plen.toNat (8 + (w + 31) / 32 * 256 + w * 65536))
    (h1 : ∃ x, x < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 1) x)
    (h2 : 32 < w → ∃ x, x < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 2) x)
    (hroom : c.k.plen.toNat + 3 ≤ c.k.pcap.toNat) : CandRaw posOf c st := by
  have hc : (8 + (w + 31) / 32 * 256 + w * 65536) % 256 = 8 := by omega
  have hl : (8 + (w + 31) / 32 * 256 + w * 65536) / 256 % 256 = (w + 31) / 32 := by omega
  refine ⟨_, by omega, hu, ?_, ?_, ?_, ?_⟩
  · rw [hl]; omega
  · rw [hc]; intro hv; rcases hv with hv | hv <;> cases hv
  · rw [hl]
    intro _ k hk
    by_cases hk0 : k = 0
    · subst hk0; exact h1
    · have hk1 : k = 1 := by omega
      subst hk1; exact h2 (by omega)
  · rw [hc]; intro _ _ hv; exact absurd rfl hv

/-- The postcondition of `MkvalSpec'`, named so that `simp` leaves it alone. -/
def MkvalPost (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (w : BitVec 32)
    (v : BitVec 64) : Option EmbC.Val → (KernelState prog State) → Prop :=
  BuildPost W sb c posOf st (fun st' i => Interned st ⟨.bvVal w.toNat
    (if w.toNat ≤ 32 then v.toNat % 2 ^ 32 else v.toNat), #[]⟩ st' i)

theorem MkvalPost.fail {W : World} {sb : Nat} {c c' : CMem} {posOf : Nat → Nat} {st : St}
    {w : BitVec 32} {v : BitVec 64} {s' : (KernelState prog State)} (h : Holds W s'.mem sb c') (hf : PoolFrame c c')
    (hinv : CoreInv posOf c' st) :
    MkvalPost W sb c posOf st w v (some (.u32 0xffffffff#32)) s' :=
  ⟨c', _, rfl, h, hf, Or.inl ⟨rfl, hinv⟩⟩

theorem mkval_spec_d' (hI : InternSpecD (State := State)) (hR : RoomSpec (State := State)) : DMkvalSpec' (State := State) := by
  intro W sb c posOf st w v
  show FnSpec (State := State) Vbcf.prog "mkval" _ (fun _ _ => MkvalPost W sb c posOf st w v)
  have hs := prog_ck
  apply FnSpec.intro' (fn := mkval) rfl
  rintro vs s ⟨rfl, h, hinv⟩
  simp [mkval, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.ite
  ck_simp
  by_cases hw0 : w = 0#32
  · simp only [hw0, ↓reduceIte]
    refine ⟨fun _ => ?_, fun e => absurd e (by decide)⟩
    apply WP.ret
    ck_simp [retPost, NOID]
    exact MkvalPost.fail h (PoolFrame.unchanged c) hinv
  by_cases hw64 : 64#32 < w
  · simp only [hw0, hw64, ↓reduceIte]
    refine ⟨fun _ => ?_, fun e => absurd e (by decide)⟩
    apply WP.ret
    ck_simp [retPost, NOID]
    exact MkvalPost.fail h (PoolFrame.unchanged c) hinv
  simp only [hw0, hw64, ↓reduceIte]
  refine ⟨fun e => absurd trivial e, fun _ => ?_⟩
  apply WP.skip
  have hw1 : 1 ≤ w.toNat := by
    have : w.toNat ≠ 0 := fun e => hw0 (BitVec.eq_of_toNat_eq e)
    omega
  have hw2 : w.toNat ≤ 64 := by simpa [BitVec.lt_def] using hw64
  have hq : ((w + 31#32) / 32#32).toNat = (w.toNat + 31) / 32 := by
    rw [BitVec.toNat_udiv, bv_add_toNat] <;> simp; omega
  apply WP.seq
  apply WP.assign
  ck_simp
  apply WP.seq
  apply WP.call (hR W sb c posOf st 3#32)
  ck_simp
  refine ⟨⟨h, hinv⟩, ?_⟩
  clear h
  intro rv s c1 h hf1 hinv1 hpl hres
  rcases hres with rfl | ⟨rfl, hroom⟩
  · ck_simp
    apply WP.seq
    apply WP.ite
    ck_simp
    apply WP.ret
    ck_simp [retPost]
    exact MkvalPost.fail h hf1 hinv1
  · ck_simp
    apply WP.seq
    apply WP.ite
    ck_simp
    apply WP.skip
    rw [← hpl] at hroom
    obtain ⟨pb, hpool⟩ := hinv1.poolPtr_of_pcap h (by omega)
    have hsz := hinv1.poolSize pb 0 hpool
    have hpmax := hinv1.poolCap.2
    simp only [maxPool] at hpmax
    have hp1 : (c1.k.plen + 1#32).toNat = c1.k.plen.toNat + 1 := by
      rw [bv_add_toNat] <;> simp <;> omega
    have hp2 : (c1.k.plen + 2#32).toNat = c1.k.plen.toNat + 2 := by
      rw [bv_add_toNat] <;> simp <;> omega
    -- the common end: intern the candidate
    have fin : ∀ (s : (KernelState prog State)) (c2 : CMem) (vl : BitVec 32), Holds W s.mem sb c2 → TailEq c1 c2 →
        U c2.pool c1.k.plen.toNat (8 + (w.toNat + 31) / 32 * 256 + w.toNat * 65536) →
        U c2.pool (c1.k.plen.toNat + 1) (v.toNat % 2 ^ 32) →
        (32 < w.toNat → U c2.pool (c1.k.plen.toNat + 2) (v.toNat / 2 ^ 32)) →
        WP Vbcf.prog ((Stmt.call (some "r") "ck_intern" [Expr.var "st"]).seq
            (Stmt.ret (some (Expr.var "r"))))
          (retPost (some .u32) (MkvalPost W sb c posOf st w v))
          [("st", .ptr (.struct "ck"), .ptr sb 0), ("w", .u32, .u32 w), ("v", .u64, .u64 v),
            ("r", .u32, .u32 1#32), ("vlen", .u32, .u32 vl)] s := by
      intro s c2 vl h ht hu hlo hhi
      have hk := ht.k
      have hinv2 := hinv1.tailEq ht
      have hvlt := v.isLt
      rw [← hk] at hu hlo hhi
      refine wp_intern_ret hI rfl rfl h hinv2
        (candRaw_bvVal hw1 hw2 hu ⟨_, Nat.mod_lt _ (by decide), hlo⟩
          (fun h32 => ⟨_, by omega, hhi h32⟩) (by rw [hk]; exact hroom)) ?_
      rintro rv s' ⟨c', r, hrv, h', hf, hres⟩
      refine ⟨c', r, hrv, h', (hf1.trans ht.poolFrame).trans hf, ?_⟩
      rcases hres with hfail | ⟨st', i, ⟨n, hc, hp⟩, hinv', hr, hne⟩
      · exact Or.inl hfail
      · have := cand_bvVal hw2 hvlt hu hlo hhi hc hp.typed
        subst this
        exact Or.inr ⟨st', i, hp, hinv', hr, hne⟩
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, BV_VAL]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr c1 c1.k.plen.toNat
      (8#32 ||| ((w + 31#32) / 32#32) <<< 8 ||| w <<< 16)) := h
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, hp1]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr (wr c1 c1.k.plen.toNat
      (8#32 ||| ((w + 31#32) / 32#32) <<< 8 ||| w <<< 16)) (c1.k.plen.toNat + 1)
      (v.setWidth 32)) := h
    have hu0 : U (wr c1 c1.k.plen.toNat (8#32 ||| ((w + 31#32) / 32#32) <<< 8 ||| w <<< 16)).pool
        c1.k.plen.toNat (8 + (w.toNat + 31) / 32 * 256 + w.toNat * 65536) :=
      U_wr_self (by omega) (bv_valhdr hw2)
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro hv2
      have h32 : 32 < w.toNat := by
        have := congrArg BitVec.toNat hv2
        rw [hq] at this; simp at this; omega
      apply WP.ck_store .pool h (by rfl) hpool
      ck_simp [hpool, hp2]
      refine ⟨by omega, ?_⟩
      clear h
      intro s h
      refine fin s _ _ h
        (((TailEq.wr (Nat.le_refl _)).trans (TailEq.wr (by simp))).trans (TailEq.wr (by simp)))
        (U_wr_ne (U_wr_ne hu0 (by simp)) (by simp))
        (U_wr_ne (U_wr_self (by simp; omega) (bv_low v)) (by simp))
        (fun _ => U_wr_self (by simp; omega) (bv_high v))
    · intro hv2
      have h32 : ¬ 32 < w.toNat := by
        intro hgt
        apply hv2
        apply BitVec.eq_of_toNat_eq
        rw [hq]; simp; omega
      apply WP.skip
      exact fin s _ _ h ((TailEq.wr (Nat.le_refl _)).trans (TailEq.wr (by simp)))
        (U_wr_ne hu0 (by simp)) (U_wr_self (by simp; omega) (bv_low v))
        (fun hgt => absurd hgt h32)

/-- The original statement, for callers that pass a value fitting one word when `w ≤ 32`. -/
theorem mkval_spec_lt_d (hI : InternSpecD (State := State)) (hR : RoomSpec (State := State)) : DMkvalSpec (State := State) := by
  intro W sb c posOf st w v
  refine FnSpec.conseq (mkval_spec_d' hI hR W sb c posOf st w v)
    (fun vs s hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
  rintro vs s rv s' ⟨-, -, -, hv⟩ ⟨c', r, hrv, h', hf, hres⟩
  refine ⟨c', r, hrv, h', hf, ?_⟩
  rcases hres with hfail | ⟨st', i, hp, hrest⟩
  · exact Or.inl hfail
  · refine Or.inr ⟨st', i, ?_, hrest⟩
    by_cases h32 : w.toNat ≤ 32
    · simp only [h32, ↓reduceIte, Nat.mod_eq_of_lt (hv h32)] at hp; exact hp
    · simp only [h32, ↓reduceIte] at hp; exact hp

/-! ## The refinement proof's builder contracts -/

theorem mkn_spec (hI : InternSpec (State := State)) (hR : RoomSpec (State := State)) : MknSpec (State := State) :=
  (mkn_spec_d (InternSpecD.of_spec hI) hR).old

theorem mkval_spec_lt (hI : InternSpec (State := State)) (hR : RoomSpec (State := State)) : MkvalSpecLt (State := State) :=
  (mkval_spec_lt_d (InternSpecD.of_spec hI) hR).old

theorem mkval_spec' (hI : InternSpec (State := State)) (hR : RoomSpec (State := State)) : MkvalSpec' (State := State) := by
  intro W sb c posOf st w v
  refine FnSpec.conseq (mkval_spec_d' (InternSpecD.of_spec hI) hR W sb c posOf st w v)
    (fun _ _ hp => hp) ?_
  rintro vs s rv s' ⟨-, -, hinv⟩ ⟨c', r, hrv, h', hf, hres⟩
  refine ⟨c', r, hrv, h', hf, ?_⟩
  rcases hres with hfail | ⟨st', i, hn, hrest⟩
  · exact Or.inl hfail
  · exact Or.inr ⟨st', i, hn.pushNode_eq hinv.ok, hrest⟩

end Vbcf.Proof
