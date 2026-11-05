import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Builders1

/-!
# Vbcf proofs: the node builders, part 2 (`mk0` … `mk3`, `mk_eq`, `mk_not`)
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## The common tail of every builder: `r = ck_intern(st); return r;` -/

theorem Env.get_set_self {env : Env} {x : Var} {t : EmbC.Ty} {v : EmbC.Val} (h : env.ty x = some t) :
    (env.set x v).get x = some v := by
  induction env with
  | nil => simp [Env.ty] at h
  | cons e env ih =>
    obtain ⟨y, t', w⟩ := e
    by_cases hy : y = x
    · simp [Env.set, Env.get, hy]
    · simp only [Env.ty, hy, ↓reduceIte] at h
      simp [Env.set, Env.get, hy, ih h]

/-- `r = ck_intern(st); return r;` in any environment: it is enough to derive the
function's postcondition from `ck_intern`'s. -/
theorem wp_intern_ret (hI : InternSpecD (State := State)) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat}
    {st : St} {env : Env} {s : (KernelState prog State)} {R : Option EmbC.Val → (KernelState prog State) → Prop}
    (hst : env.get "st" = some (.ptr sb 0)) (hr : env.ty "r" = some .u32)
    (h : Holds W s.mem sb c) (hinv : CoreInv posOf c st) (hraw : CandRaw posOf c st)
    (hR : ∀ rv s', InternPostD W sb c posOf st rv s' → R rv s') :
    WP Vbcf.prog ((Stmt.call (some "r") "ck_intern" [Expr.var "st"]).seq
      (Stmt.ret (some (Expr.var "r")))) (retPost (some .u32) R) env s := by
  have hspec : FnSpec (State := State) Vbcf.prog "ck_intern"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧ CandRaw posOf c st)
      (fun _ _ => InternPostD W sb c posOf st) := hI W sb c posOf st
  apply WP.seq
  apply WP.call hspec
  simp only [evalArgs, evalE, hst]
  refine ⟨⟨by trivial, h, hinv, hraw⟩, ?_⟩
  intro rv s' hp
  have hp' := hp
  obtain ⟨c', r, rfl, -⟩ := hp'
  simp only [assignDst_some, Env.assign, hr, Mem.hasTy_u32, ↓reduceIte]
  apply WP.ret
  simp only [evalE, Env.get_set_self hr, retPost, Mem.hasTy_u32, true_and]
  exact hR _ _ hp

/-! ## `mk1`, `mk2`, `mk3` -/

theorem mk1_spec_d (hI : InternSpecD (State := State)) (hR : RoomSpec (State := State)) : DMk1Spec (State := State) := by
  intro W sb c posOf st hd a ia
  have hs := prog_ck
  apply FnSpec.intro' (fn := mk1) rfl
  rintro vs s ⟨rfl, h, hinv, hnl, hia, ha⟩
  simp [mk1, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.call (hR W sb c posOf st 2#32)
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
    rw [← hpl] at hroom
    obtain ⟨pb, hpool⟩ := hinv1.poolPtr_of_pcap h (by omega)
    have hsz := hinv1.poolSize pb 0 hpool
    have hpmax := hinv1.poolCap.2
    simp only [maxPool] at hpmax
    have hp1 : (c1.k.plen + 1#32).toNat = c1.k.plen.toNat + 1 := by
      rw [bv_add_toNat] <;> simp <;> omega
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr c1 c1.k.plen.toNat (hd ||| 256#32)) := h
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, hp1]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr (wr c1 c1.k.plen.toNat (hd ||| 256#32)) (c1.k.plen.toNat + 1) a) := h
    have ht : TailEq c1 (wr (wr c1 c1.k.plen.toNat (hd ||| 256#32)) (c1.k.plen.toNat + 1) a) :=
      (TailEq.wr (Nat.le_refl _)).trans (TailEq.wr (by simp))
    have hinv2 := hinv1.tailEq ht
    have hw : Written (wr (wr c1 c1.k.plen.toNat (hd ||| 256#32)) (c1.k.plen.toNat + 1) a) st
        hd.toNat [ia] := by
      apply Written.of1 _ _ hia (by simpa using hroom)
      · exact U_wr_ne (U_wr_self (by omega) (bv_or_256 hnl.2.1)) (by simp)
      · exact U_wr_self (by simp; omega) (by rw [← ha, bv_ofNat_toNat])
    exact wp_intern_ret hI rfl rfl h hinv2 (hw.candRaw hnl)
      (fun rv s' hp => mk_finish (hf1.trans ht.poolFrame) hw hnl hinv2 hp)

theorem mk2_spec_d (hI : InternSpecD (State := State)) (hR : RoomSpec (State := State)) : DMk2Spec (State := State) := by
  intro W sb c posOf st hd a b ia ib
  have hs := prog_ck
  apply FnSpec.intro' (fn := mk2) rfl
  rintro vs s ⟨rfl, h, hinv, hnl, hia, ha, hib, hb⟩
  simp [mk2, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
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
    ck_simp [retPost, MkPostD, BuildPost, noid]
    exact ⟨c1, h, hf1, hinv1⟩
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
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr c1 c1.k.plen.toNat (hd ||| 512#32)) := h
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, hp1]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr (wr c1 c1.k.plen.toNat (hd ||| 512#32)) (c1.k.plen.toNat + 1) a) := h
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, hp2]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    obtain ⟨c2, hc2⟩ : ∃ c2, c2 = wr (wr (wr c1 c1.k.plen.toNat (hd ||| 512#32))
        (c1.k.plen.toNat + 1) a) (c1.k.plen.toNat + 2) b := ⟨_, rfl⟩
    have h : Holds W s.mem sb c2 := by rw [hc2]; exact h
    have ht : TailEq c1 c2 := by
      rw [hc2]
      exact ((TailEq.wr (Nat.le_refl _)).trans (TailEq.wr (by simp))).trans (TailEq.wr (by simp))
    have hinv2 := hinv1.tailEq ht
    have hw : Written c2 st hd.toNat [ia, ib] := by
      rw [hc2]
      apply Written.of2 _ _ hia _ hib (by simpa using hroom)
      · exact U_wr_ne (U_wr_ne (U_wr_self (by omega) (bv_or_512 hnl.2.1)) (by simp)) (by simp)
      · exact U_wr_ne (U_wr_self (by simp; omega) (by rw [← ha, bv_ofNat_toNat])) (by simp)
      · exact U_wr_self (by simp; omega) (by rw [← hb, bv_ofNat_toNat])
    exact wp_intern_ret hI rfl rfl h hinv2 (hw.candRaw hnl)
      (fun rv s' hp => mk_finish (hf1.trans ht.poolFrame) hw hnl hinv2 hp)

theorem mk3_spec_d (hI : InternSpecD (State := State)) (hR : RoomSpec (State := State)) : DMk3Spec (State := State) := by
  intro W sb c posOf st hd a b d ia ib id
  have hs := prog_ck
  apply FnSpec.intro' (fn := mk3) rfl
  rintro vs s ⟨rfl, h, hinv, hnl, hia, ha, hib, hb, hid, hdd⟩
  simp [mk3, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.call (hR W sb c posOf st 4#32)
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
    rw [← hpl] at hroom
    obtain ⟨pb, hpool⟩ := hinv1.poolPtr_of_pcap h (by omega)
    have hsz := hinv1.poolSize pb 0 hpool
    have hpmax := hinv1.poolCap.2
    simp only [maxPool] at hpmax
    have hp1 : (c1.k.plen + 1#32).toNat = c1.k.plen.toNat + 1 := by
      rw [bv_add_toNat] <;> simp <;> omega
    have hp2 : (c1.k.plen + 2#32).toNat = c1.k.plen.toNat + 2 := by
      rw [bv_add_toNat] <;> simp <;> omega
    have hp3 : (c1.k.plen + 3#32).toNat = c1.k.plen.toNat + 3 := by
      rw [bv_add_toNat] <;> simp <;> omega
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr c1 c1.k.plen.toNat (hd ||| 768#32)) := h
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, hp1]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr (wr c1 c1.k.plen.toNat (hd ||| 768#32)) (c1.k.plen.toNat + 1) a) := h
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, hp2]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    have h : Holds W s.mem sb (wr (wr (wr c1 c1.k.plen.toNat (hd ||| 768#32))
        (c1.k.plen.toNat + 1) a) (c1.k.plen.toNat + 2) b) := h
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool, hp3]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    obtain ⟨c2, hc2⟩ : ∃ c2, c2 = wr (wr (wr (wr c1 c1.k.plen.toNat (hd ||| 768#32))
        (c1.k.plen.toNat + 1) a) (c1.k.plen.toNat + 2) b) (c1.k.plen.toNat + 3) d := ⟨_, rfl⟩
    have h : Holds W s.mem sb c2 := by rw [hc2]; exact h
    have ht : TailEq c1 c2 := by
      rw [hc2]
      exact (((TailEq.wr (Nat.le_refl _)).trans (TailEq.wr (by simp))).trans
        (TailEq.wr (by simp))).trans (TailEq.wr (by simp))
    have hinv2 := hinv1.tailEq ht
    have hw : Written c2 st hd.toNat [ia, ib, id] := by
      rw [hc2]
      apply Written.of3 _ _ hia _ hib _ hid (by simpa using hroom)
      · exact U_wr_ne (U_wr_ne (U_wr_ne (U_wr_self (by omega) (bv_or_768 hnl.2.1)) (by simp))
          (by simp)) (by simp)
      · exact U_wr_ne (U_wr_ne (U_wr_self (by simp; omega) (by rw [← ha, bv_ofNat_toNat]))
          (by simp)) (by simp)
      · exact U_wr_ne (U_wr_self (by simp; omega) (by rw [← hb, bv_ofNat_toNat])) (by simp)
      · exact U_wr_self (by simp; omega) (by rw [← hdd, bv_ofNat_toNat])
    exact wp_intern_ret hI rfl rfl h hinv2 (hw.candRaw hnl)
      (fun rv s' hp => mk_finish (hf1.trans ht.poolFrame) hw hnl hinv2 hp)

/-! ## `mk0` on a boolean literal -/

theorem candRaw_boolVal {posOf : Nat → Nat} {c : CMem} {st : St} {b : Bool}
    (hu : U c.pool c.k.plen.toNat (if b then 0x10009 else 0x9))
    (hroom : c.k.plen.toNat + 1 ≤ c.k.pcap.toNat) : CandRaw posOf c st := by
  cases b
  · exact ⟨⟨_, by decide, hu, by simpa using hroom, by simp, by simp, by simp⟩⟩
  · exact ⟨⟨_, by decide, hu, by simpa using hroom, by simp, by simp, by simp⟩⟩

theorem mk0_bool_spec_d (hI : InternSpecD (State := State)) (hR : RoomSpec (State := State)) : DMk0BoolSpec (State := State) := by
  intro W sb c posOf st b
  have hs := prog_ck
  apply FnSpec.intro' (fn := mk0) rfl
  rintro vs s ⟨rfl, h, hinv⟩
  simp [mk0, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.call (hR W sb c posOf st 1#32)
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
    ck_simp [retPost, BuildPost, noid]
    exact ⟨c1, h, hf1, hinv1⟩
  · ck_simp
    apply WP.seq
    apply WP.ite
    ck_simp
    apply WP.skip
    rw [← hpl] at hroom
    obtain ⟨pb, hpool⟩ := hinv1.poolPtr_of_pcap h (by omega)
    have hsz := hinv1.poolSize pb 0 hpool
    apply WP.seq
    apply WP.ck_store .pool h (by rfl) hpool
    ck_simp [hpool]
    refine ⟨by omega, ?_⟩
    clear h
    intro s h
    obtain ⟨c2, hc2⟩ : ∃ c2, c2 = wr c1 c1.k.plen.toNat (if b then 0x10009#32 else 0x9#32) :=
      ⟨_, rfl⟩
    have h : Holds W s.mem sb c2 := by rw [hc2]; exact h
    have ht : TailEq c1 c2 := by rw [hc2]; exact TailEq.wr (Nat.le_refl _)
    have hinv2 := hinv1.tailEq ht
    have hu : U c2.pool c2.k.plen.toNat (if b then 0x10009 else 0x9) := by
      rw [hc2]; exact U_wr_self (by omega) (by cases b <;> rfl)
    refine wp_intern_ret hI rfl rfl h hinv2
      (candRaw_boolVal hu (by rw [hc2]; simpa using hroom)) ?_
    rintro rv s' ⟨c', r, hrv, h', hf, hres⟩
    refine ⟨c', r, hrv, h', (hf1.trans ht.poolFrame).trans hf, ?_⟩
    rcases hres with hfail | ⟨st', i, ⟨n, hc, hp⟩, hinv', hr, hne⟩
    · exact Or.inl hfail
    · have := cand_boolVal hu hc hp.typed
      subst this
      exact Or.inr ⟨st', i, hp, hinv', hr, hne⟩

/-! ## The refinement proof's builder contracts -/

theorem mk1_spec (hI : InternSpec (State := State)) (hR : RoomSpec (State := State)) : Mk1Spec (State := State) :=
  (mk1_spec_d (InternSpecD.of_spec hI) hR).old
theorem mk2_spec (hI : InternSpec (State := State)) (hR : RoomSpec (State := State)) : Mk2Spec (State := State) :=
  (mk2_spec_d (InternSpecD.of_spec hI) hR).old
theorem mk3_spec (hI : InternSpec (State := State)) (hR : RoomSpec (State := State)) : Mk3Spec (State := State) :=
  (mk3_spec_d (InternSpecD.of_spec hI) hR).old
theorem mk0_bool_spec (hI : InternSpec (State := State)) (hR : RoomSpec (State := State)) : Mk0BoolSpec (State := State) :=
  (mk0_bool_spec_d (InternSpecD.of_spec hI) hR).old

/-! ## `mk_eq`, `mk_not` -/

theorem mk_eq_spec (h2 : Mk2Spec (State := State)) : MkEqSpec (State := State) := by
  intro W sb c posOf st a b ia ib
  have hs := prog_ck
  apply FnSpec.intro' (fn := mkEq) rfl
  rintro vs s ⟨rfl, h, hinv, hia, ha, hib, hb⟩
  simp [mkEq, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.call (h2 W sb c posOf st 0x11#32 a b ia ib)
  ck_simp [BOOL_EQ]
  refine ⟨⟨h, hinv, by simp [NonLeafHdr], hia, ha, hib, hb⟩, ?_⟩
  clear h
  rintro rv s ⟨c', r, rfl, h, hf, hres⟩
  ck_simp
  apply WP.ret
  ck_simp [retPost]
  refine ⟨c', h, hf, ?_⟩
  rcases hres with hfail | ⟨n, st', i, hh, hfit, hargs, hp, hinv', hr, hne⟩
  · exact Or.inl hfail
  · have hcode := hdrW_code hfit
    have hop : n.op = .eq := opC_eq_iff.mp (by rw [← hcode, hh]; simp)
    rcases n with ⟨op, args⟩
    simp only at hop hargs
    subst hop hargs
    exact Or.inr ⟨st', i, hp, hinv', hr, hne⟩

theorem mk_not_spec (h1 : Mk1Spec (State := State)) : MkNotSpec (State := State) := by
  intro W sb c posOf st a ia
  have hs := prog_ck
  apply FnSpec.intro' (fn := mkNot) rfl
  rintro vs s ⟨rfl, h, hinv, hia, ha⟩
  simp [mkNot, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.call (h1 W sb c posOf st 0x81#32 a ia)
  ck_simp [BOOL_NOT]
  refine ⟨⟨h, hinv, by simp [NonLeafHdr], hia, ha⟩, ?_⟩
  clear h
  rintro rv s ⟨c', r, rfl, h, hf, hres⟩
  ck_simp
  apply WP.ret
  ck_simp [retPost]
  refine ⟨c', h, hf, ?_⟩
  rcases hres with hfail | ⟨n, st', i, hh, hfit, hargs, hp, hinv', hr, hne⟩
  · exact Or.inl hfail
  · have hcode := hdrW_code hfit
    have hop : n.op = .boolNot := opC_boolNot_iff.mp (by rw [← hcode, hh]; simp)
    rcases n with ⟨op, args⟩
    simp only at hop hargs
    subst hop hargs
    exact Or.inr ⟨st', i, hp, hinv', hr, hne⟩

end Vbcf.Proof
