import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.DLoad1

/-!
# Vbcf proofs: `ck_load` against its structural contract

`ck_load_dspec : DLoadSpec`.  The proof follows the C body exactly as the
refinement proof `ck_load_spec` does (same loop invariants for the candidate
writing loops), but the outer loop carries `DLoadState` and the node interned
by `ck_intern` is described by `ck_intern_dspec` (`Interned`): no functional
loader (`loadNode`, `specN`, `LoadInv`) and no `pushNode` is involved.
-/

set_option linter.unusedSimpArgs false

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The postcondition of `ck_load`, structural form. -/
def DLoadPost (W : World) (sb : Nat) (ws : Array (BitVec 32)) (tt ff : Nat) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c', Holds W s'.mem sb c' ∧
    (rv = some (.u32 0#32) ∨
     (rv = some (.u32 1#32) ∧ ∃ st2 pm, DLoadDone W ws c' tt ff st2 pm))

/-- The loop invariant of `ck_load`, structural form. -/
def DLoadLoopInv (W : World) (sb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (tt ff : Nat) :
    Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (p hdr code vlen i a id ok : BitVec 32) (c : CMem) (d : Nat) (st : St) (pm : Nat → Option Nat),
    env = ldEnv sb W.pb n (wordFn ws 1) (wordFn ws 2) p hdr code vlen i a id ok ∧
    Holds W s.mem sb c ∧ DLoadState W ws c tt ff p.toNat d st pm

theorem ck_load_dspec : DLoadSpec (State := State) := by
  intro W sb c ws n st1 tt ff
  show FnSpec (State := State) Vbcf.prog "ck_load" _ (fun _ _ => DLoadPost W sb ws tt ff)
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckLoad) rfl
  rintro vs s ⟨rfl, h, hid, hproof, hn⟩
  simp [ckLoad, bindParams, Mem.hasTy_ptr h.ck rfl, Mem.hasTy_ptr h.proof rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hws : ws.size < 2 ^ 32 := by rw [← hn]; exact n.isLt
  have hrd : ∀ i, i < ws.size → s.mem.loadArr W.pb i = some (.u32 (BitVec.ofNat 32 (wordFn ws i))) := by
    intro i hi; rw [h.loadProof, hproof, rd_words hi]
  apply WP.ifRet
  ck_simp
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · refine ⟨rfl, c, h, Or.inl rfl⟩
  have hsz : 3 ≤ ws.size := by
    rw [BitVec.le_def] at hge; simp at hge; omega
  have hwlt : ∀ i, wordFn ws i < 2 ^ 32 := wordFn_lt ws
  apply WP.ifRet
  ck_simp [hrd 0 (by omega)]
  refine ⟨fun _ => ⟨rfl, c, h, Or.inl rfl⟩, fun hmag => ?_⟩
  have hmagic : wordFn ws 0 = 0x0BCF := by
    have := congrArg BitVec.toNat hmag
    rw [bv_toNat_ofNat (hwlt 0)] at this; simpa using this
  apply WP.seq
  apply WP.assign
  ck_simp [hrd 1 (by omega)]
  apply WP.seq
  apply WP.assign
  ck_simp [hrd 2 (by omega)]
  apply WP.ifRet
  ck_simp
  by_cases hne0 : wordFn ws 1 = 0
  · have : BitVec.ofNat 32 (wordFn ws 1) = 0#32 := by rw [hne0]
    simp only [this, ↓reduceIte]
    exact ⟨fun _ => ⟨rfl, c, h, Or.inl rfl⟩, fun e => by simp at e⟩
  have hb1 : BitVec.ofNat 32 (wordFn ws 1) ≠ 0#32 := by
    intro e; have := congrArg BitVec.toNat e; rw [bv_toNat_ofNat (hwlt 1)] at this; exact hne0 this
  simp only [hb1, ↓reduceIte, Nat.mod_eq_of_lt (hwlt 2)]
  by_cases hns2 : wordFn ws 2 < 2
  · simp only [hns2, ↓reduceIte]
    exact ⟨fun _ => ⟨rfl, c, h, Or.inl rfl⟩, fun e => by simp at e⟩
  simp only [hns2, ↓reduceIte]
  refine ⟨fun e => absurd trivial e, fun _ => ?_⟩
  apply WP.ifRet
  ck_simp
  have hsum : (BitVec.setWidth 64 (BitVec.ofNat 32 (wordFn ws 1)) +
      BitVec.setWidth 64 (BitVec.ofNat 32 (wordFn ws 2)) + 3#64 = BitVec.setWidth 64 n) ↔
      3 + wordFn ws 1 + wordFn ws 2 = ws.size := by
    have h1 := hwlt 1; have h2 := hwlt 2
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, bv_toNat_ofNat h1, bv_toNat_ofNat h2, hn]
    simp only [Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod]
    omega
  rw [hsum]
  refine ⟨fun _ => ⟨rfl, c, h, Or.inl rfl⟩, fun hlen => ?_⟩
  -- st->proof = proof; st->nexpr = ne;
  have hpnull : c.k.proof = none := hid.proofNull
  obtain ⟨hst, hH⟩ := h.setProof hs
  apply WP.seq
  apply WP.setField
  embc_simp [hst]
  clear h
  have h := hH
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp
  clear h
  intro s1 h
  apply WP.seq
  apply WP.while (I := DLoadLoopInv W sb ws n tt ff)
  · refine ⟨0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, _, 0, st1, fun _ => none, rfl, h, ?_⟩
    have hcore := hid.core (posOfW (wordFn ws)) (fun a b e => posOfW_inj _ e)
    exact DLoadState.init (hcore.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) hid.b2 hid.tt
      hid.ff ⟨hid.prem.ptr, hid.prem.size, hid.prem.cells⟩ hid.factsNull hid.flen rfl
      (bv_toNat_ofNat (hwlt 1)) hproof hid.lrNull
  rintro env s2 ⟨p, hdr, code, vlen, i, a, id, ok, c, d, st, pm, rfl, h, hl⟩
  have hple := hl.ple
  ck_simp [ldEnv]
  have hne1 : (BitVec.ofNat 32 (wordFn ws 1)).toNat = wordFn ws 1 := bv_toNat_ofNat (hwlt 1)
  constructor
  · intro hge
    have hpe : p.toNat = wordFn ws 1 := by
      have : wordFn ws 1 ≤ p.toNat := by rw [BitVec.le_def, hne1] at hge; exact hge
      omega
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    clear h
    intro s3 h
    apply WP.ret
    ck_simp [retPost]
    exact ⟨_, h, Or.inr ⟨rfl, st, pm, hl.done hpe hsz hmagic hne0 (by omega) hlen (by omega)⟩⟩
  intro hlt
  have hlt' : p.toNat < wordFn ws 1 := by rw [BitVec.lt_def, hne1] at hlt; exact hlt
  -- hdr = proof[3 + p]; code = hdr & 0xff; vlen = (hdr >> 8) & 0xff;
  have h3p : (3#32 + p).toNat = 3 + p.toNat := by rw [bv_add_toNat] <;> simp <;> omega
  have hcell := hl.rest (3 + p.toNat) (Or.inr (by omega)) (by omega)
  apply WP.seq
  apply WP.assign
  ck_simp [h.loadProof, h3p, rd_u32 hcell]
  apply WP.seq
  apply WP.assign
  ck_simp
  apply WP.seq
  apply WP.assign
  ck_simp
  have hx := hwlt (3 + p.toNat)
  generalize hxe : wordFn ws (3 + p.toNat) = x at hx
  have hcode : (BitVec.ofNat 32 x &&& 255#32).toNat = hdrCode x := by
    rw [bv_and_ff, bv_toNat_ofNat hx]; rfl
  have hvlen : ((BitVec.ofNat 32 x >>> 8) &&& 255#32).toNat = hdrVlen x := by
    rw [bv_and_ff, bv_shr_8, bv_toNat_ofNat hx]; rfl
  generalize BitVec.ofNat 32 x &&& 255#32 = codev at hcode ⊢
  generalize (BitVec.ofNat 32 x >>> 8) &&& 255#32 = vlenv at hvlen ⊢
  -- if (vlen > ne - p - 1) return 0;
  apply WP.ifRet
  ck_simp
  have hsub : (BitVec.ofNat 32 (wordFn ws 1) - p - 1#32).toNat = wordFn ws 1 - p.toNat - 1 := by
    have e1 : (BitVec.ofNat 32 (wordFn ws 1) - p).toNat = wordFn ws 1 - p.toNat := by
      rw [bv_sub_toNat (by rw [hne1]; omega), hne1]
    rw [bv_sub_toNat (by rw [e1]; simp; omega), e1]; simp
  refine ⟨fun _ => ⟨rfl, c, h, Or.inl rfl⟩, fun hle => ?_⟩
  have hfit : p.toNat + 1 + hdrVlen x ≤ wordFn ws 1 := by
    rw [BitVec.le_def, hsub, hvlen] at hle; omega
  have hvl256 : hdrVlen x < 256 := by unfold hdrVlen; omega
  have h2v : (2#32 + vlenv).toNat = 2 + hdrVlen x := by
    rw [bv_add_toNat] <;> simp [hvlen] <;> omega
  -- ok = ck_room(st, 2 + vlen); if (ok == 0) return 0;
  apply WP.seq
  apply WP.call (ck_room_spec W sb c (posOfW (wordFn ws)) st (2#32 + vlenv))
  ck_simp
  refine ⟨⟨h, hl.core⟩, ?_⟩
  clear h
  intro rv s3 c1 h hf1 hinv1 hpl hres
  rcases hres with rfl | ⟨rfl, hroom⟩
  · ck_simp
    apply WP.ifRet
    ck_simp
    exact ⟨rfl, c1, h, Or.inl rfl⟩
  ck_simp
  apply WP.ifRet
  ck_simp
  have hl1 := hl.frame hf1 hinv1
  have hroom' : c1.k.plen.toNat + 2 + hdrVlen x ≤ c1.k.pcap.toNat := by
    rw [hvlen] at hroom; rw [hpl]; omega
  obtain ⟨pb, hpool⟩ := hinv1.poolPtr_of_pcap h (by omega)
  have hpsz := hinv1.poolSize pb 0 hpool
  have hpmax := hinv1.poolCap.2
  simp only [maxPool] at hpmax
  apply WP.seq
  refine WP.mono (Q := LoadMid W sb ws n c1 st pm p (BitVec.ofNat 32 x) codev vlenv id 1#32) ?_ ?_
  · have hplen1 : (c1.k.plen + 1#32).toNat = c1.k.plen.toNat + 1 := by
      rw [bv_add_toNat] <;> simp <;> omega
    have hxv : (BitVec.ofNat 32 x).toNat = x := bv_toNat_ofNat hx
    apply WP.ite
    ck_simp
    have e24 : codev = 24#32 ↔ hdrCode x = 0x18 := by rw [← BitVec.toNat_inj, hcode]; rfl
    have e25 : codev = 25#32 ↔ hdrCode x = 0x19 := by rw [← BitVec.toNat_inj, hcode]; rfl
    simp only [e24, e25]
    by_cases hv : VarHdr x
    · -- a variable: the header with arity 1, then the position
      have hif : (if hdrCode x = 24 then some (Val.u32 1#32)
          else some (Val.u32 (if hdrCode x = 25 then 1#32 else 0#32))) = some (.u32 1#32) := by
        rcases hv with e | e <;> simp [e]
      simp only [hif]
      refine ⟨fun _ => ?_, fun e => absurd e (by decide)⟩
      apply WP.ifRet
      ck_simp
      by_cases hz : hdrVlen x ≠ 0
      · have : vlenv ≠ 0#32 := fun e => hz (by rw [← hvlen, e]; rfl)
        exact ⟨fun _ => ⟨rfl, c1, h⟩, fun e => absurd e this⟩
      replace hz : hdrVlen x = 0 := by omega
      have hz' : vlenv = 0#32 := BitVec.eq_of_toNat_eq (by rw [hvlen, hz]; rfl)
      refine ⟨fun e => absurd hz' e, fun _ => ?_⟩
      apply WP.seq
      apply WP.ck_store .pool h (by rfl) hpool
      ck_simp [hpool]
      refine ⟨by omega, ?_⟩
      clear h
      intro s4 h
      apply WP.ck_store .pool h (by rfl) hpool
      ck_simp [hpool, hplen1]
      refine ⟨by omega, ?_⟩
      clear h
      intro s5 h
      have h : Holds W s5.mem sb (wr (wr c1 c1.k.plen.toNat (BitVec.ofNat 32 x ||| 256#32))
        (c1.k.plen.toNat + 1) p) := h
      have hx8 : (BitVec.ofNat 32 x).toNat / 256 % 256 = 0 := by rw [hxv]; exact hz
      refine ⟨i, a, _, rfl, h, TailEq.wr2 (Nat.le_refl _) (by omega), ?_⟩
      refine LoadWritten.of_hdr hxe ?_ ?_ ?_ (fun _ => hz) (fun hnv => absurd hv hnv)
      · show U (wr (wr c1 _ _) _ _).pool c1.k.plen.toNat _
        rw [ldHdr_var hv]
        exact U_wr_ne (U_wr_self (by omega) (by rw [bv_or_256 hx8, hxv])) (by omega)
      · intro k hk
        rw [ldLen_var hv] at hk
        have : k = 0 := by omega
        subst this
        rw [ldArg_var hxe hv]
        show U (wr (wr c1 _ _) _ _).pool (c1.k.plen.toNat + 1) _
        exact U_wr_self (by simp; omega) (bv_ofNat_toNat p).symm
      · show c1.k.plen.toNat + 1 + ldLen x ≤ c1.k.pcap.toNat
        rw [ldLen_var hv]; omega
    · have hv' : ¬ (hdrCode x = 0x18 ∨ hdrCode x = 0x19) := hv
      have hif : (if hdrCode x = 24 then some (Val.u32 1#32)
          else some (Val.u32 (if hdrCode x = 25 then 1#32 else 0#32))) = some (.u32 0#32) := by
        simp [show hdrCode x ≠ 24 by omega, show hdrCode x ≠ 25 by omega]
      simp only [hif]
      refine ⟨fun e => by simp at e, fun _ => ?_⟩
      apply WP.ite
      ck_simp
      have e8 : codev = 8#32 ↔ hdrCode x = 0x08 := by rw [← BitVec.toNat_inj, hcode]; rfl
      simp only [e8]
      have hpl3 : p.toNat + 3 + hdrVlen x ≤ ws.size := by omega
      by_cases h8 : hdrCode x = 0x08
      · -- a literal: copy the value words
        simp only [h8, ↓reduceIte]
        refine ⟨fun _ => ?_, fun e => absurd e (by decide)⟩
        apply WP.seq
        apply WP.ck_store .pool h (by rfl) hpool
        ck_simp [hpool]
        refine ⟨by omega, ?_⟩
        clear h
        intro s4 h
        have h : Holds W s4.mem sb (wr c1 c1.k.plen.toNat (BitVec.ofNat 32 x)) := h
        apply WP.seq
        apply WP.assign
        ck_simp
        apply WP.while (I := ValInv W sb ws n c1 p (BitVec.ofNat 32 x) codev vlenv a id 1#32 x)
        · exact ⟨0#32, _, rfl, by simp, h, TailEq.wr (Nat.le_refl _), U_wr_self (by omega) rfl,
            fun k hk => absurd hk (by simp)⟩
        clear h
        rintro env s5 ⟨i2, c2, rfl, hile, h, ht, hu, hargs⟩
        have hk2 := ht.k
        ck_simp [ldEnv]
        constructor
        · intro hge
          have hie : i2.toNat = hdrVlen x := by
            have : hdrVlen x ≤ i2.toNat := by rw [BitVec.le_def, hvlen] at hge; exact hge
            omega
          refine ⟨i2, a, c2, rfl, h, ht, LoadWritten.of_hdr hxe ?_ ?_ ?_ (fun e => absurd e hv)
            (fun _ e => absurd h8 e)⟩
          · rw [ldHdr_nvar hv, hk2]; exact hu
          · intro k hk
            rw [ldLen_nvar hv] at hk
            rw [ldArg_val hxe hv h8, hk2]
            exact hargs k (by omega)
          · rw [ldLen_nvar hv, hk2]; omega
        · intro hlt2
          have hlt2' : i2.toNat < hdrVlen x := by rw [BitVec.lt_def, hvlen] at hlt2; exact hlt2
          have hpool2 : c2.k.pool = some (pb, 0) := by rw [hk2]; exact hpool
          have hsz2 : c2.pool.size = c1.pool.size := ht.size
          have hidx1 : (c2.k.plen + 1#32 + i2).toNat = c1.k.plen.toNat + 1 + i2.toNat := by
            rw [hk2, bv_add_toNat, bv_add_toNat] <;> simp <;> omega
          have hidx2 : (4#32 + p + i2).toNat = 4 + p.toNat + i2.toNat := by
            rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
          have hcell2 : U c2.proof (4 + p.toNat + i2.toNat) (wordFn ws (4 + p.toNat + i2.toNat)) := by
            rw [ht.proof]; exact hl1.rest _ (Or.inr (by omega)) (by omega)
          apply WP.seq
          apply WP.ck_store .pool h (by rfl) hpool2
          ck_simp [hpool2, h.loadProof, hidx1, hidx2, rd_u32 hcell2]
          refine ⟨by omega, ?_⟩
          clear h
          intro s6 h
          have h : Holds W s6.mem sb (wr c2 (c1.k.plen.toNat + 1 + i2.toNat)
            (BitVec.ofNat 32 (wordFn ws (4 + p.toNat + i2.toNat)))) := h
          apply WP.assign
          ck_simp
          have hi1 : (i2 + 1#32).toNat = i2.toNat + 1 := by
            rw [bv_add_toNat] <;> simp <;> omega
          refine ⟨i2 + 1#32, _, rfl, by omega, h, ht.trans (TailEq.wr (by rw [hk2]; omega)),
            U_wr_ne hu (by omega), ?_⟩
          intro k hk
          rw [hi1] at hk
          by_cases hki : k < i2.toNat
          · exact U_wr_ne (hargs k hki) (by omega)
          · have : k = i2.toNat := by omega
            subst this
            exact U_wr_self (by omega) rfl
      · -- an inner node: translate the argument positions
        simp only [h8, ↓reduceIte]
        refine ⟨fun e => by simp at e, fun _ => ?_⟩
        apply WP.seq
        apply WP.ck_store .pool h (by rfl) hpool
        ck_simp [hpool]
        refine ⟨by omega, ?_⟩
        clear h
        intro s4 h
        have h : Holds W s4.mem sb (wr c1 c1.k.plen.toNat (BitVec.ofNat 32 x)) := h
        apply WP.seq
        apply WP.assign
        ck_simp
        apply WP.while (I := RefInv W sb ws n c1 st pm p (BitVec.ofNat 32 x) codev vlenv id 1#32 x)
        · exact ⟨0#32, a, _, rfl, by simp, h, TailEq.wr (Nat.le_refl _), U_wr_self (by omega) rfl,
            fun k hk => absurd hk (by simp)⟩
        clear h
        rintro env s5 ⟨i2, a2, c2, rfl, hile, h, ht, hu, hargs⟩
        have hk2 := ht.k
        ck_simp [ldEnv]
        constructor
        · intro hge
          have hie : i2.toNat = hdrVlen x := by
            have : hdrVlen x ≤ i2.toNat := by rw [BitVec.le_def, hvlen] at hge; exact hge
            omega
          refine ⟨i2, a2, c2, rfl, h, ht, LoadWritten.of_hdr hxe ?_ ?_ ?_ (fun e => absurd e hv) ?_⟩
          · rw [ldHdr_nvar hv, hk2]; exact hu
          · intro k hk
            rw [ldLen_nvar hv] at hk
            obtain ⟨_, j, hj, _, hu'⟩ := hargs k (by omega)
            rw [ldArg_ref hxe hv h8 hj, hk2]
            exact hu'
          · rw [ldLen_nvar hv, hk2]; omega
          · intro _ _ k hk
            obtain ⟨hlt, j, hj, hjl, _⟩ := hargs k (by omega)
            exact ⟨hlt, j, hj, hjl⟩
        · intro hlt2
          have hlt2' : i2.toNat < hdrVlen x := by rw [BitVec.lt_def, hvlen] at hlt2; exact hlt2
          have hpool2 : c2.k.pool = some (pb, 0) := by rw [hk2]; exact hpool
          have hsz2 : c2.pool.size = c1.pool.size := ht.size
          have hidx1 : (c2.k.plen + 1#32 + i2).toNat = c1.k.plen.toNat + 1 + i2.toNat := by
            rw [hk2, bv_add_toNat, bv_add_toNat] <;> simp <;> omega
          have hidx2 : (4#32 + p + i2).toNat = 4 + p.toNat + i2.toNat := by
            rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
          have hcell2 : U c2.proof (4 + p.toNat + i2.toNat) (wordFn ws (4 + p.toNat + i2.toNat)) := by
            rw [ht.proof]; exact hl1.rest _ (Or.inr (by omega)) (by omega)
          -- a = proof[4 + p + i]; if (a >= p) return 0;
          apply WP.seq
          apply WP.assign
          ck_simp [h.loadProof, hidx2, rd_u32 hcell2]
          have hav := hwlt (4 + p.toNat + i2.toNat)
          generalize hae : wordFn ws (4 + p.toNat + i2.toNat) = av at hav
          have hav' : (BitVec.ofNat 32 av).toNat = av := bv_toNat_ofNat hav
          apply WP.ifRet
          ck_simp
          refine ⟨fun _ => ⟨rfl, c2, h⟩, fun halt => ?_⟩
          have halt' : av < p.toNat := by rw [BitVec.lt_def, hav'] at halt; exact halt
          obtain ⟨hcellA, _, hz, hsome⟩ := hl1.ref halt'
          have hcellA2 : U c2.proof (3 + av) (mapW st.pool pm av) := by rw [ht.proof]; exact hcellA
          have hidx3 : (3#32 + BitVec.ofNat 32 av).toNat = 3 + av := by
            rw [bv_add_toNat] <;> simp [hav'] <;> omega
          -- if (proof[3 + a] == 0) return 0;
          apply WP.ifRet
          ck_simp [h.loadProof, hidx3, rd_u32 hcellA2]
          cases hpa : pm av with
          | none =>
            have h0 : mapW st.pool pm av = 0 := hz.2 hpa
            rw [h0]
            exact ⟨fun _ => ⟨rfl, c2, h⟩, fun e => by simp at e⟩
          | some j =>
            obtain ⟨hjl, hmj⟩ := hsome j hpa
            have hoffj := hl1.off_lt hjl
            have hcellJ : U c2.proof (3 + av) (offs st.pool j + 1) := by rw [← hmj]; exact hcellA2
            rw [hmj]
            have hne0 : BitVec.ofNat 32 (offs st.pool j + 1) ≠ 0#32 := by
              intro e; have := congrArg BitVec.toNat e
              rw [bv_toNat_ofNat (by omega)] at this; simp at this
            refine ⟨fun e => absurd e hne0, fun _ => ?_⟩
            have hsub1 : BitVec.ofNat 32 (offs st.pool j + 1) - 1#32 = BitVec.ofNat 32 (offs st.pool j) := by
              apply BitVec.eq_of_toNat_eq
              have e1 : (BitVec.ofNat 32 (offs st.pool j + 1)).toNat = offs st.pool j + 1 :=
                bv_toNat_ofNat (by omega)
              rw [bv_sub_toNat (by rw [e1]; simp), e1]
              simp; omega
            apply WP.seq
            apply WP.ck_store .pool h (by rfl) hpool2
            ck_simp [hpool2, hidx1, h.loadProof, hidx3, rd_u32 hcellJ, hsub1]
            refine ⟨by omega, ?_⟩
            clear h
            intro s6 h
            have h : Holds W s6.mem sb (wr c2 (c1.k.plen.toNat + 1 + i2.toNat)
              (BitVec.ofNat 32 (offs st.pool j))) := h
            apply WP.assign
            ck_simp
            have hi1 : (i2 + 1#32).toNat = i2.toNat + 1 := by
              rw [bv_add_toNat] <;> simp <;> omega
            refine ⟨i2 + 1#32, _, _, rfl, by omega, h, ht.trans (TailEq.wr (by rw [hk2]; omega)),
              U_wr_ne hu (by omega), ?_⟩
            intro k hk
            rw [hi1] at hk
            by_cases hki : k < i2.toNat
            · obtain ⟨hlt, j', hj', hjl', hu'⟩ := hargs k hki
              exact ⟨hlt, j', hj', hjl', U_wr_ne hu' (by omega)⟩
            · have : k = i2.toNat := by omega
              subst this
              rw [hae]
              exact ⟨halt', j, hpa, hjl, U_wr_self (by omega) rfl⟩
  · intro o env' s' hq
    cases o with
    | brk => exact hq.elim
    | ret rv =>
      obtain ⟨rfl, c', h'⟩ := hq
      exact ⟨rfl, c', h', Or.inl rfl⟩
    | normal =>
      obtain ⟨i2, a2, c2, rfl, h, ht, hW⟩ := hq
      dsimp only
      have hp32 : p.toNat < 2 ^ 32 := p.isLt
      have hinv2 := hinv1.tailEq ht
      have hcand := hW.candRaw hwlt hl.pos hp32
      have hspec : FnSpec (State := State) Vbcf.prog "ck_intern"
          (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c2 ∧
            CoreInv (posOfW (wordFn ws)) c2 st ∧ CandRaw (posOfW (wordFn ws)) c2 st)
          (fun _ _ => InternPostD W sb c2 (posOfW (wordFn ws)) st) :=
        ck_intern_dspec W sb c2 (posOfW (wordFn ws)) st
      -- id = ck_intern(st); if (id == NOID) return 0;
      apply WP.seq
      apply WP.call hspec
      ck_simp [ldEnv]
      refine ⟨⟨h, hinv2, hcand⟩, ?_⟩
      clear h
      rintro rv s6 ⟨c3, r, rfl, h, hf3, hres⟩
      ck_simp
      apply WP.ifRet
      ck_simp
      rcases hres with ⟨rfl, -⟩ | ⟨st', ri, ⟨nd, -, hint⟩, hinv3, hr, hrne⟩
      · exact ⟨fun _ => ⟨rfl, c3, h, Or.inl rfl⟩, fun e => absurd rfl e⟩
      have hrne' : ¬ r = 4294967295#32 := hrne
      refine ⟨fun e => absurd e hrne', fun _ => ?_⟩
      have hoffr : offs st'.pool ri < 2 ^ 30 := hinv3.off_lt hint.lt
      have hr1 : r + 1#32 = BitVec.ofNat 32 (offs st'.pool ri + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [bv_add_toNat (by simp; omega), hr,
          bv_toNat_ofNat (show offs st'.pool ri + 1 < 2 ^ 32 by omega)]; rfl
      have hf13 : PoolFrame c c3 := hf1.trans (ht.poolFrame.trans hf3)
      have hpsz3 : c3.proof.size = ws.size := by rw [hf13.proof]; exact hl.proofSize
      -- proof[3 + p] = id + 1;
      apply WP.seq
      apply WP.ck_storeProof h (by rfl)
      ck_simp [h3p, hr1]
      refine ⟨by omega, ?_⟩
      clear h
      intro s7 h
      -- i = 0; while (i < vlen) { proof[4 + p + i] = 0; i = i + 1; }
      apply WP.seq
      apply WP.assign
      ck_simp
      apply WP.seq
      apply WP.while (I := ZeroInv W sb ws n c3 p (BitVec.ofNat 32 x) codev vlenv a2 r 1#32
        (hdrVlen x) (offs st'.pool ri + 1))
      · exact ⟨0#32, _, rfl, by simp, h, ProofOut.init (by omega)⟩
      clear h
      rintro env s8 ⟨i3, P', rfl, hile, h, hP⟩
      ck_simp [ldEnv]
      constructor
      · intro hge
        have hie : i3.toNat = hdrVlen x := by
          have : hdrVlen x ≤ i3.toNat := by rw [BitVec.le_def, hvlen] at hge; exact hge
          omega
        -- p = p + 1 + vlen;
        apply WP.assign
        ck_simp
        have hpn : (p + 1#32 + vlenv).toNat = p.toNat + 1 + hdrVlen (wordFn ws (3 + p.toNat)) := by
          rw [hxe, bv_add_toNat, bv_add_toNat] <;> simp [hvlen] <;> omega
        refine ⟨p + 1#32 + vlenv, _, _, _, _, _, _, _, _, d + 1, st', pmSet pm p.toNat ri, rfl, h, ?_⟩
        rw [hpn]
        rw [hie] at hP
        exact hl.step hint (by rw [hxe]; exact hfit) hf13 hinv3 (by rw [hxe]; exact hP)
      · intro hlt3
        have hlt3' : i3.toNat < hdrVlen x := by rw [BitVec.lt_def, hvlen] at hlt3; exact hlt3
        have hidx4 : (4#32 + p + i3).toNat = 4 + p.toNat + i3.toNat := by
          rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
        apply WP.seq
        apply WP.ck_storeProof h (by rfl)
        ck_simp [hidx4]
        refine ⟨by rw [hP.size]; omega, ?_⟩
        clear h
        intro s9 h
        apply WP.assign
        ck_simp
        have hi1 : (i3 + 1#32).toNat = i3.toNat + 1 := by
          rw [bv_add_toNat] <;> simp <;> omega
        refine ⟨i3 + 1#32, _, rfl, by omega, h, ?_⟩
        rw [hi1]
        exact hP.step (by omega)

end Vbcf.Proof
