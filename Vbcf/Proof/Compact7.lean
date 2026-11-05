import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact6

/-!
# Vbcf proofs: `ck_compact`, part 7 — the worklist loop

```
while (st->sp > 0) {
  st->sp = st->sp - 1;
  o = st->stk[st->sp];
  hdr = st->pool[o];
  code = hdr & 0xff;
  if (code != BV_VAR && code != BOOL_VAR && code != BV_VAL && code != BOOL_VAL) {
    ar = (hdr >> 8) & 0xff;
    if (plen - o - 1 < ar) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
    i = 0;
    while (i < ar) {
      c = st->pool[o + 1 + i];
      if (c >= lo && c < o) {
        if (fw[c - lo] == 0) {
          fw[c - lo] = NOID;
          ok = push(st, c);
          if (ok == 0) { kvfree(fw); return 0; }
        }
      }
      i = i + 1;
    }
  }
}
```
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The inner loop of the worklist loop. -/
def cpMarkInner : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "i") (EmbC.Expr.var "ar"))
    (EmbC.Stmt.seq
      (EmbC.Stmt.assign
        "c"
        (EmbC.Expr.index
          (EmbC.Expr.field (EmbC.Expr.var "st") "pool")
          (EmbC.Expr.bin
            (EmbC.BinOp.add)
            (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "o") (EmbC.Expr.lit32 0x00000001#32))
            (EmbC.Expr.var "i"))))
      (EmbC.Stmt.seq
        (EmbC.Stmt.ite
          (EmbC.Expr.land
            (EmbC.Expr.bin (EmbC.BinOp.ge) (EmbC.Expr.var "c") (EmbC.Expr.var "lo"))
            (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "c") (EmbC.Expr.var "o")))
          (EmbC.Stmt.ite
            (EmbC.Expr.bin
              (EmbC.BinOp.eq)
              (EmbC.Expr.index
                (EmbC.Expr.var "fw")
                (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "c") (EmbC.Expr.var "lo")))
              (EmbC.Expr.lit32 0x00000000#32))
            (EmbC.Stmt.seq
              (EmbC.Stmt.store
                (EmbC.Expr.var "fw")
                (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "c") (EmbC.Expr.var "lo"))
                (EmbC.Expr.named "NOID" 0xffffffff#32))
              (EmbC.Stmt.seq
                (EmbC.Stmt.call (some "ok") "push" [EmbC.Expr.var "st", EmbC.Expr.var "c"])
                (EmbC.Stmt.ite
                  (EmbC.Expr.bin (EmbC.BinOp.eq) (EmbC.Expr.var "ok") (EmbC.Expr.lit32 0x00000000#32))
                  (EmbC.Stmt.seq
                    (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
                    (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32))))
                  (EmbC.Stmt.skip))))
            (EmbC.Stmt.skip))
          (EmbC.Stmt.skip))
        (EmbC.Stmt.assign
          "i"
          (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "i") (EmbC.Expr.lit32 0x00000001#32)))))

/-- The invariant of the worklist loop. -/
def MarkLoopInv (W : World) (sb fb : Nat) (c0 : CMem) (S : VSt) (nL : Nat) (n : BitVec 32) :
    Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c : CMem) (fw : Array EmbC.Val) (r o hdr code ar i cc ok : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r o hdr code ar i cc 0 0 ok .null 0 ∧
    Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb c ∧ MarkInv S.cs nL c0 c fw (fun _ => False) ∧
    RootsUpTo c0 S nL fw c0.k.flen.toNat

/-- The invariant of the inner loop, expanding node `y` (an inner node `nd`). -/
def MarkInnerInv (W : World) (sb fb : Nat) (c0 : CMem) (S : VSt) (nL : Nat) (n : BitVec 32)
    (y : Nat) (nd : Node) : Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c : CMem) (fw : Array EmbC.Val) (r i cc ok : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r (BitVec.ofNat 32 (offs S.cs.pool y))
      (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op)) (BitVec.ofNat 32 nd.args.size) i cc
      0 0 ok .null 0 ∧
    Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb c ∧ MarkInv S.cs nL c0 c fw (fun z => z = y) ∧
    RootsUpTo c0 S nL fw c0.k.flen.toNat ∧ i.toNat ≤ nd.args.size ∧
    ∀ k a, k < i.toNat → nd.args[k]? = some a → nL ≤ a → Mk S.cs.pool nL fw a

/-- `i = i + 1` at the end of the inner body. -/
theorem mark_inner_next {W : World} {sb fb : Nat} {c0 : CMem} {S : VSt} {nL : Nat} {n : BitVec 32}
    {y : Nat} {nd : Node} {Q : (Post prog State)} {s : (KernelState prog State)} {c : CMem} {fw : Array EmbC.Val} {r i cc ok : BitVec 32}
    (h : Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb c) (hM : MarkInv S.cs nL c0 c fw (fun z => z = y))
    (hR : RootsUpTo c0 S nL fw c0.k.flen.toNat) (hi : i.toNat < nd.args.size)
    (hsz : nd.args.size < 256)
    (hk : ∀ k a, k < i.toNat + 1 → nd.args[k]? = some a → nL ≤ a → Mk S.cs.pool nL fw a) :
    WP prog (.assign "i" (.bin .add (.var "i") (.lit32 1#32)))
      (fun o env' st' => match o with
        | .normal => MarkInnerInv W sb fb c0 S nL n y nd env' st'
        | .brk => Q .normal env' st'
        | .ret r => Q (.ret r) env' st')
      (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r (BitVec.ofNat 32 (offs S.cs.pool y))
        (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op)) (BitVec.ofNat 32 nd.args.size) i cc
        0 0 ok .null 0) s := by
  apply WP.assign
  embc_simp [cpEnv]
  have h1 : (i + 1#32).toNat = i.toNat + 1 := bv_add_toNat (by simp; omega)
  exact ⟨c, fw, r, i + 1#32, cc, ok, rfl, h, hM, hR, by omega, by rw [h1]; exact hk⟩

/-- The inner loop: every child at or above `nL` of the expanded node gets marked. -/
theorem mark_inner {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 : CMem} {fb : Nat} {n : BitVec 32}
    (hS : SInv W ws X c0 S off rest) (hW : W.aux fb = none)
    {y : Nat} {nd : Node} (hnd : S.cs.pool[y]? = some nd) (hl : ¬ IsLeaf nd.op)
    {Q : (Post prog State)} (hQ : ∀ e s', CpRet W sb ws X S off rest 0#32 s' → Q (.ret (some (.u32 0#32))) e s')
    (hexit : ∀ (s : (KernelState prog State)) (c : CMem) (fw : Array EmbC.Val) (r cc ok : BitVec 32),
      Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb c → MarkInv S.cs X.nL c0 c fw (fun z => z = y) →
      RootsUpTo c0 S X.nL fw c0.k.flen.toNat →
      (∀ k a, k < nd.args.size → nd.args[k]? = some a → X.nL ≤ a → Mk S.cs.pool X.nL fw a) →
      Q .normal (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r
        (BitVec.ofNat 32 (offs S.cs.pool y)) (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op))
        (BitVec.ofNat 32 nd.args.size) (BitVec.ofNat 32 nd.args.size) cc 0 0 ok .null 0) s)
    {env : Env} {s : (KernelState prog State)} (h0 : MarkInnerInv W sb fb c0 S X.nL n y nd env s) :
    WP prog cpMarkInner Q env s := by
  have hs := prog_ck
  have hcore := hS.inv.core.cinv
  have hok := hcore.ok
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hlo := hS.lo
  have hplen := hrep.len
  obtain ⟨pb, hpb⟩ := hS.inv.poolPtr
  have hys := lt_size_of_getElem? hnd
  have hfit := hrep.fits y nd hnd
  have hsz : nd.args.size < 256 := by
    have := hfit.2.2.1; rw [tailLen_of_not_leaf hl] at this; exact this
  have hend := hrep.node_end hnd
  rw [nodeSize_of_not_leaf hl] at hend
  have hP32 := c0.k.plen.isLt
  unfold cpMarkInner
  apply WP.while (MarkInnerInv W sb fb c0 S X.nL n y nd) h0
  rintro env s ⟨c, fw, r, i, cc, ok, rfl, h, hM, hR, hi, hk⟩
  have hfr := hM.fr
  have hpb' : c.k.pool = some (pb, 0) := by rw [hfr.poolPtr]; exact hpb
  embc_simp [cpEnv]
  have hsz32 : nd.args.size < 2 ^ 32 := by omega
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- done
    have hie : i = BitVec.ofNat 32 nd.args.size := by
      rw [BitVec.le_def, bv_toNat_ofNat hsz32] at hge
      apply BitVec.eq_of_toNat_eq; rw [bv_toNat_ofNat hsz32]; omega
    subst hie
    rw [bv_toNat_ofNat hsz32] at hk
    exact hexit s c fw r cc ok h hM hR hk
  · have hil : i.toNat < nd.args.size := by
      rw [BitVec.lt_def, bv_toNat_ofNat hsz32] at hlt; simpa using hlt
    have ha := hrep.arg hnd hl hil
    have hoy := offs_lt_end hys
    have hidx : (BitVec.ofNat 32 (offs S.cs.pool y) + 1#32 + i).toNat = offs S.cs.pool y + 1 + i.toNat := by
      rw [bv_add_toNat (by rw [bv_add_toNat (by simp; omega)]; simp [bv_toNat_ofNat (show offs S.cs.pool y < 2 ^ 32 by omega)]; omega),
        bv_add_toNat (by simp; omega)]
      simp [bv_toNat_ofNat (show offs S.cs.pool y < 2 ^ 32 by omega)]
    obtain ⟨a, haeq⟩ : ∃ a, nd.args[i.toNat]? = some a := ⟨_, Array.getElem?_eq_getElem hil⟩
    have hai : nd.args[i.toNat] = a := by
      rw [Array.getElem?_eq_getElem hil] at haeq; exact Option.some.inj haeq
    rw [hai] at ha
    have hay : a < y := hok.args_lt hnd a (by rw [← hai]; exact Array.getElem_mem hil)
    have has : a < S.cs.pool.size := by omega
    have hoa := offs_lt_of_lt hay (Nat.le_of_lt hys)
    have hoa32 : offs S.cs.pool a < 2 ^ 32 := by omega
    apply WP.seq
    apply WP.assign
    ck_simp [hpb', h.rd_pool hpb', hfr.pool, hidx, rd_u32 ha]
    apply WP.seq
    apply WP.ite
    embc_simp
    simp only [BitVec.lt_def, bv_toNat_ofNat hoa32,
      Nat.mod_eq_of_lt hoa32,
      Nat.mod_eq_of_lt (show offs S.cs.pool y < 2 ^ 32 by omega)]
    by_cases hge : X.nL ≤ a
    · have hin1 : c0.k.lo.toNat ≤ offs S.cs.pool a := by rw [hlo]; exact offs_le_of_le hge
      rw [ite_eq_right (show ¬ offs S.cs.pool a < c0.k.lo.toNat by omega), ite_eq_left hoa]
      refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
      have hk' : offs S.cs.pool a - offs S.cs.pool X.nL < fw.size := by
        rw [hM.size]; have := offs_lt_end has; omega
      have hsub : (BitVec.ofNat 32 (offs S.cs.pool a) - c0.k.lo).toNat =
          offs S.cs.pool a - offs S.cs.pool X.nL := by
        rw [bv_sub_toNat (by rw [bv_toNat_ofNat hoa32]; omega), bv_toNat_ofNat hoa32, hlo]
      apply WP.ite
      embc_simp [h.rd_aux, hsub]
      rcases hM.cells _ hk' with hz | hnn
      · simp only [rd_u32 hz]
        refine ⟨fun _ => ?_, fun hne => absurd hne (by simp)⟩
        apply WP.seq
        apply WP.aux_store h rfl
        embc_simp [hsub]
        refine ⟨hk', fun s1 h1 => ?_⟩
        clear h
        have h := h1
        apply WP.seq
        apply WP.call (push_spec _ sb c (BitVec.ofNat 32 (offs S.cs.pool a)))
        embc_simp
        refine ⟨⟨h, hM.stk⟩, ?_⟩
        intro rv s2 c2 h2 hok2 hfr2 hpre2 hcase
        rcases hcase with ⟨rfl, hsp2⟩ | ⟨rfl, hsp2, htop⟩
        · embc_simp
          apply WP.ite
          embc_simp
          refine WP.cp_fail (ws := ws) (X := X) (st := S) (off := off) (rest := rest)
            (fun e s' h => ?_) h2 hW
          exact hQ e s' h
        · embc_simp
          apply WP.ite
          embc_simp
          apply WP.skip
          have hspn : c2.k.sp.toNat = c.k.sp.toNat + 1 := by
            have h1' := hok2.cap
            have h2' := hM.stk.cap
            simp only [maxPool] at h1' h2'
            rw [hsp2, BitVec.toNat_add]; simp; omega
          have hM2 := hM.push hge has hk' hok2 hfr2 hpre2 hspn htop
          refine mark_inner_next h2 hM2 (fun j' f' hj' hL' hge' => (hR j' f' hj' hL' hge').set hk')
            hil hsz ?_
          intro k b hkb hb hgeb
          rcases Nat.lt_or_ge k i.toNat with hk'' | hk''
          · exact (hk k b hk'' hb hgeb).set hk'
          · have : k = i.toNat := by omega
            subst this
            rw [haeq] at hb; cases hb
            exact Mk.set_self hk'
      · have hn0 : ¬ (BitVec.ofNat 32 noidN = 0#32) := by decide
        simp only [rd_u32 hnn]
        refine ⟨fun h0 => absurd h0 (by simp [hn0]), fun _ => ?_⟩
        apply WP.skip
        refine mark_inner_next h hM hR hil hsz ?_
        intro k b hkb hb hgeb
        rcases Nat.lt_or_ge k i.toNat with hk'' | hk''
        · exact hk k b hk'' hb hgeb
        · have : k = i.toNat := by omega
          subst this
          rw [haeq] at hb; cases hb
          exact hnn
    · have hlow : offs S.cs.pool a < c0.k.lo.toNat := by
        rw [hlo]; exact offs_lt_of_lt (Nat.lt_of_not_le hge) hnL
      rw [ite_eq_left hlow]
      refine ⟨fun hc => absurd rfl hc, fun _ => ?_⟩
      apply WP.skip
      refine mark_inner_next h hM hR hil hsz ?_
      intro k b hkb hb hgeb
      rcases Nat.lt_or_ge k i.toNat with hk'' | hk''
      · exact hk k b hk'' hb hgeb
      · have : k = i.toNat := by omega
        subst this
        rw [haeq] at hb; cases hb
        exact absurd hgeb hge

theorem cp_mark {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 : CMem} {fb : Nat} {n : BitVec 32}
    (hS : SInv W ws X c0 S off rest) (hW : W.aux fb = none)
    {rest' : Stmt} {env : Env} {s : (KernelState prog State)} (h0 : MarkLoopInv W sb fb c0 S X.nL n env s)
    (K : ∀ (s' : (KernelState prog State)) (c : CMem) (fw : Array EmbC.Val) (r o hdr code ar i cc ok : BitVec 32),
      Holds (W.addAux fb ⟨.u32, fw⟩) s'.mem sb c → MarkInv S.cs X.nL c0 c fw (fun _ => False) →
      c.k.sp = 0#32 → RootsUpTo c0 S X.nL fw c0.k.flen.toNat →
      WP prog rest' (retPost (some .u32) (CpPost W sb ws X S off rest))
        (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r o hdr code ar i cc 0 0 ok .null 0) s') :
    WP prog (.seq cpMark rest') (retPost (some .u32) (CpPost W sb ws X S off rest)) env s := by
  have hs := prog_ck
  have hcore := hS.inv.core.cinv
  have hok := hcore.ok
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hplen := hrep.len
  obtain ⟨pb, hpb⟩ := hS.inv.poolPtr
  have hP32 := c0.k.plen.isLt
  unfold cpMark
  apply WP.loop_seq (MarkLoopInv W sb fb c0 S X.nL n) h0
  rintro env s ⟨c, fw, r, o, hdr, code, ar, i, cc, ok, rfl, h, hM, hR⟩
  have hfr := hM.fr
  have hpb' : c.k.pool = some (pb, 0) := by rw [hfr.poolPtr]; exact hpb
  ck_simp [cpEnv]
  refine ⟨fun hz => ?_, fun hpos => ?_⟩
  · -- the stack is empty
    exact K s c fw r o hdr code ar i cc ok h hM hz hR
  have hsp : 0 < c.k.sp.toNat := by
    rcases Nat.eq_zero_or_pos c.k.sp.toNat with e | e
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using e)) hpos
    · exact e
  obtain ⟨y, hy, hys, hyu, -⟩ := hM.onStk (c.k.sp.toNat - 1) (by omega)
  obtain ⟨nd, hnd⟩ : ∃ nd, S.cs.pool[y]? = some nd := ⟨_, Array.getElem?_eq_getElem hys⟩
  have hoy := offs_lt_end hys
  have hoy32 : offs S.cs.pool y < 2 ^ 32 := by omega
  have hscap : 0 < c.k.scap.toNat := by have := hM.stk.cap; omega
  obtain ⟨skb, hskb⟩ := hM.stk.stkPtr h hscap
  have hsp1 : (c.k.sp - 1#32).toNat = c.k.sp.toNat - 1 := by
    rw [bv_sub_toNat (by simp; omega)]; simp
  -- st->sp = st->sp - 1
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp
  intro s1 h1
  clear h
  have h := h1
  have hM1 := hM.pop hsp (by omega) hy hys hyu
  -- o = st->stk[st->sp]
  apply WP.seq
  apply WP.assign
  ck_simp [hskb, h.rd_stk hskb, hsp1, rd_u32 hyu]
  -- hdr = st->pool[o]
  have hhdr := hrep.hdr hnd
  apply WP.seq
  apply WP.assign
  ck_simp [hpb', h.rd_pool hpb', hfr.pool, bv_toNat_ofNat hoy32, rd_u32 hhdr]
  -- code = hdr & 0xff
  apply WP.seq
  apply WP.assign
  ck_simp [uv_and_ff, hdrW_mod256]
  have hfit := hrep.fits y nd hnd
  have hc32 : opC nd.op < 2 ^ 32 := opC_lt32 _
  apply WP.ite
  embc_simp
  by_cases hl : IsLeaf nd.op
  · -- a leaf: nothing to expand
    have hargs := hok.leaf_args hnd hl
    have hdone : Done S.cs.pool X.nL fw y := by
      intro m hm a ha
      rw [hnd] at hm; cases hm
      have : a ∈ nd.args := ha
      rw [Array.mem_iff_getElem] at this
      obtain ⟨k, hk, -⟩ := this
      omega
    have hM2 := hM1.finish (fun z hz => by rw [hz]; exact hdone)
    rcases leaf_code hl with e | e | e | e <;>
    · simp only [e]
      refine ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩
      apply WP.skip
      exact ⟨_, fw, r, _, _, _, ar, i, cc, ok, rfl, h, hM2, hR⟩
  · -- an inner node: expand it
    have e1 : opC nd.op ≠ 0x18 := fun e => hl (leaf_of_code (Or.inl e))
    have e2 : opC nd.op ≠ 0x19 := fun e => hl (leaf_of_code (Or.inr (Or.inl e)))
    have e3 : opC nd.op ≠ 0x08 := fun e => hl (leaf_of_code (Or.inr (Or.inr (Or.inl e))))
    have e4 : opC nd.op ≠ 0x09 := fun e => hl (leaf_of_code (Or.inr (Or.inr (Or.inr e))))
    simp only [ofNat32_inj hc32 (by decide : (24 : Nat) < 2 ^ 32), ofNat32_inj hc32 (by decide : (25 : Nat) < 2 ^ 32),
      ofNat32_inj hc32 (by decide : (8 : Nat) < 2 ^ 32), ofNat32_inj hc32 (by decide : (9 : Nat) < 2 ^ 32),
      e1, e2, e3, e4, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
    have hsz : nd.args.size < 256 := by
      have := hfit.2.2.1; rw [tailLen_of_not_leaf hl] at this; exact this
    have hend := hrep.node_end hnd
    rw [nodeSize_of_not_leaf hl] at hend
    -- ar = (hdr >> 8) & 0xff
    apply WP.seq
    apply WP.assign
    ck_simp [hdr_len_bv hfit, tailLen_of_not_leaf hl]
    -- if (plen - o - 1 < ar) …
    apply WP.seq
    apply WP.ite
    ck_simp
    have hsub : ¬ (c0.k.plen - BitVec.ofNat 32 (offs S.cs.pool y) - 1#32 <
        BitVec.ofNat 32 nd.args.size) := by
      bv_omega
    refine ⟨fun hc => absurd hc hsub, fun _ => ?_⟩
    apply WP.skip
    -- i = 0
    apply WP.seq
    apply WP.assign
    ck_simp
    -- the inner loop
    refine mark_inner hS hW hnd hl (fun e s' h => ⟨rfl, h⟩) ?_
      ⟨_, fw, r, 0#32, cc, ok, rfl, h, hM1, hR, by simp, fun k a hk => by simp at hk⟩
    intro s2 c2 fw2 r2 cc2 ok2 h2 hM2 hR2 hk2
    have hdone : Done S.cs.pool X.nL fw2 y := by
      intro m hm a ha hge
      rw [hnd] at hm; cases hm
      rw [Array.mem_iff_getElem] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      exact hk2 k _ hk (Array.getElem?_eq_getElem hk) hge
    exact ⟨_, fw2, r2, _, _, _, _, _, cc2, ok2, rfl, h2,
      hM2.finish (fun z hz => by rw [hz]; exact hdone), hR2⟩

end Vbcf.Proof
