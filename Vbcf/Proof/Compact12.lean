import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact11

/-!
# Vbcf proofs: `ck_compact`, part 12 — refilling the table

```
o = 0;
while (o < cur) {
  ok = ck_hput(st, o);
  if (ok == 0) { kvfree(fw); return 0; }
  o = o + 1 + ((st->pool[o] >> 8) & 0xff);
}
```
`ck_hput` is specified over `HView` (the struct, the pool and the table, every
other block as in a reference memory); `Holds.ofHView` returns to `Holds`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- `Holds` again after the table block (and the struct's scalars) changed over `HView`. -/
theorem Holds.ofHView {W : World} {m0 m : Mem} {sb : Nat} {c : CMem} {k : CK} {pb nb : Nat}
    {htab : Array EmbC.Val} (h : Holds W m0 sb c) (hv : HView m0 m sb k pb c.pool nb htab)
    (hhtab : c.k.htab = some (nb, 0)) (hk : k.ptr4 = c.k.ptr4) :
    Holds W m sb { c with k := k, htab := htab } := by
  simp only [CK.ptr4, List.cons.injEq, and_true] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hk
  have hptr : ∀ a, k.ptr a = c.k.ptr a := by intro a; cases a <;> simp [CK.ptr, *]
  have hsb := hv.hb_ne_sb
  have hpb : W.pb ≠ nb := by
    have := (h.arr .htab nb 0 hhtab).2.2.1; have := h.pbOld; omega
  refine ⟨hv.ck, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show m.block? W.pb = _
    rw [hv.frame W.pb h.pb_ne_sb hpb]; exact h.proof
  · show k.proof = none ∨ _
    rw [h7]; exact h.proofPtr
  · show k.par = none ∨ _
    rw [h6]; exact h.parPtr
  · intro a b o hp
    rw [hptr a] at hp
    obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a b o hp
    refine ⟨ho, hbs, hbb, ?_⟩
    by_cases ha : a = .htab
    · subst ha
      change c.k.htab = some (b, o) at hp
      rw [hhtab] at hp; cases hp
      exact hv.htab
    · have hbn : b ≠ nb := h.sep a .htab b nb o 0 ha hp hhtab
      show m.block? b = _
      rw [hv.frame b hbs hbn]
      cases a <;> first | exact absurd rfl ha | exact harr
  · intro a1 a2 b1 b2 o1 o2 hne p1 p2
    rw [hptr] at p1 p2
    exact h.sep a1 a2 b1 b2 o1 o2 hne p1 p2
  · intro b hlt hne
    have hbs : b ≠ sb := by have := h.sbNew; omega
    have hbn : b ≠ nb := by have := (h.arr .htab nb 0 hhtab).2.2.1; omega
    rw [hv.frame b hbs hbn]
    exact h.out b hlt hne
  · intro b hge hne hno
    have hbn : b ≠ nb := fun e => hno .htab 0 (by rw [hptr, e]; exact hhtab)
    rw [hv.frame b hne hbn]
    exact h.exact b hge hne (fun a o hp => hno a o (by rw [hptr a]; exact hp))
  · intro b hb'
    obtain ⟨g1, g2, g3⟩ := h.auxNew b hb'
    exact ⟨g1, g2, fun a o => by rw [hptr]; exact g3 a o⟩

/-- The invariant of the refill loop: the first `x` nodes are in the table. -/
def RefillInv (m0 : Mem) (sb fb : Nat) (c0 cR : CMem) (n : BitVec 32) (pb nb : Nat)
    (posOf : Nat → Nat) (lp : Pool) (cur nodes : BitVec 32) (hcv : BitVec 64) :
    Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (x : Nat) (htab : Array EmbC.Val) (wk j r hdr code ar i cc ok : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r (BitVec.ofNat 32 (offs lp x)) hdr code ar i cc
      cur nodes ok (.ptr nb 0) hcv ∧
    HView m0 s.mem sb { cR.k with hcnt := BitVec.ofNat 32 x, work := wk } pb cR.pool nb htab ∧
    x ≤ lp.size ∧ HtabPart posOf lp htab cR.k.hcap.toNat (fun y => y < x) ∧ nzCount htab = x

theorem cp_refill {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 cR : CMem} {fb : Nat} {n : BitVec 32} {fw : Array EmbC.Val}
    (hW : W.aux fb = none) {m0 : Mem} (hR : Holds (W.addAux fb ⟨.u32, fw⟩) m0 sb cR)
    {pb nb : Nat} (_hpb : cR.k.pool = some (pb, 0)) (hnb : cR.k.htab = some (nb, 0))
    {lp : Pool} (hrep : PoolRep X.posOf lp cR.pool (offs lp lp.size))
    (h30 : offs lp lp.size ≤ 2 ^ 30) {nodes : BitVec 32} {hcv : BitVec 64} {rest' : Stmt}
    {env : Env} {s : (KernelState prog State)}
    (h0 : RefillInv m0 sb fb c0 cR n pb nb X.posOf lp (BitVec.ofNat 32 (offs lp lp.size)) nodes hcv env s)
    (K : ∀ (s' : (KernelState prog State)) (htab : Array EmbC.Val) (wk j r hdr code ar i cc ok : BitVec 32),
      HView m0 s'.mem sb { cR.k with hcnt := BitVec.ofNat 32 lp.size, work := wk } pb cR.pool nb htab →
      HtabPart X.posOf lp htab cR.k.hcap.toNat (fun y => y < lp.size) → nzCount htab = lp.size →
      WP prog rest' (retPost (some .u32) (CpPost W sb ws X S off rest))
        (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r (BitVec.ofNat 32 (offs lp lp.size)) hdr code ar i cc
          (BitVec.ofNat 32 (offs lp lp.size)) nodes ok (.ptr nb 0) hcv) s') :
    WP prog (.seq cpRefill rest') (retPost (some .u32) (CpPost W sb ws X S off rest)) env s := by
  have hs := prog_ck
  have hend32 : offs lp lp.size < 2 ^ 32 := by omega
  unfold cpRefill
  apply WP.loop_seq (RefillInv m0 sb fb c0 cR n pb nb X.posOf lp (BitVec.ofNat 32 (offs lp lp.size))
    nodes hcv) h0
  rintro env s ⟨x, htab, wk, j, r, hdr, code, ar, i, cc, ok, rfl, h, hx, hpart, hnz⟩
  have hox := offs_le_end lp x
  have hox32 : offs lp x < 2 ^ 32 := by omega
  embc_simp [cpEnv]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hge' : offs lp lp.size ≤ offs lp x := by bv_omega
    have hxe : x = lp.size := by
      rcases Nat.lt_or_ge x lp.size with h' | h'
      · have := offs_lt_end h'; omega
      · omega
    subst hxe
    exact K s htab wk j r hdr code ar i cc ok h hpart hnz
  have hlt' : offs lp x < offs lp lp.size := by bv_omega
  have hxl : x < lp.size := by
    rcases Nat.lt_or_ge x lp.size with h' | h'
    · exact h'
    · rw [offs_of_size_le h'] at hlt'; omega
  obtain ⟨nx, hnx⟩ : ∃ nx, lp[x]? = some nx := ⟨_, Array.getElem?_eq_getElem hxl⟩
  have hfit := hrep.fits x nx hnx
  have hsucc := offs_succ hnx
  have hend := offs_node_end hnx
  apply WP.seq
  apply WP.call (ck_hput_spec m0 sb { cR.k with hcnt := BitVec.ofNat 32 x, work := wk } pb cR.pool nb
    htab X.posOf lp (offs lp lp.size) (fun y => y < x) (BitVec.ofNat 32 (offs lp x)) x nx)
  embc_simp
  refine ⟨⟨h, hrep, h30, hpart, hnx, hox32⟩, ?_⟩
  intro rv s1 hp
  rcases hp with ⟨rfl, wk', er', h1⟩ | ⟨rfl, slot, wk', hs0, hslot, h1, hpart'⟩
  · -- out of work: back to `Holds`, free `fw`, fail
    have hH := hR.ofHView h1 hnb (by rfl)
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    refine WP.cp_fail (ws := ws) (X := X) (st := S) (off := off) (rest := rest)
      (fun e s' h => ⟨rfl, h⟩) hH hW
  · embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.skip
    apply WP.assign_loop
    clear h
    have h := h1
    hv_simp [bv_toNat_ofNat hox32, rd_u32 (hrep.hdr hnx), hdr_len_bv hfit]
    have hnext : BitVec.ofNat 32 (offs lp x) + 1#32 + BitVec.ofNat 32 (tailLen nx) =
        BitVec.ofNat 32 (offs lp (x + 1)) := by
      rw [hsucc]; unfold nodeSize at hend ⊢
      apply BitVec.eq_of_toNat_eq
      have : offs lp x + 1 + tailLen nx < 2 ^ 32 := by omega
      bv_omega
    have hcnt : BitVec.ofNat 32 x + 1#32 = BitVec.ofNat 32 (x + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := size_le_offs lp
      have : x + 1 < 2 ^ 32 := by omega
      bv_omega
    have hne : EmbC.Val.u32 (BitVec.ofNat 32 (offs lp x) + 1#32) ≠ .u32 0#32 := by
      intro e
      simp only [EmbC.Val.u32.injEq] at e
      have := congrArg BitVec.toNat e
      rw [bv_add_toNat (by rw [bv_toNat_ofNat hox32]; simp; omega), bv_toNat_ofNat hox32] at this
      simp at this
    rw [hnext]
    refine ⟨x + 1, _, wk', j, r, hdr, code, _, i, cc, 1#32, rfl, ?_, by omega,
      hpart'.mono (fun y _ hy => by omega), ?_⟩
    · have : ({ { cR.k with hcnt := BitVec.ofNat 32 x, work := wk } with
          hcnt := BitVec.ofNat 32 x + 1#32, work := wk' } : CK) =
          { cR.k with hcnt := BitVec.ofNat 32 (x + 1), work := wk' } := by rw [hcnt]
      rw [← this]; exact h1
    · rw [nzCount_set hs0 hne, hnz]

/-- `kvfree(st->a); st->a = NULL;` for an owned array `a`. -/
theorem Holds.dropArr {P : Prog} {W : World} {m : Mem} {sb : Nat} {c : CMem}
    (hs : P.findStruct "ck" = some ckS) (h : Holds W m sb c) (a : Arr) {ob : Nat}
    (hp : c.k.ptr a = some (ob, 0)) :
    let m1 := m.free ob
    m.block? ob = some ⟨.u32, c.arr a⟩ ∧ HasCK m1 sb c.k ∧
    m1.storeField P sb a.field.1 .null = some (m1.setCell sb a.field.2 .null) ∧
    Holds W (m1.setCell sb a.field.2 .null) sb ({ c with k := c.k.setPtr a none }.setArr a #[]) := by
  intro m1
  obtain ⟨-, hobs, hobb, hobA⟩ := h.arr a ob 0 hp
  have hb1 : ∀ b, m1.block? b = if b = ob then none else m.block? b := fun b => Mem.block?_free b
  have hck : HasCK m1 sb c.k := by
    show m1.block? sb = _
    rw [hb1]; simp only [Ne.symm hobs, ↓reduceIte]; exact h.ck
  have hstore : m1.storeField P sb a.field.1 .null = some (m1.setCell sb a.field.2 .null) :=
    Mem.storeField_eq (by rw [ck_slot hs hck, a.field_slot]) rfl
      (by cases a <;> simp [Arr.field, CK.cells])
  refine ⟨hobA, hck, hstore, ?_⟩
  have hb : ∀ b', (m1.setCell sb a.field.2 .null).block? b' =
      if b' = sb then some ⟨.struct "ck", c.k.cells.setIfInBounds a.field.2 .null⟩
      else m1.block? b' := fun b' => by rw [Mem.block?_setCell b' hck]
  have hk : ({ c with k := c.k.setPtr a none }.setArr a #[]).k = c.k.setPtr a none := by
    cases a <;> rfl
  have hptr : ∀ a', ({ c with k := c.k.setPtr a none }.setArr a #[]).k.ptr a' =
      if a' = a then none else c.k.ptr a' := by
    intro a'; rw [hk, CK.setPtr_ptr]
  have hpbo : W.pb ≠ ob := by have := h.pbOld; omega
  refine ⟨?_, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (m1.setCell sb a.field.2 .null).block? sb = _
    rw [hb]; simp only [↓reduceIte]
    rw [hk, CK.setPtr_cells]; rfl
  · show (m1.setCell sb a.field.2 .null).block? W.pb = _
    rw [hb]; simp only [h.pb_ne_sb, ↓reduceIte]
    rw [hb1]; simp only [hpbo, ↓reduceIte]
    cases a <;> exact h.proof
  · cases a <;> exact h.proofPtr
  · cases a <;> exact h.parPtr
  · intro a' b o hpa
    rw [hptr] at hpa
    by_cases haa : a' = a
    · simp only [haa, ↓reduceIte] at hpa; cases hpa
    · simp only [haa, ↓reduceIte] at hpa
      obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a' b o hpa
      refine ⟨ho, hbs, hbb, ?_⟩
      have hbo : b ≠ ob := h.sep a' a b ob o 0 haa hpa hp
      show (m1.setCell sb a.field.2 .null).block? b = _
      rw [hb]; simp only [hbs, ↓reduceIte]
      rw [hb1]; simp only [hbo, ↓reduceIte]
      cases a <;> cases a' <;> first | exact absurd rfl haa | exact harr
  · intro a1 a2 b1 b2 o1 o2 hne h1 h2
    rw [hptr] at h1 h2
    by_cases e1 : a1 = a
    · simp only [e1, ↓reduceIte] at h1; cases h1
    · by_cases e2 : a2 = a
      · simp only [e2, ↓reduceIte] at h2; cases h2
      · simp only [e1, e2, ↓reduceIte] at h1 h2
        exact h.sep a1 a2 b1 b2 o1 o2 hne h1 h2
  · intro b hlt hne
    rw [hb]
    have h1 : b ≠ sb := by have := h.sbNew; omega
    have h2 : b ≠ ob := by omega
    simp only [h1, ↓reduceIte]
    rw [hb1]; simp only [h2, ↓reduceIte]
    exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]; simp only [hne, ↓reduceIte]
    rw [hb1]
    by_cases e : b = ob
    · subst e; simp only [↓reduceIte]; exact (h.aux_owned hp).symm
    · simp only [e, ↓reduceIte]
      refine h.exact b hge hne (fun a' o hp' => ?_)
      by_cases haa : a' = a
      · subst haa; rw [hp] at hp'; cases hp'; exact e rfl
      · exact hno a' o (by rw [hptr]; simp [haa, hp'])
  · intro b hb'
    obtain ⟨g1, g2, g3⟩ := h.auxNew b hb'
    refine ⟨g1, g2, fun a' o => ?_⟩
    rw [hptr]
    by_cases haa : a' = a
    · simp [haa]
    · simp only [haa, ↓reduceIte]; exact g3 a' o

end Vbcf.Proof
