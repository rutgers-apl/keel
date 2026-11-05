import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact7

/-!
# Vbcf proofs: `ck_compact`, part 8 — the slide, one node

`keepOf`: the nodes kept by compaction, read off the forwarding table after
marking (everything below `nL`, and the marked nodes).  During the slide the
pool cells from the current node's old offset on are the old ones, every
kept node below it has its new words at its new offset (`SlideCells`), and
the forwarding table holds the new offset of every kept node below it
(`SlideFw`).  This file proves the inner loop, which copies one node's tail
words, translating children at or above `lo` through the table.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The nodes kept by compaction. -/
noncomputable def keepOf (pool : Pool) (nL : Nat) (fw : Array EmbC.Val) (x : Nat) : Bool :=
  @decide (x < nL ∨ Mk pool nL fw x) (Classical.propDecidable _)

theorem keepOf_iff {pool : Pool} {nL : Nat} {fw : Array EmbC.Val} {x : Nat} :
    keepOf pool nL fw x = true ↔ x < nL ∨ Mk pool nL fw x := by
  unfold keepOf; exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem keepOf_low {pool : Pool} {nL : Nat} {fw : Array EmbC.Val} {x : Nat} (h : x < nL) :
    keepOf pool nL fw x = true := keepOf_iff.mpr (Or.inl h)

/-- After marking, the kept nodes are closed under children. -/
theorem MarkInv.closed {cs : St} {nL : Nat} {c0 c : CMem} {fw : Array EmbC.Val}
    (hM : MarkInv cs nL c0 c fw (fun _ => False)) (hsp : c.k.sp = 0#32)
    (hlt : ∀ (i : Nat) (n : Node), cs.pool[i]? = some n → ∀ a ∈ n.args, a < i) :
    KClosed (keepOf cs.pool nL fw) cs.pool := by
  intro x n hk hn a ha
  rw [keepOf_iff] at hk ⊢
  have hax := hlt x n hn a ha
  rcases hk with hx | hmk
  · exact Or.inl (by omega)
  · by_cases hge : nL ≤ a
    · right
      have hxs := lt_size_of_getElem? hn
      have hxnL : nL ≤ x := by omega
      rcases hM.todo x hxnL hxs hmk with ⟨p, hp, -⟩ | hd | hf
      · rw [hsp] at hp; simp at hp
      · exact hd n hn a ha hge
      · exact hf.elim
    · exact Or.inl (by omega)

/-- The pool cells during the slide, with node `x` next. -/
structure SlideCells (posOf : Nat → Nat) (pool : Pool) (keep : Nat → Bool) (old : Array EmbC.Val)
    (x : Nat) (P : Array EmbC.Val) : Prop where
  size : P.size = old.size
  above : ∀ k, offs pool x ≤ k → P[k]? = old[k]?
  kept : ∀ y nd, y < x → keep y = true → pool[y]? = some nd →
    WordsAt P (offK keep pool y) (newW posOf keep pool nd)

/-- The forwarding table during the slide, with node `x` next. -/
structure SlideFw (pool : Pool) (nL : Nat) (keep : Nat → Bool) (x : Nat) (fw : Array EmbC.Val) :
    Prop where
  size : fw.size = offs pool pool.size - offs pool nL
  cells : ∀ k, k < fw.size → ∃ w, w < 2 ^ 32 ∧ U fw k w
  node : ∀ y, nL ≤ y → y < pool.size →
    U fw (offs pool y - offs pool nL)
      (if keep y = true then (if y < x then offK keep pool y else noidN) else 0)

/-- The inner loop of the slide. -/
def cpSlideInner : Stmt :=
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
            (EmbC.Expr.land
              (EmbC.Expr.land
                (EmbC.Expr.land
                  (EmbC.Expr.land
                    (EmbC.Expr.bin
                      (EmbC.BinOp.ne)
                      (EmbC.Expr.var "code")
                      (EmbC.Expr.named "BV_VAR" 0x00000018#32))
                    (EmbC.Expr.bin
                      (EmbC.BinOp.ne)
                      (EmbC.Expr.var "code")
                      (EmbC.Expr.named "BOOL_VAR" 0x00000019#32)))
                  (EmbC.Expr.bin
                    (EmbC.BinOp.ne)
                    (EmbC.Expr.var "code")
                    (EmbC.Expr.named "BV_VAL" 0x00000008#32)))
                (EmbC.Expr.bin
                  (EmbC.BinOp.ne)
                  (EmbC.Expr.var "code")
                  (EmbC.Expr.named "BOOL_VAL" 0x00000009#32)))
              (EmbC.Expr.bin (EmbC.BinOp.ge) (EmbC.Expr.var "c") (EmbC.Expr.var "lo")))
            (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "c") (EmbC.Expr.var "o")))
          (EmbC.Stmt.assign
            "c"
            (EmbC.Expr.index
              (EmbC.Expr.var "fw")
              (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "c") (EmbC.Expr.var "lo"))))
          (EmbC.Stmt.skip))
        (EmbC.Stmt.seq
          (EmbC.Stmt.store
            (EmbC.Expr.field (EmbC.Expr.var "st") "pool")
            (EmbC.Expr.bin
              (EmbC.BinOp.add)
              (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "cur") (EmbC.Expr.lit32 0x00000001#32))
              (EmbC.Expr.var "i"))
            (EmbC.Expr.var "c"))
          (EmbC.Stmt.assign
            "i"
            (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "i") (EmbC.Expr.lit32 0x00000001#32))))))

/-! ## Stores into a word range -/

theorem WordsAt.setOut {cells : Array EmbC.Val} {base pos : Nat} {ws : List Nat} {v : EmbC.Val}
    (h : WordsAt cells base ws) (hp : pos < base ∨ base + ws.length ≤ pos) :
    WordsAt (cells.setIfInBounds pos v) base ws := by
  intro k x hx
  have := lt_length_of_getElem? hx
  unfold U
  rw [Array.getElem?_setIfInBounds_ne (by omega)]
  exact h k x hx

theorem WordsAt.setSnoc {cells : Array EmbC.Val} {base pos x : Nat} {ws : List Nat}
    (h : WordsAt cells base ws) (hp : pos = base + ws.length) (hs : pos < cells.size) :
    WordsAt (cells.setIfInBounds pos (uv x)) base (ws ++ [x]) := by
  intro k y hy
  unfold U
  rcases Nat.lt_or_ge k ws.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hy
    rw [Array.getElem?_setIfInBounds_ne (by omega)]
    exact h k y hy
  · rw [List.getElem?_append_right hge] at hy
    have hk : k - ws.length = 0 := by
      rcases Nat.lt_or_ge (k - ws.length) 1 with h1 | h1
      · omega
      · rw [List.getElem?_eq_none (by simpa using h1)] at hy; cases hy
    rw [hk] at hy
    simp at hy; subst hy
    rw [show base + k = pos by omega, Array.getElem?_setIfInBounds_self_of_lt hs]

/-- The invariant of the inner loop, copying kept node `x` (node `nd`). -/
def SlideInnerInv (W : World) (sb fb : Nat) (c0 cm : CMem) (S : VSt) (nL : Nat) (n : BitVec 32)
    (posOf : Nat → Nat) (keep : Nat → Bool) (fw : Array EmbC.Val) (x : Nat) (nd : Node)
    (r ok : BitVec 32) : Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (P : Array EmbC.Val) (i cc : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r (BitVec.ofNat 32 (offs S.cs.pool x))
      (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op)) (BitVec.ofNat 32 (tailLen nd)) i cc
      (BitVec.ofNat 32 (offK keep S.cs.pool x)) (BitVec.ofNat 32 (cntK keep x - nL)) ok .null 0 ∧
    Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb { cm with pool := P } ∧
    P.size = c0.pool.size ∧
    (∀ k, offs S.cs.pool x + 1 + i.toNat ≤ k → P[k]? = c0.pool[k]?) ∧
    (∀ y nd', y < x → keep y = true → S.cs.pool[y]? = some nd' →
      WordsAt P (offK keep S.cs.pool y) (newW posOf keep S.cs.pool nd')) ∧
    WordsAt P (offK keep S.cs.pool x) ((newW posOf keep S.cs.pool nd).take (1 + i.toNat)) ∧
    i.toNat ≤ tailLen nd

theorem newW_length (posOf : Nat → Nat) (keep : Nat → Bool) (pool : Pool) (nd : Node) :
    (newW posOf keep pool nd).length = nodeSize nd := by
  simp only [newW, List.length_cons, tailW_length, nodeSize]; omega

/-- The new word for tail position `i`. -/
theorem newW_take_succ {posOf : Nat → Nat} {keep : Nat → Bool} {pool : Pool} {nd : Node} {i : Nat}
    {t : Nat} (ht : (tailW posOf (offK keep pool) nd)[i]? = some t) :
    (newW posOf keep pool nd).take (1 + (i + 1)) = (newW posOf keep pool nd).take (1 + i) ++ [t] := by
  rw [show 1 + (i + 1) = (1 + i) + 1 by omega, List.take_add_one]
  congr
  simp only [newW]
  rw [show 1 + i = i + 1 by omega, List.getElem?_cons_succ, ht]; rfl

/-- `st->pool[cur + 1 + i] = c; i = i + 1;` with `c` the new tail word `t`. -/
theorem slide_store {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 cm : CMem} {fb : Nat} {n : BitVec 32}
    (hS : SInv W ws X c0 S off rest) (hfr : StkFrame c0 cm)
    {keep : Nat → Bool} {fw : Array EmbC.Val} {x : Nat} {nd : Node}
    (hnd : S.cs.pool[x]? = some nd) (_hkx : keep x = true) {r ok : BitVec 32} {I : Env → (KernelState prog State) → Prop}
    {Q : (Post prog State)} {s : (KernelState prog State)} {P : Array EmbC.Val} {i : BitVec 32} {t : Nat}
    (h : Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb { cm with pool := P }) (hPs : P.size = c0.pool.size)
    (habove : ∀ k, offs S.cs.pool x + 1 + i.toNat ≤ k → P[k]? = c0.pool[k]?)
    (hkept : ∀ y nd', y < x → keep y = true → S.cs.pool[y]? = some nd' →
      WordsAt P (offK keep S.cs.pool y) (newW X.posOf keep S.cs.pool nd'))
    (hcur : WordsAt P (offK keep S.cs.pool x) ((newW X.posOf keep S.cs.pool nd).take (1 + i.toNat)))
    (hil : i.toNat < tailLen nd) (ht : (tailW X.posOf (offK keep S.cs.pool) nd)[i.toNat]? = some t)
    (hI : ∀ s' P', Holds (W.addAux fb ⟨.u32, fw⟩) s'.mem sb { cm with pool := P' } →
      P'.size = c0.pool.size →
      (∀ k, offs S.cs.pool x + 1 + (i.toNat + 1) ≤ k → P'[k]? = c0.pool[k]?) →
      (∀ y nd', y < x → keep y = true → S.cs.pool[y]? = some nd' →
        WordsAt P' (offK keep S.cs.pool y) (newW X.posOf keep S.cs.pool nd')) →
      WordsAt P' (offK keep S.cs.pool x) ((newW X.posOf keep S.cs.pool nd).take (1 + (i.toNat + 1))) →
      I (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r (BitVec.ofNat 32 (offs S.cs.pool x))
        (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op)) (BitVec.ofNat 32 (tailLen nd))
        (i + 1#32) (BitVec.ofNat 32 t) (BitVec.ofNat 32 (offK keep S.cs.pool x))
        (BitVec.ofNat 32 (cntK keep x - X.nL)) ok .null 0) s') :
    WP prog (.seq (.store (.field (.var "st") "pool") (.bin .add (.bin .add (.var "cur") (.lit32 1#32))
        (.var "i")) (.var "c")) (.assign "i" (.bin .add (.var "i") (.lit32 1#32)))) (LoopQ I Q)
      (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r (BitVec.ofNat 32 (offs S.cs.pool x))
        (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op)) (BitVec.ofNat 32 (tailLen nd)) i
        (BitVec.ofNat 32 t) (BitVec.ofNat 32 (offK keep S.cs.pool x))
        (BitVec.ofNat 32 (cntK keep x - X.nL)) ok .null 0) s := by
  have hcore := hS.inv.core.cinv
  have hrep := hcore.rep
  obtain ⟨pb, hpb⟩ := hS.inv.poolPtr
  have hpcm : cm.k.pool = some (pb, 0) := by rw [hfr.poolPtr]; exact hpb
  have hpbc : ({ cm with pool := P } : CMem).k.pool = some (pb, 0) := hpcm
  have hxs := lt_size_of_getElem? hnd
  have hend := hrep.node_end hnd
  have hP32 := c0.k.plen.isLt
  have hkx' : offK keep S.cs.pool x ≤ offs S.cs.pool x := offK_le_offs x
  have hcap := hcore.poolCap
  have hpsz := hcore.poolSize pb 0 hpb
  have hidx : (BitVec.ofNat 32 (offK keep S.cs.pool x) + 1#32 + i).toNat =
      offK keep S.cs.pool x + 1 + i.toNat := by
    have : offK keep S.cs.pool x + 1 + i.toNat < 2 ^ 32 := by unfold nodeSize at hend; omega
    bv_omega
  have hlen : ((newW X.posOf keep S.cs.pool nd).take (1 + i.toNat)).length = 1 + i.toNat := by
    rw [List.length_take, newW_length]; unfold nodeSize; omega
  have hs := prog_ck
  apply WP.seq
  apply WP.ck_store .pool h rfl hpbc
  ck_simp [cpEnv, hpcm, hidx]
  refine ⟨by show _ < P.size; unfold nodeSize at hend; omega, fun s1 h1 => ?_⟩
  apply WP.assign_loop
  embc_simp
  apply hI s1 _ h1
  · show (P.setIfInBounds _ _).size = _; rw [Array.size_setIfInBounds]; exact hPs
  · intro k hk
    show (P.setIfInBounds _ _)[k]? = _
    rw [Array.getElem?_setIfInBounds_ne (by omega)]
    exact habove k (by omega)
  · intro y nd' hy hky hnd'
    have hyx := offK_add_le (pool := S.cs.pool) hky hnd' hy
    exact WordsAt.setOut (hkept y nd' hy hky hnd') (by rw [newW_length]; omega)
  · show WordsAt (P.setIfInBounds _ _) _ _
    rw [newW_take_succ ht]
    exact WordsAt.setSnoc hcur (by rw [hlen]; omega) (by rw [hPs]; unfold nodeSize at hend; omega)

theorem slide_inner {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 cm : CMem} {fb : Nat} {n : BitVec 32}
    (hS : SInv W ws X c0 S off rest) (hfr : StkFrame c0 cm)
    {keep : Nat → Bool} {fw : Array EmbC.Val} {x : Nat} {nd : Node}
    (hnd : S.cs.pool[x]? = some nd) (_hx : X.nL ≤ x) (hcl : KClosed keep S.cs.pool)
    (hkx : keep x = true) (hpre : ∀ y, y < X.nL → keep y = true)
    (hF : SlideFw S.cs.pool X.nL keep x fw) {r ok : BitVec 32} {Q : (Post prog State)} {rest' : Stmt}
    (K : ∀ (s : (KernelState prog State)) (P : Array EmbC.Val) (cc : BitVec 32),
      Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb { cm with pool := P } → P.size = c0.pool.size →
      (∀ k, offs S.cs.pool x + nodeSize nd ≤ k → P[k]? = c0.pool[k]?) →
      (∀ y nd', y < x → keep y = true → S.cs.pool[y]? = some nd' →
        WordsAt P (offK keep S.cs.pool y) (newW X.posOf keep S.cs.pool nd')) →
      WordsAt P (offK keep S.cs.pool x) (newW X.posOf keep S.cs.pool nd) →
      WP prog rest' Q (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r
        (BitVec.ofNat 32 (offs S.cs.pool x)) (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op))
        (BitVec.ofNat 32 (tailLen nd)) (BitVec.ofNat 32 (tailLen nd)) cc
        (BitVec.ofNat 32 (offK keep S.cs.pool x)) (BitVec.ofNat 32 (cntK keep x - X.nL)) ok .null 0) s)
    {env : Env} {s : (KernelState prog State)}
    (h0 : SlideInnerInv W sb fb c0 cm S X.nL n X.posOf keep fw x nd r ok env s) :
    WP prog (.seq cpSlideInner rest') Q env s := by
  have hs := prog_ck
  have hcore := hS.inv.core.cinv
  have hok := hcore.ok
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hlo := hS.lo
  have hplen := hrep.len
  obtain ⟨pb, hpb⟩ := hS.inv.poolPtr
  have hpb' : ({ cm with pool := (#[] : Array EmbC.Val) } : CMem).k.pool = some (pb, 0) := by
    show cm.k.pool = _; rw [hfr.poolPtr]; exact hpb
  have hxs := lt_size_of_getElem? hnd
  have hfit := hrep.fits x nd hnd
  have htl : tailLen nd < 256 := hfit.2.2.1
  have hend := hrep.node_end hnd
  have hP32 := c0.k.plen.isLt
  have hox : offs S.cs.pool x < 2 ^ 32 := by have := offs_lt_end hxs; omega
  have hkx' : offK keep S.cs.pool x ≤ offs S.cs.pool x := offK_le_offs x
  have hcap := hcore.poolCap
  have hpsz := hcore.poolSize pb 0 hpb
  unfold cpSlideInner
  apply WP.loop_seq (SlideInnerInv W sb fb c0 cm S X.nL n X.posOf keep fw x nd r ok) h0
  rintro env s ⟨P, i, cc, rfl, h, hPs, habove, hkept, hcur, hi⟩
  embc_simp [cpEnv]
  have htl32 : tailLen nd < 2 ^ 32 := by omega
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- done
    have hie : i = BitVec.ofNat 32 (tailLen nd) := by
      rw [BitVec.le_def, bv_toNat_ofNat htl32] at hge
      apply BitVec.eq_of_toNat_eq; rw [bv_toNat_ofNat htl32]; omega
    subst hie
    rw [bv_toNat_ofNat htl32] at habove hcur
    refine K s P cc h hPs (fun k hk => habove k (by unfold nodeSize at hk; omega)) hkept ?_
    rwa [List.take_of_length_le (by rw [newW_length]; unfold nodeSize; omega)] at hcur
  · have hil : i.toNat < tailLen nd := by
      rw [BitVec.lt_def, bv_toNat_ofNat htl32] at hlt; exact hlt
    -- the old word and the new one
    obtain ⟨w, hw⟩ : ∃ w, (tailW X.posOf (offs S.cs.pool) nd)[i.toNat]? = some w :=
      ⟨_, List.getElem?_eq_getElem (by rw [tailW_length]; exact hil)⟩
    obtain ⟨t, ht⟩ : ∃ t, (tailW X.posOf (offK keep S.cs.pool) nd)[i.toNat]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by rw [tailW_length]; exact hil)⟩
    have huw := hrep.tail hnd hw
    have hpcm : cm.k.pool = some (pb, 0) := by rw [hfr.poolPtr]; exact hpb
    have hpbc : ({ cm with pool := P } : CMem).k.pool = some (pb, 0) := hpcm
    have hidx : (BitVec.ofNat 32 (offs S.cs.pool x) + 1#32 + i).toNat = offs S.cs.pool x + 1 + i.toNat := by
      have : offs S.cs.pool x + 1 + i.toNat < 2 ^ 32 := by unfold nodeSize at hend; omega
      bv_omega
    have hPw : P[offs S.cs.pool x + 1 + i.toNat]? = some (.u32 (BitVec.ofNat 32 w)) := by
      rw [habove _ (Nat.le_refl _)]; exact huw
    -- the step after the word is known
    have hI : ∀ (s' : KernelState prog State) P', Holds (W.addAux fb ⟨.u32, fw⟩) s'.mem sb { cm with pool := P' } →
        P'.size = c0.pool.size →
        (∀ k, offs S.cs.pool x + 1 + (i.toNat + 1) ≤ k → P'[k]? = c0.pool[k]?) →
        (∀ y nd', y < x → keep y = true → S.cs.pool[y]? = some nd' →
          WordsAt P' (offK keep S.cs.pool y) (newW X.posOf keep S.cs.pool nd')) →
        WordsAt P' (offK keep S.cs.pool x) ((newW X.posOf keep S.cs.pool nd).take (1 + (i.toNat + 1))) →
        SlideInnerInv W sb fb c0 cm S X.nL n X.posOf keep fw x nd r ok
          (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r (BitVec.ofNat 32 (offs S.cs.pool x))
            (BitVec.ofNat 32 (hdrW nd)) (BitVec.ofNat 32 (opC nd.op)) (BitVec.ofNat 32 (tailLen nd))
            (i + 1#32) (BitVec.ofNat 32 t) (BitVec.ofNat 32 (offK keep S.cs.pool x))
            (BitVec.ofNat 32 (cntK keep x - X.nL)) ok .null 0) s' := by
      intro s' P' h' hPs' hab' hkp' hcur'
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := bv_add_toNat (by simp; omega)
      exact ⟨P', i + 1#32, _, rfl, h', hPs', by rw [hi1]; exact hab', hkp', by rw [hi1]; exact hcur',
        by rw [hi1]; omega⟩
    apply WP.seq
    apply WP.assign
    ck_simp [cpEnv, hpcm, h.rd_pool hpbc, hidx, rd_u32 hPw]
    have hc32 : opC nd.op < 2 ^ 32 := opC_lt32 _
    apply WP.seq
    apply WP.ite
    embc_simp
    by_cases hl : IsLeaf nd.op
    · -- a leaf: its words are copied as they are
      have htw : t = w := by
        rw [tailW_of_leaf (off' := offs S.cs.pool) hl, hw] at ht; exact (Option.some.inj ht).symm
      subst htw
      rcases leaf_code hl with e | e | e | e <;>
      · simp only [e]
        refine ⟨fun hc => absurd hc (by decide), fun _ => ?_⟩
        apply WP.skip
        have := slide_store hS hfr hnd hkx h hPs habove hkept hcur hil ht hI (Q := Q)
        rw [e] at this
        exact this
    · have e1 : opC nd.op ≠ 0x18 := fun e => hl (leaf_of_code (Or.inl e))
      have e2 : opC nd.op ≠ 0x19 := fun e => hl (leaf_of_code (Or.inr (Or.inl e)))
      have e3 : opC nd.op ≠ 0x08 := fun e => hl (leaf_of_code (Or.inr (Or.inr (Or.inl e))))
      have e4 : opC nd.op ≠ 0x09 := fun e => hl (leaf_of_code (Or.inr (Or.inr (Or.inr e))))
      have hil' : i.toNat < nd.args.size := by rw [← tailLen_of_not_leaf hl]; exact hil
      obtain ⟨a, haeq⟩ : ∃ a, nd.args[i.toNat]? = some a := ⟨_, Array.getElem?_eq_getElem hil'⟩
      have hai : nd.args[i.toNat] = a := by
        rw [Array.getElem?_eq_getElem hil'] at haeq; exact Option.some.inj haeq
      have ham : a ∈ nd.args := by rw [← hai]; exact Array.getElem_mem hil'
      have ht0 := ht
      rw [tailW_getElem?_of_not_leaf hl hil', hai] at hw ht
      have hwa : w = offs S.cs.pool a := (Option.some.inj hw).symm
      have hta : t = offK keep S.cs.pool a := (Option.some.inj ht).symm
      subst hwa
      subst hta
      have hay : a < x := hok.args_lt hnd a ham
      have has : a < S.cs.pool.size := by omega
      have hoa := offs_lt_of_lt hay (Nat.le_of_lt hxs)
      have hoa32 : offs S.cs.pool a < 2 ^ 32 := by omega
      have hka : keep a = true := hcl x nd hkx hnd a ham
      simp only [ofNat32_inj hc32 (by decide : (24 : Nat) < 2 ^ 32),
        ofNat32_inj hc32 (by decide : (25 : Nat) < 2 ^ 32),
        ofNat32_inj hc32 (by decide : (8 : Nat) < 2 ^ 32), ofNat32_inj hc32 (by decide : (9 : Nat) < 2 ^ 32),
        e1, e2, e3, e4, ↓reduceIte, BitVec.le_def, bv_toNat_ofNat hoa32,
        Nat.mod_eq_of_lt hoa32, Nat.mod_eq_of_lt hox]
      by_cases hge : X.nL ≤ a
      · -- a child at or above `nL`: its new offset is in the table
        have hin1 : c0.k.lo.toNat ≤ offs S.cs.pool a := by rw [hlo]; exact offs_le_of_le hge
        have h10 : ¬ (1#32 : BitVec 32) = 0#32 := by decide
        simp only [hoa, hin1, h10, ↓reduceIte]
        refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
        have hsub : (BitVec.ofNat 32 (offs S.cs.pool a) - c0.k.lo).toNat =
            offs S.cs.pool a - offs S.cs.pool X.nL := by
          rw [bv_sub_toNat (by rw [bv_toNat_ofNat hoa32]; omega), bv_toNat_ofNat hoa32, hlo]
        have hfa := hF.node a hge has
        simp only [hka, ↓reduceIte, hay] at hfa
        apply WP.assign
        embc_simp [h.rd_aux, hsub, rd_u32 hfa]
        exact slide_store hS hfr hnd hkx h hPs habove hkept hcur hil ht0 hI
      · -- a child below `nL`: it keeps its offset
        have hlow : offs S.cs.pool a < c0.k.lo.toNat := by
          rw [hlo]; exact offs_lt_of_lt (Nat.lt_of_not_le hge) hnL
        have h10 : ¬ (1#32 : BitVec 32) = 0#32 := by decide
        simp only [show ¬ c0.k.lo.toNat ≤ offs S.cs.pool a by omega, h10, ↓reduceIte]
        refine ⟨fun hc => absurd trivial hc, fun _ => ?_⟩
        apply WP.skip
        have heq : offK keep S.cs.pool a = offs S.cs.pool a :=
          offK_pre hpre hnL a (by omega)
        have := slide_store hS hfr hnd hkx h hPs habove hkept hcur hil ht0 hI (Q := Q)
        rw [heq] at this
        exact this

end Vbcf.Proof
