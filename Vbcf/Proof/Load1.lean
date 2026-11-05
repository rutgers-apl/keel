import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Intern
import Vbcf.Proof.ReplaySpecs
import Vbcf.Proof.DecodeEnc
import Vbcf.Proof.DSpecs

/-!
# Vbcf proofs: the loading phase, part 1 — allocation lemmas and `ck_init`

* `Holds.calloc`: a fresh zeroed block from `kvcalloc`, its pointer stored into
  the field of a still-`NULL` owned array (the idiom of `ck_init` and `ck_scan`);
* `Holds.setProof`: storing the proof pointer (`st->proof = proof`);
* `CoreInv.change_posOf`: the core invariant does not depend on `posOf` while
  the pool has no variables (so `ck_init` establishes it for every `posOf`);
* `ck_init_spec` (no hypotheses: `mk0` is proved in `Intern.lean`).
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## A fresh zeroed array -/

section
variable {P : Prog} {W : World} {m : Mem} {sb : Nat} {c : CMem}

/-- After `kvcalloc` of a still-`NULL` owned array `a` and the store of the
new pointer into its field, `Holds` is re-established with the new cells. -/
theorem Holds.calloc (hs : P.findStruct "ck" = some ckS) (h : Holds W m sb c) (a : Arr)
    (hnull : c.k.ptr a = none) (cells : Array EmbC.Val) :
    let m1 := (m.alloc .u32 cells).2
    let v := Val.ptr m.blocks.size 0
    m1.block? m.blocks.size = some ⟨.u32, cells⟩ ∧ HasCK m1 sb c.k ∧
    m1.storeField P sb a.field.1 v = some (m1.setCell sb a.field.2 v) ∧
    Holds W (m1.setCell sb a.field.2 v) sb
      ({ c with k := c.k.setPtr a (some (m.blocks.size, 0)) }.setArr a cells) := by
  intro m1 v
  have hsb := h.sb_lt
  have hnew : m1.block? m.blocks.size = some ⟨.u32, cells⟩ := by
    show (m.alloc _ _).2.block? _ = _
    rw [Mem.block?_alloc]; simp
  have hm1 : ∀ b', b' ≠ m.blocks.size → m1.block? b' = m.block? b' := by
    intro b' hne
    show (m.alloc _ _).2.block? _ = _
    rw [Mem.block?_alloc]; simp [hne]
  have hck : HasCK m1 sb c.k := by
    show m1.block? sb = _
    rw [hm1 sb (Nat.ne_of_lt hsb)]; exact h.ck
  have hstore : m1.storeField P sb a.field.1 v = some (m1.setCell sb a.field.2 v) :=
    Mem.storeField_eq (by rw [ck_slot hs hck, a.field_slot]) (Mem.hasTy_ptr hnew rfl)
      (by cases a <;> simp [Arr.field, CK.cells])
  refine ⟨hnew, hck, hstore, ?_⟩
  have hb : ∀ b', (m1.setCell sb a.field.2 v).block? b' =
      if b' = sb then some ⟨.struct "ck", c.k.cells.setIfInBounds a.field.2 v⟩
      else m1.block? b' := fun b' => by
    rw [Mem.block?_setCell b' hck]
  have hk : ({ c with k := c.k.setPtr a (some (m.blocks.size, 0)) }.setArr a cells).k =
      c.k.setPtr a (some (m.blocks.size, 0)) := by
    cases a <;> rfl
  have hptr : ∀ a', ({ c with k := c.k.setPtr a (some (m.blocks.size, 0)) }.setArr a cells).k.ptr a' =
      if a' = a then some (m.blocks.size, 0) else c.k.ptr a' := by
    intro a'; rw [hk, CK.setPtr_ptr]
  have hbase : W.base.blocks.size ≤ m.blocks.size := by have := h.sbNew; omega
  have howned_lt : ∀ a' b o, c.k.ptr a' = some (b, o) → b < m.blocks.size :=
    fun a' b o hp => Mem.block?_lt (h.arr a' b o hp).2.2.2
  refine ⟨?_, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (m1.setCell sb a.field.2 v).block? sb = _
    rw [hb]; simp only [↓reduceIte]
    rw [hk, CK.setPtr_cells]; rfl
  · show (m1.setCell sb a.field.2 v).block? W.pb = _
    rw [hb]; simp only [h.pb_ne_sb, ↓reduceIte]
    rw [hm1 W.pb (by have := h.pbOld; omega)]
    cases a <;> exact h.proof
  · cases a <;> exact h.proofPtr
  · cases a <;> exact h.parPtr
  · intro a' b o hpa
    rw [hptr] at hpa
    by_cases haa : a' = a
    · subst haa
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpa
      obtain ⟨rfl, rfl⟩ := hpa
      refine ⟨rfl, by omega, hbase, ?_⟩
      show (m1.setCell sb a'.field.2 v).block? m.blocks.size = _
      rw [hb]; simp only [Nat.ne_of_gt hsb, ↓reduceIte]
      rw [hnew]; cases a' <;> rfl
    · simp only [haa, ↓reduceIte] at hpa
      obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a' b o hpa
      refine ⟨ho, hbs, hbb, ?_⟩
      show (m1.setCell sb a.field.2 v).block? b = _
      rw [hb]; simp only [hbs, ↓reduceIte]
      rw [hm1 b (Nat.ne_of_lt (howned_lt a' b o hpa))]
      cases a <;> cases a' <;> first | exact absurd rfl haa | exact harr
  · intro a1 a2 b1 b2 o1 o2 hne h1 h2
    rw [hptr] at h1 h2
    by_cases e1 : a1 = a
    · subst e1
      have e2 : a2 ≠ a1 := fun e => hne e.symm
      simp only [↓reduceIte, e2, Option.some.injEq, Prod.mk.injEq] at h1 h2
      have := howned_lt a2 b2 o2 h2
      omega
    · by_cases e2 : a2 = a
      · subst e2
        simp only [↓reduceIte, e1, Option.some.injEq, Prod.mk.injEq] at h1 h2
        have := howned_lt a1 b1 o1 h1
        omega
      · simp only [e1, e2, ↓reduceIte] at h1 h2
        exact h.sep a1 a2 b1 b2 o1 o2 hne h1 h2
  · intro b hlt hne
    rw [hb]
    have h1 : b ≠ sb := by have := h.sbNew; omega
    simp only [h1, ↓reduceIte]
    rw [hm1 b (by omega)]
    exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]; simp only [hne, ↓reduceIte]
    have hbn : b ≠ m.blocks.size := fun e => hno a 0 (by rw [hptr, e]; simp)
    rw [hm1 b hbn]
    refine h.exact b hge hne (fun a' o hp => ?_)
    by_cases haa : a' = a
    · subst haa; rw [hnull] at hp; cases hp
    · exact hno a' o (by rw [hptr]; simp [haa, hp])
  · intro b hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b hb'
    refine ⟨h1, h2, fun a' o => ?_⟩
    rw [hptr]
    by_cases haa : a' = a
    · simp only [haa, ↓reduceIte, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
      intro e; subst e; exact absurd (h.aux_ge (Nat.le_refl _)) hb'
    · simp only [haa, ↓reduceIte]; exact h3 a' o

/-- The pointer stored for `t = kvcalloc(…)`, when the block is fresh. -/
theorem Holds.calloc_ptr (_h : Holds W m sb c) (cells : Array EmbC.Val) :
    ((m.alloc .u32 cells).2.block? m.blocks.size).isSome = true := by
  rw [Mem.block?_alloc]; simp

/-! ## The proof pointer -/

/-- `st->proof = proof` where `proof` is the checker's copy of the proof. -/
theorem Holds.setProof (hs : P.findStruct "ck" = some ckS) (h : Holds W m sb c) :
    m.storeField P sb "proof" (.ptr W.pb 0) = some (m.setCell sb 15 (.ptr W.pb 0)) ∧
    Holds W (m.setCell sb 15 (.ptr W.pb 0)) sb { c with k := { c.k with proof := some (W.pb, 0) } } := by
  have hstore : m.storeField P sb "proof" (.ptr W.pb 0) = some (m.setCell sb 15 (.ptr W.pb 0)) :=
    Mem.storeField_eq (by rw [ck_slot hs h.ck, fi_proof]) (Mem.hasTy_ptr h.proof rfl)
      (by simp [CK.cells])
  refine ⟨hstore, ?_⟩
  have hb := fun b' => Mem.block?_setCell (i := 15) (v := .ptr W.pb 0) b' h.ck
  have hptr : ∀ a, ({ c with k := { c.k with proof := some (W.pb, 0) } } : CMem).k.ptr a = c.k.ptr a := by
    intro a; cases a <;> rfl
  refine ⟨?_, h.sbNew, h.pbOld, ?_, Or.inr rfl, h.parPtr, ?_, ?_, ?_, ?_, ?_⟩
  · show (m.setCell sb 15 _).block? sb = _
    rw [hb]; simp [CK.cells]
  · show (m.setCell sb 15 _).block? W.pb = _
    rw [hb]; simp [h.pb_ne_sb]; exact h.proof
  · intro a b o hpa
    rw [hptr] at hpa
    obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a b o hpa
    refine ⟨ho, hbs, hbb, ?_⟩
    show (m.setCell sb 15 _).block? b = _
    rw [hb]; simp [hbs]
    cases a <;> exact harr
  · intro a a' b b' o o' hne hpa hpa'
    rw [hptr] at hpa hpa'
    exact h.sep a a' b b' o o' hne hpa hpa'
  · intro b hlt hne
    rw [hb]
    have : b ≠ sb := by have := h.sbNew; omega
    simp [this]; exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]; simp [hne]
    exact h.exact b hge hne (fun a o => by rw [← hptr]; exact hno a o)
  · intro b hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b hb'
    exact ⟨h1, h2, fun a o => by rw [hptr]; exact h3 a o⟩

end

/-! ## The core invariant does not look at `posOf` while there are no variables -/

/-- No node of the pool is a variable. -/
def NoVars (pool : Pool) : Prop :=
  ∀ (i : Nat) (n : Node), pool[i]? = some n → opC n.op ≠ 0x18 ∧ opC n.op ≠ 0x19

theorem NoVars.empty : NoVars #[] := by
  intro i n h; simp at h

theorem NoVars.push {pool : Pool} (h : NoVars pool) {n : Node}
    (hn : opC n.op ≠ 0x18 ∧ opC n.op ≠ 0x19) : NoVars (pool.push n) := by
  intro i m hm
  rw [Array.getElem?_push] at hm
  split at hm
  · simp only [Option.some.injEq] at hm; subst hm; exact hn
  · exact h i m hm

theorem NoVars.pushNode {st st' : St} {n : Node} {r : Nat} (h : NoVars st.pool)
    (hp : pushNode st n = some (st', r)) (hn : opC n.op ≠ 0x18 ∧ opC n.op ≠ 0x19) :
    NoVars st'.pool := by
  rcases pushNode_pool hp with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  · exact h
  · exact h.push hn

theorem NoVars.interned {st st' : St} {n : Node} {r : Nat} (h : NoVars st.pool)
    (hp : Interned st n st' r) (hn : opC n.op ≠ 0x18 ∧ opC n.op ≠ 0x19) :
    NoVars st'.pool := by
  rcases hp.pool with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  · exact h
  · exact h.push hn

theorem tailW_noVar {posOf posOf' off : Nat → Nat} {n : Node}
    (hn : opC n.op ≠ 0x18 ∧ opC n.op ≠ 0x19) : tailW posOf off n = tailW posOf' off n := by
  rcases n with ⟨op, args⟩
  cases op <;> first | rfl | (exfalso; simp [opC] at hn)

theorem nodeW_noVar {posOf posOf' : Nat → Nat} {pool : Pool} {n : Node}
    (hn : opC n.op ≠ 0x18 ∧ opC n.op ≠ 0x19) : nodeW posOf pool n = nodeW posOf' pool n := by
  unfold nodeW; rw [tailW_noVar (posOf' := posOf') hn]

theorem Fits.noVar {posOf posOf' : Nat → Nat} {n : Node} (hf : Fits posOf n)
    (hn : opC n.op ≠ 0x18 ∧ opC n.op ≠ 0x19) : Fits posOf' n := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨h1, h2, h3, ?_⟩
  rw [tailW_noVar (posOf' := posOf) hn]; exact h4

/-- `CoreInv` for any other injective `posOf`, while the pool has no variables. -/
theorem CoreInv.change_posOf {posOf posOf' : Nat → Nat} {c : CMem} {st : St}
    (hc : CoreInv posOf c st) (hnv : NoVars st.pool)
    (hinj : ∀ a b, posOf' a = posOf' b → a = b) : CoreInv posOf' c st where
  ok := hc.ok
  poolNull := hc.poolNull
  poolSize := hc.poolSize
  poolCap := hc.poolCap
  rep := by
    refine ⟨hc.rep.len, ?_, ?_⟩
    · intro i n hn; exact (hc.rep.fits i n hn).noVar (hnv i n hn)
    · intro i n hn
      rw [nodeW_noVar (posOf' := posOf) (hnv i n hn)]
      exact hc.rep.cell i n hn
  htabPtr := hc.htabPtr
  htab := by
    have ht := hc.htab
    refine ⟨ht.size, ht.pow, ht.cnt, ht.nz, ht.load, ht.cell, ?_⟩
    intro i n hn
    have := ht.find i n hn
    unfold hashNode at this ⊢
    rw [nodeW_noVar (posOf' := posOf) (hnv i n hn)]
    exact this
  stk := hc.stk
  posInj := hinj

/-! ## `ck_init` -/

/-- The struct after the table is allocated. -/
def initK (hb : Nat) : CK := { zeroCK with htab := some (hb, 0), hcap := 1024#32 }

/-- The struct after the table and the premise buffer are allocated. -/
def initK2 (hb pb : Nat) : CK := { initK hb with prem := some (pb, 0) }

theorem initK2_stk (hb pb : Nat) : (initK2 hb pb).stk = none := rfl

/-- The core invariant for the empty Lean pool, once the table is allocated
and the struct is otherwise as `kzalloc` left it. -/
theorem coreInv_init {c : CMem} {b pb : Nat} (posOf : Nat → Nat)
    (hinj : ∀ a b, posOf a = posOf b → a = b)
    (hk : c.k = initK2 b pb)
    (hhtab : c.htab = Array.replicate 1024 (.u32 0#32)) : CoreInv posOf c initSt where
  ok := initSt_ok
  poolNull := by intro _; rw [hk]; rfl
  poolSize := by intro b o h; rw [hk] at h; cases h
  poolCap := by rw [hk]; simp [initK2, initK, zeroCK, maxPool]
  rep := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hk]; simp [initK2, initK, zeroCK, initSt]
    · intro i n hn; simp [initSt] at hn
    · intro i n hn; simp [initSt] at hn
  htabPtr := ⟨b, by rw [hk]; rfl⟩
  htab := by
    rw [hk, hhtab]
    refine ⟨by rw [Array.size_replicate]; rfl, ⟨10, rfl, by omega⟩, rfl, nzCount_replicate _,
      by show 2 * 0 ≤ 1024; decide, ?_, ?_⟩
    · intro s hs
      refine ⟨0, ?_, by decide, fun h => absurd rfl h⟩
      have hs' : s < 1024 := hs
      unfold U
      simp [hs']
    · intro i n hn; simp [initSt] at hn
  stk := ⟨(fun _ => by rw [hk]; rfl), (fun b o h => by rw [hk] at h; cases h),
    (by rw [hk]; simp [initK2, initK, zeroCK, maxPool])⟩
  posInj := hinj

theorem CoreInv.setTt {posOf : Nat → Nat} {c : CMem} {st : St} (hc : CoreInv posOf c st)
    (x : BitVec 32) : CoreInv posOf { c with k := { c.k with tt := x } } st :=
  hc.congr rfl rfl rfl rfl rfl hc.poolNull hc.poolSize hc.poolCap (fun _ _ => rfl)
    ⟨hc.stk.null, hc.stk.size, hc.stk.cap⟩

theorem CoreInv.setFf {posOf : Nat → Nat} {c : CMem} {st : St} (hc : CoreInv posOf c st)
    (x : BitVec 32) : CoreInv posOf { c with k := { c.k with ff := x } } st :=
  hc.congr rfl rfl rfl rfl rfl hc.poolNull hc.poolSize hc.poolCap (fun _ _ => rfl)
    ⟨hc.stk.null, hc.stk.size, hc.stk.cap⟩

/-- The postcondition of `mk0` on a boolean literal, named. -/
def Mk0Post (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (b : Bool) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
    ((r = noid ∧ CoreInv posOf c' st) ∨
     (∃ st' i, Interned st ⟨.boolVal b, #[]⟩ st' i ∧
        CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid))

theorem mk0_post (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (b : Bool) :
    FnSpec (State := State) Vbcf.prog "mk0"
      (fun vs s => vs = [.ptr sb 0, .u32 (if b then 0x10009#32 else 0x9#32)] ∧
        Holds W s.mem sb c ∧ CoreInv posOf c st)
      (fun _ _ => Mk0Post W sb c posOf st b) :=
  mk0_bool_dspec W sb c posOf st b

/-- The postcondition of `ck_init`, named. -/
def InitPost (W : World) (sb : Nat) (c : CMem) : Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c', Holds W s'.mem sb c' ∧ c'.proof = c.proof ∧
    (rv = some (.u32 0#32) ∨ (rv = some (.u32 1#32) ∧ ∃ st1 tt ff, DInitDone c' st1 tt ff))

theorem bv1024_ne : (1024#64 : BitVec 64) ≠ 0 := by decide
theorem bv256_ne : (256#64 : BitVec 64) ≠ 0 := by decide

theorem ck_init_dspec : DInitSpec (State := State) := by
  intro W sb c nw g
  show FnSpec (State := State) Vbcf.prog "ck_init" _ (fun _ _ => InitPost W sb c)
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckInit) rfl
  rintro vs s ⟨rfl, h, hk⟩
  simp [ckInit, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  -- t = kvcalloc(1024, sizeof(u32));
  apply WP.seq
  apply WP.ecall
  ck_simp [kvcalloc_run bv1024_ne]
  by_cases horc : (callocResponse (P := Vbcf.prog) bv1024_ne s).1 ≠ some .null
  · simp only [ne_eq, Classical.not_not] at horc
    simp only [horc, ↓reduceIte]
    have hcap : (1024#64 : BitVec 64).toNat = 1024 := rfl
    obtain ⟨hnew, hck, hst, hH⟩ := h.calloc hs .htab (by rw [hk]; rfl)
      (Array.replicate 1024 (.u32 0#32))
    simp only [Arr.field] at hst hH
    embc_simp [Mem.hasTy_ptr hnew rfl]
    apply WP.seq
    apply WP.ite
    embc_simp [hnew]
    apply WP.skip
    apply WP.seq
    apply WP.setField
    embc_simp [hst]
    clear h
    have h := hH
    simp only [CMem.setArr, CK.setPtr] at h
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    clear h
    intro s1 h
    -- q = kvcalloc(256, sizeof(u32));
    apply WP.seq
    apply WP.ecall
    ck_simp [kvcalloc_run bv256_ne]
    by_cases horc1 : (callocResponse (P := Vbcf.prog) bv256_ne s1).1 ≠ some .null
    · simp only [ne_eq, Classical.not_not] at horc1
      simp only [horc1, ↓reduceIte]
      obtain ⟨hnew1, hck1, hst1, hH1⟩ := h.calloc hs .prem (by rw [hk]; rfl)
        (Array.replicate 256 (.u32 0#32))
      simp only [Arr.field] at hst1 hH1
      embc_simp [Mem.hasTy_ptr hnew1 rfl]
      apply WP.seq
      apply WP.ite
      embc_simp [hnew1]
      apply WP.skip
      apply WP.seq
      apply WP.setField
      embc_simp [hst1]
      clear h
      have h := hH1
      simp only [CMem.setArr, CK.setPtr] at h
      -- the state now: table and premise buffer allocated
      obtain ⟨c1, hc1⟩ : ∃ c1 : CMem, c1 =
          { k := initK2 s.mem.blocks.size s1.mem.blocks.size,
            pool := c.pool, htab := Array.replicate 1024 (.u32 0#32), facts := c.facts,
            stk := c.stk, prem := Array.replicate 256 (.u32 0#32), proof := c.proof,
            lr := c.lr } := ⟨_, rfl⟩
      rw [hk] at h
      have h : Holds W ((s1.mem.alloc .u32 (Array.replicate 256 (.u32 0#32))).2.setCell sb 13
          (.ptr s1.mem.blocks.size 0)) sb c1 := by rw [hc1]; exact h
      have hinv : CoreInv id c1 initSt :=
        coreInv_init id (fun _ _ e => e) (by rw [hc1]) (by rw [hc1])
      -- the work budget
      apply WP.seq; apply WP.assign; ck_simp
      apply WP.seq
      apply WP.ite
      ck_simp
      constructor
      · intro _
        apply WP.seq
        apply WP.ck_setField hs h (by rfl)
        ck_simp
        clear h
        intro s2 h
        apply WP.ret
        ck_simp [retPost]
        unfold InitPost
        exact ⟨_, h, by rw [hc1], Or.inl rfl⟩
      intro _
      apply WP.skip
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      clear h
      intro s1' h
      obtain ⟨w, h⟩ : ∃ w, Holds W s1'.mem sb (c1.wev w c1.k.err c1.k.val) := ⟨_, h⟩
      have hinv : CoreInv id (c1.wev w c1.k.err c1.k.val) initSt := hinv.wev
      -- the memory budget
      apply WP.seq; apply WP.assign; ck_simp
      apply WP.seq
      apply WP.ite
      ck_simp
      constructor
      · intro _
        apply WP.seq
        apply WP.ck_setField hs h (by rfl)
        ck_simp
        clear h
        intro s2 h
        apply WP.ret
        ck_simp [retPost]
        unfold InitPost
        exact ⟨_, h, by rw [hc1], Or.inl rfl⟩
      intro _
      apply WP.skip
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      clear h
      intro s1'' h
      obtain ⟨mm, h⟩ : ∃ mm, Holds W s1''.mem sb ((c1.wev w c1.k.err c1.k.val).setMem mm) := ⟨_, h⟩
      have hinv : CoreInv id ((c1.wev w c1.k.err c1.k.val).setMem mm) initSt := hinv.setMem
      -- r = mk0(st, HDR_TRUE);
      apply WP.seq
      apply WP.call (mk0_post W sb ((c1.wev w c1.k.err c1.k.val).setMem mm) id initSt true)
      ck_simp [HDR_TRUE]
      refine ⟨⟨h, hinv⟩, ?_⟩
      clear h
      rintro rv s2 ⟨c2, r, rfl, h, hf2, hres⟩
      ck_simp
      rcases hres with ⟨rfl, -⟩ | ⟨st0, tt, hpush0, hinv2, hr, hne⟩
      · apply WP.seq
        apply WP.ite
        ck_simp [noid]
        apply WP.ret
        ck_simp [retPost]
        unfold InitPost
        exact ⟨c2, h, by rw [hf2.proof, setMem_proof, wev_proof, hc1], Or.inl rfl⟩
      · simp only [noid] at hne
        apply WP.seq
        apply WP.ite
        ck_simp [hne]
        apply WP.skip
        apply WP.seq
        apply WP.ck_setField hs h (by rfl)
        ck_simp
        clear h
        intro s3 h
        have hinv3 : CoreInv id { c2 with k := { c2.k with tt := r } } st0 := hinv2.setTt r
        -- r = mk0(st, HDR_FALSE);
        apply WP.seq
        apply WP.call (mk0_post W sb _ id st0 false)
        ck_simp [HDR_FALSE]
        refine ⟨⟨h, hinv3⟩, ?_⟩
        clear h
        rintro rv s4 ⟨c4, r', rfl, h, hf4, hres⟩
        ck_simp
        rcases hres with ⟨rfl, -⟩ | ⟨st1, ff, hpush1, hinv4, hr', hne'⟩
        · apply WP.seq
          apply WP.ite
          ck_simp [noid]
          apply WP.ret
          ck_simp [retPost]
          unfold InitPost
          exact ⟨c4, h, by rw [hf4.proof, hf2.proof, setMem_proof, wev_proof, hc1], Or.inl rfl⟩
        · simp only [noid] at hne'
          apply WP.seq
          apply WP.ite
          ck_simp [hne']
          apply WP.skip
          apply WP.seq
          apply WP.ck_setField hs h (by rfl)
          ck_simp
          clear h
          intro s5 h
          apply WP.ret
          ck_simp [retPost]
          unfold InitPost
          refine ⟨_, h, by simp only [hf4.proof, hf2.proof, setMem_proof, wev_proof, hc1], Or.inr ⟨rfl, st1, tt, ff, ?_⟩⟩
          have hinv5 : CoreInv id { c4 with k := { c4.k with ff := r' } } st1 := hinv4.setFf r'
          have hnv0 : NoVars st0.pool := NoVars.empty.interned (st := initSt) hpush0 (by decide)
          have hnv1 : NoVars st1.pool := hnv0.interned hpush1 (by decide)
          have htt_lt : tt < st0.pool.size := hpush0.lt
          refine
            { b2 := ⟨st0, hpush0, hpush1⟩
              core := fun posOf hinj => hinv5.change_posOf hnv1 hinj
              tt := ?_
              ff := hr'
              prem := ?_
              factsNull := ?_
              flen := ?_
              proofNull := ?_
              parNull := ?_
              lrNull := ?_ }
          · show c4.k.tt.toNat = _
            rw [hf4.tt]
            show r.toNat = _
            rw [hr, hpush1.offs (Nat.le_of_lt htt_lt)]
          · refine ⟨⟨s1.mem.blocks.size, ?_⟩, ?_, ?_⟩
            · show c4.k.prem = _
              rw [hf4.premPtr]
              show c2.k.prem = _
              rw [hf2.premPtr, hc1]; rfl
            · show c4.prem.size = 256
              rw [hf4.prem, hf2.prem, hc1]; simp
            · intro j hj
              show ∃ w, w < 2 ^ 32 ∧ U c4.prem j w
              rw [hf4.prem, hf2.prem, hc1]
              refine ⟨0, by decide, ?_⟩
              unfold U; simp [hj]
          · show c4.k.facts = none
            rw [hf4.factsPtr]
            show c2.k.facts = none
            rw [hf2.factsPtr, hc1]; rfl
          · show c4.k.flen = 0#32
            rw [hf4.flen]
            show c2.k.flen = 0#32
            rw [hf2.flen, hc1]; rfl
          · show c4.k.proof = none
            rw [hf4.proofPtr]
            show c2.k.proof = none
            rw [hf2.proofPtr, hc1]; rfl
          · show c4.k.par = none
            rw [hf4.par]
            show c2.k.par = none
            rw [hf2.par, hc1]; rfl
          · show c4.k.lr = none
            rw [hf4.lrPtr]
            show c2.k.lr = none
            rw [hf2.lrPtr, hc1]; rfl
    · simp only [ne_eq, Classical.not_not] at horc1
      simp only [horc1, ↓reduceIte]
      embc_simp
      apply WP.seq
      apply WP.ite
      embc_simp
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      clear h
      intro s2 h
      apply WP.ret
      ck_simp [retPost]
      unfold InitPost
      exact ⟨_, h, rfl, Or.inl rfl⟩
  · simp only [ne_eq, Classical.not_not] at horc
    simp only [horc, ↓reduceIte]
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    clear h
    intro s2 h
    apply WP.ret
    ck_simp [retPost]
    unfold InitPost
    exact ⟨_, h, rfl, Or.inl rfl⟩

/-- The structural initialization result supplies the main loading phase's
precondition, including the fresh last-reference pointer. -/
theorem DInitDone.toInit {c : CMem} {st1 : St} {tt ff : Nat}
    (hd : DInitDone c st1 tt ff) : InitDone c st1 tt ff := by
  obtain ⟨st0, h0, h1⟩ := hd.b2
  exact
    { b2 := ⟨st0, h0.pushNode_eq initSt_ok, h1.pushNode_eq (h0.ok initSt_ok)⟩
      core := hd.core, tt := hd.tt, ff := hd.ff, prem := hd.prem, factsNull := hd.factsNull
      flen := hd.flen, proofNull := hd.proofNull, parNull := hd.parNull, lrNull := hd.lrNull }

/-- The main initialization contract follows from the structural proof. -/
theorem ck_init_spec : InitSpec (State := State) := by
  intro W sb c nw g
  refine FnSpec.of_post (ck_init_dspec W sb c nw g) ?_
  rintro vs s rv s' ⟨c', h, hp, hres⟩
  refine ⟨c', h, hp, ?_⟩
  rcases hres with hfail | ⟨hr, st1, tt, ff, hd⟩
  · exact Or.inl hfail
  · exact Or.inr ⟨hr, st1, tt, ff, hd.toInit⟩

end Vbcf.Proof
