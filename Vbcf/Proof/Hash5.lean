import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Hash4
import Vbcf.Proof.Alloc

/-!
# Vbcf proofs: `ck_hgrow`

`ck_hgrow` allocates a table twice the size, re-enters every node, and frees
the old table.  Between `st->htab = nt` and `kvfree(old)` the old block is
live but detached, so the loop is verified over `HView`; `Holds.swap_htab`
re-establishes `Holds` at the end.

## The strengthened invariant

`HtabOK` (in `Spec.lean`) is not preserved by `ck_hgrow`: it says
`hcnt = pool.size` but allows a node to occupy two slots, and `ck_hgrow`
recomputes `hcnt` as the number of occupied slots.  `CoreInv'` adds
`nzCount htab = hcnt` (the count field is the number of occupied slots),
which every operation preserves.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- `CoreInv`, plus: `hcnt` is the number of occupied slots of the table. -/
structure CoreInv' (posOf : Nat → Nat) (c : CMem) (st : St) : Prop where
  core : CoreInv posOf c st
  nz : nzCount c.htab = c.k.hcnt.toNat

/-- `c'` differs from `c` only in the hash table (pointer, capacity, count,
contents) and the error flag. -/
structure HFrame (c c' : CMem) : Prop where
  frame : PoolFrame c c'
  pool : c'.pool = c.pool
  poolPtr : c'.k.pool = c.k.pool
  plen : c'.k.plen = c.k.plen
  pcap : c'.k.pcap = c.k.pcap

theorem PoolFrame.self (c : CMem) : PoolFrame c c := by constructor <;> rfl

theorem HFrame.refl (c : CMem) : HFrame c c := ⟨PoolFrame.self c, rfl, rfl, rfl, rfl⟩

/-- `ck_hgrow(st)`: on success the table has twice the capacity and holds the
same nodes; on failure nothing but the error flag changes.  Called only
when the pool is allocated. -/
def HgrowSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St),
    FnSpec (State := State) Vbcf.prog "ck_hgrow"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv' posOf c st ∧
        ∃ pb, c.k.pool = some (pb, 0))
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧ HFrame c c' ∧ CoreInv' posOf c' st ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ c'.k.hcap.toNat = 2 * c.k.hcap.toNat)))

/-! ## Kernel calls -/

/-- The actual public response and private world selected by this allocation. -/
def callocResponse {P : Prog} {n : BitVec 64}
    (_hn : n ≠ 0) (st : KernelState P State) : Option EmbC.Val × KernelState P State :=
  Ext.answer P (.kvcalloc .u32) [.u64 n] st

theorem kvcalloc_run {P : Prog} {n : BitVec 64}
    {st : KernelState P State} (hn : n ≠ 0) :
    Ext.run P (.kvcalloc .u32) [.u64 n] st =
      if (callocResponse (P := P) hn st).1 ≠ some .null then
        some (some (.ptr st.mem.blocks.size 0),
          ⟨(st.mem.alloc .u32 (Array.replicate n.toNat (.u32 0#32))).2,
            (callocResponse (P := P) hn st).2.oracle⟩)
      else some (some .null, ⟨st.mem, (callocResponse (P := P) hn st).2.oracle⟩) := by
  have hd : Kernel.Defined P ⟨.kvcalloc .u32, [.u64 n], st.mem⟩ := ⟨hn, rfl⟩
  rw [Ext.run_answer hd]
  have hc := (Ext.answer_spec hd).kvcalloc
  change _ = if (Ext.answer P (.kvcalloc .u32) [.u64 n] st).1 ≠ some .null then _ else _
  generalize he : Ext.answer P (.kvcalloc .u32) [.u64 n] st = reply at *
  rcases reply with ⟨rv, ⟨mem, world⟩⟩
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [callocResponse, he, EmbC.Ty.zero]

theorem kvfree_run {P : Prog}
    {st : KernelState P State} {b : Nat} {blk : Block}
    (hb : st.mem.block? b = some blk) :
    Ext.run P .kvfree [.ptr b 0] st = some (none,
      ⟨st.mem.free b, (Ext.answer P .kvfree [.ptr b 0] st).2.oracle⟩) := by
  have hd : Kernel.Defined P ⟨.kvfree, [.ptr b 0], st.mem⟩ := ⟨rfl, blk, hb⟩
  rw [Ext.run_answer hd]
  have hc := (Ext.answer_spec hd).kvfree_ptr
  generalize he : Ext.answer P .kvfree [.ptr b 0] st = reply at *
  rcases reply with ⟨rv, ⟨mem, world⟩⟩
  rcases hc with ⟨rfl, rfl⟩
  rfl

/-! ## Replacing the table block -/

section
variable {W : World} {m : Mem} {sb : Nat} {c : CMem}

/-- `Holds` after the table has been moved to a fresh block `nb` and the old
block `ob` freed: all that is needed is the contents of the three blocks
involved, and that no other block changed. -/
theorem Holds.swap_htab (h : Holds W m sb c) {ob : Nat} (hold : c.k.htab = some (ob, 0))
    {m' : Mem} {k' : CK} {nb : Nat} {cells : Array EmbC.Val} (hnb : nb = m.blocks.size)
    (hck : HasCK m' sb k')
    (hk : k'.pool = c.k.pool ∧ k'.htab = some (nb, 0) ∧ k'.facts = c.k.facts ∧ k'.stk = c.k.stk ∧
      k'.prem = c.k.prem ∧ k'.par = c.k.par ∧ k'.proof = c.k.proof ∧ k'.lr = c.k.lr)
    (hnew : HasArr m' nb cells) (hfree : m'.block? ob = none)
    (hsame : ∀ b, b ≠ sb → b ≠ nb → b ≠ ob → m'.block? b = m.block? b) :
    Holds W m' sb { c with k := k', htab := cells } := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8⟩ := hk
  have hsb := h.sb_lt
  have hbase : W.base.blocks.size ≤ nb := by have := h.sbNew; omega
  have hlive : ∀ a b o, c.k.ptr a = some (b, o) → b < m.blocks.size :=
    fun a b o hp => Mem.block?_lt (h.arr a b o hp).2.2.2
  have hptr : ∀ a, a ≠ .htab → k'.ptr a = c.k.ptr a := by
    intro a ha; cases a <;> simp [CK.ptr, *] at *
  have hob : ∀ a b o, a ≠ .htab → c.k.ptr a = some (b, o) → b ≠ ob :=
    fun a b o ha hp => h.sep a .htab b ob o 0 ha hp hold
  have hpbob : W.pb ≠ ob := by
    have := (h.arr .htab ob 0 hold).2.2.1; have := h.pbOld; omega
  refine ⟨hck, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show m'.block? W.pb = _
    rw [hsame W.pb h.pb_ne_sb (by have := h.pbOld; omega) hpbob]; exact h.proof
  · show k'.proof = none ∨ _
    rw [hk7]; exact h.proofPtr
  · show k'.par = none ∨ _
    rw [hk6]; exact h.parPtr
  · intro a b o hpa
    by_cases ha : a = .htab
    · subst ha
      have hpa' : k'.htab = some (b, o) := hpa
      rw [hk2] at hpa'
      simp only [Option.some.injEq, Prod.mk.injEq] at hpa'
      obtain ⟨rfl, rfl⟩ := hpa'
      exact ⟨rfl, by omega, hbase, hnew⟩
    · have hpa' : c.k.ptr a = some (b, o) := by rw [← hptr a ha]; exact hpa
      obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a b o hpa'
      refine ⟨ho, hbs, hbb, ?_⟩
      show m'.block? b = _
      rw [hsame b hbs (by have := hlive a b o hpa'; omega) (hob a b o ha hpa')]
      cases a <;> first | exact absurd rfl ha | exact harr
  · intro a1 a2 b1 b2 o1 o2 hne h1 h2
    by_cases e1 : a1 = .htab
    · subst e1
      have e2 : a2 ≠ .htab := fun e => hne e.symm
      have h1' : k'.htab = some (b1, o1) := h1
      rw [hk2] at h1'
      simp only [Option.some.injEq, Prod.mk.injEq] at h1'
      have h2' : c.k.ptr a2 = some (b2, o2) := by rw [← hptr a2 e2]; exact h2
      have := hlive a2 b2 o2 h2'
      omega
    · have h1' : c.k.ptr a1 = some (b1, o1) := by rw [← hptr a1 e1]; exact h1
      by_cases e2 : a2 = .htab
      · subst e2
        have h2' : k'.htab = some (b2, o2) := h2
        rw [hk2] at h2'
        simp only [Option.some.injEq, Prod.mk.injEq] at h2'
        have := hlive a1 b1 o1 h1'
        omega
      · have h2' : c.k.ptr a2 = some (b2, o2) := by rw [← hptr a2 e2]; exact h2
        exact h.sep a1 a2 b1 b2 o1 o2 hne h1' h2'
  · intro b hlt hne
    have h1 : b ≠ sb := by have := h.sbNew; omega
    have h2 : b ≠ ob := by have := (h.arr .htab ob 0 hold).2.2.1; omega
    rw [hsame b h1 (by omega) h2]
    exact h.out b hlt hne
  · intro b hge hne hno
    have hbn : b ≠ nb := fun e => hno .htab 0 (by show k'.htab = _; rw [hk2, e])
    by_cases hbo : b = ob
    · rw [hbo, hfree, h.aux_owned (a := .htab) hold]
    · rw [hsame b hne hbn hbo]
      refine h.exact b hge hne (fun a o hp => ?_)
      by_cases ha : a = .htab
      · subst ha
        have hp' : c.k.htab = some (b, o) := hp
        rw [hold] at hp'
        simp only [Option.some.injEq, Prod.mk.injEq] at hp'
        exact hbo hp'.1.symm
      · exact hno a o (by rw [hptr a ha]; exact hp)
  · intro b hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b hb'
    refine ⟨h1, h2, fun a o hp => ?_⟩
    by_cases ha : a = .htab
    · subst ha
      have hp' : k'.htab = some (b, o) := hp
      rw [hk2] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hp'
      exact hb' (by rw [← hp'.1, hnb]; exact h.aux_ge (Nat.le_refl _))
    · exact h3 a o (by rw [← hptr a ha]; exact hp)

end

/-- `Holds` after only the struct changed, keeping every pointer: all other
blocks are as before. -/
theorem Holds.frame_ck {W : World} {m : Mem} {sb : Nat} {c : CMem} (h : Holds W m sb c)
    {m' : Mem} {k' : CK} (hck : HasCK m' sb k') (hk : k'.ptr4 = c.k.ptr4)
    (hsame : ∀ b, b ≠ sb → m'.block? b = m.block? b) :
    Holds W m' sb { c with k := k' } := by
  simp only [CK.ptr4, List.cons.injEq, and_true] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hk
  have hptr : ∀ a, k'.ptr a = c.k.ptr a := by intro a; cases a <;> simp [CK.ptr, *]
  refine ⟨hck, h.sbNew, h.pbOld, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show m'.block? W.pb = _
    rw [hsame W.pb h.pb_ne_sb]; exact h.proof
  · show k'.proof = none ∨ _
    rw [h7]; exact h.proofPtr
  · show k'.par = none ∨ _
    rw [h6]; exact h.parPtr
  · intro a b o hp
    rw [hptr a] at hp
    obtain ⟨ho, hbs, hbb, harr⟩ := h.arr a b o hp
    refine ⟨ho, hbs, hbb, ?_⟩
    show m'.block? b = _
    rw [hsame b hbs]
    cases a <;> exact harr
  · intro a1 a2 b1 b2 o1 o2 hne p1 p2
    rw [hptr] at p1 p2
    exact h.sep a1 a2 b1 b2 o1 o2 hne p1 p2
  · intro b hlt hne
    rw [hsame b (by have := h.sbNew; omega)]
    exact h.out b hlt hne
  · intro b hge hne hno
    rw [hsame b hne]
    exact h.exact b hge hne (fun a o hp => hno a o (by rw [hptr a]; exact hp))
  · intro b hb'
    obtain ⟨h1, h2, h3⟩ := h.auxNew b hb'
    exact ⟨h1, h2, fun a o => by rw [hptr]; exact h3 a o⟩

/-! ## The rebuild loop, as pure steps -/

theorem HtabPart.mono {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap : Nat}
    {S S' : Nat → Prop} (h : HtabPart posOf pool htab hcap S)
    (hS : ∀ i, i < pool.size → S' i → S i) : HtabPart posOf pool htab hcap S' :=
  ⟨h.size, h.pow, h.cell, fun i n hn hs => h.find i n hn (hS i (lt_size_of_getElem? hn) hs)⟩

/-- The struct while the table is rebuilt in block `nb`. -/
def growK (k : CK) (nb : Nat) (cnt wk : BitVec 32) : CK :=
  { k with htab := some (nb, 0), hcap := k.hcap * 2#32, hcnt := cnt, work := wk, mem := k.mem - k.hcap * 2#32 }

/-- The rebuild after the first `i` old slots: the new table knows exactly
the nodes found there, and `hcnt` counts them. -/
def HgrowSt (m2 : Mem) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (pb nb : Nat)
    (s' : (KernelState prog State)) (i : Nat) : Prop :=
  ∃ (cnt wk : BitVec 32) (htab' : Array EmbC.Val),
    HView m2 s'.mem sb (growK c.k nb cnt wk) pb c.pool nb htab' ∧
    HtabPart posOf st.pool htab' (c.k.hcap * 2#32).toNat
      (fun x => ∃ s, s < i ∧ U c.htab s (offs st.pool x + 1)) ∧
    nzCount htab' = nzUpTo c.htab i ∧ cnt.toNat = nzUpTo c.htab i

/-- An empty old slot: nothing to do. -/
theorem HgrowSt.skip {m2 : Mem} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : St} {pb nb : Nat}
    {s' : (KernelState prog State)} {i : Nat} (h : HgrowSt m2 sb c posOf st pb nb s' i)
    (hb : offs st.pool st.pool.size < 2 ^ 32) (h0 : U c.htab i 0) :
    HgrowSt m2 sb c posOf st pb nb s' (i + 1) := by
  obtain ⟨cnt, wk, htab', hv, hpart, hnz, hcnt⟩ := h
  have hsucc : nzUpTo c.htab (i + 1) = nzUpTo c.htab i := by
    rw [nzUpTo_succ h0]; simp
  refine ⟨cnt, wk, htab', hv, hpart.mono ?_, by rw [hsucc]; exact hnz, by rw [hsucc]; exact hcnt⟩
  rintro y hy ⟨s, hs, hu⟩
  by_cases hsi : s < i
  · exact ⟨s, hsi, hu⟩
  · have : s = i := by omega
    subst this
    have := offs_lt_end hy
    have := U.inj32 hu h0 (by omega) (by decide)
    omega

/-- An occupied old slot: after `ck_hput` of its node. -/
theorem HgrowSt.put {m2 : Mem} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : St} {pb nb : Nat}
    {s'' : (KernelState prog State)} {i x : Nat} {cnt wk : BitVec 32} {htab' : Array EmbC.Val} {S : Nat → Prop}
    (hS : S = fun x => ∃ s, s < i ∧ U c.htab s (offs st.pool x + 1))
    (hnz : nzCount htab' = nzUpTo c.htab i) (hcnt : cnt.toNat = nzUpTo c.htab i)
    (hb : offs st.pool st.pool.size < 2 ^ 32) (hi : i < 2 ^ 30) (hx : x < st.pool.size)
    (hu : U c.htab i (offs st.pool x + 1))
    (hp : HputPost m2 sb (growK c.k nb cnt wk) pb c.pool nb htab' posOf st.pool S
      (BitVec.ofNat 32 (offs st.pool x)) x (some (.u32 1#32)) s'') :
    HgrowSt m2 sb c posOf st pb nb s'' (i + 1) := by
  subst hS
  obtain ⟨h0, -⟩ | ⟨-, slot, wk', hs0, hslot, hv, hpart⟩ := hp
  · simp at h0
  have hox := offs_lt_end hx
  have hne : EmbC.Val.u32 (BitVec.ofNat 32 (offs st.pool x) + 1#32) ≠ .u32 0#32 := by
    intro e
    simp only [EmbC.Val.u32.injEq] at e
    have := congrArg BitVec.toNat e
    rw [bv_add_toNat (by rw [bv_toNat_ofNat (by omega)]; simp; omega),
      bv_toNat_ofNat (by omega)] at this
    simp at this
  have hne' : EmbC.Val.u32 (BitVec.ofNat 32 (offs st.pool x + 1)) ≠ .u32 0#32 := by
    intro e
    simp only [EmbC.Val.u32.injEq] at e
    have := (ofNat32_eq_zero_iff (by omega)).mp e
    omega
  have hsucc : nzUpTo c.htab (i + 1) = nzUpTo c.htab i + 1 := by
    rw [nzUpTo_succ hu]; simp [hne']
  have hle := nzUpTo_le c.htab i
  refine ⟨cnt + 1#32, wk', _, hv, hpart.mono ?_, ?_, ?_⟩
  · rintro y hy ⟨s, hs, huy⟩
    by_cases hsi : s < i
    · exact Or.inl ⟨s, hsi, huy⟩
    · have : s = i := by omega
      subst this
      have := offs_lt_end hy
      have he := U.inj32 huy hu (by omega) (by omega)
      exact Or.inr (offs_inj (Nat.le_of_lt hy) (Nat.le_of_lt hx) (by omega))
  · rw [nzCount_set hs0 hne, hnz, hsucc]
  · rw [bv_add_toNat (by simp; omega), hsucc, hcnt]; rfl

/-! ## `ck_hgrow` -/

theorem CoreInv'.setErr {posOf : Nat → Nat} {c : CMem} {st : St} (h : CoreInv' posOf c st)
    (e : BitVec 32) : CoreInv' posOf { c with k := { c.k with err := e } } st :=
  ⟨⟨h.core.ok, h.core.poolNull, h.core.poolSize, h.core.poolCap, h.core.rep, h.core.htabPtr,
    h.core.htab, ⟨h.core.stk.null, h.core.stk.size, h.core.stk.cap⟩, h.core.posInj⟩, h.nz⟩

theorem HFrame.setErr (c : CMem) (e : BitVec 32) :
    HFrame c { c with k := { c.k with err := e } } :=
  ⟨by constructor <;> rfl, rfl, rfl, rfl, rfl⟩

theorem CoreInv'.wev {posOf : Nat → Nat} {c : CMem} {st : St} (h : CoreInv' posOf c st)
    (wk er : BitVec 32) (vl : BitVec 64) : CoreInv' posOf (c.wev wk er vl) st :=
  ⟨h.core.wev, h.nz⟩

theorem HFrame.wev (c : CMem) (wk er : BitVec 32) : HFrame c (c.wev wk er c.k.val) :=
  ⟨by constructor <;> rfl, rfl, rfl, rfl, rfl⟩

theorem HFrame.wev_setMem (c : CMem) (wk er mm : BitVec 32) :
    HFrame c ((c.wev wk er c.k.val).setMem mm) :=
  ⟨by constructor <;> rfl, rfl, rfl, rfl, rfl⟩

theorem CoreInv'.setMem {posOf : Nat → Nat} {c : CMem} {st : St} (h : CoreInv' posOf c st)
    (mm : BitVec 32) : CoreInv' posOf (c.setMem mm) st :=
  ⟨⟨h.core.ok, h.core.poolNull, h.core.poolSize, h.core.poolCap, h.core.rep, h.core.htabPtr,
    h.core.htab, ⟨h.core.stk.null, h.core.stk.size, h.core.stk.cap⟩, h.core.posInj⟩, h.nz⟩

/-- The loop invariant of `ck_hgrow`. -/
def HgrowInv (m2 : Mem) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (pb nb ob : Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (i e ok : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("old", .ptr .u32, .ptr ob 0),
      ("nt", .ptr .u32, .ptr nb 0), ("ocap", .u32, .u32 c.k.hcap),
      ("ocnt", .u32, .u32 c.k.hcnt), ("i", .u32, .u32 i), ("e", .u32, .u32 e),
      ("ok", .u32, .u32 ok)] ∧
    i.toNat ≤ c.k.hcap.toNat ∧ HgrowSt m2 sb c posOf st pb nb s' i.toNat

/-- The postcondition of `ck_hgrow`, named so that `simp` leaves it alone. -/
def HgrowPost (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St)
    (rv : Option EmbC.Val) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ HFrame c c' ∧ CoreInv' posOf c' st ∧
    (rv = some (.u32 0#32) ∨
     (rv = some (.u32 1#32) ∧ c'.k.hcap.toNat = 2 * c.k.hcap.toNat))

/-- After the body's `if`, before `i = i + 1`; or the early return when the
work budget runs out. -/
def HgrowMid (W : World) (m2 : Mem) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St)
    (pb nb ob : Nat) (i : BitVec 32) : (Post prog State) := fun o env s' =>
  match o with
  | .normal => ∃ e ok : BitVec 32,
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("old", .ptr .u32, .ptr ob 0),
      ("nt", .ptr .u32, .ptr nb 0), ("ocap", .u32, .u32 c.k.hcap),
      ("ocnt", .u32, .u32 c.k.hcnt), ("i", .u32, .u32 i), ("e", .u32, .u32 e),
      ("ok", .u32, .u32 ok)] ∧
    HgrowSt m2 sb c posOf st pb nb s' (i.toNat + 1)
  | .ret rv => rv = some (.u32 0#32) ∧ HgrowPost W sb c posOf st rv s'
  | .brk => False

theorem ck_hgrow_spec : HgrowSpec (State := State) := by
  intro W sb c posOf st
  show FnSpec _ _ _ (fun _ _ rv s' => HgrowPost W sb c posOf st rv s')
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckHgrow) rfl
  rintro vs s ⟨rfl, h, hinv, pb, hpool⟩
  simp [ckHgrow, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨ob, hhtab⟩ := hinv.core.htabPtr
  have hok := hinv.core.htab
  obtain ⟨j, hj, hj30⟩ := hok.pow
  have hrep := hinv.core.rep
  have hplen : offs st.pool st.pool.size ≤ 2 ^ 30 := by
    have h1 := hrep.len; have h2 := hinv.core.poolCap; simp only [maxPool] at h2; omega
  apply WP.seq
  apply WP.ite
  ck_simp [MAX_POOL]
  constructor
  · intro hbig
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp [ERR_LIMIT]
    intro s1 h
    apply WP.ret
    ck_simp [retPost, HgrowPost]
    exact ⟨_, h, HFrame.setErr c _, hinv.setErr _⟩
  · intro hsmall
    apply WP.skip
    have hcap30 : c.k.hcap.toNat < 2 ^ 30 := by simpa [BitVec.lt_def] using hsmall
    have hcap1 : 1 ≤ c.k.hcap.toNat := by rw [hj]; exact Nat.one_le_two_pow
    have hmul : (c.k.hcap * 2#32).toNat = 2 * c.k.hcap.toNat := by
      rw [bv_mul_toNat (by simp; omega)]; simp; omega
    -- pay for the new table
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro _
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp [ERR_LIMIT]
      intro s1 h
      apply WP.ret
      ck_simp [retPost, HgrowPost]
      exact ⟨_, h, HFrame.setErr c _, hinv.setErr _⟩
    intro _
    apply WP.skip
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s h
    obtain ⟨w1, hw1⟩ : ∃ w1, w1 = c.k.work - c.k.hcap * 2#32 := ⟨_, rfl⟩
    have h : Holds W s.mem sb (c.wev w1 c.k.err c.k.val) := by rw [hw1]; exact h
    -- pay for it from the memory budget too
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro _
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp [ERR_LIMIT]
      intro s1 h
      apply WP.ret
      ck_simp [retPost, HgrowPost]
      exact ⟨_, h, ⟨by constructor <;> rfl, rfl, rfl, rfl, rfl⟩, (hinv.wev w1 c.k.err c.k.val).setErr _⟩
    intro _
    apply WP.skip
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s h
    have h : Holds W s.mem sb ((c.wev w1 c.k.err c.k.val).setMem (c.k.mem - c.k.hcap * 2#32)) := h
    have hn64 : (BitVec.setWidth 64 c.k.hcap * 2#64).toNat = (c.k.hcap * 2#32).toNat := by
      rw [hmul, BitVec.toNat_mul, BitVec.toNat_setWidth]; simp; omega
    have hn0 : BitVec.setWidth 64 c.k.hcap * 2#64 ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [hn64, hmul] at this
      simp at this; omega
    apply WP.seq
    apply WP.ecall
    ck_simp [kvcalloc_run hn0, hn64]
    by_cases horc : (callocResponse (P := Vbcf.prog) hn0 s).1 ≠ some .null
    · simp only [ne_eq, Classical.not_not] at horc
      simp only [horc, ↓reduceIte]
      have hH := h
      have hsb := hH.sb_lt
      have hpbA := hH.poolArr hpool
      have hobA := hH.htabArr hhtab
      have hpb_lt := Mem.block?_lt hpbA
      have hob_lt := Mem.block?_lt hobA
      have hne_po : ob ≠ pb := hH.sep .htab .pool ob pb 0 0 (by decide) hhtab hpool
      have hob_sb : ob ≠ sb := (hH.arr .htab ob 0 hhtab).2.1
      have hpb_sb : pb ≠ sb := (hH.arr .pool pb 0 hpool).2.1
      -- name the new capacity, block and memory
      obtain ⟨N, hN⟩ : ∃ N, N = c.k.hcap.toNat * 2 % 4294967296 := ⟨_, rfl⟩
      have hNmul : (c.k.hcap * 2#32).toNat = N := by rw [hmul, hN]; omega
      rw [← hN]
      obtain ⟨nb, hnb⟩ : ∃ nb, nb = s.mem.blocks.size := ⟨_, rfl⟩
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = (s.mem.alloc EmbC.Ty.u32
        (Array.replicate N (EmbC.Val.u32 0#32))).snd := ⟨_, rfl⟩
      rw [← hnb, ← hm1]
      have hb1 : ∀ b, m1.block? b =
          if b = nb then some ⟨.u32, Array.replicate N (.u32 0#32)⟩ else s.mem.block? b := by
        intro b; rw [hm1, hnb]; exact Mem.block?_alloc b
      have hnew : m1.block? nb = some ⟨.u32, Array.replicate N (.u32 0#32)⟩ := by
        rw [hb1]; simp
      have hck1 : HasCK m1 sb ((c.wev w1 c.k.err c.k.val).setMem (c.k.mem - c.k.hcap * 2#32)).k := by
        show m1.block? sb = _
        rw [hb1]; simp only [show sb ≠ nb by omega, ↓reduceIte]; exact hH.ck
      have hob1 : m1.block? ob = some ⟨.u32, c.htab⟩ := by
        rw [hb1]; simp only [show ob ≠ nb by omega, ↓reduceIte]; exact hobA
      have hpb1 : m1.block? pb = some ⟨.u32, c.pool⟩ := by
        rw [hb1]; simp only [show pb ≠ nb by omega, ↓reduceIte]; exact hpbA
      clear h
      embc_simp [Mem.hasTy_ptr hnew rfl]
      apply WP.seq
      apply WP.ite
      embc_simp [hnew]
      apply WP.skip
      apply WP.seq
      apply WP.assign
      embc_simp [HasCK.ld_htab hs hck1, hhtab, Mem.hasTy_ptr hob1 rfl]
      apply WP.seq
      apply WP.assign
      embc_simp [HasCK.ld_hcap hs hck1]
      apply WP.seq
      apply WP.assign
      embc_simp [HasCK.ld_hcnt hs hck1]
      -- st->htab = nt
      have hstore : m1.storeField prog sb "htab" (.ptr nb 0) = some (m1.setCell sb 3 (.ptr nb 0)) :=
        Mem.storeField_eq (by rw [ck_slot hs hck1, fi_htab]) (Mem.hasTy_ptr hnew rfl)
          (by simp [CK.cells])
      apply WP.seq
      apply WP.setField
      embc_simp [hstore]
      obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.setCell sb 3 (.ptr nb 0) := ⟨_, rfl⟩
      rw [← hm2]
      have hb2 : ∀ b, m2.block? b =
          if b = sb then some ⟨.struct "ck", ((c.wev w1 c.k.err c.k.val).setMem (c.k.mem - c.k.hcap * 2#32)).k.cells.setIfInBounds 3 (.ptr nb 0)⟩
          else m1.block? b := by
        intro b; rw [hm2]; exact Mem.block?_setCell b hck1
      have h : HView m2 m2 sb (((c.wev w1 c.k.err c.k.val).setMem (c.k.mem - c.k.hcap * 2#32)).k.setPtr .htab (some (nb, 0))) pb c.pool nb
          (Array.replicate N (.u32 0#32)) := by
        refine ⟨?_, hpool, rfl, ?_, ?_, by omega, fun _ _ _ => rfl, rfl⟩
        · show m2.block? sb = _
          rw [hb2, CK.setPtr_cells]; simp [Arr.field]
        · show m2.block? pb = _
          rw [hb2]; simp only [hpb_sb, ↓reduceIte]; exact hpb1
        · show m2.block? nb = _
          rw [hb2]; simp only [show nb ≠ sb by omega, ↓reduceIte]; exact hnew
      have hob2 : m2.block? ob = some ⟨.u32, c.htab⟩ := by
        rw [hb2]; simp only [hob_sb, ↓reduceIte]; exact hob1
      apply WP.seq
      apply WP.hv_setField hs h (by rfl)
      hv_simp
      intro s3 h
      apply WP.seq
      apply WP.hv_setField hs h (by rfl)
      hv_simp
      intro s4 h
      have h : HView m2 s4.mem sb (growK c.k nb 0#32 w1) pb c.pool nb
          (Array.replicate N (.u32 0#32)) := h
      apply WP.seq
      apply WP.while (I := HgrowInv m2 sb c posOf st pb nb ob)
      · refine ⟨0#32, 0#32, 0#32, rfl, by simp, 0#32, w1, _, h, ?_, ?_, rfl⟩
        · rw [hNmul]
          refine (HtabPart.zero posOf st.pool ⟨j + 1, ?_, ?_⟩).mono ?_
          · rw [← hNmul, hmul, hj, Nat.pow_succ]; omega
          · have : 2 ^ j < 2 ^ 30 := by rw [← hj]; exact hcap30
            have := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp this
            omega
          · rintro y _ ⟨s0, hs0, -⟩
            exact absurd hs0 (Nat.not_lt_zero _)
        · rw [nzCount_replicate]; simp [nzUpTo_zero]
      · rintro env s' ⟨i, e, ok, rfl, hile, hst⟩
        clear h
        obtain ⟨cnt, wk, htab', h, hpart, hnz, hcnt⟩ := hst
        have hold' : HasArr s'.mem ob c.htab := by
          show s'.mem.block? ob = _
          rw [h.frame ob hob_sb (by omega)]; exact hob2
        embc_simp
        constructor
        · -- the loop is done: free the old table
          intro hge
          have hieq : i.toNat = c.k.hcap.toNat := by
            have := BitVec.le_def.mp hge; omega
          apply WP.seq
          apply WP.ecall
          embc_simp [kvfree_run hold']
          apply WP.ret
          embc_simp [retPost, HgrowPost]
          refine ⟨{ c with k := growK c.k nb cnt wk, htab := htab' }, ?_,
            ⟨by constructor <;> rfl, rfl, rfl, rfl, rfl⟩, ⟨⟨hinv.core.ok, hinv.core.poolNull,
              hinv.core.poolSize, hinv.core.poolCap, hrep, ⟨nb, rfl⟩, ?_,
              ⟨hinv.core.stk.null, hinv.core.stk.size, hinv.core.stk.cap⟩, hinv.core.posInj⟩, ?_⟩,
            hmul⟩
          · -- ownership
            have hfb := fun b => Mem.block?_free (m := s'.mem) (b := ob) b
            refine hH.swap_htab hhtab hnb ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_
            · show (s'.mem.free ob).block? sb = _
              rw [hfb]; simp only [Ne.symm hob_sb, ↓reduceIte]; exact h.ck
            · show (s'.mem.free ob).block? nb = _
              rw [hfb]; simp only [show nb ≠ ob by omega, ↓reduceIte]; exact h.htab
            · rw [hfb]; simp
            · intro b h1 h2 h3
              rw [hfb]; simp only [h3, ↓reduceIte]
              rw [h.frame b h1 h2, hb2]; simp only [h1, ↓reduceIte]
              rw [hb1]; simp only [h2, ↓reduceIte]
          · -- the new table knows every node
            have hfull := nzUpTo_size c.htab (i := i.toNat) (by rw [hok.size]; omega)
            refine hpart.toOK ?_ ?_ ?_ ?_
            · intro x hx
              obtain ⟨n, hn⟩ := node_of_lt (st := st) hx
              obtain ⟨d, hd, hu, -⟩ := hok.find x n hn
              exact ⟨_, by rw [hieq]; exact Nat.mod_lt _ (by omega), hu⟩
            · show cnt.toNat = _
              rw [hcnt, hfull, hinv.nz]; exact hok.cnt
            · show nzCount htab' = cnt.toNat
              rw [hnz, hcnt]
            · have := hok.load
              show _ ≤ (c.k.hcap * 2#32).toNat
              omega
          · show nzCount htab' = cnt.toNat
            rw [hnz, hcnt]
        · -- the loop body
          intro hlt
          have hlt' : i.toNat < c.k.hcap.toNat := by simpa [BitVec.lt_def] using hlt
          obtain ⟨e0, hu, he32, hnode⟩ := hok.cell i.toNat hlt'
          have h1 : (i + 1#32).toNat = i.toNat + 1 := bv_add_toNat (by simp; omega)
          apply WP.seq
          apply WP.assign
          embc_simp [hold'.loadArr, rd_u32 hu]
          apply WP.seq
          refine WP.mono (Q := HgrowMid W m2 sb c posOf st pb nb ob i) ?_ ?_
          · apply WP.ite
            embc_simp [ofNat32_eq_zero_iff he32]
            constructor
            · intro he0
              obtain ⟨x, hx, rfl⟩ := hnode he0
              obtain ⟨n, hn⟩ := node_of_lt (st := st) hx
              have hox := offs_lt_end hx
              apply WP.seq
              apply WP.call (ck_hput_spec m2 sb (growK c.k nb cnt wk) pb c.pool nb htab' posOf st.pool
                c.k.plen.toNat (fun x => ∃ s, s < i.toNat ∧ U c.htab s (offs st.pool x + 1))
                (BitVec.ofNat 32 (offs st.pool x)) x n)
              embc_simp [ofNat_succ_sub_one]
              refine ⟨⟨h, hrep, ?_, hpart, hn, ?_⟩, ?_⟩
              · have := hrep.len; omega
              · omega
              intro rv s'' hp
              rcases hp with ⟨rfl, wk', er', h'⟩ | ⟨rfl, hsucc⟩
              · -- the work budget ran out: put the old table back
                clear h
                have h := h'
                clear h'
                embc_simp
                apply WP.ite
                embc_simp
                apply WP.seq
                apply WP.hv_setField hs h (by rfl)
                hv_simp
                intro s3 h
                apply WP.seq
                apply WP.hv_setField hs h (by rfl)
                hv_simp
                intro s4 h
                have hold4 : HasArr s4.mem ob c.htab := by
                  show s4.mem.block? ob = _
                  rw [h.frame ob hob_sb (by omega)]; exact hob2
                have hstore : s4.mem.storeField prog sb "htab" (.ptr ob 0) =
                    some (s4.mem.setCell sb 3 (.ptr ob 0)) :=
                  Mem.storeField_eq (by rw [ck_slot hs h.ck, fi_htab]) (Mem.hasTy_ptr hold4 rfl)
                    (by simp [CK.cells])
                apply WP.seq
                apply WP.setField
                embc_simp [hstore]
                have hb5 := fun b => Mem.block?_setCell (m := s4.mem) (i := 3) (v := .ptr ob 0) b h.ck
                have hnt5 : (s4.mem.setCell sb 3 (.ptr ob 0)).block? nb = some ⟨.u32, htab'⟩ := by
                  rw [hb5]; simp only [show nb ≠ sb by omega, ↓reduceIte]; exact h.htab
                apply WP.seq
                apply WP.ecall
                embc_simp [kvfree_run (st := ⟨s4.mem.setCell sb 3 (.ptr ob 0), s4.oracle⟩) hnt5]
                apply WP.ret
                embc_simp
                refine ⟨rfl, (c.wev wk' er' c.k.val).setMem (c.k.mem - c.k.hcap * 2#32), ?_, HFrame.wev_setMem c _ _ _,
                  (hinv.wev _ _ _).setMem _, Or.inl rfl⟩
                -- only the struct differs from the memory before the allocation
                have hfb := fun b => Mem.block?_free (m := s4.mem.setCell sb 3 (.ptr ob 0)) (b := nb) b
                refine hH.frame_ck (k' := ((c.wev wk' er' c.k.val).setMem (c.k.mem - c.k.hcap * 2#32)).k) ?_ rfl ?_
                · show ((s4.mem.setCell sb 3 (.ptr ob 0)).free nb).block? sb = _
                  rw [hfb]; simp only [show sb ≠ nb by omega, ↓reduceIte]
                  rw [hb5]
                  simp [CK.cells, growK, CMem.wev, CMem.setMem, hhtab]
                · intro b hbs
                  rw [hfb]
                  by_cases hbn : b = nb
                  · subst hbn
                    simp only [↓reduceIte]
                    rw [hnb]; exact Mem.block?_size.symm
                  · simp only [hbn, ↓reduceIte]
                    rw [hb5]; simp only [hbs, ↓reduceIte]
                    rw [h.frame b hbs hbn, hb2]; simp only [hbs, ↓reduceIte]
                    rw [hb1]; simp only [hbn, ↓reduceIte]
              · embc_simp
                apply WP.ite
                embc_simp
                apply WP.skip
                exact ⟨_, _, rfl,
                  HgrowSt.put rfl hnz hcnt (by omega) (by omega) hx hu (Or.inr ⟨rfl, hsucc⟩)⟩
            · intro he0
              subst he0
              apply WP.skip
              exact ⟨_, _, rfl, HgrowSt.skip ⟨cnt, wk, htab', h, hpart, hnz, hcnt⟩ (by omega) hu⟩
          · rintro o env' s'' hq
            cases o with
            | brk => exact hq.elim
            | ret rv =>
              obtain ⟨rfl, hpost⟩ := hq
              simp only [retPost, Mem.hasTy_u32, true_and]
              exact hpost
            | normal =>
              obtain ⟨e', ok', rfl, hst'⟩ := hq
              apply WP.assign
              embc_simp
              exact ⟨_, _, _, rfl, by omega, by rw [h1]; exact hst'⟩
    · simp only [ne_eq, Classical.not_not] at horc
      simp only [horc, ↓reduceIte]
      embc_simp
      apply WP.seq
      apply WP.ite
      embc_simp
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp [ERR_NOMEM]
      intro s1 h
      apply WP.ret
      ck_simp [retPost, HgrowPost]
      exact ⟨_, h, HFrame.wev_setMem c w1 1#32 (c.k.mem - c.k.hcap * 2#32), (hinv.wev w1 1#32 c.k.val).setMem (c.k.mem - c.k.hcap * 2#32)⟩

end Vbcf.Proof
