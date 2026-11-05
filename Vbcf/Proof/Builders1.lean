import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Access
import Vbcf.Proof.Push
import Vbcf.Proof.InternBridge

/-!
# Vbcf proofs: the node builders, part 1 (pure lemmas)

No C semantics here.

* frames: `PoolFrame`/`StkFrame` are reflexive and transitive; `CoreInv` survives a
  `StkFrame` change (`CoreInv.stkFrame`);
* `TailEq c c'`: `c'` is `c` with pool cells at or beyond `plen` overwritten; `CoreInv`
  does not see such a change (`CoreInv.tailEq`);
* `wr c i x`: one pool store, the shape `WP.ck_store .pool` produces;
* `Written c st h is`: a non-leaf candidate has been written at the tail; it gives
  `CandRaw` (`Written.candRaw`) and pins down the node `ck_intern` reports (`Written.cand`);
* carrying facts across a builder call (`pushNode_offs`, `RInv.push`, `StkIds.push`, …).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## Frames -/

theorem PoolFrame.unchanged (c : CMem) : PoolFrame c c := by constructor <;> rfl

theorem PoolFrame.trans {c c' c'' : CMem} (h : PoolFrame c c') (h' : PoolFrame c' c'') :
    PoolFrame c c'' where
  stk := h'.stk.trans h.stk
  facts := h'.facts.trans h.facts
  prem := h'.prem.trans h.prem
  proof := h'.proof.trans h.proof
  stkPtr := h'.stkPtr.trans h.stkPtr
  sp := h'.sp.trans h.sp
  scap := h'.scap.trans h.scap
  factsPtr := h'.factsPtr.trans h.factsPtr
  flen := h'.flen.trans h.flen
  fcap := h'.fcap.trans h.fcap
  premPtr := h'.premPtr.trans h.premPtr
  par := h'.par.trans h.par
  proofPtr := h'.proofPtr.trans h.proofPtr
  nexpr := h'.nexpr.trans h.nexpr
  tt := h'.tt.trans h.tt
  ff := h'.ff.trans h.ff
  goal := h'.goal.trans h.goal
  val := h'.val.trans h.val
  lr := h'.lr.trans h.lr
  lrPtr := h'.lrPtr.trans h.lrPtr
  lo := h'.lo.trans h.lo
  live := h'.live.trans h.live

theorem StkFrame.refl (c : CMem) : StkFrame c c := by constructor <;> rfl

theorem StkFrame.trans {c c' c'' : CMem} (h : StkFrame c c') (h' : StkFrame c' c'') :
    StkFrame c c'' where
  pool := h'.pool.trans h.pool
  htab := h'.htab.trans h.htab
  facts := h'.facts.trans h.facts
  prem := h'.prem.trans h.prem
  proof := h'.proof.trans h.proof
  poolPtr := h'.poolPtr.trans h.poolPtr
  plen := h'.plen.trans h.plen
  pcap := h'.pcap.trans h.pcap
  htabPtr := h'.htabPtr.trans h.htabPtr
  hcap := h'.hcap.trans h.hcap
  hcnt := h'.hcnt.trans h.hcnt
  factsPtr := h'.factsPtr.trans h.factsPtr
  flen := h'.flen.trans h.flen
  fcap := h'.fcap.trans h.fcap
  premPtr := h'.premPtr.trans h.premPtr
  par := h'.par.trans h.par
  proofPtr := h'.proofPtr.trans h.proofPtr
  nexpr := h'.nexpr.trans h.nexpr
  tt := h'.tt.trans h.tt
  ff := h'.ff.trans h.ff
  goal := h'.goal.trans h.goal
  val := h'.val.trans h.val
  lr := h'.lr.trans h.lr
  lrPtr := h'.lrPtr.trans h.lrPtr
  lo := h'.lo.trans h.lo
  live := h'.live.trans h.live

/-- The one place where `CoreInv` is rebuilt for a changed C state (same Lean state):
the hash table (cells, pointer, capacity, count) and `plen` are unchanged, the pool block
is still well-formed and agrees with the old one below `plen`, and the stack is
well-formed.  Every other transfer lemma below is an instance. -/
theorem CoreInv.congr {posOf : Nat → Nat} {c c' : CMem} {st : St} (hc : CoreInv posOf c st)
    (hplen : c'.k.plen = c.k.plen)
    (hhtab : c'.htab = c.htab) (hhp : c'.k.htab = c.k.htab) (hhcap : c'.k.hcap = c.k.hcap)
    (hhcnt : c'.k.hcnt = c.k.hcnt)
    (hnull : c'.k.pool = none → c'.k.pcap = 0)
    (hsize : ∀ b o, c'.k.pool = some (b, o) → c'.pool.size = c'.k.pcap.toNat)
    (hcap : c.k.plen.toNat ≤ c'.k.pcap.toNat ∧ c'.k.pcap.toNat ≤ maxPool)
    (hcells : ∀ i, i < c.k.plen.toNat → c'.pool[i]? = c.pool[i]?)
    (hstk : StkOK c') : CoreInv posOf c' st where
  ok := hc.ok
  poolNull := hnull
  poolSize := hsize
  poolCap := by rw [hplen]; exact hcap
  rep := by rw [hplen]; exact hc.rep.congr hcells
  htabPtr := by rw [hhp]; exact hc.htabPtr
  htab := by rw [hhtab, hhcap, hhcnt]; exact hc.htab
  stk := hstk
  posInj := hc.posInj

/-- `CoreInv` survives any change confined to the scratch stack, the work counter and the
error flag, as long as the stack is still well-formed. -/
theorem CoreInv.stkFrame {posOf : Nat → Nat} {c c' : CMem} {st : St} (hc : CoreInv posOf c st)
    (hf : StkFrame c c') (hs : StkOK c') : CoreInv posOf c' st := by
  refine hc.congr hf.plen hf.htab hf.htabPtr hf.hcap hf.hcnt ?_ ?_ ?_ ?_ hs
  · rw [hf.poolPtr, hf.pcap]; exact hc.poolNull
  · rw [hf.poolPtr, hf.pool, hf.pcap]; exact hc.poolSize
  · rw [hf.pcap]; exact hc.poolCap
  · intro i _; rw [hf.pool]

/-- The transfer lemma for a change of the pool block that keeps the cells below `plen`:
used for growing the pool and for writing a candidate at its tail. -/
theorem CoreInv.poolChange {posOf : Nat → Nat} {c c' : CMem} {st : St} (hc : CoreInv posOf c st)
    (hf : PoolFrame c c') (hplen : c'.k.plen = c.k.plen)
    (hhtab : c'.htab = c.htab) (hhp : c'.k.htab = c.k.htab) (hhcap : c'.k.hcap = c.k.hcap)
    (hhcnt : c'.k.hcnt = c.k.hcnt)
    (hnull : c'.k.pool = none → c'.k.pcap = 0)
    (hsize : ∀ b o, c'.k.pool = some (b, o) → c'.pool.size = c'.k.pcap.toNat)
    (hcap : c.k.plen.toNat ≤ c'.k.pcap.toNat ∧ c'.k.pcap.toNat ≤ maxPool)
    (hcells : ∀ i, i < c.k.plen.toNat → c'.pool[i]? = c.pool[i]?) : CoreInv posOf c' st := by
  refine hc.congr hplen hhtab hhp hhcap hhcnt hnull hsize hcap hcells ⟨?_, ?_, ?_⟩
  · rw [hf.stkPtr, hf.scap]; exact hc.stk.null
  · rw [hf.stkPtr, hf.stk, hf.scap]; exact hc.stk.size
  · rw [hf.sp, hf.scap]; exact hc.stk.cap

/-- Setting the error flag changes nothing the invariant looks at. -/
theorem CoreInv.setErr {posOf : Nat → Nat} {c : CMem} {st : St} (hc : CoreInv posOf c st)
    (e : BitVec 32) : CoreInv posOf { c with k := { c.k with err := e } } st :=
  hc.congr rfl rfl rfl rfl rfl hc.poolNull hc.poolSize hc.poolCap (fun _ _ => rfl)
    ⟨hc.stk.null, hc.stk.size, hc.stk.cap⟩

theorem PoolFrame.setErr (c : CMem) (e : BitVec 32) :
    PoolFrame c { c with k := { c.k with err := e } } := by constructor <;> rfl

/-! ## The pool pointer -/

section
variable {W : World} {m : Mem} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : St}

/-- A pool with capacity has a block. -/
theorem CoreInv.poolPtr_of_pcap (hc : CoreInv posOf c st) (h : Holds W m sb c)
    (hp : 0 < c.k.pcap.toNat) : ∃ b, c.k.pool = some (b, 0) := by
  cases hpool : c.k.pool with
  | none => have := hc.poolNull hpool; rw [this] at hp; simp at hp
  | some bo =>
    obtain ⟨b, o⟩ := bo
    obtain ⟨rfl, -⟩ := h.arr .pool b o hpool
    exact ⟨b, rfl⟩

/-- A non-empty pool has a block. -/
theorem CoreInv.poolPtr_of_nonempty (hc : CoreInv posOf c st) (h : Holds W m sb c)
    (hne : 0 < st.pool.size) : ∃ b, c.k.pool = some (b, 0) := by
  apply hc.poolPtr_of_pcap h
  have h1 := hc.rep.size_le
  have h2 := hc.poolCap.1
  omega

/-- A non-empty scratch stack has a block. -/
theorem StkOK.stkPtr (hk : StkOK c) (h : Holds W m sb c) (hp : 0 < c.k.scap.toNat) :
    ∃ b, c.k.stk = some (b, 0) := by
  cases hstk : c.k.stk with
  | none => have := hk.null hstk; rw [this] at hp; simp at hp
  | some bo =>
    obtain ⟨b, o⟩ := bo
    obtain ⟨rfl, -⟩ := h.arr .stk b o hstk
    exact ⟨b, rfl⟩

end

/-! ## Changes above `plen` -/

/-- `c'` is `c` with some pool cells at or beyond `plen` overwritten. -/
structure TailEq (c c' : CMem) : Prop where
  k : c'.k = c.k
  htab : c'.htab = c.htab
  facts : c'.facts = c.facts
  stk : c'.stk = c.stk
  prem : c'.prem = c.prem
  proof : c'.proof = c.proof
  size : c'.pool.size = c.pool.size
  cells : ∀ i, i < c.k.plen.toNat → c'.pool[i]? = c.pool[i]?
  lr : c'.lr = c.lr

/-- The hash table (cells, pointer, capacity, count) is untouched. -/
def HtabSame (c c' : CMem) : Prop :=
  c'.htab = c.htab ∧ c'.k.htab = c.k.htab ∧ c'.k.hcap = c.k.hcap ∧ c'.k.hcnt = c.k.hcnt

theorem HtabSame.self (c : CMem) : HtabSame c c := ⟨rfl, rfl, rfl, rfl⟩

theorem HtabSame.trans {c c' c'' : CMem} (h : HtabSame c c') (h' : HtabSame c' c'') :
    HtabSame c c'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

theorem TailEq.refl (c : CMem) : TailEq c c :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩

theorem TailEq.trans {c c' c'' : CMem} (h : TailEq c c') (h' : TailEq c' c'') : TailEq c c'' where
  k := h'.k.trans h.k
  htab := h'.htab.trans h.htab
  facts := h'.facts.trans h.facts
  stk := h'.stk.trans h.stk
  prem := h'.prem.trans h.prem
  proof := h'.proof.trans h.proof
  size := h'.size.trans h.size
  cells := fun i hi => (h'.cells i (by rw [h.k]; exact hi)).trans (h.cells i hi)
  lr := h'.lr.trans h.lr

theorem TailEq.poolFrame {c c' : CMem} (h : TailEq c c') : PoolFrame c c' := by
  have hk := h.k
  constructor <;> first | exact h.stk | exact h.facts | exact h.prem | exact h.proof | exact h.lr | rw [hk]

theorem TailEq.htabSame {c c' : CMem} (h : TailEq c c') : HtabSame c c' := by
  have hk := h.k
  exact ⟨h.htab, by rw [hk], by rw [hk], by rw [hk]⟩

/-- **`CoreInv` is insensitive to the pool cells at or above `plen`.** -/
theorem CoreInv.tailEq {posOf : Nat → Nat} {c c' : CMem} {st : St} (hc : CoreInv posOf c st)
    (h : TailEq c c') : CoreInv posOf c' st := by
  have hk := h.k
  refine hc.poolChange h.poolFrame (by rw [hk]) h.htab (by rw [hk]) (by rw [hk]) (by rw [hk])
    ?_ ?_ ?_ h.cells
  · rw [hk]; exact hc.poolNull
  · rw [hk, h.size]; exact hc.poolSize
  · rw [hk]; exact hc.poolCap

/-- One store into the pool: the state `WP.ck_store .pool` produces. -/
def wr (c : CMem) (i : Nat) (x : BitVec 32) : CMem :=
  { c with pool := c.pool.setIfInBounds i (.u32 x) }

section
variable {c : CMem} {i j : Nat} {x : BitVec 32}

@[simp] theorem wr_k : (wr c i x).k = c.k := rfl
@[simp] theorem wr_stk : (wr c i x).stk = c.stk := rfl
@[simp] theorem wr_htab : (wr c i x).htab = c.htab := rfl
@[simp] theorem wr_facts : (wr c i x).facts = c.facts := rfl
@[simp] theorem wr_prem : (wr c i x).prem = c.prem := rfl
@[simp] theorem wr_proof : (wr c i x).proof = c.proof := rfl
@[simp] theorem wr_size : (wr c i x).pool.size = c.pool.size := by simp [wr]

theorem wr_get_self (hi : i < c.pool.size) : (wr c i x).pool[i]? = some (.u32 x) := by
  simp [wr, hi]

theorem wr_get_ne (hne : i ≠ j) : (wr c i x).pool[j]? = c.pool[j]? := by
  simp [wr, hne]

theorem TailEq.wr (hi : c.k.plen.toNat ≤ i) : TailEq c (wr c i x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, wr_size, fun j hj => wr_get_ne (by omega), rfl⟩

/-- A store of the word `w` (as a 32-bit value) makes the cell hold `w`. -/
theorem U_wr_self {w : Nat} (hi : i < c.pool.size) (hx : x = BitVec.ofNat 32 w) :
    U (wr c i x).pool i w := by
  unfold U; rw [wr_get_self hi, hx]

theorem U_wr_ne {w : Nat} (h : U c.pool j w) (hne : i ≠ j) : U (wr c i x).pool j w := by
  unfold U; rw [wr_get_ne hne]; exact h

end

theorem U_inj {cells : Array EmbC.Val} {i a b : Nat} (ha : U cells i a) (hb : U cells i b)
    (hal : a < 2 ^ 32) (hbl : b < 2 ^ 32) : a = b := by
  unfold U at ha hb
  rw [ha] at hb
  simp only [Option.some.injEq, Val.u32.injEq] at hb
  exact (bv_ofNat_inj hal hbl).mp hb

/-- `TailEq` keeps what is stored below `plen`… -/
theorem TailEq.U_lt {c c' : CMem} (h : TailEq c c') {i w : Nat} (hu : U c.pool i w)
    (hi : i < c.k.plen.toNat) : U c'.pool i w := by
  unfold U; rw [h.cells i hi]; exact hu

/-! ## Header words -/

theorem nat_or_hdr {h n : Nat} (hh : h / 256 % 256 = 0) (hn : n < 256) :
    h ||| n <<< 8 = h + n * 256 := by
  have e1 := @Nat.or_mod_two_pow h (n <<< 8) 8
  have e2 := @Nat.or_div_two_pow h (n <<< 8) 8
  have e3 := @Nat.or_mod_two_pow (h / 2 ^ 8) (n <<< 8 / 2 ^ 8) 8
  have e4 := @Nat.or_div_two_pow h (n <<< 8) 16
  rw [Nat.shiftLeft_eq] at *
  simp only [Nat.reducePow] at *
  have a1 : n * 256 % 256 = 0 := by omega
  have a2 : n * 256 / 256 % 256 = n := by omega
  have a3 : n * 256 / 65536 = 0 := by omega
  rw [a1, Nat.or_zero] at e1
  rw [← e2, a2, hh, Nat.zero_or] at e3
  rw [a3, Nat.or_zero] at e4
  omega

theorem nat_or_par {h p : Nat} (hh : h < 65536) : h ||| p <<< 16 = h + p * 65536 := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 16) (by simpa using hh), Nat.shiftLeft_eq]
  omega

/-- `hdr | (n << 8)`, the header a builder writes. -/
theorem bv_or_arity {h n : BitVec 32} (hh : h.toNat / 256 % 256 = 0) (hn : n.toNat < 256) :
    h ||| n <<< 8 = BitVec.ofNat 32 (h.toNat + n.toNat * 256) := by
  have hlt := h.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, bv_toNat_ofNat (by omega)]
  have : n.toNat <<< 8 % 2 ^ 32 = n.toNat <<< 8 := by
    rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  rw [this, nat_or_hdr hh hn]

theorem bv_or_256 {h : BitVec 32} (hh : h.toNat / 256 % 256 = 0) :
    h ||| 256#32 = BitVec.ofNat 32 (h.toNat + 1 * 256) :=
  bv_or_arity (n := 1#32) hh (by decide)

theorem bv_or_512 {h : BitVec 32} (hh : h.toNat / 256 % 256 = 0) :
    h ||| 512#32 = BitVec.ofNat 32 (h.toNat + 2 * 256) :=
  bv_or_arity (n := 2#32) hh (by decide)

theorem bv_or_768 {h : BitVec 32} (hh : h.toNat / 256 % 256 = 0) :
    h ||| 768#32 = BitVec.ofNat 32 (h.toNat + 3 * 256) :=
  bv_or_arity (n := 3#32) hh (by decide)

theorem not_leaf_of_code {op : Op} (h1 : opC op ≠ 0x18) (h2 : opC op ≠ 0x19) (h3 : opC op ≠ 0x08)
    (h4 : opC op ≠ 0x09) : ¬ IsLeaf op := by
  cases op <;> simp_all [opC, isLeaf]

/-- A well-formed node whose operator is a leaf has no arguments. -/
theorem leaf_args_of_typed {st : St} {n : Node}
    (ht : Typed st n) (hl : IsLeaf n.op) : n.args = #[] := by
  obtain ⟨argTys, t, hr, hlen⟩ := ht.shape
  have := resultTy_leaf hl hr
  subst this
  exact Array.eq_empty_of_size_eq_zero hlen.symm

/-- A node that `pushNode` accepts and whose operator is a leaf has no arguments
(refinement proof). -/
theorem leaf_args_of_pushNode {st st' : St} {n : Node} {r : Nat}
    (hp : pushNode st n = some (st', r)) (hl : IsLeaf n.op) : n.args = #[] :=
  leaf_args_of_typed (typed_iff_pushNode.mpr (by rw [hp]; rfl)) hl

/-! ## A non-leaf candidate at the tail of the pool -/

/-- The cells from `plen` on hold the header `h + is.length * 256` followed by the ids
of the Lean indices `is`, and they are inside the allocated pool. -/
structure Written (c : CMem) (st : St) (h : Nat) (is : List Nat) : Prop where
  hdr : U c.pool c.k.plen.toNat (h + is.length * 256)
  args : ∀ (j i : Nat), is[j]? = some i →
    i < st.pool.size ∧ U c.pool (c.k.plen.toNat + 1 + j) (offs st.pool i)
  room : c.k.plen.toNat + 1 + is.length ≤ c.k.pcap.toNat
  len : is.length < 256

theorem NonLeafHdr.add_lt {h k : Nat} (hnl : NonLeafHdr h) (hk : k < 256) :
    h + k * 256 < 2 ^ 32 := by
  obtain ⟨h1, h2, -⟩ := hnl
  omega

theorem Written.candRaw {posOf : Nat → Nat} {c : CMem} {st : St} {h : Nat} {is : List Nat}
    (hw : Written c st h is) (hnl : NonLeafHdr h) : CandRaw posOf c st := by
  have hlen := hw.len
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnl
  have hc : (h + is.length * 256) % 256 = h % 256 := by omega
  have hl : (h + is.length * 256) / 256 % 256 = is.length := by omega
  refine ⟨h + is.length * 256, by omega, hw.hdr, ?_, ?_, ?_, ?_⟩
  · rw [hl]; exact hw.room
  · rw [hc]; intro hv; rcases hv with hv | hv <;> contradiction
  · rw [hc]; intro hv; contradiction
  · rw [hl]
    intro _ _ _ _ k hk
    obtain ⟨hi, hu⟩ := hw.args k is[k] (by simp)
    exact ⟨is[k], hi, hu⟩

/-- The candidate `ck_intern` reports is the node that was written. -/
theorem Written.cand {posOf : Nat → Nat} {c : CMem} {st : St} {h : Nat} {is : List Nat} {n : Node}
    (hw : Written c st h is) (hnl : NonLeafHdr h) (hinv : CoreInv posOf c st)
    (hc : Cand posOf c st n) : hdrW n = h + is.length * 256 ∧ n.args = is.toArray := by
  have hlen := hw.len
  have hfit := hc.fits
  have hH := hnl.add_lt hlen
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnl
  -- the header
  have hh : hdrW n = h + is.length * 256 :=
    U_inj (by simpa using hc.words 0 (hdrW n) rfl) hw.hdr (hdrW_lt hfit) hH
  have hcode := hdrW_code hfit
  have hlenW := hdrW_len hfit
  rw [hh] at hcode hlenW
  have hnleaf : ¬ IsLeaf n.op :=
    not_leaf_of_code (by omega) (by omega) (by omega) (by omega)
  have hsz : n.args.size = is.length := by
    rw [← tailLen_of_not_leaf hnleaf]; omega
  have hargs : ∀ a ∈ n.args, a < st.pool.size := by
    simpa only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] using hc.args
  refine ⟨hh, ?_⟩
  apply Array.ext
  · simpa using hsz
  · intro k hk1 hk2
    have hk2' : k < is.length := by simpa using hk2
    obtain ⟨hi, hu⟩ := hw.args k is[k] (by simp)
    have hu' : U c.pool (c.k.plen.toNat + 1 + k) (offs st.pool n.args[k]) := by
      have := hc.words (k + 1) (offs st.pool n.args[k])
        (by rw [nodeW_getElem?_succ]; exact tailW_getElem?_of_not_leaf hnleaf hk1)
      rw [Nat.add_assoc, Nat.add_comm 1 k]; exact this
    have ha : n.args[k] < st.pool.size := hargs _ (by simp)
    have e := U_inj hu' hu (by have := hinv.off_lt ha; omega) (by have := hinv.off_lt hi; omega)
    have := offs_inj (Nat.le_of_lt ha) (Nat.le_of_lt hi) e
    simpa using this

/-! ### The fixed-arity cases -/

theorem Written.of1 {c : CMem} {st : St} {h ia : Nat}
    (hh : U c.pool c.k.plen.toNat (h + 1 * 256))
    (h0 : U c.pool (c.k.plen.toNat + 1) (offs st.pool ia)) (hia : ia < st.pool.size)
    (hroom : c.k.plen.toNat + 2 ≤ c.k.pcap.toNat) : Written c st h [ia] := by
  refine ⟨hh, ?_, hroom, by simp⟩
  intro j i hj
  match j with
  | 0 => simp at hj; subst hj; exact ⟨hia, h0⟩
  | j + 1 => simp at hj

theorem Written.of2 {c : CMem} {st : St} {h ia ib : Nat}
    (hh : U c.pool c.k.plen.toNat (h + 2 * 256))
    (h0 : U c.pool (c.k.plen.toNat + 1) (offs st.pool ia)) (hia : ia < st.pool.size)
    (h1 : U c.pool (c.k.plen.toNat + 2) (offs st.pool ib)) (hib : ib < st.pool.size)
    (hroom : c.k.plen.toNat + 3 ≤ c.k.pcap.toNat) : Written c st h [ia, ib] := by
  refine ⟨hh, ?_, hroom, by simp⟩
  intro j i hj
  match j with
  | 0 => simp at hj; subst hj; exact ⟨hia, h0⟩
  | 1 => simp at hj; subst hj; exact ⟨hib, h1⟩
  | j + 2 => simp at hj

theorem Written.of3 {c : CMem} {st : St} {h ia ib id : Nat}
    (hh : U c.pool c.k.plen.toNat (h + 3 * 256))
    (h0 : U c.pool (c.k.plen.toNat + 1) (offs st.pool ia)) (hia : ia < st.pool.size)
    (h1 : U c.pool (c.k.plen.toNat + 2) (offs st.pool ib)) (hib : ib < st.pool.size)
    (h2 : U c.pool (c.k.plen.toNat + 3) (offs st.pool id)) (hid : id < st.pool.size)
    (hroom : c.k.plen.toNat + 4 ≤ c.k.pcap.toNat) : Written c st h [ia, ib, id] := by
  refine ⟨hh, ?_, hroom, by simp⟩
  intro j i hj
  match j with
  | 0 => simp at hj; subst hj; exact ⟨hia, h0⟩
  | 1 => simp at hj; subst hj; exact ⟨hib, h1⟩
  | 2 => simp at hj; subst hj; exact ⟨hid, h2⟩
  | j + 3 => simp at hj

/-- `ck_intern`'s postcondition, as a named predicate (so that `simp` leaves it alone). -/
def InternPost (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
    ((r = noid ∧ CoreInv posOf c' st) ∨
     (∃ n st' i, Cand posOf c st n ∧ pushNode st n = some (st', i) ∧
        CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid))

/-! ## Structural contracts of `ck_intern` and of the builders

Each postcondition has the common shape `BuildPost … P`: memory ownership
(`Holds`), only the pool, the hash table and the error flag change
(`PoolFrame`), and either the call failed (`NOID`; the C state still represents
the ghost pool) or `P st' i` holds of the new ghost pool `st'` and returned index
`i`, the C state represents `st'` (`CoreInv`: pool image, hash table, capacity),
and the returned word is the C id of `i`.  `P` describes the interned node
structurally (`Interned`); no executable interning function occurs. -/

/-- The common shape of the builders' postconditions. -/
def BuildPost (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St)
    (P : St → Nat → Prop) : Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
    ((r = noid ∧ CoreInv posOf c' st) ∨
     (∃ st' i, P st' i ∧ CoreInv posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid))

theorem BuildPost.mono {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : St}
    {P Q : St → Nat → Prop} {rv : Option EmbC.Val} {s' : (KernelState prog State)} (h : BuildPost W sb c posOf st P rv s')
    (hPQ : ∀ st' i, P st' i → Q st' i) : BuildPost W sb c posOf st Q rv s' := by
  obtain ⟨c', r, hrv, h', hf, hres⟩ := h
  refine ⟨c', r, hrv, h', hf, ?_⟩
  rcases hres with hfail | ⟨st', i, hP, hrest⟩
  · exact Or.inl hfail
  · exact Or.inr ⟨st', i, hPQ st' i hP, hrest⟩

/-- `ck_intern`'s structural postcondition: some candidate `n` written at the tail
of the pool was interned. -/
def InternPostD (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) :
    Option EmbC.Val → (KernelState prog State) → Prop :=
  BuildPost W sb c posOf st (fun st' i => ∃ n, Cand posOf c st n ∧ Interned st n st' i)

/-- The structural specification of `ck_intern`. -/
def InternSpecD : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_intern"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧ CandRaw posOf c st)
      (fun _ _ => InternPostD W sb c posOf st)

/-- A builder called with header `h` (code and parameters, arity bits zero) and the
ids of the indices `is`: the node interned has that header, those children, and fits
the encoding. -/
def MkPostD (posOf : Nat → Nat) (W : World) (sb : Nat) (c : CMem) (st : St) (h : Nat)
    (is : List Nat) : Option EmbC.Val → (KernelState prog State) → Prop :=
  BuildPost W sb c posOf st (fun st' i => ∃ n, hdrW n = h + is.length * 256 ∧ Fits posOf n ∧
    n.args = is.toArray ∧ Interned st n st' i)

def DMk1Spec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h a : BitVec 32) (ia : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk1"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 a] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        NonLeafHdr h.toNat ∧ ia < st.pool.size ∧ a.toNat = offs st.pool ia)
      (fun _ _ => MkPostD posOf W sb c st h.toNat [ia])

def DMk2Spec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h a b : BitVec 32)
    (ia ib : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk2"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 a, .u32 b] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ NonLeafHdr h.toNat ∧
        ia < st.pool.size ∧ a.toNat = offs st.pool ia ∧ ib < st.pool.size ∧ b.toNat = offs st.pool ib)
      (fun _ _ => MkPostD posOf W sb c st h.toNat [ia, ib])

def DMk3Spec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h a b d : BitVec 32)
    (ia ib id : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mk3"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 a, .u32 b, .u32 d] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ NonLeafHdr h.toNat ∧
        ia < st.pool.size ∧ a.toNat = offs st.pool ia ∧ ib < st.pool.size ∧ b.toNat = offs st.pool ib ∧
        id < st.pool.size ∧ d.toNat = offs st.pool id)
      (fun _ _ => MkPostD posOf W sb c st h.toNat [ia, ib, id])

/-- `mkn(st, hdr, base, n)`: the arguments are `stk[base..base+n)`. -/
def DMknSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (h base n : BitVec 32)
    (is : List Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "mkn"
      (fun vs s => vs = [.ptr sb 0, .u32 h, .u32 base, .u32 n] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ NonLeafHdr h.toNat ∧ is.length = n.toNat ∧
        base.toNat + n.toNat ≤ c.k.sp.toNat ∧ StkIdsC c st base.toNat is)
      (fun _ _ => MkPostD posOf W sb c st h.toNat is)

/-- `mk0(st, hdr)` for a boolean literal header interns the literal `b`. -/
def DMk0BoolSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (b : Bool),
    EmbC.FnSpec (State := State) Vbcf.prog "mk0"
      (fun vs s => vs = [.ptr sb 0, .u32 (if b then 0x10009#32 else 0x9#32)] ∧
        Holds W s.mem sb c ∧ CoreInv posOf c st)
      (fun _ _ => BuildPost W sb c posOf st (fun st' i => Interned st ⟨.boolVal b, #[]⟩ st' i))

/-- `mkval(st, w, v)` interns the literal `bvVal w v`, with `v` truncated to its low
word when `w ≤ 32` (what the C stores). -/
def DMkvalSpec' : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (w : BitVec 32) (v : BitVec 64),
    EmbC.FnSpec (State := State) Vbcf.prog "mkval"
      (fun vs s => vs = [.ptr sb 0, .u32 w, .u64 v] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st)
      (fun _ _ => BuildPost W sb c posOf st (fun st' i => Interned st ⟨.bvVal w.toNat
        (if w.toNat ≤ 32 then v.toNat % 2 ^ 32 else v.toNat), #[]⟩ st' i))

/-- `mkval(st, w, v)` for a value that fits one word when `w ≤ 32`. -/
def DMkvalSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (w : BitVec 32) (v : BitVec 64),
    EmbC.FnSpec (State := State) Vbcf.prog "mkval"
      (fun vs s => vs = [.ptr sb 0, .u32 w, .u64 v] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        (w.toNat ≤ 32 → v.toNat < 2 ^ 32))
      (fun _ _ => BuildPost W sb c posOf st (fun st' i => Interned st ⟨.bvVal w.toNat v.toNat, #[]⟩ st' i))

/-- From `ck_intern`'s postcondition to a builder's (`MkPostD`). -/
theorem mk_finish {posOf : Nat → Nat} {W : World} {sb : Nat} {c c1 : CMem} {st : St} {h : Nat}
    {is : List Nat} {rv : Option EmbC.Val} {s' : (KernelState prog State)}
    (hfr : PoolFrame c c1) (hw : Written c1 st h is) (hnl : NonLeafHdr h)
    (hinv : CoreInv posOf c1 st) (hpost : InternPostD W sb c1 posOf st rv s') :
    MkPostD posOf W sb c st h is rv s' := by
  obtain ⟨c', r, hrv, hh, hf, hres⟩ := hpost
  refine ⟨c', r, hrv, hh, hfr.trans hf, ?_⟩
  rcases hres with hfail | ⟨st', i, ⟨n, hc, hp⟩, hinv', hr, hne⟩
  · exact Or.inl hfail
  · obtain ⟨e1, e2⟩ := hw.cand hnl hinv hc
    exact Or.inr ⟨st', i, ⟨n, e1, hc.fits, e2, hp⟩, hinv', hr, hne⟩

/-! ### The refinement proof's builder contracts, from the structural ones -/

/-- `ck_intern`'s refinement contract gives the structural one. -/
theorem InternSpecD.of_spec (hI : InternSpec (State := State)) : InternSpecD (State := State) := by
  intro W sb c posOf st
  refine FnSpec.conseq (hI W sb c posOf st) (fun _ _ hp => hp) ?_
  rintro vs s rv s' ⟨-, -, hinv, -⟩ ⟨c', r, hrv, h', hf, hres⟩
  refine ⟨c', r, hrv, h', hf, ?_⟩
  rcases hres with hfail | ⟨n, st', i, hc, hp, hrest⟩
  · exact Or.inl hfail
  · exact Or.inr ⟨st', i, ⟨n, hc, Interned.of_pushNode hinv.ok hp⟩, hrest⟩

theorem MkPostD.toMkPost {posOf : Nat → Nat} {W : World} {sb : Nat} {c : CMem} {st : St} {h : Nat}
    {is : List Nat} {rv : Option EmbC.Val} {s' : (KernelState prog State)} (hok : PoolOK st)
    (hp : MkPostD posOf W sb c st h is rv s') : MkPost posOf W sb c st h is rv s' := by
  obtain ⟨c', r, hrv, h', hf, hres⟩ := hp
  refine ⟨c', r, hrv, h', hf, ?_⟩
  rcases hres with hfail | ⟨st', i, ⟨n, e1, e2, e3, hn⟩, hrest⟩
  · exact Or.inl hfail
  · exact Or.inr ⟨n, st', i, e1, e2, e3, hn.pushNode_eq hok, hrest⟩

theorem DMk1Spec.old (h : DMk1Spec (State := State)) : Mk1Spec (State := State) := fun W sb c posOf st hd a ia =>
  FnSpec.conseq (h W sb c posOf st hd a ia) (fun _ _ hp => hp)
    (fun _ _ _ _ hp hq => MkPostD.toMkPost hp.2.2.1.ok hq)

theorem DMk2Spec.old (h : DMk2Spec (State := State)) : Mk2Spec (State := State) := fun W sb c posOf st hd a b ia ib =>
  FnSpec.conseq (h W sb c posOf st hd a b ia ib) (fun _ _ hp => hp)
    (fun _ _ _ _ hp hq => MkPostD.toMkPost hp.2.2.1.ok hq)

theorem DMk3Spec.old (h : DMk3Spec (State := State)) : Mk3Spec (State := State) := fun W sb c posOf st hd a b d ia ib id =>
  FnSpec.conseq (h W sb c posOf st hd a b d ia ib id) (fun _ _ hp => hp)
    (fun _ _ _ _ hp hq => MkPostD.toMkPost hp.2.2.1.ok hq)

theorem DMknSpec.old (h : DMknSpec (State := State)) : MknSpec (State := State) := fun W sb c posOf st hd base n is =>
  FnSpec.conseq (h W sb c posOf st hd base n is) (fun _ _ hp => hp)
    (fun _ _ _ _ hp hq => MkPostD.toMkPost hp.2.2.1.ok hq)

theorem DMk0BoolSpec.old (h : DMk0BoolSpec (State := State)) : Mk0BoolSpec (State := State) := fun W sb c posOf st b =>
  FnSpec.conseq (h W sb c posOf st b) (fun _ _ hp => hp) (by
    rintro vs s rv s' ⟨-, -, hinv⟩ ⟨c', r, hrv, h', hf, hres⟩
    refine ⟨c', r, hrv, h', hf, ?_⟩
    rcases hres with hfail | ⟨st', i, hn, hrest⟩
    · exact Or.inl hfail
    · exact Or.inr ⟨st', i, hn.pushNode_eq hinv.ok, hrest⟩)

theorem DMkvalSpec.old (h : DMkvalSpec (State := State)) : MkvalSpec (State := State) := fun W sb c posOf st w v =>
  FnSpec.conseq (h W sb c posOf st w v) (fun _ _ hp => hp) (by
    rintro vs s rv s' ⟨-, -, hinv, -⟩ ⟨c', r, hrv, h', hf, hres⟩
    refine ⟨c', r, hrv, h', hf, ?_⟩
    rcases hres with hfail | ⟨st', i, hn, hrest⟩
    · exact Or.inl hfail
    · exact Or.inr ⟨st', i, hn.pushNode_eq hinv.ok, hrest⟩)

/-! ## Leaf candidates -/

/-- The candidate reported for a `BOOL_VAL` header. -/
theorem cand_boolVal {posOf : Nat → Nat} {c : CMem} {st : St} {n : Node} {b : Bool}
    (hu : U c.pool c.k.plen.toNat (if b then 0x10009 else 0x9))
    (hc : Cand posOf c st n) (hty : Typed st n) : n = ⟨.boolVal b, #[]⟩ := by
  have hfit := hc.fits
  have hh : hdrW n = (if b then 0x10009 else 0x9) :=
    U_inj (by simpa using hc.words 0 (hdrW n) rfl) hu (hdrW_lt hfit) (by cases b <;> decide)
  have hcode := hdrW_code hfit
  have hlo := hdrW_lo hfit
  rw [hh] at hcode hlo
  have h9 : opC n.op = 0x09 := by rw [← hcode]; cases b <;> rfl
  obtain ⟨b', hb'⟩ := opC_boolVal_iff.mp h9
  have hargs := leaf_args_of_typed hty (by rw [hb']; rfl)
  rcases n with ⟨op, args⟩
  simp only at hb' hargs hlo
  subst hb' hargs
  cases b <;> cases b' <;> simp [opLo] at hlo ⊢

/-- The candidate reported for a `BV_VAL` header of width `w` followed by the low word
of `v` and, for a wide literal, its high word. -/
theorem cand_bvVal {posOf : Nat → Nat} {c : CMem} {st : St} {n : Node} {w v : Nat}
    (hw2 : w ≤ 64) (hv : v < 2 ^ 64)
    (hu : U c.pool c.k.plen.toNat (8 + (w + 31) / 32 * 256 + w * 65536))
    (h1 : U c.pool (c.k.plen.toNat + 1) (v % 2 ^ 32))
    (h2 : 32 < w → U c.pool (c.k.plen.toNat + 2) (v / 2 ^ 32))
    (hc : Cand posOf c st n) (hty : Typed st n) :
    n = ⟨.bvVal w (if w ≤ 32 then v % 2 ^ 32 else v), #[]⟩ := by
  have hq : (w + 31) / 32 ≤ 2 := by omega
  generalize (w + 31) / 32 = q at hu hq
  have hfit := hc.fits
  have hh : hdrW n = 8 + q * 256 + w * 65536 :=
    U_inj (by simpa using hc.words 0 (hdrW n) rfl) hu (hdrW_lt hfit) (by omega)
  have hcode := hdrW_code hfit
  have hlo := hdrW_lo hfit
  rw [hh] at hcode hlo
  have h8 : opC n.op = 0x08 := by omega
  obtain ⟨w', v', hop⟩ := opC_bvVal_iff.mp h8
  have hargs := leaf_args_of_typed hty (by rw [hop]; rfl)
  obtain ⟨argTys, t, hr, -⟩ := hty.shape
  have htail := hfit.tail
  have hwords := hc.words
  rcases n with ⟨op, args⟩
  simp only at hop hargs hlo hr htail hwords
  subst hop hargs
  obtain ⟨-, -, hv'⟩ := resultTy_bvVal hr
  have hww : w' = w := by simp only [opLo] at hlo; omega
  subst hww
  have hw1 := hwords 1
  simp only [nodeW_getElem?_succ, tailW] at hw1 htail
  by_cases h32 : w' ≤ 32
  · simp only [h32, ↓reduceIte] at hw1 htail ⊢
    have e := U_inj (by simpa using hw1 (v' % 2 ^ 32) rfl) h1 (by omega) (by omega)
    have : 2 ^ w' ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) h32
    rw [Nat.mod_eq_of_lt (by omega)] at e
    rw [e]
  · simp only [h32, ↓reduceIte] at hw1 htail ⊢
    have e := U_inj (by simpa using hw1 (v' % 2 ^ 32) rfl) h1 (by omega) (by omega)
    have hw2' := hwords 2 (v' / 2 ^ 32) (by simp [tailW, h32])
    have hlt : v' / 2 ^ 32 < 2 ^ 32 := htail _ (by simp)
    have e2 := U_inj hw2' (h2 (by omega)) hlt (by omega)
    have : v' = v := by omega
    rw [this]

/-! ## Carrying facts across a builder call

A rule that calls a builder continues with the returned state: `PoolFrame c c'` and
`CoreInv posOf c' st'` (plus `pushNode st n = some (st', i)`) are enough. -/

theorem pushNode_size_le {st st' : St} {n : Node} {r : Nat} (hp : pushNode st n = some (st', r)) :
    st.pool.size ≤ st'.pool.size := by
  rcases pushNode_pool hp with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  · exact Nat.le_refl _
  · simp

/-- Ids of existing nodes do not change. -/
theorem pushNode_offs {st st' : St} {n : Node} {r : Nat} (hp : pushNode st n = some (st', r))
    {i : Nat} (hi : i ≤ st.pool.size) : offs st'.pool i = offs st.pool i := by
  rcases pushNode_pool hp with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  exact offs_push n hi

theorem pushNode_lt {st st' : St} {n : Node} {r : Nat} (hp : pushNode st n = some (st', r)) :
    r < st'.pool.size := lt_size_of_getElem? (pushNode_at hp)

theorem PremsAt.ext {c c' : CMem} {st st' : VSt} {prems : List Nat}
    (h : PremsAt c st prems) (hf : PoolFrame c c') (he : VExt st st') :
    PremsAt c' st' prems := by
  refine ⟨h.1, fun j p hj => ?_⟩
  obtain ⟨hi, hu⟩ := h.2 j p hj
  refine ⟨he.lt hi, ?_⟩
  rw [hf.prem, he.id hi]; exact hu

theorem ParamsAt.frame {W : World} {c c' : CMem} {params : List Nat} (h : ParamsAt W c params)
    (hf : PoolFrame c c') : ParamsAt W c' params := by
  obtain ⟨hl, o, hpar, hsz, hcell⟩ := h
  refine ⟨hl, o, by rw [hf.par]; exact hpar, by rw [hf.proof]; exact hsz, ?_⟩
  rw [hf.proof]; exact hcell

theorem StepFrame.ofPoolFrame {c c' : CMem} (hf : PoolFrame c c') : StepFrame c c' :=
  ⟨hf.facts, hf.factsPtr, hf.flen, hf.fcap, hf.proof, hf.nexpr, hf.lr, hf.lrPtr, hf.lo, hf.live⟩

/-- The rule invariant holds again after a successful builder call, for an
extension of the view. -/
theorem RInv.build {W : World} {X : Ctx} {m : Mem} {sb : Nat} {c c' : CMem} {st st' : VSt}
    (hinv : RInv W X c st) (h' : Holds W m sb c') (hf : PoolFrame c c')
    (hc' : CoreInv X.posOf c' st'.cs) (he : VExt st st')
    (hfits : ∀ (i : Nat) (n : Node), st'.pool[i]? = some n → Fits X.posOf n) : RInv W X c' st' := by
  have htt := hinv.tt.1
  refine
    { core := ⟨hc', hfits⟩
      poolPtr := hc'.poolPtr_of_nonempty h' (by have := st'.σ_lt (he.lt htt); omega)
      ttNode := he.get hinv.ttNode
      ffNode := he.get hinv.ffNode
      tt := ⟨he.lt hinv.tt.1, by rw [hf.tt, he.id hinv.tt.1]; exact hinv.tt.2⟩
      ff := ⟨he.lt hinv.ff.1, by rw [hf.ff, he.id hinv.ff.1]; exact hinv.ff.2⟩
      goal := ⟨he.lt hinv.goal.1, by rw [hf.goal, he.id hinv.goal.1]; exact hinv.goal.2⟩
      proofPtr := by rw [hf.proofPtr]; exact hinv.proofPtr
      nexpr := by rw [hf.nexpr, hf.proof]; exact hinv.nexpr
      nexprBound := by rw [hf.nexpr]; exact hinv.nexprBound
      ei := ?_
      eiOut := by rw [hf.nexpr]; exact hinv.eiOut
      premPtr := by rw [hf.premPtr]; exact hinv.premPtr
      premSize := by rw [hf.prem]; exact hinv.premSize
      premCells := by rw [hf.prem]; exact hinv.premCells
      floor := fun S0 h0 => (hinv.floor S0 h0).trans he }
  intro p hpn
  rw [hf.nexpr] at hpn
  obtain ⟨v, hv, hu, hm⟩ := hinv.ei p hpn
  refine ⟨v, hv, by rw [hf.proof]; exact hu, ?_⟩
  cases he' : X.ei p with
  | none => rw [he'] at hm; exact hm
  | some i =>
    rw [he'] at hm
    exact ⟨he.lt hm.1, by rw [he.id hm.1]; exact hm.2⟩

/-! ### …and across a change of the scratch stack (`push`, `push_args`) -/

theorem StepFrame.refl (c : CMem) : StepFrame c c := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem StepFrame.trans {c c' c'' : CMem} (h : StepFrame c c') (h' : StepFrame c' c'') :
    StepFrame c c'' :=
  ⟨h'.facts.trans h.facts, h'.factsPtr.trans h.factsPtr, h'.flen.trans h.flen,
    h'.fcap.trans h.fcap, h'.proof.trans h.proof, h'.nexpr.trans h.nexpr, h'.lr.trans h.lr,
    h'.lrPtr.trans h.lrPtr, h'.lo.trans h.lo, h'.live.trans h.live⟩

theorem StepFrame.ofStkFrame {c c' : CMem} (hf : StkFrame c c') : StepFrame c c' :=
  ⟨hf.facts, hf.factsPtr, hf.flen, hf.fcap, hf.proof, hf.nexpr, hf.lr, hf.lrPtr, hf.lo, hf.live⟩

theorem PremsAt.stkFrame {c c' : CMem} {st : VSt} {prems : List Nat} (h : PremsAt c st prems)
    (hf : StkFrame c c') : PremsAt c' st prems := by
  refine ⟨h.1, ?_⟩
  rw [hf.prem]; exact h.2

theorem ParamsAt.stkFrame {W : World} {c c' : CMem} {params : List Nat} (h : ParamsAt W c params)
    (hf : StkFrame c c') : ParamsAt W c' params := by
  obtain ⟨hl, o, hpar, hsz, hcell⟩ := h
  refine ⟨hl, o, by rw [hf.par]; exact hpar, by rw [hf.proof]; exact hsz, ?_⟩
  rw [hf.proof]; exact hcell

/-- The rule invariant survives a change confined to the scratch stack. -/
theorem RInv.stkFrame {W : World} {X : Ctx} {c c' : CMem} {st : VSt} (hinv : RInv W X c st)
    (hf : StkFrame c c') (hs : StkOK c') : RInv W X c' st where
  core := ⟨hinv.core.cinv.stkFrame hf hs, hinv.core.fitsAll⟩
  poolPtr := by rw [hf.poolPtr]; exact hinv.poolPtr
  ttNode := hinv.ttNode
  ffNode := hinv.ffNode
  tt := by rw [hf.tt]; exact hinv.tt
  ff := by rw [hf.ff]; exact hinv.ff
  goal := by rw [hf.goal]; exact hinv.goal
  proofPtr := by rw [hf.proofPtr]; exact hinv.proofPtr
  nexpr := by rw [hf.nexpr, hf.proof]; exact hinv.nexpr
  nexprBound := by rw [hf.nexpr]; exact hinv.nexprBound
  ei := by rw [hf.nexpr, hf.proof]; exact hinv.ei
  eiOut := by rw [hf.nexpr]; exact hinv.eiOut
  premPtr := by rw [hf.premPtr]; exact hinv.premPtr
  premSize := by rw [hf.prem]; exact hinv.premSize
  premCells := by rw [hf.prem]; exact hinv.premCells
  floor := hinv.floor

end Vbcf.Proof
