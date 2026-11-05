import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Hash5
import Vbcf.Proof.Specs2
import Vbcf.Proof.InternBridge

/-!
# Vbcf proofs: `ck_intern`

`ck_intern` interns the candidate at the tail of the pool.  The statement
proved against the C body is `InternSpecT'`, whose postcondition describes the
effect on the ghost pool structurally (`Interned`, see `Interned.lean`), with
`CoreInv` replaced by the strengthened `CoreInv'` (see `Hash5.lean`).

* `ck_intern_dspec : InternSpecD` (in `Intern.lean`) — the structural contract
  over `CoreInv`, used by the direct proof;
* `ck_intern_specT_of_nz` — the refinement proof's `InternSpecT`
  (`pushNode` on the candidate), from the structural contract and
  `Interned.pushNode_eq` (`InternBridge.lean`).
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## Pure facts used by the proof -/

/-- Every cell below `plen` holds an initialised word. -/
theorem PoolRep.isW {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) : ∀ p, p < plen → IsW cells p := by
  have key : ∀ k, k ≤ pool.size → ∀ p, p < offs pool k → IsW cells p := by
    intro k
    induction k with
    | zero => intro _ p hp; simp at hp
    | succ k ih =>
      intro hk p hp
      have hn : pool[k]? = some pool[k] := Array.getElem?_eq_getElem (by omega)
      rw [offs_succ hn] at hp
      by_cases hlt : p < offs pool k
      · exact ih (by omega) p hlt
      · have hj : p - offs pool k < (nodeW posOf pool pool[k]).length := by
          rw [nodeW_length]; omega
        have hw := h.cell k _ hn (p - offs pool k) _ (List.getElem?_eq_getElem hj)
        have hp' : offs pool k + (p - offs pool k) = p := by omega
        rw [hp'] at hw
        exact hw.isW
  intro p hp
  rw [h.len] at hp
  exact key pool.size (Nat.le_refl _) p hp

/-- The words of a node are initialised. -/
theorem WordsAt.isW {cells : Array EmbC.Val} {start : Nat} {ws : List Nat}
    (h : WordsAt cells start ws) {j : Nat} (hj : j < ws.length) : IsW cells (start + j) :=
  (h j _ (List.getElem?_eq_getElem hj)).isW

/-- **What a successful `words_eq` means**: two typed nodes whose words agree
cell by cell are equal. -/
theorem node_eq_of_words {posOf : Nat → Nat} {st : St} {cells : Array EmbC.Val} {a b : Nat}
    {m n : Node} (hm : WordsAt cells a (nodeW posOf st.pool m))
    (hn : WordsAt cells b (nodeW posOf st.pool n)) (hfm : Fits posOf m) (hfn : Fits posOf n)
    (htm : Typed st m) (htn : Typed st n) (hpos : ∀ a b, posOf a = posOf b → a = b)
    (hp : offs st.pool st.pool.size ≤ 2 ^ 32)
    (heq : ∀ j, j < nodeSize n → cells[a + j]? = cells[b + j]?) : m = n := by
  have hpos0 := nodeSize_pos n
  have hh : hdrW m = hdrW n := by
    have h1 : U cells (a + 0) (hdrW m) := hm 0 _ rfl
    have h2 : U cells (b + 0) (hdrW n) := hn 0 _ rfl
    have he := heq 0 (by omega)
    unfold U at h1 h2
    rw [h1, h2] at he
    simp only [Option.some.injEq, EmbC.Val.u32.injEq] at he
    exact (bv_ofNat_inj (hdrW_lt hfm) (hdrW_lt hfn)).mp he
  have hsz : nodeSize m = nodeSize n := by
    rw [← hdrW_nodeSize hfm, ← hdrW_nodeSize hfn, hh]
  apply nodeW_inj_bv hfm hfn htm.shape htn.shape htm.args_lt htn.args_lt hpos hp
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hj : j < nodeSize n
  · have hj1 : j < (nodeW posOf st.pool m).length := by rw [nodeW_length]; omega
    have hj2 : j < (nodeW posOf st.pool n).length := by rw [nodeW_length]; omega
    have h1 := hm j _ (List.getElem?_eq_getElem hj1)
    have h2 := hn j _ (List.getElem?_eq_getElem hj2)
    have he := heq j hj
    unfold U at h1 h2
    rw [h1, h2] at he
    simp only [Option.some.injEq, EmbC.Val.u32.injEq] at he
    rw [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2]
    simp [he]
  · rw [List.getElem?_eq_none (by rw [nodeW_length]; omega),
      List.getElem?_eq_none (by rw [nodeW_length]; omega)]

/-- `((u64)hcnt + 1) * 2 > (u64)hcap`, without overflow. -/
theorem load_gt_iff (hcnt hcap : BitVec 32) :
    BitVec.setWidth 64 hcap < (BitVec.setWidth 64 hcnt + 1#64) * 2#64 ↔
      hcap.toNat < (hcnt.toNat + 1) * 2 := by
  have h1 := hcnt.isLt
  have h2 := hcap.isLt
  rw [BitVec.lt_def, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem Cand.hframe {posOf : Nat → Nat} {c c1 : CMem} {st : St} {n : Node}
    (h : Cand posOf c st n) (hf : HFrame c c1) : Cand posOf c1 st n :=
  ⟨h.fits, by rw [hf.plen, hf.pcap]; exact h.room, by rw [hf.pool, hf.plen]; exact h.words, h.args⟩

theorem HFrame.trans {c c1 c2 : CMem} (h1 : HFrame c c1) (h2 : HFrame c1 c2) : HFrame c c2 :=
  ⟨⟨h2.frame.stk.trans h1.frame.stk, h2.frame.facts.trans h1.frame.facts,
    h2.frame.prem.trans h1.frame.prem, h2.frame.proof.trans h1.frame.proof,
    h2.frame.stkPtr.trans h1.frame.stkPtr, h2.frame.sp.trans h1.frame.sp,
    h2.frame.scap.trans h1.frame.scap, h2.frame.factsPtr.trans h1.frame.factsPtr,
    h2.frame.flen.trans h1.frame.flen, h2.frame.fcap.trans h1.frame.fcap,
    h2.frame.premPtr.trans h1.frame.premPtr, h2.frame.par.trans h1.frame.par,
    h2.frame.proofPtr.trans h1.frame.proofPtr, h2.frame.nexpr.trans h1.frame.nexpr,
    h2.frame.tt.trans h1.frame.tt, h2.frame.ff.trans h1.frame.ff, h2.frame.goal.trans h1.frame.goal,
    h2.frame.val.trans h1.frame.val, h2.frame.lr.trans h1.frame.lr,
    h2.frame.lrPtr.trans h1.frame.lrPtr, h2.frame.lo.trans h1.frame.lo,
    h2.frame.live.trans h1.frame.live⟩,
   h2.pool.trans h1.pool, h2.poolPtr.trans h1.poolPtr, h2.plen.trans h1.plen, h2.pcap.trans h1.pcap⟩

theorem PoolFrame.trans' {c c1 c2 : CMem} (h1 : PoolFrame c c1) (h2 : PoolFrame c1 c2) :
    PoolFrame c c2 := by
  constructor
  · rw [h2.stk, h1.stk]
  · rw [h2.facts, h1.facts]
  · rw [h2.prem, h1.prem]
  · rw [h2.proof, h1.proof]
  · rw [h2.stkPtr, h1.stkPtr]
  · rw [h2.sp, h1.sp]
  · rw [h2.scap, h1.scap]
  · rw [h2.factsPtr, h1.factsPtr]
  · rw [h2.flen, h1.flen]
  · rw [h2.fcap, h1.fcap]
  · rw [h2.premPtr, h1.premPtr]
  · rw [h2.par, h1.par]
  · rw [h2.proofPtr, h1.proofPtr]
  · rw [h2.nexpr, h1.nexpr]
  · rw [h2.tt, h1.tt]
  · rw [h2.ff, h1.ff]
  · rw [h2.goal, h1.goal]
  · rw [h2.val, h1.val]
  · rw [h2.lr, h1.lr]
  · rw [h2.lrPtr, h1.lrPtr]
  · rw [h2.lo, h1.lo]
  · rw [h2.live, h1.live]

/-- The C state after `ck_intern` commits the candidate `n` in slot `slot`. -/
def commitC (c : CMem) (slot : Nat) (n : Node) : CMem :=
  { c with
    k := { c.k with hcnt := c.k.hcnt + 1#32, plen := c.k.plen + BitVec.ofNat 32 (nodeSize n) }
    htab := c.htab.setIfInBounds slot (.u32 (c.k.plen + 1#32)) }

/-- **Committing a new node.**  The probe from the candidate's hash reached
an empty slot without meeting an equal node: the node is new, it is appended
to the ghost pool (`Interned.new`), and the committed C state represents the
result. -/
theorem CoreInv'.commit {posOf : Nat → Nat} {c : CMem} {st : St} {n : Node} {d : Nat}
    (hinv : CoreInv' posOf c st) (hcand : Cand posOf c st n) (hty : Typed st n)
    (hload : 2 * (st.pool.size + 1) ≤ c.k.hcap.toNat)
    (hpr : Probed st.pool c.htab c.k.hcap.toNat (hashNode posOf st.pool n) n d)
    (h0 : U c.htab (((hashNode posOf st.pool n).toNat + d) % c.k.hcap.toNat) 0) :
    ∃ st', Interned st n st' st.pool.size ∧ st'.pool = st.pool.push n ∧
      CoreInv' posOf (commitC c (((hashNode posOf st.pool n).toNat + d) % c.k.hcap.toNat) n) st' := by
  have hci := hinv.core
  have hrep := hci.rep
  have hok := hci.htab
  have hpart := hok.part
  have hcap := hci.poolCap
  have hroom := hcand.room
  simp only [maxPool] at hcap
  have hlen := hrep.len
  have hnsz := nodeSize_le hcand.fits
  have hargs := hty.args_lt
  have hwf := hci.ok.args_lt_size
  have hmiss : ∀ r : Nat, st.pool[r]? ≠ some n :=
    fun r => hpart.miss (by omega) hpr h0 r trivial
  obtain ⟨st', hp, hpool'⟩ := Interned.new hty hmiss
  have hpl : (c.k.plen + BitVec.ofNat 32 (nodeSize n)).toNat = c.k.plen.toNat + nodeSize n := by
    rw [bv_add_toNat (by rw [bv_toNat_ofNat (by omega)]; omega), bv_toNat_ofNat (by omega)]
  have hcnt1 : (c.k.hcnt + 1#32).toNat = c.k.hcnt.toNat + 1 := by
    have := hok.cnt; have := hrep.size_le
    exact bv_add_toNat (by simp; omega)
  have hne : EmbC.Val.u32 (c.k.plen + 1#32) ≠ .u32 0#32 := by
    intro e
    simp only [EmbC.Val.u32.injEq] at e
    have := congrArg BitVec.toNat e
    rw [bv_add_toNat (by simp; omega)] at this
    simp at this
  refine ⟨st', hp, hpool', ⟨hp.ok hci.ok, hci.poolNull, hci.poolSize, ?_, ?_, hci.htabPtr, ?_,
    ⟨hci.stk.null, hci.stk.size, hci.stk.cap⟩, hci.posInj⟩, ?_⟩
  · show (c.k.plen + BitVec.ofNat 32 (nodeSize n)).toNat ≤ c.k.pcap.toNat ∧ _
    rw [hpl]; exact ⟨hroom, hcap.2⟩
  · show PoolRep posOf st'.pool c.pool (c.k.plen + BitVec.ofNat 32 (nodeSize n)).toNat
    rw [hpool', hpl]
    exact hrep.push hcand.fits hargs (fun _ _ => rfl) hcand.words hwf
  · show HtabOK posOf st'.pool
      (c.htab.setIfInBounds (((hashNode posOf st.pool n).toNat + d) % c.k.hcap.toNat)
        (.u32 (c.k.plen + 1#32))) c.k.hcap.toNat (c.k.hcnt + 1#32).toNat
    rw [hpool', hcnt1]
    have hhash : hashNode posOf (st.pool.push n) n = hashNode posOf st.pool n := by
      unfold hashNode; rw [nodeW_push n (fun a ha => Nat.le_of_lt (hargs a ha))]
    have hoff : offs (st.pool.push n) st.pool.size = c.k.plen.toNat := by
      rw [offs_push n (Nat.le_refl _), hlen]
    have hins := (hpart.push n hwf).insert (x := st.pool.size) (n := n) (d := d)
      (by rw [offs_push_end, ← hlen]; omega) (by simp)
      (by rw [hhash]; exact fun d' hd' => (hpr d' hd').1) (by rw [hhash]; exact h0)
    rw [hhash, hoff, ofNat_succ_toNat] at hins
    refine hins.toOK ?_ ?_ ?_ ?_
    · intro i hi
      rw [Array.size_push] at hi
      by_cases hlt : i < st.pool.size
      · exact Or.inl ⟨hlt, trivial⟩
      · exact Or.inr (by omega)
    · rw [Array.size_push, hok.cnt]
    · rw [nzCount_set h0 hne, hinv.nz]
    · rw [Array.size_push]; exact hload
  · show nzCount (c.htab.setIfInBounds _ _) = (c.k.hcnt + 1#32).toNat
    rw [nzCount_set h0 hne, hinv.nz, hcnt1]

/-! ## `ck_intern` -/

/-- The postcondition of `InternSpec`, over `CoreInv'`. -/
def InternPost' (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St)
    (rv : Option EmbC.Val) (s' : (KernelState prog State)) : Prop :=
  ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ PoolFrame c c' ∧
    ((r = noid ∧ CoreInv' posOf c' st) ∨
     (∃ n st' i, Cand posOf c st n ∧ Interned st n st' i ∧
        CoreInv' posOf c' st' ∧ r.toNat = offs st'.pool i ∧ r ≠ noid))

/-- `InternSpecT (State := State)` with the strengthened invariant `CoreInv'` in the
precondition and in both branches of the postcondition. -/
def InternSpecT' : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St),
    FnSpec (State := State) Vbcf.prog "ck_intern"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv' posOf c st ∧ CandRawT posOf c st)
      (fun _ _ rv s' => InternPost' W sb c posOf st rv s')

/-- The postcondition of `TyckSpecT (State := State)`, named. -/
def TyckPost (c : CMem) (posOf : Nat → Nat) (st : St) (s : (KernelState prog State)) (rv : Option EmbC.Val)
    (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ (rv = some (.u32 0#32) ∨ (rv = some (.u32 1#32) ∧ ∃ n, Cand posOf c st n ∧ Typed st n))

/-- Where `ck_intern` stands once the table has room for one more node. -/
def InternMid (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (nw : BitVec 32) :
    (Post prog State) := fun o env s' =>
  match o with
  | .normal => ∃ (c1 : CMem) (ok : BitVec 32),
      env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 c.k.plen),
        ("n", .u32, .u32 nw), ("h", .u32, .u32 0#32), ("i", .u32, .u32 0#32),
        ("mask", .u32, .u32 0#32), ("e", .u32, .u32 0#32), ("ok", .u32, .u32 ok)] ∧
      Holds W s'.mem sb c1 ∧ HFrame c c1 ∧ CoreInv' posOf c1 st ∧
      2 * (st.pool.size + 1) ≤ c1.k.hcap.toNat
  | o => retPost (some .u32) (InternPost' W sb c posOf st) o env s'

/-- The probing loop of `ck_intern`: only `work` and `err` change. -/
def InternInv (W : World) (sb : Nat) (c c1 : CMem) (st : St) (n : Node) (hv : BitVec 32) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (wk er i e ok : BitVec 32) (d : Nat),
    Holds W s'.mem sb (c1.wev wk er c1.k.val) ∧
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 c.k.plen),
      ("n", .u32, .u32 (BitVec.ofNat 32 (nodeSize n))), ("h", .u32, .u32 hv), ("i", .u32, .u32 i),
      ("mask", .u32, .u32 (c1.k.hcap - 1#32)), ("e", .u32, .u32 e), ("ok", .u32, .u32 ok)] ∧
    i.toNat = (hv.toNat + d) % c1.k.hcap.toNat ∧
    Probed st.pool c1.htab c1.k.hcap.toNat hv n d

/-- **`ck_intern` interns the candidate.**  No hypotheses: the type checker
(`ck_tyck_spec`) and `ck_hgrow` (`ck_hgrow_spec`) are proved. -/
theorem ck_intern_spec : InternSpecT' (State := State) := by
  intro W sb c posOf st
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckIntern) rfl
  rintro vs s ⟨rfl, h, hinv, hraw⟩
  simp [ckIntern, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hty : FnSpec (State := State) Vbcf.prog "ck_tyck"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧ CandRawT posOf c st)
      (fun _ s rv s' => TyckPost c posOf st s rv s') := ck_tyck_spec W sb c posOf st
  apply WP.seq; apply WP.assign; ck_simp
  apply WP.seq
  apply WP.call hty
  ck_simp
  refine ⟨⟨h, hinv.core, hraw⟩, ?_⟩
  rintro rv s1 ⟨rfl, hres⟩
  rcases hres with rfl | ⟨rfl, n, hcand, htyped⟩
  · ck_simp
    apply WP.seq
    apply WP.ite
    ck_simp
    apply WP.ret
    ck_simp [retPost, InternPost', NOID]
    exact ⟨c, h, PoolFrame.self c, Or.inl ⟨rfl, hinv⟩⟩
  · ck_simp
    apply WP.seq
    apply WP.ite
    ck_simp
    apply WP.skip
    have hfit := hcand.fits
    have hnsz := nodeSize_le hfit
    have hnpos := nodeSize_pos n
    have hroom := hcand.room
    have hcap := hinv.core.poolCap
    simp only [maxPool] at hcap
    have hargs := htyped.args_lt
    obtain ⟨pb, hpool⟩ := pool_ptr_of_pos h hinv.core (by omega)
    have hhdr : U c.pool c.k.plen.toNat (hdrW n) := hcand.words 0 _ rfl
    have hnw : (BitVec.ofNat 32 (nodeSize n)).toNat = nodeSize n := bv_toNat_ofNat (by omega)
    apply WP.seq
    apply WP.assign
    ck_simp [hpool, h.rd_pool hpool, rd_u32 hhdr, size_word hfit]
    -- pay the node's size
    apply WP.seq
    apply WP.call (spend_spec W sb c (BitVec.ofNat 32 (nodeSize n)))
    ck_simp
    refine ⟨h, ?_⟩
    rintro rv s1 rfl h1
    rw [spendM_wev] at h1
    clear h
    obtain ⟨w1, hw1⟩ : ∃ w1, w1 = (spendM c (BitVec.ofNat 32 (nodeSize n))).2.k.work := ⟨_, rfl⟩
    obtain ⟨e1, he1⟩ : ∃ e1, e1 = (spendM c (BitVec.ofNat 32 (nodeSize n))).2.k.err := ⟨_, rfl⟩
    rw [← hw1, ← he1] at h1
    have h := h1
    clear h1
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro _
      apply WP.ret
      ck_simp [retPost, InternPost', NOID]
      exact ⟨_, h, by constructor <;> rfl, Or.inl ⟨rfl, hinv.wev _ _ _⟩⟩
    intro _
    apply WP.skip
    apply WP.seq
    refine WP.mono (Q := InternMid W sb c posOf st (BitVec.ofNat 32 (nodeSize n))) ?_ ?_
    · -- make room in the table
      apply WP.ite
      ck_simp [load_gt_iff]
      have hok0 := hinv.core.htab
      have hcap1 : 1 ≤ c.k.hcap.toNat := by
        obtain ⟨j, hj, -⟩ := hok0.pow; rw [hj]; exact Nat.one_le_two_pow
      constructor
      · intro hfull
        have hgr : FnSpec (State := State) Vbcf.prog "ck_hgrow"
            (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb (c.wev w1 e1 c.k.val) ∧
              CoreInv' posOf (c.wev w1 e1 c.k.val) st ∧
              ∃ pb, (c.wev w1 e1 c.k.val).k.pool = some (pb, 0))
            (fun _ _ rv s' => HgrowPost W sb (c.wev w1 e1 c.k.val) posOf st rv s') :=
          ck_hgrow_spec W sb _ posOf st
        apply WP.seq
        apply WP.call hgr
        ck_simp
        refine ⟨⟨h, hinv.wev _ _ _, pb, hpool⟩, ?_⟩
        clear h
        rintro rv s2 ⟨c1, h, hfr, hinv1, hres⟩
        rcases hres with rfl | ⟨rfl, hcap2⟩
        · ck_simp
          apply WP.ite
          ck_simp
          apply WP.ret
          ck_simp [retPost, InternMid, InternPost', NOID]
          exact ⟨c1, h, PoolFrame.trans' (by constructor <;> rfl) hfr.frame, Or.inl ⟨rfl, hinv1⟩⟩
        · ck_simp
          apply WP.ite
          ck_simp
          apply WP.skip
          have := hok0.load
          simp only [wev_k_hcap] at hcap2
          exact ⟨c1, _, rfl, h, HFrame.trans (HFrame.wev c _ _) hfr, hinv1, by omega⟩
      · intro hfree
        apply WP.skip
        have := hok0.cnt
        exact ⟨c.wev w1 e1 c.k.val, _, rfl, h, HFrame.wev c _ _, hinv.wev _ _ _,
          by simp only [wev_k_hcap]; omega⟩
    · rintro o env' s2 hq
      cases o with
      | brk => exact hq
      | ret rv => exact hq
      | normal =>
        clear h
        obtain ⟨c1, okv, rfl, h, hfr, hinv1, hload⟩ := hq
        have hcand1 := hcand.hframe hfr
        have hci := hinv1.core
        have hrep := hci.rep
        have hok := hci.htab
        have hpart := hok.part
        obtain ⟨j, hj, hj30⟩ := hok.pow
        obtain ⟨hb, hhtab⟩ := hci.htabPtr
        have hpl : c1.k.plen = c.k.plen := hfr.plen
        have hpc : c1.k.pcap = c.k.pcap := hfr.pcap
        have hpool1 : c1.k.pool = some (pb, 0) := by rw [hfr.poolPtr]; exact hpool
        have hwords : WordsAt c1.pool c.k.plen.toNat (nodeW posOf st.pool n) := hpl ▸ hcand1.words
        have hlen : c.k.plen.toNat = offs st.pool st.pool.size := by rw [← hpl]; exact hrep.len
        have hpsz : c1.pool.size = c.k.pcap.toNat := by rw [← hpc]; exact hci.poolSize pb 0 hpool1
        have hnmod : nodeSize n % 4294967296 = nodeSize n := Nat.mod_eq_of_lt (by omega)
        apply WP.seq; apply WP.assign; ck_simp
        apply WP.seq
        apply WP.call (ck_hash_spec sb c1.k pb c1.pool c.k.plen (BitVec.ofNat 32 (nodeSize n))
          ((nodeW posOf st.pool n).map (BitVec.ofNat 32)))
        ck_simp [hnmod]
        refine ⟨⟨h.ck, hpool1, h.poolArr hpool1, ?_, ?_, ?_⟩, ?_⟩
        · rw [nodeW_length]
        · omega
        · exact fun j a hj => hwords j a hj
        apply WP.seq; apply WP.assign; ck_simp
        apply WP.seq
        apply WP.while (I := InternInv W sb c c1 st n (hashNode posOf st.pool n))
        · exact ⟨c1.k.work, c1.k.err, _, _, _, 0, by rw [wev_self]; exact h, rfl, probe_start _ hj,
            Probed.zero _ _ _ _ _⟩
        · rintro env s' ⟨wk, er, i, e, okv', d, h', rfl, hi, hpr⟩
          clear h
          have h := h'
          clear h'
          obtain ⟨e0, hu, he32, hnode⟩ := hpart.slot ((hashNode posOf st.pool n).toNat + d)
          rw [← hi] at hu
          ck_simp [hhtab, h.rd_htab hhtab, rd_u32 hu, ofNat32_eq_zero_iff he32]
          constructor
          · -- an empty slot: the node is new; commit it
            intro he0
            subst he0
            have hslot : i.toNat < c1.htab.size := by
              rw [hi, hok.size]; exact Nat.mod_lt _ hpart.pos
            obtain ⟨st', hpush, hpool', hinv'⟩ := hinv1.commit hcand1 htyped hload hpr (hi ▸ hu)
            rw [← hi] at hinv'
            apply WP.seq
            apply WP.ck_store .htab h (by rfl) hhtab
            ck_simp [hhtab]
            refine ⟨hslot, ?_⟩
            intro s3 h
            apply WP.seq
            apply WP.ck_setField hs h (by rfl)
            ck_simp
            intro s4 h
            apply WP.seq
            apply WP.ck_setField hs h (by rfl)
            ck_simp
            intro s5 h
            apply WP.ret
            ck_simp [retPost, InternPost']
            have h' : Holds W s5.mem sb ((commitC c1 i.toNat n).wev wk er c1.k.val) := by
              unfold commitC CMem.wev; rw [hpl]; exact h
            have hne : ¬ c.k.plen = noid := by
              intro e
              have := congrArg BitVec.toNat e
              simp [noid] at this; omega
            refine ⟨_, h', hfr.frame.trans' (by constructor <;> rfl),
              Or.inr ⟨n, hcand, st', _, hpush, hinv'.wev _ _ _, ?_, hne⟩⟩
            rw [hpool', offs_push n (Nat.le_refl _), hlen]
          · -- an occupied slot: compare its node with the candidate
            intro he0
            obtain ⟨x, hx, rfl⟩ := hnode he0
            obtain ⟨m, hm⟩ := node_of_lt (st := st) hx
            have hoff : offs st.pool x < c.k.plen.toNat := by rw [hlen]; exact offs_lt_end hx
            have hmw := hrep.cell x m hm
            -- the node's size in work per probe
            apply WP.seq
            apply WP.call (spend_spec W sb (c1.wev wk er c1.k.val) (BitVec.ofNat 32 (nodeSize n)))
            ck_simp
            refine ⟨h, ?_⟩
            rintro rv s6 rfl h6
            rw [spendM_wev, wev_wev] at h6
            clear h
            have h := h6
            clear h6
            apply WP.seq
            apply WP.ite
            ck_simp
            constructor
            · intro _
              apply WP.ret
              ck_simp [retPost, InternPost', NOID]
              exact ⟨_, h, hfr.frame.trans' (by constructor <;> rfl), Or.inl ⟨rfl, hinv1.wev _ _ _⟩⟩
            intro _
            apply WP.skip
            have hblk : s6.mem.block? pb = some ⟨.u32, c1.pool⟩ := h.poolArr hpool1
            apply WP.seq
            apply WP.assign
            ck_simp [hhtab, h.rd_htab hhtab, rd_u32 hu, ofNat_succ_sub_one]
            apply WP.seq
            apply WP.call (words_eq_spec pb (offs st.pool x) pb c.k.plen.toNat c1.pool c1.pool
              (BitVec.ofNat 32 (nodeSize n)))
            ck_simp [hpool1, hblk, EmbC.Ty.isStruct, hnmod,
              bv_toNat_ofNat (show offs st.pool x < 2 ^ 32 by omega),
              show offs st.pool x ≤ c1.pool.size by omega,
              show c.k.plen.toNat ≤ c1.pool.size by omega]
            refine ⟨⟨h.poolArr hpool1, ?_, ?_⟩, ?_⟩
            · intro k hk
              by_cases hlt : offs st.pool x + k < c1.k.plen.toNat
              · exact hrep.isW _ hlt
              · rw [hpl] at hlt
                have he : offs st.pool x + k =
                    c.k.plen.toNat + (offs st.pool x + k - c.k.plen.toNat) := by omega
                rw [he]
                exact hwords.isW (by rw [nodeW_length]; omega)
            · intro k hk
              exact hwords.isW (by rw [nodeW_length]; exact hk)
            intro rv hres
            rcases hres with ⟨rfl, heq⟩ | ⟨rfl, k, hk, hne⟩
            · -- the same words: the candidate is node `x`
              have hmn : m = n := node_eq_of_words hmw hwords (hrep.fits x m hm) hfit
                (hci.ok.typed hm) htyped hci.posInj (by omega) heq
              subst hmn
              have hpush := Interned.found hci.ok hm
              ck_simp
              apply WP.seq
              apply WP.ite
              ck_simp
              apply WP.ret
              ck_simp [retPost, InternPost']
              exact ⟨_, h, hfr.frame.trans' (by constructor <;> rfl), Or.inr ⟨m, hcand, st, x, hpush,
                hinv1.wev _ _ _, by omega, ofNat_ne_noid (by omega)⟩⟩
            · -- different words: keep probing
              have hmn : st.pool[x]? ≠ some n := by
                rw [hm]; intro e
                simp only [Option.some.injEq] at e
                subst e
                have hk' : k < (nodeW posOf st.pool m).length := by rw [nodeW_length]; exact hk
                have h1 := hmw k _ (List.getElem?_eq_getElem hk')
                have h2 := hwords k _ (List.getElem?_eq_getElem hk')
                unfold U at h1 h2
                exact hne (by rw [h1, h2])
              ck_simp
              apply WP.seq
              apply WP.ite
              ck_simp
              apply WP.skip
              apply WP.assign
              ck_simp
              exact ⟨_, _, _, _, _, d + 1, h, rfl, probe_next hj (by omega) hi,
                hpr.step (by omega) (hi ▸ hu) he0 he32 (fun i' hi' he => by
                  have : x = i' := offs_inj (Nat.le_of_lt hx) (Nat.le_of_lt hi') (by omega)
                  subst this; exact hmn)⟩

/-- A specification still holds with a weaker postcondition. -/
theorem FnSpec.of_post {P : Prog} {f : String} {pre : List EmbC.Val → (KernelState P State) → Prop}
    {post post' : List EmbC.Val → (KernelState P State) → Option EmbC.Val → (KernelState P State) → Prop} (h : FnSpec (State := State) P f pre post)
    (hq : ∀ vs st rv st', post vs st rv st' → post' vs st rv st') : FnSpec (State := State) P f pre post' := by
  intro fuel vs st hpre
  have := h fuel vs st hpre
  split at this
  · trivial
  · exact this
  · exact hq _ _ _ _ this

/-- `InternSpecT` as stated in `Specs2.lean` (the refinement proof's contract:
`pushNode` on the candidate), given that `CoreInv` implies the extra fact of
`CoreInv'`.  Once `nz : nzCount htab = hcnt` is a field of `HtabOK`, the
hypothesis is `fun _ _ _ h => h.htab.nz`. -/
theorem ck_intern_specT_of_nz
    (hnz : ∀ (posOf : Nat → Nat) (c : CMem) (st : St), CoreInv posOf c st →
      nzCount c.htab = c.k.hcnt.toNat) : InternSpecT (State := State) := by
  intro W sb c posOf st
  refine FnSpec.conseq (ck_intern_spec W sb c posOf st) ?_ ?_
  · rintro vs s ⟨hv, h, hinv, hraw⟩
    exact ⟨hv, h, ⟨hinv, hnz _ _ _ hinv⟩, hraw⟩
  · rintro vs s rv s' ⟨-, -, hinv0, -⟩ ⟨c', r, hrv, h, hf, hres⟩
    refine ⟨c', r, hrv, h, hf, ?_⟩
    rcases hres with ⟨hr, hinv⟩ | ⟨n, st', i, hc, hp, hinv, hr, hne⟩
    · exact Or.inl ⟨hr, hinv.core⟩
    · exact Or.inr ⟨n, st', i, hc, hp.pushNode_eq hinv0.ok, hinv.core, hr, hne⟩

end Vbcf.Proof
