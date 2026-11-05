import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Builders3

/-!
# Vbcf proofs: `expr_at`, `push_args`, `ck_room`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## `expr_at`

`ExprAtSpec` in `Specs.lean` is not provable as stated: the C computes the index `3 + p`
in 32 bits, and nothing in `RInv` bounds `nexpr` (or the size of the proof block) so that
this does not wrap.  `ExprAtSpec'` adds the precondition `3 + nexpr ≤ 2^32`. -/

/-- `expr_at(st, p)` is `ei p`.  Reads only. -/
def ExprAtSpec' : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : VSt) (p : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "expr_at"
      (fun vs s => vs = [.ptr sb 0, .u32 p] ∧ Holds W s.mem sb c ∧ RInv W X c st ∧
        3 + c.k.nexpr.toNat ≤ 2 ^ 32)
      (fun _ s rv s' => s' = s ∧ ∃ r, rv = some (.u32 r) ∧
        match X.ei p.toNat with
        | none => r = noid
        | some i => st.lv i ∧ r.toNat = st.id i ∧ r ≠ noid)

/-- The postcondition of `expr_at`, named so that `simp` leaves it alone. -/
def ExprAtPost (X : Ctx) (st : VSt) (p : BitVec 32) (s : (KernelState prog State)) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  s' = s ∧ ∃ r, rv = some (.u32 r) ∧
    match X.ei p.toNat with
    | none => r = noid
    | some i => st.lv i ∧ r.toNat = st.id i ∧ r ≠ noid

theorem expr_at_spec' : ExprAtSpec' (State := State) := by
  intro W sb c X st p
  show FnSpec (State := State) Vbcf.prog "expr_at" _ (fun _ s => ExprAtPost X st p s)
  have hs := prog_ck
  apply FnSpec.intro' (fn := exprAt) rfl
  rintro vs s ⟨rfl, h, hinv, hbound⟩
  simp [exprAt, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.ite
  ck_simp
  constructor
  · intro hge
    have hge' : c.k.nexpr.toNat ≤ p.toNat := by simpa [BitVec.le_def] using hge
    apply WP.ret
    ck_simp [retPost, NOID]
    refine ⟨rfl, _, rfl, ?_⟩
    rw [hinv.eiOut _ hge']; rfl
  · intro hlt
    have hlt' : p.toNat < c.k.nexpr.toNat := by simpa [BitVec.lt_def] using hlt
    apply WP.skip
    obtain ⟨v, hv, hu, hm⟩ := hinv.ei p.toNat hlt'
    have h3p : (3#32 + p).toNat = 3 + p.toNat := by
      rw [bv_add_toNat] <;> simp <;> omega
    apply WP.seq
    apply WP.assign
    ck_simp [hinv.proofPtr, h.loadProof, h3p, rd_u32 hu]
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro hz
      have hv0 : v = 0 := by
        have := congrArg BitVec.toNat hz
        rwa [bv_toNat_ofNat hv] at this
      apply WP.ret
      ck_simp [retPost, NOID]
      refine ⟨rfl, _, rfl, ?_⟩
      cases he : X.ei p.toNat with
      | none => rfl
      | some i => rw [he] at hm; omega
    · intro hnz
      apply WP.skip
      apply WP.ret
      ck_simp [retPost]
      refine ⟨rfl, _, rfl, ?_⟩
      cases he : X.ei p.toNat with
      | none =>
        rw [he] at hm
        exact absurd (by rw [hm]) hnz
      | some i =>
        rw [he] at hm
        obtain ⟨hi, hvi⟩ := hm
        have hoff := hinv.core.off_lt hi
        have hr : (BitVec.ofNat 32 v - 1#32).toNat = st.id i := by
          rw [bv_sub_toNat] <;> rw [bv_toNat_ofNat hv] <;> simp <;> omega
        refine ⟨hi, hr, ?_⟩
        intro e
        have := congrArg BitVec.toNat e
        rw [hr] at this
        simp [noid] at this
        omega

/-! ## `push_args` -/

/-- `push_args(st, id)` pushes the argument ids of the non-leaf node `id` on the scratch
stack.  Whatever it returns, only the stack (and `work`, `err`) changed, the cells below
the old `sp` are as before, and the core invariant holds; on success (1) the stack has
grown by exactly the node's arguments. -/
def PushArgsSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (id : BitVec 32) (i : Nat)
    (nd : Node),
    EmbC.FnSpec (State := State) Vbcf.prog "push_args"
      (fun vs s => vs = [.ptr sb 0, .u32 id] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧
        st.pool[i]? = some nd ∧ ¬ IsLeaf nd.op ∧ id.toNat = offs st.pool i)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧ StkFrame c c' ∧ CoreInv posOf c' st ∧
        (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ c'.k.sp.toNat = c.k.sp.toNat + nd.args.size ∧
           StkIdsC c' st c.k.sp.toNat nd.args.toList)))

def PushArgsPost (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (nd : Node) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c', Holds W s'.mem sb c' ∧ StkFrame c c' ∧ CoreInv posOf c' st ∧
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧
    (rv = some (.u32 0#32) ∨
     (rv = some (.u32 1#32) ∧ c'.k.sp.toNat = c.k.sp.toNat + nd.args.size ∧
       StkIdsC c' st c.k.sp.toNat nd.args.toList))

/-- Loop invariant of `push_args`: the first `k` arguments are on the stack. -/
def PushArgsInv (W : World) (sb : Nat) (c : CMem) (st : St) (id nb : BitVec 32) (nd : Node) :
    Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c2 : CMem) (k ok : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, .u32 id), ("n", .u32, .u32 nb),
      ("i", .u32, .u32 k), ("ok", .u32, .u32 ok)] ∧
    k.toNat ≤ nd.args.size ∧ Holds W s.mem sb c2 ∧ StkFrame c c2 ∧ StkOK c2 ∧
    c2.k.sp.toNat = c.k.sp.toNat + k.toNat ∧
    (∀ j, j < c.k.sp.toNat → c2.stk[j]? = c.stk[j]?) ∧
    ∀ j x, j < k.toNat → nd.args.toList[j]? = some x →
      U c2.stk (c.k.sp.toNat + j) (offs st.pool x)

theorem push_args_spec : PushArgsSpec (State := State) := by
  intro W sb c posOf st id i nd
  show FnSpec (State := State) Vbcf.prog "push_args" _ (fun _ _ => PushArgsPost W sb c posOf st nd)
  have hs := prog_ck
  apply FnSpec.intro' (fn := pushArgs) rfl
  rintro vs s ⟨rfl, h, hinv, hn, hl, hid⟩
  simp [pushArgs, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hi : i < st.pool.size := lt_size_of_getElem? hn
  obtain ⟨pb, hpool⟩ := hinv.poolPtr_of_nonempty h (by omega)
  have hrep := hinv.rep
  have hfit := hrep.fits i nd hn
  have hoff := hinv.off_lt hi
  have hend := hinv.node_end_lt hn
  have hsize := nodeSize_of_not_leaf hl
  have hargs := (hinv.ok.typed hn).args_lt
  apply WP.seq
  apply WP.assign
  ck_simp [hpool, h.rd_pool hpool, hid, rd_u32 (hrep.hdr hn)]
  have hnb : (BitVec.ofNat 32 (hdrW nd) >>> 8 &&& 255#32).toNat = nd.args.size := by
    rw [bv_and_ff, bv_shr_8, bv_toNat_ofNat (hdrW_lt hfit), hdrW_len hfit, tailLen_of_not_leaf hl]
  generalize BitVec.ofNat 32 (hdrW nd) >>> 8 &&& 255#32 = nb at hnb
  apply WP.seq
  apply WP.while (I := PushArgsInv W sb c st id nb nd)
  · exact ⟨c, 0#32, 0#32, rfl, by simp, h, StkFrame.refl c, hinv.stk, by simp, fun _ _ => rfl,
      fun j x hj => by simp at hj⟩
  · clear h
    rintro env s ⟨c2, k, ok, rfl, hkle, h, hfr, hok, hsp, hlow, hpushed⟩
    ck_simp
    constructor
    · intro hge
      have hk : k.toNat = nd.args.size := by
        have : nb.toNat ≤ k.toNat := by simpa [BitVec.le_def] using hge
        omega
      apply WP.ret
      ck_simp [retPost]
      refine ⟨c2, h, hfr, hinv.stkFrame hfr hok, hlow, Or.inr ⟨rfl, by omega, ?_⟩⟩
      intro j x hj
      have hjl : j < nd.args.size := by simpa using lt_length_of_getElem? hj
      have hx : x ∈ nd.args := by
        have := List.mem_of_getElem? hj
        simpa using this
      exact ⟨hargs x hx, hpushed j x (by omega) hj⟩
    · intro hlt
      have hlt' : k.toNat < nd.args.size := by
        have : k.toNat < nb.toNat := by simpa [BitVec.lt_def] using hlt
        omega
      have hcell := hrep.arg hn hl hlt'
      have hidx : (id + 1#32 + k).toNat = offs st.pool i + 1 + k.toNat := by
        rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
      have hpool2 : c2.k.pool = some (pb, 0) := by rw [hfr.poolPtr]; exact hpool
      have hcell2 : c2.pool[offs st.pool i + 1 + k.toNat]? =
          some (.u32 (BitVec.ofNat 32 (offs st.pool nd.args[k.toNat]))) := by
        rw [hfr.pool]; exact hcell
      have hcap := hok.cap
      simp only [maxPool] at hcap
      apply WP.seq
      apply WP.call (push_spec W sb c2 (BitVec.ofNat 32 (offs st.pool nd.args[k.toNat])))
      ck_simp [hpool2, h.rd_pool hpool2, hidx, rd_u32 hcell2]
      refine ⟨⟨h, hok⟩, ?_⟩
      clear h
      intro rv s c3 h hok3 hfr3 hpre3 hres
      rcases hres with ⟨rfl, hsp3⟩ | ⟨rfl, hsp3, htop⟩
      · ck_simp
        apply WP.seq
        apply WP.ite
        ck_simp
        apply WP.ret
        ck_simp [retPost]
        exact ⟨c3, h, hfr.trans hfr3, hinv.stkFrame (hfr.trans hfr3) hok3,
          fun j hj => (hpre3 j (by omega)).trans (hlow j hj), Or.inl rfl⟩
      · ck_simp
        apply WP.seq
        apply WP.ite
        ck_simp
        apply WP.skip
        apply WP.assign
        ck_simp
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
          have := hfit.tailLen
          rw [tailLen_of_not_leaf hl] at this
          rw [bv_add_toNat] <;> simp <;> omega
        have hsp3' : c3.k.sp.toNat = c2.k.sp.toNat + 1 := by
          rw [hsp3, bv_add_toNat] <;> simp <;> omega
        refine ⟨c3, k + 1#32, 1#32, rfl, by omega, h, hfr.trans hfr3, hok3, by omega,
          fun j hj => (hpre3 j (by omega)).trans (hlow j hj), ?_⟩
        intro j x hj hx
        by_cases hjk : j < k.toNat
        · unfold U; rw [hpre3 _ (by omega)]; exact hpushed j x hjk hx
        · have hjeq : j = k.toNat := by omega
          subst hjeq
          have hxe : x = nd.args[k.toNat] := by
            simpa [hlt'] using hx.symm
          subst hxe
          unfold U; rw [← hsp]; exact htop

/-! ## `ck_room` -/

/-- `RoomSpec` with one more conjunct: the hash table is untouched (`HtabSame`), so that
any additional invariant about the table carries over. -/
def RoomSpec' : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (n : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_room"
      (fun vs s => vs = [.ptr sb 0, .u32 n] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧ PoolFrame c c' ∧ CoreInv posOf c' st ∧
        c'.k.plen = c.k.plen ∧ HtabSame c c' ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ c.k.plen.toNat + n.toNat ≤ c'.k.pcap.toNat)))

/-- The postcondition of `ck_room`, named so that `simp` leaves it alone. -/
def RoomPost (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (n : BitVec 32) :
    Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c', Holds W s'.mem sb c' ∧ PoolFrame c c' ∧ CoreInv posOf c' st ∧
    c'.k.plen = c.k.plen ∧ HtabSame c c' ∧
    (rv = some (.u32 0#32) ∨
     (rv = some (.u32 1#32) ∧ c.k.plen.toNat + n.toNat ≤ c'.k.pcap.toNat))

theorem ck_room_spec' : RoomSpec' (State := State) := by
  intro W sb c posOf st n
  show FnSpec (State := State) Vbcf.prog "ck_room" _ (fun _ _ => RoomPost W sb c posOf st n)
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckRoom) rfl
  rintro vs s ⟨rfl, h, hinv⟩
  simp [ckRoom, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hplt := c.k.plen.isLt
  have hnlt := n.isLt
  have hclt := c.k.pcap.isLt
  have hneed : (BitVec.setWidth 64 c.k.plen + BitVec.setWidth 64 n).toNat =
      c.k.plen.toNat + n.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth]; omega
  apply WP.seq
  apply WP.assign
  ck_simp
  generalize BitVec.setWidth 64 c.k.plen + BitVec.setWidth 64 n = need at hneed
  have hcap := hinv.poolCap
  -- the allocation and installation, for any new capacity `nc`
  have key : ∀ nc : BitVec 32, c.k.plen.toNat + n.toNat ≤ nc.toNat → nc.toNat ≤ maxPool →
      c.k.pcap.toNat < nc.toNat →
      WP Vbcf.prog [cstms|
          if (st->work < ncap) { st->err = ERR_LIMIT; return 0; }
          st->work = st->work - ncap;
          if (st->mem < ncap) { st->err = ERR_LIMIT; return 0; }
          st->mem = st->mem - ncap;
          np = kvrealloc(st->pool, array_size((u64)ncap, sizeof(u32)));
          if (np == NULL) { st->err = ERR_NOMEM; return 0; }
          st->pool = np;
          st->pcap = ncap;
          return 1;]
        (retPost (some .u32) (RoomPost W sb c posOf st n))
        [("st", .ptr (.struct "ck"), .ptr sb 0), ("n", .u32, .u32 n), ("np", .ptr .u32, .null),
          ("ncap", .u32, .u32 nc), ("need", .u64, .u64 need)] s := by
    intro nc hge hle hgt
    have hn : nc.setWidth 64 ≠ 0#64 := by
      intro e
      have h1 := congrArg BitVec.toNat e
      have h2 := nc.isLt
      simp at h1
      omega
    simp only [Stmt.block]
    -- pay for the new capacity
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro _
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      intro st' h'
      apply WP.ret
      embc_simp [retPost]
      exact ⟨_, h', PoolFrame.setErr c _, hinv.setErr _, rfl, ⟨rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
    intro _
    apply WP.skip
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s h
    -- pay for it from the memory budget too
    apply WP.seq
    apply WP.ite
    ck_simp
    constructor
    · intro _
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      intro st' h'
      apply WP.ret
      embc_simp [retPost]
      exact ⟨_, h', by constructor <;> rfl, hinv.wev (wk := c.k.work - nc) (er := 2#32) (vl := c.k.val),
        rfl, ⟨rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
    intro _
    apply WP.skip
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s h
    have hrun := h.realloc_run (P := Vbcf.prog) .pool hn
    simp only [CK.ptr] at hrun
    apply WP.seq
    apply WP.ecall
    ck_simp [hrun]
    by_cases horc : (reallocResponse (P := Vbcf.prog) c.k.pool hn s).1 ≠ some .null
    · simp only [ne_eq, Classical.not_not] at horc
      simp only [horc, ↓reduceIte]
      have hN : nc.toNat % 18446744073709551616 = nc.toNat := by have := nc.isLt; omega
      obtain ⟨hnew, hck⟩ := h.grow_blocks .pool (nc.toNat % 18446744073709551616)
      obtain ⟨hst, hh⟩ := h.grow hs .pool (nc.toNat % 18446744073709551616)
      simp only [Arr.field] at hst hh
      embc_simp [Mem.hasTy_ptr hnew rfl]
      apply WP.seq
      apply WP.ite
      embc_simp [hnew]
      apply WP.skip
      apply WP.seq
      apply WP.setField
      embc_simp [hst]
      apply WP.seq
      apply WP.ck_setField hs hh (by rfl)
      embc_simp [CK.setU32]
      intro st' h'
      apply WP.ret
      embc_simp [retPost]
      refine ⟨_, h', by constructor <;> rfl, ?_, rfl, ⟨rfl, rfl, rfl, rfl⟩, Or.inr ⟨rfl, hge⟩⟩
      refine hinv.poolChange (by constructor <;> rfl) rfl rfl rfl rfl rfl ?_ ?_
        ⟨show c.k.plen.toNat ≤ nc.toNat by omega, hle⟩ ?_
      · intro e; simp [CK.setPtr, CMem.setArr] at e
      · intro b' o' _
        simp [CMem.setArr, reallocCells_size, hN]
      · intro i hi
        show (reallocCells _ _)[i]? = _
        simp only [CMem.old, CK.ptr]
        cases hpool : c.k.pool with
        | none =>
          have := hinv.poolNull hpool
          rw [this] at hcap; simp at hcap; omega
        | some bo =>
          simp only []
          have hsz := hinv.poolSize bo.1 bo.2 hpool
          exact reallocCells_get _ _ _ (by show i < c.pool.size; omega) (by omega)
    · simp only [ne_eq, Classical.not_not] at horc
      simp only [horc, ↓reduceIte]
      embc_simp
      apply WP.seq
      apply WP.ite
      embc_simp
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      intro st' h'
      apply WP.ret
      embc_simp [retPost]
      exact ⟨_, h', by constructor <;> rfl,
        (hinv.wev (wk := c.k.work - nc) (er := 1#32) (vl := c.k.val)).setMem (mm := c.k.mem - nc),
        rfl, ⟨rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
  apply WP.seq
  apply WP.ite
  ck_simp
  constructor
  · intro hle
    have hle' : c.k.plen.toNat + n.toNat ≤ c.k.pcap.toNat := by
      have := BitVec.le_def.mp hle
      rw [BitVec.toNat_setWidth, hneed] at this; omega
    apply WP.ret
    ck_simp [retPost]
    exact ⟨c, h, PoolFrame.unchanged c, hinv, rfl, HtabSame.self c, Or.inr ⟨rfl, hle'⟩⟩
  · intro hgt
    have hgt' : c.k.pcap.toNat < c.k.plen.toNat + n.toNat := by
      have := BitVec.lt_def.mp hgt
      rw [BitVec.toNat_setWidth, hneed] at this; omega
    apply WP.skip
    apply WP.seq
    apply WP.ite
    ck_simp [MAX_POOL]
    constructor
    · intro hbig
      apply WP.seq
      apply WP.ck_setField hs h (by rfl)
      ck_simp
      intro st' h'
      apply WP.ret
      embc_simp [retPost]
      exact ⟨_, h', PoolFrame.setErr c _, hinv.setErr _, rfl, ⟨rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
    · intro hsmall
      have hneed30 : need.toNat ≤ 1073741824 := by simpa [BitVec.le_def] using hsmall
      have hnc0 : (BitVec.setWidth 32 (need + need / 4#64)).toNat = need.toNat + need.toNat / 4 := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_udiv]
        simp; omega
      apply WP.skip
      apply WP.seq
      apply WP.assign
      ck_simp
      generalize BitVec.setWidth 32 (need + need / 4#64) = nc0 at hnc0
      apply WP.seq
      apply WP.ite
      ck_simp
      constructor
      · intro hlt
        have hlt' : nc0.toNat < 1024 := by simpa [BitVec.lt_def] using hlt
        apply WP.assign
        ck_simp
        apply WP.seq
        apply WP.ite
        ck_simp
        apply WP.skip
        exact key 1024#32 (by simp; omega) (by simp [maxPool]) (by simp; omega)
      · intro hge
        have hge' : 1024 ≤ nc0.toNat := by simpa [BitVec.le_def] using hge
        apply WP.skip
        apply WP.seq
        apply WP.ite
        ck_simp
        constructor
        · intro hgtmax
          apply WP.assign
          ck_simp
          exact key 1073741824#32 (by simp; omega) (by simp [maxPool])
            (by simp [maxPool] at hcap ⊢; omega)
        · intro hlemax
          have hlemax' : nc0.toNat ≤ 1073741824 := by simpa [BitVec.le_def] using hlemax
          apply WP.skip
          exact key nc0 (by omega) (by simp [maxPool]; omega) (by omega)

theorem ck_room_spec : RoomSpec (State := State) := by
  intro W sb c posOf st n
  refine FnSpec.conseq (ck_room_spec' W sb c posOf st n) (fun _ _ hp => hp) ?_
  rintro vs s rv s' - ⟨c', h', hf, hinv', hpl, -, hres⟩
  exact ⟨c', h', hf, hinv', hpl, hres⟩

end Vbcf.Proof
