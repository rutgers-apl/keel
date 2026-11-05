import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Hash3

/-!
# Vbcf proofs: `ck_hput`

`ck_hput` is called only by `ck_hgrow`, while the old table is still live
but no longer referenced by the struct, so `Holds` does not describe the
memory.  `HView` is the weaker description these two functions work with:
the struct, the pool block and the (new) table block, and "every other
block is as in the reference memory `m0`".
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- Memory `m` as the table-building code sees it: the struct in `sb` has
fields `k`, the pool is block `pb`, the table is block `hb`, and every
other block is as in the reference memory `m0`. -/
structure HView (m0 m : Mem) (sb : Nat) (k : CK) (pb : Nat) (pool : Array EmbC.Val) (hb : Nat)
    (htab : Array EmbC.Val) : Prop where
  ck : HasCK m sb k
  poolPtr : k.pool = some (pb, 0)
  htabPtr : k.htab = some (hb, 0)
  pool : HasArr m pb pool
  htab : HasArr m hb htab
  ne : hb ≠ pb
  frame : ∀ b, b ≠ sb → b ≠ hb → m.block? b = m0.block? b
  size : m.blocks.size = m0.blocks.size

section
variable {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {m0 m : Mem} {sb : Nat} {k : CK}
  {pb hb : Nat} {pool htab : Array EmbC.Val}

theorem HView.hb_ne_sb (h : HView m0 m sb k pb pool hb htab) : hb ≠ sb := by
  intro e
  have h1 := h.htab; have h2 := h.ck
  rw [e] at h1
  unfold HasArr at h1; unfold HasCK at h2
  rw [h1] at h2; simp at h2

theorem HView.pb_ne_sb (h : HView m0 m sb k pb pool hb htab) : pb ≠ sb := by
  intro e
  have h1 := h.pool; have h2 := h.ck
  rw [e] at h1
  unfold HasArr at h1; unfold HasCK at h2
  rw [h1] at h2; simp at h2

theorem HView.ld_pool (hs : P.findStruct "ck" = some ckS) (h : HView m0 m sb k pb pool hb htab) :
    m.loadField P sb "pool" = some (.ptr pb 0) := by
  rw [HasCK.ld_pool hs h.ck, h.poolPtr]; rfl

theorem HView.ld_htab (hs : P.findStruct "ck" = some ckS) (h : HView m0 m sb k pb pool hb htab) :
    m.loadField P sb "htab" = some (.ptr hb 0) := by
  rw [HasCK.ld_htab hs h.ck, h.htabPtr]; rfl

/-- Setting a `u32` field of the struct. -/
theorem HView.setU32 (hs : P.findStruct "ck" = some ckS) (h : HView m0 m sb k pb pool hb htab)
    {f : String} {x : BitVec 32} {i : Nat} {k' : CK} (hk : k.setU32 f x = some (i, k')) :
    m.storeField P sb f (.u32 x) = some (m.setCell sb i (.u32 x)) ∧
    HView m0 (m.setCell sb i (.u32 x)) sb k' pb pool hb htab := by
  obtain ⟨hf, hc, hp, hi⟩ := CK.setU32_ok hk
  have hlt : i < k.cells.size := by simpa [CK.cells] using hi
  have hb' := fun b' => Mem.block?_setCell (i := i) (v := .u32 x) b' h.ck
  simp only [CK.ptr4, List.cons.injEq, and_true] at hp
  obtain ⟨h1, h2, -⟩ := hp
  refine ⟨Mem.storeField_eq (by rw [ck_slot hs h.ck, hf]) (by simp) hlt, ?_, ?_, ?_, ?_, ?_, h.ne,
    ?_, ?_⟩
  · show (m.setCell sb i (.u32 x)).block? sb = _
    rw [hb']; simp [hc]
  · rw [h1]; exact h.poolPtr
  · rw [h2]; exact h.htabPtr
  · show (m.setCell sb i (.u32 x)).block? pb = _
    rw [hb']; simp only [h.pb_ne_sb, ↓reduceIte]; exact h.pool
  · show (m.setCell sb i (.u32 x)).block? hb = _
    rw [hb']; simp only [h.hb_ne_sb, ↓reduceIte]; exact h.htab
  · intro b hbs hbh
    rw [hb']; simp only [hbs, ↓reduceIte]; exact h.frame b hbs hbh
  · rw [Mem.size_setCell]; exact h.size

/-- Writing a slot of the table. -/
theorem HView.storeHtab (h : HView m0 m sb k pb pool hb htab) {i : Nat} (hi : i < htab.size)
    (x : BitVec 32) :
    m.storeArr hb i (.u32 x) = some (m.setCell hb i (.u32 x)) ∧
    HView m0 (m.setCell hb i (.u32 x)) sb k pb pool hb (htab.setIfInBounds i (.u32 x)) := by
  have hb' := fun b' => Mem.block?_setCell (i := i) (v := .u32 x) b' h.htab
  refine ⟨Mem.storeArr_eq h.htab rfl (by simp) hi, ?_, h.poolPtr, h.htabPtr, ?_, ?_, h.ne, ?_, ?_⟩
  · show (m.setCell hb i (.u32 x)).block? sb = _
    rw [hb']; simp only [Ne.symm h.hb_ne_sb, ↓reduceIte]; exact h.ck
  · show (m.setCell hb i (.u32 x)).block? pb = _
    rw [hb']; simp only [Ne.symm h.ne, ↓reduceIte]; exact h.pool
  · show (m.setCell hb i (.u32 x)).block? hb = _
    rw [hb']; simp
  · intro b hbs hbh
    rw [hb']; simp only [hbh, ↓reduceIte]; exact h.frame b hbs hbh
  · rw [Mem.size_setCell]; exact h.size

/-- `p->f = e` for a `u32` field, over `HView`. -/
theorem WP.hv_setField {p e : Expr} {f : String}
    (hs : P.findStruct "ck" = some ckS) {m : Mem} (h : HView m0 m sb k pb pool hb htab)
    (hm : st.mem = m)
    (H : match evalE P env st.mem p, evalE P env st.mem e with
      | some (.ptr b off), some (.u32 x) =>
        b = sb ∧ off = 0 ∧
        match k.setU32 f x with
        | none => False
        | some (_, k') => ∀ st', HView m0 st'.mem sb k' pb pool hb htab → Q .normal env st'
      | _, _ => False) :
    WP P (.setField p f e) Q env st := by
  subst hm
  apply WP.setField
  split at H
  · rename_i b off x hp he
    obtain ⟨rfl, rfl, H⟩ := H
    rw [hp, he]; dsimp only
    refine ⟨rfl, ?_⟩
    split at H
    · exact H.elim
    · rename_i i k' hk
      obtain ⟨hst, hh⟩ := h.setU32 hs hk
      rw [hst]; exact H _ hh
  · exact H.elim

/-- `p[i] = e` where `p` points at the table, over `HView`. -/
theorem WP.hv_store {p i e : Expr} {m : Mem} (h : HView m0 m sb k pb pool hb htab)
    (hm : st.mem = m)
    (H : match evalE P env st.mem p, evalE P env st.mem i, evalE P env st.mem e with
      | some (.ptr b' off), some vi, some (.u32 x) =>
        b' = hb ∧
        match vi.toIdx with
        | none => False
        | some kx =>
          off + kx < htab.size ∧
          ∀ st', HView m0 st'.mem sb k pb pool hb (htab.setIfInBounds (off + kx) (.u32 x)) →
            Q .normal env st'
      | _, _, _ => False) :
    WP P (.store p i e) Q env st := by
  subst hm
  apply WP.store
  split at H
  · rename_i b' off vi x hp' hi he
    obtain ⟨rfl, H⟩ := H
    rw [hp', hi, he]; dsimp only
    split at H
    · exact H.elim
    · rename_i kx hk
      rw [hk]; dsimp only
      obtain ⟨hlt, H⟩ := H
      obtain ⟨hst, hh⟩ := h.storeHtab hlt x
      rw [hst]; exact H _ hh
  · exact H.elim

end

/-- `ck_simp` for a state described by `h : HView …`. -/
macro "hv_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let h := Lean.mkIdent `h
  let hs := Lean.mkIdent `hs
  `(tactic| embc_simp [CK.setU32,
      HView.ld_pool $hs $h, HasCK.ld_plen $hs (HView.ck $h),
      HasCK.ld_pcap $hs (HView.ck $h), HView.ld_htab $hs $h,
      HasCK.ld_hcap $hs (HView.ck $h), HasCK.ld_hcnt $hs (HView.ck $h),
      HasCK.ld_work $hs (HView.ck $h), HasCK.ld_err $hs (HView.ck $h),
      HasArr.loadArr (HView.pool $h),
      HasArr.loadArr (HView.htab $h), $ts,*])

macro "hv_simp" : tactic => `(tactic| hv_simp [])

/-! ## Reading a node's words -/

/-- The machine words of a node, as `ck_hash` and `words_eq` read them. -/
theorem WordsAt.cells {cells : Array EmbC.Val} {start : Nat} {ws : List Nat}
    (h : WordsAt cells start ws) :
    ∀ j w, (ws.map (BitVec.ofNat 32))[j]? = some w → cells[start + j]? = some (.u32 w) := by
  intro j w hw
  rw [List.getElem?_map] at hw
  cases hk : ws[j]? with
  | none => rw [hk] at hw; cases hw
  | some x =>
    rw [hk] at hw
    simp only [Option.map_some, Option.some.injEq] at hw
    subst hw
    exact h j x hk

/-- `1 + ((hdr >> 8) & 0xff)` on a node's header is its size. -/
theorem size_word {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    1#32 + (BitVec.ofNat 32 (hdrW n) >>> 8 &&& 255#32) = BitVec.ofNat 32 (nodeSize n) := by
  apply BitVec.eq_of_toNat_eq
  have h1 := hdrW_lt hf
  have h2 := hf.tailLen
  have h3 := hdrW_nodeSize hf
  rw [BitVec.toNat_add, bv_and_ff, bv_shr_8, bv_toNat_ofNat h1, bv_toNat_ofNat (by omega)]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem nodeSize_le {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) : nodeSize n ≤ 256 := by
  have := hf.tailLen; unfold nodeSize; omega

/-! ## `ck_hput` -/

/-- The probing loop of `ck_hput`: only `work` has changed. -/
def HputInv (m0 : Mem) (sb : Nat) (k : CK) (pb : Nat) (pool : Array EmbC.Val) (hb : Nat)
    (htab : Array EmbC.Val) (id hv nw : BitVec 32) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (wk i : BitVec 32) (d : Nat),
    HView m0 s'.mem sb { k with work := wk } pb pool hb htab ∧
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, .u32 id), ("i", .u32, .u32 i),
      ("mask", .u32, .u32 (k.hcap - 1#32)), ("h", .u32, .u32 hv), ("n", .u32, .u32 nw)] ∧
    i.toNat = (hv.toNat + d) % k.hcap.toNat ∧
    ∀ d', d' < d → ¬ U htab ((hv.toNat + d') % k.hcap.toNat) 0

/-- What `ck_hput` leaves: either the work budget ran out and nothing but
`work` and `err` changed, or the id is entered in an empty slot and the
count is one more. -/
def HputPost (m0 : Mem) (sb : Nat) (k : CK) (pb : Nat) (pool : Array EmbC.Val) (hb : Nat)
    (htab : Array EmbC.Val) (posOf : Nat → Nat) (lp : Pool) (S : Nat → Prop) (id : BitVec 32)
    (x : Nat) (rv : Option EmbC.Val) (s' : (KernelState prog State)) : Prop :=
  (rv = some (.u32 0#32) ∧
    ∃ wk er, HView m0 s'.mem sb { k with work := wk, err := er } pb pool hb htab) ∨
  (rv = some (.u32 1#32) ∧ ∃ slot wk, U htab slot 0 ∧ slot < htab.size ∧
    HView m0 s'.mem sb { k with hcnt := k.hcnt + 1#32, work := wk } pb pool hb
      (htab.setIfInBounds slot (.u32 (id + 1#32))) ∧
    HtabPart posOf lp (htab.setIfInBounds slot (.u32 (id + 1#32))) k.hcap.toNat
      (fun i => S i ∨ i = x))

/-- `ck_hput(st, id)`: enters node `x` (with id `id`) in the table, in the
first empty slot of its probe sequence, and adds one to `hcnt`, unless the
work budget runs out first.  No duplicate check.  The table may be partial
(`HtabPart … S`). -/
theorem ck_hput_spec (m0 : Mem) (sb : Nat) (k : CK) (pb : Nat) (pool : Array EmbC.Val) (hb : Nat)
    (htab : Array EmbC.Val) (posOf : Nat → Nat) (lp : Pool) (plen : Nat) (S : Nat → Prop)
    (id : BitVec 32) (x : Nat) (n : Node) :
    FnSpec (State := State) Vbcf.prog "ck_hput"
      (fun vs s => vs = [.ptr sb 0, .u32 id] ∧ HView m0 s.mem sb k pb pool hb htab ∧
        PoolRep posOf lp pool plen ∧ plen ≤ 2 ^ 30 ∧ HtabPart posOf lp htab k.hcap.toNat S ∧
        lp[x]? = some n ∧ id.toNat = offs lp x)
      (fun _ _ rv s' => HputPost m0 sb k pb pool hb htab posOf lp S id x rv s') := by
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckHput) rfl
  rintro vs s ⟨rfl, h, hrep, hplen, hpart, hx, hid⟩
  simp [ckHput, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hfit := hrep.fits x n hx
  have hend := hrep.node_end hx
  have hlen := hrep.len
  obtain ⟨j, hj, hj30⟩ := hpart.pow
  have hszw := size_word hfit
  have hnsz := nodeSize_le hfit
  apply WP.seq; apply WP.assign; hv_simp
  -- n = 1 + ((st->pool[id] >> 8) & 0xff);
  apply WP.seq; apply WP.assign; hv_simp [hid, rd_u32 (hrep.hdr hx), hszw]
  -- pay for hashing it
  apply WP.seq
  apply WP.ite
  hv_simp
  constructor
  · intro _
    apply WP.seq
    apply WP.hv_setField hs h (by rfl)
    hv_simp
    intro s1 h
    apply WP.ret
    hv_simp [retPost]
    exact Or.inl ⟨rfl, _, _, h⟩
  intro _
  apply WP.skip
  apply WP.seq
  apply WP.hv_setField hs h (by rfl)
  hv_simp
  clear h
  intro s1 h
  apply WP.seq
  apply WP.call (ck_hash_spec sb _ pb pool id (BitVec.ofNat 32 (nodeSize n))
    ((nodeW posOf lp n).map (BitVec.ofNat 32)))
  hv_simp [hid, rd_u32 (hrep.hdr hx), hszw]
  refine ⟨⟨h.ck, h.poolPtr, h.pool, ?_, ?_, ?_⟩, ?_⟩
  · rw [nodeW_length]; omega
  · omega
  · exact fun j a hj => hrep.cell x n hx j a hj
  apply WP.seq; apply WP.assign; hv_simp
  apply WP.seq
  apply WP.while (I := HputInv m0 sb k pb pool hb htab id (hashNode posOf lp n)
    (BitVec.ofNat 32 (nodeSize n)))
  · exact ⟨_, _, 0, h, rfl, probe_start _ hj, fun _ hd => absurd hd (Nat.not_lt_zero _)⟩
  · rintro env s' ⟨wk, i, d, h', rfl, hi, hpre⟩
    clear h
    have h := h'
    clear h'
    obtain ⟨e0, hu, he32, -⟩ := hpart.slot ((hashNode posOf lp n).toNat + d)
    rw [← hi] at hu
    hv_simp [rd_u32 hu, ofNat32_eq_zero_iff he32]
    constructor
    · intro he0
      subst he0
      have hilt : i.toNat < htab.size := by
        rw [hi, hpart.size]; exact Nat.mod_lt _ hpart.pos
      apply WP.seq
      apply WP.hv_store h rfl
      hv_simp
      refine ⟨hilt, ?_⟩
      intro s1 h
      apply WP.seq
      apply WP.hv_setField hs h (by rfl)
      hv_simp
      intro s2 h
      apply WP.ret
      hv_simp [retPost]
      refine Or.inr ⟨rfl, i.toNat, wk, hu, hilt, h, ?_⟩
      have hins := hpart.insert (by omega) hx hpre (hi ▸ hu)
      rw [← hi, ← hid, ofNat_succ_toNat] at hins
      exact hins
    · intro he0
      -- one unit of work per probe
      apply WP.seq
      apply WP.ite
      hv_simp
      constructor
      · intro _
        apply WP.seq
        apply WP.hv_setField hs h (by rfl)
        hv_simp
        intro s1 h
        apply WP.ret
        hv_simp [retPost]
        exact Or.inl ⟨rfl, _, _, h⟩
      intro _
      apply WP.skip
      apply WP.seq
      apply WP.hv_setField hs h (by rfl)
      hv_simp
      intro s1 h
      apply WP.assign
      hv_simp
      refine ⟨_, _, d + 1, h, rfl, probe_next hj (by omega) hi, ?_⟩
      intro d' hd'
      by_cases hdd : d' < d
      · exact hpre d' hdd
      · have : d' = d := by omega
        subst this
        intro h0
        exact he0 (U.inj32 (hi ▸ hu) h0 he32 (by decide))

end Vbcf.Proof
