import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Hash1

/-!
# Vbcf proofs: the hash table, as pure data

No C here.  The table is an array of words; slot contents are `0` (empty) or
one more than a node's offset.  A probe from hash `h` visits the slots
`(h + d) % hcap` for `d = 0, 1, …`.

* `Reach`: a node id is reachable from a hash through occupied slots.
* `HtabPart`: `HtabOK` restricted to a set of nodes (the table while
  `ck_hgrow` refills it); `HtabOK` is the case of all nodes.
* `HtabPart.miss`: lookup is exact; a probe that reaches an empty slot has
  proved the node absent.
* `HtabPart.insert`, `HtabPart.push`: entering a node in the empty slot its
  probe reached.
* `nzCount`: the number of occupied slots, the extra invariant `ck_hgrow`
  needs to re-establish `hcnt = pool.size`.
-/


namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ## Words -/

theorem ofNat32_eq_zero_iff {e : Nat} (h : e < 2 ^ 32) : BitVec.ofNat 32 e = 0#32 ↔ e = 0 := by
  rw [← BitVec.toNat_inj, bv_toNat_ofNat h]; simp

theorem ofNat_succ_toNat (x : BitVec 32) : BitVec.ofNat 32 (x.toNat + 1) = x + 1#32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem U.inj32 {cells : Array EmbC.Val} {i a b : Nat} (ha : U cells i a) (hb : U cells i b)
    (h1 : a < 2 ^ 32) (h2 : b < 2 ^ 32) : a = b := by
  unfold U at ha hb
  rw [ha] at hb
  simp only [Option.some.injEq, EmbC.Val.u32.injEq] at hb
  exact (bv_ofNat_inj h1 h2).mp hb

theorem U.set_self {cells : Array EmbC.Val} {s : Nat} (w : Nat) (hs : s < cells.size) :
    U (cells.setIfInBounds s (.u32 (BitVec.ofNat 32 w))) s w := by
  unfold U
  rw [Array.getElem?_setIfInBounds]
  simp [hs]

theorem U.set_ne {cells : Array EmbC.Val} {s s' : Nat} {x : EmbC.Val} {w : Nat} (hne : s' ≠ s) :
    U (cells.setIfInBounds s x) s' w ↔ U cells s' w := by
  unfold U
  rw [Array.getElem?_setIfInBounds]
  have : ¬ s = s' := fun e => hne e.symm
  simp only [this, ↓reduceIte]

/-! ## Masking with `hcap - 1` -/

theorem bv_mask_toNat {hcap : BitVec 32} {j : Nat} (hj : hcap.toNat = 2 ^ j) :
    (hcap - 1#32).toNat = 2 ^ j - 1 := by
  have h1 : 1 ≤ hcap.toNat := by rw [hj]; exact Nat.one_le_two_pow
  rw [bv_sub_toNat (by simpa using h1), hj]; rfl

/-- `x & (hcap - 1)` is `x % hcap` when `hcap` is a power of two. -/
theorem bv_and_mask (x : BitVec 32) {hcap : BitVec 32} {j : Nat} (hj : hcap.toNat = 2 ^ j) :
    (x &&& (hcap - 1#32)).toNat = x.toNat % hcap.toNat := by
  rw [BitVec.toNat_and, bv_mask_toNat hj, Nat.and_two_pow_sub_one_eq_mod, hj]

/-- The first slot of a probe. -/
theorem probe_start (h : BitVec 32) {hcap : BitVec 32} {j : Nat} (hj : hcap.toNat = 2 ^ j) :
    (h &&& (hcap - 1#32)).toNat = (h.toNat + 0) % hcap.toNat := by
  rw [bv_and_mask h hj, Nat.add_zero]

/-- The next slot of a probe. -/
theorem probe_next {i h hcap : BitVec 32} {j d : Nat} (hj : hcap.toNat = 2 ^ j) (hj32 : j ≤ 32)
    (hi : i.toNat = (h.toNat + d) % hcap.toNat) :
    ((i + 1#32) &&& (hcap - 1#32)).toNat = (h.toNat + (d + 1)) % hcap.toNat := by
  rw [bv_and_mask _ hj, BitVec.toNat_add, hi, hj]
  have hd : 2 ^ j ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hj32
  rw [Nat.mod_mod_of_dvd _ hd]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem slot_lt {hcap : Nat} (x : Nat) (h : ∃ j, hcap = 2 ^ j ∧ j ≤ 30) : x % hcap < hcap := by
  obtain ⟨j, rfl, _⟩ := h
  exact Nat.mod_lt _ (Nat.two_pow_pos j)

/-! ## Reachability -/

/-- Node id `v` (an offset) is reachable from hash `h`: some slot of the
probe sequence holds `v + 1`, and no earlier slot is empty. -/
def Reach (htab : Array EmbC.Val) (hcap : Nat) (h : BitVec 32) (v : Nat) : Prop :=
  ∃ d, d < hcap ∧ U htab ((h.toNat + d) % hcap) (v + 1) ∧
    ∀ d', d' < d → ¬ U htab ((h.toNat + d') % hcap) 0

/-- Filling an empty slot keeps every reachable id reachable. -/
theorem Reach.set {htab : Array EmbC.Val} {hcap : Nat} {h : BitVec 32} {v s : Nat} {x : EmbC.Val}
    (hr : Reach htab hcap h v) (hv : v + 1 < 2 ^ 32) (hs : U htab s 0) (hx : x ≠ .u32 0#32) :
    Reach (htab.setIfInBounds s x) hcap h v := by
  obtain ⟨d, hd, hu, hpre⟩ := hr
  refine ⟨d, hd, ?_, ?_⟩
  · have hne : (h.toNat + d) % hcap ≠ s := by
      intro e; rw [e] at hu
      have := U.inj32 hu hs hv (by decide)
      omega
    exact (U.set_ne hne).mpr hu
  · intro d' hd' hu'
    by_cases he : (h.toNat + d') % hcap = s
    · rw [he] at hu'
      unfold U at hu'
      rw [Array.getElem?_setIfInBounds] at hu'
      simp only [↓reduceIte] at hu'
      split at hu'
      · simp only [Option.some.injEq] at hu'; exact hx hu'
      · cases hu'
    · exact hpre d' hd' ((U.set_ne he).mp hu')

/-- The id entered at the end of a probe over occupied slots is reachable. -/
theorem Reach.new {htab : Array EmbC.Val} {hcap : Nat} {h : BitVec 32} {v d : Nat}
    (hpos : 0 < hcap) (hsz : htab.size = hcap) (hv : v + 1 < 2 ^ 32)
    (hpre : ∀ d', d' < d → ¬ U htab ((h.toNat + d') % hcap) 0) :
    Reach (htab.setIfInBounds ((h.toNat + d) % hcap) (.u32 (BitVec.ofNat 32 (v + 1)))) hcap h v := by
  have hslot : (h.toNat + d % hcap) % hcap = (h.toNat + d) % hcap := by
    rw [Nat.add_mod_mod]
  have hlt : (h.toNat + d) % hcap < htab.size := by rw [hsz]; exact Nat.mod_lt _ hpos
  refine ⟨d % hcap, Nat.mod_lt _ hpos, ?_, ?_⟩
  · rw [hslot]; exact U.set_self _ hlt
  · intro d' hd' hu'
    have hd'' : d' < d := Nat.lt_of_lt_of_le hd' (Nat.mod_le _ _)
    by_cases he : (h.toNat + d') % hcap = (h.toNat + d) % hcap
    · rw [he] at hu'
      have := U.inj32 hu' (U.set_self (v + 1) hlt) (by decide) hv
      omega
    · exact hpre d' hd'' ((U.set_ne he).mp hu')

/-! ## The table restricted to a set of nodes -/

/-- `HtabOK` without the counters, and with reachability only for the nodes
in `S`. -/
structure HtabPart (posOf : Nat → Nat) (pool : Pool) (htab : Array EmbC.Val) (hcap : Nat)
    (S : Nat → Prop) : Prop where
  size : htab.size = hcap
  pow : ∃ j, hcap = 2 ^ j ∧ j ≤ 30
  cell : ∀ s, s < hcap → ∃ e : Nat, U htab s e ∧ e < 2 ^ 32 ∧
    (e ≠ 0 → ∃ i, i < pool.size ∧ e = offs pool i + 1)
  find : ∀ (i : Nat) (n : Node), pool[i]? = some n → S i →
    Reach htab hcap (hashNode posOf pool n) (offs pool i)

theorem HtabOK.part {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap hcnt : Nat}
    (h : HtabOK posOf pool htab hcap hcnt) : HtabPart posOf pool htab hcap (fun _ => True) :=
  ⟨h.size, h.pow, h.cell, fun i n hn _ => h.find i n hn⟩

theorem HtabPart.toOK {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap hcnt : Nat}
    {S : Nat → Prop} (h : HtabPart posOf pool htab hcap S) (hS : ∀ i, i < pool.size → S i)
    (hcnt' : hcnt = pool.size) (hnz : nzCount htab = hcnt) (hload : 2 * pool.size ≤ hcap) :
    HtabOK posOf pool htab hcap hcnt :=
  ⟨h.size, h.pow, hcnt', hnz, hload, h.cell,
    fun i n hn => h.find i n hn (hS i (lt_size_of_getElem? hn))⟩

theorem HtabPart.pos {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap : Nat}
    {S : Nat → Prop} (h : HtabPart posOf pool htab hcap S) : 0 < hcap := by
  obtain ⟨j, rfl, _⟩ := h.pow
  exact Nat.two_pow_pos j

/-- The slot a probe is at holds a word; it is `0` or a node's id plus one. -/
theorem HtabPart.slot {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap : Nat}
    {S : Nat → Prop} (h : HtabPart posOf pool htab hcap S) (x : Nat) :
    ∃ e : Nat, U htab (x % hcap) e ∧ e < 2 ^ 32 ∧
      (e ≠ 0 → ∃ i, i < pool.size ∧ e = offs pool i + 1) :=
  h.cell _ (Nat.mod_lt _ h.pos)

/-- A freshly zeroed table. -/
theorem HtabPart.zero (posOf : Nat → Nat) (pool : Pool) {hcap : Nat}
    (hp : ∃ j, hcap = 2 ^ j ∧ j ≤ 30) :
    HtabPart posOf pool (Array.replicate hcap (.u32 0#32)) hcap (fun _ => False) where
  size := by simp
  pow := hp
  cell := by
    intro s hs
    refine ⟨0, ?_, by decide, fun e => absurd rfl e⟩
    unfold U
    simp [hs]
  find := fun _ _ _ hf => hf.elim

/-- Slots `0 .. d` of the probe from `h` are occupied, none by a node equal to `n`. -/
def Probed (pool : Pool) (htab : Array EmbC.Val) (hcap : Nat) (h : BitVec 32) (n : Node)
    (d : Nat) : Prop :=
  ∀ d', d' < d → ¬ U htab ((h.toNat + d') % hcap) 0 ∧
    ∀ i, i < pool.size → U htab ((h.toNat + d') % hcap) (offs pool i + 1) → pool[i]? ≠ some n

theorem Probed.zero (pool : Pool) (htab : Array EmbC.Val) (hcap : Nat) (h : BitVec 32) (n : Node) :
    Probed pool htab hcap h n 0 := fun _ hd => absurd hd (Nat.not_lt_zero _)

/-- One more occupied slot that is not `n`. -/
theorem Probed.step {pool : Pool} {htab : Array EmbC.Val} {hcap : Nat} {h : BitVec 32} {n : Node}
    {d e : Nat} (hp : Probed pool htab hcap h n d) (hb : offs pool pool.size < 2 ^ 32)
    (hu : U htab ((h.toNat + d) % hcap) e) (he : e ≠ 0) (he32 : e < 2 ^ 32)
    (hne : ∀ i, i < pool.size → e = offs pool i + 1 → pool[i]? ≠ some n) :
    Probed pool htab hcap h n (d + 1) := by
  intro d' hd'
  by_cases hdd : d' < d
  · exact hp d' hdd
  · have : d' = d := by omega
    subst this
    refine ⟨fun h0 => he (U.inj32 hu h0 he32 (by decide)), fun i hi hui => ?_⟩
    have := offs_lt_end hi
    exact hne i hi (U.inj32 hu hui he32 (by omega))

/-- **Lookup is exact.**  A probe from the node's hash that reaches an empty
slot without meeting the node shows the node is not in (the `S` part of) the pool. -/
theorem HtabPart.miss {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap : Nat}
    {S : Nat → Prop} (h : HtabPart posOf pool htab hcap S) {n : Node} {d : Nat}
    (hb : offs pool pool.size < 2 ^ 32)
    (hp : Probed pool htab hcap (hashNode posOf pool n) n d)
    (h0 : U htab (((hashNode posOf pool n).toNat + d) % hcap) 0) :
    ∀ i, S i → pool[i]? ≠ some n := by
  intro i hS hn
  have hi := lt_size_of_getElem? hn
  have hoff := offs_lt_end hi
  obtain ⟨di, _, hu, hpre⟩ := h.find i n hn hS
  rcases Nat.lt_trichotomy d di with hlt | heq | hgt
  · exact hpre d hlt h0
  · subst heq
    have := U.inj32 hu h0 (by omega) (by decide)
    omega
  · exact (hp di hgt).2 i hi hu hn

/-- Entering node `x` in the empty slot its probe reached. -/
theorem HtabPart.insert {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap : Nat}
    {S : Nat → Prop} (h : HtabPart posOf pool htab hcap S) {x : Nat} {n : Node} {d : Nat}
    (hb : offs pool pool.size < 2 ^ 32) (hx : pool[x]? = some n)
    (hpre : ∀ d', d' < d → ¬ U htab (((hashNode posOf pool n).toNat + d') % hcap) 0)
    (h0 : U htab (((hashNode posOf pool n).toNat + d) % hcap) 0) :
    HtabPart posOf pool
      (htab.setIfInBounds (((hashNode posOf pool n).toNat + d) % hcap)
        (.u32 (BitVec.ofNat 32 (offs pool x + 1)))) hcap (fun i => S i ∨ i = x) where
  size := by rw [Array.size_setIfInBounds]; exact h.size
  pow := h.pow
  cell := by
    intro s hs
    have hxl := lt_size_of_getElem? hx
    by_cases he : s = ((hashNode posOf pool n).toNat + d) % hcap
    · subst he
      have := offs_lt_end hxl
      exact ⟨offs pool x + 1, U.set_self _ (by rw [h.size]; exact hs), by omega,
        fun _ => ⟨x, hxl, rfl⟩⟩
    · obtain ⟨e, hu, he32, hnode⟩ := h.cell s hs
      exact ⟨e, (U.set_ne he).mpr hu, he32, hnode⟩
  find := by
    intro i m hm hS
    have hxl := lt_size_of_getElem? hx
    have hox := offs_lt_end hxl
    have hnz : EmbC.Val.u32 (BitVec.ofNat 32 (offs pool x + 1)) ≠ .u32 0#32 := by
      intro e
      simp only [EmbC.Val.u32.injEq] at e
      have := (ofNat32_eq_zero_iff (by omega)).mp e
      omega
    by_cases hix : i = x
    · subst hix
      rw [hx] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      exact Reach.new h.pos h.size (by omega) hpre
    · have hSi : S i := by
        rcases hS with hS | hS
        · exact hS
        · exact absurd hS hix
      have := offs_lt_end (lt_size_of_getElem? hm)
      exact (h.find i m hm hSi).set (by omega) h0 hnz

/-- The table of `pool` is a partial table of `pool.push m`, knowing the old nodes. -/
theorem HtabPart.push {posOf : Nat → Nat} {pool : Pool} {htab : Array EmbC.Val} {hcap : Nat}
    {S : Nat → Prop} (h : HtabPart posOf pool htab hcap S) (m : Node)
    (hwf : ∀ (i : Nat) (n : Node), pool[i]? = some n → ∀ a ∈ n.args, a < pool.size) :
    HtabPart posOf (pool.push m) htab hcap (fun i => i < pool.size ∧ S i) where
  size := h.size
  pow := h.pow
  cell := by
    intro s hs
    obtain ⟨e, hu, he32, hnode⟩ := h.cell s hs
    refine ⟨e, hu, he32, fun he => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hnode he
    exact ⟨i, by rw [Array.size_push]; omega, by rw [offs_push m (Nat.le_of_lt hi)]⟩
  find := by
    intro i n hn ⟨hi, hS⟩
    rw [Array.getElem?_push] at hn
    simp only [Nat.ne_of_lt hi, ↓reduceIte] at hn
    have hw : nodeW posOf (pool.push m) n = nodeW posOf pool n :=
      nodeW_push m (fun a ha => Nat.le_of_lt (hwf i n hn a ha))
    have hh : hashNode posOf (pool.push m) n = hashNode posOf pool n := by
      unfold hashNode; rw [hw]
    rw [hh, offs_push m (Nat.le_of_lt hi)]
    exact h.find i n hn hS

/-! ## Counting occupied slots -/

/-- Number of occupied slots among the first `i`. -/
def nzUpTo (htab : Array EmbC.Val) (i : Nat) : Nat :=
  (htab.toList.take i).countP (fun v => v != EmbC.Val.u32 0#32)

theorem nzUpTo_zero (htab : Array EmbC.Val) : nzUpTo htab 0 = 0 := by simp [nzUpTo]

theorem nzUpTo_size (htab : Array EmbC.Val) {i : Nat} (h : htab.size ≤ i) :
    nzUpTo htab i = nzCount htab := by
  unfold nzUpTo nzCount
  rw [List.take_of_length_le (by simpa using h)]

theorem nzUpTo_le (htab : Array EmbC.Val) (i : Nat) : nzUpTo htab i ≤ i := by
  unfold nzUpTo
  refine Nat.le_trans (List.countP_le_length) ?_
  simp [List.length_take]; omega

theorem nzUpTo_succ {htab : Array EmbC.Val} {i : Nat} {v : EmbC.Val} (h : htab[i]? = some v) :
    nzUpTo htab (i + 1) = nzUpTo htab i + (if v = .u32 0#32 then 0 else 1) := by
  unfold nzUpTo
  have h' : htab.toList[i]? = some v := by simpa using h
  rw [List.take_add_one, h']
  simp only [Option.toList_some, List.countP_append, List.countP_cons, List.countP_nil,
    Nat.zero_add]
  by_cases hv : v = .u32 0#32 <;> simp [hv]

theorem nzCount_replicate (n : Nat) : nzCount (Array.replicate n (.u32 0#32)) = 0 := by
  simp [nzCount, List.countP_eq_zero]

private theorem countP_set_nz {l : List EmbC.Val} {s : Nat} {x : EmbC.Val}
    (h0 : l[s]? = some (.u32 0#32)) (hx : x ≠ .u32 0#32) :
    (l.set s x).countP (fun v => v != EmbC.Val.u32 0#32) =
      l.countP (fun v => v != EmbC.Val.u32 0#32) + 1 := by
  induction l generalizing s with
  | nil => simp at h0
  | cons a l ih =>
    cases s with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      simp [hx]
    | succ s =>
      simp only [List.getElem?_cons_succ] at h0
      simp only [List.set_cons_succ, List.countP_cons, ih h0]
      omega

/-- Filling an empty slot adds one to the count. -/
theorem nzCount_set {htab : Array EmbC.Val} {s : Nat} {x : EmbC.Val}
    (h0 : U htab s 0) (hx : x ≠ .u32 0#32) :
    nzCount (htab.setIfInBounds s x) = nzCount htab + 1 := by
  unfold nzCount
  have h' : htab.toList[s]? = some (.u32 0#32) := by
    have : htab[s]? = some (.u32 0#32) := h0
    simpa using this
  rw [Array.toList_setIfInBounds]
  exact countP_set_nz h' hx

end Vbcf.Proof
