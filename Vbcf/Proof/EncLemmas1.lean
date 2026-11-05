import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Spec

/-!
# Vbcf proofs: lemmas about the pool layout (offsets, node words, `PoolRep`)

Part 1 of `Vbcf/Proof/EncLemmas.lean`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ## A. Offsets -/

theorem nodeSize_pos (n : Node) : 1 ≤ nodeSize n := by
  unfold nodeSize; omega

@[simp] theorem offs_zero (pool : Pool) : offs pool 0 = 0 := by
  simp [offs]

theorem offs_succ {pool : Pool} {i : Nat} {n : Node} (h : pool[i]? = some n) :
    offs pool (i + 1) = offs pool i + nodeSize n := by
  unfold offs
  have h' : pool.toList[i]? = some n := by simpa using h
  rw [List.take_add_one, h']
  simp

/-- Past the end of the pool the offset stops growing. -/
theorem offs_of_size_le {pool : Pool} {i : Nat} (h : pool.size ≤ i) :
    offs pool i = offs pool pool.size := by
  unfold offs
  rw [List.take_of_length_le (by simpa using h), List.take_of_length_le (by simp)]

theorem offs_le_succ (pool : Pool) (i : Nat) : offs pool i ≤ offs pool (i + 1) := by
  rcases h : pool[i]? with _ | n
  · have hi : pool.size ≤ i := by
      rcases Nat.lt_or_ge i pool.size with h' | h'
      · rw [Array.getElem?_eq_getElem h'] at h; cases h
      · exact h'
    rw [offs_of_size_le hi, offs_of_size_le (Nat.le_succ_of_le hi)]
    exact Nat.le_refl _
  · rw [offs_succ h]; omega

theorem offs_le_of_le {pool : Pool} {i j : Nat} (h : i ≤ j) : offs pool i ≤ offs pool j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega)) (offs_le_succ pool j)
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

theorem offs_lt_succ {pool : Pool} {i : Nat} (h : i < pool.size) :
    offs pool i < offs pool (i + 1) := by
  rw [offs_succ (Array.getElem?_eq_getElem h)]
  have := nodeSize_pos pool[i]
  omega

theorem offs_lt_of_lt {pool : Pool} {i j : Nat} (h : i < j) (hj : j ≤ pool.size) :
    offs pool i < offs pool j :=
  Nat.lt_of_lt_of_le (offs_lt_succ (by omega)) (offs_le_of_le h)

theorem offs_inj {pool : Pool} {i j : Nat} (hi : i ≤ pool.size) (hj : j ≤ pool.size)
    (h : offs pool i = offs pool j) : i = j := by
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · have := offs_lt_of_lt h' hj; omega
  · exact h'
  · have := offs_lt_of_lt h' hi; omega

/-- A strict inequality between offsets reflects to the indices (no size bound needed). -/
theorem lt_of_offs_lt {pool : Pool} {i j : Nat} (h : offs pool i < offs pool j) : i < j := by
  rcases Nat.lt_or_ge i j with h' | h'
  · exact h'
  · have := offs_le_of_le (pool := pool) h'; omega

theorem offs_lt_iff {pool : Pool} {i j : Nat} (hj : j ≤ pool.size) :
    offs pool i < offs pool j ↔ i < j :=
  ⟨lt_of_offs_lt, fun h => offs_lt_of_lt h hj⟩

theorem offs_le_iff {pool : Pool} {i j : Nat} (hi : i ≤ pool.size) :
    offs pool i ≤ offs pool j ↔ i ≤ j := by
  constructor
  · intro h
    rcases Nat.lt_or_ge j i with h' | h'
    · have := offs_lt_of_lt h' hi; omega
    · exact h'
  · exact offs_le_of_le

/-- An offset below the end of the pool belongs to a node of the pool. -/
theorem lt_size_of_offs_lt {pool : Pool} {i : Nat} (h : offs pool i < offs pool pool.size) :
    i < pool.size :=
  lt_of_offs_lt h

theorem offs_lt_end {pool : Pool} {i : Nat} (h : i < pool.size) :
    offs pool i < offs pool pool.size :=
  offs_lt_of_lt h (Nat.le_refl _)

theorem offs_le_end (pool : Pool) (i : Nat) : offs pool i ≤ offs pool pool.size := by
  rcases Nat.lt_or_ge i pool.size with h | h
  · exact offs_le_of_le (Nat.le_of_lt h)
  · rw [offs_of_size_le h]; exact Nat.le_refl _

theorem offs_node_end {pool : Pool} {i : Nat} {n : Node} (h : pool[i]? = some n) :
    offs pool i + nodeSize n ≤ offs pool pool.size := by
  rw [← offs_succ h]
  exact offs_le_of_le (lt_size_of_getElem? h)

/-- Each node takes at least one word. -/
theorem le_offs {pool : Pool} {i : Nat} (h : i ≤ pool.size) : i ≤ offs pool i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have := offs_lt_succ (pool := pool) (i := i) (by omega)
    have := ih (by omega)
    omega

theorem size_le_offs (pool : Pool) : pool.size ≤ offs pool pool.size :=
  le_offs (Nat.le_refl _)

/-- The header of node `i` and the header of node `j > i` are separated by node `i`'s words. -/
theorem offs_add_size_le {pool : Pool} {i j : Nat} {n : Node} (h : pool[i]? = some n)
    (hij : i < j) : offs pool i + nodeSize n ≤ offs pool j := by
  rw [← offs_succ h]
  exact offs_le_of_le hij

/-- The word ranges of two nodes overlap only if they are the same node. -/
theorem eq_of_offs_overlap {pool : Pool} {i j : Nat} {n m : Node} (hi : pool[i]? = some n)
    (hj : pool[j]? = some m) {k l : Nat} (hk : k < nodeSize n) (hl : l < nodeSize m)
    (h : offs pool i + k = offs pool j + l) : i = j ∧ k = l := by
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · have := offs_add_size_le hi h'; omega
  · subst h'; exact ⟨rfl, by omega⟩
  · have := offs_add_size_le hj h'; omega

theorem offs_push {pool : Pool} {i : Nat} (n : Node) (h : i ≤ pool.size) :
    offs (pool.push n) i = offs pool i := by
  unfold offs
  rw [Array.toList_push, List.take_append_of_le_length (by simpa using h)]

theorem offs_push_size (pool : Pool) (n : Node) :
    offs (pool.push n) (pool.size + 1) = offs pool pool.size + nodeSize n := by
  rw [offs_succ (n := n) (by simp), offs_push n (Nat.le_refl _)]

theorem offs_push_end (pool : Pool) (n : Node) :
    offs (pool.push n) (pool.push n).size = offs pool pool.size + nodeSize n := by
  rw [Array.size_push, offs_push_size]

/-! ## B. Node words -/

/-- The four operators whose tail words are not child ids. -/
def isLeaf : Op → Bool
  | .bvVar _ _ => true
  | .boolVar _ => true
  | .bvVal _ _ => true
  | .boolVal _ => true
  | _ => false

/-- `op` is `bvVar`, `boolVar`, `bvVal` or `boolVal`. -/
abbrev IsLeaf (op : Op) : Prop := isLeaf op = true

theorem isLeaf_iff {op : Op} :
    IsLeaf op ↔ (∃ w id, op = .bvVar w id) ∨ (∃ id, op = .boolVar id) ∨
      (∃ w v, op = .bvVal w v) ∨ (∃ b, op = .boolVal b) := by
  cases op <;> simp [IsLeaf, isLeaf]

theorem tailW_length (posOf off : Nat → Nat) (n : Node) :
    (tailW posOf off n).length = tailLen n := by
  rcases n with ⟨op, args⟩
  cases op <;> simp only [tailW, tailLen, List.length_cons, List.length_nil, List.length_map,
    Array.length_toList]
  split <;> rfl

theorem nodeW_length (posOf : Nat → Nat) (pool : Pool) (n : Node) :
    (nodeW posOf pool n).length = nodeSize n := by
  simp only [nodeW, List.length_cons, tailW_length, nodeSize]; omega

/-- The tail words depend on `off` only at the node's arguments. -/
theorem tailW_congr {posOf off off' : Nat → Nat} {n : Node} (h : ∀ a ∈ n.args, off a = off' a) :
    tailW posOf off n = tailW posOf off' n := by
  rcases n with ⟨op, args⟩
  have hm : args.toList.map off = args.toList.map off' :=
    List.map_congr_left (fun a ha => h a (by simpa using ha))
  cases op <;> simp only [tailW] <;> exact hm

theorem nodeW_push {posOf : Nat → Nat} {pool : Pool} {n : Node} (m : Node)
    (h : ∀ a ∈ n.args, a ≤ pool.size) : nodeW posOf (pool.push m) n = nodeW posOf pool n := by
  unfold nodeW
  rw [tailW_congr (off' := offs pool) (fun a ha => offs_push m (h a ha))]

theorem tailW_of_not_leaf {posOf off : Nat → Nat} {n : Node} (h : ¬ IsLeaf n.op) :
    tailW posOf off n = n.args.toList.map off := by
  rcases n with ⟨op, args⟩
  cases op <;> first | rfl | exact absurd rfl h

theorem tailLen_of_not_leaf {n : Node} (h : ¬ IsLeaf n.op) : tailLen n = n.args.size := by
  rcases n with ⟨op, args⟩
  cases op <;> first | rfl | exact absurd rfl h

theorem nodeSize_of_not_leaf {n : Node} (h : ¬ IsLeaf n.op) : nodeSize n = 1 + n.args.size := by
  rw [nodeSize, tailLen_of_not_leaf h]

/-- The `k`-th tail word of a non-leaf node is its `k`-th argument. -/
theorem tailW_getElem?_of_not_leaf {posOf off : Nat → Nat} {n : Node} (h : ¬ IsLeaf n.op)
    {k : Nat} (hk : k < n.args.size) : (tailW posOf off n)[k]? = some (off n.args[k]) := by
  rw [tailW_of_not_leaf h]
  simp [hk]

@[simp] theorem nodeW_getElem?_zero (posOf : Nat → Nat) (pool : Pool) (n : Node) :
    (nodeW posOf pool n)[0]? = some (hdrW n) := rfl

@[simp] theorem nodeW_getElem?_succ (posOf : Nat → Nat) (pool : Pool) (n : Node) (k : Nat) :
    (nodeW posOf pool n)[k + 1]? = (tailW posOf (offs pool) n)[k]? := rfl

/-! ## H. `PoolRep` -/

theorem lt_length_of_getElem? {α : Type} {ws : List α} {k : Nat} {w : α}
    (h : ws[k]? = some w) : k < ws.length := by
  rcases Nat.lt_or_ge k ws.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

/-- `WordsAt` only looks at the cells `start .. start + ws.length`. -/
theorem WordsAt.congr {cells cells' : Array EmbC.Val} {start : Nat} {ws : List Nat}
    (h : WordsAt cells start ws)
    (hc : ∀ k, k < ws.length → cells'[start + k]? = cells[start + k]?) :
    WordsAt cells' start ws := by
  intro k w hk
  have hlt : k < ws.length := lt_length_of_getElem? hk
  unfold U
  rw [hc k hlt]
  exact h k w hk

theorem PoolRep.hdr {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} {n : Node} (hn : pool[i]? = some n) :
    U cells (offs pool i) (hdrW n) := by
  have := h.cell i n hn 0 (hdrW n) rfl
  simpa using this

/-- The general tail word. -/
theorem PoolRep.tail {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} {n : Node} (hn : pool[i]? = some n)
    {k w : Nat} (hk : (tailW posOf (offs pool) n)[k]? = some w) :
    U cells (offs pool i + 1 + k) w := by
  have := h.cell i n hn (k + 1) w (by simpa using hk)
  rw [Nat.add_assoc, Nat.add_comm 1 k]
  exact this

/-- The `k`-th argument word of a non-leaf node is the offset of its `k`-th argument. -/
theorem PoolRep.arg {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} {n : Node} (hn : pool[i]? = some n)
    (hl : ¬ IsLeaf n.op) {k : Nat} (hk : k < n.args.size) :
    U cells (offs pool i + 1 + k) (offs pool n.args[k]) :=
  h.tail hn (tailW_getElem?_of_not_leaf hl hk)

theorem PoolRep.node_end {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} {n : Node} (hn : pool[i]? = some n) :
    offs pool i + nodeSize n ≤ plen := by
  rw [h.len]; exact offs_node_end hn

theorem PoolRep.offs_lt {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} (hi : i < pool.size) :
    offs pool i < plen := by
  rw [h.len]; exact offs_lt_end hi

theorem PoolRep.offs_lt' {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} {n : Node} (hn : pool[i]? = some n) :
    offs pool i < plen :=
  h.offs_lt (lt_size_of_getElem? hn)

/-- Every word of node `i` lies below `plen`. -/
theorem PoolRep.word_lt {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} {n : Node} (hn : pool[i]? = some n)
    {k : Nat} (hk : k < nodeSize n) : offs pool i + k < plen := by
  have := h.node_end hn; omega

theorem PoolRep.size_le {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) : pool.size ≤ plen := by
  rw [h.len]; exact size_le_offs pool

/-- An offset below `plen` is the offset of a node of the pool. -/
theorem PoolRep.lt_size {posOf : Nat → Nat} {pool : Pool} {cells : Array EmbC.Val} {plen : Nat}
    (h : PoolRep posOf pool cells plen) {i : Nat} (hi : offs pool i < plen) : i < pool.size := by
  rw [h.len] at hi; exact lt_size_of_offs_lt hi

/-- Prefix stability: `PoolRep` only looks at the cells below `plen`. -/
theorem PoolRep.congr {posOf : Nat → Nat} {pool : Pool} {cells cells' : Array EmbC.Val}
    {plen : Nat} (h : PoolRep posOf pool cells plen)
    (hc : ∀ i, i < plen → cells'[i]? = cells[i]?) : PoolRep posOf pool cells' plen where
  len := h.len
  fits := h.fits
  cell := by
    intro i n hn
    apply (h.cell i n hn).congr
    intro k hk
    rw [nodeW_length] at hk
    exact hc _ (h.word_lt hn hk)

/-- Appending a node whose words have been written at the tail of the C pool. -/
theorem PoolRep.push {posOf : Nat → Nat} {pool : Pool} {cells cells' : Array EmbC.Val}
    {plen : Nat} {n : Node} (h : PoolRep posOf pool cells plen) (hf : Fits posOf n)
    (hargs : ∀ a ∈ n.args, a < pool.size)
    (hc : ∀ i, i < plen → cells'[i]? = cells[i]?)
    (hw : WordsAt cells' plen (nodeW posOf pool n))
    (hwf : ∀ (i : Nat) (m : Node), pool[i]? = some m → ∀ a ∈ m.args, a < pool.size) :
    PoolRep posOf (pool.push n) cells' (plen + nodeSize n) where
  len := by rw [offs_push_end, h.len]
  fits := by
    intro i m hm
    rw [Array.getElem?_push] at hm
    split at hm
    · simp only [Option.some.injEq] at hm; subst hm; exact hf
    · exact h.fits i m hm
  cell := by
    intro i m hm
    rw [Array.getElem?_push] at hm
    split at hm
    · rename_i hi
      simp only [Option.some.injEq] at hm; subst hm; subst hi
      rw [offs_push n (Nat.le_refl _), nodeW_push n (fun a ha => Nat.le_of_lt (hargs a ha)),
        ← h.len]
      exact hw
    · have hi : i < pool.size := lt_size_of_getElem? hm
      rw [offs_push n (Nat.le_of_lt hi),
        nodeW_push n (fun a ha => Nat.le_of_lt (hwf i m hm a ha))]
      exact (h.congr hc).cell i m hm

/-! ## I. Positions -/

theorem posOfRaw_lt_succ (raw : Pool) (d : Nat) : posOfRaw raw d < posOfRaw raw (d + 1) := by
  unfold posOfRaw
  rcases Nat.lt_or_ge d raw.size with h | h
  · have h' : raw.toList[d]? = some raw[d] := by simp [h]
    rw [List.take_add_one, h']
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil]
    omega
  · rw [List.take_of_length_le (i := d) (by simpa using h),
      List.take_of_length_le (i := d + 1) (by simp; omega)]
    omega

theorem posOfRaw_strictMono (raw : Pool) {a b : Nat} (h : a < b) :
    posOfRaw raw a < posOfRaw raw b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h' | h'
    · exact Nat.lt_trans (ih h') (posOfRaw_lt_succ raw b)
    · have : a = b := by omega
      subst this; exact posOfRaw_lt_succ raw a

theorem posOfRaw_inj (raw : Pool) : ∀ a b, posOfRaw raw a = posOfRaw raw b → a = b := by
  intro a b h
  rcases Nat.lt_trichotomy a b with h' | h' | h'
  · have := posOfRaw_strictMono raw h'; omega
  · exact h'
  · have := posOfRaw_strictMono raw h'; omega

theorem posOfRaw_lt_iff (raw : Pool) {a b : Nat} : posOfRaw raw a < posOfRaw raw b ↔ a < b := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy a b with h' | h' | h'
    · exact h'
    · subst h'; omega
    · have := posOfRaw_strictMono raw h'; omega
  · exact posOfRaw_strictMono raw

end Vbcf.Proof
