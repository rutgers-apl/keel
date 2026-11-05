import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay5

/-!
# Vbcf proofs: `ck_compact`, part 1 — the compacted pool as pure data

`ck_compact` keeps the nodes of the C-side state `cs` selected by `keep` (every
node below `nL`, and the marked ones), in order, and renames each kept node's
children to their new indices.  The new index of a kept `x` is the number of
kept nodes below it (`cntK`), its new offset is the number of words of the
kept nodes below it (`offK`).  `cst keep cs` is the compacted state; it is a
`PoolOK` state when `keep` is closed under children (`KClosed`).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## Counting kept nodes -/

/-- The number of kept indices below `x`: the new index of a kept `x`. -/
def cntK (keep : Nat → Bool) : Nat → Nat
  | 0 => 0
  | x + 1 => cntK keep x + if keep x then 1 else 0

/-- The number of words of the kept nodes below `x`: the new offset of a kept `x`. -/
def offK (keep : Nat → Bool) (pool : Pool) : Nat → Nat
  | 0 => 0
  | x + 1 => offK keep pool x + if keep x then (pool[x]?.map nodeSize).getD 0 else 0

/-- The kept nodes below `x`, children renamed. -/
def cpL (keep : Nat → Bool) (pool : Pool) : Nat → List Node
  | 0 => []
  | x + 1 => cpL keep pool x ++ if keep x then (pool[x]?.map (Node.ren (cntK keep))).toList else []

/-- The memoised types of the kept nodes below `x`. -/
def ctL (keep : Nat → Bool) (tys : Array Bcf.Ty) : Nat → List Bcf.Ty
  | 0 => []
  | x + 1 => ctL keep tys x ++ if keep x then tys[x]?.toList else []

/-- `keep` is closed under children. -/
def KClosed (keep : Nat → Bool) (pool : Pool) : Prop :=
  ∀ x n, keep x = true → pool[x]? = some n → ∀ a ∈ n.args, keep a = true

section
variable {keep : Nat → Bool} {pool : Pool}

theorem cntK_succ (x : Nat) : cntK keep (x + 1) = cntK keep x + if keep x then 1 else 0 := rfl

theorem cntK_mono {x y : Nat} (h : x ≤ y) : cntK keep x ≤ cntK keep y := by
  induction y with
  | zero => have : x = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ y ih =>
    rcases Nat.lt_or_ge x (y + 1) with h' | h'
    · have := ih (by omega); rw [cntK_succ]; omega
    · have : x = y + 1 := by omega
      subst this; exact Nat.le_refl _

theorem cntK_lt {x y : Nat} (hk : keep x = true) (h : x < y) : cntK keep x < cntK keep y := by
  have h1 : cntK keep (x + 1) = cntK keep x + 1 := by rw [cntK_succ, hk]; rfl
  have h2 := cntK_mono (keep := keep) (show x + 1 ≤ y by omega)
  omega

theorem cntK_le (x : Nat) : cntK keep x ≤ x := by
  induction x with
  | zero => exact Nat.le_refl _
  | succ x ih => rw [cntK_succ]; split <;> omega

/-- `cntK` is injective on kept indices. -/
theorem cntK_inj {x y : Nat} (hx : keep x = true) (hy : keep y = true)
    (h : cntK keep x = cntK keep y) : x = y := by
  rcases Nat.lt_trichotomy x y with h' | h' | h'
  · have := cntK_lt hx h'; omega
  · exact h'
  · have := cntK_lt hy h'; omega

/-- Below a fully kept prefix the new index is the old one. -/
theorem cntK_pre {nL : Nat} (hpre : ∀ y, y < nL → keep y = true) :
    ∀ x, x ≤ nL → cntK keep x = x
  | 0, _ => rfl
  | x + 1, hx => by rw [cntK_succ, cntK_pre hpre x (by omega), hpre x (by omega)]; rfl

theorem cpL_length {x : Nat} (hx : x ≤ pool.size) : (cpL keep pool x).length = cntK keep x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    simp only [cpL, cntK_succ, List.length_append]
    rw [ih (by omega)]
    have : pool[x]? = some pool[x] := Array.getElem?_eq_getElem (by omega)
    split <;> simp [this]

theorem cpL_prefix {x y : Nat} (h : x ≤ y) : ∃ l, cpL keep pool y = cpL keep pool x ++ l := by
  induction y with
  | zero => have : x = 0 := by omega
            subst this; exact ⟨[], by simp⟩
  | succ y ih =>
    rcases Nat.lt_or_ge x (y + 1) with h' | h'
    · obtain ⟨l, hl⟩ := ih (by omega)
      exact ⟨l ++ _, by rw [cpL, hl, List.append_assoc]⟩
    · have : x = y + 1 := by omega
      subst this; exact ⟨[], by simp⟩

theorem cpL_get {x y : Nat} (hk : keep x = true) (hxy : x < y) (hy : y ≤ pool.size) :
    (cpL keep pool y)[cntK keep x]? = pool[x]?.map (Node.ren (cntK keep)) := by
  obtain ⟨l, hl⟩ := cpL_prefix (keep := keep) (pool := pool) (show x + 1 ≤ y by omega)
  have hx : pool[x]? = some pool[x] := Array.getElem?_eq_getElem (by omega)
  rw [hl, List.getElem?_append_left (by rw [cpL_length (by omega), cntK_succ, hk]; simp)]
  simp only [cpL, hk, ↓reduceIte, hx, Option.map_some, Option.toList_some]
  rw [List.getElem?_append_right (by rw [cpL_length (by omega)]; exact Nat.le_refl _),
    cpL_length (by omega)]
  simp

/-- Every entry of the kept list comes from a kept node. -/
theorem cpL_surj {y i : Nat} (hy : y ≤ pool.size) (hi : i < (cpL keep pool y).length) :
    ∃ x, x < y ∧ keep x = true ∧ cntK keep x = i := by
  induction y with
  | zero => simp [cpL] at hi
  | succ y ih =>
    rw [cpL_length hy, cntK_succ] at hi
    by_cases hlt : i < cntK keep y
    · obtain ⟨x, hx, hk, he⟩ := ih (by omega) (by rw [cpL_length (by omega)]; exact hlt)
      exact ⟨x, by omega, hk, he⟩
    · cases hk : keep y
      · simp [hk] at hi; omega
      · simp [hk] at hi
        exact ⟨y, by omega, hk, by omega⟩

theorem ctL_length {tys : Array Bcf.Ty} {x : Nat} (hx : x ≤ tys.size) :
    (ctL keep tys x).length = cntK keep x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    simp only [ctL, cntK_succ, List.length_append]
    rw [ih (by omega)]
    have : tys[x]? = some tys[x] := Array.getElem?_eq_getElem (by omega)
    split <;> simp [this]

theorem ctL_get {tys : Array Bcf.Ty} {x y : Nat} (hk : keep x = true) (hxy : x < y)
    (hy : y ≤ tys.size) : (ctL keep tys y)[cntK keep x]? = tys[x]? := by
  have hpre : ∀ y, x + 1 ≤ y → ∃ l, ctL keep tys y = ctL keep tys (x + 1) ++ l := by
    intro y h
    induction y with
    | zero => omega
    | succ y ih =>
      rcases Nat.lt_or_ge (x + 1) (y + 1) with h' | h'
      · obtain ⟨l, hl⟩ := ih (by omega)
        exact ⟨l ++ _, by rw [ctL, hl, List.append_assoc]⟩
      · have : x = y := by omega
        subst this; exact ⟨[], by simp⟩
  obtain ⟨l, hl⟩ := hpre y (by omega)
  have hx : tys[x]? = some tys[x] := Array.getElem?_eq_getElem (by omega)
  rw [hl, List.getElem?_append_left (by rw [ctL_length (by omega), cntK_succ, hk]; simp)]
  simp only [ctL, hk, ↓reduceIte, hx, Option.toList_some]
  rw [List.getElem?_append_right (by rw [ctL_length (by omega)]; exact Nat.le_refl _),
    ctL_length (by omega)]
  simp

/-! ## Offsets -/

theorem offK_succ (x : Nat) :
    offK keep pool (x + 1) = offK keep pool x + if keep x then (pool[x]?.map nodeSize).getD 0 else 0 :=
  rfl

theorem offK_mono {x y : Nat} (h : x ≤ y) : offK keep pool x ≤ offK keep pool y := by
  induction y with
  | zero => have : x = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ y ih =>
    rcases Nat.lt_or_ge x (y + 1) with h' | h'
    · have := ih (by omega); rw [offK_succ]; omega
    · have : x = y + 1 := by omega
      subst this; exact Nat.le_refl _

/-- The new offset of a kept node, plus its size, is at most the next one. -/
theorem offK_succ_keep {x : Nat} {n : Node} (hk : keep x = true) (hn : pool[x]? = some n) :
    offK keep pool (x + 1) = offK keep pool x + nodeSize n := by
  rw [offK_succ, hk, hn]; rfl

theorem offK_succ_drop {x : Nat} (hk : keep x = false) :
    offK keep pool (x + 1) = offK keep pool x := by
  rw [offK_succ, hk]; rfl

theorem offK_le_offs (x : Nat) : offK keep pool x ≤ offs pool x := by
  induction x with
  | zero => simp [offK]
  | succ x ih =>
    rw [offK_succ]
    rcases h : pool[x]? with _ | n
    · simp only [Option.map_none, Option.getD_none]
      have : offs pool x ≤ offs pool (x + 1) := offs_le_succ pool x
      split <;> omega
    · rw [offs_succ h]; simp only [Option.map_some, Option.getD_some]; split <;> omega

/-- Below a fully kept prefix the new offset is the old one. -/
theorem offK_pre {nL : Nat} (hpre : ∀ y, y < nL → keep y = true) (hnL : nL ≤ pool.size) :
    ∀ x, x ≤ nL → offK keep pool x = offs pool x
  | 0, _ => by simp [offK]
  | x + 1, hx => by
    have hn : pool[x]? = some pool[x] := Array.getElem?_eq_getElem (by omega)
    rw [offK_succ_keep (hpre x (by omega)) hn, offK_pre hpre hnL x (by omega), offs_succ hn]

theorem offK_lt {x y : Nat} (hk : keep x = true) (hxy : x < y) (hx : x < pool.size) :
    offK keep pool x < offK keep pool y := by
  have hn : pool[x]? = some pool[x] := Array.getElem?_eq_getElem hx
  have h1 := offK_succ_keep (keep := keep) hk hn
  have h2 := offK_mono (keep := keep) (pool := pool) (show x + 1 ≤ y by omega)
  have := nodeSize_pos pool[x]
  omega

/-- A kept node's words end at or before the next kept node's start. -/
theorem offK_add_le {x y : Nat} {n : Node} (hk : keep x = true) (hn : pool[x]? = some n)
    (hxy : x < y) : offK keep pool x + nodeSize n ≤ offK keep pool y := by
  rw [← offK_succ_keep hk hn]; exact offK_mono (by omega)

/-! ## The compacted pool -/

/-- The compacted pool. -/
def cpool (keep : Nat → Bool) (pool : Pool) : Pool := (cpL keep pool pool.size).toArray

theorem cpool_size : (cpool keep pool).size = cntK keep pool.size := by
  simp [cpool, cpL_length (Nat.le_refl _)]

theorem cpool_get {x : Nat} (hk : keep x = true) (hx : x < pool.size) :
    (cpool keep pool)[cntK keep x]? = pool[x]?.map (Node.ren (cntK keep)) := by
  simp only [cpool, List.getElem?_toArray]
  exact cpL_get hk hx (Nat.le_refl _)

theorem cpool_get' {x : Nat} {n : Node} (hk : keep x = true) (hn : pool[x]? = some n) :
    (cpool keep pool)[cntK keep x]? = some (n.ren (cntK keep)) := by
  rw [cpool_get hk (lt_size_of_getElem? hn), hn]; rfl

theorem cpool_surj {i : Nat} {m : Node} (h : (cpool keep pool)[i]? = some m) :
    ∃ x n, keep x = true ∧ pool[x]? = some n ∧ cntK keep x = i ∧ m = n.ren (cntK keep) := by
  have hi := lt_size_of_getElem? h
  rw [cpool_size, ← cpL_length (keep := keep) (Nat.le_refl _)] at hi
  obtain ⟨x, hx, hk, rfl⟩ := cpL_surj (Nat.le_refl _) hi
  have hn : pool[x]? = some pool[x] := Array.getElem?_eq_getElem hx
  rw [cpool_get' hk hn] at h
  exact ⟨x, pool[x], hk, hn, rfl, (Option.some.inj h).symm⟩

/-- The sum of the node sizes of the kept list. -/
theorem cpL_sizes {x : Nat} (hx : x ≤ pool.size) :
    ((cpL keep pool x).map nodeSize).sum = offK keep pool x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have hn : pool[x]? = some pool[x] := Array.getElem?_eq_getElem (by omega)
    simp only [cpL, List.map_append, List.sum_append, ih (by omega), offK_succ, hn]
    split <;> simp [nodeSize_ren]

/-- The offset of a node of the compacted pool. -/
theorem offs_cpool {x : Nat} (hx : x ≤ pool.size) :
    offs (cpool keep pool) (cntK keep x) = offK keep pool x := by
  unfold offs
  obtain ⟨l, hl⟩ := cpL_prefix (keep := keep) (pool := pool) hx
  simp only [cpool, List.toList_toArray, hl]
  rw [List.take_left' (cpL_length hx)]
  exact cpL_sizes hx

theorem offs_cpool_end : offs (cpool keep pool) (cpool keep pool).size = offK keep pool pool.size := by
  rw [cpool_size]; exact offs_cpool (Nat.le_refl _)

/-! ## Types -/

/-- The compacted memo of types. -/
def ctys (keep : Nat → Bool) (tys : Array Bcf.Ty) (n : Nat) : Array Bcf.Ty := (ctL keep tys n).toArray

/-- Types are preserved by compaction. -/
theorem typeOf_cpool (hcl : KClosed keep pool) (hlt : ∀ (i : Nat) (n : Node), pool[i]? = some n → ∀ a ∈ n.args, a < i) :
    ∀ x, keep x = true → x < pool.size → typeOf (cpool keep pool) (cntK keep x) = typeOf pool x := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hk hx
    have hn : pool[x]? = some pool[x] := Array.getElem?_eq_getElem hx
    rw [typeOf_unfold, typeOf_unfold, cpool_get' hk hn, hn]
    simp only [Node.ren_op, Node.ren_args, Array.toList_map]
    rw [mapOpt_map]
    have : mapOpt (fun a => if cntK keep a < cntK keep x then typeOf (cpool keep pool) (cntK keep a)
        else none) pool[x].args.toList =
        mapOpt (fun a => if a < x then typeOf pool a else none) pool[x].args.toList := by
      apply mapOpt_congr
      intro a ha
      have ha' : a ∈ pool[x].args := by simpa using ha
      have hax := hlt x _ hn a ha'
      have hka := hcl x _ hk hn a ha'
      rw [ite_eq_left (cntK_lt hka hax), ite_eq_left hax]
      exact ih a hax hka (by omega)
    rw [this]

/-! ## The index -/

/-- An index built by inserting every node of `pool` below `k`. -/
def mkIndex (pool : Pool) : Nat → Std.HashMap Node Nat
  | 0 => ∅
  | k + 1 =>
    match pool[k]? with
    | some n => (mkIndex pool k).insert n k
    | none => mkIndex pool k

theorem mkIndex_ok (pool : Pool) :
    ∀ k : Nat, (∀ (n : Node) (r : Nat), (mkIndex pool k)[n]? = some r → pool[r]? = some n) ∧
      (∀ (i : Nat) (n : Node), i < k → pool[i]? = some n → ∃ r, (mkIndex pool k)[n]? = some r)
  | 0 => ⟨fun n r h => by simp [mkIndex] at h, fun i n h => by omega⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := mkIndex_ok pool k
    simp only [mkIndex]
    cases hk : pool[k]? with
    | none =>
      refine ⟨h1, fun i n hi hn => h2 i n ?_ hn⟩
      rcases Nat.lt_or_ge i k with h | h
      · exact h
      · have : i = k := by omega
        subst this; rw [hk] at hn; cases hn
    | some m =>
      simp only []
      refine ⟨fun n r h => ?_, fun i n hi hn => ?_⟩
      · rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i he
          simp only [beq_iff_eq] at he
          subst he
          cases h; exact hk
        · exact h1 n r h
      · rw [Std.HashMap.getElem?_insert]
        split
        · exact ⟨k, rfl⟩
        · rcases Nat.lt_or_ge i k with h | h
          · exact h2 i n h hn
          · have : i = k := by omega
            subst this
            rename_i hne
            rw [hk] at hn; cases hn
            simp at hne

/-! ## The compacted state -/

/-- The compacted C-side state. -/
def cst (keep : Nat → Bool) (cs : St) : St where
  pool := cpool keep cs.pool
  tys := ctys keep cs.tys cs.pool.size
  index := mkIndex (cpool keep cs.pool) (cpool keep cs.pool).size
  facts := cs.facts

theorem cst_pool (cs : St) : (cst keep cs).pool = cpool keep cs.pool := rfl

theorem cst_tys_get {cs : St} (hok : PoolOK cs) {x : Nat} (hk : keep x = true) (hx : x < cs.pool.size) :
    (cst keep cs).tys[cntK keep x]? = cs.tys[x]? := by
  simp only [cst, ctys, List.getElem?_toArray]
  have hts := hok.tys_size
  rw [← hts] at hx ⊢
  exact ctL_get hk hx (Nat.le_refl _)

theorem cst_ok {cs : St} (hok : PoolOK cs) (hcl : KClosed keep cs.pool) : PoolOK (cst keep cs) where
  index := by
    intro i n hn
    obtain ⟨-, h2⟩ := mkIndex_ok (cpool keep cs.pool) (cpool keep cs.pool).size
    obtain ⟨r, hr⟩ := h2 i n (lt_size_of_getElem? hn) hn
    exact ⟨r, hr, (mkIndex_ok _ _).1 n r hr⟩
  nodup := by
    intro i j m hi hj
    obtain ⟨x, n, hkx, hnx, rfl, rfl⟩ := cpool_surj hi
    obtain ⟨y, n', hky, hny, rfl, he⟩ := cpool_surj hj
    have hargs : ∀ a ∈ n.args, ∀ b ∈ n'.args, cntK keep a = cntK keep b → a = b :=
      fun a ha b hb e => cntK_inj (hcl x n hkx hnx a ha) (hcl y n' hky hny b hb) e
    have := Node.ren_inj he hargs
    subst this
    rw [hok.nodup x y n hnx hny]
  tys := by
    have hts := hok.tys_size
    refine ⟨?_, ?_⟩
    · simp only [cst, ctys, cpool, List.size_toArray]
      rw [ctL_length (by omega), cpL_length (Nat.le_refl _)]
    · intro i m hm
      obtain ⟨x, n, hk, hn, rfl, rfl⟩ := cpool_surj hm
      have hx := lt_size_of_getElem? hn
      refine ⟨fun a ha => ?_, ?_⟩
      · simp only [Node.ren_args, Array.mem_map] at ha
        obtain ⟨a', ha', rfl⟩ := ha
        exact cntK_lt (hcl x n hk hn a' ha') (hok.args_lt hn a' ha')
      · show typeOf (cpool keep cs.pool) (cntK keep x) = _
        rw [typeOf_cpool hcl (fun i n hn => hok.args_lt hn) x hk hx, cst_tys_get hok hk hx]
        exact (hok.tys.2 x n hn).2

end

end Vbcf.Proof
