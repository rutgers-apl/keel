import EmbC.Kernel
import Vbcf.Prog
import Bcf.Check

/-!
# Vbcf proofs: an index-free description of `pushNode` and `findNode`

The C checker has its own hash table, so the refinement proof needs a
description of interning that does not mention the Lean hash index:
`pushNode` returns the existing position if the node is already in the
pool and appends otherwise; `findNode` returns the position iff there
is one.

`Bcf`'s soundness proof never needs the index to be *complete* (a hit
is re-checked against the pool).  Here we do: `PoolOK` adds that the
index knows every pool node and that no node occurs twice.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-- The hash index knows every node of the pool. -/
def IndexOK (st : St) : Prop :=
  ∀ (i : Nat) (n : Node), st.pool[i]? = some n → ∃ r, st.index[n]? = some r ∧ st.pool[r]? = some n

/-- No node occurs twice in the pool. -/
def NoDup (pool : Pool) : Prop :=
  ∀ (i j : Nat) (n : Node), pool[i]? = some n → pool[j]? = some n → i = j

structure PoolOK (st : St) : Prop where
  index : IndexOK st
  nodup : NoDup st.pool
  tys : TysOK st.pool st.tys

/-! ## Small helpers -/

theorem lt_size_of_getElem? {α : Type} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) :
    i < a.size := by
  rcases Nat.lt_or_ge i a.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; cases h

/-- A node already in a `TysOK` pool type-checks again against the memo, with the
type the memo records for it. -/
theorem tysOK_retype {pool : Pool} {tys : Array Ty} (hok : TysOK pool tys) {r : Nat} {n : Node}
    (hn : pool[r]? = some n) :
    n.args.all (· < pool.size) = true ∧
    ∃ argTys t, mapOpt (fun a => tys[a]?) n.args.toList = some argTys ∧
      n.op.resultTy argTys = some t ∧ tys[r]? = some t := by
  obtain ⟨hargs, hty⟩ := hok.2 r n hn
  have hr : r < pool.size := lt_size_of_getElem? hn
  have hr' : r < tys.size := by rw [hok.1]; exact hr
  refine ⟨?_, ?_⟩
  · simp only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq]
    intro a ha
    exact Nat.lt_trans (hargs a ha) hr
  · rw [typeOf_unfold, hn] at hty
    simp only at hty
    have hm : mapOpt (fun a => if a < r then typeOf pool a else none) n.args.toList =
              mapOpt (fun a => tys[a]?) n.args.toList := by
      apply mapOpt_congr
      intro a ha
      have ha' : a < r := hargs a (by simpa using ha)
      simp only [ha', ↓reduceIte]
      have ha'' : a < pool.size := Nat.lt_trans ha' hr
      exact (hok.2 a pool[a] (Array.getElem?_eq_getElem ha'')).2
    rw [hm, Array.getElem?_eq_getElem hr'] at hty
    cases hmo : mapOpt (fun a => tys[a]?) n.args.toList with
    | none => rw [hmo] at hty; cases hty
    | some argTys =>
      rw [hmo] at hty
      exact ⟨argTys, tys[r], rfl, hty, Array.getElem?_eq_getElem hr'⟩

/-! ## The invariant holds initially and is preserved -/

theorem initSt_ok : PoolOK initSt where
  index := by intro i n hn; simp [initSt] at hn
  nodup := by intro i j n hn; simp [initSt] at hn
  tys := ⟨rfl, by intro i n hn; simp [initSt] at hn⟩

theorem addFact_pool (st : St) (f : Nat) : (st.addFact f).pool = st.pool := by
  rw [St.addFact_eq]

theorem addFact_ok {st : St} {f : Nat} (h : PoolOK st) : PoolOK (st.addFact f) := by
  rw [St.addFact_eq]
  exact ⟨h.index, h.nodup, h.tys⟩

/-! ## `pushNode` -/

/-- The node an accepted push returns. -/
theorem pushNode_at {st st' : St} {n : Node} {r : Nat} (hp : pushNode st n = some (st', r)) :
    st'.pool[r]? = some n :=
  pushNode_get hp

/-- Found case: a node already in the pool is returned at its position, state unchanged. -/
theorem pushNode_found {st : St} {n : Node} {r : Nat} (h : PoolOK st)
    (hn : st.pool[r]? = some n) : pushNode st n = some (st, r) := by
  obtain ⟨hargs, argTys, t, hmap, ht, _⟩ := tysOK_retype h.tys hn
  obtain ⟨r', hidx, hr'⟩ := h.index r n hn
  have hrr : r' = r := h.nodup r' r n hr' hn
  subst hrr
  unfold pushNode
  simp only [hargs, ↓reduceIte, hmap, ht, hidx, hr']

/-- New case: a node not in the pool is appended (if it type-checks). -/
theorem pushNode_new {st st' : St} {n : Node} {r : Nat} (_h : PoolOK st)
    (hn : ∀ i : Nat, st.pool[i]? ≠ some n) (hp : pushNode st n = some (st', r)) :
    r = st.pool.size ∧ st'.pool = st.pool.push n ∧ st'.facts = st.facts := by
  refine ⟨?_, ?_, pushNode_facts hp⟩
  · rcases pushNode_pool hp with ⟨hpool, _⟩ | ⟨_, hr⟩
    · exact absurd (hpool ▸ pushNode_get hp) (hn r)
    · exact hr
  · rcases pushNode_pool hp with ⟨hpool, _⟩ | ⟨hpool, _⟩
    · exact absurd (hpool ▸ pushNode_get hp) (hn r)
    · exact hpool

/-- `pushNode_cases` without the index: under `PoolOK`, the append branch is taken
exactly when the node is not in the pool. -/
theorem pushNode_cases' {st st' : St} {n : Node} {r : Nat} (h : PoolOK st)
    (hp : pushNode st n = some (st', r)) :
    ∃ argTys t, n.args.all (· < st.pool.size) = true ∧
      mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧ n.op.resultTy argTys = some t ∧
      ((st' = st ∧ st.pool[r]? = some n) ∨
       (st' = (st.append n t).1 ∧ r = st.pool.size ∧ ∀ i : Nat, st.pool[i]? ≠ some n)) := by
  obtain ⟨argTys, t, hargs, hmap, ht, hc | ⟨hst, hr⟩⟩ := pushNode_cases hp
  · exact ⟨argTys, t, hargs, hmap, ht, Or.inl hc⟩
  · refine ⟨argTys, t, hargs, hmap, ht, Or.inr ⟨hst, hr, ?_⟩⟩
    intro i hi
    have hf := pushNode_found h hi
    rw [hp] at hf
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    have hsz : st'.pool.size = st.pool.size + 1 := by rw [hst, St.append_eq]; simp
    rw [hf.1] at hsz
    omega

theorem pushNode_ok {st st' : St} {n : Node} {r : Nat} (h : PoolOK st)
    (hp : pushNode st n = some (st', r)) : PoolOK st' := by
  obtain ⟨argTys, t, _, _, _, ⟨hst, _⟩ | ⟨hst, _, hnew⟩⟩ := pushNode_cases' h hp
  · rw [hst]; exact h
  · refine ⟨?_, ?_, pushNode_tysOK hp h.tys⟩
    · rw [hst]
      simp only [St.append_eq]
      intro i m hm
      by_cases hmn : n = m
      · subst hmn
        exact ⟨st.pool.size, by simp, by simp⟩
      · rw [Array.getElem?_push] at hm
        split at hm
        · simp only [Option.some.injEq] at hm; exact absurd hm hmn
        · obtain ⟨r', hidx, hr'⟩ := h.index i m hm
          refine ⟨r', ?_, ?_⟩
          · rw [Std.HashMap.getElem?_insert]
            simp only [beq_iff_eq, hmn, ↓reduceIte]
            exact hidx
          · rw [Array.getElem?_push]
            simp only [Nat.ne_of_lt (lt_size_of_getElem? hr'), ↓reduceIte]
            exact hr'
    · rw [hst]
      simp only [St.append_eq]
      intro i j m hi hj
      rw [Array.getElem?_push] at hi hj
      split at hi
      · rename_i hi'
        simp only [Option.some.injEq] at hi; subst hi
        split at hj
        · rename_i hj'; rw [hi', hj']
        · exact absurd hj (hnew j)
      · split at hj
        · simp only [Option.some.injEq] at hj; subst hj
          exact absurd hi (hnew i)
        · exact h.nodup i j m hi hj

/-- Success criterion: `pushNode` succeeds iff the node type-checks against the memo. -/
theorem pushNode_isSome_iff {st : St} {n : Node} :
    (pushNode st n).isSome ↔
      (n.args.all (· < st.pool.size) = true ∧
       ∃ argTys t, mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧
         n.op.resultTy argTys = some t) := by
  constructor
  · intro hs
    rcases hp : pushNode st n with _ | ⟨st', r⟩
    · rw [hp] at hs; cases hs
    · obtain ⟨argTys, t, hargs, hmap, ht, _⟩ := pushNode_cases hp
      exact ⟨hargs, argTys, t, hmap, ht⟩
  · rintro ⟨hargs, argTys, t, hmap, ht⟩
    unfold pushNode
    simp only [hargs, ↓reduceIte, hmap, ht]
    split
    · split <;> rfl
    · rfl

/-- The type recorded for a pushed node. -/
theorem pushNode_ty' {st st' : St} {n : Node} {r : Nat} (h : PoolOK st)
    (hp : pushNode st n = some (st', r)) :
    ∃ argTys t, mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧
      n.op.resultTy argTys = some t ∧ st'.tys[r]? = some t := by
  obtain ⟨argTys, t, _, hmap, ht, ⟨hst, hr⟩ | ⟨hst, hr, _⟩⟩ := pushNode_cases' h hp
  · obtain ⟨_, argTys', t', hmap', ht', hty⟩ := tysOK_retype h.tys hr
    rw [hst]
    exact ⟨argTys', t', hmap', ht', hty⟩
  · refine ⟨argTys, t, hmap, ht, ?_⟩
    rw [hst, hr]
    simp only [St.append_eq]
    rw [← h.tys.1]
    simp

/-- Existing entries of the pool and of the type memo keep their positions.  Only the sizes
of the two arrays need to agree for this (see `pushNode_tys_prefix` for the `PoolOK` form). -/
theorem pushNode_tys_prefix_of_size {st st' : St} {n : Node} {r : Nat}
    (hsz : st.tys.size = st.pool.size) (hp : pushNode st n = some (st', r))
    {i : Nat} (hi : i < st.pool.size) :
    st'.tys[i]? = st.tys[i]? ∧ st'.pool[i]? = st.pool[i]? := by
  refine ⟨?_, pushNode_prefix hp i hi⟩
  obtain ⟨_, t, _, _, _, ⟨hst, _⟩ | ⟨hst, _⟩⟩ := pushNode_cases hp
  · rw [hst]
  · rw [hst]
    simp only [St.append_eq]
    rw [Array.getElem?_push]
    simp only [hsz, Nat.ne_of_lt hi, ↓reduceIte]

/-- Monotonicity: existing entries of the pool and of the type memo keep their positions. -/
theorem pushNode_tys_prefix {st st' : St} {n : Node} {r : Nat} (h : PoolOK st)
    (hp : pushNode st n = some (st', r)) {i : Nat} (hi : i < st.pool.size) :
    st'.tys[i]? = st.tys[i]? ∧ st'.pool[i]? = st.pool[i]? :=
  pushNode_tys_prefix_of_size h.tys.1 hp hi

/-! ## `findNode` -/

theorem findNode_eq_some_iff {st : St} {n : Node} {r : Nat} (h : PoolOK st) :
    findNode st n = some r ↔ st.pool[r]? = some n := by
  constructor
  · intro hf
    unfold findNode at hf
    split at hf
    · split at hf
      · rename_i hr
        simp only [Option.some.injEq] at hf; subst hf; exact hr
      · cases hf
    · cases hf
  · intro hn
    obtain ⟨r', hidx, hr'⟩ := h.index r n hn
    have hrr : r' = r := h.nodup r' r n hr' hn
    subst hrr
    unfold findNode
    simp only [hidx, hr', ↓reduceIte]

theorem findNode_eq_none_iff {st : St} {n : Node} (h : PoolOK st) :
    findNode st n = none ↔ ∀ r : Nat, st.pool[r]? ≠ some n := by
  constructor
  · intro hf r hr
    rw [(findNode_eq_some_iff h).mpr hr] at hf
    cases hf
  · intro hn
    rcases hf : findNode st n with _ | r
    · rfl
    · exact absurd ((findNode_eq_some_iff h).mp hf) (hn r)

end Vbcf.Proof
