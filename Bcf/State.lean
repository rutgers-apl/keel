import Bcf.Typing
import Std.Data.HashMap

/-!
# Checker state and the node-building primitive

`St` holds the expression pool, a memo of every node's type, a hash
index for hash-consing, and the fact derived by each step so far.
`pushNode` is the *only* way nodes enter the pool: it type-checks the
node, then either returns an existing structurally identical node or
appends it.  Because every node is interned, structural equality of
expressions is index equality, which is what the rules compare.

Soundness never relies on the hash index being right: a hit is
accepted only after checking the stored node is literally the one
requested.
-/

namespace Bcf

structure St where
  pool     : Pool
  tys      : Array Ty
  index    : Std.HashMap Node Nat
  facts    : Array Nat
  deriving Inhabited

/-- Memoised types agree with `typeOf`, and every node is well-formed. -/
def TysOK (pool : Pool) (tys : Array Ty) : Prop :=
  tys.size = pool.size ∧
  ∀ i n, pool[i]? = some n → (∀ a ∈ n.args, a < i) ∧ typeOf pool i = tys[i]?

theorem TysOK.wf {pool : Pool} {tys : Array Ty} (h : TysOK pool tys) : WF pool := by
  intro i n hn
  obtain ⟨h1, h2⟩ := h.2 i n hn
  refine ⟨h1, ?_⟩
  rw [h2]
  have hi : i < pool.size := by
    rcases Nat.lt_or_ge i pool.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hn; cases hn
  have hi' : i < tys.size := by rw [h.1]; exact hi
  simp [Array.getElem?_eq_getElem hi']

/-- Append a node, recording its type.  The state is destructured so that the arrays are
updated in place rather than copied. -/
def St.append (st : St) (n : Node) (t : Ty) : St × Nat :=
  match st with
  | ⟨pool, tys, index, facts⟩ =>
    let sz := pool.size
    (⟨pool.push n, tys.push t, index.insert n sz, facts⟩, sz)

theorem St.append_eq (st : St) (n : Node) (t : Ty) :
    st.append n t = ({ st with pool := st.pool.push n, tys := st.tys.push t,
                               index := st.index.insert n st.pool.size }, st.pool.size) := by
  cases st; rfl

/-- Record a derived fact (in place). -/
def St.addFact (st : St) (f : Nat) : St :=
  match st with
  | ⟨pool, tys, index, facts⟩ => ⟨pool, tys, index, facts.push f⟩

theorem St.addFact_eq (st : St) (f : Nat) : st.addFact f = { st with facts := st.facts.push f } := by
  cases st; rfl

/-- Type-check a node against the current pool and intern it. -/
def pushNode (st : St) (n : Node) : Option (St × Nat) :=
  if n.args.all (· < st.pool.size) then
    match mapOpt (fun a => st.tys[a]?) n.args.toList with
    | none => none
    | some argTys =>
      match n.op.resultTy argTys with
      | none => none
      | some t =>
        match st.index[n]? with
        | some r => if st.pool[r]? = some n then some (st, r) else some (st.append n t)
        | none => some (st.append n t)
  else none

/-! ## Properties of `pushNode` -/

/-- What `pushNode` did: either it found the node, or it appended it. -/
theorem pushNode_cases {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r)) :
    ∃ argTys t, n.args.all (· < st.pool.size) = true ∧
      mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧ n.op.resultTy argTys = some t ∧
      ((st' = st ∧ st.pool[r]? = some n) ∨ (st' = (st.append n t).1 ∧ r = st.pool.size)) := by
  unfold pushNode at h
  split at h
  · rename_i hargs
    split at h
    · simp at h
    · rename_i argTys hmap
      split at h
      · simp at h
      · rename_i t ht
        split at h
        · rename_i r' hidx
          split at h
          · rename_i hr
            simp at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨argTys, t, hargs, hmap, ht, Or.inl ⟨rfl, hr⟩⟩
          · simp only [Option.some.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨argTys, t, hargs, hmap, ht, Or.inr ⟨rfl, rfl⟩⟩
        · simp only [Option.some.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨argTys, t, hargs, hmap, ht, Or.inr ⟨rfl, rfl⟩⟩
  · simp at h

/-- The pool only grows, by at most the pushed node. -/
theorem pushNode_pool {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r)) :
    (st'.pool = st.pool ∧ r < st.pool.size) ∨ (st'.pool = st.pool.push n ∧ r = st.pool.size) := by
  obtain ⟨_, t, _, _, _, hc | hc⟩ := pushNode_cases h
  · obtain ⟨hst, hr⟩ := hc
    left; rw [hst]; refine ⟨rfl, ?_⟩
    rcases Nat.lt_or_ge r st.pool.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hr; cases hr
  · obtain ⟨hst, hr⟩ := hc
    right; rw [hst, hr]; exact ⟨rfl, rfl⟩

theorem pushNode_facts {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r)) :
    st'.facts = st.facts := by
  obtain ⟨_, t, _, _, _, hc | hc⟩ := pushNode_cases h
  · obtain ⟨hst, _⟩ := hc; rw [hst]
  · obtain ⟨hst, _⟩ := hc; rw [hst]; rfl

/-- The returned index holds exactly the requested node. -/
theorem pushNode_get {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r)) :
    st'.pool[r]? = some n := by
  obtain ⟨_, t, _, _, _, hc | hc⟩ := pushNode_cases h
  · obtain ⟨hst, hr⟩ := hc; rw [hst]; exact hr
  · obtain ⟨hst, hr⟩ := hc; rw [hst, hr]; simp [St.append_eq]

/-- Existing nodes keep their positions. -/
theorem pushNode_prefix {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r)) :
    ∀ j, j < st.pool.size → st'.pool[j]? = st.pool[j]? := by
  intro j hj
  rcases pushNode_pool h with ⟨hp, _⟩ | ⟨hp, _⟩
  · rw [hp]
  · rw [hp, Array.getElem?_push]; simp [Nat.ne_of_lt hj]

theorem pushNode_size {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r)) :
    st.pool.size ≤ st'.pool.size ∧ r < st'.pool.size := by
  rcases pushNode_pool h with ⟨hp, hr⟩ | ⟨hp, hr⟩
  · rw [hp]; exact ⟨Nat.le_refl _, hr⟩
  · rw [hp, hr]; simp

/-- Evaluation of existing nodes is unchanged. -/
theorem pushNode_eval {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r))
    (ρ : Assign) {i : Nat} (hi : i < st.pool.size) : eval st'.pool ρ i = eval st.pool ρ i :=
  eval_extend ρ (pushNode_prefix h) i hi

theorem pushNode_holds {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r))
    (ρ : Assign) {i : Nat} (hi : i < st.pool.size) : holds st'.pool ρ i ↔ holds st.pool ρ i := by
  unfold holds; rw [pushNode_eval h ρ hi]

/-- The type memo stays correct. -/
theorem pushNode_tysOK {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r))
    (hok : TysOK st.pool st.tys) : TysOK st'.pool st'.tys := by
  obtain ⟨argTys, t, hargs, hmap, ht, hc | hc⟩ := pushNode_cases h
  · obtain ⟨hst, _⟩ := hc; rw [hst]; exact hok
  · obtain ⟨hst, _⟩ := hc
    rw [hst]
    simp only [St.append_eq]
    have hpre : ∀ j, j < st.pool.size → (st.pool.push n)[j]? = st.pool[j]? := by
      intro j hj; rw [Array.getElem?_push]; simp [Nat.ne_of_lt hj]
    simp only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] at hargs
    -- the new node type-checks in the extended pool
    have hnew : typeOf (st.pool.push n) st.pool.size = some t := by
      rw [typeOf_unfold]
      simp only [Array.getElem?_push_size]
      have : mapOpt (fun a => if a < st.pool.size then typeOf (st.pool.push n) a else none) n.args.toList
             = some argTys := by
        rw [← hmap]
        apply mapOpt_congr
        intro a ha
        have ha' : a < st.pool.size := hargs a (by simpa using ha)
        simp only [ha', ite_true]
        rw [typeOf_extend hpre a ha']
        rcases hn : st.pool[a]? with _ | m
        · rw [Array.getElem?_eq_none_iff] at hn; omega
        · exact (hok.2 a m hn).2
      rw [this]; exact ht
    refine ⟨by simp [hok.1], ?_⟩
    intro i m hm
    rw [Array.getElem?_push] at hm
    split at hm
    · rename_i hi; subst hi; simp at hm; subst hm
      refine ⟨hargs, ?_⟩
      rw [hnew, Array.getElem?_push, hok.1]; simp
    · rename_i hi
      have hi' : i < st.pool.size := by
        rcases Nat.lt_or_ge i st.pool.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at hm; cases hm
      obtain ⟨h1, h2⟩ := hok.2 i m hm
      refine ⟨h1, ?_⟩
      rw [typeOf_extend hpre i hi', h2, Array.getElem?_push]
      simp [hok.1, Nat.ne_of_lt hi']

/-- The type recorded for the returned node. -/
theorem pushNode_ty {st st' : St} {n : Node} {r : Nat} (h : pushNode st n = some (st', r))
    (hok : TysOK st.pool st.tys) :
    typeOf st'.pool r = (mapOpt (fun a => typeOf st'.pool a) n.args.toList).bind n.op.resultTy := by
  have hok' := pushNode_tysOK h hok
  have hg := pushNode_get h
  rw [typeOf_unfold, hg]
  simp only
  have : mapOpt (fun a => if a < r then typeOf st'.pool a else none) n.args.toList =
         mapOpt (fun a => typeOf st'.pool a) n.args.toList := by
    apply mapOpt_congr
    intro a ha
    have := (hok'.2 r n hg).1 a (by simpa using ha)
    simp [this]
  rw [this]
  cases mapOpt (fun a => typeOf st'.pool a) n.args.toList <;> rfl

end Bcf
