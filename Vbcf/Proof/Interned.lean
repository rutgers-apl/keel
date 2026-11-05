import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.EncLemmas

/-!
# Vbcf proofs: interning, described structurally

`Interned st n st' i` says what interning the node `n` does to the ghost pool,
without reference to any executable interning function:

* `n` is well-formed against `st`: its children are existing nodes and its
  operator type-checks against their memoised types (`Typed`);
* the returned index `i` holds exactly `n` in the new pool;
* either nothing changed (`st' = st`: the node was already present), or `n` was
  not present and has been appended at index `st.pool.size`, with its type
  recorded in the type memo and its position in the ghost hash index.

From this follow the facts every client needs (`Interned.ext`, `Interned.ok`,
`Interned.eval`, …): old nodes keep their position, type, C id and meaning, the
pool stays well-formed, and it grows by at most one node.

`PoolExt st st'` (`st'` is `st` with nodes appended) is the relation the rule
proofs carry across builder calls.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ## Pool extension -/

/-- `st'` is `st` with nodes appended: indices, nodes, types and ids of `st`
are kept. -/
structure PoolExt (st st' : St) : Prop where
  size : st.pool.size ≤ st'.pool.size
  node : ∀ i, i < st.pool.size → st'.pool[i]? = st.pool[i]?
  tys : ∀ i, i < st.pool.size → st'.tys[i]? = st.tys[i]?
  offs : ∀ i, i ≤ st.pool.size → offs st'.pool i = offs st.pool i

theorem PoolExt.refl (st : St) : PoolExt st st :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem PoolExt.trans {st st' st'' : St} (h1 : PoolExt st st') (h2 : PoolExt st' st'') :
    PoolExt st st'' where
  size := Nat.le_trans h1.size h2.size
  node i hi := by rw [h2.node i (Nat.lt_of_lt_of_le hi h1.size), h1.node i hi]
  tys i hi := by rw [h2.tys i (Nat.lt_of_lt_of_le hi h1.size), h1.tys i hi]
  offs i hi := by rw [h2.offs i (Nat.le_trans hi h1.size), h1.offs i hi]

theorem PoolExt.lt {st st' : St} (he : PoolExt st st') {i : Nat} (hi : i < st.pool.size) :
    i < st'.pool.size := Nat.lt_of_lt_of_le hi he.size

/-- A node read before the call is still there. -/
theorem PoolExt.get {st st' : St} (he : PoolExt st st') {i : Nat} {n : Node}
    (hn : st.pool[i]? = some n) : st'.pool[i]? = some n := by
  rw [he.node i (lt_size_of_getElem? hn), hn]

/-- The id of an old node does not change. -/
theorem PoolExt.id {st st' : St} (he : PoolExt st st') {i : Nat} (hi : i < st.pool.size) :
    Vbcf.Proof.offs st'.pool i = Vbcf.Proof.offs st.pool i := he.offs i (Nat.le_of_lt hi)

/-! ## Interning -/

/-- The ghost pool `st'` is `st` with the node `n` interned at index `i`. -/
structure Interned (st : St) (n : Node) (st' : St) (i : Nat) : Prop where
  /-- the node is well-formed: existing children, and its operator type-checks -/
  typed : Typed st n
  /-- the returned index holds the requested node -/
  get : st'.pool[i]? = some n
  /-- found (nothing changes), or new and appended with its type recorded -/
  shape : st' = st ∨
    (i = st.pool.size ∧ (∀ j : Nat, st.pool[j]? ≠ some n) ∧
      ∃ (argTys : List Ty) (t : Ty), mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧
        n.op.resultTy argTys = some t ∧
        st'.pool = st.pool.push n ∧ st'.tys = st.tys.push t ∧
        st'.index = st.index.insert n st.pool.size ∧ st'.facts = st.facts)

section
variable {st st' : St} {n : Node} {i : Nat}

theorem Interned.pool (h : Interned st n st' i) :
    (st'.pool = st.pool ∧ i < st.pool.size) ∨ (st'.pool = st.pool.push n ∧ i = st.pool.size) := by
  rcases h.shape with rfl | ⟨hi, _, _, _, _, _, hp, _⟩
  · exact Or.inl ⟨rfl, lt_size_of_getElem? h.get⟩
  · exact Or.inr ⟨hp, hi⟩

theorem Interned.lt (h : Interned st n st' i) : i < st'.pool.size := lt_size_of_getElem? h.get

theorem Interned.size_le (h : Interned st n st' i) : st.pool.size ≤ st'.pool.size := by
  rcases h.pool with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  · exact Nat.le_refl _
  · simp

theorem Interned.size_le_succ (h : Interned st n st' i) : st'.pool.size ≤ st.pool.size + 1 := by
  rcases h.pool with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  · omega
  · simp

theorem Interned.facts (h : Interned st n st' i) : st'.facts = st.facts := by
  rcases h.shape with rfl | ⟨_, _, _, _, _, _, _, _, _, hf⟩
  · rfl
  · exact hf

/-- Existing nodes keep their positions. -/
theorem Interned.prefix (h : Interned st n st' i) :
    ∀ j, j < st.pool.size → st'.pool[j]? = st.pool[j]? := by
  intro j hj
  rcases h.pool with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  rw [Array.getElem?_push]; simp [Nat.ne_of_lt hj]

/-- Existing types keep their positions (given a memo of the pool's size). -/
theorem Interned.tys_prefix (h : Interned st n st' i) (hsz : st.tys.size = st.pool.size) :
    ∀ j, j < st.pool.size → st'.tys[j]? = st.tys[j]? := by
  intro j hj
  rcases h.shape with rfl | ⟨_, _, _, _, _, _, _, ht, _⟩
  · rfl
  · rw [ht, Array.getElem?_push]; simp [hsz, Nat.ne_of_lt hj]

/-- Ids of existing nodes do not change. -/
theorem Interned.offs (h : Interned st n st' i) {j : Nat} (hj : j ≤ st.pool.size) :
    Vbcf.Proof.offs st'.pool j = Vbcf.Proof.offs st.pool j := by
  rcases h.pool with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  exact offs_push n hj

/-- Interning extends the pool. -/
theorem Interned.ext (h : Interned st n st' i) (hsz : st.tys.size = st.pool.size) : PoolExt st st' where
  size := h.size_le
  node := h.prefix
  tys := h.tys_prefix hsz
  offs _ hj := h.offs hj

/-- Evaluation of existing nodes is unchanged. -/
theorem Interned.eval (h : Interned st n st' i) (ρ : Assign) {j : Nat} (hj : j < st.pool.size) :
    Bcf.eval st'.pool ρ j = Bcf.eval st.pool ρ j :=
  eval_extend ρ h.prefix j hj

/-- The type memo stays correct. -/
theorem Interned.tysOK (h : Interned st n st' i) (hok : TysOK st.pool st.tys) :
    TysOK st'.pool st'.tys := by
  rcases h.shape with rfl | ⟨_, _, argTys, t, hmap, ht, hp, htys, _⟩
  · exact hok
  have hargs := h.typed.args_lt
  rw [hp, htys]
  have hpre : ∀ j, j < st.pool.size → (st.pool.push n)[j]? = st.pool[j]? := by
    intro j hj; rw [Array.getElem?_push]; simp [Nat.ne_of_lt hj]
  have hnew : typeOf (st.pool.push n) st.pool.size = some t := by
    rw [typeOf_unfold]
    simp only [Array.getElem?_push_size]
    have : mapOpt (fun a => if a < st.pool.size then typeOf (st.pool.push n) a else none)
        n.args.toList = some argTys := by
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
  intro j m hm
  rw [Array.getElem?_push] at hm
  split at hm
  · rename_i hj; subst hj; simp at hm; subst hm
    refine ⟨hargs, ?_⟩
    rw [hnew, Array.getElem?_push, hok.1]; simp
  · rename_i hj
    have hj' : j < st.pool.size := by
      rcases Nat.lt_or_ge j st.pool.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hm; cases hm
    obtain ⟨h1, h2⟩ := hok.2 j m hm
    refine ⟨h1, ?_⟩
    rw [typeOf_extend hpre j hj', h2, Array.getElem?_push]
    simp [hok.1, Nat.ne_of_lt hj']

/-- The ghost pool stays well-formed (memo, index, no duplicates). -/
theorem Interned.ok (h : Interned st n st' i) (hok : PoolOK st) : PoolOK st' := by
  have htys := h.tysOK hok.tys
  rcases h.shape with rfl | ⟨_, hnew, argTys, t, _, _, hp, _, hidx, _⟩
  · exact hok
  refine ⟨?_, ?_, htys⟩
  · intro j m hm
    rw [hp] at hm
    show ∃ r, st'.index[m]? = some r ∧ st'.pool[r]? = some m
    rw [hidx, hp]
    by_cases hmn : n = m
    · subst hmn
      exact ⟨st.pool.size, by simp, by simp⟩
    · have hm' : (st.pool.push n)[j]? = some m := hm
      rw [Array.getElem?_push] at hm'
      split at hm'
      · simp only [Option.some.injEq] at hm'; exact absurd hm' hmn
      · obtain ⟨r', hidx, hr'⟩ := hok.index j m hm'
        refine ⟨r', ?_, ?_⟩
        · rw [Std.HashMap.getElem?_insert]
          simp only [beq_iff_eq, hmn, ↓reduceIte]
          exact hidx
        · rw [Array.getElem?_push]
          simp only [Nat.ne_of_lt (lt_size_of_getElem? hr'), ↓reduceIte]
          exact hr'
  · intro j k m hj hk
    have hj' : (st.pool.push n)[j]? = some m := by rw [← hp]; exact hj
    have hk' : (st.pool.push n)[k]? = some m := by rw [← hp]; exact hk
    rw [Array.getElem?_push] at hj' hk'
    split at hj'
    · rename_i hj''
      simp only [Option.some.injEq] at hj'; subst hj'
      split at hk'
      · rename_i hk''; rw [hj'', hk'']
      · exact absurd hk' (hnew k)
    · split at hk'
      · simp only [Option.some.injEq] at hk'; subst hk'
        exact absurd hj' (hnew j)
      · exact hok.nodup j k m hj' hk'

/-- The type recorded for the returned node is the one its operator gives. -/
theorem Interned.ty (h : Interned st n st' i) (hok : PoolOK st) :
    ∃ argTys t, mapOpt (fun a => st.tys[a]?) n.args.toList = some argTys ∧
      n.op.resultTy argTys = some t ∧ st'.tys[i]? = some t := by
  rcases h.shape with rfl | ⟨hi, _, argTys, t, hmap, ht, _, htys, _⟩
  · obtain ⟨_, argTys', t', hmap', ht', hty⟩ := tysOK_retype hok.tys h.get
    exact ⟨argTys', t', hmap', ht', hty⟩
  · refine ⟨argTys, t, hmap, ht, ?_⟩
    rw [htys, hi, ← hok.tys.1]; simp

end

/-- **Found**: a node already in a well-formed pool is interned at its position,
and nothing changes. -/
theorem Interned.found {st : St} {n : Node} {r : Nat} (hok : PoolOK st)
    (hn : st.pool[r]? = some n) : Interned st n st r := by
  obtain ⟨hargs, argTys, t, hmap, ht, _⟩ := tysOK_retype hok.tys hn
  exact ⟨⟨hargs, argTys, t, hmap, ht⟩, hn, Or.inl rfl⟩

/-- **New**: a well-formed node not yet in the pool is appended. -/
theorem Interned.new {st : St} {n : Node} (hty : Typed st n) (hmiss : ∀ j : Nat, st.pool[j]? ≠ some n) :
    ∃ st', Interned st n st' st.pool.size ∧ st'.pool = st.pool.push n := by
  obtain ⟨hargs, argTys, t, hmap, ht⟩ := hty
  refine ⟨{ st with pool := st.pool.push n, tys := st.tys.push t,
                    index := st.index.insert n st.pool.size }, ⟨⟨hargs, argTys, t, hmap, ht⟩, ?_,
    Or.inr ⟨rfl, hmiss, argTys, t, hmap, ht, rfl, rfl, rfl, rfl⟩⟩, rfl⟩
  show (st.pool.push n)[st.pool.size]? = some n
  simp

/-! ## Function specifications -/

section
open EmbC

/-- The rule of consequence for function specifications. -/
theorem FnSpec.conseq {P : Prog} {f : String} {pre pre' : List EmbC.Val → (KernelState P State) → Prop}
    {post post' : List EmbC.Val → (KernelState P State) → Option EmbC.Val → (KernelState P State) → Prop}
    (h : FnSpec (State := State) P f pre post) (hpre : ∀ vs s, pre' vs s → pre vs s)
    (hpost : ∀ vs s rv s', pre' vs s → post vs s rv s' → post' vs s rv s') :
    FnSpec (State := State) P f pre' post' := by
  intro fuel vs st hp
  have := h fuel vs st (hpre vs st hp)
  cases hr : P.run fuel f vs st with
  | timeout => trivial
  | stuck => rw [hr] at this; exact this
  | ok a =>
    obtain ⟨rv, s'⟩ := a
    rw [hr] at this
    exact hpost _ _ _ _ hp this

end

end Vbcf.Proof
