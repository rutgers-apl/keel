import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Interned

/-!
# Vbcf proofs: the C pool's view of the Lean pool

`ck_compact` keeps only the pool nodes a later step can still reach and
renumbers them, so after a compaction the C pool is no longer the image of
the Lean pool `st.pool` (which never forgets a node).  The relation is split in
two:

* `CoreInv posOf c cs` (`Spec.lean`, unchanged) says that the C pool, hash
  table and scratch stack represent a Lean state `cs`, the *C-side state*: a
  hash-consed pool laid out contiguously, node `x` at offset `offs cs.pool x`.
  All the proofs of the core functions (`ck_intern`, the builders, …) are about
  this relation.
* `VSt` pairs the Lean checker's state with a C-side state `cs` and a renaming:
  Lean index `i` is *live* (`lv i`) when its node is in the C pool, as node
  `σ i` of `cs`, with its children renamed by `σ`.  Live nodes have live
  children, `σ` is injective on them, and every node of `cs` is the image of a
  live node.  The C id of a live Lean index is `VSt.id i = offs cs.pool (σ i)`.

Before any compaction the view is the identity (`VSt.init`).  Interning a node
whose children are live (`VSt.push`) has three outcomes: the Lean checker finds
a live node (C finds its image), appends a new node (C appends it too), or
finds a *dead* node, i.e. one dropped by a compaction (C appends it again: the
node is resurrected with a new id).  So `σ` is injective but not monotone.
`VExt` is the relation between a view and its extension by builder calls: live
nodes stay live and keep their ids.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ## Renaming the children of a node -/

/-- `n` with each child `a` replaced by `σ a`. -/
def _root_.Bcf.Node.ren (σ : Nat → Nat) (n : Node) : Node := ⟨n.op, n.args.map σ⟩

@[simp] theorem _root_.Bcf.Node.ren_op (σ : Nat → Nat) (n : Node) : (n.ren σ).op = n.op := rfl
@[simp] theorem _root_.Bcf.Node.ren_args (σ : Nat → Nat) (n : Node) : (n.ren σ).args = n.args.map σ := rfl

theorem _root_.Bcf.Node.ren_id (n : Node) : n.ren id = n := by
  rcases n with ⟨op, args⟩; simp [Node.ren]

theorem _root_.Bcf.Node.ren_congr {σ τ : Nat → Nat} {n : Node} (h : ∀ a ∈ n.args, σ a = τ a) :
    n.ren σ = n.ren τ := by
  rcases n with ⟨op, args⟩
  simp only [Node.ren, Node.mk.injEq, true_and]
  rw [← Array.toList_inj, Array.toList_map, Array.toList_map]
  exact List.map_congr_left (fun a ha => h a (by simpa using ha))

theorem _root_.Bcf.Node.ren_ren (σ τ : Nat → Nat) (n : Node) : (n.ren σ).ren τ = n.ren (fun a => τ (σ a)) := by
  rcases n with ⟨op, args⟩
  simp only [Node.ren, Node.mk.injEq, true_and]
  rw [← Array.toList_inj, Array.toList_map, Array.toList_map, Array.toList_map, List.map_map]
  rfl

theorem list_map_inj_on {σ : Nat → Nat} :
    ∀ {l l' : List Nat}, l.map σ = l'.map σ → (∀ a ∈ l, ∀ b ∈ l', σ a = σ b → a = b) → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hi => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab : a = b := hi a (by simp) b (by simp) h.1
    subst hab
    rw [list_map_inj_on h.2 (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

/-- Renaming is injective on nodes whose children `σ` does not identify. -/
theorem _root_.Bcf.Node.ren_inj {σ : Nat → Nat} {n m : Node} (h : n.ren σ = m.ren σ)
    (hi : ∀ a ∈ n.args, ∀ b ∈ m.args, σ a = σ b → a = b) : n = m := by
  rcases n with ⟨op, args⟩
  rcases m with ⟨op', args'⟩
  simp only [Node.ren, Node.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  simp only [Node.mk.injEq, true_and]
  rw [← Array.toList_inj] at h2 ⊢
  rw [Array.toList_map, Array.toList_map] at h2
  exact list_map_inj_on h2 (fun a ha b hb => hi a (by simpa using ha) b (by simpa using hb))

theorem tailLen_ren (σ : Nat → Nat) (n : Node) : tailLen (n.ren σ) = tailLen n := by
  rcases n with ⟨op, args⟩
  cases op <;> simp [tailLen, Node.ren]

theorem hdrW_ren (σ : Nat → Nat) (n : Node) : hdrW (n.ren σ) = hdrW n := by
  simp only [hdrW, tailLen_ren, Node.ren_op]

theorem nodeSize_ren (σ : Nat → Nat) (n : Node) : nodeSize (n.ren σ) = nodeSize n := by
  simp only [nodeSize, tailLen_ren]

theorem tailW_ren (posOf off σ : Nat → Nat) (n : Node) :
    tailW posOf off (n.ren σ) = tailW posOf (fun a => off (σ a)) n := by
  rcases n with ⟨op, args⟩
  cases op <;> simp [tailW, Node.ren, List.map_map] <;> rfl

theorem fits_ren {posOf σ : Nat → Nat} {n : Node} : Fits posOf (n.ren σ) ↔ Fits posOf n := by
  unfold Fits
  rw [tailLen_ren, tailW_ren]
  rfl

theorem isLeaf_ren {σ : Nat → Nat} {n : Node} : IsLeaf (n.ren σ).op ↔ IsLeaf n.op := Iff.rfl

theorem mapOpt_map {α β γ : Type} (f : β → Option γ) (g : α → β) :
    ∀ l : List α, mapOpt f (l.map g) = mapOpt (fun a => f (g a)) l
  | [] => rfl
  | a :: l => by simp only [List.map_cons, mapOpt, mapOpt_map f g l]

/-! ## Pool extension (Lean side)

`PoolExt st st'`: `st'` is `st` with nodes appended.  The relation and its
basic lemmas are shared with `Interned.lean`. -/

theorem PoolExt.get' {st st' : St} (he : PoolExt st st') {i : Nat} {n : Node}
    (hn : st.pool[i]? = some n) : st'.pool[i]? = some n := by
  rw [he.node i (lt_size_of_getElem? hn), hn]

theorem pushNode_ext {st st' : St} {n : Node} {r : Nat} (hok : PoolOK st)
    (hp : pushNode st n = some (st', r)) : PoolExt st st' where
  size := (pushNode_size hp).1
  node := pushNode_prefix hp
  tys i hi := (pushNode_tys_prefix hok hp hi).1
  offs i hi := by
    rcases pushNode_pool hp with ⟨hpl, _⟩ | ⟨hpl, _⟩
    · rw [hpl]
    · rw [hpl, offs_push n hi]

/-! ## Views -/

/-- The Lean checker's state together with the C-side state `cs` that the C
pool represents, and the renaming `σ` of the live Lean indices `lv` into it. -/
structure VSt extends St where
  σ : Nat → Nat
  lv : Nat → Prop
  cs : St
  ok : PoolOK toSt
  lvLt : ∀ i, lv i → i < pool.size
  img : ∀ i n, lv i → pool[i]? = some n → cs.pool[σ i]? = some (n.ren σ)
  ty : ∀ i, lv i → cs.tys[σ i]? = tys[i]?
  closed : ∀ i n, lv i → pool[i]? = some n → ∀ a ∈ n.args, lv a
  inj : ∀ i j, lv i → lv j → σ i = σ j → i = j
  surj : ∀ x, x < cs.pool.size → ∃ i, lv i ∧ σ i = x

instance : Coe VSt St := ⟨VSt.toSt⟩

/-- The C id of Lean index `i`. -/
def VSt.id (S : VSt) (i : Nat) : Nat := offs S.cs.pool (S.σ i)

section vst
variable {S : VSt}

theorem VSt.lt {i : Nat} (hi : S.lv i) : i < S.pool.size := S.lvLt i hi

/-- The node at a live index. -/
theorem VSt.node_of_lv {i : Nat} (hi : S.lv i) : ∃ n, S.pool[i]? = some n :=
  ⟨S.pool[i]'(S.lt hi), by simp [S.lt hi]⟩

theorem VSt.σ_lt {i : Nat} (hi : S.lv i) : S.σ i < S.cs.pool.size := by
  obtain ⟨n, hn⟩ := S.node_of_lv hi
  exact lt_size_of_getElem? (S.img i n hi hn)

/-- Two live indices with the same id are equal. -/
theorem VSt.id_inj {i j : Nat} (hi : S.lv i) (hj : S.lv j) (e : S.id i = S.id j) : i = j :=
  S.inj i j hi hj (offs_inj (Nat.le_of_lt (S.σ_lt hi)) (Nat.le_of_lt (S.σ_lt hj)) e)

theorem VSt.args_lv {i : Nat} {n : Node} (hi : S.lv i) (hn : S.pool[i]? = some n) {a : Nat}
    (ha : a ∈ n.args) : S.lv a := S.closed i n hi hn a ha

/-- `σ` does not identify children of live nodes. -/
theorem VSt.ren_inj {n m : Node} (hn : ∀ a ∈ n.args, S.lv a) (hm : ∀ a ∈ m.args, S.lv a)
    (h : n.ren S.σ = m.ren S.σ) : n = m :=
  Node.ren_inj h (fun a ha b hb e => S.inj a b (hn a ha) (hm b hb) e)

/-- A node of the C-side state is the image of a unique live node. -/
theorem VSt.cs_node {x : Nat} {m : Node} (hx : S.cs.pool[x]? = some m) :
    ∃ i n, S.lv i ∧ S.σ i = x ∧ S.pool[i]? = some n ∧ m = n.ren S.σ := by
  obtain ⟨i, hi, rfl⟩ := S.surj x (lt_size_of_getElem? hx)
  obtain ⟨n, hn⟩ := S.node_of_lv hi
  have := S.img i n hi hn
  rw [hx] at this
  exact ⟨i, n, hi, rfl, hn, Option.some.inj this⟩

end vst

/-- The identity view of a Lean state: every node is live, at its own index. -/
def VSt.init (st : St) (hok : PoolOK st) : VSt where
  toSt := st
  σ := fun i => i
  lv := fun i => i < st.pool.size
  cs := st
  ok := hok
  lvLt := fun _ h => h
  img := fun i n _ hn => by rw [show (fun i : Nat => i) = _root_.id from rfl, Node.ren_id]; exact hn
  ty := fun _ _ => rfl
  closed := fun i n _ hn a ha => Nat.lt_trans ((hok.tys.2 i n hn).1 a ha) (lt_size_of_getElem? hn)
  inj := fun _ _ _ _ e => e
  surj := fun x hx => ⟨x, hx, rfl⟩

@[simp] theorem VSt.init_toSt (st : St) (hok : PoolOK st) : (VSt.init st hok).toSt = st := rfl
@[simp] theorem VSt.init_cs (st : St) (hok : PoolOK st) : (VSt.init st hok).cs = st := rfl
@[simp] theorem VSt.init_id (st : St) (hok : PoolOK st) (i : Nat) :
    (VSt.init st hok).id i = offs st.pool i := rfl
@[simp] theorem VSt.init_lv (st : St) (hok : PoolOK st) (i : Nat) :
    (VSt.init st hok).lv i ↔ i < st.pool.size := Iff.rfl

/-- Recording a fact leaves the pool, and so the view, unchanged. -/
def VSt.withFact (S : VSt) (f : Nat) : VSt :=
  { S with
    toSt := S.toSt.addFact f
    ok := addFact_ok S.ok
    lvLt := by rw [addFact_pool]; exact S.lvLt
    img := by rw [addFact_pool]; exact S.img
    ty := by rw [St.addFact_eq]; exact S.ty
    closed := by rw [addFact_pool]; exact S.closed }

@[simp] theorem VSt.withFact_toSt (S : VSt) (f : Nat) : (S.withFact f).toSt = S.toSt.addFact f := rfl
@[simp] theorem VSt.withFact_cs (S : VSt) (f : Nat) : (S.withFact f).cs = S.cs := rfl
@[simp] theorem VSt.withFact_lv (S : VSt) (f : Nat) (i : Nat) : (S.withFact f).lv i ↔ S.lv i := Iff.rfl
@[simp] theorem VSt.withFact_id (S : VSt) (f : Nat) (i : Nat) : (S.withFact f).id i = S.id i := rfl

/-! ## Extension of a view -/

/-- `S'` extends `S`: both pools only grew, live nodes stay live with the same
image (so the same id). -/
structure VExt (S S' : VSt) : Prop where
  lean : PoolExt S.toSt S'.toSt
  lv : ∀ i, S.lv i → S'.lv i
  σ : ∀ i, S.lv i → S'.σ i = S.σ i
  cs : PoolExt S.cs S'.cs

section vext
variable {S S' S'' : VSt}

theorem VExt.refl (S : VSt) : VExt S S :=
  ⟨PoolExt.refl _, fun _ h => h, fun _ _ => rfl, PoolExt.refl _⟩

theorem VExt.trans (h1 : VExt S S') (h2 : VExt S' S'') : VExt S S'' :=
  ⟨h1.lean.trans h2.lean, fun i hi => h2.lv i (h1.lv i hi),
    fun i hi => by rw [h2.σ i (h1.lv i hi), h1.σ i hi], h1.cs.trans h2.cs⟩

/-- A live node stays live. -/
theorem VExt.lt (he : VExt S S') {i : Nat} (hi : S.lv i) : S'.lv i := he.lv i hi

/-- The id of a live node does not change. -/
theorem VExt.id (he : VExt S S') {i : Nat} (hi : S.lv i) : S'.id i = S.id i := by
  unfold VSt.id
  rw [he.σ i hi, he.cs.offs _ (Nat.le_of_lt (S.σ_lt hi))]

/-- A node read before is still there. -/
theorem VExt.get (he : VExt S S') {i : Nat} {n : Node} (hn : S.pool[i]? = some n) :
    S'.pool[i]? = some n := he.lean.get' hn

theorem VExt.size (he : VExt S S') : S.pool.size ≤ S'.pool.size := he.lean.size

theorem VExt.node (he : VExt S S') {i : Nat} (hi : i < S.pool.size) :
    S'.pool[i]? = S.pool[i]? := he.lean.node i hi

theorem VExt.tys (he : VExt S S') {i : Nat} (hi : i < S.pool.size) :
    S'.tys[i]? = S.tys[i]? := he.lean.tys i hi

end vext

/-! ## Interning through a view -/

/-- The C side interns the renamed node; then the Lean side interns the node,
with the result related by an extension of the view.  Three cases: a live
node is found (nothing changes), a new node is appended on both sides, or the
Lean checker finds a dead node, which the C side appends again (resurrection). -/
theorem VSt.push (S : VSt) (hcok : PoolOK S.cs) {n : Node} (hargs : ∀ a ∈ n.args, S.lv a)
    {cs' : St} {x : Nat} (hp : pushNode S.cs (n.ren S.σ) = some (cs', x)) :
    ∃ (S' : VSt) (i : Nat), S'.cs = cs' ∧ pushNode S.toSt n = some (S'.toSt, i) ∧ S'.lv i ∧
      S'.σ i = x ∧ VExt S S' := by
  obtain ⟨argTys, t, hall, hmap, hrt, ⟨hcs, hx⟩ | ⟨hcs, hx, hnew⟩⟩ := pushNode_cases' hcok hp
  · -- found on the C side: it is the image of a live node, which the Lean side finds
    obtain ⟨j, m, hj, rfl, hm, hmn⟩ := S.cs_node hx
    have : m = n := S.ren_inj (fun a ha => S.closed j m hj hm a ha) hargs hmn.symm
    subst this
    refine ⟨S, j, hcs.symm, pushNode_found S.ok hm, hj, rfl, VExt.refl S⟩
  · -- appended on the C side
    subst hcs
    have hlt : ∀ a ∈ n.args, a < S.pool.size := fun a ha => S.lt (hargs a ha)
    have hmapL : mapOpt (fun a => S.tys[a]?) n.args.toList = some argTys := by
      rw [← hmap]
      simp only [Node.ren_args, Array.toList_map, mapOpt_map]
      apply mapOpt_congr
      intro a ha
      exact (S.ty a (hargs a (by simpa using ha))).symm
    have hsome : (pushNode S.toSt n).isSome := by
      rw [pushNode_isSome_iff]
      refine ⟨?_, argTys, t, hmapL, hrt⟩
      simp only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq]
      exact hlt
    obtain ⟨⟨st', i⟩, hpush⟩ := Option.isSome_iff_exists.mp hsome
    -- the Lean result is not live
    have hgi : st'.pool[i]? = some n := pushNode_get hpush
    have hnlv : ¬ S.lv i := by
      intro hi
      have hi' : i < S.pool.size := S.lt hi
      rw [pushNode_prefix hpush i hi'] at hgi
      exact hnew _ (S.img i n hi hgi)
    have hne : ∀ a ∈ n.args, a ≠ i := fun a ha e => hnlv (e ▸ hargs a ha)
    have hext := pushNode_ext S.ok hpush
    have hcext := pushNode_ext hcok hp
    have hcsz : (S.cs.append (n.ren S.σ) t).1.pool.size = S.cs.pool.size + 1 := by
      simp [St.append_eq]
    have hcget : (S.cs.append (n.ren S.σ) t).1.pool[S.cs.pool.size]? = some (n.ren S.σ) := by
      rw [← hx]; exact pushNode_get hp
    -- the types agree at the new entry
    obtain ⟨argTys1, t1, hm1, hr1, ht1⟩ := pushNode_ty' S.ok hpush
    obtain ⟨argTys2, t2, hm2, hr2, ht2⟩ := pushNode_ty' hcok hp
    have hmapC : mapOpt (fun a => S.cs.tys[a]?) (n.ren S.σ).args.toList = some argTys := hmap
    rw [hmapL] at hm1; cases hm1
    rw [hmapC] at hm2; cases hm2
    simp only [Node.ren_op] at hr2
    rw [hr1] at hr2; cases hr2
    -- the extended view
    let σ' : Nat → Nat := fun j => if j = i then S.cs.pool.size else S.σ j
    have hσ' : ∀ j, S.lv j → σ' j = S.σ j := fun j hj => by
      have : j ≠ i := fun e => hnlv (e ▸ hj)
      simp [σ', this]
    have hrenn : n.ren σ' = n.ren S.σ := Node.ren_congr (fun a ha => hσ' a (hargs a ha))
    have hold : ∀ j m, S.lv j → S.pool[j]? = some m → m.ren σ' = m.ren S.σ := fun j m hj hm =>
      Node.ren_congr (fun a ha => hσ' a (S.closed j m hj hm a ha))
    let S' : VSt :=
      { toSt := st'
        σ := σ'
        lv := fun j => S.lv j ∨ j = i
        cs := (S.cs.append (n.ren S.σ) t).1
        ok := pushNode_ok S.ok hpush
        lvLt := by
          intro j hj
          rcases hj with hj | rfl
          · exact Nat.lt_of_lt_of_le (S.lt hj) hext.size
          · exact (pushNode_size hpush).2
        img := by
          intro j m hj hm
          rcases hj with hj | rfl
          · rw [hext.node j (S.lt hj)] at hm
            rw [hσ' j hj, hcext.node _ (S.σ_lt hj), hold j m hj hm]
            exact S.img j m hj hm
          · rw [hgi] at hm; cases hm
            simp only [σ', ↓reduceIte]
            rw [hrenn]; exact hcget
        ty := by
          intro j hj
          rcases hj with hj | rfl
          · rw [hσ' j hj, hcext.tys _ (S.σ_lt hj), hext.tys j (S.lt hj)]
            exact S.ty j hj
          · simp only [σ', ↓reduceIte]
            rw [← hx, ht1]; exact ht2
        closed := by
          intro j m hj hm a ha
          rcases hj with hj | rfl
          · rw [hext.node j (S.lt hj)] at hm
            exact Or.inl (S.closed j m hj hm a ha)
          · rw [hgi] at hm; cases hm
            exact Or.inl (hargs a ha)
        inj := by
          intro j k hj hk e
          rcases hj with hj | rfl <;> rcases hk with hk | rfl
          · rw [hσ' j hj, hσ' k hk] at e; exact S.inj j k hj hk e
          · rw [hσ' j hj] at e; simp only [σ', ↓reduceIte] at e
            exact absurd e (Nat.ne_of_lt (S.σ_lt hj))
          · rw [hσ' k hk] at e; simp only [σ', ↓reduceIte] at e
            exact absurd e.symm (Nat.ne_of_lt (S.σ_lt hk))
          · rfl
        surj := by
          intro y hy
          rw [hcsz] at hy
          rcases Nat.lt_or_ge y S.cs.pool.size with hy' | hy'
          · obtain ⟨j, hj, rfl⟩ := S.surj y hy'
            exact ⟨j, Or.inl hj, hσ' j hj⟩
          · exact ⟨i, Or.inr rfl, by simp only [σ', ↓reduceIte]; omega⟩ }
    refine ⟨S', i, rfl, hpush, Or.inr rfl, by simp only [S', σ', ↓reduceIte]; exact hx.symm, ?_⟩
    exact ⟨hext, fun j hj => Or.inl hj, hσ', hcext⟩

/-- Finding a node through a view: a hit on the C side is a hit on the Lean
side, at a live index. -/
theorem VSt.find_some (S : VSt) (hcok : PoolOK S.cs) {n : Node} (hargs : ∀ a ∈ n.args, S.lv a)
    {x : Nat} (hf : findNode S.cs (n.ren S.σ) = some x) :
    ∃ j, S.lv j ∧ S.σ j = x ∧ S.pool[j]? = some n ∧ findNode S.toSt n = some j := by
  have hx := (findNode_eq_some_iff hcok).mp hf
  obtain ⟨j, m, hj, rfl, hm, hmn⟩ := S.cs_node hx
  have : m = n := S.ren_inj (fun a ha => S.closed j m hj hm a ha) hargs hmn.symm
  subst this
  exact ⟨j, hj, rfl, hm, (findNode_eq_some_iff S.ok).mpr hm⟩

/-- A miss on the C side: whatever the Lean side finds is dead. -/
theorem VSt.find_none (S : VSt) (hcok : PoolOK S.cs) {n : Node}
    (hf : findNode S.cs (n.ren S.σ) = none) {j : Nat} (hj : findNode S.toSt n = some j) :
    ¬ S.lv j := by
  intro hlv
  have hn := (findNode_eq_some_iff S.ok).mp hj
  exact (findNode_eq_none_iff hcok).mp hf _ (S.img j n hlv hn)

end Vbcf.Proof
