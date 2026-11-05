import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly1
import Vbcf.Proof.View

/-!
# Vbcf proofs: linear forms through a view

The C computes the linear form of a node of its C-side state `cs` (`lin_f`), whose atoms
are ordered by C id; the Lean checker computes it on its own pool, ordered by index.  After
a compaction the two orders differ (`σ` is not monotone), so the two forms are not the
renaming of one another term by term.  They denote the same polynomial, though:

* `lin_eval_ren`: evaluating the C-side form of `σ x` under `lv` is evaluating the Lean form of
  `x` under `lv ∘ σ` (by induction over the node, with `Bcf.Lin.eval_*`);
* `lin_canon`: a Lean form has strictly increasing atoms and nonzero coefficients, and two such
  forms that agree under every valuation are equal (`canon_eq`);
* `lin_atoms`: the atoms of the Lean form of a live node are live;

which together give `lin_ren`: if the C-side forms of `σ a` and `σ b` are equal, so are the
Lean forms of `a` and `b`, which is what `r_poly_norm` needs.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf


/-! ## Atoms with a property -/

section atoms
variable {w : Nat}

/-- Every atom satisfies `P`. -/
def LinP (P : Nat → Prop) (ts : List (Nat × BitVec w)) : Prop := ∀ t ∈ ts, P t.1

theorem LinP.cons {P : Nat → Prop} {t : Nat × BitVec w} {ts : List (Nat × BitVec w)} (ht : P t.1)
    (hts : LinP P ts) : LinP P (t :: ts) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ht
  · exact hts x hx

theorem LinP.tail {P : Nat → Prop} {t : Nat × BitVec w} {ts : List (Nat × BitVec w)}
    (h : LinP P (t :: ts)) : LinP P ts := fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem LinP.head {P : Nat → Prop} {t : Nat × BitVec w} {ts : List (Nat × BitVec w)}
    (h : LinP P (t :: ts)) : P t.1 := h t (List.mem_cons_self ..)

theorem linP_merge {P : Nat → Prop} :
    ∀ (n : Nat) (xs ys : List (Nat × BitVec w)), xs.length + ys.length = n →
      LinP P xs → LinP P ys → LinP P (Lin.mergeTerms xs ys) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs ys hn hx hy
    match xs, ys with
    | [], ys => rw [pl_merge_nil_left]; exact hy
    | x :: xs, [] => rw [pl_merge_nil_right]; exact hx
    | (a, c) :: xs, (b, d) :: ys =>
      rcases Nat.lt_trichotomy a b with h | rfl | h
      · rw [pl_merge_lt h]
        exact LinP.cons hx.head (ih _ (by simp at hn ⊢; omega) _ _ rfl hx.tail hy)
      · rw [pl_merge_eq]
        split
        · exact ih _ (by simp at hn ⊢; omega) _ _ rfl hx.tail hy.tail
        · exact LinP.cons hx.head (ih _ (by simp at hn ⊢; omega) _ _ rfl hx.tail hy.tail)
      · rw [pl_merge_gt h]
        exact LinP.cons hy.head (ih _ (by simp at hn ⊢; omega) _ _ rfl hx hy.tail)

theorem LinP.add {P : Nat → Prop} {p q : Lin w} (hp : LinP P p.terms) (hq : LinP P q.terms) :
    LinP P (Lin.add p q).terms := linP_merge _ _ _ rfl hp hq

theorem LinP.scale {P : Nat → Prop} {k : BitVec w} {p : Lin w} (hp : LinP P p.terms) :
    LinP P (Lin.scale k p).terms := by
  intro x hx
  obtain ⟨hx, -⟩ := List.mem_filter.mp hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact hp t ht

theorem LinP.foldr {P : Nat → Prop} {ps : List (Lin w)} (h : ∀ p ∈ ps, LinP P p.terms) :
    LinP P (ps.foldr Lin.add (Lin.ofConst 0)).terms := by
  induction ps with
  | nil => intro x hx; simp [Lin.ofConst] at hx
  | cons p ps ih =>
    simp only [List.foldr_cons]
    exact LinP.add (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem LinP.atom {P : Nat → Prop} {a : Nat} (ha : P a) : LinP P (Lin.atom (w := w) a).terms :=
  LinP.cons ha (fun _ h => by simp at h)

theorem LinP.const {P : Nat → Prop} (x : BitVec w) : LinP P (Lin.ofConst x).terms :=
  fun _ h => by simp [Lin.ofConst] at h

end atoms

/-! ## Canonical forms -/

section canon
variable {w : Nat}

/-- Strictly increasing atoms, nonzero coefficients. -/
def Canon (ts : List (Nat × BitVec w)) : Prop :=
  ts.Pairwise (fun s t => s.1 < t.1) ∧ ∀ t ∈ ts, t.2 ≠ 0

theorem canon_merge :
    ∀ (n : Nat) (xs ys : List (Nat × BitVec w)), xs.length + ys.length = n →
      Canon xs → Canon ys →
        Canon (Lin.mergeTerms xs ys) ∧
          ∀ t ∈ Lin.mergeTerms xs ys, (∃ s ∈ xs, s.1 = t.1) ∨ (∃ s ∈ ys, s.1 = t.1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs ys hn hx hy
    match xs, ys with
    | [], ys =>
      rw [pl_merge_nil_left]
      exact ⟨hy, fun t ht => Or.inr ⟨t, ht, rfl⟩⟩
    | x :: xs, [] =>
      rw [pl_merge_nil_right]
      exact ⟨hx, fun t ht => Or.inl ⟨t, ht, rfl⟩⟩
    | (a, c) :: xs, (b, d) :: ys =>
      have hx1 := List.pairwise_cons.mp hx.1
      have hy1 := List.pairwise_cons.mp hy.1
      have hxt : Canon xs := ⟨hx1.2, fun t ht => hx.2 t (List.mem_cons_of_mem _ ht)⟩
      have hyt : Canon ys := ⟨hy1.2, fun t ht => hy.2 t (List.mem_cons_of_mem _ ht)⟩
      rcases Nat.lt_trichotomy a b with h | rfl | h
      · rw [pl_merge_lt h]
        obtain ⟨hc, hm⟩ := ih _ (by simp at hn ⊢; omega) xs ((b, d) :: ys) rfl hxt hy
        refine ⟨⟨List.pairwise_cons.mpr ⟨fun t ht => ?_, hc.1⟩, ?_⟩, ?_⟩
        · rcases hm t ht with ⟨s, hs, e⟩ | ⟨s, hs, e⟩
          · rw [← e]; exact hx1.1 s hs
          · rw [← e]
            rcases List.mem_cons.mp hs with rfl | hs
            · exact h
            · exact Nat.lt_trans h (hy1.1 s hs)
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hx.2 _ (List.mem_cons_self ..)
          · exact hc.2 t ht
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact Or.inl ⟨_, List.mem_cons_self .., rfl⟩
          · rcases hm t ht with ⟨s, hs, e⟩ | e
            · exact Or.inl ⟨s, List.mem_cons_of_mem _ hs, e⟩
            · exact Or.inr e
      · rw [pl_merge_eq]
        obtain ⟨hc, hm⟩ := ih _ (by simp at hn ⊢; omega) xs ys rfl hxt hyt
        have hm' : ∀ t ∈ Lin.mergeTerms xs ys, (∃ s ∈ (a, c) :: xs, s.1 = t.1) ∨
            (∃ s ∈ (a, d) :: ys, s.1 = t.1) := by
          intro t ht
          rcases hm t ht with ⟨s, hs, e⟩ | ⟨s, hs, e⟩
          · exact Or.inl ⟨s, List.mem_cons_of_mem _ hs, e⟩
          · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, e⟩
        split
        · exact ⟨hc, hm'⟩
        · rename_i h0
          refine ⟨⟨List.pairwise_cons.mpr ⟨fun t ht => ?_, hc.1⟩, ?_⟩, ?_⟩
          · rcases hm t ht with ⟨s, hs, e⟩ | ⟨s, hs, e⟩
            · rw [← e]; exact hx1.1 s hs
            · rw [← e]; exact hy1.1 s hs
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact h0
            · exact hc.2 t ht
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact Or.inl ⟨_, List.mem_cons_self .., rfl⟩
            · exact hm' t ht
      · rw [pl_merge_gt h]
        obtain ⟨hc, hm⟩ := ih _ (by simp at hn ⊢; omega) ((a, c) :: xs) ys rfl hx hyt
        refine ⟨⟨List.pairwise_cons.mpr ⟨fun t ht => ?_, hc.1⟩, ?_⟩, ?_⟩
        · rcases hm t ht with ⟨s, hs, e⟩ | ⟨s, hs, e⟩
          · rw [← e]
            rcases List.mem_cons.mp hs with rfl | hs
            · exact h
            · exact Nat.lt_trans h (hx1.1 s hs)
          · rw [← e]; exact hy1.1 s hs
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hy.2 _ (List.mem_cons_self ..)
          · exact hc.2 t ht
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact Or.inr ⟨_, List.mem_cons_self .., rfl⟩
          · rcases hm t ht with e | ⟨s, hs, e⟩
            · exact Or.inl e
            · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, e⟩

theorem Canon.add {p q : Lin w} (hp : Canon p.terms) (hq : Canon q.terms) :
    Canon (Lin.add p q).terms := (canon_merge _ _ _ rfl hp hq).1

theorem Canon.scale {k : BitVec w} {p : Lin w} (hp : Canon p.terms) :
    Canon (Lin.scale k p).terms := by
  refine ⟨?_, fun t ht => (List.mem_filter.mp ht).2 |> fun h => by simpa using h⟩
  apply List.Pairwise.sublist List.filter_sublist
  rw [List.pairwise_map]
  exact hp.1.imp (fun h => h)

theorem Canon.foldr {ps : List (Lin w)} (h : ∀ p ∈ ps, Canon p.terms) :
    Canon (ps.foldr Lin.add (Lin.ofConst 0)).terms := by
  induction ps with
  | nil => exact ⟨List.Pairwise.nil, fun _ h => by simp [Lin.ofConst] at h⟩
  | cons p ps ih =>
    simp only [List.foldr_cons]
    exact Canon.add (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem Canon.atom (hw : 1 ≤ w) (a : Nat) : Canon (Lin.atom (w := w) a).terms := by
  refine ⟨List.pairwise_singleton _ _, fun t ht => ?_⟩
  simp only [Lin.atom, List.mem_singleton] at ht
  subst ht
  intro e
  have := congrArg BitVec.toNat e
  simp at this
  have : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  omega

theorem Canon.const (x : BitVec w) : Canon (Lin.ofConst x).terms :=
  ⟨List.Pairwise.nil, fun _ h => by simp [Lin.ofConst] at h⟩

/-- The value of a list of terms under the valuation that is `1` at `a` and `0` elsewhere. -/
def delta (w a : Nat) : Nat → BitVec w := fun x => if x = a then 1 else 0

theorem evalTerms_delta_absent {a : Nat} :
    ∀ {ts : List (Nat × BitVec w)}, (∀ t ∈ ts, t.1 ≠ a) → Lin.evalTerms (delta w a) ts = 0
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Lin.evalTerms]
    rw [evalTerms_delta_absent (fun s hs => h s (List.mem_cons_of_mem _ hs))]
    have := h t (List.mem_cons_self ..)
    simp [delta, this]

theorem evalTerms_zero : ∀ (ts : List (Nat × BitVec w)), Lin.evalTerms (fun _ => 0#w) ts = 0#w
  | [] => rfl
  | t :: ts => by
    simp only [Lin.evalTerms]
    rw [evalTerms_zero ts]
    simp

theorem evalTerms_cons_delta {a : Nat} {c : BitVec w} {ts : List (Nat × BitVec w)}
    (h : ∀ t ∈ ts, a < t.1) : Lin.evalTerms (delta w a) ((a, c) :: ts) = c := by
  simp only [Lin.evalTerms]
  rw [evalTerms_delta_absent (fun t ht => Nat.ne_of_gt (h t ht))]
  simp [delta]

/-- Two canonical term lists with the same value under every valuation are equal. -/
theorem canon_terms_eq :
    ∀ (n : Nat) (L M : List (Nat × BitVec w)), L.length + M.length = n → Canon L → Canon M →
      (∀ lv, Lin.evalTerms lv L = Lin.evalTerms lv M) → L = M := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro L M hn hL hM he
    match L, M with
    | [], [] => rfl
    | (a, c) :: L, [] =>
      exfalso
      have := he (delta w a)
      rw [evalTerms_cons_delta (fun t ht => (List.pairwise_cons.mp hL.1).1 t ht)] at this
      exact hL.2 _ (List.mem_cons_self ..) this
    | [], (b, d) :: M =>
      exfalso
      have := he (delta w b)
      rw [evalTerms_cons_delta (fun t ht => (List.pairwise_cons.mp hM.1).1 t ht)] at this
      exact hM.2 _ (List.mem_cons_self ..) this.symm
    | (a, c) :: L, (b, d) :: M =>
      have hL1 := List.pairwise_cons.mp hL.1
      have hM1 := List.pairwise_cons.mp hM.1
      have hLt : Canon L := ⟨hL1.2, fun t ht => hL.2 t (List.mem_cons_of_mem _ ht)⟩
      have hMt : Canon M := ⟨hM1.2, fun t ht => hM.2 t (List.mem_cons_of_mem _ ht)⟩
      rcases Nat.lt_trichotomy a b with h | rfl | h
      · exfalso
        have := he (delta w a)
        rw [evalTerms_cons_delta (fun t ht => hL1.1 t ht),
          evalTerms_delta_absent (a := a) (fun t ht => by
            rcases List.mem_cons.mp ht with rfl | ht
            · exact Nat.ne_of_gt h
            · exact Nat.ne_of_gt (Nat.lt_trans h (hM1.1 t ht)))] at this
        exact hL.2 _ (List.mem_cons_self ..) this
      · have hcd : c = d := by
          have := he (delta w a)
          rwa [evalTerms_cons_delta (fun t ht => hL1.1 t ht),
            evalTerms_cons_delta (fun t ht => hM1.1 t ht)] at this
        subst hcd
        have hrest : L = M := by
          apply ih _ (by simp at hn ⊢; omega) L M rfl hLt hMt
          intro lv
          have := he lv
          simp only [Lin.evalTerms] at this
          exact (BitVec.add_right_inj _).mp this
        rw [hrest]
      · exfalso
        have := he (delta w b)
        rw [evalTerms_cons_delta (fun t ht => hM1.1 t ht),
          evalTerms_delta_absent (a := b) (fun t ht => by
            rcases List.mem_cons.mp ht with rfl | ht
            · exact Nat.ne_of_gt h
            · exact Nat.ne_of_gt (Nat.lt_trans h (hL1.1 t ht)))] at this
        exact hM.2 _ (List.mem_cons_self ..) this.symm

theorem canon_eq {p q : Lin w} (hp : Canon p.terms) (hq : Canon q.terms)
    (he : ∀ lv, Lin.eval lv p = Lin.eval lv q) : p = q := by
  have hc : p.const = q.const := by
    have := he (fun _ => 0#w)
    simp only [Lin.eval, evalTerms_zero] at this
    simpa using this
  have ht : p.terms = q.terms := by
    apply canon_terms_eq _ _ _ rfl hp hq
    intro lv
    have := he lv
    simp only [Lin.eval] at this
    rw [hc] at this
    exact (BitVec.add_right_inj _).mp this
  obtain ⟨pc, pt⟩ := p
  obtain ⟨qc, qt⟩ := q
  simp only at hc ht
  subst hc; subst ht; rfl

end canon

/-! ## The forms of a pool -/

section forms
variable {pool : Pool} {w : Nat}

/-- The arguments of a node of a well-formed pool come before it. -/
def ArgsBefore (pool : Pool) : Prop := ∀ (i : Nat) (n : Node), pool[i]? = some n → ∀ a ∈ n.args, a < i

theorem argsBefore_of_ok {st : St} (h : PoolOK st) : ArgsBefore st.pool :=
  fun i n hn => (h.tys.2 i n hn).1

/-- `lin` of a node of a well-formed pool is canonical, and its atoms satisfy every property
the node has that is closed under arguments. -/
theorem lin_canon_atoms (hw : 1 ≤ w) (hab : ArgsBefore pool) {P : Nat → Prop}
    (hcl : ∀ (i : Nat) (n : Node), P i → pool[i]? = some n → ∀ a ∈ n.args, P a) :
    ∀ i, i < pool.size → P i → Canon (Bcf.lin pool w i).terms ∧ LinP P (Bcf.lin pool w i).terms := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi hP
    have hatom : Canon (Lin.atom (w := w) i).terms ∧ LinP P (Lin.atom (w := w) i).terms :=
      ⟨Canon.atom hw i, LinP.atom hP⟩
    obtain ⟨⟨op, args⟩, hn⟩ : ∃ n, pool[i]? = some n := ⟨pool[i], by simp [hi]⟩
    have hargs := hab i _ hn
    have hcl' := hcl i _ hP hn
    have hlt : ∀ a ∈ args, a < pool.size := fun a ha => Nat.lt_trans (hargs a ha) hi
    cases op with
    | bvVal w' v =>
      rw [pl_lin_val hn]
      split
      · exact ⟨Canon.const _, LinP.const _⟩
      · exact hatom
    | bvAdd w' =>
      rw [pl_lin_add hn]
      split
      · constructor
        · apply Canon.foldr
          intro p hp
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
          have ha' : a ∈ args := by simpa using ha
          rw [ite_eq_left (hargs a ha')]
          exact (ih a (hargs a ha') (hlt a ha') (hcl' a ha')).1
        · apply LinP.foldr
          intro p hp
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
          have ha' : a ∈ args := by simpa using ha
          rw [ite_eq_left (hargs a ha')]
          exact (ih a (hargs a ha') (hlt a ha') (hcl' a ha')).2
      · exact hatom
    | bvSub w' =>
      by_cases h2 : args.size = 2
      · obtain ⟨a, b, rfl⟩ := array_eq_two h2
        have ha : a ∈ #[a, b] := by simp
        have hb : b ∈ #[a, b] := by simp
        rw [pl_lin_sub hn]
        split
        · rename_i hc
          have A := ih a hc.2.1 (hlt a ha) (hcl' a ha)
          have B := ih b hc.2.2 (hlt b hb) (hcl' b hb)
          exact ⟨Canon.add A.1 (Canon.scale B.1), LinP.add A.2 (LinP.scale B.2)⟩
        · exact hatom
      · rw [pl_lin_sub_other hn h2]; exact hatom
    | bvNeg w' =>
      by_cases h1 : args.size = 1
      · obtain ⟨a, rfl⟩ := array_eq_one h1
        have ha : a ∈ #[a] := by simp
        rw [pl_lin_neg hn]
        split
        · rename_i hc
          have A := ih a hc.2 (hlt a ha) (hcl' a ha)
          exact ⟨Canon.scale A.1, LinP.scale A.2⟩
        · exact hatom
      · rw [pl_lin_neg_other hn h1]; exact hatom
    | bvMul w' =>
      by_cases h2 : args.size = 2
      · obtain ⟨a, b, rfl⟩ := array_eq_two h2
        have ha : a ∈ #[a, b] := by simp
        have hb : b ∈ #[a, b] := by simp
        by_cases hc : w' = w ∧ a < i ∧ b < i
        · cases hka : Bcf.litVal pool w a with
          | some k =>
            rw [pl_lin_mul_a hn hc hka]
            have B := ih b hc.2.2 (hlt b hb) (hcl' b hb)
            exact ⟨Canon.scale B.1, LinP.scale B.2⟩
          | none =>
            cases hkb : Bcf.litVal pool w b with
            | some k =>
              rw [pl_lin_mul_b hn hc hka hkb]
              have A := ih a hc.2.1 (hlt a ha) (hcl' a ha)
              exact ⟨Canon.scale A.1, LinP.scale A.2⟩
            | none => rw [pl_lin_mul_none hn hka hkb]; exact hatom
        · rw [pl_lin_mul_no hn hc]; exact hatom
      · rw [pl_lin_mul_other hn h2]; exact hatom
    | _ => rw [pl_lin_other hn (by simp [opC]) (by simp [opC]) (by simp [opC]) (by simp [opC])
        (by simp [opC])]; exact hatom

end forms

/-! ## Through a view -/

section view
variable (S : VSt) {w : Nat}

theorem litVal_ren (_hcs : PoolOK S.cs) {a : Nat} (ha : S.lv a) :
    Bcf.litVal S.cs.pool w (S.σ a) = Bcf.litVal S.pool w a := by
  obtain ⟨n, hn⟩ := S.node_of_lv ha
  have hc := S.img a n ha hn
  unfold Bcf.litVal
  rw [hn, hc]
  obtain ⟨op, args⟩ := n
  cases op <;> rfl

/-- The C-side form of `σ x` and the Lean form of `x` denote the same polynomial. -/
theorem lin_eval_ren (hcs : PoolOK S.cs) :
    ∀ x, S.lv x → ∀ lv : Nat → BitVec w,
      Lin.eval lv (Bcf.lin S.cs.pool w (S.σ x)) = Lin.eval (fun y => lv (S.σ y)) (Bcf.lin S.pool w x) := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx lv
    obtain ⟨⟨op, args⟩, hn⟩ := S.node_of_lv hx
    have hc : S.cs.pool[S.σ x]? = some ⟨op, args.map S.σ⟩ := S.img x _ hx hn
    have hab := argsBefore_of_ok S.ok x _ hn
    have habc := argsBefore_of_ok hcs (S.σ x) _ hc
    have hcl : ∀ a ∈ args, S.lv a := fun a ha => S.closed x _ hx hn a ha
    have hσlt : ∀ a ∈ args, S.σ a < S.σ x := fun a ha => habc (S.σ a) (by simpa using ⟨a, ha, rfl⟩)
    have hatom : Lin.eval lv (Lin.atom (w := w) (S.σ x)) =
        Lin.eval (fun y => lv (S.σ y)) (Lin.atom (w := w) x) := by
      rw [Lin.eval_atom, Lin.eval_atom]
    cases op with
    | bvVal w' v =>
      rw [pl_lin_val hn, pl_lin_val hc]
      split
      · rfl
      · exact hatom
    | bvAdd w' =>
      rw [pl_lin_add hn, pl_lin_add hc]
      split
      · rw [Lin.eval_foldr_add, Lin.eval_foldr_add]
        simp only [Array.toList_map, List.map_map, List.foldr_map]
        apply foldr_add_congr
        intro a ha
        have ha' : a ∈ args := by simpa using ha
        simp only [Function.comp, ite_eq_left (hσlt a ha'), ite_eq_left (hab a ha')]
        exact ih a (hab a ha') (hcl a ha') lv
      · exact hatom
    | bvSub w' =>
      by_cases h2 : args.size = 2
      · obtain ⟨a, b, rfl⟩ := array_eq_two h2
        have ha : a ∈ #[a, b] := by simp
        have hb : b ∈ #[a, b] := by simp
        have hc' : S.cs.pool[S.σ x]? = some ⟨.bvSub w', #[S.σ a, S.σ b]⟩ := by simpa using hc
        rw [pl_lin_sub hn, pl_lin_sub hc']
        by_cases hw' : w' = w
        · rw [ite_eq_left ⟨hw', hσlt a ha, hσlt b hb⟩, ite_eq_left ⟨hw', hab a ha, hab b hb⟩,
            Lin.eval_add, Lin.eval_add, Lin.eval_neg, Lin.eval_neg,
            ih a (hab a ha) (hcl a ha) lv, ih b (hab b hb) (hcl b hb) lv]
        · rw [ite_eq_right (fun h => hw' h.1), ite_eq_right (fun h => hw' h.1)]; exact hatom
      · have hs : (args.map S.σ).size ≠ 2 := by simpa using h2
        rw [pl_lin_sub_other hn h2, pl_lin_sub_other hc hs]; exact hatom
    | bvNeg w' =>
      by_cases h1 : args.size = 1
      · obtain ⟨a, rfl⟩ := array_eq_one h1
        have ha : a ∈ #[a] := by simp
        have hc' : S.cs.pool[S.σ x]? = some ⟨.bvNeg w', #[S.σ a]⟩ := by simpa using hc
        rw [pl_lin_neg hn, pl_lin_neg hc']
        by_cases hw' : w' = w
        · rw [ite_eq_left ⟨hw', hσlt a ha⟩, ite_eq_left ⟨hw', hab a ha⟩, Lin.eval_neg, Lin.eval_neg,
            ih a (hab a ha) (hcl a ha) lv]
        · rw [ite_eq_right (fun h => hw' h.1), ite_eq_right (fun h => hw' h.1)]; exact hatom
      · have hs : (args.map S.σ).size ≠ 1 := by simpa using h1
        rw [pl_lin_neg_other hn h1, pl_lin_neg_other hc hs]; exact hatom
    | bvMul w' =>
      by_cases h2 : args.size = 2
      · obtain ⟨a, b, rfl⟩ := array_eq_two h2
        have ha : a ∈ #[a, b] := by simp
        have hb : b ∈ #[a, b] := by simp
        have hc' : S.cs.pool[S.σ x]? = some ⟨.bvMul w', #[S.σ a, S.σ b]⟩ := by simpa using hc
        have hla := litVal_ren S (w := w) hcs (hcl a ha)
        have hlb := litVal_ren S (w := w) hcs (hcl b hb)
        by_cases hw' : w' = w
        · have hcL : w' = w ∧ a < x ∧ b < x := ⟨hw', hab a ha, hab b hb⟩
          have hcC : w' = w ∧ S.σ a < S.σ x ∧ S.σ b < S.σ x := ⟨hw', hσlt a ha, hσlt b hb⟩
          cases hka : Bcf.litVal S.pool w a with
          | some k =>
            rw [pl_lin_mul_a hn hcL hka, pl_lin_mul_a hc' hcC (by rw [hla, hka]),
              Lin.eval_scale, Lin.eval_scale, ih b (hab b hb) (hcl b hb) lv]
          | none =>
            cases hkb : Bcf.litVal S.pool w b with
            | some k =>
              rw [pl_lin_mul_b hn hcL hka hkb, pl_lin_mul_b hc' hcC (by rw [hla, hka])
                (by rw [hlb, hkb]), Lin.eval_scale, Lin.eval_scale, ih a (hab a ha) (hcl a ha) lv]
            | none =>
              rw [pl_lin_mul_none hn hka hkb, pl_lin_mul_none hc' (by rw [hla, hka])
                (by rw [hlb, hkb])]
              exact hatom
        · rw [pl_lin_mul_no hn (fun h => hw' h.1), pl_lin_mul_no hc' (fun h => hw' h.1)]
          exact hatom
      · have hs : (args.map S.σ).size ≠ 2 := by simpa using h2
        rw [pl_lin_mul_other hn h2, pl_lin_mul_other hc hs]; exact hatom
    | _ =>
      rw [pl_lin_other hn (by simp [opC]) (by simp [opC]) (by simp [opC]) (by simp [opC])
        (by simp [opC]), pl_lin_other hc (by simp [opC]) (by simp [opC]) (by simp [opC])
        (by simp [opC]) (by simp [opC])]
      exact hatom

/-- **Equal C-side forms mean equal Lean forms.** -/
theorem lin_ren (hcs : PoolOK S.cs) (hw : 1 ≤ w) {a b : Nat} (ha : S.lv a) (hb : S.lv b)
    (h : Bcf.lin S.cs.pool w (S.σ a) = Bcf.lin S.cs.pool w (S.σ b)) :
    Bcf.lin S.pool w a = Bcf.lin S.pool w b := by
  classical
  have hab := argsBefore_of_ok S.ok
  have hcl : ∀ (i : Nat) (n : Node), S.lv i → S.pool[i]? = some n → ∀ a ∈ n.args, S.lv a :=
    fun i n hi hn a ha => S.closed i n hi hn a ha
  obtain ⟨cA, pA⟩ := lin_canon_atoms (w := w) hw hab hcl a (S.lt ha) ha
  obtain ⟨cB, pB⟩ := lin_canon_atoms (w := w) hw hab hcl b (S.lt hb) hb
  apply canon_eq cA cB
  intro lv'
  -- a valuation of the C-side atoms that is `lv'` through `σ` on the live indices
  let lv : Nat → BitVec w := fun y =>
    if hy : ∃ x, S.lv x ∧ S.σ x = y then lv' (Classical.choose hy) else 0
  have hlv : ∀ x, S.lv x → lv (S.σ x) = lv' x := by
    intro x hx
    have hy : ∃ x', S.lv x' ∧ S.σ x' = S.σ x := ⟨x, hx, rfl⟩
    simp only [lv, dite_eq_left hy]
    have := Classical.choose_spec hy
    rw [S.inj _ _ this.1 hx this.2]
  have hagree : ∀ (L : Lin w), LinP S.lv L.terms →
      Lin.eval (fun y => lv (S.σ y)) L = Lin.eval lv' L := by
    intro L hL
    unfold Lin.eval
    congr 1
    obtain ⟨_, ts⟩ := L
    simp only at hL ⊢
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [Lin.evalTerms]
      rw [hlv t.1 hL.head, ih hL.tail]
  have e := congrArg (Lin.eval lv) h
  rw [lin_eval_ren S hcs a ha lv, lin_eval_ren S hcs b hb lv, hagree _ pA, hagree _ pB] at e
  exact e

end view

end Vbcf.Proof
