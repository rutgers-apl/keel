import Bcf.Soundness

/-!
# ABSORB and ACI_NORM

Both rules reason about the maximal tree of one associative-commutative
operator.  One abstract lemma, `leaf_fold`, says the value of such a
tree is the fold of its leaves; `aci_generic` derives from it the three
ways ACI_NORM may conclude an equation.  Both are instantiated for
`conj`, `disj`, `bvand`, `bvor` and `bvxor`.
-/

namespace Bcf

/-! ## Abstract folds -/

section Folds
variable {α : Type} {f : α → α → α} {e : α}

theorem foldl_op (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) (hcomm : ∀ x y, f x y = f y x)
    (hid : ∀ x, f e x = x) (l : List α) (a : α) : l.foldl f a = f a (l.foldl f e) := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil]; rw [hcomm, hid]
  | cons x l ih => simp only [List.foldl_cons]; rw [ih (f a x), ih (f e x), hid, hassoc]

theorem foldl_cons_op (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) (hcomm : ∀ x y, f x y = f y x)
    (hid : ∀ x, f e x = x) (x : α) (l : List α) : (x :: l).foldl f e = f x (l.foldl f e) := by
  simp only [List.foldl_cons]; rw [foldl_op hassoc hcomm hid, hid]

theorem foldl_append_op (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) (hcomm : ∀ x y, f x y = f y x)
    (hid : ∀ x, f e x = x) (l1 l2 : List α) : (l1 ++ l2).foldl f e = f (l1.foldl f e) (l2.foldl f e) := by
  rw [List.foldl_append, foldl_op hassoc hcomm hid]

theorem foldl_perm (hrc : ∀ a x y, f (f a x) y = f (f a y) x) {l1 l2 : List α} (p : l1.Perm l2) :
    ∀ a, l1.foldl f a = l2.foldl f a := by
  induction p with
  | nil => intro a; rfl
  | cons x _ ih => intro a; simp only [List.foldl_cons]; exact ih _
  | swap x y l => intro a; simp only [List.foldl_cons]; rw [hrc]
  | trans _ _ ih1 ih2 => intro a; rw [ih1, ih2]

theorem foldl_absorb_dup (hrc : ∀ a x y, f (f a x) y = f (f a y) x) (hidem : ∀ a x, f (f a x) x = f a x)
    (g : Nat → α) {x : Nat} {l : List Nat} (hx : x ∈ l) (a : α) :
    (l.map g).foldl f (f a (g x)) = (l.map g).foldl f a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    by_cases hxy : x = y
    · subst hxy; rw [hidem]
    · have hx' : x ∈ rest := by simp at hx; exact hx.resolve_left hxy
      rw [hrc, ih hx']

theorem foldl_map_dedup (hrc : ∀ a x y, f (f a x) y = f (f a y) x) (hidem : ∀ a x, f (f a x) x = f a x)
    (g : Nat → α) (l : List Nat) (a : α) : ((dedupNat l).map g).foldl f a = (l.map g).foldl f a := by
  induction l generalizing a with
  | nil => rfl
  | cons x rest ih =>
    simp only [dedupNat]
    split
    · rename_i hx
      rw [ih, List.map_cons, List.foldl_cons, foldl_absorb_dup hrc hidem g hx]
    · simp only [List.map_cons, List.foldl_cons]; exact ih _

theorem rc_of_assoc_comm (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) (hcomm : ∀ x y, f x y = f y x) :
    ∀ a x y, f (f a x) y = f (f a y) x := by
  intro a x y; rw [hassoc, hassoc, hcomm x y]

end Folds

theorem mem_dedupNat {x : Nat} {l : List Nat} : x ∈ dedupNat l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupNat]
  | cons y rest ih =>
    simp only [dedupNat]
    split
    · rename_i hy; simp [ih]; intro hxy; subst hxy; exact hy
    · simp [ih]

theorem dedupNat_nil {l : List Nat} (h : dedupNat l = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons x rest =>
    exfalso
    have : x ∈ dedupNat (x :: rest) := mem_dedupNat.mpr (by simp)
    rw [h] at this; simp at this

theorem sortNat_perm (l : List Nat) : (sortNat l).Perm l := List.mergeSort_perm l _

theorem perm_of_sortNat_eq {l1 l2 : List Nat} (h : sortNat l1 = sortNat l2) : l1.Perm l2 :=
  (sortNat_perm l1).symm.trans (h ▸ sortNat_perm l2)

/-! ## Flattening -/

theorem flattenF_stable (pool : Pool) (op : Op) (i : Nat) :
    ∀ f f', i < f → i < f' → flattenF pool op f i = flattenF pool op f' i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f f' hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [flattenF]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      split
      · congr 1
        funext a
        split
        · exact ih a (by assumption) g g' (by omega) (by omega)
        · rfl
      · rfl

/-- What the children of a same-operator node contribute to the flattening. -/
def childLeaves (pool : Pool) (op : Op) (i : Nat) (a : Nat) : List Nat :=
  if a < i then flatten pool op a else []

theorem sameAssoc_refl (op : Op) : sameAssoc op op = true := by
  unfold sameAssoc; split <;> simp_all

theorem sameAssoc_of_not_concat {op o : Op} (hnc : isConcatOp op = false) :
    sameAssoc op o = (o == op) := by
  unfold sameAssoc
  rw [ite_eq_right (by simp [hnc])]
  cases h1 : (op == o) <;> cases h2 : (o == op) <;> simp_all

theorem sameAssoc_concat (w : Nat) (o : Op) : sameAssoc (.bvConcat w) o = isConcatOp o := by
  simp [sameAssoc, isConcatOp]

theorem isConcatOp_iff (o : Op) : isConcatOp o = true ↔ ∃ w, o = .bvConcat w := by
  cases o <;> simp [isConcatOp]

theorem flatten_node' {pool : Pool} {op : Op} {i : Nat} {n : Node}
    (h : pool[i]? = some n) (hs : sameAssoc op n.op = true) :
    flatten pool op i = n.args.toList.flatMap (childLeaves pool op i) := by
  unfold flatten
  simp only [flattenF, h, hs, ite_true]
  congr 1
  funext a
  unfold childLeaves flatten
  split
  · exact flattenF_stable pool op a _ _ (by assumption) (by omega)
  · rfl

theorem flatten_node {pool : Pool} {op : Op} {i : Nat} {args : Array Nat}
    (h : pool[i]? = some ⟨op, args⟩) :
    flatten pool op i = args.toList.flatMap (childLeaves pool op i) :=
  flatten_node' h (sameAssoc_refl op)

theorem flatten_leaf {pool : Pool} {op : Op} {i : Nat} {n : Node}
    (h : pool[i]? = some n) (hop : sameAssoc op n.op = false) :
    flatten pool op i = if isNilElem op n then [] else [i] := by
  unfold flatten
  simp only [flattenF, h]
  simp [hop]

theorem node_of_lt {pool : Pool} {a : Nat} (ha : a < pool.size) : ∃ m, pool[a]? = some m := by
  cases hm : pool[a]? with
  | none => rw [Array.getElem?_eq_none_iff] at hm; omega
  | some m => exact ⟨m, rfl⟩

/-- **Abstract flattening lemma.**  If every same-operator node is the
fold of its children and every identity literal is `e`, then every
same-operator node is the fold of the leaves of its tree. -/
theorem leaf_fold {α : Type} {f : α → α → α} {e : α}
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) (hcomm : ∀ x y, f x y = f y x) (hid : ∀ x, f e x = x)
    {pool : Pool} (hwf : WF pool) (op : Op) (hnc : isConcatOp op = false) (lv : Nat → α)
    (hnode : ∀ i args, pool[i]? = some ⟨op, args⟩ → lv i = (args.toList.map lv).foldl f e)
    (hnil : ∀ i n, pool[i]? = some n → isNilElem op n = true → lv i = e) :
    ∀ i args, pool[i]? = some ⟨op, args⟩ → lv i = ((flatten pool op i).map lv).foldl f e := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro args h
    rw [hnode i args h, flatten_node h]
    have hlt := (hwf i _ h).1
    have key : ∀ a ∈ args.toList, ((childLeaves pool op i a).map lv).foldl f e = lv a := by
      intro a ha
      have ha' : a < i := hlt a (by simpa using ha)
      unfold childLeaves
      simp only [ha', ite_true]
      obtain ⟨m, hm⟩ := node_of_lt (Nat.lt_trans ha' (idx_lt_of_get h))
      by_cases hop : m.op = op
      · obtain ⟨o, margs⟩ := m
        simp only at hop; subst hop
        exact (ih a ha' margs hm).symm
      · rw [flatten_leaf hm (by rw [sameAssoc_of_not_concat hnc]; simpa using hop)]
        split
        · rename_i hn; simp only [List.map_nil, List.foldl_nil]; exact (hnil a m hm hn).symm
        · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hid]
    clear ih hnode
    generalize args.toList = l at key ⊢
    induction l with
    | nil => rfl
    | cons a rest ihl =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons]
      rw [foldl_append_op hassoc hcomm hid, foldl_cons_op hassoc hcomm hid, key a (by simp),
          ihl (fun a' ha' => key a' (by simp [ha']))]

/-- Leaves of a same-operator tree are arguments of some node of the tree. -/
theorem flatten_typed {pool : Pool} (hwf : WF pool) (op : Op) (hnc : isConcatOp op = false) (T : Ty)
    (hargty : ∀ (i : Nat) (args : Array Nat), pool[i]? = some ⟨op, args⟩ → ∀ a ∈ args, typeOf pool a = some T) :
    ∀ (i : Nat) (args : Array Nat), pool[i]? = some ⟨op, args⟩ → ∀ x ∈ flatten pool op i, typeOf pool x = some T := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro args h x hx
    rw [flatten_node h] at hx
    obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
    have ha' : a < i := (hwf i _ h).1 a (by simpa using ha)
    unfold childLeaves at hx
    simp only [ha', ite_true] at hx
    obtain ⟨m, hm⟩ := node_of_lt (Nat.lt_trans ha' (idx_lt_of_get h))
    by_cases hop : m.op = op
    · obtain ⟨o, margs⟩ := m
      simp only at hop; subst hop
      exact ih a ha' margs hm x hx
    · rw [flatten_leaf hm (by rw [sameAssoc_of_not_concat hnc]; simpa using hop)] at hx
      split at hx
      · simp at hx
      · simp at hx; subst x; exact hargty i args h a (by simpa using ha)

/-! ## The generic ACI consequences -/

theorem aci_generic {α : Type} {f : α → α → α} {e : α}
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) (hcomm : ∀ x y, f x y = f y x) (hid : ∀ x, f e x = x)
    {pool : Pool} (hwf : WF pool) (ρ : Assign) (op : Op) (lv : Nat → α) (emb : α → Val) (T : Ty)
    (hnc : isConcatOp op = false)
    (hidem : isIdemOp op = true → ∀ a x, f (f a x) x = f a x)
    (hnode : ∀ (i : Nat) (args : Array Nat), pool[i]? = some ⟨op, args⟩ → lv i = (args.toList.map lv).foldl f e)
    (hnil : ∀ (i : Nat) (n : Node), pool[i]? = some n → isNilElem op n = true → lv i = e)
    (hemb : ∀ i, typeOf pool i = some T → eval pool ρ i = emb (lv i))
    (hty : ∀ (i : Nat) (args : Array Nat), pool[i]? = some ⟨op, args⟩ → typeOf pool i = some T)
    (hargty : ∀ (i : Nat) (args : Array Nat), pool[i]? = some ⟨op, args⟩ → ∀ a ∈ args, typeOf pool a = some T)
    (hnilval : ∀ (i : Nat) (n : Node), pool[i]? = some n → isNilElem op n = true → eval pool ρ i = emb e) :
    (∀ (a b : Nat) (aargs bargs : Array Nat), pool[a]? = some ⟨op, aargs⟩ → pool[b]? = some ⟨op, bargs⟩ →
        aciLeaves pool op a = aciLeaves pool op b → eval pool ρ a = eval pool ρ b) ∧
    (∀ (a : Nat) (aargs : Array Nat) (x : Nat), pool[a]? = some ⟨op, aargs⟩ → aciLeaves pool op a = [x] →
        eval pool ρ a = eval pool ρ x) ∧
    (∀ (a : Nat) (aargs : Array Nat) (b : Nat) (n : Node), pool[a]? = some ⟨op, aargs⟩ → aciLeaves pool op a = [] →
        pool[b]? = some n → isNilElem op n = true → eval pool ρ a = eval pool ρ b) := by
  have hrc := rc_of_assoc_comm hassoc hcomm
  have hlf := leaf_fold hassoc hcomm hid hwf op hnc lv hnode hnil
  -- the canonical leaf list determines the fold
  have hcanon : ∀ i args, pool[i]? = some ⟨op, args⟩ →
      lv i = ((aciLeaves pool op i).map lv).foldl f e := by
    intro i args h
    rw [hlf i args h]
    unfold aciLeaves
    rw [ite_eq_right (by simpa using hnc)]
    split
    · rename_i hi
      rw [← foldl_map_dedup hrc (hidem hi) lv (flatten pool op i) e]
      exact foldl_perm hrc ((sortNat_perm _).map lv) e |>.symm
    · exact foldl_perm hrc ((sortNat_perm _).map lv) e |>.symm
  refine ⟨?_, ?_, ?_⟩
  · intro a b aargs bargs ha hb heq
    rw [hemb a (hty a aargs ha), hemb b (hty b bargs hb), hcanon a aargs ha, hcanon b bargs hb, heq]
  · intro a aargs x ha hl
    have hx : x ∈ flatten pool op a := by
      have : x ∈ aciLeaves pool op a := by rw [hl]; simp
      unfold aciLeaves at this
      rw [ite_eq_right (by simpa using hnc)] at this
      have := (sortNat_perm _).mem_iff.mp this
      split at this
      · exact mem_dedupNat.mp this
      · exact this
    rw [hemb a (hty a aargs ha), hemb x (flatten_typed hwf op hnc T hargty a aargs ha x hx), hcanon a aargs ha, hl]
    simp [hid]
  · intro a aargs b n ha hl hb hn
    rw [hemb a (hty a aargs ha), hcanon a aargs ha, hl, hnilval b n hb hn]
    rfl

/-! ## Leaf values for the five operators -/

def evalB (pool : Pool) (ρ : Assign) (a : Nat) : Bool :=
  match eval pool ρ a with
  | .bool b => b
  | _ => false

def evalV (pool : Pool) (ρ : Assign) (w : Nat) (a : Nat) : BitVec w :=
  match eval pool ρ a with
  | .bv w' x => if h : w' = w then x.cast h else 0
  | _ => 0

theorem evalB_spec {pool : Pool} {ρ : Assign} {a : Nat} (h : typeOf pool a = some .bool) :
    eval pool ρ a = .bool (evalB pool ρ a) := by
  obtain ⟨b, hb⟩ := eval_bool (ρ := ρ) h
  simp [evalB, hb]

theorem evalV_spec {pool : Pool} {ρ : Assign} {w a : Nat} (h : typeOf pool a = some (.bv w)) :
    eval pool ρ a = .bv w (evalV pool ρ w a) := by
  obtain ⟨x, hx⟩ := eval_bv (ρ := ρ) h
  simp [evalV, hx]

theorem bools_map_evalB {pool : Pool} {ρ : Assign} {l : List Nat}
    (h : ∀ a ∈ l, typeOf pool a = some .bool) :
    Val.bools (l.map (eval pool ρ)) = some (l.map (evalB pool ρ)) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, Val.bools, evalB_spec (h a (by simp)), Val.asBool_bool,
      ih (fun a' ha' => h a' (by simp [ha']))]

theorem bvs_map_evalV {pool : Pool} {ρ : Assign} {w : Nat} {l : List Nat}
    (h : ∀ a ∈ l, typeOf pool a = some (.bv w)) :
    Val.bvs w (l.map (eval pool ρ)) = some (l.map (evalV pool ρ w)) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, Val.bvs, evalV_spec (h a (by simp)), Val.asBv_bv, dite_true,
      BitVec.cast_eq, ih (fun a' ha' => h a' (by simp [ha']))]

theorem all_eq_foldl (l : List Bool) (b : Bool) : (b && l.all id) = l.foldl (· && ·) b := by
  induction l generalizing b with
  | nil => simp
  | cons x rest ih => simp only [List.all_cons, List.foldl_cons, id]; rw [← ih]; simp [Bool.and_assoc]

theorem any_eq_foldl (l : List Bool) (b : Bool) : (b || l.any id) = l.foldl (· || ·) b := by
  induction l generalizing b with
  | nil => simp
  | cons x rest ih => simp only [List.any_cons, List.foldl_cons, id]; rw [← ih]; simp [Bool.or_assoc]

theorem allBv_mem {w : Nat} {tys : List Ty} (h : allBv w tys = true) {t : Ty} (ht : t ∈ tys) : t = .bv w := by
  induction tys with
  | nil => simp at ht
  | cons a rest ih =>
    cases a with
    | bv w' =>
      simp [allBv] at h; simp at ht
      rcases ht with rfl | ht
      · rw [h.1]
      · exact ih h.2 ht
    | bool => simp [allBv] at h
    | list _ _ => simp [allBv] at h

/-- Arguments of a well-typed n-ary bit-vector node have its width. -/
theorem bvN_args_bv {pool : Pool} (hwf : WF pool) {e w : Nat} {args : Array Nat} {op : Op}
    (he : pool[e]? = some ⟨op, args⟩) (hres : op.resultTy = bvNTy w) :
    (∀ a ∈ args, typeOf pool a = some (.bv w)) ∧ 2 ≤ args.size ∧ w ≠ 0 ∧ typeOf pool e = some (.bv w) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf e _ he).2
  have h2 := ht
  rw [typeOf_node hwf he, hres] at h2
  cases hm : mapOpt (typeOf pool) args.toList with
  | none => rw [hm] at h2; simp at h2
  | some tys =>
    rw [hm] at h2
    simp only [Option.bind_some, bvNTy, tyGuard] at h2
    split at h2
    · rename_i hc
      refine ⟨?_, ?_, hc.1, ?_⟩
      · intro a ha
        obtain ⟨y, hy, hfy⟩ := mapOpt_mem hm (by simpa using ha)
        rw [hfy]; congr; exact allBv_mem hc.2.1 hy
      · have := mapOpt_length hm; simp at this; have := hc.2.2; omega
      · rw [ht]; simp at h2; rw [h2]
    · simp at h2

theorem boolN_args_bool' {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat} {op : Op}
    (he : pool[e]? = some ⟨op, args⟩) (hres : op.resultTy = boolNTy) :
    (∀ a ∈ args, typeOf pool a = some .bool) ∧ 2 ≤ args.size := by
  have h2 := (hwf e _ he).2
  rw [typeOf_node hwf he, hres] at h2
  cases hm : mapOpt (typeOf pool) args.toList with
  | none => rw [hm] at h2; simp at h2
  | some tys =>
    rw [hm] at h2
    simp only [Option.bind_some, boolNTy, tyGuard] at h2
    split at h2
    · rename_i hc
      refine ⟨?_, ?_⟩
      · intro a ha
        obtain ⟨y, hy, hfy⟩ := mapOpt_mem hm (by simpa using ha)
        rw [hfy]; congr; exact allBool_mem hc.1 hy
      · have := mapOpt_length hm; simp at this; omega
    · simp at h2

/-- The value of a literal node. -/
theorem eval_lit_bool {pool : Pool} (hwf : WF pool) {i : Nat} {b : Bool} {args : Array Nat}
    (h : pool[i]? = some ⟨.boolVal b, args⟩) (ρ : Assign) : eval pool ρ i = .bool b := by
  obtain rfl := boolVal_typing hwf h
  exact eval_boolVal hwf h ρ

theorem eval_lit_bv {pool : Pool} (hwf : WF pool) {i w v : Nat} {args : Array Nat}
    (h : pool[i]? = some ⟨.bvVal w v, args⟩) (ρ : Assign) : eval pool ρ i = .bv w (BitVec.ofNat w v) := by
  obtain ⟨rfl, hw, hw64, hv⟩ := bvVal_typing hwf h
  rw [eval_node hwf ρ h]
  simp [Op.eval, bvValEval, hw, hw64, hv]

theorem ofNat_allOnes (w : Nat) : BitVec.ofNat w (2 ^ w - 1) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes]
  exact Nat.mod_eq_of_lt (Nat.sub_one_lt (Nat.ne_of_gt (Nat.two_pow_pos w)))

/-! ## Node semantics for each operator, in leaf-fold form -/

theorem conj_node {pool : Pool} (hwf : WF pool) (ρ : Assign) :
    ∀ i args, pool[i]? = some ⟨.conj, args⟩ →
      evalB pool ρ i = (args.toList.map (evalB pool ρ)).foldl (· && ·) true := by
  intro i args h
  obtain ⟨hargs, hlen⟩ := boolN_args_bool' hwf h rfl
  have hb := bools_map_evalB (ρ := ρ) (l := args.toList) (fun a ha => hargs a (by simpa using ha))
  have hv := eval_node hwf ρ h
  simp only [Op.eval, boolN, hb, List.length_map, Array.length_toList] at hv
  rw [ite_eq_left hlen] at hv
  have : evalB pool ρ i = (args.toList.map (evalB pool ρ)).all id := by rw [evalB, hv]
  rw [this, ← all_eq_foldl, Bool.true_and]

theorem disj_node {pool : Pool} (hwf : WF pool) (ρ : Assign) :
    ∀ i args, pool[i]? = some ⟨.disj, args⟩ →
      evalB pool ρ i = (args.toList.map (evalB pool ρ)).foldl (· || ·) false := by
  intro i args h
  obtain ⟨hargs, hlen⟩ := boolN_args_bool' hwf h rfl
  have hb := bools_map_evalB (ρ := ρ) (l := args.toList) (fun a ha => hargs a (by simpa using ha))
  have hv := eval_node hwf ρ h
  simp only [Op.eval, boolN, hb, List.length_map, Array.length_toList] at hv
  rw [ite_eq_left hlen] at hv
  have : evalB pool ρ i = (args.toList.map (evalB pool ρ)).any id := by rw [evalB, hv]
  rw [this, ← any_eq_foldl, Bool.false_or]

theorem bvop_node {pool : Pool} (hwf : WF pool) (ρ : Assign) (w : Nat) (op : Op)
    (f : BitVec w → BitVec w → BitVec w) (e : BitVec w)
    (hres : op.resultTy = bvNTy w) (heval : ∀ vs, op.eval ρ vs = bvN w (List.foldl f e) vs) :
    ∀ i args, pool[i]? = some ⟨op, args⟩ →
      evalV pool ρ w i = (args.toList.map (evalV pool ρ w)).foldl f e := by
  intro i args h
  obtain ⟨hargs, hlen, hw, _⟩ := bvN_args_bv hwf h hres
  have hb := bvs_map_evalV (ρ := ρ) (w := w) (l := args.toList) (fun a ha => hargs a (by simpa using ha))
  have hv := eval_node hwf ρ h
  simp only [heval, bvN, hb, List.length_map, Array.length_toList] at hv
  rw [ite_eq_left ⟨hw, hlen⟩] at hv
  simp [evalV, hv]

theorem isNilElem_conj {n : Node} (h : isNilElem .conj n = true) : n.op = .boolVal true := by
  simpa [isNilElem] using h

theorem isNilElem_disj {n : Node} (h : isNilElem .disj n = true) : n.op = .boolVal false := by
  simpa [isNilElem] using h

theorem isNilElem_bvAnd {w : Nat} {n : Node} (h : isNilElem (.bvAnd w) n = true) : n.op = .bvVal w (2 ^ w - 1) := by
  simpa [isNilElem] using h

theorem isNilElem_bvOr {w : Nat} {n : Node} (h : isNilElem (.bvOr w) n = true) : n.op = .bvVal w 0 := by
  simpa [isNilElem] using h

theorem isNilElem_bvXor {w : Nat} {n : Node} (h : isNilElem (.bvXor w) n = true) : n.op = .bvVal w 0 := by
  simpa [isNilElem] using h

theorem nil_conj_val {pool : Pool} (hwf : WF pool) (ρ : Assign) :
    ∀ i n, pool[i]? = some n → isNilElem .conj n = true → eval pool ρ i = .bool true := by
  intro i n h hn
  obtain ⟨o, args⟩ := n
  have := isNilElem_conj hn; simp at this; subst this
  exact eval_lit_bool hwf h ρ

theorem nil_disj_val {pool : Pool} (hwf : WF pool) (ρ : Assign) :
    ∀ i n, pool[i]? = some n → isNilElem .disj n = true → eval pool ρ i = .bool false := by
  intro i n h hn
  obtain ⟨o, args⟩ := n
  have := isNilElem_disj hn; simp at this; subst this
  exact eval_lit_bool hwf h ρ

theorem nil_bvAnd_val {pool : Pool} (hwf : WF pool) (ρ : Assign) {w : Nat} :
    ∀ i n, pool[i]? = some n → isNilElem (.bvAnd w) n = true → eval pool ρ i = .bv w (BitVec.allOnes w) := by
  intro i n h hn
  obtain ⟨o, args⟩ := n
  have := isNilElem_bvAnd hn; simp at this; subst this
  rw [eval_lit_bv hwf h ρ, ofNat_allOnes]

theorem nil_bvOr_val {pool : Pool} (hwf : WF pool) (ρ : Assign) {w : Nat} :
    ∀ i n, pool[i]? = some n → isNilElem (.bvOr w) n = true → eval pool ρ i = .bv w 0 := by
  intro i n h hn
  obtain ⟨o, args⟩ := n
  have := isNilElem_bvOr hn; simp at this; subst this
  rw [eval_lit_bv hwf h ρ]; rfl

theorem nil_bvXor_val {pool : Pool} (hwf : WF pool) (ρ : Assign) {w : Nat} :
    ∀ i n, pool[i]? = some n → isNilElem (.bvXor w) n = true → eval pool ρ i = .bv w 0 := by
  intro i n h hn
  obtain ⟨o, args⟩ := n
  have := isNilElem_bvXor hn; simp at this; subst this
  rw [eval_lit_bv hwf h ρ]; rfl

/-- Bit-vector op node type, from `bvN_args_bv`. -/
theorem bv_node_ty {pool : Pool} (hwf : WF pool) {w i : Nat} {args : Array Nat} {op : Op}
    (h : pool[i]? = some ⟨op, args⟩) (hres : op.resultTy = bvNTy w) : typeOf pool i = some (.bv w) :=
  (bvN_args_bv hwf h hres).2.2.2

/-! ## The five instances -/

/-- The three ACI consequences for an operator (the statement of `aci_generic`). -/
def AciProp (pool : Pool) (ρ : Assign) (op : Op) : Prop :=
  (∀ (a b : Nat) (aargs bargs : Array Nat), pool[a]? = some ⟨op, aargs⟩ → pool[b]? = some ⟨op, bargs⟩ →
      aciLeaves pool op a = aciLeaves pool op b → eval pool ρ a = eval pool ρ b) ∧
  (∀ (a : Nat) (aargs : Array Nat) (x : Nat), pool[a]? = some ⟨op, aargs⟩ → aciLeaves pool op a = [x] →
      eval pool ρ a = eval pool ρ x) ∧
  (∀ (a : Nat) (aargs : Array Nat) (b : Nat) (n : Node), pool[a]? = some ⟨op, aargs⟩ → aciLeaves pool op a = [] →
      pool[b]? = some n → isNilElem op n = true → eval pool ρ a = eval pool ρ b)

section Instances
variable {pool : Pool}

theorem aci_conj (hwf : WF pool) (ρ : Assign) : AciProp pool ρ .conj := aci_generic (f := (· && ·)) (e := true)
  (by intros; simp [Bool.and_assoc]) (by intros; simp [Bool.and_comm]) (by simp)
  hwf ρ .conj (evalB pool ρ) Val.bool .bool
  rfl
  (fun _ a x => by cases a <;> cases x <;> rfl)
  (conj_node hwf ρ)
  (fun i n h hn => by have := nil_conj_val hwf ρ i n h hn; simp [evalB, this])
  (fun i h => evalB_spec h)
  (fun i args h => typeOf_conj_bool hwf h)
  (fun i args h => (boolN_args_bool' hwf h rfl).1)
  (nil_conj_val hwf ρ)

theorem aci_disj (hwf : WF pool) (ρ : Assign) : AciProp pool ρ .disj := aci_generic (f := (· || ·)) (e := false)
  (by intros; simp [Bool.or_assoc]) (by intros; simp [Bool.or_comm]) (by simp)
  hwf ρ .disj (evalB pool ρ) Val.bool .bool
  rfl
  (fun _ a x => by cases a <;> cases x <;> rfl)
  (disj_node hwf ρ)
  (fun i n h hn => by have := nil_disj_val hwf ρ i n h hn; simp [evalB, this])
  (fun i h => evalB_spec h)
  (fun i args h => typeOf_disj_bool hwf h)
  (fun i args h => (boolN_args_bool' hwf h rfl).1)
  (nil_disj_val hwf ρ)

theorem aci_bvAnd (hwf : WF pool) (ρ : Assign) (w : Nat) : AciProp pool ρ (.bvAnd w) := aci_generic (f := (· &&& ·)) (e := BitVec.allOnes w)
  (fun x y z => BitVec.and_assoc x y z) (fun x y => BitVec.and_comm x y) (fun x => BitVec.allOnes_and)
  hwf ρ (.bvAnd w) (evalV pool ρ w) (Val.bv w) (.bv w) rfl
  (fun _ a x => by rw [BitVec.and_assoc, BitVec.and_self])
  (bvop_node hwf ρ w _ _ _ rfl (fun _ => rfl))
  (fun i n h hn => by have := nil_bvAnd_val hwf ρ i n h hn; simp [evalV, this])
  (fun i h => evalV_spec h)
  (fun i args h => bv_node_ty hwf h rfl)
  (fun i args h => (bvN_args_bv hwf h rfl).1)
  (nil_bvAnd_val hwf ρ)

theorem aci_bvOr (hwf : WF pool) (ρ : Assign) (w : Nat) : AciProp pool ρ (.bvOr w) := aci_generic (f := (· ||| ·)) (e := (0 : BitVec w))
  (fun x y z => BitVec.or_assoc x y z) (fun x y => BitVec.or_comm x y) (fun x => BitVec.zero_or)
  hwf ρ (.bvOr w) (evalV pool ρ w) (Val.bv w) (.bv w) rfl
  (fun _ a x => by rw [BitVec.or_assoc, BitVec.or_self])
  (bvop_node hwf ρ w _ _ _ rfl (fun _ => rfl))
  (fun i n h hn => by have := nil_bvOr_val hwf ρ i n h hn; simp [evalV, this])
  (fun i h => evalV_spec h)
  (fun i args h => bv_node_ty hwf h rfl)
  (fun i args h => (bvN_args_bv hwf h rfl).1)
  (nil_bvOr_val hwf ρ)

theorem aci_bvXor (hwf : WF pool) (ρ : Assign) (w : Nat) : AciProp pool ρ (.bvXor w) := aci_generic (f := (· ^^^ ·)) (e := (0 : BitVec w))
  (fun x y z => BitVec.xor_assoc x y z) (fun x y => BitVec.xor_comm x y) (fun x => BitVec.zero_xor)
  hwf ρ (.bvXor w) (evalV pool ρ w) (Val.bv w) (.bv w) rfl
  (fun hi => by simp [isIdemOp] at hi)
  (bvop_node hwf ρ w _ _ _ rfl (fun _ => rfl))
  (fun i n h hn => by have := nil_bvXor_val hwf ρ i n h hn; simp [evalV, this])
  (fun i h => evalV_spec h)
  (fun i args h => bv_node_ty hwf h rfl)
  (fun i args h => (bvN_args_bv hwf h rfl).1)
  (nil_bvXor_val hwf ρ)

end Instances

/-! ## Concatenation: associative only -/

/-- Combine two concatenation results. -/
def catOpt : Option Val → Option Val → Option Val
  | some (.bv n x), some (.bv m y) => some (.bv (n + m) (x ++ y))
  | _, _ => none

theorem bv_cast_eq {w1 w2 : Nat} (h : w1 = w2) (v : BitVec w1) : Val.bv w1 v = Val.bv w2 (v.cast h) := by
  subst h; simp

theorem concatVals_cons_ne {v : Val} {l : List Val} (hl : l ≠ []) :
    Val.concatVals (v :: l) = catOpt (some v) (Val.concatVals l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b rest =>
    cases v with
    | bv n x =>
      rw [Val.concatVals.eq_def]
      simp only
      cases Val.concatVals (b :: rest) with
      | none => rfl
      | some u => cases u <;> rfl
    | bool _ => rw [Val.concatVals.eq_def]; simp only; cases Val.concatVals (b :: rest) with
      | none => rfl
      | some u => cases u <;> rfl
    | list _ _ => rw [Val.concatVals.eq_def]; simp only; cases Val.concatVals (b :: rest) with
      | none => rfl
      | some u => cases u <;> rfl
    | bad => rw [Val.concatVals.eq_def]; simp only; cases Val.concatVals (b :: rest) with
      | none => rfl
      | some u => cases u <;> rfl

theorem catOpt_assoc (x y z : Option Val) : catOpt (catOpt x y) z = catOpt x (catOpt y z) := by
  cases x with
  | none => cases y <;> cases z <;> simp [catOpt]
  | some u =>
    cases u with
    | bv n a =>
      cases y with
      | none => cases z <;> simp [catOpt]
      | some v =>
        cases v with
        | bv m b =>
          cases z with
          | none => simp [catOpt]
          | some t =>
            cases t with
            | bv k c =>
              simp only [catOpt]
              rw [bv_cast_eq (Nat.add_assoc n m k).symm, BitVec.append_assoc]
            | bool _ => simp [catOpt]
            | list _ _ => simp [catOpt]
            | bad => simp [catOpt]
        | bool _ => cases z <;> simp [catOpt]
        | list _ _ => cases z <;> simp [catOpt]
        | bad => cases z <;> simp [catOpt]
    | bool _ => cases y <;> cases z <;> simp [catOpt]
    | list _ _ => cases y <;> cases z <;> simp [catOpt]
    | bad => cases y <;> cases z <;> simp [catOpt]

theorem concatVals_singleton_bv {v : Val} {n : Nat} {x : BitVec n} (h : v = .bv n x) :
    Val.concatVals [v] = some v := by
  subst h; rfl

theorem concatVals_append {l1 l2 : List Val} (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    Val.concatVals (l1 ++ l2) = catOpt (Val.concatVals l1) (Val.concatVals l2) := by
  induction l1 with
  | nil => exact absurd rfl h1
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [List.singleton_append]
      rw [concatVals_cons_ne h2]
      cases a with
      | bv n x => rfl
      | bool _ => simp [Val.concatVals, catOpt]
      | list _ _ => simp [Val.concatVals, catOpt]
      | bad => simp [Val.concatVals, catOpt]
    | cons b rest' =>
      rw [List.cons_append, concatVals_cons_ne (l := b :: rest' ++ l2) (by simp), ih (by simp),
          concatVals_cons_ne (l := b :: rest') (by simp), catOpt_assoc]

/-- Concatenation over a flattening: the generic step. -/
theorem concatVals_flatMap {ev : Nat → Val} {cl : Nat → List Nat} :
    ∀ (l : List Nat), l ≠ [] →
      (∀ a ∈ l, some (ev a) = Val.concatVals ((cl a).map ev) ∧ cl a ≠ []) →
      Val.concatVals (l.map ev) = Val.concatVals ((l.flatMap cl).map ev) ∧ l.flatMap cl ≠ [] := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _ key
    obtain ⟨ka, kna⟩ := key a (by simp)
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine ⟨?_, kna⟩
      obtain ⟨n, x, hx⟩ := Val.concatVals_isBv ka.symm
      rw [concatVals_singleton_bv hx, ka]
    | cons b rest' =>
      obtain ⟨ih1, ih2⟩ := ih (by simp) (fun a' ha' => key a' (by simp [ha']))
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, List.flatMap_cons, List.map_append]
        rw [concatVals_cons_ne (l := (b :: rest').map ev) (by simp),
            concatVals_append (by simpa using kna) (by simpa using ih2), ka, ih1]
      · simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff]
        intro hh; exact kna hh.1

theorem concat_args {pool : Pool} (hwf : WF pool) {w i : Nat} {args : Array Nat}
    (h : pool[i]? = some ⟨.bvConcat w, args⟩) :
    (∀ a ∈ args, ∃ n, typeOf pool a = some (.bv n)) ∧ 2 ≤ args.size ∧ typeOf pool i = some (.bv w) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i _ h).2
  have h2 := ht
  rw [typeOf_node hwf h] at h2
  cases hm : mapOpt (typeOf pool) args.toList with
  | none => rw [hm] at h2; simp at h2
  | some tys =>
    rw [hm] at h2
    simp only [Option.bind_some, Op.resultTy, bvConcatTy, tyGuard] at h2
    split at h2
    · rename_i hc
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨y, hy, hfy⟩ := mapOpt_mem hm (by simpa using ha)
        -- every type in a list with a defined width sum is a bit-vector
        have : ∀ (ts : List Ty) (n : Nat), bvWidths ts = some n → ∀ t ∈ ts, ∃ k, t = .bv k := by
          intro ts
          induction ts with
          | nil => simp
          | cons t rest ih =>
            intro n hn t' ht'
            cases t with
            | bv k =>
              simp at ht'
              rcases ht' with rfl | ht'
              · exact ⟨k, rfl⟩
              · cases rest with
                | nil => simp at ht'
                | cons u us =>
                  simp only [bvWidths] at hn
                  cases hu : bvWidths (u :: us) with
                  | none => rw [hu] at hn; simp at hn
                  | some m => exact ih m hu t' ht'
            | bool => simp [bvWidths] at hn
            | list _ _ => simp [bvWidths] at hn
        obtain ⟨k, hk⟩ := this tys w hc.2.1 y hy
        exact ⟨k, by rw [hfy, hk]⟩
      · have := mapOpt_length hm; simp at this; have := hc.2.2; omega
      · rw [ht]; simp at h2; rw [h2]
    · simp at h2

/-- A well-typed concatenation is the concatenation of its arguments' values. -/
theorem concat_node {pool : Pool} (hwf : WF pool) (ρ : Assign) {w i : Nat} {args : Array Nat}
    (h : pool[i]? = some ⟨.bvConcat w, args⟩) :
    some (eval pool ρ i) = Val.concatVals (args.toList.map (eval pool ρ)) := by
  obtain ⟨hargs, hlen, hty⟩ := concat_args hwf h
  have hv := eval_node hwf ρ h
  simp only [Op.eval, bvConcatEval] at hv
  have key := Val.concatVals_ty (args.toList.map (eval pool ρ))
  cases hc : Val.concatVals (args.toList.map (eval pool ρ)) with
  | none =>
    -- impossible: the node is typed
    exfalso
    rw [hc] at key hv
    simp at hv
    have := eval_ty pool ρ i; rw [hv, hty] at this; simp at this
  | some v =>
    obtain ⟨n, x, rfl⟩ := Val.concatVals_isBv hc
    rw [hc] at hv
    simp only at hv
    split at hv
    · rename_i hcond
      obtain ⟨_, rfl, _⟩ := hcond
      rw [hv]; simp
    · exfalso
      have := eval_ty pool ρ i; rw [hv, hty] at this; simp at this

theorem concat_leaves {pool : Pool} (hwf : WF pool) (ρ : Assign) (w : Nat) :
    ∀ i (w' : Nat) (args : Array Nat), pool[i]? = some ⟨.bvConcat w', args⟩ →
      some (eval pool ρ i) = Val.concatVals ((flatten pool (.bvConcat w) i).map (eval pool ρ)) ∧
      flatten pool (.bvConcat w) i ≠ [] := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro w' args h
    rw [concat_node hwf ρ h, flatten_node' h (by simp [sameAssoc_concat, isConcatOp])]
    obtain ⟨hargs, hlen, _⟩ := concat_args hwf h
    have hlt := (hwf i _ h).1
    have key : ∀ a ∈ args.toList, some (eval pool ρ a) = Val.concatVals ((childLeaves pool (.bvConcat w) i a).map (eval pool ρ)) ∧
        childLeaves pool (.bvConcat w) i a ≠ [] := by
      intro a ha
      have ha' : a < i := hlt a (by simpa using ha)
      unfold childLeaves
      simp only [ha', ite_true]
      obtain ⟨m, hm⟩ := node_of_lt (Nat.lt_trans ha' (idx_lt_of_get h))
      by_cases hop : isConcatOp m.op = true
      · obtain ⟨o, margs⟩ := m
        obtain ⟨w'', hw⟩ := (isConcatOp_iff o).mp hop
        subst hw
        exact ih a ha' w'' margs hm
      · rw [flatten_leaf hm (by rw [sameAssoc_concat]; simpa using hop)]
        have hnil : isNilElem (.bvConcat w) m = false := by simp [isNilElem]
        simp only [hnil, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil]
        obtain ⟨n, hn⟩ := hargs a (by simpa using ha)
        obtain ⟨x, hx⟩ := eval_bv (ρ := ρ) hn
        exact ⟨by rw [hx]; rfl, by simp⟩
    have hne : args.toList ≠ [] := by
      intro hh
      have h0 : args.toList.length = 0 := by rw [hh]; rfl
      simp only [Array.length_toList] at h0; omega
    exact concatVals_flatMap args.toList hne key

theorem aci_concat {pool : Pool} (hwf : WF pool) (ρ : Assign) (w : Nat) :
    (∀ (a b : Nat) (aargs bargs : Array Nat), pool[a]? = some ⟨.bvConcat w, aargs⟩ → pool[b]? = some ⟨.bvConcat w, bargs⟩ →
        aciLeaves pool (.bvConcat w) a = aciLeaves pool (.bvConcat w) b → eval pool ρ a = eval pool ρ b) ∧
    (∀ (a : Nat) (aargs : Array Nat) (x : Nat), pool[a]? = some ⟨.bvConcat w, aargs⟩ → aciLeaves pool (.bvConcat w) a = [x] →
        eval pool ρ a = eval pool ρ x) ∧
    (∀ (a : Nat) (aargs : Array Nat) (b : Nat) (n : Node), pool[a]? = some ⟨.bvConcat w, aargs⟩ → aciLeaves pool (.bvConcat w) a = [] →
        pool[b]? = some n → isNilElem (.bvConcat w) n = true → eval pool ρ a = eval pool ρ b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b aargs bargs ha hb heq
    simp only [aciLeaves, isConcatOp, ite_true] at heq
    have h1 := (concat_leaves hwf ρ w a w aargs ha).1
    have h2 := (concat_leaves hwf ρ w b w bargs hb).1
    rw [heq] at h1; rw [← h1] at h2; simpa using h2.symm
  · intro a aargs x ha hl
    simp only [aciLeaves, isConcatOp, ite_true] at hl
    have h1 := (concat_leaves hwf ρ w a w aargs ha).1
    rw [hl] at h1
    simp only [List.map_cons, List.map_nil] at h1
    -- concatVals of a singleton is the element when it is a bit-vector
    cases hx : eval pool ρ x <;> rw [hx] at h1 <;> simp [Val.concatVals] at h1
    rw [h1]
  · intro a aargs b n ha hl hb hn
    simp [isNilElem] at hn

/-- The three ACI consequences for any assoc operator. -/
theorem aci_all {pool : Pool} (hwf : WF pool) (ρ : Assign) {op : Op} (hop : isAssocOp op = true) :
    (∀ (a b : Nat) (aargs bargs : Array Nat), pool[a]? = some ⟨op, aargs⟩ → pool[b]? = some ⟨op, bargs⟩ →
        aciLeaves pool op a = aciLeaves pool op b → eval pool ρ a = eval pool ρ b) ∧
    (∀ (a : Nat) (aargs : Array Nat) (x : Nat), pool[a]? = some ⟨op, aargs⟩ → aciLeaves pool op a = [x] →
        eval pool ρ a = eval pool ρ x) ∧
    (∀ (a : Nat) (aargs : Array Nat) (b : Nat) (n : Node), pool[a]? = some ⟨op, aargs⟩ → aciLeaves pool op a = [] →
        pool[b]? = some n → isNilElem op n = true → eval pool ρ a = eval pool ρ b) := by
  cases op <;> simp [isAssocOp] at hop
  · exact aci_bvOr hwf ρ _
  · exact aci_bvAnd hwf ρ _
  · exact aci_bvXor hwf ρ _
  · exact aci_concat hwf ρ _
  · exact aci_conj hwf ρ
  · exact aci_disj hwf ρ

/-! ## ABSORB -/

theorem absorbF_stable (pool : Pool) (op : Op) (i : Nat) :
    ∀ f f', i < f → i < f' → absorbF pool op f i = absorbF pool op f' i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f f' hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [absorbF]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      have hfun : (fun a => decide (a < i) && absorbF pool op g a) =
                  (fun a => decide (a < i) && absorbF pool op g' a) := by
        funext a
        by_cases ha : a < i
        · simp only [ha, decide_true, Bool.true_and]; exact ih a ha g g' (by omega) (by omega)
        · simp [ha]
      rw [hfun]

theorem foldl_and_zero {w : Nat} {xs : List (BitVec w)} (h : 0 ∈ xs) (a : BitVec w) :
    xs.foldl (· &&& ·) a = 0 := by
  induction xs generalizing a with
  | nil => simp at h
  | cons x rest ih =>
    simp only [List.foldl_cons]
    simp at h
    rcases h with rfl | h
    · rw [BitVec.and_zero]
      clear ih
      induction rest with
      | nil => rfl
      | cons y r ih' => simp only [List.foldl_cons, BitVec.zero_and]; exact ih'
    · exact ih h _

theorem foldl_or_allOnes {w : Nat} {xs : List (BitVec w)} (h : BitVec.allOnes w ∈ xs) (a : BitVec w) :
    xs.foldl (· ||| ·) a = BitVec.allOnes w := by
  induction xs generalizing a with
  | nil => simp at h
  | cons x rest ih =>
    simp only [List.foldl_cons]
    simp at h
    rcases h with rfl | h
    · rw [BitVec.or_allOnes]
      clear ih
      induction rest with
      | nil => rfl
      | cons y r ih' => simp only [List.foldl_cons, BitVec.allOnes_or]; exact ih'
    · exact ih h _

/-- The absorbing value denoted by `isZeroElem`. -/
def zeroVal : Op → Val
  | .disj => .bool true
  | .conj => .bool false
  | .bvAnd w => .bv w 0
  | .bvOr w => .bv w (BitVec.allOnes w)
  | _ => .bad

theorem isZeroElem_cases {op : Op} {n : Node} (h : isZeroElem op n = true) :
    (op = .disj ∧ n.op = .boolVal true) ∨ (op = .conj ∧ n.op = .boolVal false) ∨
    (∃ w, op = .bvAnd w ∧ n.op = .bvVal w 0) ∨ (∃ w, op = .bvOr w ∧ n.op = .bvVal w (2 ^ w - 1)) := by
  cases op <;> simp [isZeroElem] at h
  · exact Or.inr (Or.inr (Or.inr ⟨_, rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl, h⟩))
  · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · exact Or.inl ⟨rfl, h⟩

theorem isZeroElem_eval {pool : Pool} (hwf : WF pool) (ρ : Assign) {op : Op} {i : Nat} {n : Node}
    (h : pool[i]? = some n) (hz : isZeroElem op n = true) : eval pool ρ i = zeroVal op := by
  obtain ⟨o, args⟩ := n
  rcases isZeroElem_cases hz with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨w, rfl, ho⟩ | ⟨w, rfl, ho⟩ <;> simp at ho <;> subst ho
  · exact eval_lit_bool hwf h ρ
  · exact eval_lit_bool hwf h ρ
  · rw [eval_lit_bv hwf h ρ]; rfl
  · rw [eval_lit_bv hwf h ρ, ofNat_allOnes]; rfl

theorem absorb_eval {pool : Pool} (hwf : WF pool) (ρ : Assign) (op : Op) :
    ∀ i, absorbF pool op (i + 1) i = true → eval pool ρ i = zeroVal op := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro h
    simp only [absorbF] at h
    cases hn : pool[i]? with
    | none => rw [hn] at h; simp at h
    | some n =>
      rw [hn] at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Array.any_eq_true'] at h
      rcases h with hz | ⟨hop, a, ha, hlt, hrec⟩
      · exact isZeroElem_eval hwf ρ hn hz
      · simp only [decide_eq_true_eq] at hlt
        have hrec' : absorbF pool op (a + 1) a = true := by
          rw [absorbF_stable pool op a _ _ (by omega) hlt]; exact hrec
        have hva := ih a hlt hrec'
        obtain ⟨o, args⟩ := n
        simp only at hop; subst o
        cases op
        case disj =>
          obtain ⟨hargs, hlen⟩ := boolN_args_bool' hwf hn rfl
          simp only [zeroVal] at hva ⊢
          exact holds_disj_intro hwf hn ρ hlen ⟨a, ha, hva⟩
        case conj =>
          obtain ⟨hargs, hlen⟩ := boolN_args_bool' hwf hn rfl
          have hb := bools_map_evalB (ρ := ρ) (l := args.toList) (fun a ha => hargs a (by simpa using ha))
          rw [eval_node hwf ρ hn]
          simp only [Op.eval, boolN, hb, List.length_map, Array.length_toList]
          rw [ite_eq_left hlen]
          simp only [zeroVal]
          congr 1
          simp only [List.all_eq_false, List.mem_map]
          exact ⟨evalB pool ρ a, ⟨a, by simpa using ha, rfl⟩, by simp [evalB, hva, zeroVal]⟩
        case bvAnd w =>
          obtain ⟨hargs, hlen, hw, _⟩ := bvN_args_bv hwf hn rfl
          have hb := bvs_map_evalV (ρ := ρ) (w := w) (l := args.toList) (fun a ha => hargs a (by simpa using ha))
          rw [eval_node hwf ρ hn]
          simp only [Op.eval, bvN, hb, List.length_map, Array.length_toList]
          rw [ite_eq_left ⟨hw, hlen⟩]
          simp only [zeroVal]
          congr 1
          apply foldl_and_zero
          refine List.mem_map.mpr ⟨a, by simpa using ha, ?_⟩
          simp [evalV, hva, zeroVal]
        case bvOr w =>
          obtain ⟨hargs, hlen, hw, _⟩ := bvN_args_bv hwf hn rfl
          have hb := bvs_map_evalV (ρ := ρ) (w := w) (l := args.toList) (fun a ha => hargs a (by simpa using ha))
          rw [eval_node hwf ρ hn]
          simp only [Op.eval, bvN, hb, List.length_map, Array.length_toList]
          rw [ite_eq_left ⟨hw, hlen⟩]
          simp only [zeroVal]
          congr 1
          apply foldl_or_allOnes
          refine List.mem_map.mpr ⟨a, by simpa using ha, ?_⟩
          simp [evalV, hva, zeroVal]
        all_goals
          exfalso
          obtain ⟨ma, hma⟩ := node_of_lt (Nat.lt_trans hlt (idx_lt_of_get hn))
          have hty := (hwf a ma hma).2
          rw [← eval_ty (ρ := ρ), hva] at hty
          simp [zeroVal] at hty

theorem ruleAbsorb_sound {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat} {ei : EI}
    {prems params : List Nat} (h : ruleAbsorb ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleAbsorb at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i r z hrz
        split at h
        · rename_i rn zn hr hz
          split at h
          · rename_i hc
            simp at h; obtain ⟨rfl, rfl⟩ := h
            have hen := node_bind_eq hrz
            rw [St.node] at hr hz
            refine ⟨hinv, idx_lt_of_get hen, ?_⟩
            intro ρ _
            rw [holds_eq_node hinv.wf hen ρ]
            have hvr := absorb_eval hinv.wf ρ rn.op r hc.2
            have hvz := isZeroElem_eval hinv.wf ρ hz hc.1
            refine ⟨by rw [hvr, hvz], ?_⟩
            rw [hvr]
            rcases isZeroElem_cases hc.1 with ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨w, ho, _⟩ | ⟨w, ho, _⟩ <;> rw [ho] <;>
              exact ⟨_, rfl, rfl⟩
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-! ## ACI_NORM -/

theorem aciNF_some {pool : Pool} {i : Nat} {op : Op} {l : List Nat} (h : aciNF pool i = some (op, l)) :
    ∃ args, pool[i]? = some ⟨op, args⟩ ∧ isAssocOp op = true ∧ l = aciLeaves pool op i := by
  unfold aciNF at h
  split at h
  · rename_i n hn
    split at h
    · rename_i hop
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨n.args, hn, hop, rfl⟩
    · simp at h
  · simp at h

theorem aciReduces_eval {st : St} (hwf : WF st.pool) (ρ : Assign) {a b : Nat}
    (h : aciReduces st a b = true) : eval st.pool ρ a = eval st.pool ρ b := by
  unfold aciReduces at h
  split at h
  · rename_i op x hna
    simp at h; subst h
    obtain ⟨args, ha, hop, hl⟩ := aciNF_some hna
    exact (aci_all hwf ρ hop).2.1 a args _ ha hl.symm
  · rename_i op hna
    split at h
    · rename_i bn hbn
      obtain ⟨args, ha, hop, hl⟩ := aciNF_some hna
      rw [St.node] at hbn
      exact (aci_all hwf ρ hop).2.2 a args b bn ha hl.symm hbn h
    · simp at h
  · simp at h

theorem aciEq_eval {st : St} (hwf : WF st.pool) (ρ : Assign) {a b : Nat} (h : aciEq st a b = true) :
    eval st.pool ρ a = eval st.pool ρ b := by
  unfold aciEq at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · subst h; rfl
  · split at h
    · rename_i op la op' lb hna hnb
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hl⟩ := h
      obtain ⟨aargs, ha, hop, hla⟩ := aciNF_some hna
      obtain ⟨bargs, hb, _, hlb⟩ := aciNF_some hnb
      exact (aci_all hwf ρ hop).1 a b aargs bargs ha hb (by rw [← hla, ← hlb]; exact hl)
    · simp at h
  · exact aciReduces_eval hwf ρ h
  · exact (aciReduces_eval hwf ρ h).symm

theorem ruleAciNorm_sound {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat} {ei : EI}
    {prems params : List Nat} (h : ruleAciNorm ei st prems params = some (st', f))
    (hinv : Inv base g bi st) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleAciNorm at h
  split at h
  · rename_i pe
    split at h
    · rename_i e _
      split at h
      · rename_i a b hab
        split at h
        · rename_i hc
          simp at h; obtain ⟨rfl, rfl⟩ := h
          have hen := node_bind_eq hab
          refine ⟨hinv, idx_lt_of_get hen, ?_⟩
          intro ρ _
          rw [holds_eq_node hinv.wf hen ρ]
          refine ⟨aciEq_eval hinv.wf ρ hc, ?_⟩
          -- the equation node type-checks, so its sides are scalars
          have h2 := (hinv.wf e _ hen).2
          rw [typeOf_node hinv.wf hen] at h2
          simp only [mapOpt] at h2
          cases hta : typeOf st.pool a <;> rw [hta] at h2 <;> cases htb : typeOf st.pool b <;> rw [htb] at h2 <;>
            simp [Op.resultTy, eqTy, tyGuard] at h2
          rename_i ta tb
          refine ⟨ta, ?_, h2.2⟩
          rw [eval_ty, hta]
        · simp at h
      · simp at h
    · simp at h
  · simp at h

end Bcf
