import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Aci3

/-!
# Vbcf proofs: the Aci family, part 4 — `aci_sort`

`aci_sort` is an insertion sort of `stk[base..sp)` by id.  Ids need not compare like
indices (a node resurrected after a compaction gets a new, larger id), so the result is
a permutation of the index list sorted by id (`st.id`); the callers compare such lists
through `aciEq`, which only needs them up to permutation.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Lean side -/

/-- A sorted permutation is `sortNat`. -/
theorem aci_sorted_eq {P M : List Nat} (hs : P.Pairwise (· ≤ ·)) (hp : P.Perm M) :
    P = sortNat M := by
  have h2 : (sortNat M).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) M
    exact this.imp (fun h => by simpa using h)
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) hs h2
  exact hp.trans (sortNat_perm M).symm

theorem aci_mem_take {P : List Nat} {m a : Nat} (ha : a ∈ P.take m) :
    ∃ t, ∃ h : t < P.length, t < m ∧ P[t] = a := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  simp only [List.length_take] at ht
  exact ⟨t, by omega, by omega, by simp [List.getElem_take]⟩

theorem aci_mem_drop {P : List Nat} {m a : Nat} (ha : a ∈ P.drop m) :
    ∃ t, ∃ h : t < P.length, m ≤ t ∧ P[t] = a := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  simp only [List.length_drop] at ht
  exact ⟨m + t, by omega, by omega, by simp [List.getElem_drop]⟩

theorem aci_sorted_le {P : List Nat} (hs : P.Pairwise (· ≤ ·)) {i j : Nat} (hi : i < P.length)
    (hj : j < P.length) (hij : i ≤ j) : P[i] ≤ P[j] := by
  rcases Nat.lt_or_ge i j with h | h
  · exact List.pairwise_iff_getElem.mp hs i j hi hj h
  · have : i = j := by omega
    subst this; exact Nat.le_refl _

/-- `aci_sorted_le` for a list sorted by a key `f`. -/
theorem aci_sorted_le_by {f : Nat → Nat} {P : List Nat} (hs : P.Pairwise (fun a b => f a ≤ f b))
    {i j : Nat} (hi : i < P.length) (hj : j < P.length) (hij : i ≤ j) : f P[i] ≤ f P[j] := by
  rcases Nat.lt_or_ge i j with h | h
  · exact List.pairwise_iff_getElem.mp hs i j hi hj h
  · have : i = j := by omega
    subst this; exact Nat.le_refl _

/-- Inserting `x` at its place keeps a list sorted by the key `f`. -/
theorem aci_insert_sorted {f : Nat → Nat} {P : List Nat} {m x : Nat}
    (hs : P.Pairwise (fun a b => f a ≤ f b)) (hm : m ≤ P.length)
    (hlo : ∀ h : 0 < m, f (P[m - 1]'(by omega)) ≤ f x)
    (hhi : ∀ t (h : t < P.length), m ≤ t → f x < f P[t]) :
    (P.take m ++ x :: P.drop m).Pairwise (fun a b => f a ≤ f b) := by
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hs.sublist (List.take_sublist _ _), ⟨fun b hb => ?_, hs.sublist (List.drop_sublist _ _)⟩,
    fun a ha b hb => ?_⟩
  · obtain ⟨t, ht, hmt, rfl⟩ := aci_mem_drop hb
    exact Nat.le_of_lt (hhi t ht hmt)
  · obtain ⟨t, ht, htm, rfl⟩ := aci_mem_take ha
    have h1 : f P[t] ≤ f x :=
      Nat.le_trans (aci_sorted_le_by hs ht (by omega) (by omega)) (hlo (by omega))
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1
    · obtain ⟨t', ht', hmt', rfl⟩ := aci_mem_drop hb
      exact aci_sorted_le_by hs ht ht' (by omega)

theorem aci_insert_perm {P M : List Nat} {m k : Nat} (hp : P.Perm (M.take k)) (hk : k < M.length) :
    (P.take m ++ M[k] :: P.drop m).Perm (M.take (k + 1)) := by
  rw [List.take_succ_eq_append_getElem hk]
  refine List.perm_middle.trans ?_
  rw [List.take_append_drop]
  exact (List.Perm.cons _ hp).trans (List.perm_append_singleton _ _).symm

theorem aci_shift_list {P : List Nat} {m : Nat} (h1 : 0 < m) (h2 : m ≤ P.length) :
    P.take m ++ P[m - 1] :: P.drop m = P.take (m - 1) ++ P[m - 1] :: P.drop (m - 1) := by
  have e1 : P.take m = P.take (m - 1) ++ [P[m - 1]] := by
    have := List.take_succ_eq_append_getElem (l := P) (i := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  have e2 : P.drop (m - 1) = P[m - 1] :: P.drop m := by
    rw [List.drop_eq_getElem_cons (by omega)]
    congr 2; omega
  rw [e1, e2, List.append_assoc]; rfl

theorem aci_hole_get {A P R : List Nat} {m hv : Nat} (h1 : 0 < m) (h2 : m ≤ P.length) :
    (A ++ (P.take m ++ hv :: P.drop m) ++ R)[A.length + (m - 1)]'(by simp; omega) = P[m - 1] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp),
    List.getElem_append_left (by simp; omega)]
  simp [List.getElem_take]

theorem aci_hole_set {A P R : List Nat} {m hv y : Nat} (h2 : m ≤ P.length) :
    (A ++ (P.take m ++ hv :: P.drop m) ++ R).set (A.length + m) y =
      A ++ (P.take m ++ y :: P.drop m) ++ R := by
  rw [List.append_assoc, List.set_append_right _ _ (by omega), List.append_assoc,
    List.set_append_right _ _ (by simp; omega)]
  simp [Nat.min_eq_left h2]

theorem aci_get_mid {A P M : List Nat} {k : Nat} (hP : P.length = k) (hk : k < M.length) :
    (A ++ P ++ M.drop k)[A.length + k]'(by simp; omega) = M[k] := by
  rw [List.getElem_append_right (by simp; omega)]
  simp [hP]

/-! ## The stack -/

/-- A store into the list on the stack. -/
theorem StkTop.aci_set {c : CMem} {st : VSt} {base : Nat} {L : List Nat} (ht : StkTop c st base L)
    {p : Nat} (hp : p < L.length) {y : Nat} (hy : st.lv y) :
    StkTop { c with stk := c.stk.setIfInBounds (base + p) (uv (st.id y)) } st base (L.set p y) := by
  refine ⟨by simp [ht.1], fun j i hj => ?_⟩
  have hjl : j < L.length := by have := lt_length_of_getElem? hj; simpa using this
  have hin : base + p < c.stk.size := by
    have := (ht.2 p L[p] (List.getElem?_eq_getElem hp)).2
    unfold U at this
    exact lt_size_of_getElem? this
  rw [List.getElem?_eq_getElem (by simpa using hjl), List.getElem_set] at hj
  simp only [Option.some.injEq] at hj
  unfold U
  by_cases e : p = j
  · subst e
    rw [ite_eq_left rfl] at hj
    subst hj
    exact ⟨hy, by simp [Array.getElem?_setIfInBounds_self_of_lt hin]⟩
  · rw [ite_eq_right e] at hj
    subst hj
    obtain ⟨hi, hU⟩ := ht.2 j L[j] (List.getElem?_eq_getElem hjl)
    exact ⟨hi, by simp only; rw [Array.getElem?_setIfInBounds_ne (by omega)]; exact hU⟩

/-- Comparing id words compares ids. -/
theorem VInv.aci_id_lt {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {a b : Nat} (ha : st.lv a) (hb : st.lv b) :
    (BitVec.ofNat 32 (st.id a) < BitVec.ofNat 32 (st.id b)) ↔ st.id a < st.id b := by
  have h1 := hc.off_lt ha
  have h2 := hc.off_lt hb
  rw [uv_lt (by omega) (by omega)]

/-- The cell of a list on the stack. -/
theorem StkTop.aci_rd {c : CMem} {st : VSt} {base : Nat} {L : List Nat} (ht : StkTop c st base L)
    {j : Nat} (hj : j < L.length) : rd c.stk (base + j) = some (uv (st.id L[j])) :=
  rd_u32 (ht.cell hj)

/-- `while (cond) body` as the last statement, with invariant `I`. -/
theorem WP.aci_loop {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {cond : Expr} {body : Stmt}
    (I : Env → (KernelState P State) → Prop) (h0 : I env s)
    (hstep : ∀ env s, I env s →
      match evalE P env s.mem cond with
      | some (.u32 v) => (v = 0 → Q .normal env s) ∧ (v ≠ 0 → WP P body (LoopQ I Q) env s)
      | _ => False) :
    WP P (.while cond body) Q env s := by
  apply WP.while I h0
  intro env s hI
  have H := hstep env s hI
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨H.1, fun hne => WP.mono (H.2 hne) ?_⟩
    intro o env' s' hq
    cases o with
    | normal => exact hq
    | brk => exact hq.elim
    | ret r => exact hq
  · exact H.elim

section stmts
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)}

/-- `st->stk[i] = e;` where `i` is the cell of position `p` of a list on the stack and `e`
the id of node `y`. -/
theorem WP.aci_stk_store {i e : Expr} {base : Nat} {L : List Nat} {p y : Nat}
    (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (ht : StkTop c st base L)
    (hp : p < L.length) (hy : st.lv y) (henv : env.get "st" = some (.ptr sb 0))
    (hidx : evalE Vbcf.prog env s.mem i = some (uv (base + p)))
    (hval : evalE Vbcf.prog env s.mem e = some (uv (st.id y)))
    (H : ∀ s' c', Holds W s'.mem sb c' → RCtx W X c0 prems params c' st →
      StkTop c' st base (L.set p y) → Q .normal env s') :
    WP Vbcf.prog (.store (.field (.var "st") "stk") i e) Q env s := by
  have hs := prog_ck
  have hsp := ht.1
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hstk := hR.stk_eq h (by omega)
  have hsz := hR.stk_size h (by omega)
  apply WP.ck_store .stk h rfl hstk
  simp only [evalE, henv, hidx, hval, ↓reduceIte, HasCK.ld_stk hs h.ck, hstk, Ptr.val, Val.toIdx,
    CMem.arr]
  refine ⟨trivial, ?_⟩
  rw [uv_toNat (by omega)]
  refine ⟨by simp; omega, fun s' h' => H s' _ h' (hR.set_stk _ _) ?_⟩
  simpa [CMem.setArr] using ht.aci_set hp hy

end stmts

/-! ## `aci_sort` -/

def AciSortSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (A M : List Nat),
    FnSpec (State := State) Vbcf.prog "aci_sort"
      (fun vs s => vs = [.ptr sb 0, uv (base + A.length)] ∧ Holds W s.mem sb c ∧
        RCtx W X c0 prems params c st ∧ StkTop c st base (A ++ M))
      (fun _ _ _ s' => ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
        ∃ M', M'.Perm M ∧ M'.Pairwise (fun a b => st.id a ≤ st.id b) ∧ StkTop c' st base (A ++ M'))

/-- Outer loop of `aci_sort`: the first `k` elements are sorted. -/
def AciSortInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (A M : List Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (P : List Nat) (jv xv : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, uv (base + A.length)),
      ("i", .u32, uv (base + A.length + k)), ("j", .u32, .u32 jv), ("x", .u32, .u32 xv)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ 1 ≤ k ∧ (k ≤ M.length ∨ (M = [] ∧ k = 1)) ∧
    P.length = min k M.length ∧ P.Pairwise (fun a b => st.id a ≤ st.id b) ∧ P.Perm (M.take k) ∧
    StkTop c' st base (A ++ P ++ M.drop k)

/-- Inner loop of `aci_sort`: the elements of `P` from position `m` on have moved up by one;
the cell at `m` holds some `hv`. -/
def AciSortInner (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (A M : List Nat) (k : Nat) (P : List Nat) (hk : k < M.length) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (m hv : Nat),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, uv (base + A.length)),
      ("i", .u32, uv (base + A.length + k)), ("j", .u32, uv (base + A.length + m)),
      ("x", .u32, uv (st.id M[k]))] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧ m ≤ k ∧ st.lv hv ∧
    StkTop c' st base (A ++ (P.take m ++ hv :: P.drop m) ++ M.drop (k + 1)) ∧
    ∀ t (ht : t < P.length), m ≤ t → st.id M[k] < st.id P[t]

theorem aci_sort_spec : AciSortSpec (State := State) := by
  intro W sb X c0 c prems params st base A M
  have hs := prog_ck
  apply FnSpec.intro' (fn := aciSort) rfl
  rintro vs s ⟨rfl, h, hR, htop⟩
  simp [aciSort, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hspmax := hR.sp_lt
  simp only [maxPool] at hspmax
  have hsp1 := htop.1
  simp only [List.length_append] at hsp1
  have hspw : c.k.sp = BitVec.ofNat 32 (base + A.length + M.length) := by
    rw [← bv_ofNat_toNat c.k.sp, hsp1]; congr 1; omega
  rule_assign
  apply WP.aci_loop (AciSortInv W sb X c0 prems params st base A M)
  · refine ⟨c, 1, M.take 1, 0#32, 0#32, by simp, h, hR, by omega, ?_, by simp, ?_, by simp, ?_⟩
    · rcases M with _ | ⟨a, M⟩ <;> simp
    · rcases M with _ | ⟨a, M⟩ <;> simp
    · rw [List.append_assoc, List.take_append_drop]; exact htop
  clear h hR htop
  rintro env s' ⟨c', k, P, jv, xv, rfl, h, hR, hk1, hkM, hPl, hPs, hPp, htop⟩
  have hsp2 := htop.1
  simp only [List.length_append, List.length_drop] at hsp2
  have hPl2 : (k ≤ M.length ∧ P.length = k) ∨ (M.length = 0 ∧ k = 1 ∧ P.length = 0) := by
    rcases hkM with e | ⟨e, rfl⟩
    · left; rw [Nat.min_eq_left e] at hPl; exact ⟨e, hPl⟩
    · right; subst e; simp at hPl; simp [hPl]
  clear hPl hkM
  have hspmax2 := hR.sp_lt
  simp only [maxPool] at hspmax2
  have hkb : base + A.length + k < 4294967296 := by omega
  have hspw2 : c'.k.sp = BitVec.ofNat 32 (base + A.length + M.length) := by
    rw [← bv_ofNat_toNat c'.k.sp, hsp2]; congr 1; omega
  rule_simp [hspw2]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkM' : M.length ≤ k := by omega
    refine ⟨c', h, hR, ?_⟩
    rw [List.take_of_length_le hkM'] at hPp
    rw [List.drop_of_length_le hkM', List.append_nil] at htop
    exact ⟨P, hPp, hPs, htop⟩
  have hkM' : k < M.length := by omega
  have hPk : P.length = k := by omega
  have hstk := hR.stk_eq h (by omega)
  have hx := hR.core.ok
  have hMk : st.lv M[k] := by
    have := htop.lt_size (j := A.length + k) (by simp; omega)
    rwa [aci_get_mid hPk hkM'] at this
  have hcx : rd c'.stk (base + A.length + k) = some (uv (st.id M[k])) := by
    have := htop.aci_rd (j := A.length + k) (by simp; omega)
    rwa [aci_get_mid hPk hkM', ← Nat.add_assoc] at this
  rule_assign [hstk, hcx]
  rule_assign
  apply WP.loop_seq (AciSortInner W sb X c0 prems params st base A M k P hkM')
  · refine ⟨c', k, M[k], rfl, h, hR, by omega, hMk, ?_, fun t ht hkt => by omega⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
    rw [List.drop_eq_getElem_cons hkM'] at htop
    simpa using htop
  clear h hR htop hstk
  rintro env s2 ⟨c2, m, hv, rfl, h, hR, hmk, hhv, htop, hgt⟩
  have hlenL : (A ++ (P.take m ++ hv :: P.drop m) ++ M.drop (k + 1)).length =
      A.length + M.length := by
    simp [List.length_take, List.length_drop, hPk]; omega
  have hsp3 := htop.1
  rw [hlenL] at hsp3
  have hstk := hR.stk_eq h (by omega)
  have hexit : (m = 0 ∨ ∀ h0 : 0 < m, ¬ st.id M[k] < st.id (P[m - 1]'(by omega))) →
      WP Vbcf.prog ((Stmt.store ((Expr.var "st").field "stk") (Expr.var "j") (Expr.var "x")).seq
          (Stmt.assign "i" (Expr.bin BinOp.add (Expr.var "i") (Expr.lit32 1#32))))
        (LoopQ (AciSortInv W sb X c0 prems params st base A M)
          (retPost none fun x s' =>
            ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
              ∃ M', M'.Perm M ∧ M'.Pairwise (fun a b => st.id a ≤ st.id b) ∧
                StkTop c' st base (A ++ M')))
        [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, uv (base + A.length)),
          ("i", .u32, uv (base + A.length + k)), ("j", .u32, uv (base + A.length + m)),
          ("x", .u32, uv (st.id M[k]))] s2 := by
    intro hstop
    apply WP.seq
    apply WP.aci_stk_store h hR htop (p := A.length + m) (y := M[k]) (by rw [hlenL]; omega) hMk
      (by simp [Env.get]) (by simp [evalE, Env.get, Nat.add_assoc]) (by simp [evalE, Env.get])
    intro s3 c3 h3 hR3 htop3
    rw [aci_hole_set (by omega)] at htop3
    apply WP.assign_loop
    rule_simp
    refine ⟨c3, k + 1, P.take m ++ M[k] :: P.drop m, BitVec.ofNat 32 (base + A.length + m),
      BitVec.ofNat 32 (st.id M[k]), by simp [Nat.add_assoc], h3, hR3, by omega,
      by omega, ?_, ?_, aci_insert_perm hPp hkM', by simpa using htop3⟩
    · simp [List.length_take, List.length_drop]; omega
    · apply aci_insert_sorted hPs (by omega)
      · intro h0
        rcases hstop with e | e
        · omega
        · exact Nat.le_of_not_lt (e h0)
      · exact hgt
  have hb1 : base + A.length + m < 4294967296 := by omega
  by_cases hm0 : m = 0
  · subst hm0
    rule_simp
    simpa using hexit (Or.inl rfl)
  have hPm : st.lv P[m - 1] := by
    have := htop.lt_size (j := A.length + (m - 1)) (by rw [hlenL]; omega)
    rwa [aci_hole_get (by omega) (by omega)] at this
  have hcell : rd c2.stk (base + A.length + (m - 1)) = some (uv (st.id P[m - 1])) := by
    have := htop.aci_rd (j := A.length + (m - 1)) (by rw [hlenL]; omega)
    rwa [aci_hole_get (by omega) (by omega), ← Nat.add_assoc] at this
  have hj1 : BitVec.ofNat 32 (base + A.length + m) - 1#32 = BitVec.ofNat 32 (base + A.length + (m - 1)) := by
    rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl, cw_sub hb1 (by omega)]
    congr 1; omega
  rule_simp [hj1, hstk, hcell, hR.core.aci_id_lt hMk hPm]
  refine ⟨fun hle => hexit (Or.inr fun _ => Nat.not_lt_of_le (hle hm0)), fun _ hlt2 => ?_⟩
  apply WP.seq
  apply WP.aci_stk_store h hR htop (p := A.length + m) (y := P[m - 1]) (by rw [hlenL]; omega) hPm
    (by simp [Env.get]) (by simp [evalE, Env.get, Nat.add_assoc])
    (by rule_simp [hj1, hstk, hcell])
  intro s3 c3 h3 hR3 htop3
  rw [aci_hole_set (by omega), aci_shift_list (by omega) (by omega)] at htop3
  apply WP.assign_loop
  rule_simp [hj1]
  refine ⟨c3, m - 1, P[m - 1], rfl, h3, hR3, by omega, hPm, htop3, fun t ht hmt => ?_⟩
  rcases Nat.lt_or_ge t m with h1 | h1
  · have : t = m - 1 := by omega
    subst this
    exact hlt2
  · exact hgt t ht h1

end Vbcf.Proof
