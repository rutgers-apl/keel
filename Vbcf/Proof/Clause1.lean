import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bool
import Bcf.Soundness
import Init.Internal.Order.While

/-!
# Vbcf proofs: the Clause family, part 1 — the Lean side

Characterisations of the Lean functions behind `ruleResolution`, `ruleFactoring` and
`ruleReordering` in the shape the C loops compute them:

* `resolveChain` as a fold (`clRfold`), extended one step at a time (`clRfold_snoc`);
* `parseDupPairs` through `clPd` (its loop with the loop state as arguments), and the
  three one-step equations the C needs (`clPd_ge`, `clPd_zero`, `clPd_step`); this uses the
  `while`-loop unfolding `Lean.Loop.forIn_eq_of_monadTail` of Lean 4.34;
* `keptLits` on a prefix (`clKept`);
* `applySwaps` as a fold of swaps (`applySwaps_eq_fold`), and the permutation facts that
  make both `subsetB` tests true.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf


/-! ## Generic list facts -/

theorem cl_mapOpt_of_get {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l'.length = l.length →
      (∀ j (hj : j < l.length) (hj' : j < l'.length), f l[j] = some l'[j]) → mapOpt f l = some l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hf => by
    have h0 := hf 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih := cl_mapOpt_of_get (l := l) (l' := l') (by simpa using h)
      (fun j hj hj' => by
        have := hf (j + 1) (by simp; omega) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        exact this)
    simp [mapOpt, h0, ih]

/-- `l.erase x` when `x` is first found at index `k`. -/
theorem cl_erase_at {l : List Nat} {x k : Nat} (hk : k < l.length) (hx : l[k] = x)
    (hpre : ∀ j (hj : j < k), l[j]'(by omega) ≠ x) : l.erase x = l.eraseIdx k := by
  rw [List.erase_eq_eraseIdx]
  have : List.idxOf? x l = some k := by
    rw [List.idxOf?_eq_some_iff]
    exact ⟨hk, hx, fun j hj => hpre j hj⟩
  rw [this]

/-! ## Words -/

theorem cw_shr {x : Nat} (hx : x < 4294967296) (s : Nat) :
    BitVec.ofNat 32 x >>> s = BitVec.ofNat 32 (x / 2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, bv_toNat_ofNat hx, Nat.shiftRight_eq_div_pow,
    bv_toNat_ofNat (by have := Nat.div_le_self x (2 ^ s); omega)]

theorem cw_and1 (x : Nat) : BitVec.ofNat 32 x &&& 1#32 = BitVec.ofNat 32 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_1]
  simp only [BitVec.toNat_ofNat]
  omega

theorem cw_andffff (x : Nat) : BitVec.ofNat 32 x &&& 65535#32 = BitVec.ofNat 32 (x % 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (65535 : Nat) % 2 ^ 32 = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem cw_div {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    BitVec.ofNat 32 a / BitVec.ofNat 32 b = BitVec.ofNat 32 (a / b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, bv_toNat_ofNat ha, bv_toNat_ofNat hb,
    bv_toNat_ofNat (by have := Nat.div_le_self a b; omega)]

theorem cw_mod {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    BitVec.ofNat 32 a % BitVec.ofNat 32 b = BitVec.ofNat 32 (a % b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, bv_toNat_ofNat ha, bv_toNat_ofNat hb,
    bv_toNat_ofNat (by have := Nat.mod_le a b; omega)]

theorem cw_mul (a b : Nat) :
    BitVec.ofNat 32 a * BitVec.ofNat 32 b = BitVec.ofNat 32 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [← Nat.mul_mod]

theorem cw_sub {a b : Nat} (ha : a < 4294967296) (hb : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_sub_toNat (by rw [bv_toNat_ofNat ha, bv_toNat_ofNat (by omega)]; omega),
    bv_toNat_ofNat ha, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]

/-! ## Resolution -/

/-- The two pivots of step `i` with pivot literal `lit`. -/
def clPiv0 (st : St) (pols : List Nat) (i lit : Nat) : Option Nat :=
  if testPol pols i then some lit else findNode st ⟨.boolNot, #[lit]⟩

def clPiv1 (st : St) (pols : List Nat) (i lit : Nat) : Option Nat :=
  if testPol pols i then findNode st ⟨.boolNot, #[lit]⟩ else some lit

/-- One step of `resolveChain`. -/
def clRstep (st : St) (pols : List Nat) (i rhsPm lit : Nat) (lhs : List Nat) : List Nat :=
  eraseOpt lhs (clPiv0 st pols i lit) ++
    eraseOpt (litsOf st rhsPm (clPiv1 st pols i lit)) (clPiv1 st pols i lit)

/-- `resolveChain` without its length check. -/
def clRfold (st : St) (pols : List Nat) : List Nat → List Nat → Nat → List Nat → List Nat
  | r :: rest, l :: lits, i, lhs => clRfold st pols rest lits (i + 1) (clRstep st pols i r l lhs)
  | _, _, _, lhs => lhs

theorem clRfold_eq {st : St} {pols : List Nat} :
    ∀ {rest lits : List Nat} {i : Nat} {lhs : List Nat}, rest.length = lits.length →
      resolveChain st pols rest lits i lhs = some (clRfold st pols rest lits i lhs)
  | [], [], _, _, _ => by simp [resolveChain, clRfold]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | r :: rest, l :: lits, i, lhs, h => by
    simp only [resolveChain, clRfold]
    exact clRfold_eq (by simpa using h)

theorem clRfold_snoc {st : St} {pols : List Nat} :
    ∀ {rest lits : List Nat} {i : Nat} {lhs : List Nat} {l : Nat} (h : lits.length < rest.length),
      clRfold st pols rest (lits ++ [l]) i lhs =
        clRstep st pols (i + lits.length) rest[lits.length] l (clRfold st pols rest lits i lhs)
  | [], _, _, _, _, h => by simp at h
  | r :: rest, [], i, lhs, l, _ => by
    cases rest <;> simp [clRfold]
  | r :: rest, a :: lits, i, lhs, l, h => by
    simp only [List.cons_append, clRfold, List.length_cons, List.getElem_cons_succ]
    rw [clRfold_snoc (by simp at h; omega)]
    congr 1
    omega

/-- The clause on the stack after the first `lits.length` steps of `r_resolution`. -/
def clRcur (st : St) (pols : List Nat) (p0 : Nat) (rest : List Nat) : List Nat → List Nat
  | [] => []
  | l0 :: ls => clRfold st pols rest (l0 :: ls) 0 (litsOf st p0 (clPiv0 st pols 0 l0))

/-- `testPol` on the polarity words when the word is in range. -/
theorem cl_testPol {params : List Nat} {pw i : Nat} (hi : i / 32 < pw) (hpw : pw ≤ params.length) :
    testPol (params.take pw) i = decide (params[i / 32] / 2 ^ (i % 32) % 2 = 1) := by
  unfold testPol
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi,
    List.getElem?_eq_getElem (by omega)]
  simp [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-! ## Factoring: `parseDupPairs` -/

theorem cl_loop_unfold {β : Type} (b : β) (f : Unit → β → Id (ForInStep β)) :
    forIn Lean.Loop.mk b f = (match (f () b).run with
      | .done v => pure v | .yield v => forIn Lean.Loop.mk v f) := by
  show Lean.Loop.forIn _ b f = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

/-- The loop of `parseDupPairs` from the loop state `(idx, dups, preUniq)` on. -/
def clPd (args : Array Nat) (params : List Nat) (idx0 : Nat) (dups0 : List Nat)
    (pre0 : Option Nat) : Option (List Nat) := Id.run do
  let vlen := params.length * 4
  let mut idx := idx0
  let mut dups : List Nat := dups0
  let mut preUniq : Option Nat := pre0
  while idx < vlen do
    let pairLen := paramByte params idx
    idx := idx + 1
    if pairLen = 0 then break
    if pairLen < 2 ∨ idx + pairLen > vlen then return none
    let uniq := paramByte params idx
    if uniq ≥ args.size then return none
    match preUniq with
    | some pu => if uniq ≤ pu then return none
    | none => pure ()
    preUniq := some uniq
    for j in [1:pairLen] do
      let d := paramByte params (idx + j)
      if d ≥ args.size ∨ d ≤ uniq then return none
      if args[uniq]? ≠ args[d]? then return none
      dups := d :: dups
    idx := idx + pairLen
  if dups.isEmpty then return none
  -- trailing bytes must be zero
  for k in [idx:vlen] do
    if paramByte params k ≠ 0 then return none
  return some dups

theorem parseDupPairs_eq_clPd (args : Array Nat) (params : List Nat) :
    parseDupPairs args params = clPd args params 0 [] none := rfl

theorem cl_fin_forIn (params : List Nat) (a n : Nat)
    (hz : ∀ k, a ≤ k → k < a + n → paramByte params k = 0) :
    forIn (m := Id) (List.range' a n) ((none : Option (Option (List Nat))), ())
      (fun k (_ : Option (Option (List Nat)) × Unit) =>
        if paramByte params k = 0 then pure (ForInStep.yield (none, ()))
        else pure (ForInStep.done (some none, ()))) = pure (none, ()) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    simp [hz a (by omega) (by omega)]
    exact ih (a + 1) (fun k h1 h2 => hz k (by omega) (by omega))

/-- The loop ends at the end of the bytes. -/
theorem clPd_ge {args : Array Nat} {params : List Nat} {idx : Nat} {dups : List Nat}
    {pre : Option Nat} (h : params.length * 4 ≤ idx) (hd : dups ≠ []) :
    clPd args params idx dups pre = some dups := by
  unfold clPd
  dsimp only
  rw [cl_loop_unfold]
  simp [show ¬ idx < params.length * 4 by omega, hd, show params.length * 4 - idx = 0 by omega]

/-- The loop ends at a zero length byte; the rest must be zero. -/
theorem clPd_zero {args : Array Nat} {params : List Nat} {idx : Nat} {dups : List Nat}
    {pre : Option Nat} (h : idx < params.length * 4) (h0 : paramByte params idx = 0)
    (hd : dups ≠ [])
    (hz : ∀ k, idx + 1 ≤ k → k < params.length * 4 → paramByte params k = 0) :
    clPd args params idx dups pre = some dups := by
  unfold clPd
  dsimp only
  rw [cl_loop_unfold]
  simp [h, h0, hd]
  rw [cl_fin_forIn params _ _ (fun k h1 h2 => hz k h1 (by omega))]
  rfl

theorem cl_list_forIn_yield {γ : Type} (g : Nat → Nat)
    (G : Nat → Option γ × List Nat → Id (ForInStep (Option γ × List Nat)))
    (a n : Nat) (hG : ∀ j, a ≤ j → j < a + n → ∀ s, G j (none, s) = pure (.yield (none, g j :: s)))
    (dups : List Nat) :
    forIn (List.range' a n) (none, dups) G = pure (none, ((List.range' a n).map g).reverse ++ dups) := by
  induction n generalizing a dups with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons, hG a (by omega) (by omega)]
    show forIn _ _ G = _
    rw [ih (a + 1) (fun j h1 h2 s => hG j (by omega) (by omega) s)]
    simp

theorem cl_range_forIn_yield {γ : Type} (g : Nat → Nat)
    (G : Nat → Option γ × List Nat → Id (ForInStep (Option γ × List Nat)))
    (pl : Nat) (hG : ∀ j, 1 ≤ j → j < pl → ∀ s, G j (none, s) = pure (.yield (none, g j :: s)))
    (dups : List Nat) :
    forIn [1:pl] (none, dups) G = pure (none, ((List.range' 1 (pl - 1)).map g).reverse ++ dups) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  exact cl_list_forIn_yield g G 1 (pl - 1) (fun j h1 h2 s => hG j h1 (by omega) s) dups

/-- The positions recorded by the pair starting at byte `idx`. -/
def clNew (params : List Nat) (idx : Nat) : List Nat :=
  ((List.range' 1 (paramByte params idx - 1)).map (fun j => paramByte params (idx + 1 + j))).reverse

/-- One well-formed pair. -/
theorem clPd_step {args : Array Nat} {params : List Nat} {idx : Nat} {dups : List Nat}
    {pre : Option Nat}
    (h : idx < params.length * 4) (h0 : paramByte params idx ≠ 0) (h2 : 2 ≤ paramByte params idx)
    (hle : idx + 1 + paramByte params idx ≤ params.length * 4)
    (hu : paramByte params (idx + 1) < args.size)
    (hpre : ∀ pu, pre = some pu → pu < paramByte params (idx + 1))
    (hin : ∀ j, 1 ≤ j → j < paramByte params idx →
      paramByte params (idx + 1 + j) < args.size ∧
      paramByte params (idx + 1) < paramByte params (idx + 1 + j) ∧
      args[paramByte params (idx + 1)]? = args[paramByte params (idx + 1 + j)]?) :
    clPd args params idx dups pre = clPd args params (idx + 1 + paramByte params idx)
      (clNew params idx ++ dups) (some (paramByte params (idx + 1))) := by
  conv => lhs; unfold clPd
  dsimp only
  rw [cl_loop_unfold]
  dsimp only
  rw [ite_eq_left h, ite_eq_right h0, ite_eq_right (by omega), ite_eq_right (by omega)]
  have key : ∀ (G : Nat → Option (Option (List Nat)) × List Nat →
      Id (ForInStep (Option (Option (List Nat)) × List Nat))),
    (∀ j, 1 ≤ j → j < paramByte params idx → ∀ s,
      G j (none, s) = pure (.yield (none, paramByte params (idx + 1 + j) :: s))) →
    forIn [1:paramByte params idx] (none, dups) G = pure (none, clNew params idx ++ dups) :=
    fun G hG => cl_range_forIn_yield _ G _ hG dups
  cases pre with
  | none =>
    dsimp only
    rw [key]
    · rfl
    · intro j h1 h2 s
      obtain ⟨a1, a2, a3⟩ := hin j h1 h2
      simp [a3]
      omega
  | some pu =>
    dsimp only
    rw [ite_eq_right (by have := hpre pu rfl; omega)]
    rw [key]
    · rfl
    · intro j h1 h2 s
      obtain ⟨a1, a2, a3⟩ := hin j h1 h2
      simp [a3]
      omega

theorem cl_range'_snoc (j : Nat) (g : Nat → Nat) :
    ((List.range' 1 (j + 1)).map g).reverse = g (j + 1) :: ((List.range' 1 j).map g).reverse := by
  rw [List.range'_concat]
  simp [Nat.add_comm]

/-! ## Factoring: the kept literals -/

/-- `keptLits` over the first `k` positions. -/
def clKept (args : Array Nat) (dups : List Nat) (k : Nat) : List Nat :=
  ((List.range k).filter (fun i => !dups.contains i)).filterMap (fun i => args[i]?)

theorem clKept_size (args : Array Nat) (dups : List Nat) :
    clKept args dups args.size = keptLits args dups := rfl

theorem clKept_zero (args : Array Nat) (dups : List Nat) : clKept args dups 0 = [] := rfl

theorem clKept_succ {args : Array Nat} {dups : List Nat} {k : Nat} (hk : k < args.size) :
    clKept args dups (k + 1) =
      clKept args dups k ++ (if k ∈ dups then [] else [args[k]]) := by
  unfold clKept
  rw [List.range_succ, List.filter_append, List.filterMap_append]
  congr 1
  by_cases h : k ∈ dups
  · simp [h]
  · simp [h, hk]

theorem clKept_mem {args : Array Nat} {dups : List Nat} {k i : Nat} (hi : i < k)
    (hik : i < args.size) (hd : i ∉ dups) : args[i] ∈ clKept args dups k := by
  unfold clKept
  rw [List.mem_filterMap]
  exact ⟨i, by simp [hi, hd], by simp [hik]⟩

theorem clKept_sub {args : Array Nat} {dups : List Nat} {k : Nat} {x : Nat}
    (hx : x ∈ clKept args dups k) : x ∈ args := by
  unfold clKept at hx
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hx
  rw [Array.getElem?_eq_some_iff] at hi
  obtain ⟨hk, rfl⟩ := hi
  exact Array.getElem_mem hk

/-! ## Reordering: `applySwaps` -/

/-- Half-word `t` of the parameter words. -/
def clHalfW (params : List Nat) (t : Nat) : Nat :=
  ((params.getD (t / 2) 0) >>> (16 * (t % 2))) &&& 0xffff

def clSwapStep (params : List Nat) (a : Array Nat) (t : Nat) : Array Nat :=
  a.swapIfInBounds (clHalfW params t &&& 0xff) ((clHalfW params t >>> 8) &&& 0xff)

/-- The first `k` swaps. -/
def clSwaps (params : List Nat) (args : Array Nat) (k : Nat) : Array Nat :=
  (List.range' 1 k).foldl (clSwapStep params) args

theorem clSwaps_zero (params : List Nat) (args : Array Nat) : clSwaps params args 0 = args := rfl

theorem clSwaps_succ (params : List Nat) (args : Array Nat) (k : Nat) :
    clSwaps params args (k + 1) = clSwapStep params (clSwaps params args k) (k + 1) := by
  unfold clSwaps
  rw [List.range'_concat]
  simp [Nat.add_comm]

theorem clSwaps_size (params : List Nat) (args : Array Nat) (k : Nat) :
    (clSwaps params args k).size = args.size := by
  induction k with
  | zero => rfl
  | succ k ih => rw [clSwaps_succ]; simp [clSwapStep, ih]

theorem cl_list_forIn_fold {γ : Type} (step : Array Nat → Nat → Array Nat) (N : Nat)
    (hstep : ∀ a t, a.size = N → (step a t).size = N)
    (G : Nat → Option γ × Array Nat → Id (ForInStep (Option γ × Array Nat)))
    (b n : Nat) (hG : ∀ j, b ≤ j → j < b + n → ∀ a, a.size = N →
      G j (none, a) = pure (.yield (none, step a j)))
    (a : Array Nat) (ha : a.size = N) :
    forIn (List.range' b n) (none, a) G = pure (none, (List.range' b n).foldl step a) := by
  induction n generalizing b a with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons, hG b (by omega) (by omega) a ha]
    show forIn _ _ G = _
    rw [ih (b + 1) (fun j h1 h2 a' ha' => hG j (by omega) (by omega) a' ha') _ (hstep a b ha)]
    simp

theorem applySwaps_eq_fold {params : List Nat} {args : Array Nat}
    (hcnt : clHalfW params 0 ≤ args.size)
    (hlen : ((clHalfW params 0 + 1) * 2 + 3) / 4 = params.length)
    (hpad : (clHalfW params 0 + 1) * 2 % 4 ≠ 0 → clHalfW params (clHalfW params 0 + 1) = 0)
    (hin : ∀ t, 1 ≤ t → t ≤ clHalfW params 0 →
      clHalfW params t &&& 0xff < args.size ∧ (clHalfW params t >>> 8) &&& 0xff < args.size) :
    applySwaps params args = some (clSwaps params args (clHalfW params 0)) := by
  unfold applySwaps
  dsimp only
  have e : ∀ t, ((params.getD (t / 2) 0) >>> (16 * (t % 2))) &&& 65535 = clHalfW params t :=
    fun t => rfl
  simp only [e]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  rw [cl_list_forIn_fold (clSwapStep params) args.size (fun a t ha => by simp [clSwapStep, ha])
    _ 1 _ ?_ args rfl]
  · rfl
  · intro j h1 h2 a ha
    obtain ⟨a1, a2⟩ := hin j h1 (by omega)
    simp [ha, clSwapStep]
    omega

theorem cl_swap_perm (a : Array Nat) (i j : Nat) : (a.swapIfInBounds i j).toList.Perm a.toList := by
  rw [Array.swapIfInBounds_def]
  split
  · split
    · exact Array.perm_iff_toList_perm.mp (Array.swap_perm _ _)
    · exact List.Perm.refl _
  · exact List.Perm.refl _

theorem clSwaps_perm (params : List Nat) (args : Array Nat) (k : Nat) :
    (clSwaps params args k).toList.Perm args.toList := by
  induction k with
  | zero => exact List.Perm.refl _
  | succ k ih =>
    rw [clSwaps_succ]
    exact (cl_swap_perm _ _ _).trans ih

/-- A permutation passes both `subsetB` tests. -/
theorem cl_subsetB_perm {l m : List Nat} (h : l.Perm m) : subsetB l m = true := by
  rw [subsetB_eq, List.all_eq_true]
  intro x hx
  simpa using h.mem_iff.mp hx

end Vbcf.Proof
