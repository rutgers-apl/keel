import Bcf.Semantics

/-!
# Evaluation agrees with the type checker

`eval_ty`: the dynamic type of a node's value is exactly its static
type, and an ill-typed node evaluates to `bad`.  Proved once per typing
combinator, then assembled over the operator table and lifted to pools.
-/

namespace Bcf

theorem tyGuard_pos {p : Prop} [Decidable p] (h : p) (t : Ty) : tyGuard p t = some t := by
  simp [tyGuard, h]
theorem tyGuard_neg {p : Prop} [Decidable p] (h : ¬p) (t : Ty) : tyGuard p t = none := by
  simp [tyGuard, h]

namespace Val

theorem asBv_some_iff {w : Nat} {v : Val} {x : BitVec w} : asBv w v = some x ↔ v = .bv w x := by
  cases v with
  | bv w' y =>
    by_cases h : w' = w
    · subst h; simp
    · simp [h]
  | bool _ => simp
  | list _ _ => simp
  | bad => simp

theorem asBv_none_iff {w : Nat} {v : Val} : asBv w v = none ↔ v.ty ≠ some (.bv w) := by
  cases v with
  | bv w' y =>
    by_cases h : w' = w
    · subst h; simp
    · simp [h]
  | bool _ => simp
  | list _ _ => simp
  | bad => simp

theorem ty_eq_bv_iff {v : Val} {w : Nat} : v.ty = some (.bv w) ↔ ∃ x, v = .bv w x := by
  cases v with
  | bv w' y =>
    by_cases h : w' = w
    · subst h; simp
    · simp [h]
  | bool _ => simp
  | list _ _ => simp
  | bad => simp

theorem ty_eq_bool_iff {v : Val} : v.ty = some .bool ↔ ∃ b, v = .bool b := by
  cases v <;> simp

theorem asBool_some_iff {v : Val} {b : Bool} : asBool v = some b ↔ v = .bool b := by
  cases v <;> simp

theorem asBool_none_iff {v : Val} : asBool v = none ↔ v.ty ≠ some .bool := by
  cases v <;> simp

theorem tys_length {vs : List Val} {ts : List Ty} (h : tys vs = some ts) : ts.length = vs.length := by
  induction vs generalizing ts with
  | nil => simp at h; subst h; rfl
  | cons v rest ih =>
    simp only [tys_cons] at h
    split at h
    · rename_i t ts' _ hrest
      simp at h; subst h
      simp [ih hrest]
    · simp at h

theorem bvs_some_tys {w : Nat} {vs : List Val} {xs : List (BitVec w)}
    (h : bvs w vs = some xs) : tys vs = some (xs.map fun _ => Ty.bv w) := by
  induction vs generalizing xs with
  | nil => simp [bvs] at h; subst h; rfl
  | cons v rest ih =>
    simp only [bvs] at h
    split at h
    · rename_i x xs' hx hrest
      simp at h; subst h
      rw [tys_cons, ih hrest, asBv_some_iff.mp hx]
      simp
    · simp at h

theorem bvs_none_tys {w : Nat} {vs : List Val} (h : bvs w vs = none) :
    ∀ ts, tys vs = some ts → allBv w ts = false := by
  induction vs with
  | nil => simp [bvs] at h
  | cons v rest ih =>
    intro ts hts
    rw [tys_cons] at hts
    simp only [bvs] at h
    split at h
    · simp at h
    · rename_i hne
      split at hts
      · rename_i t ts' ht hrest
        simp at hts; subst hts
        cases hx : asBv w v with
        | some x =>
          have := asBv_some_iff.mp hx; subst this
          simp at ht; subst ht
          have hr : bvs w rest = none := by
            cases hr : bvs w rest with
            | some _ => exact absurd hr (hne x _ hx)
            | none => rfl
          simp [allBv, ih hr ts' hrest]
        | none =>
          have := asBv_none_iff.mp hx
          rw [ht] at this
          cases t with
          | bv w' =>
            have hw : w' ≠ w := fun e => this (by rw [e])
            simp [allBv, hw]
          | bool => simp [allBv]
          | list _ _ => simp [allBv]
      · simp at hts

theorem bools_some_tys {vs : List Val} {bs : List Bool}
    (h : bools vs = some bs) : tys vs = some (bs.map fun _ => Ty.bool) := by
  induction vs generalizing bs with
  | nil => simp [bools] at h; subst h; rfl
  | cons v rest ih =>
    simp only [bools] at h
    split at h
    · rename_i x xs' hx hrest
      simp at h; subst h
      rw [tys_cons, ih hrest, asBool_some_iff.mp hx]
      simp
    · simp at h

theorem bools_none_tys {vs : List Val} (h : bools vs = none) :
    ∀ ts, tys vs = some ts → allBool ts = false := by
  induction vs with
  | nil => simp [bools] at h
  | cons v rest ih =>
    intro ts hts
    rw [tys_cons] at hts
    simp only [bools] at h
    split at h
    · simp at h
    · rename_i hne
      split at hts
      · rename_i t ts' ht hrest
        simp at hts; subst hts
        cases hx : asBool v with
        | some x =>
          have := asBool_some_iff.mp hx; subst this
          simp at ht; subst ht
          have hr : bools rest = none := by
            cases hr : bools rest with
            | some _ => exact absurd hr (hne x _ hx)
            | none => rfl
          simp [allBool, ih hr ts' hrest]
        | none =>
          have := asBool_none_iff.mp hx
          rw [ht] at this
          cases t with
          | bv w' => simp [allBool]
          | bool => exact absurd rfl this
          | list _ _ => simp [allBool]
      · simp at hts

theorem concatVals_isBv {vs : List Val} {v : Val} (h : concatVals vs = some v) :
    ∃ n x, v = .bv n x := by
  cases vs with
  | nil => simp [concatVals] at h
  | cons a rest =>
    cases a with
    | bv n x =>
      cases rest with
      | nil => simp [concatVals] at h; subst h; exact ⟨_, _, rfl⟩
      | cons b rest' =>
        simp only [concatVals] at h
        split at h
        · simp at h; subst h; exact ⟨_, _, rfl⟩
        · simp at h
    | bool _ => simp [concatVals] at h
    | list _ _ => simp [concatVals] at h
    | bad => simp [concatVals] at h

/-- The type of a concatenation is the sum of the widths. -/
theorem concatVals_ty (vs : List Val) :
    (concatVals vs).bind ty = (tys vs).bind (fun ts => (bvWidths ts).map Ty.bv) := by
  induction vs with
  | nil => simp [concatVals, bvWidths]
  | cons a rest ih =>
    cases a with
    | bv n x =>
      cases rest with
      | nil => simp [concatVals, bvWidths]
      | cons b rest' =>
        have hlen : ∀ ts, tys (b :: rest') = some ts → ts ≠ [] := by
          intro ts hts hnil; subst hnil; have := tys_length hts; simp at this
        simp only [concatVals]
        cases hc : concatVals (b :: rest') with
        | some v =>
          obtain ⟨m, y, rfl⟩ := concatVals_isBv hc
          rw [hc] at ih
          simp only [Option.bind_some, ty_bv] at ih
          -- ih : some (bv m) = (tys (b :: rest')).bind ...
          cases hts : tys (b :: rest') with
          | none => rw [hts] at ih; simp at ih
          | some ts =>
            rw [hts] at ih
            simp only [Option.bind_some] at ih
            have hw : bvWidths ts = some m := by
              cases hw : bvWidths ts with
              | none => rw [hw] at ih; simp at ih
              | some m' => rw [hw] at ih; simp at ih; rw [ih]
            obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
              cases ts with
              | nil => exact absurd rfl (hlen [] hts)
              | cons t ts' => exact ⟨t, ts', rfl⟩
            simp [tys_cons, hts, bvWidths, hw]
        | none =>
          rw [hc] at ih
          simp only [Option.bind_none] at ih
          cases hts : tys (b :: rest') with
          | none => simp [tys_cons, hts]
          | some ts =>
            rw [hts] at ih
            simp only [Option.bind_some] at ih
            have hw : bvWidths ts = none := by
              cases hw : bvWidths ts with
              | none => rfl
              | some m' => rw [hw] at ih; simp at ih
            obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
              cases ts with
              | nil => exact absurd rfl (hlen [] hts)
              | cons t ts' => exact ⟨t, ts', rfl⟩
            simp [tys_cons, hts, bvWidths, hw]
    | bool _ =>
      simp only [concatVals, Option.bind_none, tys_cons, ty_bool]
      cases tys rest <;> simp [bvWidths]
    | list _ _ =>
      simp only [concatVals, Option.bind_none, tys_cons, ty_list]
      cases tys rest <;> simp [bvWidths]
    | bad => simp [concatVals, tys_cons]

end Val

theorem allBv_map_const (w : Nat) (xs : List α) : allBv w (xs.map fun _ => Ty.bv w) = true := by
  induction xs <;> simp_all [allBv]

theorem allBool_map_const (xs : List α) : allBool (xs.map fun _ => Ty.bool) = true := by
  induction xs <;> simp_all [allBool]

/-! ## One lemma per combinator -/

theorem bvVarEval_ty (ρ : Assign) (w id : Nat) (vs : List Val) :
    (bvVarEval ρ w id vs).ty = (Val.tys vs).bind (bvVarTy w) := by
  rcases vs with _ | ⟨a, rest⟩
  · simp [bvVarEval, bvVarTy, tyGuard]
  · simp only [bvVarEval, Val.tys_cons]; cases a.ty <;> cases Val.tys rest <;> simp [bvVarTy]

theorem bvValEval_ty (w v : Nat) (vs : List Val) :
    (bvValEval w v vs).ty = (Val.tys vs).bind (bvValTy w v) := by
  rcases vs with _ | ⟨a, rest⟩
  · simp [bvValEval, bvValTy, tyGuard]
  · simp only [bvValEval, Val.tys_cons]; cases a.ty <;> cases Val.tys rest <;> simp [bvValTy]

theorem boolConstEval_ty (b : Bool) (vs : List Val) :
    (boolConstEval b vs).ty = (Val.tys vs).bind boolNullTy := by
  rcases vs with _ | ⟨a, rest⟩
  · simp [boolConstEval, boolNullTy]
  · simp only [boolConstEval, Val.tys_cons]; cases a.ty <;> cases Val.tys rest <;> simp [boolNullTy]

theorem bvUn_ty (w : Nat) (f : BitVec w → BitVec w) (vs : List Val) :
    (bvUn w f vs).ty = (Val.tys vs).bind (bvUnTy w) := by
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [bvUn, bvUnTy]
  · cases a with
    | bv w' x =>
      by_cases h : w' = w
      · subst h; simp [bvUn, bvUnTy, tyGuard]
      · simp [bvUn, bvUnTy, tyGuard, h]
    | bool _ => simp [bvUn, bvUnTy, tyGuard]
    | list _ _ => simp [bvUn, bvUnTy, tyGuard]
    | bad => simp [bvUn]
  · simp only [bvUn, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases Val.tys rest <;> simp [bvUnTy]

theorem bvBin_ty (w : Nat) (f : BitVec w → BitVec w → BitVec w) (vs : List Val) :
    (bvBin w f vs).ty = (Val.tys vs).bind (bvBinTy w) := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [bvBin, bvBinTy]
  · simp only [bvBin, Val.tys_cons]; cases a.ty <;> simp [bvBinTy]
  · cases a with
    | bv wa x =>
      cases b with
      | bv wb y =>
        by_cases ha : wa = w
        · subst wa
          by_cases hb : wb = w
          · subst wb; simp [bvBin, bvBinTy, tyGuard]
          · simp [bvBin, bvBinTy, tyGuard, hb]
        · simp [bvBin, bvBinTy, tyGuard, ha]
      | bool _ => simp [bvBin, bvBinTy, tyGuard]
      | list _ _ => simp [bvBin, bvBinTy, tyGuard]
      | bad => simp [bvBin]
    | bool _ => cases b <;> simp [bvBin, bvBinTy, tyGuard]
    | list _ _ => cases b <;> simp [bvBin, bvBinTy, tyGuard]
    | bad => cases b <;> simp [bvBin]
  · simp only [bvBin, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases c.ty <;> cases Val.tys rest <;> simp [bvBinTy]

theorem bvN_ty (w : Nat) (f : List (BitVec w) → BitVec w) (vs : List Val) :
    (bvN w f vs).ty = (Val.tys vs).bind (bvNTy w) := by
  unfold bvN
  cases hb : Val.bvs w vs with
  | some xs =>
    rw [Val.bvs_some_tys hb]
    simp [bvNTy, tyGuard, allBv_map_const]
  | none =>
    cases ht : Val.tys vs with
    | none => simp
    | some ts => simp [bvNTy, tyGuard, Val.bvs_none_tys hb ts ht]

theorem boolN_ty (f : List Bool → Bool) (vs : List Val) :
    (boolN f vs).ty = (Val.tys vs).bind boolNTy := by
  unfold boolN
  cases hb : Val.bools vs with
  | some bs =>
    rw [Val.bools_some_tys hb]
    simp [boolNTy, tyGuard, allBool_map_const]
  | none =>
    cases ht : Val.tys vs with
    | none => simp
    | some ts => simp [boolNTy, tyGuard, Val.bools_none_tys hb ts ht]

theorem bvFromBoolEval_ty (vs : List Val) :
    (bvFromBoolEval vs).ty = (Val.tys vs).bind bvFromBoolTy := by
  unfold bvFromBoolEval
  cases hb : Val.bools vs with
  | some bs =>
    rw [Val.bools_some_tys hb]
    simp [bvFromBoolTy, tyGuard, allBool_map_const]
  | none =>
    cases ht : Val.tys vs with
    | none => simp
    | some ts => simp [bvFromBoolTy, tyGuard, Val.bools_none_tys hb ts ht]

theorem bvConcatEval_ty (w : Nat) (vs : List Val) :
    (bvConcatEval w vs).ty = (Val.tys vs).bind (bvConcatTy w) := by
  have key := Val.concatVals_ty vs
  unfold bvConcatEval
  cases hc : Val.concatVals vs with
  | some v =>
    obtain ⟨n, x, rfl⟩ := Val.concatVals_isBv hc
    rw [hc] at key
    simp only [Option.bind_some, Val.ty_bv] at key
    cases hts : Val.tys vs with
    | none => rw [hts] at key; simp at key
    | some ts =>
      rw [hts] at key
      simp only [Option.bind_some] at key
      have hw : bvWidths ts = some n := by
        cases hw : bvWidths ts with
        | none => rw [hw] at key; simp at key
        | some m' => rw [hw] at key; simp at key; rw [key]
      simp [bvConcatTy, tyGuard, hw, Val.tys_length hts]
  | none =>
    rw [hc] at key
    simp only [Option.bind_none] at key
    cases hts : Val.tys vs with
    | none => simp
    | some ts =>
      rw [hts] at key
      simp only [Option.bind_some] at key
      have hw : bvWidths ts = none := by
        cases hw : bvWidths ts with
        | none => rfl
        | some m' => rw [hw] at key; simp at key
      simp [bvConcatTy, tyGuard, hw]

theorem listEval_ty (e : Bool) (vs : List Val) :
    (listEval e vs).ty = (Val.tys vs).bind (listTy e) := by
  unfold listEval
  cases ht : Val.tys vs with
  | none => simp
  | some ts => simp [listTy, tyGuard, Val.tys_length ht]

theorem bvIteEval_ty (w : Nat) (vs : List Val) :
    (bvIteEval w vs).ty = (Val.tys vs).bind (bvIteTy w) := by
  rcases vs with _ | ⟨c, _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩⟩
  · simp [bvIteEval, bvIteTy]
  · simp only [bvIteEval, Val.tys_cons]; cases c.ty <;> simp [bvIteTy]
  · simp only [bvIteEval, Val.tys_cons]; cases c.ty <;> cases a.ty <;> simp [bvIteTy]
  · cases c with
    | bool cb =>
      cases a with
      | bv wa x =>
        cases b with
        | bv wb y =>
          by_cases ha : wa = w
          · subst wa
            by_cases hb : wb = w
            · subst wb; simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
            · simp [bvIteEval, bvIteTy, tyGuard, Val.asCond, hb]
          · simp [bvIteEval, bvIteTy, tyGuard, Val.asCond, ha]
        | bool _ => simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
        | list _ _ => simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
        | bad => simp [bvIteEval, Val.asCond]
      | bool _ => cases b <;> simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
      | list _ _ => cases b <;> simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
      | bad => cases b <;> simp [bvIteEval, Val.asCond]
    | bv n z =>
      by_cases hn : n = 1
      · subst hn
        cases a with
        | bv wa x =>
          cases b with
          | bv wb y =>
            by_cases ha : wa = w
            · subst wa
              by_cases hb : wb = w
              · subst wb; simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
              · simp [bvIteEval, bvIteTy, tyGuard, Val.asCond, hb]
            · simp [bvIteEval, bvIteTy, tyGuard, Val.asCond, ha]
          | bool _ => simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
          | list _ _ => simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
          | bad => simp [bvIteEval, Val.asCond]
        | bool _ => cases b <;> simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
        | list _ _ => cases b <;> simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
        | bad => cases b <;> simp [bvIteEval, Val.asCond]
      · cases a <;> cases b <;> simp [bvIteEval, bvIteTy, tyGuard, Val.asCond, hn]
    | list _ _ => cases a <;> cases b <;> simp [bvIteEval, bvIteTy, tyGuard, Val.asCond]
    | bad => cases a <;> cases b <;> simp [bvIteEval, Val.asCond]
  · simp only [bvIteEval, Val.tys_cons]
    cases c.ty <;> cases a.ty <;> cases b.ty <;> cases d.ty <;> cases Val.tys rest <;> simp [bvIteTy]

theorem bvExtractEval_ty (hi lo : Nat) (vs : List Val) :
    (bvExtractEval hi lo vs).ty = (Val.tys vs).bind (bvExtractTy hi lo) := by
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [bvExtractEval, bvExtractTy]
  · cases a <;> simp [bvExtractEval, bvExtractTy, tyGuard]
  · simp only [bvExtractEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases Val.tys rest <;> simp [bvExtractTy]

theorem bvExtEval_ty (s : Bool) (w e : Nat) (vs : List Val) :
    (bvExtEval s w e vs).ty = (Val.tys vs).bind (bvExtTy w e) := by
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [bvExtEval, bvExtTy]
  · cases a <;> simp [bvExtEval, bvExtTy, tyGuard]
  · simp only [bvExtEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases Val.tys rest <;> simp [bvExtTy]

theorem bvSizeEval_ty (w : Nat) (vs : List Val) :
    (bvSizeEval w vs).ty = (Val.tys vs).bind (bvSizeTy w) := by
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [bvSizeEval, bvSizeTy]
  · cases a <;> simp [bvSizeEval, bvSizeTy, tyGuard]
  · simp only [bvSizeEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases Val.tys rest <;> simp [bvSizeTy]

theorem bvRepeatEval_ty (w k : Nat) (vs : List Val) :
    (bvRepeatEval w k vs).ty = (Val.tys vs).bind (bvRepeatTy w k) := by
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [bvRepeatEval, bvRepeatTy]
  · cases a <;> simp [bvRepeatEval, bvRepeatTy, tyGuard]
  · simp only [bvRepeatEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases Val.tys rest <;> simp [bvRepeatTy]

theorem boolNotEval_ty (vs : List Val) :
    (boolNotEval vs).ty = (Val.tys vs).bind boolNotTy := by
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [boolNotEval, boolNotTy]
  · cases a <;> simp [boolNotEval, boolNotTy, tyGuard]
  · simp only [boolNotEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases Val.tys rest <;> simp [boolNotTy]

theorem bitofEval_ty (i : Nat) (vs : List Val) :
    (bitofEval i vs).ty = (Val.tys vs).bind (bitofTy i) := by
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [bitofEval, bitofTy]
  · cases a <;> simp [bitofEval, bitofTy, tyGuard]
  · simp only [bitofEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases Val.tys rest <;> simp [bitofTy]

theorem eqEval_ty (neg : Bool) (vs : List Val) :
    (eqEval neg vs).ty = (Val.tys vs).bind eqTy := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [eqEval, eqTy]
  · simp only [eqEval, Val.tys_cons]; cases a.ty <;> simp [eqTy]
  · cases a with
    | bv n x =>
      cases b with
      | bv m y =>
        by_cases h : m = n
        · subst h; simp [eqEval, Val.eqv, eqTy, tyGuard, Ty.isScalar]
        · have h' : ¬n = m := fun e => h e.symm
          simp [eqEval, Val.eqv, eqTy, tyGuard, h, h']
      | bool _ => simp [eqEval, Val.eqv, eqTy, tyGuard]
      | list _ _ => simp [eqEval, Val.eqv, eqTy, tyGuard]
      | bad => simp [eqEval, Val.eqv]
    | bool x => cases b <;> simp [eqEval, Val.eqv, eqTy, tyGuard, Ty.isScalar]
    | list e vs => cases b <;> simp [eqEval, Val.eqv, eqTy, tyGuard, Ty.isScalar]
    | bad => cases b <;> simp [eqEval, Val.eqv]
  · simp only [eqEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases c.ty <;> cases Val.tys rest <;> simp [eqTy]

theorem bvCmp_ty (f : {w : Nat} → BitVec w → BitVec w → Bool) (vs : List Val) :
    (bvCmp f vs).ty = (Val.tys vs).bind cmpTy := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [bvCmp, cmpTy]
  · simp only [bvCmp, Val.tys_cons]; cases a.ty <;> simp [cmpTy]
  · cases a with
    | bv n x =>
      cases b with
      | bv m y =>
        by_cases h : m = n
        · subst h; simp [bvCmp, cmpTy, tyGuard, Ty.sameBv]
        · have h' : ¬n = m := fun e => h e.symm
          simp [bvCmp, cmpTy, tyGuard, Ty.sameBv, h, h']
      | bool _ => simp [bvCmp, cmpTy, tyGuard, Ty.sameBv]
      | list _ _ => simp [bvCmp, cmpTy, tyGuard, Ty.sameBv]
      | bad => simp [bvCmp]
    | bool _ => cases b <;> simp [bvCmp, cmpTy, tyGuard, Ty.sameBv]
    | list _ _ => cases b <;> simp [bvCmp, cmpTy, tyGuard, Ty.sameBv]
    | bad => cases b <;> simp [bvCmp]
  · simp only [bvCmp, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases c.ty <;> cases Val.tys rest <;> simp [cmpTy]

theorem impliesEval_ty (vs : List Val) :
    (impliesEval vs).ty = (Val.tys vs).bind impliesTy := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [impliesEval, impliesTy]
  · simp only [impliesEval, Val.tys_cons]; cases a.ty <;> simp [impliesTy]
  · cases a <;> cases b <;> simp [impliesEval, impliesTy, tyGuard]
  · simp only [impliesEval, Val.tys_cons]
    cases a.ty <;> cases b.ty <;> cases c.ty <;> cases Val.tys rest <;> simp [impliesTy]

theorem boolIteEval_ty (vs : List Val) :
    (boolIteEval vs).ty = (Val.tys vs).bind boolIteTy := by
  rcases vs with _ | ⟨c, _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩⟩
  · simp [boolIteEval, boolIteTy]
  · simp only [boolIteEval, Val.tys_cons]; cases c.ty <;> simp [boolIteTy]
  · simp only [boolIteEval, Val.tys_cons]; cases c.ty <;> cases a.ty <;> simp [boolIteTy]
  · cases c <;> cases a <;> cases b <;> simp [boolIteEval, boolIteTy, tyGuard]
  · simp only [boolIteEval, Val.tys_cons]
    cases c.ty <;> cases a.ty <;> cases b.ty <;> cases d.ty <;> cases Val.tys rest <;> simp [boolIteTy]

/-! ## Assembly -/

theorem Op.eval_ty (ρ : Assign) (op : Op) (vs : List Val) :
    (op.eval ρ vs).ty = (Val.tys vs).bind op.resultTy := by
  cases op <;> simp only [Op.eval, Op.resultTy]
  · exact bvVarEval_ty ρ _ _ vs
  · exact bvValEval_ty _ _ vs
  · exact bvIteEval_ty _ vs
  · exact bvUn_ty _ _ vs
  · exact bvUn_ty _ _ vs
  · exact bvExtractEval_ty _ _ vs
  · exact bvExtEval_ty _ _ _ vs
  · exact bvExtEval_ty _ _ _ vs
  · exact bvSizeEval_ty _ vs
  · exact bvRepeatEval_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvBin_ty _ _ vs
  · exact bvN_ty _ _ vs
  · exact bvN_ty _ _ vs
  · exact bvN_ty _ _ vs
  · exact bvN_ty _ _ vs
  · exact bvN_ty _ _ vs
  · exact bvConcatEval_ty _ vs
  · exact bvFromBoolEval_ty vs
  · exact boolConstEval_ty _ vs
  · exact boolConstEval_ty _ vs
  · exact boolNotEval_ty vs
  · exact bitofEval_ty _ vs
  · exact eqEval_ty _ vs
  · exact eqEval_ty _ vs
  · exact bvCmp_ty _ vs
  · exact bvCmp_ty _ vs
  · exact bvCmp_ty _ vs
  · exact bvCmp_ty _ vs
  · exact bvCmp_ty _ vs
  · exact bvCmp_ty _ vs
  · exact bvCmp_ty _ vs
  · exact bvCmp_ty _ vs
  · exact impliesEval_ty vs
  · exact boolIteEval_ty vs
  · exact boolN_ty _ vs
  · exact boolN_ty _ vs
  · exact boolN_ty _ vs
  · exact listEval_ty _ vs

theorem tys_map (g : Nat → Val) (l : List Nat) :
    Val.tys (l.map g) = mapOpt (fun a => (g a).ty) l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.map_cons, Val.tys_cons, ih, mapOpt]
    cases (g a).ty <;> cases mapOpt (fun a => (g a).ty) rest <;> rfl

/-- **Evaluation agrees with typing** on every pool node. -/
theorem eval_ty (pool : Pool) (ρ : Assign) (i : Nat) : (eval pool ρ i).ty = typeOf pool i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [eval_unfold, typeOf_unfold]
    cases pool[i]? with
    | none => rfl
    | some n =>
      simp only
      rw [Op.eval_ty, tys_map]
      have : mapOpt (fun a => (if a < i then eval pool ρ a else Val.bad).ty) n.args.toList =
             mapOpt (fun a => if a < i then typeOf pool a else none) n.args.toList := by
        apply mapOpt_congr
        intro a _
        split
        · exact ih a (by assumption)
        · rfl
      rw [this]
      cases mapOpt (fun a => if a < i then typeOf pool a else none) n.args.toList <;> rfl

theorem eval_bv {pool : Pool} {ρ : Assign} {i w : Nat} (h : typeOf pool i = some (.bv w)) :
    ∃ x, eval pool ρ i = .bv w x :=
  Val.ty_eq_bv_iff.mp (by rw [eval_ty]; exact h)

theorem eval_bool {pool : Pool} {ρ : Assign} {i : Nat} (h : typeOf pool i = some .bool) :
    ∃ b, eval pool ρ i = .bool b :=
  Val.ty_eq_bool_iff.mp (by rw [eval_ty]; exact h)

end Bcf
