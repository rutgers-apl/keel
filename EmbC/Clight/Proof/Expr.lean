import EmbC.Clight.Proof.ExprOps
import EmbC.Clight.Proof.Layout2

/-!
# Correctness of expression lowering
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-! ## Static facts -/

theorem LE_static {ctx : LCtx} {σ : LSt} {e : EmbC.Expr} {r : LX} {σ' : LSt}
    (h : LE ctx σ e r σ') : σ.next ≤ σ'.next ∧ CC.typeof r.ex = tyO r.ty := by
  induction h with
  | var _ => exact ⟨Nat.le_refl _, rfl⟩
  | lit32 => exact ⟨Nat.le_refl _, rfl⟩
  | named => exact ⟨Nat.le_refl _, rfl⟩
  | lit64 => exact ⟨Nat.le_refl _, rfl⟩
  | null => exact ⟨Nat.le_refl _, rfl⟩
  | cload _ _ _ ih => exact ⟨by simp; omega, rfl⟩
  | bin _ _ _ iha ihb =>
    refine ⟨by simp at ihb ⊢; omega, ?_⟩
    unfold binResult
    split
    · rfl
    · simp only [LX.ex_mk, LX.ty_mk, capExpr_ex, capExpr_ty, CC.typeof]; exact iha.2
  | lnot _ _ ih => exact ⟨ih.1, rfl⟩
  | bnot _ _ ih => exact ⟨ih.1, ih.2⟩
  | land _ _ _ _ iha ihb => exact ⟨by simp at ihb ⊢; omega, rfl⟩
  | lor _ _ _ _ iha ihb => exact ⟨by simp at ihb ⊢; omega, rfl⟩
  | cast _ _ _ ih => exact ⟨ih.1, rfl⟩
  | index _ _ _ _ _ ihp ihi => exact ⟨by simp at ihi ⊢; omega, rfl⟩
  | field _ _ _ ih => exact ⟨ih.1, rfl⟩
  | padd _ _ _ _ _ ihp ihi => exact ⟨by simp at ihi ⊢; omega, rfl⟩

/-! ## The dynamic statement -/

/-- Facts available while evaluating expressions of one function body. -/
structure XCtx (P : Prog) (ge : CC.CGenv) (ctx : LCtx) (m : Mem) (j : MemoryInjection)
    (cm : CC.Mem) : Prop where
  prog : ctx.prog = P
  ok : CtxOK ctx
  cenv : ge.genv_cenv = compositeEnv P
  scal : ∀ d ∈ P.structs, Scalars d.fields
  ids : ∀ d ∈ P.structs, (idents d.fields).Nodup
  consts : ∀ table ∈ P.consts, (table.words.size : Int) * 4 ≤ CC.Integers.Ptrofs.max_unsigned
  mem : memoryRel P j m cm
  const : ConstRel P ge j m cm
  fits : memoryFits P m

/-- Running the prelude from `le` and then evaluating the expression yields `w`. -/
def XRun (ge : CC.CGenv) (cm : CC.Mem) (ctx : LCtx) (lo hi : Nat) (le : CC.TempEnv)
    (pre : CC.Stmt) (ex : CC.Expr) (w : CC.Val) : Prop :=
  ∃ le', PRun ge cm pre le le' ∧ Frame ctx lo hi le le' ∧
    ∀ le'', Agree ctx lo hi le' le'' → CC.doEvalExpr ge CC.emptyEnv le'' cm ex = some w

/-- Conclusion for one expression. -/
def EOK (P : Prog) (ge : CC.CGenv) (cm : CC.Mem) (ctx : LCtx) (m : Mem) (j : MemoryInjection)
    (σ σ' : LSt) (r : LX) (le : CC.TempEnv) (v : Val) : Prop :=
  ValTyO m v r.ty ∧ valueFits P m v ∧
    ∃ w, valRel P m j v w ∧ XRun ge cm ctx σ.next σ'.next le r.pre r.ex w

section Run

variable {ge : CC.CGenv} {cm : CC.Mem} {ctx : LCtx}

theorem XRun.capture {lo : Nat} {σa : LSt} {le : CC.TempEnv} {r : LX} {w : CC.Val}
    (h : XRun ge cm ctx lo σa.next le r.pre r.ex w) (hlo : lo ≤ σa.next) :
    XRun ge cm ctx lo (σa.next + 1) le (capExpr ctx σa r).pre (capExpr ctx σa r).ex w := by
  obtain ⟨le', hp, hf, he⟩ := h
  refine ⟨le'.set (freshId ctx σa.next) w, ?_, ?_, ?_⟩
  · exact PRun.sequence hp (.set (he le' (Agree.refl _ _ _)))
  · exact Frame.trans (hf.mono (Nat.le_refl _) (Nat.le_refl _)) (Frame.set_fresh _ _ _) hlo
      (Nat.le_succ _) |>.mono (Nat.le_refl _) (Nat.le_refl _)
  · intro le'' hA
    simp only [capExpr_ex, CC.doEvalExpr]
    rw [hA _ (.inr ⟨σa.next, hlo, Nat.lt_succ_self _, rfl⟩), CC.PTree.gss]

/-- Two consecutive preludes, both of whose results are used afterwards. -/
theorem XRun.pair (hc : CtxOK ctx) {lo mid hi : Nat} (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    {le leA leB : CC.TempEnv} {preA preB : CC.Stmt} {exA exB : CC.Expr} {wA wB : CC.Val}
    (hA : PRun ge cm preA le leA) (hFA : Frame ctx lo mid le leA)
    (hEA : ∀ le'', Agree ctx lo mid leA le'' → CC.doEvalExpr ge CC.emptyEnv le'' cm exA = some wA)
    (hB : PRun ge cm preB leA leB) (hFB : Frame ctx mid hi leA leB)
    (hEB : ∀ le'', Agree ctx mid hi leB le'' → CC.doEvalExpr ge CC.emptyEnv le'' cm exB = some wB) :
    PRun ge cm (Priv.sequence preA preB) le leB ∧ Frame ctx lo hi le leB ∧
      ∀ le'', Agree ctx lo hi leB le'' →
        CC.doEvalExpr ge CC.emptyEnv le'' cm exA = some wA ∧
        CC.doEvalExpr ge CC.emptyEnv le'' cm exB = some wB := by
  refine ⟨PRun.sequence hA hB, Frame.trans hFA hFB hlm hmh, fun le'' hAg => ⟨?_, ?_⟩⟩
  · exact hEA _ (Agree.of_frame hc (hAg.mono (Nat.le_refl _) hmh) hFB (Nat.le_refl _))
  · exact hEB _ (hAg.mono hlm (Nat.le_refl _))

end Run

/-! ## Binary operators on values -/

theorem pointerType_tyO {o : Option Ty} (h : Priv.pointerType o = true) :
    ∃ X, tyO o = CC.tptr X := by
  rcases o with _ | ⟨_ | _ | t | _ | _⟩ <;> simp [Priv.pointerType] at h
  · exact ⟨_, rfl⟩
  · exact ⟨type t, rfl⟩

theorem pointerType_val {m : Mem} {v : Val} {o : Option Ty} (h : Priv.pointerType o = true)
    (hv : ValTyO m v o) : v = .null ∨ ∃ b off, v = .ptr b off := by
  rcases o with _ | ⟨_ | _ | t | _ | _⟩ <;> simp [Priv.pointerType] at h
  · exact .inl hv
  · rcases hv with h | ⟨b, off, rfl, _⟩
    · exact .inl h
    · exact .inr ⟨b, off, rfl⟩

theorem int_val {m : Mem} {v : Val} {o : Option Ty} (h : o.any Priv.intType = true)
    (hv : ValTyO m v o) :
    (o = some .u32 ∧ ∃ a, v = .u32 a) ∨ (o = some .u64 ∧ ∃ a, v = .u64 a) := by
  rcases o with _ | ⟨_ | _ | t | _ | _⟩ <;> simp [Priv.intType] at h
  · exact .inl ⟨rfl, hv⟩
  · exact .inr ⟨rfl, hv⟩

/-- Value-level correctness of a binary operator. -/
theorem bin_val {P : Prog} {m : Mem} {j : MemoryInjection} {cm : CC.Mem} (hrel : memoryRel P j m cm)
    (ce : CC.CompositeEnv) {op : BinOp} {oa ob : Option Ty} (hcond : binCond op oa ob = true)
    {va vb v : Val} {wa wb : CC.Val} (hta : ValTyO m va oa) (htb : ValTyO m vb ob)
    (hra : valRel P m j va wa) (hrb : valRel P m j vb wb)
    (hfa : valueFits P m va) (hfb : valueFits P m vb) (hv : evalBin m op va vb = some v) :
    ∃ w, valRel P m j v w ∧ valueFits P m v ∧
      ValTyO m v (if Priv.comparison op = true then some .u32 else oa) ∧
      (Priv.comparison op = true →
        CC.Cop.semBinaryOperation ce (Priv.binop op) wa (tyO oa) wb (tyO ob) cm >>=
          (fun x => CC.Cop.semCast x CC.tint CC.tuint cm) = some w) ∧
      (Priv.comparison op = false →
        CC.Cop.semBinaryOperation ce (Priv.binop op) wa (tyO oa) wb (tyO ob) cm = some w) := by
  unfold binCond at hcond
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
  rcases hcond with ⟨hint, rfl⟩ | ⟨⟨hop, hpa⟩, hpb⟩
  · rcases int_val hint hta with ⟨rfl, a, rfl⟩ | ⟨rfl, a, rfl⟩
    · obtain ⟨b, rfl⟩ := htb
      simp only [valRel] at hra hrb; subst hra hrb
      simp only [evalBin] at hv
      cases hc : Priv.comparison op
      · obtain ⟨r, rfl, hs⟩ := arith32 op a b v ce cm hv hc
        refine ⟨_, rfl, trivial, ?_, fun h => absurd h (by decide), fun _ => hs⟩
        simp only [Bool.false_eq_true, ite_false]; exact ⟨r, rfl⟩
      · obtain ⟨c, rfl, hs⟩ := cmp32 op a b v ce cm hv hc
        refine ⟨_, ofBool_rel c, trivial, ⟨_, rfl⟩, fun _ => ?_, fun h => absurd h (by decide)⟩
        simp only [tyO, type] at hs ⊢
        rw [hs]; show CC.Cop.semCast (CC.Val.ofBool c) CC.tint CC.tuint cm = _
        rw [cast_bool_tint_tuint, ofBool_rel]
    · obtain ⟨b, rfl⟩ := htb
      simp only [valRel] at hra hrb; subst hra hrb
      simp only [evalBin] at hv
      cases hc : Priv.comparison op
      · obtain ⟨r, rfl, hs⟩ := arith64 op a b v ce cm hv hc
        refine ⟨_, rfl, trivial, ?_, fun h => absurd h (by decide), fun _ => hs⟩
        simp only [Bool.false_eq_true, ite_false]; exact ⟨r, rfl⟩
      · obtain ⟨c, rfl, hs⟩ := cmp64 op a b v ce cm hv hc
        refine ⟨_, ofBool_rel c, trivial, ⟨_, rfl⟩, fun _ => ?_, fun h => absurd h (by decide)⟩
        simp only [tyO, type] at hs ⊢
        rw [hs]; show CC.Cop.semCast (CC.Val.ofBool c) CC.tint CC.tuint cm = _
        rw [cast_bool_tint_tuint, ofBool_rel]
  · obtain ⟨X, hX⟩ := pointerType_tyO hpa
    obtain ⟨Y, hY⟩ := pointerType_tyO hpb
    have hop' : op = .eq ∨ op = .ne := by simpa using hop
    have hcmp : Priv.comparison op = true := by rcases hop' with rfl | rfl <;> rfl
    have hshape : ∃ r, ptrEq m va vb = some r ∧ v = Val.ofBool (if op = .eq then r else !r) := by
      rcases pointerType_val hpa hta with h1 | ⟨b1, o1, h1⟩ <;>
        rcases pointerType_val hpb htb with h2 | ⟨b2, o2, h2⟩ <;> subst h1 h2 <;>
        rcases hop' with rfl | rfl <;> simp only [evalBin] at hv <;>
        (generalize hp : ptrEq m _ _ = o at hv; rcases o with _ | r <;> simp at hv <;>
          exact ⟨r, rfl, by simp [← hv]⟩)
    obtain ⟨r, hr, rfl⟩ := hshape
    have hs := ptr_cmp hrel hop' hr hra hrb hfa hfb X Y ce
    refine ⟨_, ofBool_rel _, trivial, ?_, fun _ => ?_, fun h => by rw [hcmp] at h; exact absurd h (by decide)⟩
    · simp only [hcmp, ite_true]; exact ⟨_, rfl⟩
    rw [hX, hY, hs]
    show CC.Cop.semCast (CC.Val.ofBool _) CC.tint CC.tuint cm = _
    rw [cast_bool_tint_tuint, ofBool_rel]

/-! ## Inversion of source evaluation -/

section Inv

variable {P : Prog} {env : Env} {m : Mem} {v : Val}

theorem evalE_cload_inv {g : String} {i : EmbC.Expr} (hv : evalE P env m (.cload g i) = some v) :
    ∃ c vi k w, P.findConst g = some c ∧ evalE P env m i = some vi ∧ vi.toIdx = some k ∧
      c.words[k]? = some w ∧ v = .u32 w := by
  simp only [evalE] at hv
  generalize hc : P.findConst g = oc at hv
  generalize hi : evalE P env m i = oi at hv
  rcases oc with _ | c <;> rcases oi with _ | vi <;> simp at hv
  generalize hk : vi.toIdx = ok at hv
  rcases ok with _ | k <;> simp at hv
  generalize hw : c.words[k]? = ow at hv
  rcases ow with _ | w <;> simp at hv
  exact ⟨c, vi, k, w, rfl, rfl, hk, hw, hv.symm⟩

theorem evalE_bin_inv {op : BinOp} {a b : EmbC.Expr} (hv : evalE P env m (.bin op a b) = some v) :
    ∃ va vb, evalE P env m a = some va ∧ evalE P env m b = some vb ∧ evalBin m op va vb = some v := by
  simp only [evalE] at hv
  generalize ha : evalE P env m a = oa at hv
  generalize hb : evalE P env m b = ob at hv
  rcases oa with _ | va <;> rcases ob with _ | vb <;> simp at hv
  exact ⟨va, vb, rfl, rfl, hv⟩

theorem evalE_lnot_inv {a : EmbC.Expr} (hv : evalE P env m (.lnot a) = some v) :
    ∃ x, evalE P env m a = some (.u32 x) ∧ v = Val.ofBool (decide (x = 0)) := by
  simp only [evalE] at hv
  generalize ha : evalE P env m a = oa at hv
  rcases oa with _ | ⟨x | _ | _ | _ | _ | _⟩ <;> simp at hv
  exact ⟨x, rfl, hv.symm⟩

theorem evalE_bnot_inv {a : EmbC.Expr} (hv : evalE P env m (.bnot a) = some v) :
    (∃ x, evalE P env m a = some (.u32 x) ∧ v = .u32 (~~~x)) ∨
      (∃ x, evalE P env m a = some (.u64 x) ∧ v = .u64 (~~~x)) := by
  simp only [evalE] at hv
  generalize ha : evalE P env m a = oa at hv
  rcases oa with _ | ⟨x | x | _ | _ | _ | _⟩ <;> simp at hv
  · exact .inl ⟨x, rfl, hv.symm⟩
  · exact .inr ⟨x, rfl, hv.symm⟩

theorem evalE_land_inv {a b : EmbC.Expr} (hv : evalE P env m (.land a b) = some v) :
    ∃ x, evalE P env m a = some (.u32 x) ∧
      ((x = 0 ∧ v = .u32 0) ∨
        (x ≠ 0 ∧ ∃ y, evalE P env m b = some (.u32 y) ∧ v = Val.ofBool (decide (y ≠ 0)))) := by
  simp only [evalE] at hv
  generalize ha : evalE P env m a = oa at hv
  rcases oa with _ | ⟨x | _ | _ | _ | _ | _⟩
  all_goals try (simp at hv; done)
  refine ⟨x, rfl, ?_⟩
  by_cases hx : x = 0
  · simp only [hx, ite_true, Option.some.injEq] at hv; exact .inl ⟨hx, hv.symm⟩
  · simp only [hx, ite_false] at hv
    generalize hb : evalE P env m b = ob at hv
    rcases ob with _ | ⟨y | _ | _ | _ | _ | _⟩
    all_goals try (simp at hv; done)
    simp only [Option.some.injEq] at hv
    exact .inr ⟨hx, y, rfl, hv.symm⟩

theorem evalE_lor_inv {a b : EmbC.Expr} (hv : evalE P env m (.lor a b) = some v) :
    ∃ x, evalE P env m a = some (.u32 x) ∧
      ((x ≠ 0 ∧ v = .u32 1) ∨
        (x = 0 ∧ ∃ y, evalE P env m b = some (.u32 y) ∧ v = Val.ofBool (decide (y ≠ 0)))) := by
  simp only [evalE] at hv
  generalize ha : evalE P env m a = oa at hv
  rcases oa with _ | ⟨x | _ | _ | _ | _ | _⟩
  all_goals try (simp at hv; done)
  refine ⟨x, rfl, ?_⟩
  by_cases hx : x = 0
  · have : ¬ (x ≠ 0) := fun h => h hx
    simp only [this, ite_false] at hv
    generalize hb : evalE P env m b = ob at hv
    rcases ob with _ | ⟨y | _ | _ | _ | _ | _⟩
    all_goals try (simp at hv; done)
    simp only [Option.some.injEq] at hv
    exact .inr ⟨hx, y, rfl, hv.symm⟩
  · simp only [hx, ne_eq, not_false_eq_true, ite_true, Option.some.injEq] at hv
    exact .inl ⟨hx, hv.symm⟩

theorem evalE_cast_inv {t : Ty} {a : EmbC.Expr} (hv : evalE P env m (.cast t a) = some v) :
    ∃ va, evalE P env m a = some va ∧ evalCast t va = some v := by
  simp only [evalE] at hv
  generalize ha : evalE P env m a = oa at hv
  rcases oa with _ | va <;> simp at hv
  exact ⟨va, rfl, hv⟩

theorem evalE_index_inv {p i : EmbC.Expr} (hv : evalE P env m (.index p i) = some v) :
    ∃ b off vi k, evalE P env m p = some (.ptr b off) ∧ evalE P env m i = some vi ∧
      vi.toIdx = some k ∧ m.loadArr b (off + k) = some v := by
  simp only [evalE] at hv
  generalize hp : evalE P env m p = op at hv
  generalize hi : evalE P env m i = oi at hv
  rcases op with _ | ⟨_ | _ | ⟨b, off⟩ | _ | _ | _⟩ <;> rcases oi with _ | vi <;> simp at hv
  generalize hk : vi.toIdx = ok at hv
  rcases ok with _ | k <;> simp at hv
  exact ⟨b, off, vi, k, rfl, rfl, hk, hv⟩

theorem evalE_field_inv {p : EmbC.Expr} {f : String} (hv : evalE P env m (.field p f) = some v) :
    ∃ b, evalE P env m p = some (.ptr b 0) ∧ m.loadField P b f = some v := by
  simp only [evalE] at hv
  generalize hp : evalE P env m p = op at hv
  rcases op with _ | ⟨_ | _ | ⟨b, off⟩ | _ | _ | _⟩ <;> simp at hv
  obtain ⟨rfl, hv⟩ := hv
  exact ⟨b, rfl, hv⟩

theorem evalE_padd_inv {p i : EmbC.Expr} (hv : evalE P env m (.padd p i) = some v) :
    ∃ b off vi k blk, evalE P env m p = some (.ptr b off) ∧ evalE P env m i = some vi ∧
      vi.toIdx = some k ∧ m.block? b = some blk ∧ blk.elem.isStruct = false ∧
      off + k ≤ blk.cells.size ∧ v = .ptr b (off + k) := by
  simp only [evalE] at hv
  generalize hp : evalE P env m p = op at hv
  generalize hi : evalE P env m i = oi at hv
  rcases op with _ | ⟨_ | _ | ⟨b, off⟩ | _ | _ | _⟩ <;> rcases oi with _ | vi <;> simp at hv
  generalize hk : vi.toIdx = ok at hv
  generalize hb : m.block? b = ob at hv
  rcases ok with _ | k <;> rcases ob with _ | blk <;> simp at hv
  exact ⟨b, off, vi, k, blk, rfl, rfl, hk, hb, hv.1, hv.2.1, hv.2.2.symm⟩

end Inv

/-! ## Reading represented memory -/

theorem rep_arr {P : Prog} {m : Mem} (hrep : Representable P m) {b : Nat} {blk : Block}
    (hb : m.block? b = some blk) (hns : blk.elem.isStruct = false) :
    ∀ (i : Nat) v, blk.cells[i]? = some v → cellTyped m v blk.elem := by
  obtain ⟨_, _, h⟩ := hrep.2 b blk hb
  split at h
  · rename_i s hs; rw [hs] at hns; cases hns
  · exact h

theorem rep_struct {P : Prog} {m : Mem} (hrep : Representable P m) {b : Nat} {blk : Block}
    (hb : m.block? b = some blk) {s : String} (he : blk.elem = .struct s) :
    ∃ d, P.findStruct s = some d ∧ blk.cells.size = d.fields.length ∧
      ∀ (i : Nat) f t v, d.fields[i]? = some (f, t) → blk.cells[i]? = some v → cellTyped m v t := by
  obtain ⟨_, _, h⟩ := hrep.2 b blk hb
  split at h
  · rename_i s' hs; rw [hs] at he; cases he; exact h
  · rename_i hn; exact absurd he (hn s)

theorem fits_cell {P : Prog} {m : Mem} (hfit : memoryFits P m) {b : Nat} {blk : Block}
    (hb : m.block? b = some blk) {i : Nat} {v : Val} (hv : blk.cells[i]? = some v) :
    valueFits P m v :=
  (hfit.2 b blk hb).2.2 v (by
    rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hv)

theorem fieldIn_get : ∀ {fs : List (String × Ty)} {f : String} {i : Nat} {t : Ty},
    fieldIn fs f = some (i, t) → fs[i]? = some (f, t)
  | [], _, _, _, h => by simp [fieldIn] at h
  | (g, u) :: rest, f, i, t, h => by
    simp only [fieldIn] at h
    split at h
    · rename_i hg; cases h; subst hg; rfl
    · generalize hr : fieldIn rest f = o at h
      rcases o with _ | ⟨i', t'⟩
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa using fieldIn_get hr

theorem lookupVar_mem {ctx : LCtx} {x : Var} {t : Ty} (h : lookupVar ctx x = some t) :
    (x, t) ∈ ctx.vars := by
  unfold lookupVar at h
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.find?_some hd
  have hdx : d.1 = x := by simpa using this
  have := List.mem_of_find?_eq_some hd
  rw [← hdx]; exact this

end EmbC.Clight.Proof
