import EmbC.Clight.Proof.Expr

/-!
# Simulation of expression evaluation

A successful source evaluation of a lowered expression is matched by a run of
its Clight prelude followed by evaluation of the residual Clight expression.
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-! ## Generic facts about `XRun` -/

section XRunFacts

variable {ge : CC.CGenv} {cm : CC.Mem} {ctx : LCtx}

theorem XRun.atom {lo hi : Nat} {le : CC.TempEnv} {ex : CC.Expr} {w : CC.Val}
    (h : ∀ le'', Agree ctx lo hi le le'' → CC.doEvalExpr ge CC.emptyEnv le'' cm ex = some w) :
    XRun ge cm ctx lo hi le .Sskip ex w :=
  ⟨le, .skip le, Frame.refl _ _ _, h⟩

theorem XRun.map {lo hi : Nat} {le : CC.TempEnv} {pre : CC.Stmt} {ex ex' : CC.Expr} {w w' : CC.Val}
    (h : XRun ge cm ctx lo hi le pre ex w)
    (hF : ∀ le'', CC.doEvalExpr ge CC.emptyEnv le'' cm ex = some w →
      CC.doEvalExpr ge CC.emptyEnv le'' cm ex' = some w') :
    XRun ge cm ctx lo hi le pre ex' w' := by
  obtain ⟨le', hp, hf, he⟩ := h
  exact ⟨le', hp, hf, fun le'' hA => hF _ (he le'' hA)⟩

end XRunFacts

/-! ## Evaluation equations -/

section Ev

variable {ge : CC.CGenv} {e : CC.Env} {le : CC.TempEnv} {m : CC.Mem}

theorem ev_cast {a : CC.Expr} {ty : CC.Ty} {v : CC.Val} (h : CC.doEvalExpr ge e le m a = some v) :
    CC.doEvalExpr ge e le m (.Ecast a ty) = CC.Cop.semCast v (CC.typeof a) ty m := by
  simp only [CC.doEvalExpr, h]

theorem ev_unop {a : CC.Expr} {op : CC.Unop} {ty : CC.Ty} {v : CC.Val}
    (h : CC.doEvalExpr ge e le m a = some v) :
    CC.doEvalExpr ge e le m (.Eunop op a ty) = CC.Cop.semUnaryOperation op v (CC.typeof a) m := by
  simp only [CC.doEvalExpr, h]

theorem ev_binop {a b : CC.Expr} {op : CC.Binop} {ty : CC.Ty} {va vb : CC.Val}
    (ha : CC.doEvalExpr ge e le m a = some va) (hb : CC.doEvalExpr ge e le m b = some vb) :
    CC.doEvalExpr ge e le m (.Ebinop op a b ty) =
      CC.Cop.semBinaryOperation ge.genv_cenv op va (CC.typeof a) vb (CC.typeof b) m := by
  simp only [CC.doEvalExpr, ha, hb]

theorem ev_deref {a : CC.Expr} {ty : CC.Ty} {B : CC.Block} {o : CC.Integers.Ptrofs}
    (h : CC.doEvalExpr ge e le m a = some (.Vptr B o)) :
    CC.doEvalExpr ge e le m (.Ederef a ty) = CC.doDerefLoc ty m B o .Full := by
  simp only [CC.doEvalExpr, h]

theorem ev_field {a : CC.Expr} {i : CC.Ident} {ty : CC.Ty} {v : CC.Val} {loc : CC.Block}
    {ofs : CC.Integers.Ptrofs} {bf : CC.Bitfield}
    (h : CC.doEvalExpr ge e le m a = some v) (hl : CC.lvalOfField ge (CC.typeof a) i v = some (loc, ofs, bf)) :
    CC.doEvalExpr ge e le m (.Efield a i ty) = CC.doDerefLoc ty m loc ofs bf := by
  simp only [CC.doEvalExpr, h, hl]

theorem ev_evar_global {id : CC.Ident} {ty : CC.Ty} {B : CC.Block}
    (hs : CC.Genv.findSymbol ge.genv_genv id = some B) (hacc : CC.accessMode ty = .By_reference) :
    CC.doEvalExpr ge CC.emptyEnv le m (.Evar id ty) = some (.Vptr B CC.Integers.Ptrofs.zero) := by
  simp [CC.doEvalExpr, CC.lvalOfVar, CC.emptyEnv, hs, CC.doDerefLoc, hacc]

theorem ev_temp {id : CC.Ident} {ty : CC.Ty} : CC.doEvalExpr ge e le m (.Etempvar id ty) = le.get id := rfl

end Ev

/-! ## Small facts -/

theorem accepts_u32 {o : Option Ty} (h : Priv.accepts .u32 o = true) : o = some .u32 := by
  rcases o with _ | t
  · simp [Priv.accepts] at h
  · have : t = .u32 := by simpa [Priv.accepts] using h
    rw [this]

theorem findConst_mem {P : Prog} {g : String} {c : ConstDef} (h : P.findConst g = some c) :
    c ∈ P.consts ∧ c.name = g := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem findStruct_mem {P : Prog} {s : String} {d : StructDef} (h : P.findStruct s = some d) :
    d ∈ P.structs ∧ d.name = s := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem type_ptr (t : Ty) : type (.ptr t) = CC.tptr (type t) := rfl

theorem ptrofs_zero_eq : CC.Integers.Ptrofs.zero = CC.Integers.Ptrofs.repr 0 := rfl

theorem max_unsigned_eq : CC.Integers.Ptrofs.max_unsigned = 2 ^ 64 - 1 := by decide

theorem ptrofs_unsigned_repr' {z : CC.Z} (h0 : 0 ≤ z) (h1 : z ≤ CC.Integers.Ptrofs.max_unsigned) :
    CC.Integers.Ptrofs.unsigned (CC.Integers.Ptrofs.repr z) = z :=
  ptrofs_unsigned_repr h0 (by rw [max_unsigned_eq] at h1; exact Int.lt_of_le_sub_one h1)

theorem val_ofBool_inj {c d : Bool} (h : Val.ofBool c = Val.ofBool d) : c = d := by
  cases c <;> cases d <;> simp_all [Val.ofBool]

theorem boolExpr_eval {ge : CC.CGenv} {le : CC.TempEnv} {cm : CC.Mem} {ex : CC.Expr} {y : BitVec 32}
    (h : CC.doEvalExpr ge CC.emptyEnv le cm ex = some (.Vint y)) (ht : CC.typeof ex = CC.tuint) :
    CC.doEvalExpr ge CC.emptyEnv le cm (Priv.boolExpr ex) = some (CC.Val.ofBool (decide (y ≠ 0))) := by
  obtain ⟨c, hc, hs⟩ := cmp32 .ne y 0 (Val.ofBool (decide (y ≠ 0))) ge.genv_cenv cm rfl rfl
  have := val_ofBool_inj hc; subst this
  have h1 : CC.doEvalExpr ge CC.emptyEnv le cm (.Ebinop .One ex (.Econst_int 0 CC.tuint) CC.tint) =
      some (CC.Val.ofBool (decide (y ≠ 0))) := by
    rw [ev_binop h rfl, ht]; exact hs
  unfold Priv.boolExpr
  rw [ev_cast h1]; exact cast_bool_tint_tuint _ _

/-! ## Pointer arithmetic and array reads -/

theorem ptr_add_eval {P : Prog} {ge : CC.CGenv} {le : CC.TempEnv} {cm : CC.Mem}
    (hcenv : ge.genv_cenv = compositeEnv P) {pe ie : CC.Expr} {B : CC.Block} {s off k : Nat}
    {t : Ty} {wi : CC.Val}
    (hp : CC.doEvalExpr ge CC.emptyEnv le cm pe = some (.Vptr B (CC.Integers.Ptrofs.repr ((off * s : Nat) : CC.Z))))
    (hi : CC.doEvalExpr ge CC.emptyEnv le cm ie = some wi)
    (htp : CC.typeof pe = CC.tptr (type t)) (hidx : IdxW wi (CC.typeof ie) k)
    (hs : (s : CC.Z) = byteSize P t) :
    CC.doEvalExpr ge CC.emptyEnv le cm (.Ebinop .Oadd pe ie (CC.tptr (type t))) =
      some (.Vptr B (CC.Integers.Ptrofs.repr (((off + k) * s : Nat) : CC.Z))) := by
  rw [ev_binop hp hi, htp, add_ptr_idx ge.genv_cenv rfl B _ hidx cm, ptrofs_add_repr]
  congr 3
  rw [hcenv]
  show ((off * s : Nat) : CC.Z) + byteSize P t * (k : CC.Z) = (((off + k) * s : Nat) : CC.Z)
  rw [← hs]; push_cast; rw [Int.add_mul, Int.mul_comm (s : CC.Z) (k : CC.Z)]

theorem loadArr_inv {m : Mem} {b i : Nat} {v : Val} (h : m.loadArr b i = some v) :
    ∃ blk, m.block? b = some blk ∧ blk.elem.isStruct = false ∧ blk.cells[i]? = some v ∧
      v ≠ .undef := by
  unfold Mem.loadArr at h
  split at h
  · cases h
  · rename_i blk hblk
    split at h
    · cases h
    · rename_i hs
      split at h
      · cases h
      · cases h
      · rename_i v' hne hv
        cases h
        exact ⟨blk, hblk, by simpa using hs, hv, hne⟩

theorem arr_offset_fits {P : Prog} {m : Mem} (hfit : memoryFits P m) {b : Nat} {blk : Block}
    (hb : m.block? b = some blk) (hns : blk.elem.isStruct = false) {n : Nat}
    (hn : n ≤ blk.cells.size) :
    0 ≤ byteSize P blk.elem ∧ (n : CC.Z) * byteSize P blk.elem ≤ CC.Integers.Ptrofs.max_unsigned := by
  have hpos : 0 ≤ byteSize P blk.elem := by
    rw [byteSize_scalar P hns]; exact Int.le_of_lt (sizeChunk_chunkOf_pos _)
  refine ⟨hpos, ?_⟩
  have h2 := (hfit.2 b blk hb).2.1
  have hbs : blockByteSize P blk = (blk.cells.size : CC.Z) * byteSize P blk.elem := by
    simp [blockByteSize, hns]
  rw [hbs] at h2
  exact Int.le_trans (Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hn) hpos) h2

theorem lt_two64_of_le_max {z : CC.Z} (h : z ≤ CC.Integers.Ptrofs.max_unsigned) : z < 2 ^ 64 := by
  rw [max_unsigned_eq] at h; exact Int.lt_of_le_sub_one h

/-! ## Struct fields -/

theorem loadField_inv {P : Prog} {m : Mem} {b : Nat} {f : String} {v : Val}
    (h : m.loadField P b f = some v) :
    ∃ blk i t, m.fieldSlot P b f = some (blk, i, t) ∧ blk.cells[i]? = some v ∧ v ≠ .undef := by
  unfold Mem.loadField at h
  split at h
  · cases h
  · rename_i blk i t hs
    split at h
    · cases h
    · cases h
    · rename_i v' hne hv
      cases h
      exact ⟨blk, i, t, hs, hv, hne⟩

theorem fieldSlot_inv {P : Prog} {m : Mem} {b : Nat} {f : String} {blk : Block} {i : Nat} {t : Ty}
    (h : m.fieldSlot P b f = some (blk, i, t)) :
    ∃ s d, m.block? b = some blk ∧ blk.elem = .struct s ∧ P.findStruct s = some d ∧
      d.field? f = some (i, t) := by
  unfold Mem.fieldSlot at h
  split at h
  · cases h
  · rename_i blk' hblk
    split at h
    · rename_i s hs
      split at h
      · cases h
      · rename_i d hd
        split at h
        · cases h
        · rename_i i' t' hf
          cases h
          exact ⟨s, d, hblk, hs, hd, hf⟩
    · cases h

theorem sizeof_struct {ce : CC.CompositeEnv} {s : String} {co : CC.Composite}
    (h : ce.get (CC.identOfString s) = some co) :
    CC.sizeof ce (type (.struct s)) = co.co_sizeof := by
  simp [type, CC.sizeof, h]

/-- Everything known about one field of a live struct block. -/
theorem struct_field_info {P : Prog} {ge : CC.CGenv} {ctx : LCtx} {m : Mem} {j : MemoryInjection}
    {cm : CC.Mem} (hx : XCtx P ge ctx m j cm) {b : Nat} {blk : Block} {s : String} {d : StructDef}
    {f : String} {i : Nat} {t : Ty} {v : Val}
    (hblk : m.block? b = some blk) (he : blk.elem = .struct s) (hd : P.findStruct s = some d)
    (hf : d.field? f = some (i, t)) (hv : blk.cells[i]? = some v) :
    ∃ co off, (compositeEnv P).get (CC.identOfString s) = some co ∧
      CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members = .OK (off, .Full) ∧
      0 ≤ off ∧ off + CC.sizeChunk (chunkOf t) ≤ blockByteSize P blk ∧
      blockByteSize P blk ≤ CC.Integers.Ptrofs.max_unsigned ∧
      t.isStruct = false ∧ d.fields[i]? = some (f, t) ∧ cellRel P m j cm b off t v ∧
      cellTyped m v t := by
  obtain ⟨d', co, hd', hco, -, hmem, hcells⟩ := memRel_struct hx.mem hblk he
  rw [hd] at hd'; cases hd'
  have hfi := fieldIn_get hf
  obtain ⟨off, hoff, hcr⟩ := hcells i f t v hfi hv
  have hdm := (findStruct_mem hd).1
  obtain ⟨h0, hle⟩ := field_bounds hx.scal hx.ids hx.mem.1.1 hd hco hmem hfi hoff
  have hbs : blockByteSize P blk = co.co_sizeof := by
    simp only [blockByteSize, he, Ty.isStruct, ite_true, byteSize]
    exact sizeof_struct hco
  obtain ⟨d'', hd'', -, hty⟩ := rep_struct hx.fits.1 hblk he
  rw [hd] at hd''; cases hd''
  refine ⟨co, off, hco, hoff, h0, hbs ▸ hle, (hx.fits.2 b blk hblk).2.1, ?_, hfi,
    hcr, hty i f t v hfi hv⟩
  exact hx.scal d hdm _ (List.mem_of_getElem? hfi)

theorem field_lval {P : Prog} {ge : CC.CGenv} {le : CC.TempEnv} {cm : CC.Mem}
    (hcenv : ge.genv_cenv = compositeEnv P) {pe : CC.Expr} {B : CC.Block} {s f : String}
    {co : CC.Composite} {off : CC.Z}
    (hp : CC.doEvalExpr ge CC.emptyEnv le cm pe = some (.Vptr B (CC.Integers.Ptrofs.repr 0)))
    (hco : (compositeEnv P).get (CC.identOfString s) = some co)
    (hoff : CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members = .OK (off, .Full)) :
    CC.doEvalExpr ge CC.emptyEnv le cm (.Ederef pe (type (.struct s))) =
        some (.Vptr B (CC.Integers.Ptrofs.repr 0)) ∧
      CC.lvalOfField ge (CC.typeof (.Ederef pe (type (.struct s)))) (CC.identOfString f)
        (.Vptr B (CC.Integers.Ptrofs.repr 0)) = some (B, CC.Integers.Ptrofs.repr off, .Full) := by
  refine ⟨by rw [ev_deref hp]; rfl, ?_⟩
  simp only [CC.lvalOfField, CC.typeof, type, hcenv, hco, hoff, ptrofs_add_repr, Int.zero_add]

/-! ## The simulation statement -/

/-- Simulation of one lowered expression, for every matching temporary environment. -/
def ESim (P : Prog) (ge : CC.CGenv) (cm : CC.Mem) (ctx : LCtx) (m : Mem) (j : MemoryInjection)
    (env : Env) (σ : LSt) (e : EmbC.Expr) (r : LX) (σ' : LSt) : Prop :=
  ∀ le v, EnvRel ctx m j env le → evalE P env m e = some v → EOK P ge cm ctx m j σ σ' r le v

section Cases

variable {P : Prog} {ge : CC.CGenv} {cm : CC.Mem} {ctx : LCtx} {m : Mem} {j : MemoryInjection}
  {env : Env}

theorem esim_var (hx : XCtx P ge ctx m j cm) (hef : envFits P m env) {σ : LSt} {x : Var} {t : Ty}
    (ht : lookupVar ctx x = some t) :
    ESim P ge cm ctx m j env σ (.var x)
      (Priv.LowerExpr.mk (some t) .Sskip (.Etempvar (CC.identOfString x) (type t))) σ := by
  intro le v henv hv
  simp only [evalE] at hv
  obtain ⟨hty, w, hw, hrel⟩ := henv.get hv ht
  obtain ⟨t', _, hmem⟩ := env_get_mem henv.1 hv
  refine ⟨hty, hef _ hmem, w, hx.prog ▸ hrel, XRun.atom fun le'' hA => ?_⟩
  show le''.get _ = _
  rw [hA _ (.inl ⟨(x, t), lookupVar_mem ht, rfl⟩)]; exact hw

theorem esim_lit32 {σ : LSt} {v32 : BitVec 32} {e : EmbC.Expr} (he : ∀ env m, evalE P env m e = some (.u32 v32)) :
    ESim P ge cm ctx m j env σ e
      (Priv.LowerExpr.mk (some .u32) .Sskip (.Econst_int v32 CC.tuint)) σ := by
  intro le v _ hv
  rw [he] at hv; cases hv
  exact ⟨⟨v32, rfl⟩, trivial, _, rfl, XRun.atom fun _ _ => rfl⟩

theorem esim_lit64 {σ : LSt} {v64 : BitVec 64} :
    ESim P ge cm ctx m j env σ (.lit64 v64)
      (Priv.LowerExpr.mk (some .u64) .Sskip (.Econst_long v64 CC.tulong)) σ := by
  intro le v _ hv
  simp only [evalE, Option.some.injEq] at hv; subst hv
  exact ⟨⟨v64, rfl⟩, trivial, _, rfl, XRun.atom fun _ _ => rfl⟩

theorem esim_null {σ : LSt} :
    ESim P ge cm ctx m j env σ .null (Priv.LowerExpr.mk none .Sskip
      (.Ecast (.Econst_long 0 CC.tulong) (CC.tptr .Tvoid))) σ := by
  intro le v _ hv
  simp only [evalE, Option.some.injEq] at hv; subst hv
  exact ⟨rfl, trivial, _, rfl, XRun.atom fun _ _ => rfl⟩

theorem esim_lnot {σ σa : LSt} {a : EmbC.Expr} {ra : LX}
    (ha : ESim P ge cm ctx m j env σ a ra σa) (hacc : Priv.accepts .u32 ra.ty = true)
    (hst : CC.typeof ra.ex = tyO ra.ty) :
    ESim P ge cm ctx m j env σ (.lnot a) (Priv.LowerExpr.mk (some .u32) ra.pre
      (.Ecast (.Eunop .Onotbool ra.ex CC.tint) CC.tuint)) σa := by
  intro le v henv hv
  obtain ⟨x, hx, rfl⟩ := evalE_lnot_inv hv
  obtain ⟨-, -, w, hw, hrun⟩ := ha le _ henv hx
  simp only [valRel] at hw; subst hw
  refine ⟨⟨_, rfl⟩, trivial, CC.Val.ofBool (decide (x = 0)), ?_, hrun.map fun le'' h => ?_⟩
  · rw [ofBool_rel]; rfl
  · have h1 : CC.doEvalExpr ge CC.emptyEnv le'' cm (.Eunop .Onotbool ra.ex CC.tint) =
        some (CC.Val.ofBool (decide (x = 0))) := by
      rw [ev_unop h, hst, accepts_u32 hacc]; exact notbool32 _ _
    rw [LX.ex_mk, ev_cast h1]; exact cast_bool_tint_tuint _ _

theorem esim_bnot {σ σa : LSt} {a : EmbC.Expr} {ra : LX}
    (ha : ESim P ge cm ctx m j env σ a ra σa) (hint : ra.ty.any Priv.intType = true)
    (hst : CC.typeof ra.ex = tyO ra.ty) :
    ESim P ge cm ctx m j env σ (.bnot a) (Priv.LowerExpr.mk ra.ty ra.pre
      (.Eunop .Onotint ra.ex (CC.typeof ra.ex))) σa := by
  intro le v henv hv
  rcases evalE_bnot_inv hv with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · obtain ⟨hty, -, w, hw, hrun⟩ := ha le _ henv hx
    simp only [valRel] at hw; subst hw
    rcases int_val hint hty with ⟨ht, _⟩ | ⟨ht, _, h⟩
    · refine ⟨by simp only [LX.ty_mk, ht]; exact ⟨_, rfl⟩, trivial, _, rfl, hrun.map fun le'' h => ?_⟩
      rw [LX.ex_mk, ev_unop h, hst, ht]; exact notint32 _ _
    · cases h
  · obtain ⟨hty, -, w, hw, hrun⟩ := ha le _ henv hx
    simp only [valRel] at hw; subst hw
    rcases int_val hint hty with ⟨ht, _, h⟩ | ⟨ht, _⟩
    · cases h
    · refine ⟨by simp only [LX.ty_mk, ht]; exact ⟨_, rfl⟩, trivial, _, rfl, hrun.map fun le'' h => ?_⟩
      rw [LX.ex_mk, ev_unop h, hst, ht]; exact notint64 _ _

theorem esim_cast {σ σa : LSt} {t : Ty} {a : EmbC.Expr} {ra : LX}
    (ha : ESim P ge cm ctx m j env σ a ra σa) (hint : ra.ty.any Priv.intType = true)
    (ht : Priv.intType t = true) (hst : CC.typeof ra.ex = tyO ra.ty) :
    ESim P ge cm ctx m j env σ (.cast t a) (Priv.LowerExpr.mk (some t) ra.pre
      (.Ecast ra.ex (type t))) σa := by
  intro le v henv hv
  obtain ⟨va, hva, hc⟩ := evalE_cast_inv hv
  obtain ⟨hty, -, w, hw, hrun⟩ := ha le _ henv hva
  rcases int_val hint hty with ⟨hra, x, rfl⟩ | ⟨hra, x, rfl⟩ <;>
    simp only [valRel] at hw <;> subst hw <;>
    rcases t with _ | _ | _ | _ | _ <;> simp [Priv.intType] at ht <;>
    simp only [evalCast, Option.some.injEq] at hc <;> subst hc
  · exact ⟨⟨_, rfl⟩, trivial, _, rfl, hrun.map fun le'' h => by
      rw [LX.ex_mk, ev_cast h, hst, hra]; exact cast32_32 _ _⟩
  · exact ⟨⟨_, rfl⟩, trivial, _, rfl, hrun.map fun le'' h => by
      rw [LX.ex_mk, ev_cast h, hst, hra]; exact cast32_64 _ _⟩
  · exact ⟨⟨_, rfl⟩, trivial, _, rfl, hrun.map fun le'' h => by
      rw [LX.ex_mk, ev_cast h, hst, hra]; exact cast64_32 _ _⟩
  · exact ⟨⟨_, rfl⟩, trivial, _, rfl, hrun.map fun le'' h => by
      rw [LX.ex_mk, ev_cast h, hst, hra]; exact cast64_64 _ _⟩

/-- Two captured operands evaluated one after the other. -/
theorem esim_pair (hx : XCtx P ge ctx m j cm) {σ σa σb : LSt} {a b : EmbC.Expr} {ra rb : LX}
    (ha : ESim P ge cm ctx m j env σ a ra σa)
    (hb : ESim P ge cm ctx m j env (capState ctx σa ra) b rb σb)
    (h1 : σ.next ≤ σa.next) (h2 : σa.next + 1 ≤ σb.next)
    {le : CC.TempEnv} {va vb : Val} (henv : EnvRel ctx m j env le)
    (hva : evalE P env m a = some va) (hvb : evalE P env m b = some vb) :
    ValTyO m va ra.ty ∧ valueFits P m va ∧ ValTyO m vb rb.ty ∧ valueFits P m vb ∧
    ∃ wa wb leB, valRel P m j va wa ∧ valRel P m j vb wb ∧
      PRun ge cm (Priv.sequence (capExpr ctx σa ra).pre (capExpr ctx σb rb).pre) le leB ∧
      Frame ctx σ.next (σb.next + 1) le leB ∧
      ∀ le'', Agree ctx σ.next (σb.next + 1) leB le'' →
        CC.doEvalExpr ge CC.emptyEnv le'' cm (capExpr ctx σa ra).ex = some wa ∧
        CC.doEvalExpr ge CC.emptyEnv le'' cm (capExpr ctx σb rb).ex = some wb := by
  obtain ⟨tya, fa, wa, rela, runa⟩ := ha le va henv hva
  obtain ⟨leA, pA, fA, eA⟩ := runa.capture h1
  obtain ⟨tyb, fb, wb, relb, runb⟩ := hb leA vb (henv.frame hx.ok fA) hvb
  rw [capState_next] at runb
  obtain ⟨leB, pB, fB, eB⟩ := runb.capture h2
  obtain ⟨p, f, e⟩ := XRun.pair hx.ok (Nat.le_succ_of_le h1) (Nat.le_succ_of_le h2) pA fA eA pB fB eB
  exact ⟨tya, fa, tyb, fb, wa, wb, leB, rela, relb, p, f, e⟩

theorem esim_bin (hx : XCtx P ge ctx m j cm) {σ σa σb : LSt} {op : BinOp} {a b : EmbC.Expr}
    {ra rb : LX}
    (ha : ESim P ge cm ctx m j env σ a ra σa)
    (hb : ESim P ge cm ctx m j env (capState ctx σa ra) b rb σb)
    (h1 : σ.next ≤ σa.next) (h2 : σa.next + 1 ≤ σb.next)
    (hsa : CC.typeof ra.ex = tyO ra.ty) (hsb : CC.typeof rb.ex = tyO rb.ty)
    (hc : binCond op ra.ty rb.ty = true) :
    ESim P ge cm ctx m j env σ (.bin op a b)
      (binResult op (capExpr ctx σa ra) (capExpr ctx σb rb)) (capState ctx σb rb) := by
  intro le v henv hv
  obtain ⟨va, vb, hva, hvb, hbin⟩ := evalE_bin_inv hv
  obtain ⟨tya, fa, tyb, fb, wa, wb, leB, rela, relb, p, f, e⟩ :=
    esim_pair hx ha hb h1 h2 henv hva hvb
  obtain ⟨w, hw, hfit, hty, hcmp, hncmp⟩ :=
    bin_val hx.mem ge.genv_cenv hc tya tyb rela relb fa fb hbin
  have hrun : ∀ ex, (∀ le'', CC.doEvalExpr ge CC.emptyEnv le'' cm (capExpr ctx σa ra).ex = some wa →
      CC.doEvalExpr ge CC.emptyEnv le'' cm (capExpr ctx σb rb).ex = some wb →
      CC.doEvalExpr ge CC.emptyEnv le'' cm ex = some w) →
      XRun ge cm ctx σ.next (capState ctx σb rb).next le
        (Priv.sequence (capExpr ctx σa ra).pre (capExpr ctx σb rb).pre) ex w := by
    intro ex hex
    rw [capState_next]
    exact ⟨leB, p, f, fun le'' hA => hex le'' (e le'' hA).1 (e le'' hA).2⟩
  have tA : CC.typeof (capExpr ctx σa ra).ex = tyO ra.ty := hsa
  have tB : CC.typeof (capExpr ctx σb rb).ex = tyO rb.ty := hsb
  unfold binResult
  split
  · rename_i hcp
    refine ⟨by simpa [hcp] using hty, hfit, w, hx.prog ▸ hw, hrun _ fun le'' ea eb => ?_⟩
    have := hcmp hcp
    generalize hs : CC.Cop.semBinaryOperation _ _ _ _ _ _ _ = o at this
    rcases o with _ | x
    · cases this
    · have h1 : CC.doEvalExpr ge CC.emptyEnv le'' cm
          (.Ebinop (Priv.binop op) (capExpr ctx σa ra).ex (capExpr ctx σb rb).ex CC.tint) = some x := by
        rw [ev_binop ea eb, tA, tB]; exact hs
      rw [LX.ex_mk, ev_cast h1]; exact this
  · rename_i hcp
    have hcp' : Priv.comparison op = false := by simpa using hcp
    refine ⟨by simpa [hcp'] using hty, hfit, w, hx.prog ▸ hw, hrun _ fun le'' ea eb => ?_⟩
    rw [LX.ex_mk, ev_binop ea eb, tA, tB]; exact hncmp hcp'

theorem esim_land (hx : XCtx P ge ctx m j cm) {σ σa σb : LSt} {a b : EmbC.Expr} {ra rb : LX}
    (ha : ESim P ge cm ctx m j env σ a ra σa) (hacca : Priv.accepts .u32 ra.ty = true)
    (hb : ESim P ge cm ctx m j env (capState ctx σa ra) b rb σb)
    (haccb : Priv.accepts .u32 rb.ty = true)
    (h1 : σ.next ≤ σa.next) (h2 : σa.next + 1 ≤ σb.next)
    (hsa : CC.typeof ra.ex = tyO ra.ty) (hsb : CC.typeof rb.ex = tyO rb.ty) :
    ESim P ge cm ctx m j env σ (.land a b) (Priv.LowerExpr.mk (some .u32)
        (Priv.sequence (capExpr ctx σa ra).pre (.Sifthenelse (capExpr ctx σa ra).ex
          (Priv.sequence rb.pre (.Sset (freshId ctx σb.next) (Priv.boolExpr rb.ex)))
          (.Sset (freshId ctx σb.next) (.Econst_int 0 CC.tuint))))
        (.Etempvar (freshId ctx σb.next) CC.tuint)) (freshState ctx σb CC.tuint) := by
  intro le v henv hv
  obtain ⟨x, hx0, hcase⟩ := evalE_land_inv hv
  obtain ⟨-, -, wa, rela, runa⟩ := ha le _ henv hx0
  simp only [valRel] at rela; subst rela
  obtain ⟨leA, pA, fA, eA⟩ := runa.capture h1
  have tA : CC.typeof (capExpr ctx σa ra).ex = CC.tuint := by
    show CC.typeof ra.ex = _; rw [hsa, accepts_u32 hacca]; rfl
  have evA := eA leA (Agree.refl _ _ _)
  unfold EOK XRun; rw [freshState_next]
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hx1, y, hy, rfl⟩
  · refine ⟨⟨_, rfl⟩, trivial, _, rfl, leA.set (freshId ctx σb.next) (.Vint 0), ?_, ?_, ?_⟩
    · refine PRun.sequence pA (PRun.ite evA (by rw [tA]; exact boolVal32 _ _) ?_)
      simp only [ne_eq, not_true_eq_false, decide_false]
      exact .set rfl
    · exact Frame.trans fA ((Frame.set_fresh _ _ _).mono h2 (Nat.le_refl _)) (Nat.le_succ_of_le h1)
        (Nat.le_succ_of_le h2)
    · intro le'' hA
      rw [LX.ex_mk, ev_temp, hA _ (.inr ⟨σb.next, by omega, by omega, rfl⟩), CC.PTree.gss]
  · obtain ⟨-, -, wb, relb, runb⟩ := hb leA _ (henv.frame hx.ok fA) hy
    simp only [valRel] at relb; subst relb
    rw [capState_next] at runb
    obtain ⟨leB, pB, fB, eB⟩ := runb
    have tB : CC.typeof rb.ex = CC.tuint := by rw [hsb, accepts_u32 haccb]; rfl
    refine ⟨⟨_, rfl⟩, trivial, CC.Val.ofBool (decide (y ≠ 0)), ?_,
      leB.set (freshId ctx σb.next) (CC.Val.ofBool (decide (y ≠ 0))), ?_, ?_, ?_⟩
    · rw [src_ofBool, ofBool_rel]; rfl
    · refine PRun.sequence pA (PRun.ite evA (by rw [tA]; exact boolVal32 _ _) ?_)
      simp only [ne_eq, hx1, not_false_eq_true, decide_true, ite_true]
      exact PRun.sequence pB (.set (boolExpr_eval (eB leB (Agree.refl _ _ _)) tB))
    · exact Frame.trans fA (Frame.trans fB (Frame.set_fresh _ _ _) h2 (Nat.le_succ _))
        (Nat.le_succ_of_le h1) (Nat.le_succ_of_le h2)
    · intro le'' hA
      rw [LX.ex_mk, ev_temp, hA _ (.inr ⟨σb.next, by omega, by omega, rfl⟩), CC.PTree.gss]

theorem esim_lor (hx : XCtx P ge ctx m j cm) {σ σa σb : LSt} {a b : EmbC.Expr} {ra rb : LX}
    (ha : ESim P ge cm ctx m j env σ a ra σa) (hacca : Priv.accepts .u32 ra.ty = true)
    (hb : ESim P ge cm ctx m j env (capState ctx σa ra) b rb σb)
    (haccb : Priv.accepts .u32 rb.ty = true)
    (h1 : σ.next ≤ σa.next) (h2 : σa.next + 1 ≤ σb.next)
    (hsa : CC.typeof ra.ex = tyO ra.ty) (hsb : CC.typeof rb.ex = tyO rb.ty) :
    ESim P ge cm ctx m j env σ (.lor a b) (Priv.LowerExpr.mk (some .u32)
        (Priv.sequence (capExpr ctx σa ra).pre (.Sifthenelse (capExpr ctx σa ra).ex
          (.Sset (freshId ctx σb.next) (.Econst_int 1 CC.tuint))
          (Priv.sequence rb.pre (.Sset (freshId ctx σb.next) (Priv.boolExpr rb.ex)))))
        (.Etempvar (freshId ctx σb.next) CC.tuint)) (freshState ctx σb CC.tuint) := by
  intro le v henv hv
  obtain ⟨x, hx0, hcase⟩ := evalE_lor_inv hv
  obtain ⟨-, -, wa, rela, runa⟩ := ha le _ henv hx0
  simp only [valRel] at rela; subst rela
  obtain ⟨leA, pA, fA, eA⟩ := runa.capture h1
  have tA : CC.typeof (capExpr ctx σa ra).ex = CC.tuint := by
    show CC.typeof ra.ex = _; rw [hsa, accepts_u32 hacca]; rfl
  have evA := eA leA (Agree.refl _ _ _)
  unfold EOK XRun; rw [freshState_next]
  rcases hcase with ⟨hx1, rfl⟩ | ⟨rfl, y, hy, rfl⟩
  · refine ⟨⟨_, rfl⟩, trivial, _, rfl, leA.set (freshId ctx σb.next) (.Vint 1), ?_, ?_, ?_⟩
    · refine PRun.sequence pA (PRun.ite evA (by rw [tA]; exact boolVal32 _ _) ?_)
      simp only [ne_eq, hx1, not_false_eq_true, decide_true, ite_true]
      exact .set rfl
    · exact Frame.trans fA ((Frame.set_fresh _ _ _).mono h2 (Nat.le_refl _)) (Nat.le_succ_of_le h1)
        (Nat.le_succ_of_le h2)
    · intro le'' hA
      rw [LX.ex_mk, ev_temp, hA _ (.inr ⟨σb.next, by omega, by omega, rfl⟩), CC.PTree.gss]
  · obtain ⟨-, -, wb, relb, runb⟩ := hb leA _ (henv.frame hx.ok fA) hy
    simp only [valRel] at relb; subst relb
    rw [capState_next] at runb
    obtain ⟨leB, pB, fB, eB⟩ := runb
    have tB : CC.typeof rb.ex = CC.tuint := by rw [hsb, accepts_u32 haccb]; rfl
    refine ⟨⟨_, rfl⟩, trivial, CC.Val.ofBool (decide (y ≠ 0)), ?_,
      leB.set (freshId ctx σb.next) (CC.Val.ofBool (decide (y ≠ 0))), ?_, ?_, ?_⟩
    · rw [src_ofBool, ofBool_rel]; rfl
    · refine PRun.sequence pA (PRun.ite evA (by rw [tA]; exact boolVal32 _ _) ?_)
      simp only [ne_eq, not_true_eq_false, decide_false]
      exact PRun.sequence pB (.set (boolExpr_eval (eB leB (Agree.refl _ _ _)) tB))
    · exact Frame.trans fA (Frame.trans fB (Frame.set_fresh _ _ _) h2 (Nat.le_succ _))
        (Nat.le_succ_of_le h1) (Nat.le_succ_of_le h2)
    · intro le'' hA
      rw [LX.ex_mk, ev_temp, hA _ (.inr ⟨σb.next, by omega, by omega, rfl⟩), CC.PTree.gss]

/-- Common shape of a pointer operand of static type `ptr t`. -/
theorem ptr_operand {m : Mem} {P : Prog} {j : MemoryInjection} {b off : Nat} {t : Ty} {w : CC.Val}
    (hty : ValTyO m (.ptr b off) (some (.ptr t))) (hrel : valRel P m j (.ptr b off) w) :
    (∀ blk, m.block? b = some blk → blk.elem = t) ∧ b < m.blocks.size ∧
      off * j.stride b < 2 ^ 64 ∧
      w = .Vptr (j.block b) (CC.Integers.Ptrofs.repr ((off * j.stride b : Nat) : CC.Z)) := by
  rcases hty with h | ⟨b', off', h, _, hel⟩
  · cases h
  · cases h
    exact ⟨hel, hrel⟩

theorem esim_index (hx : XCtx P ge ctx m j cm) {σ σp σi : LSt} {p i : EmbC.Expr} {rp ri : LX}
    {t : Ty}
    (hp : ESim P ge cm ctx m j env σ p rp σp) (hpt : rp.ty = some (.ptr t))
    (hts : t.isStruct = false)
    (hi : ESim P ge cm ctx m j env (capState ctx σp rp) i ri σi)
    (hint : ri.ty.any Priv.intType = true)
    (h1 : σ.next ≤ σp.next) (h2 : σp.next + 1 ≤ σi.next)
    (hsp : CC.typeof rp.ex = tyO rp.ty) (hsi : CC.typeof ri.ex = tyO ri.ty) :
    ESim P ge cm ctx m j env σ (.index p i) (Priv.LowerExpr.mk (some t)
        (Priv.sequence (capExpr ctx σp rp).pre (capExpr ctx σi ri).pre)
        (.Ederef (.Ebinop .Oadd (capExpr ctx σp rp).ex (capExpr ctx σi ri).ex (type (.ptr t)))
          (type t))) (capState ctx σi ri) := by
  intro le v henv hv
  obtain ⟨b, off, vi, k, hvp, hvi, hk, hload⟩ := evalE_index_inv hv
  obtain ⟨tyb, fb, tyi, fi, wp, wi, leB, relp, reli, prun, fr, ev⟩ :=
    esim_pair hx hp hi h1 h2 henv hvp hvi
  rw [hpt] at tyb
  obtain ⟨hel, hb, hlt, rfl⟩ := ptr_operand tyb relp
  obtain ⟨k', hk', hidx⟩ := idxW_of reli tyi hint
  rw [hk] at hk'; cases hk'
  obtain ⟨blk, hblk, hns, hcell, hne⟩ := loadArr_inv hload
  have hte := hel blk hblk; subst hte
  have hstr := stride_eq hx.mem hblk
  have hlt' : off + k < blk.cells.size := (Array.getElem?_eq_some_iff.mp hcell).1
  obtain ⟨hnn, hmax⟩ := arr_offset_fits hx.fits hblk hns (Nat.le_of_lt hlt')
  obtain ⟨chunk, w, hacc, hl, hw⟩ := memRel_arr hx.mem hblk hns (off + k) v hcell
  have hck := chunk_eq_of_accessMode hns hacc; subst hck
  have hoff : (((off + k) * j.stride b : Nat) : CC.Z) = ((off + k : Nat) : CC.Z) * byteSize P blk.elem := by
    rw [Int.natCast_mul, hstr]
  refine ⟨ValTy.of_cellTyped (rep_arr hx.fits.1 hblk hns _ _ hcell) hne, fits_cell hx.fits hblk hcell,
    w, hw, ?_⟩
  rw [capState_next]
  refine ⟨leB, prun, fr, fun le'' hA => ?_⟩
  obtain ⟨ep, ei⟩ := ev le'' hA
  have hadd := ptr_add_eval hx.cenv ep ei (by show CC.typeof rp.ex = _; rw [hsp, hpt]; rfl)
    (by show IdxW wi (CC.typeof ri.ex) k; rw [hsi]; exact hidx) hstr
  rw [LX.ex_mk, type_ptr, ev_deref hadd, deref_scalar hns, hoff,
    ptrofs_unsigned_repr (Int.mul_nonneg (Int.natCast_nonneg _) hnn) (lt_two64_of_le_max hmax)]
  exact hl

theorem esim_padd (hx : XCtx P ge ctx m j cm) {σ σp σi : LSt} {p i : EmbC.Expr} {rp ri : LX}
    {t : Ty}
    (hp : ESim P ge cm ctx m j env σ p rp σp) (hpt : rp.ty = some (.ptr t))
    (hts : t.isStruct = false)
    (hi : ESim P ge cm ctx m j env (capState ctx σp rp) i ri σi)
    (hint : ri.ty.any Priv.intType = true)
    (h1 : σ.next ≤ σp.next) (h2 : σp.next + 1 ≤ σi.next)
    (hsp : CC.typeof rp.ex = tyO rp.ty) (hsi : CC.typeof ri.ex = tyO ri.ty) :
    ESim P ge cm ctx m j env σ (.padd p i) (Priv.LowerExpr.mk (some (.ptr t))
        (Priv.sequence (capExpr ctx σp rp).pre (capExpr ctx σi ri).pre)
        (.Ebinop .Oadd (capExpr ctx σp rp).ex (capExpr ctx σi ri).ex (type (.ptr t))))
        (capState ctx σi ri) := by
  intro le v henv hv
  obtain ⟨b, off, vi, k, blk, hvp, hvi, hk, hblk, hns, hle, rfl⟩ := evalE_padd_inv hv
  obtain ⟨tyb, fb, tyi, fi, wp, wi, leB, relp, reli, prun, fr, ev⟩ :=
    esim_pair hx hp hi h1 h2 henv hvp hvi
  rw [hpt] at tyb
  obtain ⟨hel, hb, hlt, rfl⟩ := ptr_operand tyb relp
  obtain ⟨k', hk', hidx⟩ := idxW_of reli tyi hint
  rw [hk] at hk'; cases hk'
  have hte := hel blk hblk; subst hte
  have hstr := stride_eq hx.mem hblk
  obtain ⟨hnn, hmax⟩ := arr_offset_fits hx.fits hblk hns hle
  have hoff : (((off + k) * j.stride b : Nat) : CC.Z) = ((off + k : Nat) : CC.Z) * byteSize P blk.elem := by
    rw [Int.natCast_mul, hstr]
  have hlt2 : (off + k) * j.stride b < 2 ^ 64 := by
    have := lt_two64_of_le_max hmax
    rw [← hoff] at this
    exact Int.ofNat_lt.mp (by simpa using this)
  refine ⟨.inr ⟨b, off + k, rfl, hb, hel⟩, ?_, _, ⟨hb, hlt2, rfl⟩, ?_⟩
  · simp only [valueFits, hblk, hns]
    exact ⟨by simpa using hle, hnn, hmax⟩
  rw [capState_next]
  refine ⟨leB, prun, fr, fun le'' hA => ?_⟩
  obtain ⟨ep, ei⟩ := ev le'' hA
  exact ptr_add_eval hx.cenv ep ei (by show CC.typeof rp.ex = _; rw [hsp, hpt]; rfl)
    (by show IdxW wi (CC.typeof ri.ex) k; rw [hsi]; exact hidx) hstr

theorem esim_cload (hx : XCtx P ge ctx m j cm) {σ σi : LSt} {g : String} {i : EmbC.Expr} {ri : LX}
    {c : ConstDef} (hc : ctx.prog.findConst g = some c)
    (hi : ESim P ge cm ctx m j env σ i ri σi) (hint : ri.ty.any Priv.intType = true)
    (h1 : σ.next ≤ σi.next) (hsi : CC.typeof ri.ex = tyO ri.ty) :
    ESim P ge cm ctx m j env σ (.cload g i) (Priv.LowerExpr.mk (some .u32) (capExpr ctx σi ri).pre
        (.Ederef (.Ebinop .Oadd (.Evar (CC.identOfString g) (CC.tarray CC.tuint c.words.size))
          (capExpr ctx σi ri).ex (CC.tptr CC.tuint)) CC.tuint)) (capState ctx σi ri) := by
  intro le v henv hv
  obtain ⟨c', vi, k, w, hc', hvi, hk, hw, rfl⟩ := evalE_cload_inv hv
  rw [hx.prog] at hc; rw [hc] at hc'; cases hc'
  obtain ⟨tyi, -, wi, reli, runi⟩ := hi le _ henv hvi
  obtain ⟨leI, pI, fI, eI⟩ := runi.capture h1
  obtain ⟨k', hk', hidx⟩ := idxW_of reli tyi hint
  rw [hk] at hk'; cases hk'
  obtain ⟨hcm, hname⟩ := findConst_mem hc
  obtain ⟨B, hsym, -, -, hload⟩ := hx.const c hcm
  rw [hname] at hsym
  have hlt : k < c.words.size := (Array.getElem?_eq_some_iff.mp hw).1
  have hmax := hx.consts c hcm
  have h4 : (k : CC.Z) * 4 ≤ CC.Integers.Ptrofs.max_unsigned :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr (Nat.le_of_lt hlt)) (by decide)) hmax
  refine ⟨⟨_, rfl⟩, trivial, _, rfl, ?_⟩
  rw [capState_next]
  refine ⟨leI, pI, fI, fun le'' hA => ?_⟩
  have hadd : CC.doEvalExpr ge CC.emptyEnv le'' cm
      (.Ebinop .Oadd (.Evar (CC.identOfString g) (CC.tarray CC.tuint c.words.size))
        (capExpr ctx σi ri).ex (CC.tptr CC.tuint)) =
      some (.Vptr B (CC.Integers.Ptrofs.repr ((k : CC.Z) * 4))) := by
    rw [ev_binop (ev_evar_global hsym rfl) (eI le'' hA),
      add_ptr_idx ge.genv_cenv rfl B _ (by show IdxW wi (CC.typeof ri.ex) k; rw [hsi]; exact hidx) cm,
      ptrofs_zero_eq, ptrofs_add_repr]
    congr 3
    show 0 + 4 * (k : CC.Z) = _
    rw [Int.zero_add, Int.mul_comm]
  rw [LX.ex_mk, ev_deref hadd, show CC.tuint = type .u32 from rfl, deref_scalar (t := .u32) rfl,
    ptrofs_unsigned_repr' (Int.mul_nonneg (Int.natCast_nonneg _) (by decide)) h4]
  exact hload k w hw

theorem esim_field (hx : XCtx P ge ctx m j cm) {σ σp : LSt} {p : EmbC.Expr} {f : String} {rp : LX}
    {s : String} {t : Ty}
    (hp : ESim P ge cm ctx m j env σ p rp σp) (hpt : rp.ty = some (.ptr (.struct s)))
    (hft : fieldTy ctx rp.ty f = some t) :
    ESim P ge cm ctx m j env σ (.field p f) (Priv.LowerExpr.mk (some t) rp.pre
        (.Efield (.Ederef rp.ex (type (.struct s))) (CC.identOfString f) (type t))) σp := by
  intro le v henv hv
  obtain ⟨b, hvp, hload⟩ := evalE_field_inv hv
  obtain ⟨typ, -, wp, relp, runp⟩ := hp le _ henv hvp
  rw [hpt] at typ
  obtain ⟨hel, hb, -, rfl⟩ := ptr_operand typ relp
  obtain ⟨blk, i, t', hslot, hcell, hne⟩ := loadField_inv hload
  obtain ⟨s', d, hblk, he, hd, hf⟩ := fieldSlot_inv hslot
  have := hel blk hblk; rw [he] at this; cases this
  have htt : t' = t := by
    rw [hpt] at hft
    simp only [fieldTy, hx.prog, hd, hf, Option.map_some, Option.some.injEq] at hft
    exact hft
  subst htt
  obtain ⟨co, off, hco, hoff, h0, hle, hmax, hts, -, ⟨chunk, w, hacc, hl, hw⟩, hcty⟩ :=
    struct_field_info hx hblk he hd hf hcell
  have hck := chunk_eq_of_accessMode hts hacc; subst hck
  refine ⟨ValTy.of_cellTyped hcty hne, fits_cell hx.fits hblk hcell, w, hw, runp.map fun le'' h => ?_⟩
  have h' : CC.doEvalExpr ge CC.emptyEnv le'' cm rp.ex = some (.Vptr (j.block b) (CC.Integers.Ptrofs.repr 0)) := by
    rw [h]; simp
  obtain ⟨e1, e2⟩ := field_lval hx.cenv h' hco hoff
  have hoffmax : off ≤ CC.Integers.Ptrofs.max_unsigned :=
    Int.le_trans (Int.le_add_of_nonneg_right (Int.le_of_lt (sizeChunk_chunkOf_pos _)))
      (Int.le_trans hle hmax)
  rw [LX.ex_mk, ev_field e1 e2, deref_scalar hts, ptrofs_unsigned_repr' h0 hoffmax]
  exact hl

end Cases

end EmbC.Clight.Proof

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-- Simulation of every lowered expression. -/
theorem expr_sim {P : Prog} {ge : CC.CGenv} {cm : CC.Mem} {ctx : LCtx} {m : Mem}
    {j : MemoryInjection} {env : Env} (hx : XCtx P ge ctx m j cm) (hef : envFits P m env) :
    ∀ {σ e r σ'}, LE ctx σ e r σ' → ESim P ge cm ctx m j env σ e r σ' := by
  intro σ e r σ' h
  induction h with
  | var ht => exact esim_var hx hef ht
  | lit32 => exact esim_lit32 fun _ _ => rfl
  | named => exact esim_lit32 fun _ _ => rfl
  | lit64 => exact esim_lit64
  | null => exact esim_null
  | cload hc hi hint ih =>
    exact esim_cload hx hc ih hint (LE_static hi).1 (LE_static hi).2
  | bin ha hb hc iha ihb =>
    have sa := LE_static ha; have sb := LE_static hb
    exact esim_bin hx iha ihb sa.1 (by simpa using sb.1) sa.2 sb.2 hc
  | lnot ha hacc ih => exact esim_lnot ih hacc (LE_static ha).2
  | bnot ha hint ih => exact esim_bnot ih hint (LE_static ha).2
  | land ha hacca hb haccb iha ihb =>
    have sa := LE_static ha; have sb := LE_static hb
    exact esim_land hx iha hacca ihb haccb sa.1 (by simpa using sb.1) sa.2 sb.2
  | lor ha hacca hb haccb iha ihb =>
    have sa := LE_static ha; have sb := LE_static hb
    exact esim_lor hx iha hacca ihb haccb sa.1 (by simpa using sb.1) sa.2 sb.2
  | cast ha hint ht ih => exact esim_cast ih hint ht (LE_static ha).2
  | index hp hpt hts hi hint ihp ihi =>
    have sp := LE_static hp; have si := LE_static hi
    exact esim_index hx ihp hpt hts ihi hint sp.1 (by simpa using si.1) sp.2 si.2
  | field hp hpt hft ih => exact esim_field hx ih hpt hft
  | padd hp hpt hts hi hint ihp ihi =>
    have sp := LE_static hp; have si := LE_static hi
    exact esim_padd hx ihp hpt hts ihi hint sp.1 (by simpa using si.1) sp.2 si.2

/-! ## Argument lists -/

/-- Evaluated, captured arguments. -/
inductive ArgsR (ge : CC.CGenv) (cm : CC.Mem) (P : Prog) (m : Mem) (j : MemoryInjection)
    (le : CC.TempEnv) : List LX → List Val → List CC.Val → Prop
  | nil : ArgsR ge cm P m j le [] [] []
  | cons {r rs v vs w ws} : CC.doEvalExpr ge CC.emptyEnv le cm r.ex = some w →
      ValTyO m v r.ty → valRel P m j v w → valueFits P m v →
      ArgsR ge cm P m j le rs vs ws → ArgsR ge cm P m j le (r :: rs) (v :: vs) (w :: ws)

theorem LA_static {ctx : LCtx} : ∀ {σ es pre rs σ'}, LA ctx σ es pre rs σ' → σ.next ≤ σ'.next := by
  intro σ es pre rs σ' h
  induction h with
  | nil => exact Nat.le_refl _
  | cons he _ ih =>
    have := (LE_static he).1
    simp only [capState_next] at ih
    omega

theorem evalArgs_cons_inv {P : Prog} {env : Env} {m : Mem} {e : EmbC.Expr} {es : List EmbC.Expr}
    {vs : List Val} (h : evalArgs P env m (e :: es) = some vs) :
    ∃ v vs', evalE P env m e = some v ∧ evalArgs P env m es = some vs' ∧ vs = v :: vs' := by
  simp only [evalArgs] at h
  generalize h1 : evalE P env m e = o1 at h
  generalize h2 : evalArgs P env m es = o2 at h
  rcases o1 with _ | v <;> rcases o2 with _ | vs' <;> simp at h
  exact ⟨v, vs', rfl, rfl, h.symm⟩

theorem args_sim {P : Prog} {ge : CC.CGenv} {cm : CC.Mem} {ctx : LCtx} {m : Mem}
    {j : MemoryInjection} {env : Env} (hx : XCtx P ge ctx m j cm) (hef : envFits P m env) :
    ∀ {σ es pre rs σ'}, LA ctx σ es pre rs σ' → ∀ {le vs}, EnvRel ctx m j env le →
      evalArgs P env m es = some vs →
      ∃ le' ws, PRun ge cm pre le le' ∧ Frame ctx σ.next σ'.next le le' ∧
        ∀ le'', Agree ctx σ.next σ'.next le' le'' → ArgsR ge cm P m j le'' rs vs ws := by
  intro σ es pre rs σ' h
  induction h with
  | nil =>
    intro le vs _ hv
    simp only [evalArgs, Option.some.injEq] at hv; subst hv
    exact ⟨le, [], .skip le, Frame.refl _ _ _, fun _ _ => .nil⟩
  | @cons σ e es r σ1 pre rs σ' he hrest ih =>
    intro le vs henv hv
    obtain ⟨v, vs', hve, hvs, rfl⟩ := evalArgs_cons_inv hv
    obtain ⟨ty, fit, w, rel, run⟩ := expr_sim hx hef he le v henv hve
    have s1 := (LE_static he).1
    have s2 := LA_static hrest
    simp only [capState_next] at s2
    obtain ⟨leA, pA, fA, eA⟩ := run.capture s1
    obtain ⟨le', ws, p', f', e'⟩ := ih (henv.frame hx.ok fA) hvs
    simp only [capState_next] at f' e'
    refine ⟨le', w :: ws, PRun.sequence pA p', Frame.trans fA f' (Nat.le_succ_of_le s1) s2,
      fun le'' hA => .cons ?_ ty rel fit (e' le'' (hA.mono (Nat.le_succ_of_le s1) (Nat.le_refl _)))⟩
    exact eA le'' (Agree.of_frame hx.ok (hA.mono (Nat.le_refl _) s2) f' (Nat.le_refl _))

/-- Casts applied to evaluated arguments are the identity. -/
inductive CastsOK (cm : CC.Mem) : List LX → List CC.Ty → List CC.Val → Prop
  | nil : CastsOK cm [] [] []
  | cons {r rs t ts w ws} : CC.Cop.semCast w (CC.typeof r.ex) t cm = some w →
      CastsOK cm rs ts ws → CastsOK cm (r :: rs) (t :: ts) (w :: ws)

theorem evalList_of {ge : CC.CGenv} {cm : CC.Mem} {P : Prog} {m : Mem} {j : MemoryInjection}
    {le : CC.TempEnv} : ∀ {rs vs ws ts}, ArgsR ge cm P m j le rs vs ws → CastsOK cm rs ts ws →
      CC.doEvalExprlist ge CC.emptyEnv le cm (rs.map LX.ex) ts = some ws
  | [], [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons he _ _ _ hr, .cons hc hcs => by
    simp only [List.map_cons, CC.doEvalExprlist, he, hc, evalList_of hr hcs]

theorem argsR_rel {ge : CC.CGenv} {cm : CC.Mem} {P : Prog} {m : Mem} {j : MemoryInjection}
    {le : CC.TempEnv} : ∀ {rs vs ws}, ArgsR ge cm P m j le rs vs ws → argsRel P m j vs ws
  | [], [], [], .nil => trivial
  | _ :: _, _ :: _, _ :: _, .cons _ _ hr _ hrs => ⟨hr, argsR_rel hrs⟩

end EmbC.Clight.Proof
