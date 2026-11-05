import EmbC.Clight.Proof.Target
import EmbC.Clight.Proof.Program

/-!
# The expression and statement lowering as inductive relations

`Priv.lowerExpr`/`Priv.lowerStmt` are monadic functions.  Here their successful
runs are characterised once and for all by inductive relations `LE` and `LS`,
whose constructors carry every side condition the lowering checked.
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

abbrev LSt := Priv.LowerState
abbrev LX := Priv.LowerExpr
abbrev LCtx := Priv.LowerContext

def LSt.next (σ : LSt) : Nat := Priv.LowerState.next σ
def LSt.temps (σ : LSt) : List (CC.Ident × CC.Ty) := Priv.LowerState.temps σ
def LX.ty (e : LX) : Option Ty := Priv.LowerExpr.sourceType e
def LX.pre (e : LX) : CC.Stmt := Priv.LowerExpr.prelude e
def LX.ex (e : LX) : CC.Expr := Priv.LowerExpr.expr e
def LCtx.pfx (c : LCtx) : String := Priv.LowerContext.freshPrefix c
def LCtx.vars (c : LCtx) : List (Var × Ty) := Priv.LowerContext.variables c
def LCtx.prog (c : LCtx) : Prog := Priv.LowerContext.program c
def LCtx.res (c : LCtx) : Option Ty := Priv.LowerContext.result c

@[simp] theorem LX.ty_mk (a : Option Ty) (b : CC.Stmt) (c : CC.Expr) :
    LX.ty (Priv.LowerExpr.mk a b c) = a := rfl
@[simp] theorem LX.pre_mk (a : Option Ty) (b : CC.Stmt) (c : CC.Expr) :
    LX.pre (Priv.LowerExpr.mk a b c) = b := rfl
@[simp] theorem LX.ex_mk (a : Option Ty) (b : CC.Stmt) (c : CC.Expr) :
    LX.ex (Priv.LowerExpr.mk a b c) = c := rfl
@[simp] theorem LSt.next_mk (a : Nat) (b : List (CC.Ident × CC.Ty)) :
    LSt.next (Priv.LowerState.mk a b) = a := rfl
@[simp] theorem LSt.temps_mk (a : Nat) (b : List (CC.Ident × CC.Ty)) :
    LSt.temps (Priv.LowerState.mk a b) = b := rfl

/-- The `n`-th fresh temporary of a lowering context. -/
def freshId (ctx : LCtx) (n : Nat) : CC.Ident := CC.identOfString (ctx.pfx ++ toString n)

def capExpr (ctx : LCtx) (σ : LSt) (e : LX) : LX :=
  Priv.LowerExpr.mk e.ty (Priv.sequence e.pre (.Sset (freshId ctx σ.next) e.ex))
    (.Etempvar (freshId ctx σ.next) (CC.typeof e.ex))

def capState (ctx : LCtx) (σ : LSt) (e : LX) : LSt :=
  Priv.LowerState.mk (σ.next + 1) (σ.temps ++ [(freshId ctx σ.next, CC.typeof e.ex)])

def freshState (ctx : LCtx) (σ : LSt) (t : CC.Ty) : LSt :=
  Priv.LowerState.mk (σ.next + 1) (σ.temps ++ [(freshId ctx σ.next, t)])

theorem capture_eq (ctx : LCtx) (σ : LSt) (e : LX) :
    Priv.capture ctx e σ = .ok (capExpr ctx σ e, capState ctx σ e) := rfl

theorem fresh_eq (ctx : LCtx) (σ : LSt) (t : CC.Ty) :
    Priv.fresh ctx t σ = .ok (freshId ctx σ.next, freshState ctx σ t) := rfl

@[simp] theorem capExpr_ty (ctx : LCtx) (σ : LSt) (e : LX) : (capExpr ctx σ e).ty = e.ty := rfl
@[simp] theorem capExpr_pre (ctx : LCtx) (σ : LSt) (e : LX) :
    (capExpr ctx σ e).pre = Priv.sequence e.pre (.Sset (freshId ctx σ.next) e.ex) := rfl
@[simp] theorem capExpr_ex (ctx : LCtx) (σ : LSt) (e : LX) :
    (capExpr ctx σ e).ex = .Etempvar (freshId ctx σ.next) (CC.typeof e.ex) := rfl
@[simp] theorem capState_next (ctx : LCtx) (σ : LSt) (e : LX) :
    (capState ctx σ e).next = σ.next + 1 := rfl
@[simp] theorem freshState_next (ctx : LCtx) (σ : LSt) (t : CC.Ty) :
    (freshState ctx σ t).next = σ.next + 1 := rfl

def lookupVar (ctx : LCtx) (x : Var) : Option Ty := (ctx.vars.find? (·.1 == x)).map (·.2)

/-- The struct field accessed by `p->f`, when `p` has static type `ptr (struct s)`. -/
def fieldTy (ctx : LCtx) (pt : Option Ty) (f : String) : Option Ty :=
  match pt with
  | some (.ptr (.struct s)) =>
    match ctx.prog.findStruct s with
    | some d => (d.field? f).map (·.2)
    | none => none
  | _ => none

def binCond (op : BinOp) (a b : Option Ty) : Bool :=
  a.any Priv.intType && a == b ||
    (op == .eq || op == .ne) && Priv.pointerType a && Priv.pointerType b

def binResult (op : BinOp) (A B : LX) : LX :=
  if Priv.comparison op = true then
    Priv.LowerExpr.mk (some .u32) (Priv.sequence A.pre B.pre)
      (.Ecast (.Ebinop (Priv.binop op) A.ex B.ex CC.tint) CC.tuint)
  else
    Priv.LowerExpr.mk A.ty (Priv.sequence A.pre B.pre)
      (.Ebinop (Priv.binop op) A.ex B.ex (CC.typeof A.ex))

/-- Successful runs of `lowerExpr`. -/
inductive LE (ctx : LCtx) : LSt → EmbC.Expr → LX → LSt → Prop
  | var {σ x t} : lookupVar ctx x = some t →
      LE ctx σ (.var x) (Priv.LowerExpr.mk (some t) .Sskip
        (.Etempvar (CC.identOfString x) (type t))) σ
  | lit32 {σ v} : LE ctx σ (.lit32 v) (Priv.LowerExpr.mk (some .u32) .Sskip (.Econst_int v CC.tuint)) σ
  | named {σ n v} : LE ctx σ (.named n v)
      (Priv.LowerExpr.mk (some .u32) .Sskip (.Econst_int v CC.tuint)) σ
  | lit64 {σ v} : LE ctx σ (.lit64 v) (Priv.LowerExpr.mk (some .u64) .Sskip (.Econst_long v CC.tulong)) σ
  | null {σ} : LE ctx σ .null (Priv.LowerExpr.mk none .Sskip
      (.Ecast (.Econst_long 0 CC.tulong) (CC.tptr .Tvoid))) σ
  | cload {σ g i c ri σi} : ctx.prog.findConst g = some c → LE ctx σ i ri σi →
      ri.ty.any Priv.intType = true →
      LE ctx σ (.cload g i) (Priv.LowerExpr.mk (some .u32) (capExpr ctx σi ri).pre
        (.Ederef (.Ebinop .Oadd (.Evar (CC.identOfString g) (CC.tarray CC.tuint c.words.size))
          (capExpr ctx σi ri).ex (CC.tptr CC.tuint)) CC.tuint)) (capState ctx σi ri)
  | bin {σ op a b ra σa rb σb} : LE ctx σ a ra σa → LE ctx (capState ctx σa ra) b rb σb →
      binCond op ra.ty rb.ty = true →
      LE ctx σ (.bin op a b) (binResult op (capExpr ctx σa ra) (capExpr ctx σb rb))
        (capState ctx σb rb)
  | lnot {σ a ra σa} : LE ctx σ a ra σa → Priv.accepts .u32 ra.ty = true →
      LE ctx σ (.lnot a) (Priv.LowerExpr.mk (some .u32) ra.pre
        (.Ecast (.Eunop .Onotbool ra.ex CC.tint) CC.tuint)) σa
  | bnot {σ a ra σa} : LE ctx σ a ra σa → ra.ty.any Priv.intType = true →
      LE ctx σ (.bnot a) (Priv.LowerExpr.mk ra.ty ra.pre (.Eunop .Onotint ra.ex (CC.typeof ra.ex))) σa
  | land {σ a b ra σa rb σb} : LE ctx σ a ra σa → Priv.accepts .u32 ra.ty = true →
      LE ctx (capState ctx σa ra) b rb σb → Priv.accepts .u32 rb.ty = true →
      LE ctx σ (.land a b) (Priv.LowerExpr.mk (some .u32)
        (Priv.sequence (capExpr ctx σa ra).pre (.Sifthenelse (capExpr ctx σa ra).ex
          (Priv.sequence rb.pre (.Sset (freshId ctx σb.next) (Priv.boolExpr rb.ex)))
          (.Sset (freshId ctx σb.next) (.Econst_int 0 CC.tuint))))
        (.Etempvar (freshId ctx σb.next) CC.tuint)) (freshState ctx σb CC.tuint)
  | lor {σ a b ra σa rb σb} : LE ctx σ a ra σa → Priv.accepts .u32 ra.ty = true →
      LE ctx (capState ctx σa ra) b rb σb → Priv.accepts .u32 rb.ty = true →
      LE ctx σ (.lor a b) (Priv.LowerExpr.mk (some .u32)
        (Priv.sequence (capExpr ctx σa ra).pre (.Sifthenelse (capExpr ctx σa ra).ex
          (.Sset (freshId ctx σb.next) (.Econst_int 1 CC.tuint))
          (Priv.sequence rb.pre (.Sset (freshId ctx σb.next) (Priv.boolExpr rb.ex)))))
        (.Etempvar (freshId ctx σb.next) CC.tuint)) (freshState ctx σb CC.tuint)
  | cast {σ t a ra σa} : LE ctx σ a ra σa → ra.ty.any Priv.intType = true →
      Priv.intType t = true →
      LE ctx σ (.cast t a) (Priv.LowerExpr.mk (some t) ra.pre (.Ecast ra.ex (type t))) σa
  | index {σ p i rp σp ri σi t} : LE ctx σ p rp σp → rp.ty = some (.ptr t) → t.isStruct = false →
      LE ctx (capState ctx σp rp) i ri σi → ri.ty.any Priv.intType = true →
      LE ctx σ (.index p i) (Priv.LowerExpr.mk (some t)
        (Priv.sequence (capExpr ctx σp rp).pre (capExpr ctx σi ri).pre)
        (.Ederef (.Ebinop .Oadd (capExpr ctx σp rp).ex (capExpr ctx σi ri).ex (type (.ptr t)))
          (type t))) (capState ctx σi ri)
  | field {σ p f rp σp s t} : LE ctx σ p rp σp → rp.ty = some (.ptr (.struct s)) →
      fieldTy ctx rp.ty f = some t →
      LE ctx σ (.field p f) (Priv.LowerExpr.mk (some t) rp.pre
        (.Efield (.Ederef rp.ex (type (.struct s))) (CC.identOfString f) (type t))) σp
  | padd {σ p i rp σp ri σi t} : LE ctx σ p rp σp → rp.ty = some (.ptr t) → t.isStruct = false →
      LE ctx (capState ctx σp rp) i ri σi → ri.ty.any Priv.intType = true →
      LE ctx σ (.padd p i) (Priv.LowerExpr.mk (some (.ptr t))
        (Priv.sequence (capExpr ctx σp rp).pre (capExpr ctx σi ri).pre)
        (.Ebinop .Oadd (capExpr ctx σp rp).ex (capExpr ctx σi ri).ex (type (.ptr t))))
        (capState ctx σi ri)

/-! ## Monad inversion -/

section Monad

variable {α β : Type}

theorem bind_ok {x : Priv.LowerM α} {f : α → Priv.LowerM β} {σ : LSt} {r : β} {σ' : LSt}
    (h : (x >>= f) σ = .ok (r, σ')) : ∃ a σ₁, x σ = .ok (a, σ₁) ∧ f a σ₁ = .ok (r, σ') := by
  simp only [bind, StateT.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v hv; exact ⟨v.1, v.2, hv, h⟩

theorem pure_ok {a : α} {σ : LSt} {r : α} {σ' : LSt}
    (h : (pure a : Priv.LowerM α) σ = .ok (r, σ')) : r = a ∧ σ' = σ := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem throw_ok {e : String} {σ : LSt} {r : α} {σ' : LSt}
    (h : (throw e : Priv.LowerM α) σ = .ok (r, σ')) : False := by
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift,
    bind, Except.bind] at h
  all_goals cases h

theorem when_ok {c : Bool} {e : String} {σ : LSt} {u : PUnit} {σ' : LSt}
    (h : (if c = true then (throw e : Priv.LowerM PUnit) else pure PUnit.unit) σ = .ok (u, σ')) :
    c = false ∧ σ' = σ := by
  cases c
  · simp only [Bool.false_eq_true, ite_false] at h
    exact ⟨rfl, (pure_ok h).2⟩
  · simp only [ite_true] at h; exact (throw_ok h).elim

theorem bind_ok_iff {x : Priv.LowerM α} {f : α → Priv.LowerM β} {σ : LSt} {r : β} {σ' : LSt} :
    (x >>= f) σ = .ok (r, σ') ↔ ∃ a σ₁, x σ = .ok (a, σ₁) ∧ f a σ₁ = .ok (r, σ') := by
  constructor
  · exact bind_ok
  · rintro ⟨a, σ₁, h1, h2⟩
    simp only [bind, StateT.bind, Except.bind, h1]; exact h2

theorem pure_ok_iff {a : α} {σ : LSt} {r : α} {σ' : LSt} :
    (pure a : Priv.LowerM α) σ = .ok (r, σ') ↔ r = a ∧ σ' = σ := by
  constructor
  · exact pure_ok
  · rintro ⟨rfl, rfl⟩; rfl

theorem throw_ok_iff {e : String} {σ : LSt} {r : α} {σ' : LSt} :
    (throw e : Priv.LowerM α) σ = .ok (r, σ') ↔ False := ⟨throw_ok, False.elim⟩

theorem ite_apply' {c : Prop} [Decidable c] {x y : Priv.LowerM α} {σ : LSt} :
    (if c then x else y) σ = if c then x σ else y σ := by split <;> rfl

theorem ite_eq_iff' {γ : Type} {c : Prop} [Decidable c] {x y z : γ} :
    (if c then x else y) = z ↔ (c ∧ x = z) ∨ (¬c ∧ y = z) := by
  by_cases h : c <;> simp [h]

end Monad


/-! ## Inversion of the small checks -/

section Checks

variable {σ σ' : LSt}

theorem lookupVariable_ok {ctx : LCtx} {x : Var} {t : Ty}
    (h : Priv.lookupVariable ctx x σ = .ok (t, σ')) : lookupVar ctx x = some t ∧ σ' = σ := by
  unfold Priv.lookupVariable at h
  unfold lookupVar LCtx.vars
  generalize List.find? _ (Priv.LowerContext.variables ctx) = o at h
  rcases o with _ | ⟨y, t'⟩
  · exact (throw_ok h).elim
  · obtain ⟨rfl, rfl⟩ := pure_ok h
    simp

theorem pointerElement_ok {e : LX} {t : Ty}
    (h : Priv.pointerElement e σ = .ok (t, σ')) : e.ty = some (.ptr t) ∧ σ' = σ := by
  unfold Priv.pointerElement at h
  unfold LX.ty
  revert h
  rcases Priv.LowerExpr.sourceType e with _ | ⟨_ | _ | t' | _ | _⟩ <;> intro h
  all_goals first | exact (throw_ok h).elim | skip
  obtain ⟨rfl, rfl⟩ := pure_ok h; exact ⟨rfl, rfl⟩

theorem arrayElement_ok {e : LX} {t : Ty}
    (h : Priv.arrayElement e σ = .ok (t, σ')) :
    e.ty = some (.ptr t) ∧ t.isStruct = false ∧ σ' = σ := by
  unfold Priv.arrayElement at h
  obtain ⟨t', σ1, h1, h2⟩ := bind_ok h
  obtain ⟨he, rfl⟩ := pointerElement_ok h1
  simp only [ite_apply', ite_eq_iff', bind_ok_iff, throw_ok_iff, pure_ok_iff] at h2
  rcases h2 with ⟨_, _, _, h, _⟩ | ⟨hc, rfl, rfl⟩
  · exact h.elim
  · exact ⟨he, by simpa using hc, rfl⟩

theorem when_ok' {c : Bool} {e : String} {σ : LSt} {u : Unit} {σ' : LSt}
    (h : (if c = true then (throw e : Priv.LowerM Unit) else pure ()) σ = .ok (u, σ')) :
    c = false ∧ σ' = σ := by
  cases c
  · simp only [Bool.false_eq_true, ite_false] at h
    exact ⟨rfl, (pure_ok h).2⟩
  · simp only [ite_true] at h; exact (throw_ok h).elim

theorem requireType_ok {t : Ty} {e : LX} {u : Unit}
    (h : Priv.requireType t e σ = .ok (u, σ')) : Priv.accepts t e.ty = true ∧ σ' = σ := by
  unfold Priv.requireType at h
  have := when_ok' h
  refine ⟨?_, this.2⟩
  have h1 := this.1
  unfold LX.ty
  cases hh : Priv.accepts t (Priv.LowerExpr.sourceType e) <;> simp_all

theorem requireInteger_ok {e : LX} {u : Unit}
    (h : Priv.requireInteger e σ = .ok (u, σ')) : e.ty.any Priv.intType = true ∧ σ' = σ := by
  unfold Priv.requireInteger at h
  have := when_ok' h
  refine ⟨?_, this.2⟩
  have h1 := this.1
  unfold LX.ty
  cases hh : (Priv.LowerExpr.sourceType e).any Priv.intType <;> simp_all

theorem fieldType_ok {ctx : LCtx} {e : LX} {f : String} {t : Ty}
    (h : Priv.fieldType ctx e f σ = .ok (t, σ')) :
    (∃ s, e.ty = some (.ptr (.struct s))) ∧ fieldTy ctx e.ty f = some t ∧ σ' = σ := by
  unfold Priv.fieldType at h
  obtain ⟨t', σ1, h1, h2⟩ := bind_ok h
  obtain ⟨he, rfl⟩ := pointerElement_ok h1
  rw [he]
  revert h2
  rcases t' with _ | _ | _ | s | _ <;> intro h2
  all_goals first | exact (throw_ok h2).elim | skip
  refine ⟨⟨s, rfl⟩, ?_⟩
  unfold fieldTy LCtx.prog
  dsimp only at h2 ⊢
  generalize (Priv.LowerContext.program ctx).findStruct s = o at h2 ⊢
  rcases o with _ | d
  · exact (throw_ok h2).elim
  · dsimp only at h2 ⊢
    generalize d.field? f = o at h2 ⊢
    rcases o with _ | ⟨i, t''⟩
    · exact (throw_ok h2).elim
    · obtain ⟨rfl, rfl⟩ := pure_ok h2
      simp

end Checks


/-- Unfold monadic plumbing in a hypothesis `m σ = .ok (r, σ')`. -/
macro "lsimp" " at " h:ident : tactic =>
  `(tactic| simp only [bind_ok_iff, pure_ok_iff, throw_ok_iff, capture_eq, fresh_eq, ite_apply',
      ite_eq_iff', Except.ok.injEq, Prod.mk.injEq, false_and, and_false, exists_false, false_or,
      or_false, exists_eq_left, exists_eq_right, exists_and_left, exists_and_right,
      exists_eq_right_right, exists_eq_left'] at $h:ident)

theorem lowerExpr_LE (ctx : LCtx) : ∀ (e : EmbC.Expr) (σ : LSt) (r : LX) (σ' : LSt),
    Priv.lowerExpr ctx e σ = .ok (r, σ') → LE ctx σ e r σ' := by
  intro e
  induction e with
  | var x =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    obtain ⟨t, σ1, h1, h2⟩ := bind_ok h
    obtain ⟨ht, rfl⟩ := lookupVariable_ok h1
    obtain ⟨rfl, rfl⟩ := pure_ok h2
    exact .var ht
  | lit32 v => intro σ r σ' h; obtain ⟨rfl, rfl⟩ := pure_ok h; exact .lit32
  | lit64 v => intro σ r σ' h; obtain ⟨rfl, rfl⟩ := pure_ok h; exact .lit64
  | null => intro σ r σ' h; obtain ⟨rfl, rfl⟩ := pure_ok h; exact .null
  | named n v => intro σ r σ' h; obtain ⟨rfl, rfl⟩ := pure_ok h; exact .named
  | cload g i ih =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    generalize hc : (Priv.LowerContext.program ctx).findConst g = oc at h
    rcases oc with _ | c
    · lsimp at h
    lsimp at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨ri, σi, hi, rfl, rfl⟩, _, _, hreq, rfl, rfl⟩ := h
    obtain ⟨hint, rfl⟩ := requireInteger_ok hreq
    exact LE.cload hc (ih _ _ _ hi) hint
  | bin op a b iha ihb =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨_, _, ⟨ra, σa, ha, rfl, rfl⟩, _, _, ⟨rb, σb, hb, rfl, rfl⟩, hc, h⟩ := h
    have hc0 : (!(binCond op (LX.ty ra) (LX.ty rb))) ≠ true := hc
    have hc' : binCond op (LX.ty ra) (LX.ty rb) = true := by simpa using hc0
    have := LE.bin (iha _ _ _ ha) (ihb _ _ _ hb) hc'
    rcases h with ⟨hcmp, rfl, rfl⟩ | ⟨hcmp, rfl, rfl⟩
    · simp only [binResult, hcmp, ↓reduceIte] at this; exact this
    · simp only [binResult, hcmp, ↓reduceIte, Bool.false_eq_true] at this; exact this
  | lnot a ih =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨ra, σa, ha, _, _, hreq, rfl, rfl⟩ := h
    obtain ⟨hacc, rfl⟩ := requireType_ok hreq
    exact LE.lnot (ih _ _ _ ha) hacc
  | bnot a ih =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨ra, σa, ha, _, _, hreq, rfl, rfl⟩ := h
    obtain ⟨hacc, rfl⟩ := requireInteger_ok hreq
    exact LE.bnot (ih _ _ _ ha) hacc
  | land a b iha ihb =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨_, _, ⟨ra, σa, ha, rfl, rfl⟩, _, _, hra, rb, σb, hb, _, _, hrb, _, _, ⟨rfl, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨hacc, rfl⟩ := requireType_ok hra
    obtain ⟨hbcc, rfl⟩ := requireType_ok hrb
    exact LE.land (iha _ _ _ ha) hacc (ihb _ _ _ hb) hbcc
  | lor a b iha ihb =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨_, _, ⟨ra, σa, ha, rfl, rfl⟩, _, _, hra, rb, σb, hb, _, _, hrb, _, _, ⟨rfl, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨hacc, rfl⟩ := requireType_ok hra
    obtain ⟨hbcc, rfl⟩ := requireType_ok hrb
    exact LE.lor (iha _ _ _ ha) hacc (ihb _ _ _ hb) hbcc
  | cast t a ih =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨ra, σa, ha, _, _, hreq, hc, rfl, rfl⟩ := h
    obtain ⟨hacc, rfl⟩ := requireInteger_ok hreq
    exact LE.cast (ih _ _ _ ha) hacc (by simpa using hc)
  | index p i ihp ihi =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨_, _, ⟨rp, σp, hp, rfl, rfl⟩, t, _, hae, _, _, ⟨ri, σi, hi, rfl, rfl⟩, _, _, hreq,
      rfl, rfl⟩ := h
    obtain ⟨hpt, hns, rfl⟩ := arrayElement_ok hae
    obtain ⟨hint, rfl⟩ := requireInteger_ok hreq
    exact LE.index (ihp _ _ _ hp) hpt hns (ihi _ _ _ hi) hint
  | field p f ih =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨rp, σp, hp, t, _, hft, rfl, rfl⟩ := h
    obtain ⟨⟨s, hs⟩, hf, rfl⟩ := fieldType_ok hft
    have := LE.field (ih _ _ _ hp) hs hf
    have hs' : Priv.LowerExpr.sourceType rp = some (.ptr (.struct s)) := hs
    simp only [Priv.fieldExpr, hs']
    exact this
  | padd p i ihp ihi =>
    intro σ r σ' h
    simp only [Priv.lowerExpr] at h
    lsimp at h
    obtain ⟨_, _, ⟨rp, σp, hp, rfl, rfl⟩, t, _, hae, _, _, ⟨ri, σi, hi, rfl, rfl⟩, _, _, hreq,
      rfl, rfl⟩ := h
    obtain ⟨hpt, hns, rfl⟩ := arrayElement_ok hae
    obtain ⟨hint, rfl⟩ := requireInteger_ok hreq
    exact LE.padd (ihp _ _ _ hp) hpt hns (ihi _ _ _ hi) hint


/-! ## Arguments, destinations, kernel signatures, statements -/

/-- Successful runs of `lowerArgs`. -/
inductive LA (ctx : LCtx) : LSt → List EmbC.Expr → CC.Stmt → List LX → LSt → Prop
  | nil {σ} : LA ctx σ [] .Sskip [] σ
  | cons {σ e es r σ1 pre rs σ'} : LE ctx σ e r σ1 → LA ctx (capState ctx σ1 r) es pre rs σ' →
      LA ctx σ (e :: es) (Priv.sequence (capExpr ctx σ1 r).pre pre) (capExpr ctx σ1 r :: rs) σ'

/-- `checkArgs` succeeded. -/
inductive ArgsOK : List Ty → List LX → Prop
  | nil : ArgsOK [] []
  | cons {t ts a as} : Priv.accepts t a.ty = true → ArgsOK ts as → ArgsOK (t :: ts) (a :: as)

/-- `lowerDestination` succeeded. -/
def DstOK (ctx : LCtx) (dst : Option Var) (ret : Option Ty) (dst' : Option CC.Ident) : Prop :=
  (dst = none ∧ dst' = none) ∨
    ∃ x t, dst = some x ∧ lookupVar ctx x = some t ∧ ret = some t ∧ dst' = some (CC.identOfString x)

/-- `kernelTypes` succeeded. -/
inductive KT (P : Prog) : Ext → List LX → List CC.Ty → Option Ty → Prop
  | kvcalloc {t a} : t.isStruct = false → Priv.accepts .u64 a.ty = true →
      KT P (.kvcalloc t) [a] [CC.tulong] (some (.ptr t))
  | kzalloc {s} : KT P (.kzalloc s) [] [] (some (.ptr (.struct s)))
  | kvrealloc {t p n} : t.isStruct = false → Priv.accepts (.ptr t) p.ty = true →
      Priv.accepts .u64 n.ty = true →
      KT P (.kvrealloc t) [p, n] [type (.ptr t), CC.tulong] (some (.ptr t))
  | kvfree {p} : Priv.pointerType p.ty = true → KT P .kvfree [p] [CC.tptr .Tvoid] none
  | copyFromBpfptr {d s n} : Priv.accepts (.ptr .u32) d.ty = true →
      Priv.accepts .bpfptr s.ty = true → Priv.accepts .u64 n.ty = true →
      KT P .copyFromBpfptr [d, s, n] [type (.ptr .u32), type .bpfptr, CC.tulong] (some .u32)
  | signalPending : KT P .signalPending [] [] (some .u32)
  | condResched : KT P .condResched [] [] none

def funTy (fn : Fn) : CC.Ty :=
  .Tfunction (fn.params.map (fun p => type p.2)) ((fn.ret.map type).getD .Tvoid) CC.cc_default

/-- Successful runs of `lowerStmt`. -/
inductive LS (ctx : LCtx) : Nat → LSt → Stmt → CC.Stmt → LSt → Prop
  | skip {d σ} : LS ctx d σ .skip .Sskip σ
  | assign {d σ x e t r σ'} : lookupVar ctx x = some t → LE ctx σ e r σ' →
      Priv.accepts t r.ty = true →
      LS ctx d σ (.assign x e) (Priv.sequence r.pre (.Sset (CC.identOfString x) r.ex)) σ'
  | store {d σ p i e rp σp t ri σi re σ'} : LE ctx σ p rp σp → rp.ty = some (.ptr t) →
      t.isStruct = false → LE ctx (capState ctx σp rp) i ri σi → ri.ty.any Priv.intType = true →
      LE ctx (capState ctx σi ri) e re σ' → Priv.accepts t re.ty = true →
      LS ctx d σ (.store p i e) (Priv.sequence (capExpr ctx σp rp).pre
        (Priv.sequence (capExpr ctx σi ri).pre (Priv.sequence re.pre
          (.Sassign (.Ederef (.Ebinop .Oadd (capExpr ctx σp rp).ex (capExpr ctx σi ri).ex
            (type (.ptr t))) (type t)) re.ex)))) σ'
  | setField {d σ p f e rp σp s t re σ'} : LE ctx σ p rp σp → rp.ty = some (.ptr (.struct s)) →
      fieldTy ctx rp.ty f = some t → LE ctx (capState ctx σp rp) e re σ' →
      Priv.accepts t re.ty = true →
      LS ctx d σ (.setField p f e) (Priv.sequence (capExpr ctx σp rp).pre
        (Priv.sequence re.pre (.Sassign (.Efield (.Ederef (capExpr ctx σp rp).ex (type (.struct s)))
          (CC.identOfString f) (type t)) re.ex))) σ'
  | seq {d σ a b a' σ1 b' σ'} : LS ctx d σ a a' σ1 → LS ctx d σ1 b b' σ' →
      LS ctx d σ (.seq a b) (Priv.sequence a' b') σ'
  | ite {d σ c a b rc σ1 a' σ2 b' σ'} : LE ctx σ c rc σ1 → Priv.accepts .u32 rc.ty = true →
      LS ctx d σ1 a a' σ2 → LS ctx d σ2 b b' σ' →
      LS ctx d σ (.ite c a b) (Priv.sequence rc.pre (.Sifthenelse rc.ex a' b')) σ'
  | while {d σ c body rc σ1 b' σ'} : LE ctx σ c rc σ1 → Priv.accepts .u32 rc.ty = true →
      LS ctx (d + 1) σ1 body b' σ' →
      LS ctx d σ (.while c body) (.Sloop (Priv.sequence rc.pre
        (.Ssequence (.Sifthenelse rc.ex .Sskip .Sbreak) b')) .Sskip) σ'
  | call {d σ dst f args fn pre rs σ' dst'} : ctx.prog.findFn f = some fn →
      LA ctx σ args pre rs σ' → ArgsOK (fn.params.map (·.2)) rs → DstOK ctx dst fn.ret dst' →
      LS ctx d σ (.call dst f args) (Priv.sequence pre
        (.Scall dst' (.Evar (CC.identOfString f) (funTy fn)) (rs.map LX.ex))) σ'
  | ecall {d σ dst ext args pre rs σ' types ret dst'} : LA ctx σ args pre rs σ' →
      KT ctx.prog ext rs types ret → DstOK ctx dst ret dst' →
      LS ctx d σ (.ecall dst ext args) (Priv.sequence pre
        (.Sbuiltin dst' (kernelExternal ext) types (rs.map LX.ex))) σ'
  | ret0 {d σ} : ctx.res = none → LS ctx d σ (.ret none) (.Sreturn none) σ
  | ret1 {d σ e t r σ'} : ctx.res = some t → LE ctx σ e r σ' → Priv.accepts t r.ty = true →
      LS ctx d σ (.ret (some e)) (Priv.sequence r.pre (.Sreturn (some r.ex))) σ'
  | brk {d σ} : d ≠ 0 → LS ctx d σ .brk .Sbreak σ

end EmbC.Clight.Proof
