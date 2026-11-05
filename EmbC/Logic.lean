import EmbC.Semantics.Continuation
import EmbC.Kernel.Conformance

/-!
# EmbC: proof rules

`WP P s Q env st` establishes safe partial correctness of a statement.
`Outcome` is used only in proof postconditions; the operational machine
has exactly regular, call, and return states.
-/

namespace EmbC

variable {State : Type}

abbrev Post (P : Prog) (State : Type) := Outcome → Env → (KernelState P State) → Prop

/-- The continuation obligations for a statement's logical outcome.
Normal completion and break resume ordinary statements. Return values have
already been evaluated and are checked at the enclosing function boundary. -/
def Semantics.PostValid (P : Prog) (fuel : Nat) (R : Option Val → (KernelState P State) → Prop)
    (o : Outcome) (env : Env) (st : (KernelState P State)) (k : Semantics.Cont) : Prop :=
  match o with
  | .normal => Semantics.ValidFor P fuel R (.exec .skip env st k)
  | .brk => Semantics.ValidFor P fuel R (.exec .brk env st k)
  | .ret rv => match Semantics.returnTarget rv st k with
    | none => False
    | some target => Semantics.ValidFor P fuel R target

theorem Semantics.PostValid.down {P : Prog} {n m : Nat}
    {R : Option Val → (KernelState P State) → Prop} {o : Outcome} {env : Env}
    {st : (KernelState P State)} {k : Semantics.Cont}
    (h : Semantics.PostValid P m R o env st k) (hnm : n ≤ m) :
    Semantics.PostValid P n R o env st k := by
  cases o with
  | normal | brk => exact Semantics.ValidFor.down h hnm
  | ret rv =>
    simp only [Semantics.PostValid] at h ⊢
    cases hr : Semantics.returnTarget rv st k with
    | none => simp [hr] at h
    | some target =>
      exact Semantics.ValidFor.down (by simpa [hr] using h) hnm

/-- Continuation-based partial correctness over the sole operational machine. -/
def WP (P : Prog) (s : Stmt) (Q : (Post P State)) (env : Env) (st : (KernelState P State)) : Prop :=
  ∀ fuel (k : Semantics.Cont) (R : Option Val → (KernelState P State) → Prop),
    (∀ o env' st', Q o env' st' → Semantics.PostValid P fuel R o env' st' k) →
    Semantics.ValidFor P fuel R (.exec s env st k)

def FnSpec (P : Prog) (f : String) (pre : List Val → (KernelState P State) → Prop)
    (post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop) : Prop :=
  ∀ fuel vs st, pre vs st →
    match P.run fuel f vs st with
    | .timeout => True
    | .stuck => False
    | .ok (rv, st') => post vs st rv st'

/-! ## Statement rules -/

theorem WP.mono {P : Prog} {s : Stmt} {Q Q' : (Post P State)} {env : Env} {st : (KernelState P State)}
    (h : WP P s Q env st) (hq : ∀ o env' st', Q o env' st' → Q' o env' st') :
    WP P s Q' env st := by
  intro fuel k R hk
  exact h fuel k R (fun o env' st' ho => hk o env' st' (hq o env' st' ho))

/-- A primitive update completes by entering the ordinary `skip` state. -/
theorem WP.of_next {P : Prog} {s : Stmt} {Q : (Post P State)} {env : Env} {st : (KernelState P State)}
    (h : ∀ k, ∃ a env' st', Semantics.nextFor P (.exec s env st k) = some a ∧
      a.target = .exec .skip env' st' k ∧ Q .normal env' st') : WP P s Q env st := by
  intro fuel k R hk
  cases fuel with
  | zero => trivial
  | succ n =>
    obtain ⟨a, env', st', hn, ht, hq⟩ := h k
    apply Semantics.ValidFor.step hn
    rw [ht]
    exact (hk .normal env' st' hq).down (by omega)

theorem WP.skip {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)}
    (h : Q .normal env st) : WP P .skip Q env st := by
  intro fuel k R hk
  exact hk .normal env st h

theorem WP.brk {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)}
    (h : Q .brk env st) : WP P .brk Q env st := by
  intro fuel k R hk
  exact hk .brk env st h

theorem WP.retVoid {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)}
    (h : Q (.ret none) env st) : WP P (.ret none) Q env st := by
  intro fuel k R hk
  cases fuel with
  | zero => trivial
  | succ n =>
    have hp := hk (.ret none) env st h
    simp only [Semantics.PostValid] at hp
    cases ht : Semantics.returnTarget none st k with
    | none => simp [ht] at hp
    | some target =>
      simp only [ht] at hp
      apply Semantics.ValidFor.step (a := .silent target) (by simp [Semantics.nextFor, Semantics.nextCore, ht])
      exact hp.down (by omega)

theorem WP.ret {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {e : Expr}
    (h : match evalE P env st.mem e with
      | none => False
      | some v => Q (.ret (some v)) env st) :
    WP P (.ret (some e)) Q env st := by
  intro fuel k R hk
  cases fuel with
  | zero => trivial
  | succ n =>
    split at h
    · exact h.elim
    · rename_i v hv
      have hp := hk (.ret (some v)) env st h
      simp only [Semantics.PostValid] at hp
      cases ht : Semantics.returnTarget (some v) st k with
      | none => simp [ht] at hp
      | some target =>
        simp only [ht] at hp
        apply Semantics.ValidFor.step (a := .silent target) (by simp [Semantics.nextFor, Semantics.nextCore, hv, ht])
        exact hp.down (by omega)

theorem WP.assign {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {x : Var} {e : Expr}
    (h : match evalE P env st.mem e with
      | none => False
      | some v => match env.assign st.mem x v with
        | none => False
        | some env' => Q .normal env' st) :
    WP P (.assign x e) Q env st := by
  apply WP.of_next
  intro k
  split at h
  · exact h.elim
  · rename_i v hv
    split at h
    · exact h.elim
    · rename_i env' he
      exact ⟨.silent (.exec .skip env' st k), env', st,
        by simp [Semantics.nextFor, Semantics.nextCore, hv, he], rfl, h⟩

theorem WP.store {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {p i e : Expr}
    (h : match evalE P env st.mem p, evalE P env st.mem i, evalE P env st.mem e with
      | some (.ptr b off), some vi, some v => match vi.toIdx with
        | none => False
        | some k => match st.mem.storeArr b (off + k) v with
          | none => False
          | some m' => Q .normal env { st with mem := m' }
      | _, _, _ => False) :
    WP P (.store p i e) Q env st := by
  apply WP.of_next
  intro cont
  split at h
  · rename_i b off vi v hp hi he
    split at h
    · exact h.elim
    · rename_i k hk
      split at h
      · exact h.elim
      · rename_i m' hm
        exact ⟨.silent (.exec .skip env { st with mem := m' } cont),
          env, { st with mem := m' }, by simp [Semantics.nextFor, Semantics.nextCore, hp, hi, he, hk, hm], rfl, h⟩
  · exact h.elim

theorem WP.setField {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {p e : Expr} {f : String}
    (h : match evalE P env st.mem p, evalE P env st.mem e with
      | some (.ptr b off), some v => off = 0 ∧
        match st.mem.storeField P b f v with
        | none => False
        | some m' => Q .normal env { st with mem := m' }
      | _, _ => False) :
    WP P (.setField p f e) Q env st := by
  apply WP.of_next
  intro k
  split at h
  · rename_i b off v hp he
    obtain ⟨h0, h⟩ := h
    split at h
    · exact h.elim
    · rename_i m' hm
      exact ⟨.silent (.exec .skip env { st with mem := m' } k),
        env, { st with mem := m' }, by simp [Semantics.nextFor, Semantics.nextCore, hp, he, h0, hm], rfl, h⟩
  · exact h.elim

theorem WP.seq {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {a b : Stmt}
    (h : WP P a (fun o env' st' => match o with
      | .normal => WP P b Q env' st'
      | o => Q o env' st') env st) : WP P (.seq a b) Q env st := by
  intro fuel k R hk
  cases fuel with
  | zero => trivial
  | succ n =>
    apply Semantics.ValidFor.step (a := .silent (.exec a env st (.seq b k))) rfl
    apply h n (.seq b k) R
    intro o env' st' ho
    cases o with
    | normal =>
      cases n with
      | zero => trivial
      | succ n =>
        apply Semantics.ValidFor.step (a := .silent (.exec b env' st' k)) rfl
        exact ho n k R (fun o e s hq => (hk o e s hq).down (by omega))
    | brk =>
      cases n with
      | zero => trivial
      | succ n =>
        apply Semantics.ValidFor.step (a := .silent (.exec .brk env' st' k)) rfl
        exact (hk _ _ _ ho).down (by omega)
    | ret rv =>
      exact (hk _ _ _ ho).down (by omega)

theorem WP.ite {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {c : Expr} {a b : Stmt}
    (h : match evalE P env st.mem c with
      | some (.u32 v) => (v ≠ 0 → WP P a Q env st) ∧ (v = 0 → WP P b Q env st)
      | _ => False) : WP P (.ite c a b) Q env st := by
  intro fuel k R hk
  cases fuel with
  | zero => trivial
  | succ n =>
    split at h
    · rename_i v hc
      by_cases hz : v = 0
      · apply Semantics.ValidFor.step (a := .silent (.exec b env st k))
          (by simp only [Semantics.nextFor, Semantics.nextCore, hc, hz, ↓reduceIte])
        exact h.2 hz n k R (fun o e s hq => (hk o e s hq).down (by omega))
      · apply Semantics.ValidFor.step (a := .silent (.exec a env st k))
          (by simp only [Semantics.nextFor, Semantics.nextCore, hc, hz, ↓reduceIte])
        exact h.1 hz n k R (fun o e s hq => (hk o e s hq).down (by omega))
    · exact h.elim

theorem WP.while {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {c : Expr} {body : Stmt}
    (I : Env → (KernelState P State) → Prop) (h0 : I env st)
    (hstep : ∀ env st, I env st → match evalE P env st.mem c with
      | some (.u32 v) => (v = 0 → Q .normal env st) ∧
        (v ≠ 0 → WP P body (fun o env' st' => match o with
          | .normal => I env' st'
          | .brk => Q .normal env' st'
          | .ret r => Q (.ret r) env' st') env st)
      | _ => False) : WP P (.while c body) Q env st := by
  intro fuel k R hk
  induction fuel generalizing env st with
  | zero => trivial
  | succ n ih =>
    have hs := hstep env st h0
    split at hs
    · rename_i v hc
      by_cases hz : v = 0
      · apply Semantics.ValidFor.step (a := .silent (.exec .skip env st k))
          (by simp only [Semantics.nextFor, Semantics.nextCore, hc, hz, ↓reduceIte])
        exact (hk _ _ _ (hs.1 hz)).down (by omega)
      · apply Semantics.ValidFor.step (a := .silent (.exec body env st (.loop c body k)))
          (by simp only [Semantics.nextFor, Semantics.nextCore, hc, hz, ↓reduceIte])
        apply hs.2 hz n (.loop c body k) R
        intro o env' st' ho
        cases o with
        | normal =>
          cases n with
          | zero => trivial
          | succ n =>
            apply Semantics.ValidFor.step (a := .silent (.exec (.while c body) env' st' k)) rfl
            exact (ih ho (fun o e s hq => (hk o e s hq).down (by omega))).down (by omega)
        | brk =>
          cases n with
          | zero => trivial
          | succ n =>
            apply Semantics.ValidFor.step (a := .silent (.exec .skip env' st' k)) rfl
            exact (hk _ _ _ ho).down (by omega)
        | ret rv => exact (hk _ _ _ ho).down (by omega)
    · exact hs.elim

theorem WP.ecall {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {dst : Option Var} {f : Ext}
    {args : List Expr}
    (h : match evalArgs P env st.mem args with
      | none => False
      | some vs => match Ext.run P f vs st with
        | none => False
        | some (rv, st') => match assignDst env st'.mem dst rv with
          | none => False
          | some env' => Q .normal env' st') : WP P (.ecall dst f args) Q env st := by
  intro fuel k R hk
  cases fuel with
  | zero => trivial
  | succ n =>
    split at h
    · exact h.elim
    · rename_i vs ha
      apply Semantics.ValidFor.step
        (a := .silent (.call (.external f) vs st (.call dst env k)))
        (by simp [Semantics.nextFor, Semantics.nextCore, ha])
      cases n with
      | zero => trivial
      | succ n =>
        split at h
        · exact h.elim
        · rename_i rv st' hr
          apply Semantics.ValidFor.step
            (a := .external f vs st rv st' (.returned rv st' (.call dst env k)))
            (by simp [Semantics.Action.target, Semantics.nextFor, Semantics.nextCore, hr])
          cases n with
          | zero => trivial
          | succ n =>
            split at h
            · exact h.elim
            · rename_i env' he
              apply Semantics.ValidFor.step (a := .silent (.exec .skip env' st' k))
                (by simp [Semantics.Action.target, Semantics.nextFor, Semantics.nextCore, he])
              exact (hk _ _ _ h).down (by omega)

/-- A kernel-call proof uses the public contract, without inspecting the private oracle state. -/
theorem WP.ecall_spec {P : Prog}
    {Q : Post P State} {env : Env} {st : KernelState P State}
    {dst : Option Var} {f : Ext} {args : List Expr} {vs : List Val}
    (ha : evalArgs P env st.mem args = some vs)
    (hd : Kernel.Defined P ⟨f, vs, st.mem⟩)
    (h : ∀ rv (after : KernelState P State),
      Oracle.Returns P ⟨f, vs, st.mem⟩ ⟨rv, after.mem⟩ →
      match assignDst env after.mem dst rv with
      | none => False
      | some env' => Q .normal env' after) :
    WP P (.ecall dst f args) Q env st := by
  apply WP.ecall
  obtain ⟨rv, after, hr⟩ := Ext.run_defined hd
  simpa only [ha, hr] using h rv after (Ext.run_spec hr)

theorem WP.call {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {dst : Option Var} {f : String}
    {args : List Expr}
    {pre : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop}
    (hspec : FnSpec P f pre post)
    (h : match evalArgs P env st.mem args with
      | none => False
      | some vs => pre vs st ∧ ∀ rv st', post vs st rv st' →
          match assignDst env st'.mem dst rv with
          | none => False
          | some env' => Q .normal env' st') : WP P (.call dst f args) Q env st := by
  intro fuel k R hk
  cases fuel with
  | zero => trivial
  | succ n =>
    split at h
    · exact h.elim
    · rename_i vs ha
      obtain ⟨hp, hpost⟩ := h
      apply Semantics.ValidFor.step (a := .silent (.call (.internal f) vs st (.call dst env k)))
        (by simp [Semantics.nextFor, Semantics.nextCore, ha])
      exact Semantics.ValidFor.append_call (c := Semantics.initial f vs st)
        (fun fuel => hspec fuel vs st hp) (by
          intro rv st' hr
          cases n with
          | zero => trivial
          | succ n =>
            have ho := hpost rv st' hr
            split at ho
            · exact ho.elim
            · rename_i env' he
              apply Semantics.ValidFor.step (a := .silent (.exec .skip env' st' k))
                (by simp [Semantics.nextFor, Semantics.nextCore, he])
              exact (hk _ _ _ ho).down (by omega))

/-! ## Function specifications -/

def retPost (rt : Option Ty) (R : Option Val → (KernelState P State) → Prop) : (Post P State) := fun o _ st' =>
  match o, rt with
  | .normal, none => R none st'
  | .ret none, none => R none st'
  | .ret (some v), some t => st'.mem.hasTy v t = true ∧ R (some v) st'
  | _, _ => False

theorem Semantics.ValidFor.final {P : Prog} {n : Nat} {R : Option Val → (KernelState P State) → Prop}
    {rv : Option Val} {st : (KernelState P State)} (h : R rv st) :
    Semantics.ValidFor P n R (.returned rv st .stop) := by
  cases n <;> simp [Semantics.ValidFor, Semantics.run, Semantics.runCore, Semantics.nextFor, Semantics.nextCore, h]

theorem FnSpec.intro {P : Prog} {f : String} {fn : Fn}
    {pre : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop}
    (hf : P.findFn f = some fn)
    (h : ∀ vs st, pre vs st → ∃ penv, bindParams st.mem fn.params vs = some penv ∧
      WP P fn.body (retPost fn.ret (post vs st)) (penv ++ initLocals fn.locals) st) :
    FnSpec P f pre post := by
  intro fuel vs st hp
  obtain ⟨penv, hb, hw⟩ := h vs st hp
  change Semantics.ValidFor P fuel (post vs st) (Semantics.initial f vs st)
  cases fuel with
  | zero => trivial
  | succ n =>
    apply Semantics.ValidFor.step
      (a := .silent (.exec fn.body (penv ++ initLocals fn.locals) st (.function fn.ret .stop)))
      (by simp [Semantics.initial, Semantics.nextFor, Semantics.nextCore, hf, hb])
    apply hw n (.function fn.ret .stop) (post vs st)
    intro o env' st' ho
    cases o with
    | normal =>
      cases ht : fn.ret with
      | some t => simp [retPost, ht] at ho
      | none =>
        cases n with
        | zero => trivial
        | succ n =>
          apply Semantics.ValidFor.step (a := .silent (.returned none st' .stop))
            (by simp [Semantics.nextFor, Semantics.nextCore])
          exact Semantics.ValidFor.final (by simpa [retPost, ht] using ho)
    | brk => simp [retPost] at ho
    | ret rv =>
      cases rv with
      | none =>
        cases ht : fn.ret with
        | none =>
          have hp : post vs st none st' := by simpa [retPost, ht] using ho
          simpa [Semantics.PostValid, Semantics.returnTarget, Semantics.Cont.returnCont, ht]
            using (Semantics.ValidFor.final (n := n) hp)
        | some t => simp [retPost, ht] at ho
      | some v =>
        cases ht : fn.ret with
        | none => simp [retPost, ht] at ho
        | some t =>
          have hp : st'.mem.hasTy v t = true ∧ post vs st (some v) st' := by
            simpa [retPost, ht] using ho
          simpa [Semantics.PostValid, Semantics.returnTarget, Semantics.Cont.returnCont, ht, hp.1]
            using (Semantics.ValidFor.final (n := n) hp.2)

/-! ## Memory lemmas -/

theorem Mem.block?_lt {m : Mem} {b : Nat} {blk : Block} (h : m.block? b = some blk) :
    b < m.blocks.size := by
  unfold Mem.block? at h
  rcases Nat.lt_or_ge b m.blocks.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; simp at h

theorem Mem.block?_eq {m : Mem} {b : Nat} {blk : Block} :
    m.block? b = some blk ↔ m.blocks[b]? = some (some blk) := by
  unfold Mem.block?
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp [h]

theorem Mem.block?_setCell {m : Mem} {b i : Nat} {blk : Block} {v : Val} (b' : Nat)
    (h : m.block? b = some blk) :
    (m.setCell b i v).block? b' =
      if b' = b then some { blk with cells := blk.cells.setIfInBounds i v } else m.block? b' := by
  have hlt := Mem.block?_lt h
  have hb := Mem.block?_eq.mp h
  unfold Mem.setCell Mem.block?
  by_cases hbb : b' = b
  · subst hbb; simp [Array.getElem?_modify, hb]
  · have : ¬ b = b' := fun h => hbb h.symm
    simp [hbb, Array.getElem?_modify, this]

theorem Mem.block?_alloc {m : Mem} {t : Ty} {cells : Array Val} (b' : Nat) :
    (m.alloc t cells).2.block? b' =
      if b' = m.blocks.size then some ⟨t, cells⟩ else m.block? b' := by
  unfold Mem.alloc Mem.block?
  by_cases hb : b' = m.blocks.size
  · subst hb; simp
  · simp [hb, Array.getElem?_push]

theorem Mem.block?_size {m : Mem} : m.block? m.blocks.size = none := by
  simp [Mem.block?]

@[simp] theorem Mem.alloc_fst {m : Mem} {t : Ty} {cells : Array Val} :
    (m.alloc t cells).1 = m.blocks.size := rfl

theorem Mem.block?_free {m : Mem} {b : Nat} (b' : Nat) :
    (m.free b).block? b' = if b' = b then none else m.block? b' := by
  unfold Mem.free Mem.block?
  by_cases hb : b' = b
  · subst hb
    by_cases hlt : b' < m.blocks.size
    · simp [hlt]
    · simp [hlt]
  · have : ¬ b = b' := fun h => hb h.symm
    simp [hb, this]

@[simp] theorem Mem.size_setCell {m : Mem} {b i : Nat} {v : Val} :
    (m.setCell b i v).blocks.size = m.blocks.size := by simp [Mem.setCell]

@[simp] theorem Mem.size_free {m : Mem} {b : Nat} : (m.free b).blocks.size = m.blocks.size := by
  simp [Mem.free]

@[simp] theorem Mem.size_alloc {m : Mem} {t : Ty} {cells : Array Val} :
    (m.alloc t cells).2.blocks.size = m.blocks.size + 1 := by simp [Mem.alloc]

@[simp] theorem assignDst_none {env : Env} {m : Mem} {rv : Option Val} :
    assignDst env m none rv = some env := by cases rv <;> rfl

@[simp] theorem assignDst_some {env : Env} {m : Mem} {x : Var} {v : Val} :
    assignDst env m (some x) (some v) = env.assign m x v := rfl

/-! ## Typing of values -/

@[simp] theorem Mem.hasTy_u32 {m : Mem} {v : BitVec 32} : m.hasTy (.u32 v) .u32 = true := rfl
@[simp] theorem Mem.hasTy_u64 {m : Mem} {v : BitVec 64} : m.hasTy (.u64 v) .u64 = true := rfl
@[simp] theorem Mem.hasTy_null {m : Mem} {t : Ty} : m.hasTy .null (.ptr t) = true := rfl

theorem Mem.hasTy_ptr {m : Mem} {b off : Nat} {blk : Block} {t : Ty}
    (h : m.block? b = some blk) (he : blk.elem = t) : m.hasTy (.ptr b off) (.ptr t) = true := by
  subst he
  unfold Mem.hasTy
  simp only [h, beq_self_eq_true]

/-! ## Array access under a known block -/

theorem Mem.loadArr_eq {m : Mem} {b i : Nat} {blk : Block} {v : Val}
    (h : m.block? b = some blk) (hs : blk.elem.isStruct = false)
    (hc : blk.cells[i]? = some v) (hv : v ≠ .undef) : m.loadArr b i = some v := by
  unfold Mem.loadArr
  simp only [h, hs, hc]
  cases v <;> simp_all

theorem Mem.storeArr_eq {m : Mem} {b i : Nat} {blk : Block} {v : Val}
    (h : m.block? b = some blk) (hs : blk.elem.isStruct = false)
    (ht : m.hasTy v blk.elem = true) (hi : i < blk.cells.size) :
    m.storeArr b i v = some (m.setCell b i v) := by
  unfold Mem.storeArr
  simp [h, hs, ht, hi]

/-! ## Field access under a known slot -/

theorem Mem.loadField_eq {P : Prog} {m : Mem} {b i : Nat} {f : String} {blk : Block} {t : Ty}
    {v : Val} (h : m.fieldSlot P b f = some (blk, i, t)) (hc : blk.cells[i]? = some v)
    (hv : v ≠ .undef) : m.loadField P b f = some v := by
  unfold Mem.loadField
  simp only [h, hc]

theorem Mem.storeField_eq {P : Prog} {m : Mem} {b i : Nat} {f : String} {blk : Block} {t : Ty}
    {v : Val} (h : m.fieldSlot P b f = some (blk, i, t)) (ht : m.hasTy v t = true)
    (hi : i < blk.cells.size) : m.storeField P b f v = some (m.setCell b i v) := by
  unfold Mem.storeField
  simp [h, ht, hi]

/-! ## Derived forms of the kernel specifications -/

/-- A valid reallocation from `NULL` either fails without changing the heap,
or returns the newly allocated block. The private oracle state remains abstract. -/
theorem kvrealloc_null {P : Prog} {t : Ty}
    {n : BitVec 64} {st st' : KernelState P State} {rv : Option Val}
    (hn : n ≠ 0) (ht : t.isStruct = false)
    (hr : Ext.run P (.kvrealloc t) [.null, .u64 n] st = some (rv, st')) :
    (rv = some .null ∧ st'.mem = st.mem) ∨
    (rv = some (.ptr st.mem.blocks.size 0) ∧
      st'.mem = (st.mem.alloc t (Array.replicate n.toNat Val.undef)).2) := by
  have h := Ext.run_spec hr
  exact h.kvrealloc_null

/-- The same contract for a reallocation from a live array block. -/
theorem kvrealloc_ptr {P : Prog} {t : Ty}
    {n : BitVec 64} {st st' : KernelState P State} {rv : Option Val}
    {b : Nat} {blk : Block} (hn : n ≠ 0) (ht : t.isStruct = false)
    (hb : st.mem.block? b = some blk) (he : blk.elem = t)
    (hr : Ext.run P (.kvrealloc t) [.ptr b 0, .u64 n] st = some (rv, st')) :
    (rv = some .null ∧ st'.mem = st.mem) ∨
    (rv = some (.ptr st.mem.blocks.size 0) ∧
      st'.mem = ((st.mem.free b).alloc t (reallocCells blk.cells n.toNat)).2) := by
  have h := Ext.run_spec hr
  obtain ⟨blk', hb', hreply⟩ := h.kvrealloc_ptr
  have heq : blk' = blk := Option.some.inj (hb'.symm.trans hb)
  subst blk'
  simpa only [Kernel.Reply.mk.injEq] using hreply

/-! ## Tactics

`embc_simp` evaluates expressions and environment updates on concrete
program text.  `wp_step` applies the rule for the statement at the head of a
`WP` goal and then evaluates. -/

macro "embc_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [evalE, evalBin, evalArith, evalCast, evalArgs, ptrEq,
      Env.get, Env.ty, Env.set, Env.assign, Val.toIdx, Val.ofBool, $ts,*])

macro "embc_simp" : tactic => `(tactic| embc_simp [])

end EmbC
