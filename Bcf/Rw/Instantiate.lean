import Bcf.Poly
import Bcf.Rw.Zero

/-!
# Soundness of REWRITE

`instE_spec`: instantiating a pattern yields a node whose value is the
pattern's denotation under the parameter values.  A rewrite is sound
(`RwRule.Sound`) when both sides denote the same value whenever the
parameters have the declared types and the condition holds; then the
REWRITE step's conclusion is entailed.
-/

namespace Bcf

/-- The value shapes allowed for each parameter type. -/
def RwTy.ok : RwTy → Val → Prop
  | .any, _ => True
  | .bool, v => ∃ b, v = .bool b
  | .bv w, v => ∃ x : BitVec w, v = .bv w x
  | .bvq, v => ∃ (w : Nat) (x : BitVec w), v = .bv w x ∧ w ≤ 255
  | .bools, v => ∃ vs, v = .list true vs
  | .bvqs, v => ∃ vs, v = .list false vs

def envOK (tys : List RwTy) (env : Nat → Val) : Prop :=
  ∀ i t, tys[i]? = some t → RwTy.ok t (env i)

/-- A rewrite is sound when its sides agree under every typed environment
satisfying its condition. -/
def RwRule.Sound (r : RwRule) : Prop :=
  ∀ env, envOK r.params env → (∀ c, r.cond = some c → denoteE env c = .bool true) →
    denoteE env r.lhs ≠ .bad → denoteE env r.rhs ≠ .bad → denoteE env r.lhs = denoteE env r.rhs

/-! ## Generic facts -/

theorem RwOp.node_not_var (op : RwOp) (w : Nat) :
    (∀ w' id, op.node w ≠ .bvVar w' id) ∧ (∀ id, op.node w ≠ .boolVar id) := by
  cases op <;> simp [RwOp.node]

theorem eval_ne_bad {pool : Pool} (hwf : WF pool) (ρ : Assign) {i : Nat} (hi : i < pool.size) :
    eval pool ρ i ≠ .bad := by
  obtain ⟨n, hn⟩ := node_of_lt hi
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf i n hn).2
  have := eval_ty pool ρ i
  rw [ht] at this
  intro hb; rw [hb] at this; simp [Val.ty] at this

theorem ty_eq_list {v : Val} {e : Bool} {n : Nat} (h : v.ty = some (.list e n)) : ∃ vs, v = .list e vs := by
  cases v with
  | list e' vs => simp [Val.ty] at h; obtain ⟨rfl, _⟩ := h; exact ⟨vs, rfl⟩
  | bv _ _ => simp [Val.ty] at h
  | bool _ => simp [Val.ty] at h
  | bad => simp [Val.ty] at h

/-- Types of existing nodes are in the memo. -/
theorem tys_of_lt {st : St} (hok : TysOK st.pool st.tys) {a : Nat} (ha : a < st.pool.size) :
    st.tys[a]? = typeOf st.pool a := by
  obtain ⟨n, hn⟩ := node_of_lt ha
  exact (hok.2 a n hn).2.symm

theorem lt_of_tys {st : St} (hok : TysOK st.pool st.tys) {a : Nat} {t : Ty} (h : st.tys[a]? = some t) :
    a < st.pool.size := by
  rw [← hok.1]; exact (Array.getElem?_eq_some_iff.mp h).1

/-! ## Constant evaluation -/

theorem cvalF_eval {st : St} (hok : TysOK st.pool st.tys) (ρ : Assign) :
    ∀ i f v, i < f → cvalF st f i = some v → eval st.pool ρ i = v := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f v hf h
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [cvalF] at h
    split at h
    · simp at h
    · rename_i n hn
      have hwf := hok.wf
      have hlt := (hok.2 i n hn).1
      split at h
      · simp at h
      · simp at h
      · rename_i w hop
        split at h
        · rename_i a hargs
          split at h
          · rename_i m hm
            simp at h; subst h
            obtain ⟨op, args⟩ := n
            simp only at hop hargs; subst hop
            have : args = #[a] := Array.ext' hargs
            subst this
            rw [eval_node hwf ρ hn]
            have ha : a < st.pool.size := lt_of_tys hok hm
            rw [tys_of_lt hok ha] at hm
            obtain ⟨x, hx⟩ := eval_bv (ρ := ρ) hm
            simp only [List.map, hx]
            rfl
          · simp at h
        · simp at h
      · rename_i hnv hnb hns
        split at h
        · rename_i vs hvs
          simp at h; subst h
          rw [eval_node hwf ρ hn]
          have hmap : n.args.toList.map (eval st.pool ρ) = vs := by
            apply mapOpt_eq_map hvs
            intro a ha v' hv'
            have ha' : a < i := hlt a (by simpa using ha)
            simp only [ha', ite_true] at hv'
            exact ih a ha' g v' (by omega) hv'
          rw [hmap]
          exact Op.eval_indep n.op (fun w id hh => hnv w id hh) (fun id hh => hnb id hh) ρ _ vs
        · simp at h

theorem constNat_eval {st : St} (hok : TysOK st.pool st.tys) {i n : Nat} (h : constNat st i = some n) (ρ : Assign) :
    ∃ (w : Nat) (x : BitVec w), eval st.pool ρ i = .bv w x ∧ x.toNat = n := by
  unfold constNat at h
  split at h
  · rename_i w x hc
    simp at h; subst h
    exact ⟨w, x, cvalF_eval hok ρ i (i + 1) _ (by omega) hc, rfl⟩
  · simp at h

/-! ## Environments -/

def envOf (st : St) (ρ : Assign) (args : Array Nat) : Nat → Val :=
  fun i => match args[i]? with
    | some a => eval st.pool ρ a
    | none => .bad

theorem envOf_ext {st st' : St} (h : Extends st st') (ρ : Assign) {args : Array Nat}
    (hargs : ∀ a ∈ args, a < st.pool.size) : envOf st' ρ args = envOf st ρ args := by
  funext i
  unfold envOf
  cases hi : args[i]? with
  | none => rfl
  | some a => exact eval_ext h ρ (hargs a (Array.mem_of_getElem? hi))

theorem args_ext {st st' : St} (h : Extends st st') {args : Array Nat}
    (hargs : ∀ a ∈ args, a < st.pool.size) : ∀ a ∈ args, a < st'.pool.size :=
  fun a ha => Nat.lt_of_lt_of_le (hargs a ha) h.1

/-! ## Splicing -/

theorem spliceIdx_spec {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {items : List Nat}
    (hi : i < st.pool.size) (h : spliceIdx st i = some items) (ρ : Assign) :
    (∀ x ∈ items, x < st.pool.size) ∧ items.map (eval st.pool ρ) = spliceVal (eval st.pool ρ i) := by
  unfold spliceIdx at h
  have hty := eval_ty st.pool ρ i
  rw [← tys_of_lt hok hi] at hty
  split at h
  · rename_i e k hl
    split at h
    · rename_i e' elems hn'
      simp at h; subst h
      refine ⟨fun x hx => child_lt hok.wf hn' (by simpa using hx), ?_⟩
      rw [hl] at hty
      rw [eval_node hok.wf ρ hn'] at hty ⊢
      simp only [Op.eval, listEval] at hty ⊢
      cases hts : Val.tys (elems.toList.map (eval st.pool ρ)) with
      | none => rw [hts] at hty; simp [Val.ty] at hty
      | some ts =>
        rw [hts] at hty
        by_cases hall : ts.all (Ty.inClass e') = true
        · simp [hall, spliceVal]
        · simp [hall, Val.ty] at hty
    · simp at h
  · rename_i t hnl ht
    simp at h; subst h
    rw [ht] at hty
    refine ⟨fun x hx => by simp at hx; subst hx; exact hi, ?_⟩
    simp only [List.map_cons, List.map_nil]
    cases hv : eval st.pool ρ i with
    | list e vs =>
      rw [hv] at hty
      exact absurd (by simpa [Val.ty] using hty.symm) (hnl e vs.length)
    | bv _ _ => rfl
    | bool _ => rfl
    | bad => rfl
  · simp at h

/-! ## Operator application -/

theorem pushNodeApp_spec {st st' : St} (hok : TysOK st.pool st.tys) {op : RwOp} {is : List Nat} {r : Nat}
    {tys : List Ty} (his : ∀ a ∈ is, a < st.pool.size)
    (htys : mapOpt (fun a => st.tys[a]?) is = some tys)
    (h : pushNode st ⟨op.node (op.width tys), is.toArray⟩ = some (st', r)) :
    Extends st st' ∧ TysOK st'.pool st'.tys ∧ r < st'.pool.size ∧
    ∀ ρ, eval st'.pool ρ r = Op.eval (fun _ => 0) (op.node (op.widthV (is.map (eval st.pool ρ)))) (is.map (eval st.pool ρ)) := by
  have hok' := pushNode_tysOK h hok
  refine ⟨pushNode_extends h, hok', (pushNode_size h).2, ?_⟩
  intro ρ
  rw [eval_node hok'.wf ρ (pushNode_get h)]
  simp only
  have hmap : is.map (eval st'.pool ρ) = is.map (eval st.pool ρ) :=
    List.map_congr_left (fun a ha => pushNode_eval h ρ (his a ha))
  rw [hmap]
  have hw : op.widthV (is.map (eval st.pool ρ)) = op.width tys := by
    unfold RwOp.widthV
    rw [tys_map]
    have : mapOpt (fun a => (eval st.pool ρ a).ty) is = some tys := by
      rw [← htys]
      apply mapOpt_congr
      intro a ha
      rw [eval_ty, tys_of_lt hok (his a ha)]
    rw [this]
  rw [hw]
  exact Op.eval_indep _ (RwOp.node_not_var op _).1 (RwOp.node_not_var op _).2 ρ _ _

theorem pushApp_spec {st st' : St} (hok : TysOK st.pool st.tys) {op : RwOp} {is : List Nat} {r : Nat}
    (his : ∀ a ∈ is, a < st.pool.size) (h : pushApp st op is = some (st', r)) :
    Extends st st' ∧ TysOK st'.pool st'.tys ∧ r < st'.pool.size ∧
    ∀ ρ, eval st'.pool ρ r = appVal op (is.map (eval st.pool ρ)) := by
  unfold pushApp at h
  split at h
  · simp at h
  · rename_i i
    split at h
    · rename_i hred
      simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨Extends.refl _, hok, his i (by simp), ?_⟩
      intro ρ; simp [appVal, hred]
    · rename_i hred
      split at h
      · rename_i tys htys
        obtain ⟨h1, h2, h3, h4⟩ := pushNodeApp_spec hok his htys h
        refine ⟨h1, h2, h3, ?_⟩
        intro ρ; rw [h4 ρ]; simp [appVal, hred]
      · simp at h
  · rename_i hn1 hn2
    split at h
    · rename_i tys htys
      obtain ⟨h1, h2, h3, h4⟩ := pushNodeApp_spec hok his htys h
      refine ⟨h1, h2, h3, ?_⟩
      intro ρ; rw [h4 ρ]
      rcases is with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact absurd rfl hn1
      · exact absurd rfl (hn2 a)
      · simp only [appVal, List.map_cons]
    · simp at h

theorem pushApp_facts {st st' : St} {op : RwOp} {is : List Nat} {r : Nat}
    (h : pushApp st op is = some (st', r)) : st' = st ∨ st'.facts = st.facts := by
  unfold pushApp at h
  split at h
  · simp at h
  · split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
    · split at h
      · exact Or.inr (pushNode_facts h)
      · simp at h
  · split at h
    · exact Or.inr (pushNode_facts h)
    · simp at h

theorem pushLit_spec {st st' : St} {sz v r : Nat} (h : pushLit st sz v = some (st', r)) :
    pushNode st ⟨.bvVal sz v, #[]⟩ = some (st', r) := by
  unfold pushLit at h; split at h
  · exact h
  · simp at h

/-- What a freshly pushed node evaluates to. -/
theorem eval_pushed {st st' : St} {n : Node} {r : Nat} (hok : TysOK st.pool st.tys)
    (h : pushNode st n = some (st', r)) (ρ : Assign) :
    eval st'.pool ρ r = n.op.eval ρ (n.args.toList.map (eval st'.pool ρ)) :=
  eval_node (pushNode_tysOK h hok).wf ρ (pushNode_get h)

/-! ## Instantiation agrees with denotation -/

/-- The invariant carried through instantiation. -/
def InstOK (bi : Builtins) (args : Array Nat) (st : St) : Prop :=
  (∀ a ∈ args, a < st.pool.size) ∧ TysOK st.pool st.tys ∧
  st.pool[bi.tt]? = some ⟨.boolVal true, #[]⟩ ∧ st.pool[bi.ff]? = some ⟨.boolVal false, #[]⟩

theorem InstOK.ext {bi : Builtins} {args : Array Nat} {st st' : St} (h : InstOK bi args st)
    (hext : Extends st st') (hok : TysOK st'.pool st'.tys) : InstOK bi args st' :=
  ⟨args_ext hext h.1, hok, get_ext hext h.2.2.1, get_ext hext h.2.2.2⟩

theorem InstOK.push {bi : Builtins} {args : Array Nat} {st st' : St} {n : Node} {r : Nat} (h : InstOK bi args st)
    (hp : pushNode st n = some (st', r)) : InstOK bi args st' :=
  h.ext (pushNode_extends hp) (pushNode_tysOK hp h.2.1)

mutual
theorem instE_spec (bi : Builtins) (args : Array Nat) (e : RwExpr) :
    ∀ (st st' : St) (r : Nat), InstOK bi args st → instE bi args e st = some (st', r) →
      Extends st st' ∧ TysOK st'.pool st'.tys ∧ st'.facts = st.facts ∧ r < st'.pool.size ∧
      ∀ ρ, eval st'.pool ρ r = denoteE (envOf st ρ args) e :=
  match e with
  | .var i => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i a ha
      simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨Extends.refl _, hst.2.1, rfl, hst.1 a (Array.mem_of_getElem? ha), ?_⟩
      intro ρ; simp [denoteE, envOf, ha]
    · simp at h
  | .tt => by
    intro st st' r hst h
    simp only [instE] at h
    simp at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨Extends.refl _, hst.2.1, rfl, idx_lt_of_get hst.2.2.1, ?_⟩
    intro ρ; rw [eval_lit_bool hst.2.1.wf hst.2.2.1 ρ]; rfl
  | .ff => by
    intro st st' r hst h
    simp only [instE] at h
    simp at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨Extends.refl _, hst.2.1, rfl, idx_lt_of_get hst.2.2.2, ?_⟩
    intro ρ; rw [eval_lit_bool hst.2.1.wf hst.2.2.2 ρ]; rfl
  | .lit v => by
    intro st st' r hst h
    simp only [instE] at h
    refine ⟨pushNode_extends h, pushNode_tysOK h hst.2.1, pushNode_facts h, (pushNode_size h).2, ?_⟩
    intro ρ; rw [eval_pushed hst.2.1 h ρ]; rfl
  | .symVal val sz => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 v h1
      obtain ⟨ext1, hok1, hf1, hv, hev1⟩ := instE_spec bi args val st st1 v hst h1
      have hst1 := hst.ext ext1 hok1
      split at h
      · rename_i st2 s h2
        obtain ⟨ext2, hok2, hf2, hs, hev2⟩ := instE_spec bi args sz st1 st2 s hst1 h2
        split at h
        · rename_i vn sn hvn hsn
          have h' := pushLit_spec h
          refine ⟨(ext1.trans ext2).trans (pushNode_extends h'), pushNode_tysOK h' hok2,
            by rw [pushNode_facts h', hf2, hf1], (pushNode_size h').2, ?_⟩
          intro ρ
          rw [eval_pushed hok2 h' ρ]
          obtain ⟨w1, x1, hx1, hx1n⟩ := constNat_eval hok2 hvn ρ
          obtain ⟨w2, x2, hx2, hx2n⟩ := constNat_eval hok2 hsn ρ
          have e1 : denoteE (envOf st ρ args) val = .bv w1 x1 := by
            rw [← hev1 ρ, ← eval_ext ext2 ρ hv, hx1]
          have e2 : denoteE (envOf st ρ args) sz = .bv w2 x2 := by
            rw [← envOf_ext ext1 ρ hst.1, ← hev2 ρ, hx2]
          simp only [denoteE, e1, e2, hx1n, hx2n]
          rfl
        · simp at h
      · simp at h
    · simp at h
  | .bvmax sz => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 s h1
      obtain ⟨ext1, hok1, hf1, hs, hev1⟩ := instE_spec bi args sz st st1 s hst h1
      split at h
      · rename_i sn hsn
        have h' := pushLit_spec h
        refine ⟨ext1.trans (pushNode_extends h'), pushNode_tysOK h' hok1,
          by rw [pushNode_facts h', hf1], (pushNode_size h').2, ?_⟩
        intro ρ
        rw [eval_pushed hok1 h' ρ]
        obtain ⟨w2, x2, hx2, hx2n⟩ := constNat_eval hok1 hsn ρ
        have e2 : denoteE (envOf st ρ args) sz = .bv w2 x2 := by rw [← hev1 ρ, hx2]
        simp only [denoteE, e2, hx2n]
        rfl
      · simp at h
    · simp at h
  | .app op as => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 is h1
      obtain ⟨ext1, hok1, hf1, his, hev⟩ := instA_spec bi args as st st1 is hst h1
      obtain ⟨ext2, hok2, hr, hev2⟩ := pushApp_spec hok1 his h
      refine ⟨ext1.trans ext2, hok2, ?_, hr, ?_⟩
      · rw [← hf1]
        rcases pushApp_facts h with hh | hh
        · rw [hh]
        · exact hh
      · intro ρ; rw [hev2 ρ, hev ρ]; rfl
    · simp at h
  | .ite c t e => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 ci h1
      obtain ⟨ext1, hok1, hf1, hc, hev1⟩ := instE_spec bi args c st st1 ci hst h1
      have hst1 := hst.ext ext1 hok1
      split at h
      · rename_i st2 ti h2
        obtain ⟨ext2, hok2, hf2, ht, hev2⟩ := instE_spec bi args t st1 st2 ti hst1 h2
        have hst2 := hst1.ext ext2 hok2
        split at h
        · rename_i st3 ei h3
          obtain ⟨ext3, hok3, hf3, he, hev3⟩ := instE_spec bi args e st2 st3 ei hst2 h3
          have hc3 : ci < st3.pool.size := Nat.lt_of_lt_of_le hc (Nat.le_trans ext2.1 ext3.1)
          have ht3 : ti < st3.pool.size := Nat.lt_of_lt_of_le ht ext3.1
          have ec : ∀ ρ, denoteE (envOf st ρ args) c = eval st3.pool ρ ci := by
            intro ρ; rw [← hev1 ρ, ← eval_ext ext2 ρ hc, ← eval_ext ext3 ρ (Nat.lt_of_lt_of_le hc ext2.1)]
          have et : ∀ ρ, denoteE (envOf st ρ args) t = eval st3.pool ρ ti := by
            intro ρ; rw [← envOf_ext ext1 ρ hst.1, ← hev2 ρ, ← eval_ext ext3 ρ ht]
          have ee : ∀ ρ, denoteE (envOf st ρ args) e = eval st3.pool ρ ei := by
            intro ρ; rw [← envOf_ext ext1 ρ hst.1, ← envOf_ext ext2 ρ hst1.1, ← hev3 ρ]
          have htyt := eval_ty st3.pool (fun _ => 0) ti
          rw [← tys_of_lt hok3 ht3] at htyt
          split at h
          · rename_i hb
            rw [hb] at htyt
            refine ⟨((ext1.trans ext2).trans ext3).trans (pushNode_extends h), pushNode_tysOK h hok3,
              by rw [pushNode_facts h, hf3, hf2, hf1], (pushNode_size h).2, ?_⟩
            intro ρ
            rw [eval_pushed hok3 h ρ]
            simp only [List.map, Op.eval]
            rw [pushNode_eval h ρ hc3, pushNode_eval h ρ ht3, pushNode_eval h ρ he]
            have : (eval st3.pool ρ ti).ty = some .bool := by rw [eval_ty, ← tys_of_lt hok3 ht3, hb]
            obtain ⟨b, hbv⟩ := Val.ty_eq_bool_iff.mp this
            simp only [denoteE, et, ec, ee, hbv]
          · rename_i w hb
            refine ⟨((ext1.trans ext2).trans ext3).trans (pushNode_extends h), pushNode_tysOK h hok3,
              by rw [pushNode_facts h, hf3, hf2, hf1], (pushNode_size h).2, ?_⟩
            intro ρ
            rw [eval_pushed hok3 h ρ]
            simp only [List.map, Op.eval]
            rw [pushNode_eval h ρ hc3, pushNode_eval h ρ ht3, pushNode_eval h ρ he]
            have : (eval st3.pool ρ ti).ty = some (.bv w) := by rw [eval_ty, ← tys_of_lt hok3 ht3, hb]
            obtain ⟨x, hbv⟩ := Val.ty_eq_bv_iff.mp this
            simp only [denoteE, et, ec, ee, hbv]
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  | .extract hi lo x => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 hi' h1
      obtain ⟨ext1, hok1, hf1, hhi, hev1⟩ := instE_spec bi args hi st st1 hi' hst h1
      have hst1 := hst.ext ext1 hok1
      split at h
      · rename_i st2 lo' h2
        obtain ⟨ext2, hok2, hf2, hlo, hev2⟩ := instE_spec bi args lo st1 st2 lo' hst1 h2
        have hst2 := hst1.ext ext2 hok2
        split at h
        · rename_i st3 xi h3
          obtain ⟨ext3, hok3, hf3, hx, hev3⟩ := instE_spec bi args x st2 st3 xi hst2 h3
          split at h
          · rename_i hn ln hhn hln
            split at h
            · refine ⟨((ext1.trans ext2).trans ext3).trans (pushNode_extends h), pushNode_tysOK h hok3,
                by rw [pushNode_facts h, hf3, hf2, hf1], (pushNode_size h).2, ?_⟩
              intro ρ
              rw [eval_pushed hok3 h ρ]
              simp only [List.map, Op.eval]
              rw [pushNode_eval h ρ hx]
              obtain ⟨w1, x1, hx1, hx1n⟩ := constNat_eval hok3 hhn ρ
              obtain ⟨w2, x2, hx2, hx2n⟩ := constNat_eval hok3 hln ρ
              have e1 : denoteE (envOf st ρ args) hi = .bv w1 x1 := by
                rw [← hev1 ρ, ← eval_ext ext2 ρ hhi, ← eval_ext ext3 ρ (Nat.lt_of_lt_of_le hhi ext2.1), hx1]
              have e2 : denoteE (envOf st ρ args) lo = .bv w2 x2 := by
                rw [← envOf_ext ext1 ρ hst.1, ← hev2 ρ, ← eval_ext ext3 ρ hlo, hx2]
              have e3 : denoteE (envOf st ρ args) x = eval st3.pool ρ xi := by
                rw [← envOf_ext ext1 ρ hst.1, ← envOf_ext ext2 ρ hst1.1, ← hev3 ρ]
              simp only [denoteE, e1, e2, e3, hx1n, hx2n]
            · simp at h
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  | .zext e x => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 e' h1
      obtain ⟨ext1, hok1, hf1, he, hev1⟩ := instE_spec bi args e st st1 e' hst h1
      have hst1 := hst.ext ext1 hok1
      split at h
      · rename_i st2 xi h2
        obtain ⟨ext2, hok2, hf2, hx, hev2⟩ := instE_spec bi args x st1 st2 xi hst1 h2
        split at h
        · rename_i k n hk hn
          split at h
          · refine ⟨(ext1.trans ext2).trans (pushNode_extends h), pushNode_tysOK h hok2,
              by rw [pushNode_facts h, hf2, hf1], (pushNode_size h).2, ?_⟩
            intro ρ
            rw [eval_pushed hok2 h ρ]
            simp only [List.map, Op.eval]
            rw [pushNode_eval h ρ hx]
            obtain ⟨w1, x1, hx1, hx1n⟩ := constNat_eval hok2 hk ρ
            have e1 : denoteE (envOf st ρ args) e = .bv w1 x1 := by
              rw [← hev1 ρ, ← eval_ext ext2 ρ he, hx1]
            have : (eval st2.pool ρ xi).ty = some (.bv n) := by rw [eval_ty, ← tys_of_lt hok2 hx, hn]
            obtain ⟨xv, hxv⟩ := Val.ty_eq_bv_iff.mp this
            have e2 : denoteE (envOf st ρ args) x = .bv n xv := by
              rw [← envOf_ext ext1 ρ hst.1, ← hev2 ρ, hxv]
            simp only [denoteE, e1, e2, hx1n, hxv]
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  | .sext e x => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 e' h1
      obtain ⟨ext1, hok1, hf1, he, hev1⟩ := instE_spec bi args e st st1 e' hst h1
      have hst1 := hst.ext ext1 hok1
      split at h
      · rename_i st2 xi h2
        obtain ⟨ext2, hok2, hf2, hx, hev2⟩ := instE_spec bi args x st1 st2 xi hst1 h2
        split at h
        · rename_i k n hk hn
          split at h
          · refine ⟨(ext1.trans ext2).trans (pushNode_extends h), pushNode_tysOK h hok2,
              by rw [pushNode_facts h, hf2, hf1], (pushNode_size h).2, ?_⟩
            intro ρ
            rw [eval_pushed hok2 h ρ]
            simp only [List.map, Op.eval]
            rw [pushNode_eval h ρ hx]
            obtain ⟨w1, x1, hx1, hx1n⟩ := constNat_eval hok2 hk ρ
            have e1 : denoteE (envOf st ρ args) e = .bv w1 x1 := by
              rw [← hev1 ρ, ← eval_ext ext2 ρ he, hx1]
            have : (eval st2.pool ρ xi).ty = some (.bv n) := by rw [eval_ty, ← tys_of_lt hok2 hx, hn]
            obtain ⟨xv, hxv⟩ := Val.ty_eq_bv_iff.mp this
            have e2 : denoteE (envOf st ρ args) x = .bv n xv := by
              rw [← envOf_ext ext1 ρ hst.1, ← hev2 ρ, hxv]
            simp only [denoteE, e1, e2, hx1n, hxv]
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  | .repeat n x => by
    intro st st' r hst h
    simp only [instE] at h
    split at h
    · rename_i st1 n' h1
      obtain ⟨ext1, hok1, hf1, hn', hev1⟩ := instE_spec bi args n st st1 n' hst h1
      have hst1 := hst.ext ext1 hok1
      split at h
      · rename_i st2 xi h2
        obtain ⟨ext2, hok2, hf2, hx, hev2⟩ := instE_spec bi args x st1 st2 xi hst1 h2
        split at h
        · rename_i k m hk hm
          split at h
          · refine ⟨(ext1.trans ext2).trans (pushNode_extends h), pushNode_tysOK h hok2,
              by rw [pushNode_facts h, hf2, hf1], (pushNode_size h).2, ?_⟩
            intro ρ
            rw [eval_pushed hok2 h ρ]
            simp only [List.map, Op.eval]
            rw [pushNode_eval h ρ hx]
            obtain ⟨w1, x1, hx1, hx1n⟩ := constNat_eval hok2 hk ρ
            have e1 : denoteE (envOf st ρ args) n = .bv w1 x1 := by
              rw [← hev1 ρ, ← eval_ext ext2 ρ hn', hx1]
            have : (eval st2.pool ρ xi).ty = some (.bv m) := by rw [eval_ty, ← tys_of_lt hok2 hx, hm]
            obtain ⟨xv, hxv⟩ := Val.ty_eq_bv_iff.mp this
            have e2 : denoteE (envOf st ρ args) x = .bv m xv := by
              rw [← envOf_ext ext1 ρ hst.1, ← hev2 ρ, hxv]
            simp only [denoteE, e1, e2, hx1n, hxv]
          · simp at h
        · simp at h
      · simp at h
    · simp at h

theorem instA_spec (bi : Builtins) (args : Array Nat) (as : RwArgs) :
    ∀ (st st' : St) (is : List Nat), InstOK bi args st → instA bi args as st = some (st', is) →
      Extends st st' ∧ TysOK st'.pool st'.tys ∧ st'.facts = st.facts ∧ (∀ a ∈ is, a < st'.pool.size) ∧
      ∀ ρ, is.map (eval st'.pool ρ) = denoteA (envOf st ρ args) as :=
  match as with
  | .nil => by
    intro st st' is hst h
    simp only [instA] at h
    simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨Extends.refl _, hst.2.1, rfl, by simp, fun ρ => rfl⟩
  | .cons a rest => by
    intro st st' is hst h
    simp only [instA] at h
    split at h
    · rename_i st1 i h1
      obtain ⟨ext1, hok1, hf1, hi, hev1⟩ := instE_spec bi args a st st1 i hst h1
      have hst1 := hst.ext ext1 hok1
      split at h
      · rename_i items hitems
        have hsp := spliceIdx_spec hok1 hi hitems
        have hlt := (hsp (fun _ => 0)).1
        split at h
        · rename_i st2 is2 h2
          obtain ⟨ext2, hok2, hf2, his2, hev2⟩ := instA_spec bi args rest st1 st2 is2 hst1 h2
          simp at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨ext1.trans ext2, hok2, by rw [hf2, hf1], ?_, ?_⟩
          · intro x hx
            simp at hx
            rcases hx with hx | hx
            · exact Nat.lt_of_lt_of_le (hlt x hx) ext2.1
            · exact his2 x hx
          · intro ρ
            simp only [List.map_append]
            rw [hev2 ρ, envOf_ext ext1 ρ hst.1]
            have : items.map (eval st2.pool ρ) = items.map (eval st1.pool ρ) :=
              List.map_congr_left (fun x hx => eval_ext ext2 ρ (hlt x hx))
            rw [this, (hsp ρ).2, hev1 ρ]
            rfl
        · simp at h
      · simp at h
    · simp at h
end

/-! ## Parameter typing -/

theorem rwTyOK_some {t : RwTy} {o : Option Ty} (h : rwTyOK t o = true) : ∃ T, o = some T := by
  unfold rwTyOK at h
  split at h <;> first | exact ⟨_, rfl⟩ | simp at h

theorem rwTyOK_spec {st : St} (hok : TysOK st.pool st.tys) {t : RwTy} {a : Nat}
    (h : rwTyOK t st.tys[a]? = true) (ρ : Assign) : RwTy.ok t (eval st.pool ρ a) := by
  obtain ⟨T, hT⟩ := rwTyOK_some h
  have hty : (eval st.pool ρ a).ty = some T := by
    rw [eval_ty, ← tys_of_lt hok (lt_of_tys hok hT), hT]
  rw [hT] at h
  cases t with
  | any => trivial
  | bool =>
    cases T with
    | bool => exact Val.ty_eq_bool_iff.mp hty
    | bv w => simp [rwTyOK] at h
    | list e n => simp [rwTyOK] at h
  | bv w =>
    cases T with
    | bv w' =>
      simp [rwTyOK] at h; subst h
      exact Val.ty_eq_bv_iff.mp hty
    | bool => simp [rwTyOK] at h
    | list e n => simp [rwTyOK] at h
  | bvq =>
    cases T with
    | bv w' =>
      obtain ⟨x, hx⟩ := Val.ty_eq_bv_iff.mp hty
      simp [rwTyOK] at h
      exact ⟨w', x, hx, h⟩
    | bool => simp [rwTyOK] at h
    | list e n => simp [rwTyOK] at h
  | bools =>
    cases T with
    | list e n =>
      cases e with
      | true => exact ty_eq_list hty
      | false => simp [rwTyOK] at h
    | bool => simp [rwTyOK] at h
    | bv w => simp [rwTyOK] at h
  | bvqs =>
    cases T with
    | list e n =>
      cases e with
      | false => exact ty_eq_list hty
      | true => simp [rwTyOK] at h
    | bool => simp [rwTyOK] at h
    | bv w => simp [rwTyOK] at h

theorem paramsOK_lt {st : St} (hok : TysOK st.pool st.tys) :
    ∀ (tys : List RwTy) (args : List Nat), paramsOK st tys args = true → ∀ a ∈ args.toArray, a < st.pool.size := by
  intro tys
  induction tys with
  | nil =>
    intro args h a ha
    cases args with
    | nil => simp at ha
    | cons _ _ => simp [paramsOK] at h
  | cons t ts ih =>
    intro args h a ha
    cases args with
    | nil => simp [paramsOK] at h
    | cons b bs =>
      simp only [paramsOK, Bool.and_eq_true] at h
      simp at ha
      rcases ha with rfl | ha
      · obtain ⟨T, hT⟩ := rwTyOK_some h.1; exact lt_of_tys hok hT
      · exact ih bs h.2 a (by simpa using ha)

theorem envOK_of_paramsOK {st : St} (hok : TysOK st.pool st.tys) (ρ : Assign) :
    ∀ (tys : List RwTy) (args : List Nat), paramsOK st tys args = true →
      envOK tys (envOf st ρ args.toArray) := by
  intro tys
  induction tys with
  | nil => intro args h i t ht; simp at ht
  | cons t ts ih =>
    intro args h
    cases args with
    | nil => simp [paramsOK] at h
    | cons a as =>
      simp only [paramsOK, Bool.and_eq_true] at h
      intro i t' ht'
      cases i with
      | zero =>
        simp at ht'; subst ht'
        simp only [envOf, List.getElem?_toArray, List.getElem?_cons_zero]
        exact rwTyOK_spec hok h.1 ρ
      | succ j =>
        simp at ht'
        have := ih as h.2 j t' ht'
        simpa [envOf, List.getElem?_toArray] using this

/-! ## Conditions -/

theorem conj_len {pool : Pool} (hwf : WF pool) {e : Nat} {args : Array Nat}
    (he : pool[e]? = some ⟨.conj, args⟩) : 2 ≤ args.size := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hwf e _ he).2
  rw [typeOf_node hwf he] at ht
  cases hm : mapOpt (typeOf pool) args.toList with
  | none => rw [hm] at ht; simp at ht
  | some tys =>
    rw [hm] at ht
    simp only [Option.bind_some, Op.resultTy, boolNTy, tyGuard] at ht
    split at ht
    · rename_i hc; have := mapOpt_length hm; simp at this; have := hc.2; omega
    · simp at ht

theorem condMatch_sound {base : Pool} {g : Nat} {bi : Builtins} {st : St} (hinv : Inv base g bi st) {c p : Nat}
    (h : condMatch bi st c p = true) (hp : Entails st g p) (ρ : Assign) (hg : holds st.pool ρ g) :
    holds st.pool ρ c := by
  unfold condMatch at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact hp.2 ρ hg
  · split at h
    · rename_i args hn
      split at h
      · rename_i x t hl
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst t; subst x
        have hpn : st.pool[p]? = some ⟨.eq, #[c, bi.tt]⟩ := by
          simp only [St.node] at hn; rw [hn]; congr; exact Array.ext' hl
        have hh := (holds_eq_node hinv.wf hpn ρ).mp (hp.2 ρ hg)
        unfold holds
        rw [hh.1, eval_lit_bool hinv.wf hinv.tt ρ]
      · simp at h
    · simp at h

theorem condsOK_sound {base : Pool} {g : Nat} {bi : Builtins} {st : St} (hinv : Inv base g bi st) :
    ∀ (cs ps : List Nat), condsOK bi st cs ps = true → (∀ p ∈ ps, Entails st g p) →
      ∀ ρ, holds st.pool ρ g → ∀ c ∈ cs, holds st.pool ρ c := by
  intro cs
  induction cs with
  | nil => intro ps h hp ρ hg c hc; simp at hc
  | cons c cs ih =>
    intro ps h hp ρ hg c' hc'
    simp at hc'
    cases ps with
    | nil =>
      simp only [condsOK] at h
      split at h
      · rename_i hcv
        rcases hc' with rfl | hc'
        · exact cvalF_eval hinv.tys ρ c' (c' + 1) _ (by omega) hcv
        · exact ih [] h (by simp) ρ hg c' hc'
      · simp at h
    | cons p ps =>
      simp only [condsOK, Bool.and_eq_true] at h
      rcases hc' with rfl | hc'
      · exact condMatch_sound hinv h.1 (hp p (by simp)) ρ hg
      · exact ih ps h.2 (fun q hq => hp q (by simp [hq])) ρ hg c' hc'

theorem checkCond_sound {base : Pool} {g : Nat} {bi : Builtins} {st : St} (hinv : Inv base g bi st) {c : Nat}
    {prems : List Nat} (h : checkCond bi st c prems = true) (hp : ∀ p ∈ prems, Entails st g p)
    (ρ : Assign) (hg : holds st.pool ρ g) : holds st.pool ρ c := by
  unfold checkCond at h
  split at h
  · rename_i cs hn
    simp only [St.node] at hn
    apply holds_conj_intro hinv.wf hn ρ (conj_len hinv.wf hn)
    intro a ha
    exact condsOK_sound hinv cs.toList prems h hp ρ hg a (by simpa using ha)
  · exact condsOK_sound hinv [c] prems h hp ρ hg c (by simp)

/-! ## The step -/

theorem Inv.ofExtends {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} (hinv : Inv base g bi st)
    (hext : Extends st st') (hok : TysOK st'.pool st'.tys) (hf : st'.facts = st.facts) : Inv base g bi st' where
  tys := hok
  ext := fun j hj => by rw [hext.2 j (Nat.lt_of_lt_of_le hj hinv.size)]; exact hinv.ext j hj
  size := Nat.le_trans hinv.size hext.1
  goal := Nat.lt_of_lt_of_le hinv.goal hext.1
  tt := get_ext hext hinv.tt
  ff := get_ext hext hinv.ff
  facts := fun k f hf' => by rw [hf] at hf'; exact Nat.lt_of_lt_of_le (hinv.facts k f hf') hext.1
  sound := fun ρ hg k f hf' => by
    rw [hf] at hf'
    rw [holds_ext hext ρ (hinv.facts k f hf')]
    rw [holds_ext hext ρ hinv.goal] at hg
    exact hinv.sound ρ hg k f hf'

theorem Entails.ext {st st' : St} {g f : Nat} (hext : Extends st st') (hg : g < st.pool.size)
    (h : Entails st g f) : Entails st' g f :=
  ⟨Nat.lt_of_lt_of_le h.1 hext.1, fun ρ hρ => by
    rw [holds_ext hext ρ h.1]; rw [holds_ext hext ρ hg] at hρ; exact h.2 ρ hρ⟩

theorem rwConclude_sound {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat} {r : RwRule}
    (hr : r.Sound) (hinv : Inv base g bi st) {args : List Nat}
    (hargs : ∀ a ∈ args.toArray, a < st.pool.size)
    (henv : ∀ ρ, envOK r.params (envOf st ρ args.toArray))
    (hcond : ∀ c, r.cond = some c → ∀ ρ, holds st.pool ρ g → denoteE (envOf st ρ args.toArray) c = .bool true)
    (h : rwConclude bi args.toArray r st = some (st', f)) : Inv base g bi st' ∧ Entails st' g f := by
  have hst : InstOK bi args.toArray st := ⟨hargs, hinv.tys, hinv.tt, hinv.ff⟩
  unfold rwConclude at h
  split at h
  · rename_i st1 m h1
    obtain ⟨ext1, hok1, hf1, hm, hev1⟩ := instE_spec bi args.toArray r.lhs st st1 m hst h1
    have hst1 := hst.ext ext1 hok1
    split at h
    · rename_i st2 t h2
      obtain ⟨ext2, hok2, hf2, ht, hev2⟩ := instE_spec bi args.toArray r.rhs st1 st2 t hst1 h2
      have hinv2 : Inv base g bi st2 := hinv.ofExtends (ext1.trans ext2) hok2 (by rw [hf2, hf1])
      apply mkEq_entails hinv2 h _ (Nat.lt_of_lt_of_le hm ext2.1) ht
      intro ρ hg
      have hg0 : holds st.pool ρ g := by rwa [holds_ext (ext1.trans ext2) ρ hinv.goal] at hg
      rw [eval_ext ext2 ρ hm, hev1 ρ, hev2 ρ, envOf_ext ext1 ρ hargs]
      apply hr _ (henv ρ) (fun c hc => hcond c hc ρ hg0)
      · rw [← hev1 ρ]; exact eval_ne_bad hok1.wf ρ hm
      · rw [← envOf_ext ext1 ρ hargs, ← hev2 ρ]; exact eval_ne_bad hok2.wf ρ ht
    · simp at h
  · simp at h

theorem ruleRewrite_sound {tbl : Nat → Option RwRule} (htbl : ∀ rid r, tbl rid = some r → r.Sound)
    {base : Pool} {g : Nat} {bi : Builtins} {st st' : St} {f : Nat} {ei : EI}
    {prems params : List Nat} (h : ruleRewrite tbl bi ei st prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold ruleRewrite at h
  split at h
  · simp at h
  · rename_i rid ps
    split at h
    · split at h
      · rename_i p
        split at h
        · rename_i e he
          split at h
          · rename_i h0
            simp at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨hinv, rw0_sound hinv h0⟩
          · simp at h
        · simp at h
      · simp at h
    · split at h
      · simp at h
      · rename_i r hr
        split at h
        · simp at h
        · rename_i args hargs
          split at h
          · rename_i hpok
            have hlt := paramsOK_lt hinv.tys _ _ hpok
            have hst : InstOK bi args.toArray st := ⟨hlt, hinv.tys, hinv.tt, hinv.ff⟩
            have henv : ∀ ρ, envOK r.params (envOf st ρ args.toArray) := fun ρ =>
              envOK_of_paramsOK hinv.tys ρ _ _ hpok
            split at h
            · rename_i hnc
              split at h
              · exact rwConclude_sound (htbl rid r hr) hinv hlt henv
                  (fun c hc => by rw [hnc] at hc; simp at hc) h
              · simp at h
            · rename_i c hc
              split at h
              · rename_i st1 ci hci
                split at h
                · rename_i hcc
                  obtain ⟨ext1, hok1, hf1, hcl, hev1⟩ := instE_spec bi args.toArray c st st1 ci hst hci
                  have hinv1 := hinv.ofExtends ext1 hok1 hf1
                  have hp1 : ∀ q ∈ prems, Entails st1 g q := fun q hq => (hp q hq).ext ext1 hinv.goal
                  apply rwConclude_sound (htbl rid r hr) hinv1 (args_ext ext1 hlt) ?_ ?_ h
                  · intro ρ; rw [envOf_ext ext1 ρ hlt]; exact henv ρ
                  · intro c' hc' ρ hg
                    rw [hc] at hc'; simp at hc'; subst hc'
                    rw [envOf_ext ext1 ρ hlt, ← hev1 ρ]
                    exact checkCond_sound hinv1 hcc hp1 ρ hg
                · simp at h
              · simp at h
          · simp at h

end Bcf
