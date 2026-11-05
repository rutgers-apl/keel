import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bool2

/-!
# Vbcf proofs: the Bool family, part 4 — `bl_mk_nots`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- `mkNots` on a list with one more element at the end. -/
theorem mkNots_snoc (st : St) (l : List Nat) (x : Nat) :
    mkNots st (l ++ [x]) =
      match mkNots st l with
      | some (st1, nas) =>
        match Bcf.mkNot st1 x with
        | some (st2, na) => some (st2, nas ++ [na])
        | none => none
      | none => none := by
  induction l generalizing st with
  | nil =>
    cases h1 : Bcf.mkNot st x <;> simp [mkNots, h1]
  | cons a l ih =>
    cases h1 : Bcf.mkNot st a with
    | none => simp [mkNots, h1]
    | some p =>
      obtain ⟨st1, na⟩ := p
      simp only [List.cons_append, mkNots, h1, ih]
      cases h2 : mkNots st1 l with
      | none => simp
      | some p2 =>
        obtain ⟨st2, nas⟩ := p2
        cases h3 : Bcf.mkNot st2 x <;> simp [h3]

/-- What `bl_mk_nots` guarantees when it returns `r`: either `r = 0`, or `r = 1` and the
negations of the arguments `args` are on the stack after the ids `is` from `base` on. -/
def MkNotsRet (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (is : List Nat) (args : Array Nat) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧
    (r = 0#32 ∨ (r = 1#32 ∧ ∃ (st' : VSt) (nas : List Nat), mkNots st args.toList = some (st'.toSt, nas) ∧
      RCtx W X c0 prems params c' st' ∧ VExt st st' ∧ StkTop c' st' base (is ++ nas)))

def MkNotsQ (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (base : Nat) (is : List Nat) (args : Array Nat) : (Post prog State) := fun o _ s' =>
  match o with
  | .ret (some (.u32 r)) => MkNotsRet W sb X c0 prems params st base is args r s'
  | _ => False

def MkNotsSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (q : Nat) (op : Op) (args : Array Nat) (base : Nat) (is : List Nat),
    FnSpec (State := State) Vbcf.prog "bl_mk_nots"
      (fun vs s => vs = [.ptr sb 0, uv (st.id q)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.pool[q]? = some ⟨op, args⟩ ∧
        ¬ IsLeaf op ∧ StkTop c st base is ∧ st.lv q)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ MkNotsRet W sb X c0 prems params st base is args r s')

/-- Loop invariant of `bl_mk_nots`: the first `k` arguments have been negated. -/
def MkNotsInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (q : Nat) (args : Array Nat) (base : Nat) (is : List Nat) : Env → (KernelState prog State) → Prop :=
  fun env s' =>
  ∃ (c' : CMem) (st' : VSt) (k : Nat) (nas : List Nat) (r ok : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("id", .u32, uv (st.id q)),
      ("n", .u32, uv args.size), ("i", .u32, uv k), ("r", .u32, .u32 r), ("ok", .u32, .u32 ok)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st' ∧ VExt st st' ∧ k ≤ args.size ∧
    mkNots st (args.toList.take k) = some (st'.toSt, nas) ∧ StkTop c' st' base (is ++ nas)

theorem bl_mk_nots_spec : MkNotsSpec (State := State) := by
  intro W sb X c0 c prems params st q op args base is
  have hs := prog_ck
  apply FnSpec.intro' (fn := blMkNots) rfl
  rintro vs s ⟨rfl, h, hR, hn, hl, htop, hq⟩
  simp [blMkNots, bindParams, Mem.hasTy_ptr h.ck rfl]
  obtain ⟨args', he, hsz, -, hargs⟩ := hR.core.argsN hn rfl hl
  cases he
  apply WP.mono (Q := MkNotsQ W sb X c0 prems params st base is args)
  rotate_left
  · intro o env' s' hq
    unfold MkNotsQ at hq
    split at hq
    · rename_i r
      exact ⟨rfl, r, rfl, hq⟩
    · exact hq.elim
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  rule_assign [hR.core.rdN hn hl]
  apply WP.loop_seq (MkNotsInv W sb X c0 prems params st q args base is)
  · exact ⟨c, st, 0, [], 0#32, 0#32, rfl, h, hR, VExt.refl st, by omega, by simp [mkNots],
      by simpa using htop⟩
  clear h hR htop
  rintro env s' ⟨c', st', k, nas, r, ok, rfl, h, hR, hext, hk, hnots, htop⟩
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkl : k = args.size := by omega
    subst hkl
    rw [List.take_of_length_le (by simp)] at hnots
    apply WP.ret
    simp only [evalE, MkNotsQ]
    exact ⟨c', h, Or.inr ⟨rfl, st', nas, hnots, hR, hext, htop⟩⟩
  have hq' := hext.lt hq
  have ha := hext.lt (hargs k hlt)
  rw [← hext.id hq]
  apply WP.rule_mk_not mk_not_specT h hR args[k] ha
  refine ⟨by rule_simp [hR.core.rdN (hext.get hn) hl], ?_⟩
  intro s2 c2 r2 h hB
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun hnoid => ⟨c2, h, Or.inl rfl⟩, fun hne => ?_⟩
  obtain ⟨st2, i, hP, hR, hext2, hstk, hi, rfl⟩ := hB.ok hne
  have htop2 := StkTop.built htop hext2 hstk
  apply WP.rule_push h hR
  rule_simp
  intro s3 c3 ok3 h3 hPu
  have htop3 := fun hok => StkTop.push htop2 hPu hok hi
  have hR3 := hPu.1
  clear h hR
  have h := h3
  have hR := hR3
  clear h3 hR3
  apply WP.guard_lit
  rule_simp
  refine ⟨fun hok => ⟨c3, h, Or.inl rfl⟩, fun hok => ?_⟩
  apply WP.assign_loop
  rule_simp
  rw [hext.id hq]
  refine ⟨c3, st2, k + 1, nas ++ [i], _, ok3, rfl, h, hR, hext.trans hext2, by omega, ?_, by simpa using htop3 hok⟩
  rw [List.take_succ_eq_append_getElem (by simpa using hlt), mkNots_snoc, hnots]
  simp [hP]

/-! ## Calling `bl_mk_nots` and `push_args` from a rule -/

theorem mkNots_length {st st' : St} {l nas : List Nat} (h : mkNots st l = some (st', nas)) :
    nas.length = l.length := by
  induction l generalizing st st' nas with
  | nil => simp [mkNots] at h; simp [← h.2]
  | cons a l ih =>
    simp only [mkNots] at h
    split at h
    · split at h
      · rename_i h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        simp [ih h2]
      · cases h
    · cases h

/-- A list pushed above `sp` extends the list on the stack. -/
theorem StkTop.append {c c' : CMem} {st : VSt} {base : Nat} {is js : List Nat}
    (ht : StkTop c st base is) (hpre : ∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?)
    (hsp : c'.k.sp.toNat = c.k.sp.toNat + js.length) (hids : StkIds c' st c.k.sp.toNat js) :
    StkTop c' st base (is ++ js) := by
  refine ⟨by rw [hsp, ht.1]; simp; omega, ?_⟩
  intro j a hj
  rcases Nat.lt_or_ge j is.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hj
    obtain ⟨ha, hU⟩ := ht.2 j a hj
    exact ⟨ha, by unfold U; rw [hpre _ (by rw [ht.1]; omega)]; exact hU⟩
  · rw [List.getElem?_append_right hge] at hj
    obtain ⟨ha, hU⟩ := hids _ _ hj
    refine ⟨ha, ?_⟩
    rwa [ht.1, show base + is.length + (j - is.length) = base + j by omega] at hU

section calls
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {es : List Expr} {rest : Stmt}

/-- `x = bl_mk_nots(st, q); rest`. -/
theorem WP.rule_mk_nots (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (q : Nat)
    {op : Op} {args : Array Nat} (hn : st.pool[q]? = some ⟨op, args⟩) (hl : ¬ IsLeaf op)
    {base : Nat} {is : List Nat} (htop : StkTop c st base is) (hq : st.lv q := by vlv)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv (st.id q)] ∧
      ∀ s' r, MkNotsRet W sb X c0 prems params st base is args r s' →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "bl_mk_nots" es) rest) Q env s := by
  apply WP.call_seq (bl_mk_nots_spec W sb X c0 c prems params st q op args base is) H.1
    ⟨rfl, h, hR, hn, hl, htop, hq⟩
  rintro rv s' ⟨r, rfl, hr⟩
  exact H.2 s' r hr

/-- `x = push_args(st, e); rest`, where `e` evaluates to the id of node `i`. -/
theorem WP.rule_push_args (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (i : Nat)
    {nd : Node} (hn : st.pool[i]? = some nd) (hl : ¬ IsLeaf nd.op) {base : Nat} {is : List Nat}
    (htop : StkTop c st base is) (hi : st.lv i := by vlv)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv (st.id i)] ∧
      ∀ s' c' ok, Holds W s'.mem sb c' → RCtx W X c0 prems params c' st →
        (ok = 0#32 ∨ (ok = 1#32 ∧ StkTop c' st base (is ++ nd.args.toList))) →
        match env.assign s'.mem x (.u32 ok) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "push_args" es) rest) Q env s := by
  apply WP.call_seq (push_args_spec W sb c X.posOf st.cs _ (st.σ i) (nd.ren st.σ)) H.1
    ⟨rfl, h, hR.core.cinv, st.img i nd hi hn, hl, hR.core.id_toNat hi⟩
  rintro rv s' ⟨c', h', hfr, hc', hpre, hcase⟩
  have hR' := hR.after_push hfr hc'.stk
  rcases hcase with rfl | ⟨rfl, hsp, hids⟩
  · exact H.2 s' c' 0#32 h' hR' (Or.inl rfl)
  · refine H.2 s' c' 1#32 h' hR' (Or.inr ⟨rfl, htop.append hpre (by simpa using hsp) ?_⟩)
    simp only [Node.ren_args, Array.toList_map] at hids
    exact StkIds.ofC hids (fun a ha => st.closed i nd hi hn a (by simpa using ha))

end calls

end Vbcf.Proof
