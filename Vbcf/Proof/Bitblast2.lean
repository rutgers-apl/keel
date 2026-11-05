import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast1

/-!
# Vbcf proofs: the Bitblast family, part 2 — lists on the scratch stack

`BbRange c st base l`: the ids of the list `l` are on the stack from `base` on, below `sp`.
`bb_zip_not`, `bb_list_eq`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- The list `l` is on the stack from `base` on, below `sp`. -/
def BbRange (c : CMem) (st : VSt) (base : Nat) (l : List Nat) : Prop :=
  base + l.length ≤ c.k.sp.toNat ∧ StkIds c st base l

section range
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {m : Mem}

theorem BbRange.lt {base : Nat} {l : List Nat} (hr : BbRange c st base l) {k : Nat}
    (hk : k < l.length) : st.lv l[k] := (hr.2 k _ (List.getElem?_eq_getElem hk)).1

theorem BbRange.rd {base : Nat} {l : List Nat} (hr : BbRange c st base l) {k : Nat}
    (hk : k < l.length) : rd c.stk (base + k) = some (uv (st.id l[k])) :=
  rd_u32 (hr.2 k _ (List.getElem?_eq_getElem hk)).2

theorem BbRange.stk (hR : RCtx W X c0 prems params c st) (h : Holds W m sb c) {base : Nat}
    {l : List Nat} (hr : BbRange c st base l) {k : Nat} (hk : k < l.length) :
    c.k.stk = some (stkB c, 0) := hR.stk_eq h (by have := hr.1; omega)

theorem BbRange.bound (hR : RCtx W X c0 prems params c st) {base : Nat} {l : List Nat}
    (hr : BbRange c st base l) : base + l.length ≤ 2147483648 := by
  have := hR.sp_lt; have := hr.1; simp only [maxPool] at *; omega

/-- A sub-list. -/
theorem BbRange.take {base : Nat} {l : List Nat} (hr : BbRange c st base l) (j : Nat) :
    BbRange c st base (l.take j) :=
  ⟨by have := hr.1; simp; omega, fun k i hk => hr.2 k i (by
    rw [List.getElem?_take] at hk; split at hk <;> simp_all)⟩

/-- A list on top of the stack is a range. -/
theorem StkTop.bbRange {base : Nat} {l : List Nat} (ht : StkTop c st base l) : BbRange c st base l :=
  ⟨Nat.le_of_eq ht.1.symm, ht.2⟩

/-- Ranges survive pushes. -/
theorem BbRange.frame {c' : CMem} {base : Nat} {l : List Nat} (hr : BbRange c st base l)
    (hpre : ∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) (hsp : c.k.sp.toNat ≤ c'.k.sp.toNat) :
    BbRange c' st base l :=
  ⟨by have := hr.1; omega, hr.2.frame (fun j hj => hpre j (by have := hr.1; omega))⟩

end range

/-! ## `zipAll` one position at a time -/

theorem bb_zipAll_drop (f : Nat → Nat → Bool) {xs ys : List Nat} {k : Nat} (hx : k < xs.length)
    (hy : k < ys.length) :
    zipAll f (xs.drop k) (ys.drop k) = (f xs[k] ys[k] && zipAll f (xs.drop (k + 1)) (ys.drop (k + 1))) := by
  rw [List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy]; rfl

theorem bb_zipAll_step {f : Nat → Nat → Bool} {xs ys : List Nat} {k : Nat} {P : Prop}
    (hx : k < xs.length) (hy : k < ys.length) (H : zipAll f (xs.drop k) (ys.drop k) = true → P)
    (hf : f xs[k] ys[k] = true) : zipAll f (xs.drop (k + 1)) (ys.drop (k + 1)) = true → P :=
  fun h' => H (by rw [bb_zipAll_drop f hx hy, hf, h']; rfl)

theorem bb_zipAll_end {f : Nat → Nat → Bool} {xs ys : List Nat} {k : Nat} {P : Prop}
    (hx : xs.length ≤ k) (hy : ys.length ≤ k) (H : zipAll f (xs.drop k) (ys.drop k) = true → P) : P :=
  H (by rw [List.drop_of_length_le hx, List.drop_of_length_le hy]; rfl)

/-! ## `bb_zip_not` -/

def BbZipNotSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (pb xb : Nat) (ps xs : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_zip_not"
      (fun vs s => vs = [.ptr sb 0, uv pb, uv ps.length, uv xb, uv xs.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st pb ps ∧
        BbRange c st xb xs)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (zipAll (fun p x => isNotOf st p x) ps xs = true) r s')

theorem bb_zip_not_spec : BbZipNotSpec (State := State) := by
  intro W sb X c0 c prems params st pb xb ps xs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbZipNot) rfl
  rintro vs s ⟨rfl, h, hR, hp, hx⟩
  simp [bbZipNot, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbZipNot) rfl
  simp only [bbZipNot, Stmt.block, initLocals, List.map, Ty.zero]
  have hpb := hp.bound hR
  have hxb := hx.bound hR
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hlen => ?_⟩
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" ["ok"] ps.length
    (fun k => zipAll (fun p x => isNotOf st p x) (ps.drop k) (xs.drop k) = true →
      zipAll (fun p x => isNotOf st p x) ps xs = true))
  · exact ⟨rfl, 0, [0#32], rfl, by simp [bbSets, Env.set], by omega, fun h => h⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain ⟨ok, rfl⟩ := len_shape 1 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact bb_zipAll_end (by omega) (by omega) hres
  have hkx : k < xs.length := by omega
  have hstk := hp.stk hR h hlt
  refine WP.bb_call (bb_is1_spec W sb X c0 c prems params st ps[k] 385#32 .boolNot xs[k]) ?_
    ⟨rfl, h, hR, hp.lt hlt, hx.lt hkx, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hstk, hp.rd hlt, hx.rd hkx]
  intro r hr
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hr0 => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, k + 1, [r], rfl, by simp [bbSets, Env.set], by omega, ?_⟩
  exact bb_zipAll_step hlt hkx hres (hr hr0)

/-! ## `bb_list_eq` -/

theorem bb_drop_eq_step {xs ys : List Nat} {k : Nat} (hx : k < xs.length) (hy : k < ys.length)
    (he : xs[k] = ys[k]) (h : xs.drop (k + 1) = ys.drop (k + 1)) : xs.drop k = ys.drop k := by
  rw [List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy, he, h]

def BbListEqSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (pb xb : Nat) (ps xs : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_list_eq"
      (fun vs s => vs = [.ptr sb 0, uv pb, uv ps.length, uv xb, uv xs.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st pb ps ∧
        BbRange c st xb xs)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (ps = xs) r s')

theorem bb_list_eq_spec : BbListEqSpec (State := State) := by
  intro W sb X c0 c prems params st pb xb ps xs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbListEq) rfl
  rintro vs s ⟨rfl, h, hR, hp, hx⟩
  simp [bbListEq, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbListEq) rfl
  simp only [bbListEq, Stmt.block, initLocals, List.map, Ty.zero]
  have hpb := hp.bound hR
  have hxb := hx.bound hR
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hlen => ?_⟩
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" [] ps.length
    (fun k => ps.drop k = xs.drop k → ps = xs))
  · exact ⟨rfl, 0, [], rfl, by simp [bbSets, Env.set], by omega, fun h => by simpa using h⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain rfl := len_shape 0 hws
  simp only [bbSets, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact hres (by rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)])
  have hkx : k < xs.length := by omega
  have hstk := hp.stk hR h hlt
  have h1 := hp.lt hlt
  have h2 := hx.lt hkx
  apply WP.guard_lit
  rule_simp [hstk, hp.rd hlt, hx.rd hkx]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun he => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, k + 1, [], rfl, by simp [bbSets, Env.set], by omega, ?_⟩
  exact fun hd => hres (bb_drop_eq_step hlt hkx he hd)

/-! ## Calling helpers -/

/-- `x = f(args); rest` for a pure helper returning the word of `v`. -/
theorem WP.bb_pure {Q : (Post prog State)} {env : Env} {s : (KernelState prog State)} {x : Var} {f : String}
    {es : List Expr} {rest : Stmt} {vs : List EmbC.Val} {pre : List EmbC.Val → (KernelState prog State) → Prop}
    {v : Nat}
    (hspec : FnSpec (State := State) Vbcf.prog f pre (fun _ s0 => PureRet s0 v))
    (hargs : evalArgs Vbcf.prog env s.mem es = some vs) (hpre : pre vs s)
    (H : match env.assign s.mem x (uv v) with
      | none => False
      | some env' => WP Vbcf.prog rest Q env' s) :
    WP Vbcf.prog (.seq (.call (some x) f es) rest) Q env s := by
  apply WP.call_seq hspec hargs hpre
  rintro rv s' ⟨rfl, rfl⟩
  exact H

/-! ## `preSum`, `preAdder` -/

/-- `p` is argument `k` of the first argument of `r`. -/
def BbPreAt (st : St) (k r p : Nat) : Prop :=
  ∃ n s ns, st.pool[r]? = some n ∧ n.args[0]? = some s ∧ st.pool[s]? = some ns ∧
    ns.args[k]? = some p

theorem bb_toList_cons {args : Array Nat} {s : Nat} (h : args[0]? = some s) :
    args.toList = s :: args.toList.drop 1 := by
  rcases args with ⟨l⟩
  rcases l with _ | ⟨a, l⟩ <;> simp_all

theorem bb_toList_cons2 {args : Array Nat} {q : Nat} (h : args[1]? = some q) :
    ∃ a tl, args.toList = a :: q :: tl := by
  rcases args with ⟨l⟩
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all

theorem bb_preSum_of {st : St} : ∀ {rs L : List Nat}, L.length = rs.length →
    (∀ (j : Nat) (hj : j < rs.length) (hj' : j < L.length), BbPreAt st 0 rs[j] L[j]) →
    preSum st rs = some L
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, p :: L, hl, H => by
    obtain ⟨⟨op, args⟩, s, ⟨sop, sargs⟩, hn, ha, hs, hsa⟩ := H 0 (by simp) (by simp)
    have ih := bb_preSum_of (rs := rs) (L := L) (by simpa using hl)
      (fun j hj hj' => H (j + 1) (by simp; omega) (by simp; omega))
    simp only at ha hsa
    simp only [List.getElem_cons_zero] at hn hsa ha
    obtain ⟨tl, htl⟩ : ∃ tl, args.toList = s :: tl := ⟨_, bb_toList_cons ha⟩
    obtain ⟨tl2, htl2⟩ : ∃ tl, sargs.toList = p :: tl := ⟨_, bb_toList_cons hsa⟩
    unfold preSum
    simp only [hn, htl, hs, htl2, ih, Option.map_some]

theorem bb_preAdder_of {st : St} : ∀ {rs L : List Nat}, L.length = rs.length →
    (∀ (j : Nat) (hj : j < rs.length) (hj' : j < L.length), BbPreAt st 1 rs[j] L[j]) →
    preAdder st rs = some L
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, p :: L, hl, H => by
    obtain ⟨⟨op, args⟩, s, ⟨sop, sargs⟩, hn, ha, hs, hsa⟩ := H 0 (by simp) (by simp)
    have ih := bb_preAdder_of (rs := rs) (L := L) (by simpa using hl)
      (fun j hj hj' => H (j + 1) (by simp; omega) (by simp; omega))
    simp only at ha hsa
    simp only [List.getElem_cons_zero] at hn hsa ha
    obtain ⟨a0, tl2, ha0⟩ := bb_toList_cons2 hsa
    obtain ⟨tl, htl⟩ : ∃ tl, args.toList = s :: tl := ⟨_, bb_toList_cons ha⟩
    unfold preAdder
    simp only [hn, htl, hs, ha0, ih, Option.map_some]

/-! ## Helpers that push a list -/

/-- What a helper that pushes a list returns: `NOID`, or the old `sp` with a list `L`
satisfying `P` pushed from there. -/
def BbPush (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (c : CMem) (P : List Nat → Prop) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (r = noid ∨ (r = BitVec.ofNat 32 c.k.sp.toNat ∧
      (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧ c.k.sp.toNat ≤ c'.k.sp.toNat ∧
      ∃ L, P L ∧ StkTop c' st c.k.sp.toNat L))

/-- Loop invariant of a pushing loop with counter `iv`. -/
def BbPushInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (c : CMem) (env0 : Env) (iv : Var) (vs : List Var) (n : Nat) (P : Nat → List Nat → Prop) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (L : List Nat) (ws : List (BitVec 32)), ws.length = vs.length ∧
    env = bbSets (env0.set iv (uv k)) (vs.zip ws) ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧ c.k.sp.toNat ≤ c'.k.sp.toNat ∧
    k ≤ n ∧ P k L ∧ StkTop c' st c.k.sp.toNat L

theorem BbPush.fail {W : World} {sb : Nat} {X : Ctx} {c0 c c' : CMem} {prems params : List Nat}
    {st : VSt} {P : List Nat → Prop} {s' : (KernelState prog State)} (h : Holds W s'.mem sb c')
    (hR : RCtx W X c0 prems params c' st) : BbPush W sb X c0 prems params st c P noid s' :=
  ⟨c', h, hR, Or.inl rfl⟩

/-- A successful push of the id of node `x`: the list grows by `x`. -/
theorem Pushed.bb {W : World} {X : Ctx} {c0 c c' : CMem} {prems params : List Nat} {st : VSt}
    {x : Nat} {ok : BitVec 32} (hP : Pushed W X c0 prems params st c (BitVec.ofNat 32 (st.id x)) c' ok)
    (hok : ¬ ok = 0#32) {base : Nat} {L : List Nat} (ht : StkTop c st base L) (hx : st.lv x) :
    StkTop c' st base (L ++ [x]) ∧ c'.k.sp.toNat = c.k.sp.toNat + 1 := by
  refine ⟨StkTop.push ht hP hok hx, ?_⟩
  obtain ⟨-, -, hcase⟩ := hP
  rcases hcase with ⟨h0, -⟩ | ⟨-, -, hsp, -⟩
  · exact absurd h0 hok
  · exact hsp

theorem Pushed.bb_pre {W : World} {X : Ctx} {c0 c c' : CMem} {prems params : List Nat} {st : VSt}
    {v ok : BitVec 32} (hP : Pushed W X c0 prems params st c v c' ok) :
    (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧ c.k.sp.toNat ≤ c'.k.sp.toNat := by
  obtain ⟨-, hpre, hcase⟩ := hP
  refine ⟨hpre, ?_⟩
  rcases hcase with ⟨-, hsp⟩ | ⟨-, -, hsp, -⟩
  · rw [hsp]; exact Nat.le_refl _
  · omega

/-! ## `bb_pre` -/

theorem VInv.bb_size_le {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) : n.args.size ≤ 255 := by
  by_cases hl : IsLeaf n.op
  · rw [hc.bb_leaf_args hn hl]; omega
  · have := (hc.fits i _ hn).tailLen
    rw [tailLen_of_not_leaf hl] at this
    omega

/-- A node with arguments is not a leaf. -/
theorem VInv.bb_not_leaf {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) (h : n.args.size ≠ 0) : ¬ IsLeaf n.op :=
  fun hl => h (hc.bb_leaf_args hn hl)

/-- Argument `k` of a node with more than `k` arguments. -/
theorem VInv.bb_rdArg {posOf : Nat → Nat} {c : CMem} {st : VSt} (hc : VInv posOf c st)
    {i : Nat} {n : Node} (hn : st.pool[i]? = some n) {k : Nat} (hk : k < n.args.size)
    (hi : st.lv i := by vlv) :
    rd c.pool (st.id i + 1 + k) = some (uv (st.id n.args[k])) :=
  hc.rdArg hn (hc.bb_not_leaf hn (by omega)) hk hi

def BbPreSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (rb : Nat) (rs : List Nat) (kk : Nat),
    FnSpec (State := State) Vbcf.prog "bb_pre"
      (fun vs s => vs = [.ptr sb 0, uv rb, uv rs.length, uv kk] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st rb rs ∧ kk ≤ 1)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧ BbPush W sb X c0 prems params st c
        (fun L => L.length = rs.length ∧
          ∀ (j : Nat) (hj : j < rs.length) (hj' : j < L.length), BbPreAt st kk rs[j] L[j]) r s')

theorem bb_pre_spec : BbPreSpec (State := State) := by
  intro W sb X c0 c prems params st rb rs kk
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbPre) rfl
  rintro vs s ⟨rfl, h, hR, hr, hkk⟩
  simp [bbPre, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbPre) rfl
  simp only [bbPre, Stmt.block, initLocals, List.map, Ty.zero]
  have hrb := hr.bound hR
  rule_assign
  apply WP.bb_loop (fun env0 => BbPushInv W sb X c0 prems params st c env0 "i" ["r", "s", "m", "ok"]
    rs.length (fun k L => L.length = k ∧
      ∀ (j : Nat) (hj : j < rs.length) (hj' : j < L.length), BbPreAt st kk rs[j] L[j]))
  · exact ⟨c, 0, [], [0#32, 0#32, 0#32, 0#32], rfl, by simp [bbSets, Env.set], h, hR,
      fun _ _ => rfl, Nat.le_refl _, by omega, ⟨rfl, fun j _ hj => by simp at hj⟩, StkTop.nil rfl⟩
  clear h hR
  rintro env s' ⟨c', k, L, ws, hws, rfl, h, hR, hpre, hsp, hk, ⟨hL, hLp⟩, htop⟩
  obtain ⟨wr, ws1, wm, wok, rfl⟩ := len_shape 4 hws
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  have hr' := hr.frame hpre hsp
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp
    refine ⟨c', h, hR, Or.inr ⟨(bv_ofNat_toNat _).symm, hpre, hsp, L, ⟨by omega, hLp⟩, htop⟩⟩
  have hstk := hr'.stk hR h hlt
  have hrk := hr'.lt hlt
  rule_assign [hstk, hr'.rd hlt]
  obtain ⟨nr, hnr⟩ := node_of_lv hrk
  apply WP.bb_pure (bb_nargs_spec W sb X c0 c' prems params st rs[k] nr) (by rule_simp)
    ⟨rfl, h, hR, hnr, by vlv⟩
  rule_simp
  apply WP.ifRet
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · simp only [LoopQ, RetQ]
    exact BbPush.fail h hR
  have hsz := hR.core.bb_size_le hnr
  rw [uv_eq_zero_iff (by omega)] at h0
  have h1 := hR.core.bb_rdArg hnr (k := 0) (by omega)
  simp only [Nat.add_zero] at h1
  have hsk : st.lv nr.args[0] := hR.core.bb_arg_lt hnr (Array.getElem_mem _)
  rule_assign [h1]
  obtain ⟨ns, hns⟩ := node_of_lv hsk
  apply WP.bb_pure (bb_nargs_spec W sb X c0 c' prems params st nr.args[0] ns) (by rule_simp)
    ⟨rfl, h, hR, hns, by vlv⟩
  rule_simp
  have hsz2 := hR.core.bb_size_le hns
  apply WP.ifRet
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · simp only [LoopQ, RetQ]
    exact BbPush.fail h hR
  have h2 := hR.core.bb_rdArg hns (k := kk) (by omega)
  have hpk : st.lv ns.args[kk] := hR.core.bb_arg_lt hns (Array.getElem_mem _)
  apply WP.rule_push h hR
  rule_simp [h2]
  intro s2 c2 ok hh2 hP
  obtain ⟨hpre2, hsp2⟩ := hP.bb_pre
  have hpre' : ∀ j, j < c.k.sp.toNat → c2.stk[j]? = c.stk[j]? := fun j hj => by
    rw [hpre2 j (by omega), hpre j hj]
  clear h hR
  have h := hh2
  have hR := hP.1
  apply WP.ifRet
  rule_simp
  refine ⟨fun h0 => ?_, fun hok => ?_⟩
  · simp only [LoopQ, RetQ]
    exact BbPush.fail h hR
  obtain ⟨htop2, -⟩ := hP.bb hok htop hpk
  apply WP.assign_loop
  rule_simp
  refine ⟨c2, k + 1, L ++ [ns.args[kk]], [BitVec.ofNat 32 (st.id rs[k]),
    BitVec.ofNat 32 (st.id nr.args[0]), BitVec.ofNat 32 ns.args.size, ok], rfl,
    by simp [bbSets, Env.set], h, hR,
    hpre', by omega, by omega, ⟨by simp; omega, fun j hj hj' => ?_⟩, htop2⟩
  rcases Nat.lt_or_ge j L.length with hjl | hjl
  · rw [List.getElem_append_left hjl]; exact hLp j hj hjl
  · have hjk : j = k := by simp at hj'; omega
    subst hjk
    rw [List.getElem_append_right (by omega)]
    simp only [hL, Nat.sub_self, List.getElem_cons_zero]
    exact ⟨nr, nr.args[0], ns, hnr, by simp, hns, by simp⟩

/-! ## `bb_carry` -/

def BbCarrySpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (pa pb pc cc : Nat),
    FnSpec (State := State) Vbcf.prog "bb_carry"
      (fun vs s => vs = [.ptr sb 0, uv (st.id pa), uv (st.id pb), uv (st.id pc),
          uv (st.id cc)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv pa ∧
        st.lv pb ∧ st.lv pc ∧ st.lv cc)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (carryNode st pa pb pc cc = true) r s')

theorem bb_carry_spec : BbCarrySpec (State := State) := by
  intro W sb X c0 c prems params st pa pb pc cc
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbCarry) rfl
  rintro vs s ⟨rfl, h, hR, hpa, hpb, hpc, hcc⟩
  simp [bbCarry, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbCarry) rfl
  simp only [bbCarry, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨nc, hnc⟩ := node_of_lv hcc
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnc]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh => ?_⟩
  obtain ⟨u, v, rfl, hu, hv⟩ := hR.core.bb_hdr2 hnc (op := .disj) (by decide) (by decide)
    (by decide) (by decide) hh
  rule_assign [hR.core.rd2 hnc]
  rule_assign [hR.core.rd2 hnc]
  refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st u 513#32 .conj pa pb) ?_
    ⟨rfl, h, hR, hu, hpa, hpb, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp
  intro r hr
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hr0 => ?_⟩
  obtain ⟨nv, hnv⟩ := node_of_lv hv
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnv]
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hh1 => ?_⟩
  obtain ⟨x, w, rfl, hx, hw⟩ := hR.core.bb_hdr2 hnv (op := .conj) (by decide) (by decide)
    (by decide) (by decide) hh1
  refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st x 569#32 .boolXor pa pb) ?_
    ⟨rfl, h, hR, hx, hpa, hpb, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp [hR.core.rd2 hnv]
  intro r2 hr2
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hr20 => ?_⟩
  apply WP.rule_ret
  rule_simp [hR.core.rd2 hnv]
  refine ⟨rfl, fun hne => ?_⟩
  have hww : w = pc := by
    by_cases hc : w = pc
    · exact hc
    · simp [hc] at hne
  have e1 := hr hr0
  have e2 := hr2 hr20
  simp only [carryNode, hnc, hnv]
  simp only [isConjOf, isXorOf, e1, e2, hww, beq_self_eq_true, Bool.and_self]

/-! ## `bb_ripple` -/

/-- `BbInv` where the condition may also mention the scratch words. -/
def BbInvW (s : (KernelState prog State)) (env0 : Env) (iv : Var) (vs : List Var) (n : Nat)
    (P : Nat → List (BitVec 32) → Prop) : Env → (KernelState prog State) → Prop :=
  fun env s' => s' = s ∧ ∃ (k : Nat) (ws : List (BitVec 32)), ws.length = vs.length ∧
    env = bbSets (env0.set iv (uv k)) (vs.zip ws) ∧ k ≤ n ∧ P k ws

theorem bb_rippleGo_step {st : St} {as bs rs : List Nat} {k pa pb pc s c : Nat}
    (ha : k < as.length) (hb : k < bs.length) (hr : k < rs.length)
    (hn : st.pool[rs[k]]? = some ⟨.boolXor, #[s, c]⟩) (hs : isXorOf st s as[k] bs[k] = true)
    (hc : carryNode st pa pb pc c = true)
    (H : rippleGo st (as.drop (k + 1)) (bs.drop (k + 1)) (rs.drop (k + 1)) as[k] bs[k] c = true) :
    rippleGo st (as.drop k) (bs.drop k) (rs.drop k) pa pb pc = true := by
  rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb, List.drop_eq_getElem_cons hr]
  simp only [rippleGo, hn, hs, hc, H, Bool.and_self]

theorem bb_ripple_first {st : VSt} {bi : Builtins} {as bs rs : List Nat} {init : Bool} {s c : Nat}
    (ha : 0 < as.length) (hb : 0 < bs.length) (hr : 0 < rs.length)
    (hn : st.pool[rs[0]]? = some ⟨.boolXor, #[s, c]⟩) (hs : isXorOf st s as[0] bs[0] = true)
    (hc : c = if init then bi.tt else bi.ff)
    (H : rippleGo st (as.drop 1) (bs.drop 1) (rs.drop 1) as[0] bs[0] c = true) :
    ripple st bi as bs rs init = true := by
  rcases as with _ | ⟨a0, as⟩
  · simp at ha
  rcases bs with _ | ⟨b0, bs⟩
  · simp at hb
  rcases rs with _ | ⟨r0, rs⟩
  · simp at hr
  simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at hn hs H
  subst hc
  simp only [ripple, hn, hs, H, beq_self_eq_true, Bool.and_self]

theorem bb_rippleGo_end {st : St} {as bs rs : List Nat} {k pa pb pc : Nat} (ha : as.length ≤ k)
    (hb : bs.length ≤ k) (hr : rs.length ≤ k) :
    rippleGo st (as.drop k) (bs.drop k) (rs.drop k) pa pb pc = true := by
  rw [List.drop_of_length_le ha, List.drop_of_length_le hb, List.drop_of_length_le hr]; rfl

/-- The condition of the loop of `bb_ripple` after `k` positions: for `k > 0` the previous
position is in `pa`, `pb`, `pc`, and what is left to check is a `rippleGo`. -/
def BbRipP (st : VSt) (bi : Builtins) (as bs rs : List Nat) (init : Bool) (k : Nat)
    (ws : List (BitVec 32)) : Prop :=
  k ≠ 0 → ∃ pc, st.lv pc ∧
    ws[5]? = some (BitVec.ofNat 32 (st.id (as.getD (k - 1) 0))) ∧
    ws[6]? = some (BitVec.ofNat 32 (st.id (bs.getD (k - 1) 0))) ∧
    ws[7]? = some (BitVec.ofNat 32 (st.id pc)) ∧
    (rippleGo st (as.drop k) (bs.drop k) (rs.drop k) (as.getD (k - 1) 0) (bs.getD (k - 1) 0) pc = true →
      ripple st bi as bs rs init = true)

def BbRippleSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (xb yb rb : Nat) (xs ys rs : List Nat) (init : Bool),
    FnSpec (State := State) Vbcf.prog "bb_ripple"
      (fun vs s => vs = [.ptr sb 0, uv xb, uv xs.length, uv yb, uv ys.length, uv rb, uv rs.length,
          .u32 (if init then 1#32 else 0#32)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st xb xs ∧
        BbRange c st yb ys ∧ BbRange c st rb rs)
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (ripple st X.bi xs ys rs init = true) r s')

theorem bb_ripple_spec : BbRippleSpec (State := State) := by
  intro W sb X c0 c prems params st xb yb rb xs ys rs init
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbRipple) rfl
  rintro vs s ⟨rfl, h, hR, hx, hy, hr⟩
  simp [bbRipple, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbRipple) rfl
  simp only [bbRipple, Stmt.block, initLocals, List.map, Ty.zero]
  have hxb := hx.bound hR
  have hyb := hy.bound hR
  have hrb := hr.bound hR
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hlen hly hlr => ?_⟩
  have hx0 : 0 < xs.length := by
    rcases xs with _ | _
    · exact absurd rfl hlen
    · simp
  clear hlen
  apply WP.bb_loop (fun env0 => BbInvW s env0 "i" ["a", "b", "r", "s", "c", "pa", "pb", "pc", "ok"]
    xs.length (BbRipP st X.bi xs ys rs init))
  · exact ⟨rfl, 0, [0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32], rfl,
      by simp [bbSets, Env.set], by omega, fun h0 => absurd rfl h0⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, rfl⟩ : ∃ w1 w2 w3 w4 w5 w6 w7 w8 w9,
      ws = [w1, w2, w3, w4, w5, w6, w7, w8, w9] := by
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ |
      ⟨w9, _ | ⟨w10, ws⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hws
    exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    have hk0 : k ≠ 0 := by omega
    obtain ⟨pc, -, -, -, -, H⟩ := hres hk0
    exact H (bb_rippleGo_end (by omega) (by omega) (by omega))
  have hky : k < ys.length := by omega
  have hkr : k < rs.length := by omega
  have hstk := hx.stk hR h hlt
  have hak := hx.lt hlt
  have hbk := hy.lt hky
  have hrk := hr.lt hkr
  rule_assign [hstk, hx.rd hlt]
  rule_assign [hstk, hy.rd hky]
  rule_assign [hstk, hr.rd hkr]
  obtain ⟨nr, hnr⟩ := node_of_lv hrk
  apply WP.guard_lit
  rule_simp [hR.core.rdHdr hnr]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hh => ?_⟩
  obtain ⟨sx, cx, rfl, hsx, hcx⟩ := hR.core.bb_hdr2 hnr (op := .boolXor) (by decide) (by decide)
    (by decide) (by decide) hh
  rule_assign [hR.core.rd2 hnr]
  rule_assign [hR.core.rd2 hnr]
  refine WP.bb_call (bb_is2_spec W sb X c0 c prems params st sx 569#32 .boolXor xs[k] ys[k]) ?_
    ⟨rfl, h, hR, hsx, hak, hbk, by decide, by decide, by decide, by decide⟩ ?_
  · rule_simp
  intro r1 hr1
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hr10 => ?_⟩
  have hsx' := hr1 hr10
  have htt := hR.tt_lt
  have hff := hR.ff_lt
  have hgx : xs.getD (k + 1 - 1) 0 = xs[k] := by simp [List.getElem?_eq_getElem hlt]
  have hgy : ys.getD (k + 1 - 1) 0 = ys[k] := by simp [List.getElem?_eq_getElem hky]
  by_cases hk0 : k = 0
  · subst hk0
    apply WP.seq_mid_env (fun env0 env' s'' => s'' = s' ∧ env' = env0 ∧
      cx = if init then X.bi.tt else X.bi.ff)
    · apply WP.ite
      rule_simp
      apply WP.ite
      cases init
      · rule_simp
        apply WP.ite
        rule_simp
        refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ, BbOK.zero], fun he => ?_⟩
        apply WP.skip; simp [LoopQ, he]
      · rule_simp
        apply WP.ite
        rule_simp
        refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ, BbOK.zero], fun he => ?_⟩
        apply WP.skip; simp [LoopQ, he]
    rintro env' s'' ⟨rfl, rfl, hcx0⟩
    rule_assign
    rule_assign
    rule_assign
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, 1, [BitVec.ofNat 32 (st.id xs[0]), BitVec.ofNat 32 (st.id ys[0]),
      BitVec.ofNat 32 (st.id rs[0]), BitVec.ofNat 32 (st.id sx),
      BitVec.ofNat 32 (st.id cx), BitVec.ofNat 32 (st.id xs[0]),
      BitVec.ofNat 32 (st.id ys[0]), BitVec.ofNat 32 (st.id cx), r1], rfl, by simp [bbSets, Env.set], by omega,
      fun _ => ⟨cx, hcx, by rw [hgx] <;> rfl, by rw [hgy] <;> rfl, rfl, ?_⟩⟩
    intro H
    simp only [Nat.zero_add, Nat.sub_self] at hgx hgy H
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hky, Option.getD_some] at H
    exact bb_ripple_first hlt hky hkr hnr hsx' hcx0 H
  obtain ⟨pc, hpc, h6, h7, h8, H⟩ := hres hk0
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h6 h7 h8
  subst h6 h7 h8
  have hpa : st.lv (xs.getD (k - 1) 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hx.lt (by omega)
  have hpb : st.lv (ys.getD (k - 1) 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hy.lt (by omega)
  generalize xs.getD (k - 1) 0 = pa at *
  generalize ys.getD (k - 1) 0 = pb at *
  apply WP.seq_mid_env (fun env0 env' s'' => s'' = s' ∧ ∃ r2, env' = env0.set "ok" (.u32 r2) ∧
    carryNode st pa pb pc cx = true)
  · apply WP.ite
    rule_simp [hk0]
    refine WP.bb_call (bb_carry_spec W sb X c0 c prems params st _ _ pc cx) ?_
      ⟨rfl, h, hR, hpa, hpb, hpc, hcx⟩ ?_
    · rule_simp
    intro r2 hr2
    rule_simp
    apply WP.ite
    rule_simp
    refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ, BbOK.zero], fun hr20 => ?_⟩
    apply WP.skip
    simp only [LoopQ]
    exact ⟨trivial, ⟨r2, rfl⟩, hr2 hr20⟩
  rintro env' s'' ⟨rfl, r2, rfl, hcar⟩
  rule_assign
  rule_assign
  rule_assign
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, k + 1, [BitVec.ofNat 32 (st.id xs[k]), BitVec.ofNat 32 (st.id ys[k]),
    BitVec.ofNat 32 (st.id rs[k]), BitVec.ofNat 32 (st.id sx),
    BitVec.ofNat 32 (st.id cx), BitVec.ofNat 32 (st.id xs[k]),
    BitVec.ofNat 32 (st.id ys[k]), BitVec.ofNat 32 (st.id cx), r2], rfl, by simp [bbSets, Env.set], by omega,
    fun _ => ⟨cx, hcx, by rw [hgx] <;> rfl, by rw [hgy] <;> rfl, rfl, ?_⟩⟩
  intro H'
  rw [hgx, hgy] at H'
  exact H (bb_rippleGo_step hlt hky hkr hnr hsx' hcar H')

end Vbcf.Proof
