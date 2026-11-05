import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.RuleLib
import Vbcf.Proof.Intern

/-!
# Vbcf proofs: the Bool family, part 1 — infrastructure

Lemmas shared by the proofs of `Vbcf/Rules/Bool.lean`: carrying node facts across a builder
call (`CoreInv.rd*_ext`), composing builder outcomes (`Built.trans`), the postcondition of a
helper that builds a node (`HRet`/`HQ`) and calling such a helper (`WP.rule_hcall`).
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The code field of a header, with no side condition (for `rule_simp`, whichever way it
normalises `hdr & 0xff`). -/
theorem hdrW_mod_code (n : Node) : hdrW n % 256 = opC n.op := by
  have h1 := opC_lt n.op
  unfold hdrW; omega

/-- `(hdr & 0xff) == CODE` once `hdr & 0xff` has become the word of `hdrW n % 256`. -/
theorem uv_code_eq (n : Node) (k : Nat) (hk : k < 256) :
    (BitVec.ofNat 32 (hdrW n % 256) = BitVec.ofNat 32 k) ↔ opC n.op = k := by
  rw [uv_inj (by omega) (by omega), hdrW_mod_code]

/-- … or once it has become the word of `opC n.op`. -/
theorem uv_opC_eq (n : Node) (k : Nat) (hk : k < 256) :
    (BitVec.ofNat 32 (opC n.op) = BitVec.ofNat 32 k) ↔ opC n.op = k := by
  have := opC_lt n.op
  rw [uv_inj (by omega) (by omega)]

/-! ## Node facts after a builder call

After `x = mk_…(st, …)`, the Lean state is `st'`, a `PoolExt` of `st`, but the C locals still
hold ids computed as `offs st.pool i`.  These restate `rd1`/`rd2`/`rd3`/`rdN` for the new C
state at the old id. -/

section ext
variable {posOf : Nat → Nat} {c : CMem} {st st' : VSt}

theorem VInv.rd1_ext (hc : VInv posOf c st') (he : VExt st st') {i : Nat} {op : Op} {a : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hl : ¬ IsLeaf op := by decide) (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, #[a]⟩)) ∧
    rd c.pool (st.id i + 1) = some (uv (st'.id a)) := by
  have := hc.rd1 (he.get hn) hl (he.lt hi)
  rwa [he.id hi] at this

theorem VInv.rd2_ext (hc : VInv posOf c st') (he : VExt st st') {i : Nat} {op : Op} {a b : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hl : ¬ IsLeaf op := by decide) (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, #[a, b]⟩)) ∧
    rd c.pool (st.id i + 1) = some (uv (st'.id a)) ∧
    rd c.pool (st.id i + 2) = some (uv (st'.id b)) := by
  have := hc.rd2 (he.get hn) hl (he.lt hi)
  rwa [he.id hi] at this

theorem VInv.rd3_ext (hc : VInv posOf c st') (he : VExt st st') {i : Nat} {op : Op}
    {a b d : Nat} (hn : st.pool[i]? = some ⟨op, #[a, b, d]⟩) (hl : ¬ IsLeaf op := by decide) (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, #[a, b, d]⟩)) ∧
    rd c.pool (st.id i + 1) = some (uv (st'.id a)) ∧
    rd c.pool (st.id i + 2) = some (uv (st'.id b)) ∧
    rd c.pool (st.id i + 3) = some (uv (st'.id d)) := by
  have := hc.rd3 (he.get hn) hl (he.lt hi)
  rwa [he.id hi] at this

theorem VInv.rdN_ext (hc : VInv posOf c st') (he : VExt st st') {i : Nat} {op : Op}
    {args : Array Nat} (hn : st.pool[i]? = some ⟨op, args⟩) (hl : ¬ IsLeaf op := by decide) (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, args⟩)) ∧
    (BitVec.ofNat 32 (hdrW ⟨op, args⟩) >>> 8 &&& 255#32 = BitVec.ofNat 32 args.size) ∧
    ∀ (k : Nat) (hk : k < args.size),
      rd c.pool (st.id i + 1 + k) = some (uv (st'.id args[k])) := by
  have := hc.rdN (he.get hn) hl (he.lt hi)
  rwa [he.id hi] at this

end ext

/-! ## Composing builder outcomes -/

section built
variable {W : World} {X : Ctx} {c0 c c1 c2 : CMem} {prems params : List Nat} {st st1 : VSt}
  {sb : Nat} {s : (KernelState prog State)} {P P' : St → Nat → Prop} {r : BitVec 32}

theorem Built.mono (hB : Built W X c0 prems params c st P c2 r) (himp : ∀ st' i, P st' i → P' st' i) :
    Built W X c0 prems params c st P' c2 r := by
  rcases hB with h | ⟨st', i, hP, hR, hext, hs, hi, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨st', i, himp st' i hP, hR, hext, hs, hi, hr⟩

/-- A builder call made after an earlier one, seen from the state before the first. -/
theorem Built.trans (hext : VExt st st1) (hs : c1.stk = c.stk ∧ c1.k.sp = c.k.sp)
    (hB : Built W X c0 prems params c1 st1 P c2 r) (himp : ∀ st' i, P st' i → P' st' i) :
    Built W X c0 prems params c st P' c2 r := by
  rcases hB with h | ⟨st', i, hP, hR, hext', hs', hi, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨st', i, himp st' i hP, hR, hext.trans hext', ⟨hs'.1.trans hs.1, hs'.2.trans hs.2⟩,
      hi, hr⟩

/-- The outcome "nothing was built, `r` is the id of `i`". -/
theorem Built.id (hR : RCtx W X c0 prems params c st) {i : Nat} (hi : st.lv i)
    (hP : P st i) : Built W X c0 prems params c st P c (BitVec.ofNat 32 (st.id i)) :=
  Or.inr ⟨st, i, hP, hR, VExt.refl st, ⟨rfl, rfl⟩, hi, rfl⟩

/-! ## Helpers that build a node

A helper such as `bl_equiv_elim_clause` returns an id or `NOID`, exactly like a builder; its
postcondition is `HRet`: the final C state is a `Built` outcome for the Lean function `P`
the helper mirrors. -/

/-- What must hold when a node-building helper returns the word `r` in state `s'`. -/
def HRet (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem) (st : VSt)
    (P : St → Nat → Prop) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ Built W X c0 prems params c st P c' r

/-- The postcondition of the body of such a helper. -/
def HQ (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem) (st : VSt)
    (P : St → Nat → Prop) : (Post prog State) :=
  fun o _ s' =>
    match o with
    | .ret (some (.u32 r)) => HRet W sb X c0 prems params c st P r s'
    | _ => False

instance : RetsTo (State := State) (HQ W sb X c0 prems params c st P) (HRet W sb X c0 prems params c st P) :=
  ⟨fun _ _ _ h => h⟩

/-- The postcondition of the call, as `FnSpec` wants it. -/
def HPost (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem) (st : VSt)
    (P : St → Nat → Prop) : Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ r, rv = some (.u32 r) ∧ HRet W sb X c0 prems params c st P r s'

/-- Returning `NOID` from a helper. -/
theorem HRet.fail {c' : CMem} (h : Holds W s.mem sb c') :
    HRet W sb X c0 prems params c st P 4294967295#32 s := ⟨c', h, Or.inl rfl⟩

/-- Returning the word of a builder call made in the state the helper was entered in. -/
theorem HRet.of_built {c' : CMem} (h : Holds W s.mem sb c')
    (hB : Built W X c0 prems params c st P c' r) (himp : ∀ st' i, P st' i → P' st' i) :
    HRet W sb X c0 prems params c st P' r s := ⟨c', h, hB.mono himp⟩

/-- Returning the word of a builder call made after an earlier builder call. -/
theorem HRet.of_built2 {c' : CMem} (h : Holds W s.mem sb c') (hext : VExt st st1)
    (hs : c1.stk = c.stk ∧ c1.k.sp = c.k.sp) (hB : Built W X c0 prems params c1 st1 P c' r)
    (himp : ∀ st' i, P st' i → P' st' i) :
    HRet W sb X c0 prems params c st P' r s := ⟨c', h, hB.trans hext hs himp⟩

/-- Returning an existing id without building anything. -/
theorem HRet.id (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) {i : Nat}
    (hi : st.lv i) (hP : P st i) :
    HRet W sb X c0 prems params c st P (BitVec.ofNat 32 (st.id i)) s :=
  ⟨c, h, Built.id hR hi hP⟩

end built

/-! ## Statement rules for helper bodies -/

section stmts
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {P : St → Nat → Prop}

/-- `if (cond) { return NOID; } rest` inside a helper. -/
theorem WP.h_guard {cond : Expr} {rest : Stmt} {nm : String} {c' : CMem}
    [RetsTo Q (HRet W sb X c0 prems params c st P)] (h : Holds W s.mem sb c')
    (H : match evalE Vbcf.prog env s.mem cond with
      | some (.u32 v) => v = 0 → WP Vbcf.prog rest Q env s
      | _ => False) :
    WP Vbcf.prog (.seq (.ite cond (.ret (some (.named nm 4294967295#32))) .skip) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun _ => ?_, fun he => ?_⟩
    · apply WP.ret
      simp only [evalE]
      exact RetsTo.ret (Q := Q) _ _ _ (HRet.fail h)
    · apply WP.skip
      exact H he
  · exact H.elim

/-- `return NOID;` inside a helper. -/
theorem WP.h_fail {nm : String} {c' : CMem} [RetsTo Q (HRet W sb X c0 prems params c st P)]
    (h : Holds W s.mem sb c') :
    WP Vbcf.prog (.ret (some (.named nm 4294967295#32))) Q env s := by
  apply WP.ret
  simp only [evalE]
  exact RetsTo.ret _ _ _ (HRet.fail h)

/-- `if (cond) { a } rest` where `a` is a branch ending in `return`, and `b` likewise:
both branches are proved with the postcondition "falling off the end runs `rest`". -/
theorem WP.ite_seq2 {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {c : Expr} {a b rest : Stmt}
    (H : match evalE P env s.mem c with
      | some (.u32 v) =>
        (v ≠ 0 → WP P a (LoopQ (fun env' s' => WP P rest Q env' s') Q) env s) ∧
        (v = 0 → WP P b (LoopQ (fun env' s' => WP P rest Q env' s') Q) env s)
      | _ => False) :
    WP P (.seq (.ite c a b) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun hne => WP.mono (H.1 hne) ?_, fun he => WP.mono (H.2 he) ?_⟩ <;>
    · intro o env' s' hq
      cases o with
      | normal => exact hq
      | brk => exact hq.elim
      | ret r => exact hq
  · exact H.elim

/-- `if (cond) { return K; } rest` for a literal `K` and any postcondition. -/
theorem WP.guard_lit {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {cond : Expr} {rest : Stmt}
    {k : BitVec 32}
    (H : match evalE P env s.mem cond with
      | some (.u32 v) => (v ≠ 0 → Q (.ret (some (.u32 k))) env s) ∧ (v = 0 → WP P rest Q env s)
      | _ => False) :
    WP P (.seq (.ite cond (.ret (some (.lit32 k))) .skip) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun hne => ?_, fun he => ?_⟩
    · apply WP.ret
      simp only [evalE]
      exact H.1 hne
    · apply WP.skip
      exact H.2 he
  · exact H.elim

/-- `x = f(args); rest` for a node-building helper with a proved `HPost` specification. -/
theorem WP.rule_hcall {f : String} {args : List Expr} {x : Var} {rest : Stmt} {vs : List EmbC.Val}
    {pre : List EmbC.Val → (KernelState prog State) → Prop}
    (hspec : FnSpec (State := State) Vbcf.prog f pre (fun _ _ => HPost W sb X c0 prems params c st P))
    (hargs : evalArgs Vbcf.prog env s.mem args = some vs) (hpre : pre vs s)
    (H : ∀ s' c' r, Holds W s'.mem sb c' → Built W X c0 prems params c st P c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) f args) rest) Q env s := by
  apply WP.call_seq hspec hargs hpre
  rintro rv s' ⟨r, rfl, c', h', hB⟩
  exact H s' c' r h' hB

end stmts

/-! ## Entering a helper -/

/-- The body postcondition `HQ` gives the function postcondition `HPost`. -/
theorem HQ.retPost {W : World} {sb : Nat} {X : Ctx} {c0 c : CMem} {prems params : List Nat}
    {st : VSt} {P : St → Nat → Prop} (o : Outcome) (env : Env) (s' : (KernelState prog State))
    (hq : HQ W sb X c0 prems params c st P o env s') :
    retPost (some .u32) (HPost W sb X c0 prems params c st P) o env s' := by
  unfold HQ at hq
  split at hq
  · rename_i r
    exact ⟨rfl, r, rfl, hq⟩
  · exact hq.elim

end Vbcf.Proof
