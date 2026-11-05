import EmbC.Kernel
import Vbcf.Proof.Mem
import Vbcf.Prog

/-!
# Vbcf proofs: symbolic-execution rules over the abstract memory

Rules for the three kinds of store a Vbcf function performs (a scalar field,
a cell of an owned array, a cell of the proof block), phrased so that the
continuation receives a fresh state together with `Holds` for the updated
`CMem`.  A proof therefore always has exactly one `Holds` hypothesis, for the
current state, and never mentions blocks.

Convention used by the tactics: the current state's hypothesis is named `h`,
and `hs : P.findStruct "ck" = some ckS`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

section
variable {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {W : World} {sb : Nat} {c : CMem}

/-- `p->f = e` for a `u32` field of the checker struct. -/
theorem WP.ck_setField {p e : Expr} {f : String}
    (hs : P.findStruct "ck" = some ckS) {m : Mem} (h : Holds W m sb c) (hm : st.mem = m)
    (H : match evalE P env st.mem p, evalE P env st.mem e with
      | some (.ptr b off), some (.u32 x) =>
        b = sb ∧ off = 0 ∧
        match c.k.setU32 f x with
        | none => False
        | some (_, k') => ∀ st', Holds W st'.mem sb { c with k := k' } → Q .normal env st'
      | _, _ => False) :
    WP P (.setField p f e) Q env st := by
  subst hm
  apply WP.setField
  split at H
  · rename_i b off x hp he
    obtain ⟨rfl, rfl, H⟩ := H
    rw [hp, he]; dsimp only
    refine ⟨rfl, ?_⟩
    split at H
    · exact H.elim
    · rename_i i k' hk
      obtain ⟨hst, hh⟩ := h.setU32 hs hk
      rw [hst]; exact H _ hh
  · exact H.elim

/-- `p[i] = e` where `p` points into the owned array `a`. -/
theorem WP.ck_store {p i e : Expr} (a : Arr) {b : Nat} {m : Mem}
    (h : Holds W m sb c) (hm : st.mem = m) (hp : c.k.ptr a = some (b, 0))
    (H : match evalE P env st.mem p, evalE P env st.mem i, evalE P env st.mem e with
      | some (.ptr b' off), some vi, some (.u32 x) =>
        b' = b ∧
        match vi.toIdx with
        | none => False
        | some kx =>
          off + kx < (c.arr a).size ∧
          ∀ st', Holds W st'.mem sb (c.setArr a ((c.arr a).setIfInBounds (off + kx) (.u32 x))) →
            Q .normal env st'
      | _, _, _ => False) :
    WP P (.store p i e) Q env st := by
  subst hm
  apply WP.store
  split at H
  · rename_i b' off vi x hp' hi he
    obtain ⟨rfl, H⟩ := H
    rw [hp', hi, he]; dsimp only
    split at H
    · exact H.elim
    · rename_i kx hk
      rw [hk]; dsimp only
      obtain ⟨hlt, H⟩ := H
      obtain ⟨hst, hh⟩ := h.storeArr hp hlt x
      rw [hst]; exact H _ hh
  · exact H.elim

/-- `p[i] = e` where `p` points into the proof block. -/
theorem WP.ck_storeProof {p i e : Expr} {m : Mem}
    (h : Holds W m sb c) (hm : st.mem = m)
    (H : match evalE P env st.mem p, evalE P env st.mem i, evalE P env st.mem e with
      | some (.ptr b' off), some vi, some (.u32 x) =>
        b' = W.pb ∧
        match vi.toIdx with
        | none => False
        | some kx =>
          off + kx < c.proof.size ∧
          ∀ st', Holds W st'.mem sb { c with proof := c.proof.setIfInBounds (off + kx) (.u32 x) } →
            Q .normal env st'
      | _, _, _ => False) :
    WP P (.store p i e) Q env st := by
  subst hm
  apply WP.store
  split at H
  · rename_i b' off vi x hp' hi he
    obtain ⟨rfl, H⟩ := H
    rw [hp', hi, he]; dsimp only
    split at H
    · exact H.elim
    · rename_i kx hk
      rw [hk]; dsimp only
      obtain ⟨hlt, H⟩ := H
      obtain ⟨hst, hh⟩ := h.storeProof hlt x
      rw [hst]; exact H _ hh
  · exact H.elim

end

/-! ## Reads -/

section
variable {P : Prog} {W : World} {m : Mem} {sb : Nat} {c : CMem}

theorem Holds.rd_pool (h : Holds W m sb c) {b o : Nat} (hp : c.k.pool = some (b, o)) (i : Nat) :
    m.loadArr b i = rd c.pool i := h.loadArr (a := .pool) hp i
theorem Holds.rd_htab (h : Holds W m sb c) {b o : Nat} (hp : c.k.htab = some (b, o)) (i : Nat) :
    m.loadArr b i = rd c.htab i := h.loadArr (a := .htab) hp i
theorem Holds.rd_facts (h : Holds W m sb c) {b o : Nat} (hp : c.k.facts = some (b, o)) (i : Nat) :
    m.loadArr b i = rd c.facts i := h.loadArr (a := .facts) hp i
theorem Holds.rd_stk (h : Holds W m sb c) {b o : Nat} (hp : c.k.stk = some (b, o)) (i : Nat) :
    m.loadArr b i = rd c.stk i := h.loadArr (a := .stk) hp i
theorem Holds.rd_prem (h : Holds W m sb c) {b o : Nat} (hp : c.k.prem = some (b, o)) (i : Nat) :
    m.loadArr b i = rd c.prem i := h.loadArr (a := .prem) hp i
theorem Holds.rd_lr (h : Holds W m sb c) {b o : Nat} (hp : c.k.lr = some (b, o)) (i : Nat) :
    m.loadArr b i = rd c.lr i := h.loadArr (a := .lr) hp i

end

/-! ## Tactics

`ck_simp [facts]` evaluates expressions in the current state: it knows every
field of the struct (from `h` and `hs`) and takes array-cell facts as
arguments. -/

open Lean in
macro "ck_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let h := mkIdent `h
  let hs := mkIdent `hs
  `(tactic| embc_simp [CK.setU32, CMem.arr, CMem.setArr, CK.ptr,
      HasCK.ld_pool $hs (Holds.ck $h), HasCK.ld_plen $hs (Holds.ck $h),
      HasCK.ld_pcap $hs (Holds.ck $h), HasCK.ld_htab $hs (Holds.ck $h),
      HasCK.ld_hcap $hs (Holds.ck $h), HasCK.ld_hcnt $hs (Holds.ck $h),
      HasCK.ld_facts $hs (Holds.ck $h), HasCK.ld_flen $hs (Holds.ck $h),
      HasCK.ld_fcap $hs (Holds.ck $h), HasCK.ld_nexpr $hs (Holds.ck $h),
      HasCK.ld_stk $hs (Holds.ck $h), HasCK.ld_sp $hs (Holds.ck $h),
      HasCK.ld_scap $hs (Holds.ck $h), HasCK.ld_prem $hs (Holds.ck $h),
      HasCK.ld_par $hs (Holds.ck $h), HasCK.ld_proof $hs (Holds.ck $h),
      HasCK.ld_tt $hs (Holds.ck $h), HasCK.ld_ff $hs (Holds.ck $h),
      HasCK.ld_goal $hs (Holds.ck $h), HasCK.ld_err $hs (Holds.ck $h),
      HasCK.ld_work $hs (Holds.ck $h), HasCK.ld_val $hs (Holds.ck $h),
      HasCK.ld_mem $hs (Holds.ck $h), HasCK.ld_lr $hs (Holds.ck $h),
      HasCK.ld_lo $hs (Holds.ck $h), HasCK.ld_live $hs (Holds.ck $h), $ts,*])

macro "ck_simp" : tactic => `(tactic| ck_simp [])

/-! ## Entering a function -/

/-- `FnSpec.intro` with the parameter binding left as a computation, so that
`simp` produces the initial environment. -/
theorem FnSpec.intro' {P : Prog} {f : String} {fn : Fn}
    {pre : List Val → (KernelState P State) → Prop} {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop}
    (hf : P.findFn f = some fn)
    (h : ∀ vs st, pre vs st →
      match bindParams st.mem fn.params vs with
      | none => False
      | some penv => WP P fn.body (retPost fn.ret (post vs st)) (penv ++ initLocals fn.locals) st) :
    FnSpec (State := State) P f pre post := by
  apply FnSpec.intro hf
  intro vs st hpre
  have := h vs st hpre
  split at this
  · exact this.elim
  · rename_i penv hb
    exact ⟨penv, hb, this⟩

/-! ## 32-bit arithmetic without overflow

Conditional rewrites from `BitVec` operations to operations on `toNat`.  Use
them with `simp (disch := omega)`, which is what `bv_norm` does. -/

theorem bv_add_toNat {a b : BitVec 32} (h : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; omega

theorem bv_sub_toNat {a b : BitVec 32} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]; omega

theorem bv_mul_toNat {a b : BitVec 32} (h : a.toNat * b.toNat < 4294967296) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat_lt {n : Nat} (h : n < 4294967296) : (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat]; omega

theorem bv_eq_toNat {a b : BitVec 32} : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, BitVec.eq_of_toNat_eq⟩

/-- Rewrite `toNat` of sums, differences, products and `ofNat` when `omega`
can show there is no wrap-around; also turns `<`/`≤` on words into `Nat`. -/
macro "bv_norm" : tactic =>
  `(tactic| simp (disch := omega) only [bv_add_toNat, bv_sub_toNat, bv_mul_toNat, toNat_ofNat_lt,
      BitVec.lt_def, BitVec.le_def, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *)

/-- The struct definition is in the program. -/
theorem prog_ck : Vbcf.prog.findStruct "ck" = some ckS := rfl

end Vbcf.Proof
