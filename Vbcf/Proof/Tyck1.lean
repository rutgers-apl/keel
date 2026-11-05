import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Access

/-!
# Vbcf proofs: `ty_of`, `ck_all_ty`, `ck_sum_bv`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## Truth values as C integers

The C semantics turns a comparison into `Val.ofBool (decide p)` and `&&`/`||` into nested
`if`s over such values.  `tk_simp` keeps them in the normal form `Val.u32 (bw p)`, with
`p` a proposition built with `∧`, `∨`, `¬`. -/

/-- A proposition as a C truth value. -/
def bw (p : Prop) [Decidable p] : BitVec 32 := if p then 1#32 else 0#32

theorem ofBool_eq (b : Bool) : Val.ofBool b = .u32 (bw (b = true)) := by
  cases b <;> rfl

@[simp] theorem bw_eq_zero {p : Prop} [Decidable p] : bw p = 0#32 ↔ ¬p := by
  unfold bw; split <;> simp_all

@[simp] theorem bw_eq_one {p : Prop} [Decidable p] : bw p = 1#32 ↔ p := by
  unfold bw; split <;> simp_all

theorem bw_cases (p : Prop) [Decidable p] : bw p = 0#32 ∨ bw p = 1#32 := by
  unfold bw; split <;> simp

theorem bw_pos {p : Prop} [Decidable p] (h : p) : bw p = 1#32 := bw_eq_one.mpr h
theorem bw_neg {p : Prop} [Decidable p] (h : ¬p) : bw p = 0#32 := bw_eq_zero.mpr h

/-- `a && b` after both sides are evaluated. -/
theorem land_some {p q : Prop} [Decidable p] [Decidable q] :
    (if p then some (Val.u32 (bw q)) else some (Val.u32 0#32)) = some (Val.u32 (bw (p ∧ q))) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bw, hp, hq]

theorem land_some' {p q : Prop} [Decidable p] [Decidable q] :
    (if p then some (Val.u32 0#32) else some (Val.u32 (bw q))) = some (Val.u32 (bw (¬p ∧ q))) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bw, hp, hq]

/-- `a || b` after both sides are evaluated. -/
theorem lor_some {p q : Prop} [Decidable p] [Decidable q] :
    (if p then some (Val.u32 1#32) else some (Val.u32 (bw q))) = some (Val.u32 (bw (p ∨ q))) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bw, hp, hq]

theorem lor_some' {p q : Prop} [Decidable p] [Decidable q] :
    (if p then some (Val.u32 (bw q)) else some (Val.u32 1#32)) = some (Val.u32 (bw (¬p ∨ q))) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bw, hp, hq]

/-- `ck_simp` with truth values kept as `bw p` (see above). -/
macro "tk_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let h := Lean.mkIdent `h
  let hs := Lean.mkIdent `hs
  `(tactic| simp [evalE, evalBin, evalArith, evalCast, evalArgs, EmbC.ptrEq,
      Env.get, Env.ty, Env.set, Env.assign, Val.toIdx, ofBool_eq, land_some, land_some', lor_some,
      lor_some', CK.ptr, CMem.arr,
      HasCK.ld_pool $hs (Holds.ck $h), HasCK.ld_plen $hs (Holds.ck $h),
      HasCK.ld_pcap $hs (Holds.ck $h), $ts,*])

macro "tk_simp" : tactic => `(tactic| tk_simp [])

/-! ## `if (c) { return e; }` followed by more -/

theorem WP.ifRet {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {c e : Expr} {rest : Stmt}
    (h : match evalE P env st.mem c with
      | some (.u32 v) =>
        (v ≠ 0 → match evalE P env st.mem e with
          | none => False
          | some r => Q (.ret (some r)) env st) ∧
        (v = 0 → WP P rest Q env st)
      | _ => False) :
    WP P (.seq (.ite c (.ret (some e)) .skip) rest) Q env st := by
  apply WP.seq
  apply WP.ite
  split at h
  · rename_i v hv
    rw [hv]; dsimp only
    refine ⟨fun hne => ?_, fun he => ?_⟩
    · apply WP.ret
      have := h.1 hne
      split at this
      · exact this.elim
      · rename_i r hr
        rw [hr]; exact this
    · apply WP.skip
      exact h.2 he
  · exact h.elim

/-! ## `ty_of` -/

theorem ty_of_spec : TyOfSpec (State := State) tyOfB := by
  intro hd
  apply FnSpec.intro' (fn := tyOf) rfl
  rintro vs st rfl
  simp [tyOf, bindParams]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.assign
  embc_simp
  apply WP.ifRet
  embc_simp
  constructor
  · intro h1
    embc_simp [retPost, tyOfB, h1]
  intro h1
  apply WP.ifRet
  embc_simp
  constructor
  · intro h2
    embc_simp [retPost, tyOfB, h1, h2]
  intro h2
  apply WP.ifRet
  embc_simp
  constructor
  · intro h3
    embc_simp [retPost, tyOfB, h1, h2, h3]
  intro h3
  apply WP.ifRet
  embc_simp
  constructor
  · intro h4
    embc_simp [retPost, tyOfB, h1, h2, h3, h4]
  intro h4
  apply WP.ret
  embc_simp [retPost, tyOfB, h1, h2, h3, h4]

/-! ## Reading the type of an argument -/

section
variable {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : St}

/-- If the pool has a node, the C pool is allocated. -/
theorem CoreInv.poolPtr {m : Mem} (hc : CoreInv posOf c st) (h : Holds W m sb c)
    (hne : 0 < c.k.pcap.toNat) : ∃ b, c.k.pool = some (b, 0) := by
  cases hp : c.k.pool with
  | none => have := hc.poolNull hp; rw [this] at hne; simp at hne
  | some bo =>
    obtain ⟨b, o⟩ := bo
    obtain ⟨rfl, -⟩ := h.arr .pool b o hp
    exact ⟨b, rfl⟩

theorem CoreInv.poolPtr_of_node {m : Mem} (hc : CoreInv posOf c st) (h : Holds W m sb c)
    {i : Nat} (hi : i < st.pool.size) : ∃ b, c.k.pool = some (b, 0) := by
  apply hc.poolPtr h
  have h1 := hc.rep.offs_lt hi
  have h2 := hc.poolCap.1
  omega

/-- The header of node `i`, and what `ty_of` makes of it: the encoding of the type the
Lean checker has memoised for `i`. -/
theorem CoreInv.argTy (hc : CoreInv posOf c st) {i : Nat} (hi : i < st.pool.size) :
    ∃ hw ty, U c.pool (offs st.pool i) hw ∧ st.tys[i]? = some ty ∧ TyFits ty ∧
      tyOfB (BitVec.ofNat 32 hw) = BitVec.ofNat 32 (tyW ty) := by
  obtain ⟨n, hn⟩ := node_of_lt hi
  have hf := hc.rep.fits i n hn
  obtain ⟨ty, hty, he, hfit⟩ := hc.ok.tyOfM_hdrW hn hf
  refine ⟨hdrW n, ty, hc.rep.hdr hn, hty, hfit, ?_⟩
  rw [tyOfB_eq, bv_toNat_ofNat (hdrW_lt hf), he]

/-- The words after the header at `base` are the ids of the nodes `is`. -/
def ArgsAt (c : CMem) (st : St) (base : Nat) (is : List Nat) : Prop :=
  ∀ (k i : Nat), is[k]? = some i → i < st.pool.size ∧ U c.pool (base + 1 + k) (offs st.pool i)

end

/-! ## `ck_all_ty` -/

/-- `ck_all_ty(st, base, n, t)`: the `n` words after `base` are the ids of the nodes `is`,
whose types are `ts`; returns 1 iff every one of these types encodes to `t`.  Reads only. -/
def AllTySpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (base n t : BitVec 32)
    (is : List Nat) (ts : List Bcf.Ty),
    FnSpec (State := State) Vbcf.prog "ck_all_ty"
      (fun vs s => vs = [.ptr sb 0, .u32 base, .u32 n, .u32 t] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ is.length = n.toNat ∧ base.toNat + 1 + n.toNat ≤ 2 ^ 32 ∧
        ArgsAt c st base.toNat is ∧ mapOpt (fun a => st.tys[a]?) is = some ts)
      (fun _ s rv s' => s' = s ∧
        rv = some (.u32 (bw (∀ ty ∈ ts, tyW ty = t.toNat))))

/-- The loop invariant of `ck_all_ty`. -/
def AllTyInv (sb : Nat) (base n t : BitVec 32) (ts : List Bcf.Ty) (s0 : (KernelState prog State)) : Env → (KernelState prog State) → Prop :=
  fun env s => s = s0 ∧ ∃ i ta : BitVec 32,
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("n", .u32, .u32 n),
      ("t", .u32, .u32 t), ("i", .u32, .u32 i), ("ta", .u32, .u32 ta)] ∧
    i.toNat ≤ n.toNat ∧ ∀ k ty, k < i.toNat → ts[k]? = some ty → tyW ty = t.toNat

theorem ck_all_ty_spec : AllTySpec (State := State) := by
  intro W sb c posOf st base n t is ts
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckAllTy) rfl
  rintro vs s ⟨rfl, h, hinv, hlen, hbnd, hargs, hts⟩
  simp [ckAllTy, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.while (I := AllTyInv sb base n t ts s)
  · exact ⟨rfl, 0#32, 0#32, rfl, by simp, fun k ty hk => by simp at hk⟩
  · rintro env s' ⟨rfl, i, ta, rfl, hile, hpre⟩
    tk_simp
    constructor
    · intro hge
      apply WP.ret
      tk_simp [retPost]
      symm; apply bw_pos
      intro ty hty
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hty
      have hk' : k < i.toNat := by
        have := mapOpt_length hts
        have := BitVec.le_def.mp hge
        omega
      exact hpre k _ hk' (by simp)
    · intro hlt
      have hlt' : i.toNat < n.toNat := BitVec.lt_def.mp hlt
      have hk : i.toNat < is.length := by omega
      obtain ⟨hai, hcell⟩ := hargs i.toNat is[i.toNat] (by simp)
      obtain ⟨hw, ty, hhdr, hty, hfit, htyof⟩ := hinv.argTy hai
      obtain ⟨pb, hpool⟩ := hinv.poolPtr_of_node h hai
      have hoff := hinv.off_lt hai
      have hidx : (base + 1#32 + i).toNat = base.toNat + 1 + i.toNat := by
        rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
      have htk : ts[i.toNat]? = some ty := by
        rw [← hty]; exact (mapOpt_getElem? hts hk).symm
      apply WP.seq
      apply WP.call (ty_of_spec (BitVec.ofNat 32 hw))
      tk_simp [hpool, h.rd_pool hpool, hidx, rd_u32 hcell,
        bv_toNat_ofNat (show offs st.pool is[i.toNat] < 2 ^ 32 by omega), rd_u32 hhdr, htyof]
      have hbv : BitVec.ofNat 32 (tyW ty) = t ↔ tyW ty = t.toNat := ofNat_eq_iff (tyW_lt_two_pow hfit)
      apply WP.ifRet
      tk_simp [hbv]
      constructor
      · intro hne
        tk_simp [retPost]
        symm; apply bw_neg
        intro hall
        exact hne (hall ty (List.mem_of_getElem? htk))
      · intro heq
        apply WP.assign
        tk_simp
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
          rw [bv_add_toNat] <;> simp <;> omega
        refine ⟨rfl, _, _, rfl, by omega, ?_⟩
        intro k ty' hk' hty'
        rw [hi1] at hk'
        rcases Nat.lt_or_ge k i.toNat with hlt2 | hge2
        · exact hpre k ty' hlt2 hty'
        · have : k = i.toNat := by omega
          subst this
          rw [htk] at hty'
          cases hty'
          exact heq

/-! ## `ck_sum_bv` -/

theorem tyW_lt_bool_iff_inClass {ty : Bcf.Ty} (h : TyFits ty) :
    tyW ty < 0x1000 ↔ Ty.inClass false ty = true := by
  rw [tyW_lt_bool_iff h]
  cases ty <;> simp [Ty.inClass]

/-- The result of `ck_sum_bv` on arguments of types `ts`. -/
def sumBvM (ts : List Bcf.Ty) : BitVec 32 :=
  if ts.all (Ty.inClass false) = true then BitVec.ofNat 32 (ts.map tyW).sum else noid

/-- `ck_sum_bv(st, base, n)`: the `n` words after `base` are the ids of the nodes `is`,
whose types are `ts`; returns the sum of the widths (in 32-bit arithmetic) if every one of
these types is a bit-vector type, else `NOID`.  Reads only. -/
def SumBvSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) (base n : BitVec 32)
    (is : List Nat) (ts : List Bcf.Ty),
    FnSpec (State := State) Vbcf.prog "ck_sum_bv"
      (fun vs s => vs = [.ptr sb 0, .u32 base, .u32 n] ∧ Holds W s.mem sb c ∧
        CoreInv posOf c st ∧ is.length = n.toNat ∧ base.toNat + 1 + n.toNat ≤ 2 ^ 32 ∧
        ArgsAt c st base.toNat is ∧ mapOpt (fun a => st.tys[a]?) is = some ts)
      (fun _ s rv s' => s' = s ∧
        rv = some (.u32 (sumBvM ts)))

/-- The loop invariant of `ck_sum_bv`. -/
def SumBvInv (sb : Nat) (base n : BitVec 32) (ts : List Bcf.Ty) (s0 : (KernelState prog State)) : Env → (KernelState prog State) → Prop :=
  fun env s => s = s0 ∧ ∃ i t sum : BitVec 32,
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("n", .u32, .u32 n),
      ("i", .u32, .u32 i), ("t", .u32, .u32 t), ("sum", .u32, .u32 sum)] ∧
    i.toNat ≤ n.toNat ∧ (∀ k ty, k < i.toNat → ts[k]? = some ty → Ty.inClass false ty = true) ∧
    sum = BitVec.ofNat 32 ((ts.take i.toNat).map tyW).sum

theorem ck_sum_bv_spec : SumBvSpec (State := State) := by
  intro W sb c posOf st base n is ts
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckSumBv) rfl
  rintro vs s ⟨rfl, h, hinv, hlen, hbnd, hargs, hts⟩
  simp [ckSumBv, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hlts := mapOpt_length hts
  apply WP.seq
  apply WP.while (I := SumBvInv sb base n ts s)
  · exact ⟨rfl, 0#32, 0#32, 0#32, rfl, by simp, fun k ty hk => by simp at hk, by simp⟩
  · rintro env s' ⟨rfl, i, t, sum, rfl, hile, hpre, hsum⟩
    tk_simp
    constructor
    · intro hge
      apply WP.ret
      tk_simp [retPost]
      have hi : i.toNat = ts.length := by
        have := BitVec.le_def.mp hge
        omega
      have hall : ts.all (Ty.inClass false) = true := by
        rw [List.all_eq_true]
        intro ty hty
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hty
        exact hpre k _ (by omega) (by simp)
      simp only [sumBvM, hall, ↓reduceIte]
      rw [hsum, hi, List.take_length]
    · intro hlt
      have hlt' : i.toNat < n.toNat := BitVec.lt_def.mp hlt
      have hk : i.toNat < is.length := by omega
      obtain ⟨hai, hcell⟩ := hargs i.toNat is[i.toNat] (by simp)
      obtain ⟨hw, ty, hhdr, hty, hfit, htyof⟩ := hinv.argTy hai
      obtain ⟨pb, hpool⟩ := hinv.poolPtr_of_node h hai
      have hoff := hinv.off_lt hai
      have hidx : (base + 1#32 + i).toNat = base.toNat + 1 + i.toNat := by
        rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
      have htk : ts[i.toNat]? = some ty := by
        rw [← hty]; exact (mapOpt_getElem? hts hk).symm
      apply WP.seq
      apply WP.call (ty_of_spec (BitVec.ofNat 32 hw))
      tk_simp [hpool, h.rd_pool hpool, hidx, rd_u32 hcell,
        bv_toNat_ofNat (show offs st.pool is[i.toNat] < 2 ^ 32 by omega), rd_u32 hhdr, htyof]
      have hbv : 4096#32 ≤ BitVec.ofNat 32 (tyW ty) ↔ ¬ Ty.inClass false ty = true := by
        rw [← tyW_lt_bool_iff_inClass hfit, BitVec.le_def, bv_toNat_ofNat (tyW_lt_two_pow hfit)]
        simp
      apply WP.ifRet
      tk_simp [hbv]
      constructor
      · intro hne
        tk_simp [retPost]
        have hna : ¬ ts.all (Ty.inClass false) = true := by
          rw [List.all_eq_true]
          intro hall
          have := hall ty (List.mem_of_getElem? htk)
          rw [hne] at this; cases this
        simp only [sumBvM, hna]
        rfl
      · intro heq
        apply WP.seq
        apply WP.assign
        tk_simp
        apply WP.assign
        tk_simp
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
          rw [bv_add_toNat] <;> simp <;> omega
        refine ⟨rfl, _, _, _, rfl, by omega, ?_, ?_⟩
        · intro k ty' hk' hty'
          rw [hi1] at hk'
          rcases Nat.lt_or_ge k i.toNat with hlt2 | hge2
          · exact hpre k ty' hlt2 hty'
          · have : k = i.toNat := by omega
            subst this
            rw [htk] at hty'
            cases hty'
            exact heq
        · rw [hi1, hsum, List.take_add_one, htk]
          simp [BitVec.ofNat_add]

end Vbcf.Proof
