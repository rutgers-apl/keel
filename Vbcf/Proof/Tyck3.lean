import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Tyck2

/-!
# Vbcf proofs: `ck_tyck`

The symbolic execution of the C function.  Every `return` that can yield 1 is
closed by the matching lemma of `Vbcf/Proof/Tyck2.lean`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- `ck_tyck(st)` under `CandRawT` (`CandRaw` plus: a variable's identity word fits 32 bits). -/
def TyckSpecT : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_tyck"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧ CandRawT posOf c st)
      (fun _ s rv s' => s' = s ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ n, Cand posOf c st n ∧ Typed st n)))

/-- The postcondition of `ck_tyck`, as a named predicate (so that `simp` leaves it alone). -/
def TyckQ (posOf : Nat → Nat) (c : CMem) (st : St) (s : (KernelState prog State)) : Option EmbC.Val → (KernelState prog State) → Prop :=
  fun rv s' => s' = s ∧
    (rv = some (.u32 0#32) ∨ (rv = some (.u32 1#32) ∧ Acc posOf c st))

section
variable {posOf : Nat → Nat} {c : CMem} {st : St} {s : (KernelState prog State)}

theorem tyckQ_zero : TyckQ posOf c st s (some (.u32 0#32)) s := ⟨rfl, Or.inl rfl⟩

theorem tyckQ_one (h : Acc posOf c st) : TyckQ posOf c st s (some (.u32 1#32)) s :=
  ⟨rfl, Or.inr ⟨rfl, h⟩⟩

theorem tyckQ_bw {p : Prop} [Decidable p] (h : p → Acc posOf c st) :
    TyckQ posOf c st s (some (.u32 (bw p))) s := by
  by_cases hp : p
  · rw [bw_pos hp]; exact tyckQ_one (h hp)
  · rw [bw_neg hp]; exact tyckQ_zero

end

theorem or_of_imp2 {a b : Prop} (h : ¬a → b) : a ∨ b := by
  by_cases ha : a
  · exact Or.inl ha
  · exact Or.inr (h ha)

theorem or_of_imp3 {a b d : Prop} (h : ¬a → ¬b → d) : a ∨ b ∨ d :=
  or_of_imp2 fun ha => or_of_imp2 (h ha)

theorem or_of_imp5 {a b d e f : Prop} (h : ¬a → ¬b → ¬d → ¬e → f) : a ∨ b ∨ d ∨ e ∨ f :=
  or_of_imp2 fun ha => or_of_imp2 fun hb => or_of_imp3 (h ha hb)

theorem or_of_imp8 {a b d e f g i j : Prop} (h : ¬a → ¬b → ¬d → ¬e → ¬f → ¬g → ¬i → j) :
    a ∨ b ∨ d ∨ e ∨ f ∨ g ∨ i ∨ j :=
  or_of_imp2 fun ha => or_of_imp2 fun hb => or_of_imp2 fun hd => or_of_imp5 (h ha hb hd)

/-- `if (c) { … }` followed by more, where the block may return. -/
theorem WP.ifThen {P : Prog} {Q : (Post P State)} {env : Env} {st : (KernelState P State)} {c : Expr} {a rest : Stmt}
    (h : match evalE P env st.mem c with
      | some (.u32 v) =>
        (v ≠ 0 → WP P a (fun o env' st' =>
          match o with
          | .normal => WP P rest Q env' st'
          | o => Q o env' st') env st) ∧
        (v = 0 → WP P rest Q env st)
      | _ => False) :
    WP P (.seq (.ite c a .skip) rest) Q env st := by
  apply WP.seq
  apply WP.ite
  split at h
  · rename_i v hv
    rw [hv]; dsimp only
    exact ⟨h.1, fun he => WP.skip (h.2 he)⟩
  · exact h.elim

/-- The local variables of `ck_tyck`. -/
def tyckEnv (sb : Nat) (base hdr code n par lo hi t0 t1 t2 r : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("base", .u32, .u32 base), ("hdr", .u32, .u32 hdr),
   ("code", .u32, .u32 code), ("n", .u32, .u32 n), ("par", .u32, .u32 par), ("lo", .u32, .u32 lo),
   ("hi", .u32, .u32 hi), ("t0", .u32, .u32 t0), ("t1", .u32, .u32 t1), ("t2", .u32, .u32 t2),
   ("r", .u32, .u32 r)]

/-- After `if (n >= k + 1) { tk = ty_of(…); }`: the state is unchanged and `tk` is the
encoded type of argument `k`, if there is one. -/
def TyMid (s0 : (KernelState prog State)) (envf : BitVec 32 → Env) (ts : List Bcf.Ty) (k : Nat) : (Post prog State) :=
  fun o env' s' =>
    match o with
    | .normal => s' = s0 ∧ ∃ t : BitVec 32, env' = envf t ∧ ∀ ty, ts[k]? = some ty → t.toNat = tyW ty
    | _ => False

theorem ck_tyck_aux (W : World) (sb : Nat) (c : CMem) (posOf : Nat → Nat) (st : St) :
    EmbC.FnSpec (State := State) Vbcf.prog "ck_tyck"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ CoreInv posOf c st ∧ CandRawT posOf c st)
      (fun _ s => TyckQ posOf c st s) := by
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckTyck) rfl
  rintro vs s ⟨rfl, h, hinv, hcand⟩
  simp [ckTyck, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hd, hdlt, hcell, hroom, hvar, hval, hargs⟩ := hcand.hdr
  obtain ⟨pb, hpool⟩ := hinv.poolPtr h (by omega)
  have hcap := hinv.poolCap
  simp only [maxPool] at hcap
  -- the header and its fields
  apply WP.seq
  apply WP.assign
  tk_simp
  apply WP.seq
  apply WP.assign
  tk_simp [hpool, h.rd_pool hpool, rd_u32 hcell]
  generalize hH : BitVec.ofNat 32 hd = H
  have hHn : H.toNat = hd := by rw [← hH]; exact bv_toNat_ofNat hdlt
  apply WP.seq
  apply WP.assign
  tk_simp
  generalize hcode : H &&& 255#32 = code
  apply WP.seq
  apply WP.assign
  tk_simp
  generalize hn : H >>> 8 &&& 255#32 = n
  apply WP.seq
  apply WP.assign
  tk_simp
  generalize hpar : H >>> 16 = par
  apply WP.seq
  apply WP.assign
  tk_simp
  generalize hlo : par &&& 255#32 = lo
  apply WP.seq
  apply WP.assign
  tk_simp
  generalize hhi : par >>> 8 = hi
  have X : TCtx posOf c st hd code n par lo hi := by
    have e1 : code.toNat = hd % 256 := by rw [← hcode, bv_and_ff, hHn]
    have e2 : n.toNat = hd / 256 % 256 := by rw [← hn, bv_and_ff, bv_shr_8, hHn]
    have e3 : par.toNat = hd / 65536 := by rw [← hpar, bv_shr_16, hHn]
    have e4 : lo.toNat = hd / 65536 % 256 := by rw [← hlo, bv_and_ff, e3]
    have e5 : hi.toNat = hd / 16777216 := by rw [← hhi, bv_shr_8, e3]; omega
    exact ⟨hinv, hdlt, hcell, hroom, e1, e2, e3, e4, e5⟩
  clear hcode hn hpar hlo hhi
  have hC := X.code; have hN := X.n
  have hi1 : (c.k.plen + 1#32).toNat = c.k.plen.toNat + 1 := by
    rw [bv_add_toNat] <;> simp <;> omega
  have hi2 : (c.k.plen + 2#32).toNat = c.k.plen.toNat + 2 := by
    rw [bv_add_toNat] <;> simp <;> omega
  have hi3 : (c.k.plen + 3#32).toNat = c.k.plen.toNat + 3 := by
    rw [bv_add_toNat] <;> simp <;> omega
  -- BV_VAR
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    refine tyckQ_bw fun ⟨⟨h1, h2⟩, h3⟩ => X.bvVar (hvar ?_ ?_) hc h1 h2 h3
    · bvn at hc; omega
    · bvn at h1; omega
  intro hc1
  -- BOOL_VAR
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    refine tyckQ_bw fun ⟨h1, h2⟩ => X.boolVar (hvar ?_ ?_) hc h1 h2
    · bvn at hc; omega
    · bvn at h1; omega
  intro hc2
  -- BOOL_VAL
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨h1, h2⟩ => X.boolVal hc h1 h2
  intro hc3
  -- BV_VAL
  apply WP.ifThen
  tk_simp
  constructor
  · intro hc
    apply WP.ifRet
    tk_simp
    constructor
    · intro _
      tk_simp [retPost]
      exact tyckQ_zero
    intro h1 h2 h3 h4
    obtain ⟨w0, w1, hw0, c0, c1⟩ := X.valWords hval hc h2 h3 h4
    by_cases hlt : lo < 32#32
    · have hlt' : lo.toNat < 32 := BitVec.lt_def.mp hlt
      apply WP.ifRet
      tk_simp [hlt, hlt', hpool, h.rd_pool hpool, hi1, rd_u32 c0]
      tk_simp [retPost]
      exact tyckQ_bw fun hz => X.bvVal_lo hc h1 h2 h3 h4 w0 w1 hw0 c0 c1 hlt hz
    apply WP.ifRet
    tk_simp [hlt]
    by_cases hmid : 32#32 < lo ∧ lo < 64#32
    · have hgt' : 32 < lo.toNat := BitVec.lt_def.mp hmid.1
      have hlt' : lo.toNat < 64 := BitVec.lt_def.mp hmid.2
      have hsub : (lo - 32#32).toNat = lo.toNat - 32 := by
        rw [bv_sub_toNat] <;> simp <;> omega
      have hsh : lo.toNat - 32 < 32 := by omega
      apply WP.ifRet
      tk_simp [hmid.1, hmid.2, hsub, hsh, hpool, h.rd_pool hpool, hi2, rd_u32 (c1 hgt').2]
      tk_simp [retPost]
      exact tyckQ_bw fun hz => X.bvVal_mid hc h1 h2 h3 h4 w0 w1 hw0 c0 c1 hmid.1 hz
    apply WP.ifRet
    tk_simp [hmid]
    apply WP.ret
    tk_simp [retPost]
    exact tyckQ_one (X.bvVal_full hc h1 h2 h3 h4 w0 w1 hw0 c0 c1 hlt hmid)
  intro hc4
  -- the arguments
  have hnl : ∀ k, k < n.toNat →
      ∃ i, i < st.pool.size ∧ U c.pool (c.k.plen.toNat + 1 + k) (offs st.pool i) := by
    rw [hN]
    bvn at hc1 hc2 hc3 hc4
    exact hargs (by omega) (by omega) (by omega) (by omega)
  obtain ⟨is, hislen, hisargs⟩ := args_exist n.toNat hnl
  have hislt : ∀ i ∈ is, i < st.pool.size := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
    exact (hisargs k _ (by simp)).1
  obtain ⟨ts, hts, hfit⟩ := tys_exist hinv hislt
  have htslen : ts.length = n.toNat := by rw [mapOpt_length hts, hislen]
  -- t0
  apply WP.seq
  refine WP.mono (Q := TyMid s (fun t => tyckEnv sb c.k.plen H code n par lo hi t 0#32 0#32 0#32)
    ts 0) ?_ ?_
  · apply WP.ite
    tk_simp
    constructor
    · intro hn1
      have hk : 0 < is.length := by
        rw [hislen]; bvn at hn1; omega
      obtain ⟨hai, hcl⟩ := hisargs 0 is[0] (by simp)
      obtain ⟨hw, ty, hhdr, hty, hfit0, htyof⟩ := hinv.argTy hai
      have hoff := hinv.off_lt hai
      have htk : ts[0]? = some ty := by
        rw [← hty]; exact (mapOpt_getElem? hts hk).symm
      apply WP.call (ty_of_spec (BitVec.ofNat 32 hw))
      tk_simp [hpool, h.rd_pool hpool, hi1, rd_u32 hcl,
        bv_toNat_ofNat (show offs st.pool is[0] < 2 ^ 32 by omega), rd_u32 hhdr, htyof]
      refine ⟨rfl, _, rfl, fun ty' hty' => ?_⟩
      rw [htk] at hty'
      cases hty'
      exact bv_toNat_ofNat (tyW_lt_two_pow hfit0)
    · intro hn0
      apply WP.skip
      refine ⟨rfl, 0#32, rfl, fun ty' hty' => ?_⟩
      have hlt := lt_length_of_getElem? hty'
      rw [htslen] at hlt
      bvn at hn0
      omega
  rintro o env' s1 hq
  cases o with
  | brk => exact hq.elim
  | ret r => exact hq.elim
  | normal =>
  obtain ⟨hs1, t0, rfl, ht0⟩ := hq
  subst s1
  simp only [tyckEnv]
  -- t1
  apply WP.seq
  refine WP.mono (Q := TyMid s (fun t => tyckEnv sb c.k.plen H code n par lo hi t0 t 0#32 0#32)
    ts 1) ?_ ?_
  · apply WP.ite
    tk_simp
    constructor
    · intro hn1
      have hk : 1 < is.length := by
        rw [hislen]; bvn at hn1; omega
      obtain ⟨hai, hcl⟩ := hisargs 1 is[1] (by simp)
      obtain ⟨hw, ty, hhdr, hty, hfit0, htyof⟩ := hinv.argTy hai
      have hoff := hinv.off_lt hai
      have htk : ts[1]? = some ty := by
        rw [← hty]; exact (mapOpt_getElem? hts hk).symm
      apply WP.call (ty_of_spec (BitVec.ofNat 32 hw))
      tk_simp [hpool, h.rd_pool hpool, hi2, rd_u32 hcl,
        bv_toNat_ofNat (show offs st.pool is[1] < 2 ^ 32 by omega), rd_u32 hhdr, htyof]
      refine ⟨rfl, _, rfl, fun ty' hty' => ?_⟩
      rw [htk] at hty'
      cases hty'
      exact bv_toNat_ofNat (tyW_lt_two_pow hfit0)
    · intro hn0
      apply WP.skip
      refine ⟨rfl, 0#32, rfl, fun ty' hty' => ?_⟩
      have hlt := lt_length_of_getElem? hty'
      rw [htslen] at hlt
      bvn at hn0
      omega
  rintro o env' s1 hq
  cases o with
  | brk => exact hq.elim
  | ret r => exact hq.elim
  | normal =>
  obtain ⟨hs1, t1, rfl, ht1⟩ := hq
  subst s1
  simp only [tyckEnv]
  -- t2
  apply WP.seq
  refine WP.mono (Q := TyMid s (fun t => tyckEnv sb c.k.plen H code n par lo hi t0 t1 t 0#32)
    ts 2) ?_ ?_
  · apply WP.ite
    tk_simp
    constructor
    · intro hn1
      have hk : 2 < is.length := by
        rw [hislen]; bvn at hn1; omega
      obtain ⟨hai, hcl⟩ := hisargs 2 is[2] (by simp)
      obtain ⟨hw, ty, hhdr, hty, hfit0, htyof⟩ := hinv.argTy hai
      have hoff := hinv.off_lt hai
      have htk : ts[2]? = some ty := by
        rw [← hty]; exact (mapOpt_getElem? hts hk).symm
      apply WP.call (ty_of_spec (BitVec.ofNat 32 hw))
      tk_simp [hpool, h.rd_pool hpool, hi3, rd_u32 hcl,
        bv_toNat_ofNat (show offs st.pool is[2] < 2 ^ 32 by omega), rd_u32 hhdr, htyof]
      refine ⟨rfl, _, rfl, fun ty' hty' => ?_⟩
      rw [htk] at hty'
      cases hty'
      exact bv_toNat_ofNat (tyW_lt_two_pow hfit0)
    · intro hn0
      apply WP.skip
      refine ⟨rfl, 0#32, rfl, fun ty' hty' => ?_⟩
      have hlt := lt_length_of_getElem? hty'
      rw [htslen] at hlt
      bvn at hn0
      omega
  rintro o env' s1 hq
  cases o with
  | brk => exact hq.elim
  | ret r => exact hq.elim
  | normal =>
  obtain ⟨hs1, t2, rfl, ht2⟩ := hq
  subst s1
  simp only [tyckEnv]
  have A : ACtx c st n is ts t0 t1 t2 := ⟨hislen, hisargs, hts, hfit, ht0, ht1, ht2⟩
  have hbnd : c.k.plen.toNat + 1 + n.toNat ≤ 4294967296 := by omega
  clear ht0 ht1 ht2 hnl hargs hval hvar hi1 hi2 hi3
  -- BV_NEG, BV_NOT
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.bvUn A (or_of_imp2 hc) h1 h2 h3 h4
  intro _ _
  -- BV_EXTRACT
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.bvExtract A hc h1 h2 h3 h4
  intro _
  -- BV_SEXT, BV_ZEXT
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.bvExt A (or_of_imp2 hc) h1 h2 h3 h4
  intro _ _
  -- BV_SIZE
  apply WP.ifThen
  tk_simp
  constructor
  · intro hc
    apply WP.ifRet
    tk_simp
    constructor
    · intro _
      tk_simp [retPost]
      exact tyckQ_zero
    intro h1 h2 h3 h4
    by_cases h9 : 9#32 ≤ lo
    · apply WP.ifRet
      tk_simp [h9, retPost]
      exact tyckQ_one (X.bvSize A hc h1 h2 h3 h4 (Or.inl h9))
    · have h9' : lo < 9#32 := by bvn at h9 ⊢; omega
      have hsh : lo.toNat < 32 := by bvn at h9'; omega
      apply WP.ifRet
      tk_simp [h9, h9']
      apply WP.ret
      tk_simp [retPost, hsh]
      exact tyckQ_bw fun h6 => X.bvSize A hc h1 h2 h3 h4 (Or.inr ⟨h9', h6⟩)
  intro _
  -- BV_REPEAT
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.bvRepeat A hc h1 h2 h3 h4
  intro _
  -- BV_SUB, shifts, divisions
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3, h4⟩, h5⟩ => X.bvBin A (or_of_imp8 hc) h1 h2 h3 h4 h5
  intro _ _ _ _ _ _ _ _
  -- BV_ITE
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ => X.bvIte A hc h1 h2 h3 (or_of_imp2 h4) h5 h6
  intro _
  -- BV_ADD, ...
  apply WP.ifThen
  tk_simp
  constructor
  · intro hc
    apply WP.ifRet
    tk_simp
    constructor
    · intro _
      tk_simp [retPost]
      exact tyckQ_zero
    intro h1 h2 h3
    apply WP.seq
    apply WP.call (ck_all_ty_spec W sb c posOf st c.k.plen n lo is ts)
    tk_simp
    refine ⟨⟨h, hinv, hislen, hbnd, hisargs, hts⟩, ?_⟩
    apply WP.ret
    tk_simp [retPost]
    exact tyckQ_bw fun h4 => X.bvN A (or_of_imp5 hc) h1 h2 h3 h4
  intro _ _ _ _ _
  -- BV_CONCAT
  apply WP.ifThen
  tk_simp
  constructor
  · intro hc
    apply WP.ifRet
    tk_simp
    constructor
    · intro _
      tk_simp [retPost]
      exact tyckQ_zero
    intro h1 h2 h3
    apply WP.seq
    apply WP.call (ck_sum_bv_spec W sb c posOf st c.k.plen n is ts)
    tk_simp
    refine ⟨⟨h, hinv, hislen, hbnd, hisargs, hts⟩, ?_⟩
    apply WP.ret
    tk_simp [retPost]
    exact tyckQ_bw fun h4 => X.bvConcat A hc h1 h2 h3 h4
  intro _
  -- BV_FROM_BOOL
  apply WP.ifThen
  tk_simp
  constructor
  · intro hc
    apply WP.ifRet
    tk_simp
    constructor
    · intro _
      tk_simp [retPost]
      exact tyckQ_zero
    intro h1 h2
    apply WP.seq
    apply WP.call (ck_all_ty_spec W sb c posOf st c.k.plen n 4096#32 is ts)
    tk_simp
    refine ⟨⟨h, hinv, hislen, hbnd, hisargs, hts⟩, ?_⟩
    apply WP.ret
    tk_simp [retPost]
    exact tyckQ_bw fun h4 => X.bvFromBool A hc h1 h2 h4
  intro _
  -- BOOL_NOT
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2⟩, h3⟩ => X.boolNot A hc h1 h2 h3
  intro _
  -- BOOL_BITOF
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.boolBitof A hc h1 h2 h3 h4
  intro _
  -- BOOL_EQ, BOOL_DISTINCT
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.boolEq A (or_of_imp2 hc) h1 h2 h3 h4
  intro _ _
  -- comparisons
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.boolCmp A (or_of_imp8 hc) h1 h2 h3 h4
  intro _ _ _ _ _ _ _ _
  -- BOOL_IMPLIES
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3⟩, h4⟩ => X.boolImplies A hc h1 h2 h3 h4
  intro _
  -- BOOL_ITE
  apply WP.ifRet
  tk_simp
  constructor
  · intro hc
    tk_simp [retPost]
    exact tyckQ_bw fun ⟨⟨h1, h2, h3, h4⟩, h5⟩ => X.boolIte A hc h1 h2 h3 h4 h5
  intro _
  -- BOOL_CONJ, ...
  apply WP.ifThen
  tk_simp
  constructor
  · intro hc
    apply WP.ifRet
    tk_simp
    constructor
    · intro _
      tk_simp [retPost]
      exact tyckQ_zero
    intro h1 h2
    apply WP.seq
    apply WP.call (ck_all_ty_spec W sb c posOf st c.k.plen n 4096#32 is ts)
    tk_simp
    refine ⟨⟨h, hinv, hislen, hbnd, hisargs, hts⟩, ?_⟩
    apply WP.ret
    tk_simp [retPost]
    exact tyckQ_bw fun h4 => X.boolN A (or_of_imp3 hc) h1 h2 h4
  intro _ _ _
  -- LIST_VAL
  apply WP.ifThen
  tk_simp
  constructor
  · intro hc
    apply WP.ifRet
    tk_simp
    constructor
    · intro _
      tk_simp [retPost]
      exact tyckQ_zero
    intro h1 h2
    by_cases hl1 : lo = 1#32
    · apply WP.ifThen
      tk_simp [hl1]
      apply WP.seq
      apply WP.call (ck_all_ty_spec W sb c posOf st c.k.plen n 4096#32 is ts)
      tk_simp
      refine ⟨⟨h, hinv, hislen, hbnd, hisargs, hts⟩, ?_⟩
      apply WP.ret
      tk_simp [retPost]
      exact tyckQ_bw fun h4 => X.listBool A hc h1 hl1 h4
    · apply WP.ifThen
      tk_simp [hl1]
      apply WP.seq
      apply WP.call (ck_sum_bv_spec W sb c posOf st c.k.plen n is ts)
      tk_simp
      refine ⟨⟨h, hinv, hislen, hbnd, hisargs, hts⟩, ?_⟩
      apply WP.ret
      tk_simp [retPost]
      exact tyckQ_bw fun h4 => X.listBv A hc h1 h2 hl1 h4
  intro _
  apply WP.ret
  tk_simp [retPost]
  exact tyckQ_zero

/-- `ck_tyck` accepts only candidates that are the encoding of a well-typed node. -/
theorem ck_tyck_spec : TyckSpecT (State := State) :=
  fun W sb c posOf st => ck_tyck_aux W sb c posOf st

end Vbcf.Proof
