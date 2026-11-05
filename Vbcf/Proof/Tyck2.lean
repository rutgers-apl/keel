import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Tyck1

/-!
# Vbcf proofs: `ck_tyck`, the pure part

For each `return` of `ck_tyck` that can yield 1: if the C's test holds, then
the candidate words are the encoding of a typed Lean node.  No program
semantics here; `Vbcf/Proof/Tyck3.lean` runs the C and uses these lemmas.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-- The candidate at the tail of the pool is the encoding of a well-typed node. -/
def Acc (posOf : Nat → Nat) (c : CMem) (st : St) : Prop :=
  ∃ n, Cand posOf c st n ∧ Typed st n

/-- Historical name: `CandRaw` now carries the identity-word bound. -/
abbrev CandRawT (posOf : Nat → Nat) (c : CMem) (st : St) : Prop := CandRaw posOf c st

theorem CandRawT.toRaw {posOf : Nat → Nat} {c : CMem} {st : St} (h : CandRawT posOf c st) :
    CandRaw posOf c st := h

theorem CandRaw.toT_nonvar {posOf : Nat → Nat} {c : CMem} {st : St} (h : CandRaw posOf c st)
    (_hnv : ∀ hd, hd < 2 ^ 32 → U c.pool c.k.plen.toNat hd → hd % 256 ≠ 0x18 ∧ hd % 256 ≠ 0x19) :
    CandRawT posOf c st := h

theorem CandRaw.toT_of_fits {posOf : Nat → Nat} {c : CMem} {st : St} (h : CandRaw posOf c st)
    (_hfit : ∀ id, U c.pool (c.k.plen.toNat + 1) (posOf id) → posOf id < 2 ^ 32) :
    CandRawT posOf c st := h

/-- The header word `hd` of the candidate and the fields `ck_tyck` extracts from it. -/
structure TCtx (posOf : Nat → Nat) (c : CMem) (st : St) (hd : Nat)
    (code n par lo hi : BitVec 32) : Prop where
  inv : CoreInv posOf c st
  lt : hd < 2 ^ 32
  cell : U c.pool c.k.plen.toNat hd
  room : c.k.plen.toNat + 1 + hd / 256 % 256 ≤ c.k.pcap.toNat
  code : code.toNat = hd % 256
  n : n.toNat = hd / 256 % 256
  par : par.toNat = hd / 65536
  lo : lo.toNat = hd / 65536 % 256
  hi : hi.toNat = hd / 16777216

/-- The arguments of a non-leaf candidate: their indices `is`, their types `ts`, and the
encoded types `t0`, `t1`, `t2` of the first three as `ck_tyck` reads them. -/
structure ACtx (c : CMem) (st : St) (n : BitVec 32) (is : List Nat) (ts : List Bcf.Ty)
    (t0 t1 t2 : BitVec 32) : Prop where
  len : is.length = n.toNat
  args : ArgsAt c st c.k.plen.toNat is
  tys : mapOpt (fun a => st.tys[a]?) is = some ts
  fit : ∀ ty ∈ ts, TyFits ty
  t0 : ∀ ty, ts[0]? = some ty → t0.toNat = tyW ty
  t1 : ∀ ty, ts[1]? = some ty → t1.toNat = tyW ty
  t2 : ∀ ty, ts[2]? = some ty → t2.toNat = tyW ty

section
variable {posOf : Nat → Nat} {c : CMem} {st : St} {hd : Nat} {code n par lo hi : BitVec 32}

/-- A node whose header fields and tail words are the candidate's is accepted. -/
theorem TCtx.cand (X : TCtx posOf c st hd code n par lo hi) (nd : Node)
    (hc : opC nd.op = code.toNat) (hlo : opLo nd.op = lo.toNat) (hhi : opHi nd.op = hi.toNat)
    (htl : tailLen nd = n.toNat)
    (hfit : ∀ w ∈ tailW posOf id nd, w < 2 ^ 32)
    (hcells : ∀ k w, (tailW posOf (offs st.pool) nd)[k]? = some w →
      U c.pool (c.k.plen.toNat + 1 + k) w)
    (hty : Typed st nd) : Acc posOf c st := by
  have hC := X.code; have hN := X.n; have hL := X.lo; have hH := X.hi; have hlt := X.lt
  have hf : Fits posOf nd := ⟨by omega, by omega, by omega, tailW_zero_lt hfit⟩
  have hh : hdrW nd = hd := by rw [hdrW, hc, hlo, hhi, htl, hC, hN, hL, hH]; omega
  refine ⟨nd, ⟨hf, ?_, ?_, hty.1⟩, hty⟩
  · have := X.room; unfold nodeSize; omega
  · intro k w hk
    cases k with
    | zero =>
      simp only [nodeW_getElem?_zero, Option.some.injEq] at hk
      rw [← hk, hh]; exact X.cell
    | succ k =>
      rw [nodeW_getElem?_succ] at hk
      have := hcells k w hk
      rwa [show c.k.plen.toNat + (k + 1) = c.k.plen.toNat + 1 + k by omega]

variable {is : List Nat} {ts : List Bcf.Ty} {t0 t1 t2 : BitVec 32}

/-- A non-leaf operator with the candidate's code and parameters that type-checks on the
argument types is accepted. -/
theorem TCtx.accept (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (op : Op) {t : Bcf.Ty} (hl : isLeaf op = false) (hc : opC op = code.toNat)
    (hlo : opLo op = lo.toNat) (hhi : opHi op = hi.toNat) (hty : op.resultTy ts = some t) :
    Acc posOf c st := by
  have hnl : ¬ IsLeaf (Node.mk op is.toArray).op := by simp [IsLeaf, hl]
  have hlt : ∀ i ∈ is, i < st.pool.size := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
    exact (A.args k _ (by simp)).1
  apply X.cand ⟨op, is.toArray⟩ hc hlo hhi
  · rw [tailLen_of_not_leaf hnl]; simpa using A.len
  · rw [tailW_of_not_leaf hnl]
    intro w hw
    simp at hw
    have h1 := hlt w hw
    have h2 := X.inv.rep.size_le
    have h3 := X.inv.poolCap
    simp only [maxPool] at h3
    omega
  · intro k w hk
    rw [tailW_of_not_leaf hnl] at hk
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    exact (A.args k i hi).2
  · refine ⟨?_, ts, t, A.tys, hty⟩
    simpa using hlt

end

/-! ## Machine-word facts as facts about natural numbers -/

/-- Turn comparisons of 32-bit words into comparisons of their values. -/
macro "bvn" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [bv_eq_toNat, BitVec.lt_def, BitVec.le_def, BitVec.toNat_ofNat,
      BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, Nat.reducePow, Nat.reduceMod] $[$loc]?)

/-! ## Decoding an encoded type -/

theorem ty_bv_of_eq {a : Bcf.Ty} {w : Nat} (hf : TyFits a) (h : tyW a = w) (hw : w < 0x1000) :
    a = .bv w := (tyW_eq_bv_iff hf hw).mp h

theorem ty_bool_of_eq {a : Bcf.Ty} (hf : TyFits a) (h : tyW a = 0x1000) : a = .bool :=
  (tyW_eq_bool_iff hf).mp h

theorem ty_bv_of_lt {a : Bcf.Ty} (hf : TyFits a) (h : tyW a < 0x1000) :
    ∃ m, a = .bv m ∧ 1 ≤ m ∧ m ≤ 256 := by
  obtain ⟨m, rfl⟩ := (tyW_lt_bool_iff hf).mp h
  exact ⟨m, rfl, hf⟩

theorem allBv_of_forall {ts : List Bcf.Ty} {w : Nat} (hf : ∀ ty ∈ ts, TyFits ty) (hw : w < 0x1000)
    (h : ∀ ty ∈ ts, tyW ty = w) : allBv w ts = true := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
    have ea := ty_bv_of_eq (hf a (by simp)) (h a (by simp)) hw
    subst ea
    simp only [allBv, beq_self_eq_true, Bool.true_and]
    exact ih (fun ty hty => hf ty (by simp [hty])) (fun ty hty => h ty (by simp [hty]))

theorem allBool_of_forall {ts : List Bcf.Ty} (hf : ∀ ty ∈ ts, TyFits ty)
    (h : ∀ ty ∈ ts, tyW ty = 0x1000) : allBool ts = true := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
    have ea := ty_bool_of_eq (hf a (by simp)) (h a (by simp))
    subst ea
    simp only [allBool]
    exact ih (fun ty hty => hf ty (by simp [hty])) (fun ty hty => h ty (by simp [hty]))

theorem inClass_true_of_forall {ts : List Bcf.Ty} (hf : ∀ ty ∈ ts, TyFits ty)
    (h : ∀ ty ∈ ts, tyW ty = 0x1000) : ts.all (Ty.inClass true) = true := by
  rw [List.all_eq_true]
  intro ty hty
  rw [ty_bool_of_eq (hf ty hty) (h ty hty)]
  rfl

theorem bvWidths_eq {ts : List Bcf.Ty} (hne : ts ≠ [])
    (h : ts.all (Ty.inClass false) = true) : bvWidths ts = some (ts.map tyW).sum := by
  induction ts with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ha, hrest⟩ := h
    cases a with
    | bool => cases ha
    | list e k => cases ha
    | bv m =>
      cases rest with
      | nil => simp [bvWidths]
      | cons b rest' =>
        have := ih (by simp) hrest
        simp only [bvWidths, this, Option.map_some, List.map_cons, List.sum_cons, tyW_bv]

theorem sum_tyW_le {ts : List Bcf.Ty} (hf : ∀ ty ∈ ts, TyFits ty) :
    (ts.map tyW).sum ≤ ts.length * 0x2200 := by
  induction ts with
  | nil => simp
  | cons a rest ih =>
    have h1 := tyW_lt (hf a (by simp))
    have h2 := ih (fun ty hty => hf ty (by simp [hty]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-! ## The shape of the argument list -/

theorem list_len_two {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem list_len_three {α : Type} {l : List α} (h : l.length = 3) : ∃ a b d, l = [a, b, d] := by
  match l, h with
  | [a, b, d], _ => exact ⟨a, b, d, rfl⟩

section
variable {c : CMem} {st : St} {n : BitVec 32} {is : List Nat} {ts : List Bcf.Ty}
  {t0 t1 t2 : BitVec 32}

theorem ACtx.ts_len (A : ACtx c st n is ts t0 t1 t2) : ts.length = n.toNat := by
  rw [mapOpt_length A.tys, A.len]

theorem ACtx.one (A : ACtx c st n is ts t0 t1 t2) (h : n = 1#32) :
    ∃ a, ts = [a] ∧ TyFits a ∧ t0.toNat = tyW a := by
  have hl := A.ts_len
  rw [h] at hl
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
  exact ⟨a, rfl, A.fit a (by simp), A.t0 a rfl⟩

theorem ACtx.two (A : ACtx c st n is ts t0 t1 t2) (h : n = 2#32) :
    ∃ a b, ts = [a, b] ∧ TyFits a ∧ TyFits b ∧ t0.toNat = tyW a ∧ t1.toNat = tyW b := by
  have hl := A.ts_len
  rw [h] at hl
  obtain ⟨a, b, rfl⟩ := list_len_two hl
  exact ⟨a, b, rfl, A.fit a (by simp), A.fit b (by simp), A.t0 a rfl, A.t1 b rfl⟩

theorem ACtx.three (A : ACtx c st n is ts t0 t1 t2) (h : n = 3#32) :
    ∃ a b d, ts = [a, b, d] ∧ TyFits a ∧ TyFits b ∧ TyFits d ∧
      t0.toNat = tyW a ∧ t1.toNat = tyW b ∧ t2.toNat = tyW d := by
  have hl := A.ts_len
  rw [h] at hl
  obtain ⟨a, b, d, rfl⟩ := list_len_three hl
  exact ⟨a, b, d, rfl, A.fit a (by simp), A.fit b (by simp), A.fit d (by simp),
    A.t0 a rfl, A.t1 b rfl, A.t2 d rfl⟩

end

/-! ## Leaves -/

section
variable {posOf : Nat → Nat} {c : CMem} {st : St} {hd : Nat} {code n par lo hi : BitVec 32}

theorem typed_leaf {op : Op} {t : Bcf.Ty} (h : op.resultTy [] = some t) : Typed st ⟨op, #[]⟩ :=
  ⟨by simp, [], t, rfl, h⟩

theorem TCtx.bvVar (X : TCtx posOf c st hd code n par lo hi)
    (hv : ∃ id, posOf id < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 1) (posOf id))
    (hc : code = 24#32) (h1 : n = 1#32) (h2 : hi = 0#32) (h3 : ¬ lo = 0#32) :
    Acc posOf c st := by
  obtain ⟨id, hid, hcell⟩ := hv
  bvn at hc h1 h2 h3
  apply X.cand ⟨.bvVar lo.toNat id, #[]⟩ hc.symm rfl h2.symm h1.symm
  · intro w hw
    simp only [tailW, List.mem_singleton] at hw
    subst hw; exact hid
  · intro k w hk
    rcases k with _ | k
    · simp only [tailW, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk; exact hcell
    · simp [tailW] at hk
  · exact typed_leaf (bvVarTy_eq_some.mpr ⟨rfl, h3, rfl⟩)

theorem TCtx.boolVar (X : TCtx posOf c st hd code n par lo hi)
    (hv : ∃ id, posOf id < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 1) (posOf id))
    (hc : code = 25#32) (h1 : n = 1#32) (h2 : par = 0#32) : Acc posOf c st := by
  obtain ⟨id, hid, hcell⟩ := hv
  bvn at hc h1 h2
  have hP := X.par; have hL := X.lo; have hH := X.hi
  apply X.cand ⟨.boolVar id, #[]⟩ hc.symm (show 0 = lo.toNat by omega)
    (show 0 = hi.toNat by omega) h1.symm
  · intro w hw
    simp only [tailW, List.mem_singleton] at hw
    subst hw; exact hid
  · intro k w hk
    rcases k with _ | k
    · simp only [tailW, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk; exact hcell
    · simp [tailW] at hk
  · exact typed_leaf (t := .bool) rfl

theorem TCtx.boolVal (X : TCtx posOf c st hd code n par lo hi)
    (hc : code = 9#32) (h1 : n = 0#32) (h2 : par &&& 65534#32 = 0#32) : Acc posOf c st := by
  have hP := X.par; have hL := X.lo; have hH := X.hi; have hlt := X.lt
  have hp2 : par.toNat < 2 := (bv_and_fffe_eq_zero_iff (by omega)).mp h2
  bvn at hc h1
  have hb : ∀ b : Bool, (if b then 1 else 0) = lo.toNat → Acc posOf c st := by
    intro b hb
    apply X.cand ⟨.boolVal b, #[]⟩ hc.symm hb (show 0 = hi.toNat by omega) h1.symm
    · intro w hw; simp [tailW] at hw
    · intro k w hk; simp [tailW] at hk
    · exact typed_leaf (t := .bool) rfl
  rcases Nat.lt_or_ge par.toNat 1 with hp | hp
  · exact hb false (by simp; omega)
  · exact hb true (by simp; omega)

/-- `BV_VAL`: `w0` is the first value word and, for a width above 32, `w1` the second. -/
theorem TCtx.bvVal (X : TCtx posOf c st hd code n par lo hi)
    (hc : code = 8#32) (h1 : hi = 0#32) (h2 : ¬ lo = 0#32) (h3 : lo ≤ 64#32)
    (h4 : n = (lo + 31#32) / 32#32) (w0 w1 : Nat) (hw0 : w0 < 2 ^ 32)
    (c0 : U c.pool (c.k.plen.toNat + 1) w0)
    (c1 : 32 < lo.toNat → w1 < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 2) w1)
    (hv : if lo.toNat ≤ 32 then w0 < 2 ^ lo.toNat else w1 < 2 ^ (lo.toNat - 32)) :
    Acc posOf c st := by
  have hL := X.lo
  bvn at hc h1 h2 h3 h4
  by_cases hle : lo.toNat ≤ 32
  · simp only [hle, ↓reduceIte] at hv
    apply X.cand ⟨.bvVal lo.toNat w0, #[]⟩ hc.symm rfl h1.symm
    · simp only [tailLen, hle, ↓reduceIte]; omega
    · intro w hw
      simp only [tailW, hle, ↓reduceIte, List.mem_singleton] at hw
      subst hw; omega
    · intro k w hk
      simp only [tailW, hle, ↓reduceIte] at hk
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        rw [← hk, Nat.mod_eq_of_lt hw0]; exact c0
      · simp at hk
    · exact typed_leaf (bvValTy_eq_some.mpr ⟨rfl, ⟨h2, by omega, hv⟩, rfl⟩)
  · simp only [hle, ↓reduceIte] at hv
    obtain ⟨hw1, c1⟩ := c1 (by omega)
    have e0 : (w0 + w1 * 4294967296) % 4294967296 = w0 := by omega
    have e1 : (w0 + w1 * 4294967296) / 4294967296 = w1 := by omega
    apply X.cand ⟨.bvVal lo.toNat (w0 + w1 * 4294967296), #[]⟩ hc.symm rfl h1.symm
    · simp only [tailLen, hle, ↓reduceIte]; omega
    · intro w hw
      simp only [tailW, hle, ↓reduceIte, Nat.reducePow, e0, e1, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · intro k w hk
      simp only [tailW, hle, ↓reduceIte, Nat.reducePow, e0, e1] at hk
      rcases k with _ | _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        rw [← hk]; exact c0
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk
        rw [← hk]; exact c1
      · simp at hk
    · refine typed_leaf (bvValTy_eq_some.mpr ⟨rfl, ⟨h2, by omega, ?_⟩, rfl⟩)
      have e : lo.toNat = (lo.toNat - 32) + 32 := by omega
      rw [e, Nat.pow_add]
      generalize 2 ^ (lo.toNat - 32) = P at hv
      have : (w1 + 1) * 4294967296 ≤ P * 4294967296 := Nat.mul_le_mul_right _ hv
      omega

end

/-! ## Operators with arguments -/

section
variable {posOf : Nat → Nat} {c : CMem} {st : St} {hd : Nat} {code n par lo hi : BitVec 32}
  {is : List Nat} {ts : List Bcf.Ty} {t0 t1 t2 : BitVec 32}

/-- `BV_NEG`, `BV_NOT`. -/
theorem TCtx.bvUn (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 128#32 ∨ code = 120#32) (h1 : n = 1#32) (h2 : hi = 0#32) (h3 : ¬ lo = 0#32)
    (h4 : t0 = lo) : Acc posOf c st := by
  obtain ⟨a, rfl, hfa, ha⟩ := A.one h1
  bvn at hc h2 h3 h4
  have hL := X.lo
  have ea : a = .bv lo.toNat := ty_bv_of_eq hfa (by omega) (by omega)
  have key : ∀ op : Op, isLeaf op = false → opLo op = lo.toNat → opHi op = 0 →
      op.resultTy = bvUnTy lo.toNat → opC op = code.toNat → Acc posOf c st := by
    intro op hl hlo hhi hr hcc
    exact X.accept A op hl hcc hlo (by omega)
      (by rw [hr]; exact bvUnTy_eq_some.mpr ⟨by rw [ea], h3, rfl⟩)
  rcases hc with hc | hc
  · exact key (.bvNeg lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvNot lo.toNat) rfl rfl rfl rfl hc.symm

/-- `BV_EXTRACT`. -/
theorem TCtx.bvExtract (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 56#32) (h1 : n = 1#32) (h2 : t0 < 4096#32) (h3 : lo ≤ hi) (h4 : hi < t0) :
    Acc posOf c st := by
  obtain ⟨a, rfl, hfa, ha⟩ := A.one h1
  bvn at hc h2 h3 h4
  obtain ⟨m, rfl, hm, -⟩ := ty_bv_of_lt hfa (by omega)
  simp only [tyW_bv] at ha
  exact X.accept A (.bvExtract hi.toNat lo.toNat) rfl hc.symm rfl rfl
    (bvExtractTy_eq_some.mpr ⟨m, rfl, h3, by omega, rfl⟩)

/-- `BV_SEXT`, `BV_ZEXT`. -/
theorem TCtx.bvExt (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 72#32 ∨ code = 88#32) (h1 : n = 1#32) (h2 : t0 < 4096#32) (h3 : ¬ lo = 0#32)
    (h4 : t0 + hi = lo) : Acc posOf c st := by
  obtain ⟨a, rfl, hfa, ha⟩ := A.one h1
  bvn at hc h2 h3 h4
  obtain ⟨m, rfl, hm, -⟩ := ty_bv_of_lt hfa (by omega)
  simp only [tyW_bv] at ha
  have hH := X.hi; have hlt := X.lt
  have key : ∀ op : Op, isLeaf op = false → opLo op = lo.toNat → opHi op = hi.toNat →
      op.resultTy = bvExtTy lo.toNat hi.toNat → opC op = code.toNat → Acc posOf c st := by
    intro op hl hlo hhi hr hcc
    exact X.accept A op hl hcc hlo hhi
      (by rw [hr]; exact bvExtTy_eq_some.mpr ⟨m, rfl, h3, by omega, rfl⟩)
  rcases hc with hc | hc
  · exact key (.bvSignExtend lo.toNat hi.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvZeroExtend lo.toNat hi.toNat) rfl rfl rfl rfl hc.symm

/-- `BV_SIZE`. -/
theorem TCtx.bvSize (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 104#32) (h1 : n = 1#32) (h2 : hi = 0#32) (h3 : ¬ lo = 0#32) (h4 : t0 < 4096#32)
    (h5 : 9#32 ≤ lo ∨ (lo < 9#32 ∧ t0 < 1#32 <<< lo.toNat)) : Acc posOf c st := by
  obtain ⟨a, rfl, hfa, ha⟩ := A.one h1
  bvn at hc h2 h3 h4
  obtain ⟨m, rfl, hm, hm'⟩ := ty_bv_of_lt hfa (by omega)
  simp only [tyW_bv] at ha
  refine X.accept A (.bvSize lo.toNat) rfl hc.symm rfl h2.symm
    (bvSizeTy_eq_some.mpr ⟨m, rfl, h3, ?_, rfl⟩)
  rcases h5 with h5 | ⟨h5, h6⟩
  · have h9 : 9 ≤ lo.toNat := by bvn at h5; exact h5
    have : 2 ^ 9 ≤ 2 ^ lo.toNat := Nat.pow_le_pow_right (by omega) h9
    omega
  · have h9 : lo.toNat < 9 := by bvn at h5; exact h5
    have hp : 2 ^ lo.toNat < 2 ^ 9 := Nat.pow_lt_pow_right (by omega) h9
    rw [BitVec.lt_def, BitVec.toNat_shiftLeft] at h6
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.one_shiftLeft] at h6
    rw [Nat.mod_eq_of_lt (by omega)] at h6
    omega

/-- `BV_REPEAT`. -/
theorem TCtx.bvRepeat (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 168#32) (h1 : n = 1#32) (h2 : t0 < 4096#32) (h3 : ¬ lo = 0#32)
    (h4 : t0 * hi = lo) : Acc posOf c st := by
  obtain ⟨a, rfl, hfa, ha⟩ := A.one h1
  bvn at hc h2 h3 h4
  obtain ⟨m, rfl, hm, hm'⟩ := ty_bv_of_lt hfa (by omega)
  simp only [tyW_bv] at ha
  have hH := X.hi; have hlt := X.lt
  have hmul : m * hi.toNat ≤ 256 * 255 := Nat.mul_le_mul hm' (by omega)
  rw [ha, Nat.mod_eq_of_lt (by omega)] at h4
  exact X.accept A (.bvRepeat lo.toNat hi.toNat) rfl hc.symm rfl rfl
    (bvRepeatTy_eq_some.mpr ⟨m, rfl, h3, h4, rfl⟩)

/-- `BV_SUB`, shifts, divisions. -/
theorem TCtx.bvBin (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 16#32 ∨ code = 96#32 ∨ code = 112#32 ∨ code = 192#32 ∨ code = 48#32 ∨
      code = 144#32 ∨ code = 176#32 ∨ code = 208#32)
    (h1 : n = 2#32) (h2 : hi = 0#32) (h3 : ¬ lo = 0#32) (h4 : t0 = lo) (h5 : t1 = lo) :
    Acc posOf c st := by
  obtain ⟨a, b, rfl, hfa, hfb, ha, hb⟩ := A.two h1
  bvn at hc h2 h3 h4 h5
  have hL := X.lo
  have ea : a = .bv lo.toNat := ty_bv_of_eq hfa (by omega) (by omega)
  have eb : b = .bv lo.toNat := ty_bv_of_eq hfb (by omega) (by omega)
  have key : ∀ op : Op, isLeaf op = false → opLo op = lo.toNat → opHi op = 0 →
      op.resultTy = bvBinTy lo.toNat → opC op = code.toNat → Acc posOf c st := by
    intro op hl hlo hhi hr hcc
    exact X.accept A op hl hcc hlo (by omega)
      (by rw [hr]; exact bvBinTy_eq_some.mpr ⟨by rw [ea, eb], h3, rfl⟩)
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc
  · exact key (.bvSub lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvShl lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvLshr lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvAshr lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvUdiv lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvUrem lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvSdiv lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvSmod lo.toNat) rfl rfl rfl rfl hc.symm

/-- `BV_ITE`. -/
theorem TCtx.bvIte (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 40#32) (h1 : n = 3#32) (h2 : hi = 0#32) (h3 : ¬ lo = 0#32)
    (h4 : t0 = 4096#32 ∨ t0 = 1#32) (h5 : t1 = lo) (h6 : t2 = lo) : Acc posOf c st := by
  obtain ⟨a, b, d, rfl, hfa, hfb, hfd, ha, hb, hd'⟩ := A.three h1
  bvn at hc h2 h3 h4 h5 h6
  have hL := X.lo
  have eb : b = .bv lo.toNat := ty_bv_of_eq hfb (by omega) (by omega)
  have ed : d = .bv lo.toNat := ty_bv_of_eq hfd (by omega) (by omega)
  have ea : a = .bool ∨ a = .bv 1 := by
    rcases h4 with h4 | h4
    · exact Or.inl (ty_bool_of_eq hfa (by omega))
    · exact Or.inr (ty_bv_of_eq hfa (by omega) (by omega))
  subst eb ed
  exact X.accept A (.bvIte lo.toNat) rfl hc.symm rfl h2.symm
    (bvIteTy_eq_some.mpr ⟨a, rfl, h3, ea, rfl⟩)

/-- `BV_ADD`, `BV_MUL`, `BV_OR`, `BV_AND`, `BV_XOR`. -/
theorem TCtx.bvN (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 0#32 ∨ code = 32#32 ∨ code = 64#32 ∨ code = 80#32 ∨ code = 160#32)
    (h1 : 2#32 ≤ n) (h2 : hi = 0#32) (h3 : ¬ lo = 0#32)
    (h4 : ∀ ty ∈ ts, tyW ty = lo.toNat) : Acc posOf c st := by
  bvn at hc h1 h2 h3
  have hL := X.lo
  have hlen := A.ts_len
  have key : ∀ op : Op, isLeaf op = false → opLo op = lo.toNat → opHi op = 0 →
      op.resultTy = bvNTy lo.toNat → opC op = code.toNat → Acc posOf c st := by
    intro op hl hlo hhi hr hcc
    exact X.accept A op hl hcc hlo (by omega)
      (by rw [hr]
          exact bvNTy_eq_some.mpr ⟨h3, allBv_of_forall A.fit (by omega) h4, by omega, rfl⟩)
  rcases hc with hc | hc | hc | hc | hc
  · exact key (.bvAdd lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvMul lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvOr lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvAnd lo.toNat) rfl rfl rfl rfl hc.symm
  · exact key (.bvXor lo.toNat) rfl rfl rfl rfl hc.symm

/-- `BV_CONCAT`. -/
theorem TCtx.bvConcat (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 152#32) (h1 : 2#32 ≤ n) (h2 : hi = 0#32) (h3 : ¬ lo = 0#32)
    (h4 : sumBvM ts = lo) : Acc posOf c st := by
  bvn at hc h1 h2 h3
  have hL := X.lo; have hN := X.n
  have hlen := A.ts_len
  have hsum := sum_tyW_le A.fit
  have hall : ts.all (Ty.inClass false) = true := by
    by_cases hall : ts.all (Ty.inClass false) = true
    · exact hall
    · simp only [sumBvM, hall] at h4
      have := congrArg BitVec.toNat h4
      simp [noid] at this
      omega
  simp only [sumBvM, hall, ↓reduceIte] at h4
  have h5 := congrArg BitVec.toNat h4
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h5
  have hne : ts ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
  exact X.accept A (.bvConcat lo.toNat) rfl hc.symm rfl h2.symm
    (bvConcatTy_eq_some.mpr ⟨h3, by rw [bvWidths_eq hne hall, h5], by omega, rfl⟩)

/-- `BV_FROM_BOOL`. -/
theorem TCtx.bvFromBool (X : TCtx posOf c st hd code n par lo hi)
    (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 136#32) (h1 : ¬ n = 0#32) (h2 : par = 0#32)
    (h4 : ∀ ty ∈ ts, tyW ty = 4096) : Acc posOf c st := by
  bvn at hc h1 h2
  have hP := X.par; have hL := X.lo; have hH := X.hi
  have hlen := A.ts_len
  exact X.accept A .bvFromBool rfl hc.symm (show 0 = lo.toNat by omega)
    (show 0 = hi.toNat by omega)
    (bvFromBoolTy_eq_some.mpr ⟨allBool_of_forall A.fit h4, by omega, rfl⟩)

/-- `BOOL_NOT`. -/
theorem TCtx.boolNot (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 129#32) (h1 : par = 0#32) (h2 : n = 1#32) (h3 : t0 = 4096#32) :
    Acc posOf c st := by
  obtain ⟨a, rfl, hfa, ha⟩ := A.one h2
  bvn at hc h1 h3
  have hP := X.par; have hL := X.lo; have hH := X.hi
  have ea : a = .bool := ty_bool_of_eq hfa (by omega)
  subst ea
  exact X.accept A .boolNot rfl hc.symm (show 0 = lo.toNat by omega)
    (show 0 = hi.toNat by omega) (boolNotTy_eq_some.mpr ⟨rfl, rfl⟩)

/-- `BOOL_BITOF`. -/
theorem TCtx.boolBitof (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 73#32) (h1 : hi = 0#32) (h2 : n = 1#32) (h3 : t0 < 4096#32) (h4 : lo < t0) :
    Acc posOf c st := by
  obtain ⟨a, rfl, hfa, ha⟩ := A.one h2
  bvn at hc h1 h3 h4
  obtain ⟨m, rfl, hm, -⟩ := ty_bv_of_lt hfa (by omega)
  simp only [tyW_bv] at ha
  exact X.accept A (.boolBitof lo.toNat) rfl hc.symm rfl h1.symm
    (bitofTy_eq_some.mpr ⟨m, rfl, by omega, rfl⟩)

/-- `BOOL_EQ`, `BOOL_DISTINCT`. -/
theorem TCtx.boolEq (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 17#32 ∨ code = 81#32) (h1 : par = 0#32) (h2 : n = 2#32) (h3 : t0 = t1)
    (h4 : t0 < 8192#32) : Acc posOf c st := by
  obtain ⟨a, b, rfl, hfa, hfb, ha, hb⟩ := A.two h2
  bvn at hc h1 h3 h4
  have hP := X.par; have hL := X.lo; have hH := X.hi
  have eab : a = b := tyW_inj hfa hfb (by omega)
  subst eab
  have hsc : a.isScalar = true := (tyW_lt_list_iff hfa).mp (by omega)
  have key : ∀ op : Op, isLeaf op = false → opLo op = 0 → opHi op = 0 →
      op.resultTy = eqTy → opC op = code.toNat → Acc posOf c st := by
    intro op hl hlo hhi hr hcc
    exact X.accept A op hl hcc (by omega) (by omega)
      (by rw [hr]; exact eqTy_eq_some.mpr ⟨a, rfl, hsc, rfl⟩)
  rcases hc with hc | hc
  · exact key .eq rfl rfl rfl rfl hc.symm
  · exact key .distinct rfl rfl rfl rfl hc.symm

/-- The eight comparisons. -/
theorem TCtx.boolCmp (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 33#32 ∨ code = 49#32 ∨ code = 97#32 ∨ code = 113#32 ∨ code = 161#32 ∨
      code = 177#32 ∨ code = 193#32 ∨ code = 209#32)
    (h1 : par = 0#32) (h2 : n = 2#32) (h3 : t0 < 4096#32) (h4 : t0 = t1) : Acc posOf c st := by
  obtain ⟨a, b, rfl, hfa, hfb, ha, hb⟩ := A.two h2
  bvn at hc h1 h3 h4
  have hP := X.par; have hL := X.lo; have hH := X.hi
  have eab : a = b := tyW_inj hfa hfb (by omega)
  subst eab
  obtain ⟨m, rfl, -, -⟩ := ty_bv_of_lt hfa (by omega)
  have key : ∀ op : Op, isLeaf op = false → opLo op = 0 → opHi op = 0 →
      op.resultTy = cmpTy → opC op = code.toNat → Acc posOf c st := by
    intro op hl hlo hhi hr hcc
    exact X.accept A op hl hcc (by omega) (by omega)
      (by rw [hr]; exact cmpTy_eq_some.mpr ⟨m, rfl, rfl⟩)
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc
  · exact key .ugt rfl rfl rfl rfl hc.symm
  · exact key .uge rfl rfl rfl rfl hc.symm
  · exact key .sgt rfl rfl rfl rfl hc.symm
  · exact key .sge rfl rfl rfl rfl hc.symm
  · exact key .ult rfl rfl rfl rfl hc.symm
  · exact key .ule rfl rfl rfl rfl hc.symm
  · exact key .slt rfl rfl rfl rfl hc.symm
  · exact key .sle rfl rfl rfl rfl hc.symm

/-- `BOOL_IMPLIES`. -/
theorem TCtx.boolImplies (X : TCtx posOf c st hd code n par lo hi)
    (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 145#32) (h1 : par = 0#32) (h2 : n = 2#32) (h3 : t0 = 4096#32)
    (h4 : t1 = 4096#32) : Acc posOf c st := by
  obtain ⟨a, b, rfl, hfa, hfb, ha, hb⟩ := A.two h2
  bvn at hc h1 h3 h4
  have hP := X.par; have hL := X.lo; have hH := X.hi
  have ea : a = .bool := ty_bool_of_eq hfa (by omega)
  have eb : b = .bool := ty_bool_of_eq hfb (by omega)
  subst ea eb
  exact X.accept A .implies rfl hc.symm (show 0 = lo.toNat by omega)
    (show 0 = hi.toNat by omega) (impliesTy_eq_some.mpr ⟨rfl, rfl⟩)

/-- `BOOL_ITE`. -/
theorem TCtx.boolIte (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 41#32) (h1 : par = 0#32) (h2 : n = 3#32) (h3 : t0 = 4096#32)
    (h4 : t1 = 4096#32) (h5 : t2 = 4096#32) : Acc posOf c st := by
  obtain ⟨a, b, d, rfl, hfa, hfb, hfd, ha, hb, hd'⟩ := A.three h2
  bvn at hc h1 h3 h4 h5
  have hP := X.par; have hL := X.lo; have hH := X.hi
  have ea : a = .bool := ty_bool_of_eq hfa (by omega)
  have eb : b = .bool := ty_bool_of_eq hfb (by omega)
  have ed : d = .bool := ty_bool_of_eq hfd (by omega)
  subst ea eb ed
  exact X.accept A .boolIte rfl hc.symm (show 0 = lo.toNat by omega)
    (show 0 = hi.toNat by omega) (boolIteTy_eq_some.mpr ⟨rfl, rfl⟩)

/-- `BOOL_CONJ`, `BOOL_DISJ`, `BOOL_XOR`. -/
theorem TCtx.boolN (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 1#32 ∨ code = 65#32 ∨ code = 57#32) (h1 : par = 0#32) (h2 : 2#32 ≤ n)
    (h4 : ∀ ty ∈ ts, tyW ty = 4096) : Acc posOf c st := by
  bvn at hc h1 h2
  have hP := X.par; have hL := X.lo; have hH := X.hi
  have hlen := A.ts_len
  have key : ∀ op : Op, isLeaf op = false → opLo op = 0 → opHi op = 0 →
      op.resultTy = boolNTy → opC op = code.toNat → Acc posOf c st := by
    intro op hl hlo hhi hr hcc
    exact X.accept A op hl hcc (by omega) (by omega)
      (by rw [hr]; exact boolNTy_eq_some.mpr ⟨allBool_of_forall A.fit h4, by omega, rfl⟩)
  rcases hc with hc | hc | hc
  · exact key .conj rfl rfl rfl rfl hc.symm
  · exact key .disj rfl rfl rfl rfl hc.symm
  · exact key .boolXor rfl rfl rfl rfl hc.symm

/-- `LIST_VAL` of booleans. -/
theorem TCtx.listBool (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 10#32) (h1 : hi = 0#32) (h2 : lo = 1#32)
    (h4 : ∀ ty ∈ ts, tyW ty = 4096) : Acc posOf c st := by
  bvn at hc h1 h2
  exact X.accept A (.listVal true) rfl hc.symm h2.symm h1.symm
    (listTy_eq_some.mpr ⟨inClass_true_of_forall A.fit h4, rfl⟩)

/-- `LIST_VAL` of bit-vectors. -/
theorem TCtx.listBv (X : TCtx posOf c st hd code n par lo hi) (A : ACtx c st n is ts t0 t1 t2)
    (hc : code = 10#32) (h1 : hi = 0#32) (h2 : lo ≤ 1#32) (h3 : ¬ lo = 1#32)
    (h4 : ¬ sumBvM ts = noid) : Acc posOf c st := by
  bvn at hc h1 h2 h3
  have hall : ts.all (Ty.inClass false) = true := by
    by_cases hall : ts.all (Ty.inClass false) = true
    · exact hall
    · simp only [sumBvM, hall] at h4
      exact absurd rfl h4
  exact X.accept A (.listVal false) rfl hc.symm (show 0 = lo.toNat by omega) h1.symm
    (listTy_eq_some.mpr ⟨hall, rfl⟩)

end

/-! ## The value words of `BV_VAL`, as the C tests them -/

theorem shr_zero_lt {w k : Nat} (hw : w < 2 ^ 32) (h : BitVec.ofNat 32 w >>> k = 0#32) :
    w < 2 ^ k := by
  have h1 := congrArg BitVec.toNat h
  rw [bv_shr, bv_toNat_ofNat hw] at h1
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h1
  rcases (Nat.div_eq_zero_iff).mp h1 with h2 | h2
  · have := Nat.two_pow_pos k; omega
  · exact h2

section
variable {posOf : Nat → Nat} {c : CMem} {st : St} {hd : Nat} {code n par lo hi : BitVec 32}

/-- Width below 32: the C tests `w0 >> lo == 0`. -/
theorem TCtx.bvVal_lo (X : TCtx posOf c st hd code n par lo hi)
    (hc : code = 8#32) (h1 : hi = 0#32) (h2 : ¬ lo = 0#32) (h3 : lo ≤ 64#32)
    (h4 : n = (lo + 31#32) / 32#32) (w0 w1 : Nat) (hw0 : w0 < 2 ^ 32)
    (c0 : U c.pool (c.k.plen.toNat + 1) w0)
    (c1 : 32 < lo.toNat → w1 < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 2) w1)
    (hlt : lo < 32#32) (hz : BitVec.ofNat 32 w0 >>> lo.toNat = 0#32) : Acc posOf c st := by
  apply X.bvVal hc h1 h2 h3 h4 w0 w1 hw0 c0 c1
  have : lo.toNat < 32 := BitVec.lt_def.mp hlt
  simp only [show lo.toNat ≤ 32 by omega, ↓reduceIte]
  exact shr_zero_lt hw0 hz

/-- Width strictly between 32 and 64: the C tests `w1 >> (lo - 32) == 0`. -/
theorem TCtx.bvVal_mid (X : TCtx posOf c st hd code n par lo hi)
    (hc : code = 8#32) (h1 : hi = 0#32) (h2 : ¬ lo = 0#32) (h3 : lo ≤ 64#32)
    (h4 : n = (lo + 31#32) / 32#32) (w0 w1 : Nat) (hw0 : w0 < 2 ^ 32)
    (c0 : U c.pool (c.k.plen.toNat + 1) w0)
    (c1 : 32 < lo.toNat → w1 < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 2) w1)
    (hgt : 32#32 < lo) (hz : BitVec.ofNat 32 w1 >>> (lo.toNat - 32) = 0#32) :
    Acc posOf c st := by
  apply X.bvVal hc h1 h2 h3 h4 w0 w1 hw0 c0 c1
  have hgt' : 32 < lo.toNat := BitVec.lt_def.mp hgt
  simp only [show ¬ lo.toNat ≤ 32 by omega, ↓reduceIte]
  exact shr_zero_lt (c1 hgt').1 hz

/-- Width 32 or 64: nothing to test. -/
theorem TCtx.bvVal_full (X : TCtx posOf c st hd code n par lo hi)
    (hc : code = 8#32) (h1 : hi = 0#32) (h2 : ¬ lo = 0#32) (h3 : lo ≤ 64#32)
    (h4 : n = (lo + 31#32) / 32#32) (w0 w1 : Nat) (hw0 : w0 < 2 ^ 32)
    (c0 : U c.pool (c.k.plen.toNat + 1) w0)
    (c1 : 32 < lo.toNat → w1 < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 2) w1)
    (hge : ¬ lo < 32#32) (hmid : ¬ (32#32 < lo ∧ lo < 64#32)) : Acc posOf c st := by
  apply X.bvVal hc h1 h2 h3 h4 w0 w1 hw0 c0 c1
  have h3' := h3
  bvn at h3' hge hmid
  by_cases hle : lo.toNat ≤ 32
  · simp only [hle, ↓reduceIte]
    have : lo.toNat = 32 := by omega
    rw [this]; exact hw0
  · simp only [hle, ↓reduceIte]
    have : lo.toNat = 64 := by omega
    rw [this]; exact (c1 (by omega)).1

/-- The value words of a `BV_VAL` candidate that passed the header test. -/
theorem TCtx.valWords (X : TCtx posOf c st hd code n par lo hi)
    (hval : hd % 256 = 0x08 → ∀ k, k < hd / 256 % 256 →
      ∃ w, w < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 1 + k) w)
    (hc : code = 8#32) (h2 : ¬ lo = 0#32) (h3 : lo ≤ 64#32) (h4 : n = (lo + 31#32) / 32#32) :
    ∃ w0 w1, w0 < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 1) w0 ∧
      (32 < lo.toNat → w1 < 2 ^ 32 ∧ U c.pool (c.k.plen.toNat + 2) w1) := by
  have hC := X.code; have hN := X.n
  bvn at hc h2 h3 h4
  have hv := hval (by omega)
  obtain ⟨w0, hw0, c0⟩ := hv 0 (by omega)
  by_cases hgt : 32 < lo.toNat
  · obtain ⟨w1, hw1, c1⟩ := hv 1 (by omega)
    exact ⟨w0, w1, hw0, c0, fun _ => ⟨hw1, c1⟩⟩
  · exact ⟨w0, 0, hw0, c0, fun h => absurd h hgt⟩

end

/-! ## The arguments of a non-leaf candidate -/

theorem args_exist {P : Nat → Nat → Prop} (m : Nat) (h : ∀ k, k < m → ∃ i, P k i) :
    ∃ is : List Nat, is.length = m ∧ ∀ k i, is[k]? = some i → P k i := by
  induction m with
  | zero => exact ⟨[], rfl, fun k i hk => by simp at hk⟩
  | succ m ih =>
    obtain ⟨is, hlen, his⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨i, hi⟩ := h m (by omega)
    refine ⟨is ++ [i], by simp [hlen], ?_⟩
    intro k j hk
    rcases Nat.lt_or_ge k m with hlt | hge
    · rw [List.getElem?_append_left (by omega)] at hk
      exact his k j hk
    · rw [List.getElem?_append_right (by omega)] at hk
      rcases hk' : k - is.length with _ | d
      · rw [hk'] at hk
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        have : k = m := by omega
        subst this; subst hk; exact hi
      · rw [hk'] at hk; simp at hk

theorem tys_exist {posOf : Nat → Nat} {c : CMem} {st : St} (hc : CoreInv posOf c st)
    {is : List Nat} (h : ∀ i ∈ is, i < st.pool.size) :
    ∃ ts, mapOpt (fun a => st.tys[a]?) is = some ts ∧ ∀ ty ∈ ts, TyFits ty := by
  induction is with
  | nil => exact ⟨[], rfl, fun ty hty => by simp at hty⟩
  | cons i rest ih =>
    obtain ⟨ts, hts, hfit⟩ := ih (fun j hj => h j (by simp [hj]))
    obtain ⟨_, ty, _, hty, hf, _⟩ := hc.argTy (h i (by simp))
    refine ⟨ty :: ts, by simp only [mapOpt, hty, hts], ?_⟩
    intro ty' hty'
    rcases List.mem_cons.mp hty' with rfl | hm
    · exact hf
    · exact hfit ty' hm

end Vbcf.Proof
