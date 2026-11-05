import EmbC.Kernel
import Vbcf.Proof.Eval9
import Vbcf.Prog

/-!
# Vbcf proofs: the Rewrite family, part 1 — the constant table, on the Lean side

* `RwAt p ws`: the words `ws` sit at offset `p` of `RwEnc.words` (the contents of `rw_tbl`).
* The table is decoded **generically**, by induction on `RwEnc.encUpTo`: the index word of a
  rule id is `0` or the offset of a record that encodes `rwTable rid` (`rw_tbl_index`), and a
  record splits into its header words, parameter types and patterns (`rw_rec_*`).
* Well-formedness of the table (`rw_tbl_wf`): its length is below `2^16`, and every pattern has
  variable numbers below 256 and literal values below `2^32`, every `BV(w)` parameter has
  `w < 2^16`.  These are the only facts about the concrete 151 rules that the proof uses; they
  are checked by one `decide` each (a few seconds), not word by word.
* `cval = memoVal` (`rw_cval_eq`): the C's `cval` is specified by `memoVal`, the Lean rule
  uses `cval`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

/-! ## `cval` is `memoVal` -/

theorem rw_cvalF_eq (st : St) : ∀ i f, i < f → cvalF st f i = memoVal st i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hm : ∀ l : List Nat, mapOpt (fun a => if a < i then cvalF st g a else none) l =
        mapOpt (fun a => if a < i then ((memoBuild st i)[a]?).bind id else none) l := by
      intro l
      apply mapOpt_congr
      intro a _
      by_cases ha : a < i
      · rw [ite_eq_left ha, ite_eq_left ha, ih a ha g (by omega), memoBuild_get st i a ha]; rfl
      · rw [ite_eq_right ha, ite_eq_right ha]
    unfold memoVal memoStep
    simp only [cvalF]
    split
    · rfl
    · rename_i n _
      split <;> simp only [hm]

theorem rw_cval_eq (st : St) (i : Nat) : Bcf.cval st i = memoVal st i :=
  rw_cvalF_eq st i (i + 1) (by omega)

/-! ## Words at an offset -/

/-- The words `ws` are at offset `p` of the table. -/
def RwAt (p : Nat) (ws : List Nat) : Prop :=
  ∀ (j : Nat) (hj : j < ws.length), RwEnc.words[p + j]? = some ws[j]

theorem RwAt.append {p : Nat} {a b : List Nat} : RwAt p (a ++ b) ↔ RwAt p a ∧ RwAt (p + a.length) b := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h j (by simp; omega)
      rwa [List.getElem_append_left hj] at this
    · have := h (a.length + j) (by simp; omega)
      simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at this
      rwa [show p + (a.length + j) = p + a.length + j by omega] at this
  · rintro ⟨ha, hb⟩ j hj
    rcases Nat.lt_or_ge j a.length with hlt | hge
    · rw [List.getElem_append_left hlt]; exact ha j hlt
    · rw [List.getElem_append_right hge]
      have := hb (j - a.length) (by simp at hj; omega)
      rwa [show p + a.length + (j - a.length) = p + j by omega] at this

theorem RwAt.cons {p x : Nat} {xs : List Nat} :
    RwAt p (x :: xs) ↔ RwEnc.words[p]? = some x ∧ RwAt (p + 1) xs := by
  rw [show x :: xs = [x] ++ xs from rfl, RwAt.append]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1 0 (by simp), by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j hj => by simp at hj; subst hj; simpa using h1, by simpa using h2⟩

theorem RwAt.head {p x : Nat} {xs : List Nat} (h : RwAt p (x :: xs)) : RwEnc.words[p]? = some x :=
  (RwAt.cons.mp h).1

theorem RwAt.tail {p x : Nat} {xs : List Nat} (h : RwAt p (x :: xs)) : RwAt (p + 1) xs :=
  (RwAt.cons.mp h).2

theorem RwAt.left {p : Nat} {a b : List Nat} (h : RwAt p (a ++ b)) : RwAt p a := (RwAt.append.mp h).1

theorem RwAt.right {p : Nat} {a b : List Nat} (h : RwAt p (a ++ b)) : RwAt (p + a.length) b :=
  (RwAt.append.mp h).2

/-- Words at an offset are inside the table. -/
theorem RwAt.le {p : Nat} {ws : List Nat} (h : RwAt p ws) (hne : 0 < ws.length) :
    p + ws.length ≤ RwEnc.words.length := by
  rcases ws with _ | ⟨x, xs⟩
  · simp at hne
  · have := h xs.length (by simp)
    have := lt_length_of_getElem? this
    simp; omega

/-! ## The table well-formedness facts -/

mutual
/-- A pattern whose variable numbers fit a byte and whose literals fit a word. -/
def wfE : RwExpr → Bool
  | .var i => i < 256
  | .tt => true
  | .ff => true
  | .lit v => v < 2 ^ 32
  | .symVal a b => wfE a && wfE b
  | .bvmax a => wfE a
  | .app _ as => wfA as
  | .ite a b c => wfE a && wfE b && wfE c
  | .extract a b c => wfE a && wfE b && wfE c
  | .zext a b => wfE a && wfE b
  | .sext a b => wfE a && wfE b
  | .repeat a b => wfE a && wfE b
def wfA : RwArgs → Bool
  | .nil => true
  | .cons a rest => wfE a && wfA rest
end

def wfTy : RwTy → Bool
  | .bv w => w < 65536
  | _ => true

def wfOpt : Option RwExpr → Bool
  | none => true
  | some e => wfE e

def wfRule (r : RwRule) : Bool :=
  r.params.all wfTy && wfOpt r.cond && wfE r.lhs && wfE r.rhs

/-- Count record words without constructing their absolute offsets. -/
private def rw_recWords (r : RwRule) : Nat :=
  4 + r.params.length + (encOpt r.cond).length + (encE r.lhs).length + (encE r.rhs).length

private theorem encRule_length_direct (off : Nat) (r : RwRule) :
    (encRule off r).length = rw_recWords r := by
  simp [encRule, rw_recWords]
  omega

private def rw_bodyWords (tbl : Nat → Option RwRule) : Nat → Nat
  | 0 => 0
  | n + 1 => rw_bodyWords tbl n + match tbl n with
    | none => 0
    | some r => rw_recWords r

private theorem encUpTo_lengths_direct (tbl : Nat → Option RwRule) : ∀ n,
    (encUpTo tbl n).1.length = n ∧
      (encUpTo tbl n).2.length = rw_bodyWords tbl n := by
  intro n
  induction n with
  | zero => simp [encUpTo, rw_bodyWords]
  | succ n ih =>
    simp only [encUpTo, rw_bodyWords]
    split <;> simp_all [encRule_length_direct]

set_option maxRecDepth 100000 in
/-- All of the table is shorter than `2^16` words. -/
theorem rw_words_len : RwEnc.words.length < 65536 := by
  have h : bound + rw_bodyWords rwTable bound < 65536 := by decide +kernel
  simpa [RwEnc.words, encTable, List.length_append,
    (encUpTo_lengths_direct rwTable bound).1,
    (encUpTo_lengths_direct rwTable bound).2] using h

set_option maxRecDepth 100000 in
theorem rw_tbl_wf_all :
    (List.range RwEnc.bound).all (fun i => match rwTable i with
      | some r => wfRule r
      | none => true) = true := by decide +kernel

theorem rw_tbl_wf {rid : Nat} (hr : rid < RwEnc.bound) {r : RwRule} (h : rwTable rid = some r) :
    wfRule r = true := by
  have := List.all_eq_true.mp rw_tbl_wf_all rid (List.mem_range.mpr hr)
  simpa [h] using this

/-! ## The index and the records -/

theorem rw_encUpTo (tbl : Nat → Option RwRule) : ∀ n,
    (encUpTo tbl n).1.length = n ∧
    ∀ i, i < n →
      (tbl i = none → (encUpTo tbl n).1[i]? = some 0) ∧
      (∀ r, tbl i = some r → ∃ pre post, (encUpTo tbl n).2 = pre ++ encRule (bound + pre.length) r ++ post ∧
        (encUpTo tbl n).1[i]? = some (bound + pre.length)) := by
  intro n
  induction n with
  | zero => exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    obtain ⟨hl, hi⟩ := ih
    simp only [encUpTo]
    split
    · rename_i hn
      refine ⟨by simp [hl], fun i hin => ?_⟩
      rcases Nat.lt_or_ge i n with hlt | hge
      · obtain ⟨h1, h2⟩ := hi i hlt
        refine ⟨fun e => ?_, fun r e => ?_⟩
        · rw [List.getElem?_append_left (by omega)]; exact h1 e
        · obtain ⟨pre, post, hb, hx⟩ := h2 r e
          exact ⟨pre, post, hb, by rw [List.getElem?_append_left (by omega)]; exact hx⟩
      · have : i = n := by omega
        subst this
        refine ⟨fun _ => by simp [hl], fun r e => by rw [hn] at e; cases e⟩
    · rename_i r0 hn
      refine ⟨by simp [hl], fun i hin => ?_⟩
      rcases Nat.lt_or_ge i n with hlt | hge
      · obtain ⟨h1, h2⟩ := hi i hlt
        refine ⟨fun e => ?_, fun r e => ?_⟩
        · rw [List.getElem?_append_left (by omega)]; exact h1 e
        · obtain ⟨pre, post, hb, hx⟩ := h2 r e
          refine ⟨pre, post ++ encRule (bound + (encUpTo tbl n).2.length) r0, ?_, ?_⟩
          · rw [hb]; simp
          · rw [List.getElem?_append_left (by omega)]; exact hx
      · have : i = n := by omega
        subst this
        refine ⟨fun e => (by rw [hn] at e; cases e), fun r e => ?_⟩
        rw [hn] at e; cases e
        exact ⟨(encUpTo tbl i).2, [], by simp, by simp [hl]⟩

theorem rw_encTable_eq (tbl : Nat → Option RwRule) :
    encTable tbl = (encUpTo tbl bound).1 ++ (encUpTo tbl bound).2 := by
  unfold encTable; cases encUpTo tbl bound; rfl

theorem rw_words_eq : RwEnc.words = (encUpTo rwTable bound).1 ++ (encUpTo rwTable bound).2 :=
  rw_encTable_eq rwTable

/-- The index word of a rule id below `RW_NRULES`. -/
theorem rw_tbl_index {rid : Nat} (hr : rid < bound) :
    (rwTable rid = none → RwEnc.words[rid]? = some 0) ∧
    (∀ r, rwTable rid = some r → ∃ off, RwEnc.words[rid]? = some off ∧ bound ≤ off ∧
      RwAt off (encRule off r)) := by
  obtain ⟨hl, hi⟩ := rw_encUpTo rwTable bound
  obtain ⟨h1, h2⟩ := hi rid hr
  refine ⟨fun e => ?_, fun r e => ?_⟩
  · rw [rw_words_eq, List.getElem?_append_left (by omega)]; exact h1 e
  · obtain ⟨pre, post, hb, hx⟩ := h2 r e
    refine ⟨bound + pre.length, ?_, by omega, ?_⟩
    · rw [rw_words_eq, List.getElem?_append_left (by omega)]; exact hx
    · intro j hj
      rw [rw_words_eq, List.getElem?_append_right (by omega), hl, hb,
        show bound + pre.length + j - bound = pre.length + j by omega, List.append_assoc,
        List.getElem?_append_right (by omega), show pre.length + j - pre.length = j by omega,
        List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

/-! ### A record -/

/-- The pieces of a record at offset `off`. -/
structure RwRec (off : Nat) (r : RwRule) : Prop where
  np : RwEnc.words[off]? = some r.params.length
  params : RwAt (off + recHdr) (r.params.map encTy)
  cond : ∃ g, RwEnc.words[off + 1]? = some g ∧
    match r.cond with
    | none => g = 0
    | some e => 0 < g ∧ RwAt g (encE e)
  lhs : ∃ g, RwEnc.words[off + 2]? = some g ∧ RwAt g (encE r.lhs)
  rhs : ∃ g, RwEnc.words[off + 3]? = some g ∧ RwAt g (encE r.rhs)

theorem rw_rec {off : Nat} {r : RwRule} (hoff : 0 < off) (h : RwAt off (encRule off r)) :
    RwRec off r := by
  unfold encRule at h
  simp only [List.append_assoc] at h
  have h0 := h.left
  have h1 := h.right
  simp only [List.length_cons, List.length_nil] at h1
  have hp := h1.left
  have h3 := h1.right
  have hc := h3.left
  have h4 := h3.right
  have hl := h4.left
  have hrr := h4.right
  have g0 := h0.head; have g1 := h0.tail.head; have g2 := h0.tail.tail.head
  have g3 := h0.tail.tail.tail.head
  refine ⟨by simpa using g0, by simpa [recHdr] using hp, ⟨_, g1, ?_⟩, ⟨_, g2, ?_⟩, ⟨_, g3, ?_⟩⟩
  · cases e : r.cond with
    | none => simp
    | some ce =>
      simp only [Option.isSome_some, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      have := hc
      simp only [e] at this
      simpa [recHdr, encOpt] using this
  · simpa [recHdr, Nat.add_assoc] using hl
  · simpa [recHdr, Nat.add_assoc] using hrr

/-! ## Reading `rw_tbl` in C -/

theorem rw_findConst : Vbcf.prog.findConst "rw_tbl" = some rwTblDef := rfl

theorem rw_tbl_get {k w : Nat} (h : RwEnc.words[k]? = some w) :
    rwTblDef.words[k]? = some (BitVec.ofNat 32 w) := by
  simp [rwTblDef, h]

/-! ## Header words -/

theorem rw_hdr_eq {t a l : Nat} (ht : t < 256) (ha : a < 256) : hdr t a l = t + a * 256 + l * 65536 := by
  unfold hdr
  have h1 : t ||| a <<< 8 = a * 256 + t := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : t < 2 ^ 8), Nat.shiftLeft_eq]
  rw [h1, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : a * 256 + t < 2 ^ 16),
    Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  omega

section hdrbv
variable {t a l : Nat} (ht : t < 256) (ha : a < 256) (hl : l < 65536)
include ht ha hl

theorem rw_hdr_tag : BitVec.ofNat 32 (t + a * 256 + l * 65536) &&& 255#32 = BitVec.ofNat 32 t := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]; omega

theorem rw_hdr_aux :
    BitVec.ofNat 32 (t + a * 256 + l * 65536) >>> 8 &&& 255#32 = BitVec.ofNat 32 a := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_shr_8, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]; omega

theorem rw_hdr_len :
    BitVec.ofNat 32 (t + a * 256 + l * 65536) >>> 16 = BitVec.ofNat 32 l := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_16, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]; omega

end hdrbv

/-! ## Patterns -/

/-- The tag of a pattern. -/
def tagE : RwExpr → Nat
  | .var _ => tVar
  | .tt => tTT
  | .ff => tFF
  | .lit _ => tLit
  | .symVal _ _ => tSymVal
  | .bvmax _ => tBvmax
  | .app _ _ => tApp
  | .ite _ _ _ => tIte
  | .extract _ _ _ => tExtract
  | .zext _ _ => tZext
  | .sext _ _ => tSext
  | .repeat _ _ => tRepeat

/-- The `aux` byte of a pattern. -/
def auxE : RwExpr → Nat
  | .var i => i
  | .app op _ => (opCode (op.node 0)).1
  | _ => 0

theorem rw_opC_lt (op : RwOp) : opC (op.node 0) < 256 := by
  cases op <;> decide

theorem rw_encE_cons (e : RwExpr) : ∃ rest, encE e = hdr (tagE e) (auxE e) (encE e).length :: rest := by
  cases e <;> simp [encE, tagE, auxE]

theorem rw_encE_len_pos (e : RwExpr) : 0 < (encE e).length := by
  obtain ⟨rest, h⟩ := rw_encE_cons e
  rw [h]; simp

theorem rw_tagE_lt (e : RwExpr) : tagE e < 12 := by
  cases e <;> simp only [tagE] <;> decide

theorem rw_auxE_lt {e : RwExpr} (hw : wfE e = true) : auxE e < 256 := by
  cases e <;> simp [auxE, wfE] at hw ⊢
  · exact hw
  · exact rw_opC_lt _

/-- The header word of a well-formed pattern at offset `p`, as `tag + aux * 256 + len * 65536`. -/
theorem rw_head {p : Nat} {e : RwExpr} (h : RwAt p (encE e)) (hw : wfE e = true) :
    RwEnc.words[p]? = some (tagE e + auxE e * 256 + (encE e).length * 65536) ∧
      (encE e).length < 65536 ∧ p + (encE e).length < 65536 := by
  obtain ⟨rest, hr⟩ := rw_encE_cons e
  have h1 := h.le (rw_encE_len_pos e)
  have h2 := rw_words_len
  rw [hr] at h
  refine ⟨?_, by omega, by omega⟩
  rw [h.head, rw_hdr_eq (by have := rw_tagE_lt e; omega) (rw_auxE_lt hw)]

end Vbcf.Proof
