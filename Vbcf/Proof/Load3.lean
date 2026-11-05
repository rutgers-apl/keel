import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Load2

/-!
# Vbcf proofs: the loading phase, part 3 — the candidate `ck_load` writes

One iteration of `ck_load`'s loop writes a candidate node at the tail of the
pool, from the header at position `p` of the input:

* a variable (`BV_VAR`, `BOOL_VAR`, with `vlen = 0`): the header with arity 1,
  then its position `p` as the identity word;
* a bit-vector literal (`BV_VAL`): the header, then the `vlen` value words;
* anything else: the header, then for each argument word `a` (an earlier
  position) the id of the node loaded at `a`.

`LoadWritten` describes these cells.  `LoadWritten.candRaw` gives
`ck_intern`'s precondition, and `LoadWritten.loadNode` says that the node
`ck_intern` reports (if any) is what the Lean loader's `loadNode` produces.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem ld_if_pos {c : Prop} [Decidable c] (hc : c) {α : Sort _} {t e : α} : (if c then t else e) = t := by
  simp [hc]
theorem ld_if_neg {c : Prop} [Decidable c] (hc : ¬ c) {α : Sort _} {t e : α} : (if c then t else e) = e := by
  simp [hc]

/-! ## The words written -/

/-- The header is that of a variable. -/
def VarHdr (h : Nat) : Prop := hdrCode h = 0x18 ∨ hdrCode h = 0x19

instance (h : Nat) : Decidable (VarHdr h) := inferInstanceAs (Decidable (_ ∨ _))

/-- The header word written: a variable gets arity 1. -/
def ldHdr (h : Nat) : Nat := if VarHdr h then h + 256 else h

/-- The number of words written after the header. -/
def ldLen (h : Nat) : Nat := if VarHdr h then 1 else hdrVlen h

/-- The `k`-th word written after the header. -/
def ldArg (w : Nat → Nat) (p : Nat) (pm : Nat → Option Nat) (pool : Pool) (k : Nat) : Nat :=
  if VarHdr (w (3 + p)) then p
  else if hdrCode (w (3 + p)) = 0x08 then w (4 + p + k)
  else match pm (w (4 + p + k)) with
    | some i => offs pool i
    | none => 0

/-- The candidate for the expression at position `p` is at the tail of the pool. -/
structure LoadWritten (w : Nat → Nat) (p : Nat) (pm : Nat → Option Nat) (st : St) (c : CMem) :
    Prop where
  hdr : U c.pool c.k.plen.toNat (ldHdr (w (3 + p)))
  args : ∀ k, k < ldLen (w (3 + p)) → U c.pool (c.k.plen.toNat + 1 + k) (ldArg w p pm st.pool k)
  room : c.k.plen.toNat + 1 + ldLen (w (3 + p)) ≤ c.k.pcap.toNat
  var0 : VarHdr (w (3 + p)) → hdrVlen (w (3 + p)) = 0
  refs : ¬ VarHdr (w (3 + p)) → hdrCode (w (3 + p)) ≠ 0x08 → ∀ k, k < hdrVlen (w (3 + p)) →
    w (4 + p + k) < p ∧ ∃ i, pm (w (4 + p + k)) = some i ∧ i < st.pool.size

/-! ## Header arithmetic -/

theorem ldHdr_var {h : Nat} (hv : VarHdr h) : ldHdr h = h + 256 := by simp [ldHdr, hv]
theorem ldHdr_nvar {h : Nat} (hv : ¬ VarHdr h) : ldHdr h = h := by simp [ldHdr, hv]
theorem ldLen_var {h : Nat} (hv : VarHdr h) : ldLen h = 1 := by simp [ldLen, hv]
theorem ldLen_nvar {h : Nat} (hv : ¬ VarHdr h) : ldLen h = hdrVlen h := by simp [ldLen, hv]

theorem ldHdr_lt {h : Nat} (hh : h < 2 ^ 32) (hv0 : VarHdr h → hdrVlen h = 0) : ldHdr h < 2 ^ 32 := by
  unfold ldHdr
  split
  · rename_i hv; have := hv0 hv; unfold hdrVlen at this; omega
  · exact hh

theorem ldHdr_code {h : Nat} (_hv0 : VarHdr h → hdrVlen h = 0) : ldHdr h % 256 = hdrCode h := by
  unfold ldHdr hdrCode
  split
  · omega
  · rfl

theorem ldHdr_len {h : Nat} (hv0 : VarHdr h → hdrVlen h = 0) : ldHdr h / 256 % 256 = ldLen h := by
  unfold ldHdr ldLen
  split
  · rename_i hv; have := hv0 hv; unfold hdrVlen at this; omega
  · rfl

theorem ldHdr_params {h : Nat} (hv0 : VarHdr h → hdrVlen h = 0) : ldHdr h / 65536 = hdrParams h := by
  unfold ldHdr hdrParams
  split
  · rename_i hv; have := hv0 hv; unfold hdrVlen at this; omega
  · rfl

/-! ## `ck_intern`'s precondition -/

theorem LoadWritten.candRaw {w : Nat → Nat} {p d : Nat} {pm : Nat → Option Nat} {st : St} {c : CMem}
    (hW : LoadWritten w p pm st c) (hw : ∀ i, w i < 2 ^ 32) (hp : p = posOfW w d)
    (hp32 : p < 2 ^ 32) : CandRaw (posOfW w) c st := by
  have hv0 := hW.var0
  have hc := ldHdr_code hv0
  have hl := ldHdr_len hv0
  refine ⟨ldHdr (w (3 + p)), ldHdr_lt (hw _) hv0, hW.hdr, ?_, ?_, ?_, ?_⟩
  · rw [hl]; exact hW.room
  · rw [hc]
    intro hv _
    refine ⟨d, by rw [← hp]; exact hp32, ?_⟩
    have := hW.args 0 (by rw [ldLen_var hv]; omega)
    rw [ldArg, ld_if_pos (show VarHdr (w (3 + p)) from hv), Nat.add_zero] at this
    rw [← hp]; exact this
  · rw [hc, hl]
    intro h8 k hk
    have hnv : ¬ VarHdr (w (3 + p)) := by unfold VarHdr; omega
    refine ⟨w (4 + p + k), hw _, ?_⟩
    have := hW.args k hk
    simp only [ldArg, ld_if_neg hnv, h8, ↓reduceIte] at this
    exact this
  · rw [hc, hl]
    intro h18 h19 h8 _ k hk
    have hnv : ¬ VarHdr (w (3 + p)) := by unfold VarHdr; omega
    rw [ldLen_nvar hnv] at hk
    obtain ⟨_, i, hi, hlt⟩ := hW.refs hnv h8 k hk
    refine ⟨i, hlt, ?_⟩
    have := hW.args k (by rw [ldLen_nvar hnv]; exact hk)
    simp only [ldArg, ld_if_neg hnv, h8, ↓reduceIte, hi] at this
    exact this

/-! ## The node `ck_intern` reports is `loadNode`'s -/

/-- A list whose words are stored at `s, s+1, …` and that fits 32 bits is the
list of stored words. -/
theorem list_eq_of_U {cells : Array EmbC.Val} {s L : Nat} {l : List Nat} {f : Nat → Nat}
    (hl : l.length = L) (hW : ∀ k t, l[k]? = some t → U cells (s + k) t)
    (hU : ∀ k, k < L → U cells (s + k) (f k)) (hlt : ∀ t ∈ l, t < 2 ^ 32)
    (hf : ∀ k, k < L → f k < 2 ^ 32) : l = (List.range L).map f := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < L
  · have hk' : k < l.length := by omega
    have e := U_inj (hW k l[k] (by simp [hk'])) (hU k hk) (hlt _ (List.getElem_mem hk')) (hf k hk)
    simp [hk', hk, e]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem mapOpt_eq_some_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ k (hk : k < l.length) (hk' : k < l'.length), f l[k] = some l'[k]) → mapOpt f l = some l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hf => by
    have h0 := hf 0 (by simp) (by simp)
    have ih := mapOpt_eq_some_of (l := l) (l' := l') (by simpa using h)
      (fun k hk hk' => by
        have := hf (k + 1) (by simp; omega) (by simp; omega)
        simpa only [List.getElem_cons_succ] using this)
    simp only [List.getElem_cons_zero] at h0
    simp [mapOpt, h0, ih]

theorem LoadWritten.loadNode {w : Nat → Nat} {p d : Nat} {pm : Nat → Option Nat} {st st' : St}
    {c : CMem} {n : Node} {r : Nat}
    (hW : LoadWritten w p pm st c) (hw : ∀ i, w i < 2 ^ 32) (hp : p = posOfW w d)
    (hp32 : p < 2 ^ 32) (hoff : ∀ i, i < st.pool.size → offs st.pool i < 2 ^ 32)
    (hc : Cand (posOfW w) c st n) (hpush : pushNode st n = some (st', r)) :
    loadNode w p d pm = some n := by
  have hfit := hc.fits
  have hv0 := hW.var0
  have hh : hdrW n = ldHdr (w (3 + p)) :=
    U_inj (by simpa using hc.words 0 (hdrW n) rfl) hW.hdr (hdrW_lt hfit) (ldHdr_lt (hw _) hv0)
  have hcode : opC n.op = hdrCode (w (3 + p)) := by
    rw [← hdrW_code hfit, hh, ldHdr_code hv0]
  have hlen : tailLen n = ldLen (w (3 + p)) := by
    rw [← hdrW_len hfit, hh, ldHdr_len hv0]
  have e1 : hdrCode (w (3 + p)) = hdrW n % 256 := by rw [hdrW_code hfit, hcode]
  have e2 : hdrParams (w (3 + p)) = hdrW n / 65536 := by rw [hh, ldHdr_params hv0]
  have hargs : ∀ a ∈ n.args, a < st.pool.size := by
    simpa only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] using hc.args
  have hwords := hc.words
  unfold Vbcf.Proof.loadNode
  by_cases hv : VarHdr (w (3 + p))
  · -- a variable
    have hv' : hdrCode (w (3 + p)) = 0x18 ∨ hdrCode (w (3 + p)) = 0x19 := hv
    rw [ld_if_pos hv', ld_if_pos (hv0 hv), e1, e2]
    have hop : opC n.op = 0x18 ∨ opC n.op = 0x19 := by rw [hcode]; exact hv'
    rw [decodeNode_hdrW_var hfit hop d 0 #[]]
    have hleaf : IsLeaf n.op := by
      rcases hop with h | h
      · obtain ⟨_, _, e⟩ := opC_bvVar_iff.mp h; rw [e]; rfl
      · obtain ⟨_, e⟩ := opC_boolVar_iff.mp h; rw [e]; rfl
    have hnargs := leaf_args_of_pushNode hpush hleaf
    have ha0 := hW.args 0 (by rw [ldLen_var hv]; omega)
    simp only [ldArg, ld_if_pos hv, Nat.add_zero] at ha0
    have htail := hfit.tail
    rcases n with ⟨op, args⟩
    simp only at hnargs hop htail hwords ⊢
    subst hnargs
    rcases hop with h | h
    · obtain ⟨wd, id, rfl⟩ := opC_bvVar_iff.mp h
      have hu := hwords 1 (posOfW w id) (by simp [tailW])
      have e := U_inj hu ha0 (htail _ (by simp [tailW])) hp32
      rw [hp] at e
      rw [posOfW_inj w e]; rfl
    · obtain ⟨id, rfl⟩ := opC_boolVar_iff.mp h
      have hu := hwords 1 (posOfW w id) (by simp [tailW])
      have e := U_inj hu ha0 (htail _ (by simp [tailW])) hp32
      rw [hp] at e
      rw [posOfW_inj w e]; rfl
  · have hv' : ¬ (hdrCode (w (3 + p)) = 0x18 ∨ hdrCode (w (3 + p)) = 0x19) := hv
    rw [ld_if_neg hv']
    rw [ldHdr_nvar hv] at hh
    rw [ldLen_nvar hv] at hlen
    by_cases h8 : hdrCode (w (3 + p)) = 0x08
    · -- a bit-vector literal
      rw [ld_if_pos h8]
      have hop : opC n.op = 0x08 := by rw [hcode]; exact h8
      obtain ⟨wd, v, hopv⟩ := opC_bvVal_iff.mp hop
      have hnargs := leaf_args_of_pushNode hpush (by rw [hopv]; rfl)
      obtain ⟨argTys, t, _, _, hty, _⟩ := pushNode_cases hpush
      have htail : tailW (posOfW w) (offs st.pool) n = argWords w p (hdrVlen (w (3 + p))) := by
        unfold argWords
        apply list_eq_of_U (s := c.k.plen.toNat + 1) (cells := c.pool)
        · rw [tailW_length, hlen]
        · intro k t hk
          have := hwords (k + 1) t (by rw [nodeW_getElem?_succ]; exact hk)
          rw [show c.k.plen.toNat + (k + 1) = c.k.plen.toNat + 1 + k by omega] at this
          exact this
        · intro k hk
          have := hW.args k (by rw [ldLen_nvar hv]; exact hk)
          simp only [ldArg, ld_if_neg hv, h8, ↓reduceIte] at this
          exact this
        · rw [tailW_of_leaf (off' := fun _ => 0) (by rw [hopv]; rfl)]; exact hfit.tail
        · intro k _; exact hw _
      have := decodeNode_hdrW_bvVal hfit hty hop (offs st.pool) d
      rw [htail, hh] at this
      show decodeNode d (w (3 + p) % 256) (w (3 + p) / 256 % 256) (w (3 + p) / 65536) _ = _
      rw [this]
      rcases n with ⟨op, args⟩
      simp only at hnargs
      rw [hnargs]
    · rw [ld_if_neg h8]
      by_cases h9 : hdrCode (w (3 + p)) = 0x09
      · -- a boolean literal: no words after the header
        have hop : opC n.op = 0x09 := by rw [hcode]; exact h9
        obtain ⟨b, hopb⟩ := opC_boolVal_iff.mp hop
        have hnargs := leaf_args_of_pushNode hpush (by rw [hopb]; rfl)
        have hvl : hdrVlen (w (3 + p)) = 0 := by
          rw [← hlen]; unfold tailLen; rw [hopb]
        rw [e1, e2, decodeNode_hdrW_boolVal hfit hop]
        simp only [hvl, argWords, List.range_zero, List.map_nil, mapOpt]
        rcases n with ⟨op, args⟩
        simp only at hnargs
        rw [hnargs]
      · -- an inner node: the arguments are the ids loaded at the argument positions
        have hnl : ¬ IsLeaf n.op := not_leaf_of_code (by rw [hcode]; omega)
          (by rw [hcode]; omega) (by rw [hcode]; exact h8) (by rw [hcode]; exact h9)
        rw [e1, e2, decodeNode_hdrW_inner hfit hnl]
        have hsz : n.args.size = hdrVlen (w (3 + p)) := by rw [← tailLen_of_not_leaf hnl, hlen]
        have hmap : mapOpt (fun a => if a < p then pm a else none)
            (argWords w p (hdrVlen (w (3 + p)))) = some n.args.toList := by
          apply mapOpt_eq_some_of
          · simp [argWords_length, hsz]
          · intro k hk hk'
            have hk1 : k < hdrVlen (w (3 + p)) := by simpa [argWords_length] using hk
            have hk2 : k < n.args.size := by simpa using hk'
            obtain ⟨hlt, i, hi, hilt⟩ := hW.refs hv h8 k hk1
            have hak : (argWords w p (hdrVlen (w (3 + p))))[k] = w (4 + p + k) := by
              simp [argWords]
            rw [hak, ld_if_pos hlt, hi]
            have hu1 := hwords (k + 1) (offs st.pool n.args[k])
              (by rw [nodeW_getElem?_succ]; exact tailW_getElem?_of_not_leaf hnl hk2)
            rw [show c.k.plen.toNat + (k + 1) = c.k.plen.toNat + 1 + k by omega] at hu1
            have hu2 := hW.args k (by rw [ldLen_nvar hv]; exact hk1)
            simp only [ldArg, ld_if_neg hv, h8, ↓reduceIte, hi] at hu2
            have ha : n.args[k] < st.pool.size := hargs _ (by simp)
            have e := U_inj hu1 hu2 (hoff _ ha) (hoff _ hilt)
            have := offs_inj (Nat.le_of_lt ha) (Nat.le_of_lt hilt) e
            simp [this]
        simp only [hmap]

end Vbcf.Proof
