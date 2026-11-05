import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.LoadSpec2

/-!
# Vbcf proofs: the one-pass loader — the Lean passes, one by one

From a successful incremental run `specN w st1 D = some T` (with
`posOfW w D = ne`), each pass of the Lean pipeline succeeds with the
corresponding component of `T`: `decodeExprs` gives `T.raw`, `densify` gives
`T.dense`, `canonicalize` gives `(T.st, T.remap)`, and `positionMap` is
`idxOf w D`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-! ## `decodeExprs` -/

theorem LoadSpec.u32At_word (ws : Array (BitVec 32)) (off i : Nat) (ho : off = 4 * i) (hi : i < ws.size) :
    u32At (wordsToBytes ws) off = wordFn ws i := by
  subst ho; exact u32At_wordFn ws i hi

theorem nodeWordsAt_words (ws : Array (BitVec 32)) (p v : Nat) (h : 4 + p + v ≤ ws.size) :
    nodeWordsAt (wordsToBytes ws) (12 + 4 * p) v = (argWords (wordFn ws) p v).toArray := by
  unfold nodeWordsAt argWords
  congr 1
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  exact LoadSpec.u32At_word ws _ (4 + p + k) (by omega) (by omega)

theorem LoadSpec.hdr_fields (h : Nat) (hh : h < 2 ^ 32) :
    h &&& 0xff = hdrCode h ∧ (h >>> 8) &&& 0xff = hdrVlen h ∧ (h >>> 16) &&& 0xffff = hdrParams h := by
  refine ⟨LoadSpec.and_ff h, ?_, ?_⟩
  · rw [LoadSpec.and_ff, LoadSpec.shr8]; rfl
  · rw [LoadSpec.and_ffff, LoadSpec.shr16]; unfold hdrParams; omega

theorem decodeExprsGo_step (ws : Array (BitVec 32)) (ne fuel p : Nat) (pool : Pool) (n : Node)
    (hb : p + 1 + hdrVlen (wordFn ws (3 + p)) ≤ ne) (hsz : 3 + ne ≤ ws.size)
    (hn : decodeNode p (hdrCode (wordFn ws (3 + p))) (hdrVlen (wordFn ws (3 + p)))
      (hdrParams (wordFn ws (3 + p)))
      (argWords (wordFn ws) p (hdrVlen (wordFn ws (3 + p)))).toArray = some n) :
    decodeExprsGo (wordsToBytes ws) (12 + 4 * ne) (fuel + 1) (12 + 4 * p) p pool =
      decodeExprsGo (wordsToBytes ws) (12 + 4 * ne) fuel
        (12 + 4 * (p + 1 + hdrVlen (wordFn ws (3 + p)))) (p + 1 + hdrVlen (wordFn ws (3 + p)))
        (pool.push n) := by
  have hw : u32At (wordsToBytes ws) (12 + 4 * p) = wordFn ws (3 + p) :=
    LoadSpec.u32At_word ws _ (3 + p) (by omega) (by omega)
  obtain ⟨f1, f2, f3⟩ := LoadSpec.hdr_fields _ (wordFn_lt ws (3 + p))
  rw [decodeExprsGo]
  simp only [hw, f1, f2, f3]
  rw [nodeWordsAt_words ws p _ (by omega)]
  have h1 : 12 + 4 * p < 12 + 4 * ne := by omega
  have h2 : 12 + 4 * p + 4 + 4 * hdrVlen (wordFn ws (3 + p)) ≤ 12 + 4 * ne := by omega
  simp only [h1, h2, ↓reduceIte, hn]
  congr 1
  omega

theorem decodeExprsGo_done (b : ByteArray) (stop fuel idx : Nat) (pool : Pool) :
    decodeExprsGo b stop fuel stop idx pool = some pool := by
  cases fuel <;> simp [decodeExprsGo]

theorem decodeExprsGo_spec {ws : Array (BitVec 32)} {st1 : St} {D ne : Nat} {T : Loaded}
    (hT : specN (wordFn ws) st1 D = some T) (hD : posOfW (wordFn ws) D = ne)
    (hsz : 3 + ne ≤ ws.size) :
    ∀ (m d fuel : Nat) (t : Loaded), m ≤ fuel → d + m = D → specN (wordFn ws) st1 d = some t →
      decodeExprsGo (wordsToBytes ws) (12 + 4 * ne) fuel (12 + 4 * posOfW (wordFn ws) d)
        (posOfW (wordFn ws) d) t.raw = some T.raw := by
  intro m
  induction m with
  | zero =>
    intro d fuel t _ hd ht
    have : d = D := by omega
    subst this
    rw [hT] at ht; simp only [Option.some.injEq] at ht; subst ht
    rw [hD]; exact decodeExprsGo_done _ _ _ _ _
  | succ m ih =>
    intro d fuel t hf hd ht
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨t0, t', rn, dargs, cargs, r, h0, h1, hrn, _, _, _, _, hraw, _⟩ :=
      specN_at hT (d := d) (by omega)
    rw [ht] at h0; simp only [Option.some.injEq] at h0; subst h0
    have hle : posOfW (wordFn ws) (d + 1) ≤ ne := hD ▸ posOfW_mono _ (by omega)
    rw [decodeExprsGo_step ws ne fuel _ _ rn hle hsz hrn]
    have := ih (d + 1) fuel t' (by omega) (by omega) h1
    rw [hraw] at this
    exact this

theorem decodeExprs_spec {ws : Array (BitVec 32)} {st1 : St} {D ne : Nat} {T : Loaded}
    (hT : specN (wordFn ws) st1 D = some T) (hD : posOfW (wordFn ws) D = ne)
    (hsz : 3 + ne ≤ ws.size) :
    decodeExprs (wordsToBytes ws) 12 ne = some T.raw := by
  unfold decodeExprs
  have hDle : D ≤ ne := hD ▸ le_posOfW _ D
  exact decodeExprsGo_spec hT hD hsz D 0 (ne + 1) _ (by omega) (by omega) rfl

/-! ## A loop rule for `for i in [0:n]` -/

theorem LoadSpec.list_forIn'_inv {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type}
    (Inv : Nat → β → Prop) :
    ∀ (l : List Nat) (f : (a : Nat) → a ∈ l → β → m (ForInStep β)) (d : Nat) (s : β),
      l = List.range' d l.length → Inv d s →
      (∀ i (h : i ∈ l) s, Inv i s → ∃ s', f i h s = pure (ForInStep.yield s') ∧ Inv (i + 1) s') →
      ∃ s', forIn' l s f = pure s' ∧ Inv (d + l.length) s' := by
  intro l
  induction l with
  | nil => intro f d s _ h _; exact ⟨s, by simp, h⟩
  | cons a as ih =>
    intro f d s hl hinv hstep
    simp only [List.length_cons, List.range'_succ, List.cons.injEq] at hl
    obtain ⟨rfl, has⟩ := hl
    obtain ⟨s1, hf, hinv1⟩ := hstep a (by simp) s hinv
    obtain ⟨s', hs', hinv'⟩ := ih (fun a' h b => f a' (List.mem_cons_of_mem _ h) b) (a + 1) s1 has hinv1
      (fun i h s hi => hstep i (List.mem_cons_of_mem _ h) s hi)
    refine ⟨s', ?_, ?_⟩
    · rw [List.forIn'_cons, hf]; simpa using hs'
    · rw [List.length_cons, show a + (as.length + 1) = a + 1 + as.length by omega]; exact hinv'

theorem LoadSpec.range_forIn'_inv {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type}
    (Inv : Nat → β → Prop) (n : Nat) (init : β)
    (f : (i : Nat) → i ∈ [:n] → β → m (ForInStep β))
    (h0 : Inv 0 init)
    (hstep : ∀ i (h : i ∈ [:n]) s, Inv i s → ∃ s', f i h s = pure (ForInStep.yield s') ∧ Inv (i + 1) s') :
    ∃ s, forIn' [:n] init f = pure s ∧ Inv n s := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  obtain ⟨s', hs', hinv'⟩ := LoadSpec.list_forIn'_inv Inv (List.range' 0 ([:n] : Std.Legacy.Range).size 1)
    (fun a h => f a (Std.Legacy.Range.mem_of_mem_range' h)) 0 init (by simp) h0
    (fun i h s hi => hstep i _ s hi)
  exact ⟨s', hs', by simpa [hsize] using hinv'⟩

theorem LoadSpec.range_forIn'_bind {m : Type → Type} [Monad m] [LawfulMonad m] {β γ : Type}
    (Inv : Nat → β → Prop) (n : Nat) (init : β)
    (f : (i : Nat) → i ∈ [:n] → β → m (ForInStep β)) (k : β → m γ) (R : m γ)
    (h0 : Inv 0 init)
    (hstep : ∀ i (h : i ∈ [:n]) s, Inv i s → ∃ s', f i h s = pure (ForInStep.yield s') ∧ Inv (i + 1) s')
    (hk : ∀ s, Inv n s → k s = R) :
    (forIn' [:n] init f >>= k) = R := by
  obtain ⟨s, hs, hinv⟩ := LoadSpec.range_forIn'_inv Inv n init f h0 hstep
  rw [hs, pure_bind]
  exact hk s hinv

/-! ## `densify` -/

/-- The inner loop of `densify`: renumber the arguments of one node. -/
theorem LoadSpec.densArgs_forIn (g : Nat → Option Nat) (F : Nat → Array Nat → Option (ForInStep (Array Nat)))
    (hF : ∀ a s, F a s = match g a with
      | some j => some (ForInStep.yield (s.push j))
      | none => none) :
    ∀ (l : List Nat) (acc : Array Nat) (js : List Nat), mapOpt g l = some js →
      forIn l acc F = some (acc ++ js.toArray) := by
  intro l
  induction l with
  | nil => intro acc js h; simp [mapOpt] at h; subst h; simp
  | cons a rest ih =>
    intro acc js h
    simp only [mapOpt] at h
    split at h
    · rename_i j js' hj hrest
      simp only [Option.some.injEq] at h; subst h
      rw [List.forIn_cons, hF, hj]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ih _ _ hrest]
      simp
    · simp at h

/-- The invariant of `densify`'s loop after `i` nodes. -/
def DensInv (w : Nat → Nat) (T : Loaded) (i : Nat) (s : Std.HashMap Nat Nat × Nat × Pool) : Prop :=
  (∀ a, s.1[a]? = idxOf w i a) ∧ s.2.1 = posOfW w i ∧ s.2.2.size = i ∧
    ∀ j, j < i → s.2.2[j]? = T.dense[j]?

theorem LoadSpec.insert_lookup {w : Nat → Nat} {i : Nat} {m : Std.HashMap Nat Nat}
    (hm : ∀ a, m[a]? = idxOf w i a) (a : Nat) :
    (m.insert (posOfW w i) i)[a]? = idxOf w (i + 1) a := by
  rw [Std.HashMap.getElem?_insert, hm]
  simp only [idxOf, beq_iff_eq]

theorem idxOf_self (w : Nat → Nat) (i : Nat) : idxOf w i (posOfW w i) = none := by
  cases h : idxOf w i (posOfW w i) with
  | none => rfl
  | some j =>
    obtain ⟨h1, h2⟩ := (idxOf_eq_some w _ _ _).1 h
    have := posOfW_inj w h2
    omega

theorem LoadSpec.array_eq_of_prefix {α : Type} {a b : Array α} (hs : a.size = b.size)
    (h : ∀ j, j < a.size → a[j]? = b[j]?) : a = b := by
  apply Array.ext_getElem?
  intro j
  rcases Nat.lt_or_ge j a.size with hj | hj
  · exact h j hj
  · rw [Array.getElem?_eq_none hj, Array.getElem?_eq_none (by omega)]

theorem densify_spec {w : Nat → Nat} {st1 : St} {D : Nat} {T : Loaded}
    (hT : specN w st1 D = some T) : densify T.raw = some T.dense := by
  obtain ⟨hrs, hds, _⟩ := specN_sizes hT
  unfold densify
  apply LoadSpec.range_forIn'_bind (DensInv w T)
  · exact ⟨fun a => by simp [idxOf], rfl, rfl, fun j hj => by omega⟩
  · intro i hi s hinv
    obtain ⟨hmap, hpos, hsz, hout⟩ := hinv
    have hiD : i < D := by rw [← hrs]; exact hi.2.1
    obtain ⟨t, t', rn, dargs, cargs, r, _, _, hrn, hvl, hd, _, _, _, _, _, hTr, hTd, _⟩ := specN_at hT hiD
    have hget : T.raw[i]'(Membership.get_elem_helper hi rfl) = rn := by
      have := hTr
      rw [Array.getElem?_eq_getElem (by omega)] at this
      simpa using this
    simp only [hget]
    refine ⟨(s.1.insert s.2.1 i, s.2.1 + 1 + vlenOf rn, s.2.2.push ⟨reidx rn.op i, dargs.toArray⟩), ?_, ?_⟩
    · rw [← Array.forIn_toList, LoadSpec.densArgs_forIn (idxOf w i) _ ?hF _ _ _ hd]
      · simp only [Array.empty_append, Option.bind_eq_bind, Option.bind_some]
        rfl
      · intro a acc
        rw [hpos, LoadSpec.insert_lookup hmap a]
        simp only [idxOf]
        by_cases h : posOfW w i = a
        · rw [← h, idxOf_self]
          simp
        · simp only [h, ↓reduceIte]
          cases hj : idxOf w i a with
          | none => rfl
          | some j =>
            have := ((idxOf_eq_some w _ _ _).1 hj).1
            simp [this]
    · refine ⟨fun a => hpos ▸ LoadSpec.insert_lookup hmap a, ?_, by simp [hsz], fun j hj => ?_⟩
      · show s.2.1 + 1 + vlenOf rn = posOfW w i + 1 + _
        rw [hpos, hvl]
      · show (s.2.2.push _)[j]? = _
        rw [Array.getElem?_push]
        split
        · rename_i h
          rw [h, hsz, hTd]
        · exact hout j (by omega)
  · intro s hinv
    obtain ⟨_, _, hsz, hout⟩ := hinv
    show some s.2.2 = some T.dense
    rw [LoadSpec.array_eq_of_prefix (by omega) (fun j hj => hout j (by omega))]
/-! ## `canonicalize` -/

theorem LoadSpec.mapOpt_forall {α β : Type} {f : α → Option β} {P : β → Prop} {l : List α} {l' : List β}
    (h : mapOpt f l = some l') (hP : ∀ a b, f a = some b → P b) : ∀ b ∈ l', P b := by
  induction l generalizing l' with
  | nil => simp [mapOpt] at h; subst h; simp
  | cons a rest ih =>
    simp only [mapOpt] at h
    split at h
    · rename_i b bs hb hrest
      simp only [Option.some.injEq] at h; subst h
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hP a _ hb
      · exact ih hrest x hx
    · simp at h

theorem canonFrom_spec {w : Nat → Nat} {st1 : St} {D : Nat} {T : Loaded}
    (hT : specN w st1 D = some T) :
    ∀ (m k : Nat) (t : Loaded), k + m = D → specN w st1 k = some t →
      canonFrom T.dense m k (t.st, t.remap) = some (T.st, T.remap) := by
  intro m
  induction m with
  | zero =>
    intro k t hk ht
    have : k = D := by omega
    subst this
    rw [hT] at ht; simp only [Option.some.injEq] at ht; subst ht
    rfl
  | succ m ih =>
    intro k t hk ht
    obtain ⟨t0, t', rn, dargs, cargs, r, h0, h1, _, _, hd, hc, hp, _, _, hrm, _, hTd, _⟩ :=
      specN_at hT (d := k) (by omega)
    rw [ht] at h0; simp only [Option.some.injEq] at h0; subst h0
    have hall : (dargs.toArray.all (· < k)) = true := by
      simp only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq, List.mem_toArray]
      exact LoadSpec.mapOpt_forall hd (fun a b hab => ((idxOf_eq_some w _ _ _).1 hab).1)
    have hstep : canonStep T.dense (t.st, t.remap) k = some (t'.st, t'.remap) := by
      unfold canonStep
      simp only [hTd, hall, ↓reduceIte, hc, hp, hrm]
    rw [canonFrom, hstep]
    exact ih (k + 1) t' (by omega) h1

theorem canonicalize_spec {w : Nat → Nat} {st1 : St} {D : Nat} {T : Loaded}
    (hT : specN w st1 D = some T) :
    canonicalize T.dense st1 = some (T.st, T.remap) := by
  unfold canonicalize
  rw [(specN_sizes hT).2.1]
  exact canonFrom_spec hT D 0 _ (by omega) rfl

/-! ## `positionMap` -/

theorem vlenOf_reidx (o : Op) (i : Nat) (args args' : Array Nat) (h : args'.size = args.size) :
    vlenOf ⟨reidx o i, args'⟩ = vlenOf ⟨o, args⟩ := by
  cases o <;> simp [vlenOf, reidx, h]

theorem positionMap_spec {w : Nat → Nat} {st1 : St} {D : Nat} {T : Loaded}
    (hT : specN w st1 D = some T) (a : Nat) : (positionMap T.dense)[a]? = idxOf w D a := by
  obtain ⟨_, hds, _⟩ := specN_sizes hT
  obtain ⟨s, hs, hinv⟩ := LoadSpec.range_forIn'_inv (m := Id)
    (fun i (s : Std.HashMap Nat Nat × Nat) => (∀ a, s.1[a]? = idxOf w i a) ∧ s.2 = posOfW w i)
    T.dense.size (∅, 0)
    (fun i h s => pure (ForInStep.yield (s.1.insert s.2 i,
      s.2 + 1 + vlenOf (T.dense[i]'(Membership.get_elem_helper h rfl)))))
    ⟨fun a => by simp [idxOf], rfl⟩
    (by
      intro i hi s hinv
      obtain ⟨hmap, hpos⟩ := hinv
      have hiD : i < D := by rw [← hds]; exact hi.2.1
      obtain ⟨t, t', rn, dargs, cargs, r, _, _, hrn, hvl, hd, _, _, _, _, _, _, hTd, _⟩ := specN_at hT hiD
      have hget : T.dense[i]'(Membership.get_elem_helper hi rfl) = ⟨reidx rn.op i, dargs.toArray⟩ := by
        have := hTd
        rw [Array.getElem?_eq_getElem (by omega)] at this
        simpa using this
      refine ⟨_, rfl, fun a => hpos ▸ LoadSpec.insert_lookup hmap a, ?_⟩
      show s.2 + 1 + vlenOf _ = posOfW w i + 1 + _
      rw [hget, vlenOf_reidx rn.op i rn.args _ (by simpa using mapOpt_length hd), hpos, hvl])
  have hpm : positionMap T.dense = s.1 := congrArg Prod.fst hs
  rw [hpm, hinv.1 a, hds]

end Vbcf.Proof
