import Bcf.State

/-!
# Verified canonicalisation of the input pool

The raw pool from the file may contain structurally identical nodes at
different indices (BCF compares expressions structurally).  We intern
every raw node through `pushNode`, in order, producing a canonical pool
in which structural equality is index equality, together with the map
from raw to canonical indices.  `eval_canon` proves the meaning of
every raw node is preserved.
-/

namespace Bcf

def remapArgs (remap : Array Nat) (args : Array Nat) : Option (Array Nat) :=
  (mapOpt (fun a => remap[a]?) args.toList).map List.toArray

def canonStep (raw : Pool) (acc : St × Array Nat) (i : Nat) : Option (St × Array Nat) :=
  match raw[i]? with
  | none => none
  | some n =>
    if n.args.all (· < i) then
      match remapArgs acc.2 n.args with
      | none => none
      | some args =>
        match pushNode acc.1 ⟨n.op, args⟩ with
        | none => none
        | some (st', r) => some (st', acc.2.push r)
    else none

def canonFrom (raw : Pool) : Nat → Nat → St × Array Nat → Option (St × Array Nat)
  | 0, _, acc => some acc
  | m + 1, k, acc =>
    match canonStep raw acc k with
    | none => none
    | some acc' => canonFrom raw m (k + 1) acc'

/-- Intern all nodes of `raw` into `st`. -/
def canonicalize (raw : Pool) (st : St) : Option (St × Array Nat) :=
  canonFrom raw raw.size 0 (st, #[])

/-! ## Invariant -/

def CanonInv (raw : Pool) (st : St) (remap : Array Nat) (k : Nat) : Prop :=
  remap.size = k ∧
  ∀ j n, j < k → raw[j]? = some n →
    (∀ a ∈ n.args, a < j) ∧
    ∃ r args, remap[j]? = some r ∧ remapArgs remap n.args = some args ∧ st.pool[r]? = some ⟨n.op, args⟩

theorem remapArgs_push {remap : Array Nat} {args : Array Nat} (r : Nat)
    (h : ∀ a ∈ args, a < remap.size) :
    remapArgs (remap.push r) args = remapArgs remap args := by
  unfold remapArgs
  congr 1
  apply mapOpt_congr
  intro a ha
  rw [Array.getElem?_push]
  have := h a (by simpa using ha)
  simp [Nat.ne_of_lt this]

theorem canonStep_inv {raw : Pool} {st st' : St} {remap remap' : Array Nat} {k : Nat}
    (hinv : CanonInv raw st remap k) (hok : TysOK st.pool st.tys)
    (h : canonStep raw (st, remap) k = some (st', remap')) :
    CanonInv raw st' remap' (k + 1) ∧ TysOK st'.pool st'.tys := by
  unfold canonStep at h
  split at h
  · simp at h
  · rename_i n hn
    split at h
    · rename_i hargs
      split at h
      · simp at h
      · rename_i args hra
        split at h
        · simp at h
        · rename_i st'' r hpush
          simp at h; obtain ⟨rfl, rfl⟩ := h
          simp only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] at hargs
          refine ⟨⟨by simp [hinv.1], ?_⟩, pushNode_tysOK hpush hok⟩
          intro j m hj hm
          rcases Nat.lt_or_ge j k with hjk | hjk
          · obtain ⟨h1, r', args', hr', hra', hp'⟩ := hinv.2 j m hjk hm
            refine ⟨h1, r', args', ?_, ?_, ?_⟩
            · rw [Array.getElem?_push]; simp [hinv.1, Nat.ne_of_lt hjk, hr']
            · rw [remapArgs_push r (fun a ha => by rw [hinv.1]; exact Nat.lt_trans (h1 a ha) hjk)]; exact hra'
            · rw [pushNode_prefix hpush r' ?_]; exact hp'
              rcases Nat.lt_or_ge r' st.pool.size with h' | h'
              · exact h'
              · rw [Array.getElem?_eq_none h'] at hp'; cases hp'
          · have hjk' : j = k := by omega
            subst hjk'
            rw [hn] at hm; simp at hm; subst hm
            refine ⟨hargs, r, args, ?_, ?_, pushNode_get hpush⟩
            · rw [Array.getElem?_push]; simp [hinv.1]
            · rw [remapArgs_push r (fun a ha => by rw [hinv.1]; exact hargs a ha)]; exact hra
    · simp at h

theorem canonFrom_inv {raw : Pool} :
    ∀ (m k : Nat) {st st' : St} {remap remap' : Array Nat},
    CanonInv raw st remap k → TysOK st.pool st.tys →
    canonFrom raw m k (st, remap) = some (st', remap') →
    CanonInv raw st' remap' (k + m) ∧ TysOK st'.pool st'.tys := by
  intro m
  induction m with
  | zero =>
    intro k st st' remap remap' hinv hok h
    simp [canonFrom] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨hinv, hok⟩
  | succ m ih =>
    intro k st st' remap remap' hinv hok h
    unfold canonFrom at h
    split at h
    · simp at h
    · rename_i acc' hstep
      obtain ⟨st1, remap1⟩ := acc'
      obtain ⟨hinv1, hok1⟩ := canonStep_inv hinv hok hstep
      have := ih (k + 1) hinv1 hok1 h
      rw [show k + 1 + m = k + (m + 1) by omega] at this
      exact this

theorem canonicalize_inv {raw : Pool} {st st' : St} {remap : Array Nat}
    (hok : TysOK st.pool st.tys) (h : canonicalize raw st = some (st', remap)) :
    CanonInv raw st' remap raw.size ∧ TysOK st'.pool st'.tys := by
  have := canonFrom_inv raw.size 0 (st := st) (remap := #[]) ⟨rfl, by intro j n hj; omega⟩ hok h
  simpa using this

/-! ## Meaning is preserved -/

theorem mapOpt_map_rel {f : α → Option β} {l : List α} {l' : List β}
    (hm : mapOpt f l = some l') (g : α → γ) (k : β → γ)
    (hrel : ∀ a ∈ l, ∀ b, f a = some b → g a = k b) : l.map g = l'.map k := by
  induction l generalizing l' with
  | nil => simp [mapOpt] at hm; subst hm; rfl
  | cons a rest ih =>
    simp only [mapOpt] at hm
    split at hm
    · rename_i b bs hb hrest
      simp at hm; subst hm
      simp only [List.map_cons]
      rw [hrel a (by simp) b hb, ih hrest (fun a ha => hrel a (by simp [ha]))]
    · simp at hm

theorem eval_canon {raw : Pool} {st : St} {remap : Array Nat}
    (hinv : CanonInv raw st remap raw.size) (hok : TysOK st.pool st.tys) (ρ : Assign) :
    ∀ j, j < raw.size → ∀ r, remap[j]? = some r → eval raw ρ j = eval st.pool ρ r := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj r hr
    obtain ⟨n, hn⟩ : ∃ n, raw[j]? = some n := by
      cases h : raw[j]? with
      | none => rw [Array.getElem?_eq_none_iff] at h; omega
      | some n => exact ⟨n, rfl⟩
    obtain ⟨hlt, r', args, hr', hra, hp⟩ := hinv.2 j n hj hn
    rw [hr] at hr'; simp at hr'; subst hr'
    rw [eval_unfold, hn]
    simp only
    rw [eval_node hok.wf ρ hp]
    simp only
    congr 1
    unfold remapArgs at hra
    simp only [Option.map_eq_some_iff] at hra
    obtain ⟨args', hmap, rfl⟩ := hra
    rw [show (List.toArray args').toList = args' from by simp]
    have hmap' : mapOpt (fun a => remap[a]?) n.args.toList = some args' := hmap
    have := mapOpt_map_rel hmap' (fun a => if a < j then eval raw ρ a else Val.bad) (eval st.pool ρ)
      (fun a ha b hb => by
        have hlt' := hlt a (by simpa using ha)
        simp only [hlt', ite_true]
        exact ih a hlt' (Nat.lt_trans hlt' hj) b hb)
    exact this

end Bcf
