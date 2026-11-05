import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval5

/-!
# Vbcf proofs: the Eval family, part 7 — the n-ary group of `cval` (the loop)
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- The loop of the n-ary group and what follows it. -/
def cvNl : Stmt := [cstms|
    while (i < n) {
      cw = cval(st, st->pool[id + 1 + i], depth - 1);
      if (cw == 0 || cw == NOID) { return cw; }
      x = st->val;
      if (code == BV_ADD) { acc = (acc + x) & m; }
      else if (code == BV_MUL) { acc = (acc * x) & m; }
      else if (code == BV_OR || code == BOOL_DISJ) { acc = acc | x; }
      else if (code == BV_AND || code == BOOL_CONJ) { acc = acc & x; }
      else if (code == BV_XOR || code == BOOL_XOR) { acc = acc ^ x; }
      else if (code == BV_CONCAT) { acc = (acc << (u64)cw) | x; }
      else { acc = acc | (x << (u64)i); }
      i = i + 1;
    }
    st->val = acc;
    return w;
]

/-- The accumulation step inside the loop. -/
def cvNc : Stmt := [cstm|
      if (code == BV_ADD) { acc = (acc + x) & m; }
      else if (code == BV_MUL) { acc = (acc * x) & m; }
      else if (code == BV_OR || code == BOOL_DISJ) { acc = acc | x; }
      else if (code == BV_AND || code == BOOL_CONJ) { acc = acc & x; }
      else if (code == BV_XOR || code == BOOL_XOR) { acc = acc ^ x; }
      else if (code == BV_CONCAT) { acc = (acc << (u64)cw) | x; }
      else { acc = acc | (x << (u64)i); }
]

/-- The loop, for any accumulator invariant `R j acc` (after `j` arguments). -/
theorem grpN_loop {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {op : Op} {args : Array Nat} {hdr code par lo hi w cw : BitVec 32}
    {x y z m sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some ⟨op, args⟩) (hl : ¬ IsLeaf op) (hQ : CvQ W sb c st i Q)
    (R : Nat → BitVec 64 → Prop) (h0 : R 0 acc)
    (STEP : ∀ (j : Nat) (acc : BitVec 64) (r : BitVec 32) (vl : BitVec 64) (v : Bcf.Val)
      (s' : (KernelState prog State)) (Q' : (Post prog State)) (hj : j < args.size),
      R j acc → memoVal st args[j] = some v → CvRep r vl v →
      (∀ acc', R (j + 1) acc' →
        Q' .normal (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code
          (BitVec.ofNat 32 args.size) par lo hi w r (BitVec.ofNat 32 j) vl y z m sbv acc') s') →
      WP Vbcf.prog cvNc Q'
        (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code (BitVec.ofNat 32 args.size) par lo
          hi w r (BitVec.ofNat 32 j) vl y z m sbv acc) s')
    (FIN : ∀ acc, R args.size acc → ∃ v, memoVal st i = some v ∧ CvRep w acc v) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvNl Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code (BitVec.ofNat 32 args.size) par lo hi
        w cw 0#32 x y z m sbv acc) s := by
  have hii := h_lv
  have hs := prog_ck
  obtain ⟨hrd, -, hargs⟩ := hc.rdN hn hl
  obtain ⟨args', he, hsz, -, hlt⟩ := hc.argsN hn rfl hl
  injection he with _ he2
  subst he2
  simp only [cvNl, Stmt.block]
  apply WP.loop_seq (fun env s => ∃ j cwv xv acc wk er vl, j ≤ args.size ∧
    Holds W s.mem sb (c.wev wk er vl) ∧
    env = cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code (BitVec.ofNat 32 args.size) par lo
      hi w cwv (BitVec.ofNat 32 j) xv y z m sbv acc ∧ R j acc)
  · exact ⟨0, cw, x, acc, c.k.work, c.k.err, c.k.val, Nat.zero_le _, by rw [wev_self]; exact h, rfl, h0⟩
  rintro env s ⟨j, cwv, xv, acc, wk, er, vl, hj, h, rfl, hR⟩
  cv_simp
  refine ⟨fun hjs => ?_, fun hjs => ?_⟩
  · have : j = args.size := by omega
    subst this
    exact WP.cv_finish (x' := acc) hQ h (by simp [Env.get]) (by simp [Env.get]) (by cv_simp)
      (fun _ _ => FIN acc hR)
  apply WP.cval_child (IH _ (cv_dec_lt hd)) h hc.wev (hlt j hjs) (by cv_simp [hargs j hjs])
  intro r wk' er' vl' s' h' hv
  simp only [wev_wev] at h'
  cv_simp
  apply WP.cw_guard (r := r) hQ.loopQ h' (by cv_simp)
  intro hr hr'
  replace h := h'
  apply WP.assign_seq; cv_simp
  obtain ⟨v, hmv, hvr⟩ := hv hr hr'
  apply WP.seq
  apply STEP j acc r vl' v s' _ hjs hR hmv hvr
  intro acc' hR'
  apply WP.assign_loop; cv_simp
  exact ⟨j + 1, hjs, ⟨_, _, _, h⟩, r, vl', acc', ⟨rfl, rfl, rfl, rfl⟩, hR'⟩

/-! ## Folds over the represented arguments -/

/-- The number a represented value stands for. -/
def cvNv : Bcf.Val → Nat
  | .bv _ x => x.toNat
  | .bool b => if b then 1 else 0
  | _ => 0

/-- The width of a bit-vector value. -/
def cvVw : Bcf.Val → Nat
  | .bv n _ => n
  | _ => 0

theorem CvRep.cvNv {r : BitVec 32} {vl : BitVec 64} {v : Bcf.Val} (h : CvRep r vl v) :
    vl.toNat = Vbcf.Proof.cvNv v := by
  rcases h.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
  · rw [h.2]; cases b <;> rfl
  · exact h.2.2.2

theorem cv_mapOpt_take_succ {f : Nat → Option Bcf.Val} {l : List Nat} {j : Nat} (hj : j < l.length)
    {vs : List Bcf.Val} (h : mapOpt f (l.take j) = some vs) {v : Bcf.Val} (hv : f l[j] = some v) :
    mapOpt f (l.take (j + 1)) = some (vs ++ [v]) := by
  induction l generalizing j vs with
  | nil => simp at hj
  | cons a rest ih =>
    cases j with
    | zero =>
      simp [mapOpt] at h ⊢; subst h; simp at hv; simp [hv]
    | succ j =>
      simp only [List.take_succ_cons, mapOpt] at h ⊢
      split at h
      · rename_i b bs hb hbs
        simp at h; subst h
        rw [hb, ih (by simpa using hj) hbs (by simpa using hv)]
        rfl
      · simp at h

theorem cv_mapOpt_take_all {f : Nat → Option Bcf.Val} {l : List Nat} {vs : List Bcf.Val}
    (h : mapOpt f (l.take l.length) = some vs) : mapOpt f l = some vs := by
  rwa [List.take_length] at h

theorem cv_bvs_eq_map {w : Nat} : ∀ {vs : List Bcf.Val} {xs : List (BitVec w)},
    Val.bvs w vs = some xs → vs = xs.map (Val.bv w)
  | [], xs, h => by simp [Val.bvs] at h; subst h; rfl
  | v :: rest, xs, h => by
    simp only [Val.bvs] at h
    split at h
    · rename_i x xs' hx hrest
      simp at h; subst h
      rw [Val.asBv_some_iff.mp hx, cv_bvs_eq_map hrest]; rfl
    · simp at h

theorem cv_bools_eq_map : ∀ {vs : List Bcf.Val} {bs : List Bool},
    Val.bools vs = some bs → vs = bs.map Val.bool
  | [], bs, h => by simp [Val.bools] at h; subst h; rfl
  | v :: rest, bs, h => by
    simp only [Val.bools] at h
    split at h
    · rename_i x xs' hx hrest
      simp at h; subst h
      rw [Val.asBool_some_iff.mp hx, cv_bools_eq_map hrest]; rfl
    · simp at h

/-- The end of an n-ary bit-vector operator: the fold of the words is the fold of the values. -/
theorem cv_fin_bvN {ρ : Assign} {op : Op} {w' : Nat} {F : List (BitVec w') → BitVec w'}
    (hop : Op.eval ρ op = bvN w' F) (G : List Nat → Nat)
    (hFG : ∀ xs : List (BitVec w'), (F xs).toNat = G (xs.map BitVec.toNat))
    {vs : List Bcf.Val} {t : Bcf.Ty} {w : BitVec 32} {acc : BitVec 64}
    (hty : (Op.eval ρ op vs).ty = some t) (hw : CvW t w) (hacc : acc.toNat = G (vs.map cvNv)) :
    CvRep w acc (Op.eval ρ op vs) := by
  rw [hop] at hty ⊢
  unfold bvN at hty ⊢
  split at hty
  · rename_i xs hxs
    by_cases hg : w' ≠ 0 ∧ 2 ≤ xs.length
    · rw [ite_eq_left hg] at hty ⊢
      simp at hty; subst hty
      apply CvRep.of_bv hw
      rw [hacc, hFG, cv_bvs_eq_map hxs, List.map_map]
      rfl
    · simp [hg] at hty
  · simp at hty

/-- The end of an n-ary boolean operator. -/
theorem cv_fin_boolN {ρ : Assign} {op : Op} {F : List Bool → Bool}
    (hop : Op.eval ρ op = boolN F) (G : List Nat → Nat)
    (hFG : ∀ bs : List Bool, G (bs.map (fun b => if b then 1 else 0)) = if F bs then 1 else 0)
    {vs : List Bcf.Val} {t : Bcf.Ty} {w : BitVec 32} {acc : BitVec 64}
    (hty : (Op.eval ρ op vs).ty = some t) (hw : CvW t w) (hacc : acc.toNat = G (vs.map cvNv)) :
    CvRep w acc (Op.eval ρ op vs) := by
  rw [hop] at hty ⊢
  unfold boolN at hty ⊢
  split at hty
  · rename_i bs hbs
    by_cases hg : 2 ≤ bs.length
    · rw [ite_eq_left hg] at hty ⊢
      simp at hty; subst hty
      apply CvRep.of_bool hw
      apply BitVec.eq_of_toNat_eq
      rw [hacc, cv_bools_eq_map hbs, List.map_map]
      have := hFG bs
      simp only [Function.comp_def, Vbcf.Proof.cvNv] at this ⊢
      rw [this]
      split <;> rfl
    · simp [hg] at hty
  · simp at hty

/-! ### The folds of the individual operators -/

theorem cv_foldl_add_toNat {w : Nat} : ∀ (xs : List (BitVec w)) (a : BitVec w),
    (xs.foldl (· + ·) a).toNat = (a.toNat + (xs.map BitVec.toNat).sum) % 2 ^ w
  | [], a => by simp [Nat.mod_eq_of_lt a.isLt]
  | x :: xs, a => by
    rw [List.foldl_cons, cv_foldl_add_toNat xs, BitVec.toNat_add]
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.mod_add_mod, Nat.add_assoc]

theorem cv_foldl_mul_toNat {w : Nat} : ∀ (xs : List (BitVec w)) (a : BitVec w),
    (xs.foldl (· * ·) a).toNat = (a.toNat * (xs.map BitVec.toNat).prod) % 2 ^ w
  | [], a => by simp [Nat.mod_eq_of_lt a.isLt]
  | x :: xs, a => by
    rw [List.foldl_cons, cv_foldl_mul_toNat xs, BitVec.toNat_mul]
    simp only [List.map_cons, List.prod_cons]
    rw [Nat.mod_mul_mod, Nat.mul_assoc]

theorem cv_foldl_or_toNat {w : Nat} : ∀ (xs : List (BitVec w)) (a : BitVec w),
    (xs.foldl (· ||| ·) a).toNat = (xs.map BitVec.toNat).foldl (· ||| ·) a.toNat
  | [], a => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, cv_foldl_or_toNat xs, BitVec.toNat_or]; rfl

theorem cv_foldl_and_toNat {w : Nat} : ∀ (xs : List (BitVec w)) (a : BitVec w),
    (xs.foldl (· &&& ·) a).toNat = (xs.map BitVec.toNat).foldl (· &&& ·) a.toNat
  | [], a => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, cv_foldl_and_toNat xs, BitVec.toNat_and]; rfl

theorem cv_foldl_xor_toNat {w : Nat} : ∀ (xs : List (BitVec w)) (a : BitVec w),
    (xs.foldl (· ^^^ ·) a).toNat = (xs.map BitVec.toNat).foldl (· ^^^ ·) a.toNat
  | [], a => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, cv_foldl_xor_toNat xs, BitVec.toNat_xor]; rfl

end Vbcf.Proof
