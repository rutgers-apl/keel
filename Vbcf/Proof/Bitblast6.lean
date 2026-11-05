import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast5

/-!
# Vbcf proofs: the Bitblast family, part 6 — `bb_concat`, `bb_extract`, `bb_sext`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


theorem bb_flatten_drop {xss : List (List Nat)} {k : Nat} (hk : k < xss.length) :
    (xss.drop k).reverse.flatten = (xss.drop (k + 1)).reverse.flatten ++ xss[k] := by
  rw [List.drop_eq_getElem_cons hk, List.reverse_cons, List.flatten_append]; simp

/-- `while (cond) body` as the last statement, with an invariant that may mention the
environment on entry. -/
theorem WP.bb_loop_last {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {cond : Expr} {body : Stmt}
    (I : Env → Env → (KernelState P State) → Prop) (h0 : I env env s)
    (hstep : ∀ env' s', I env env' s' →
      match evalE P env' s'.mem cond with
      | some (.u32 v) => (v = 0 → Q .normal env' s') ∧ (v ≠ 0 → WP P body (LoopQ (I env) Q) env' s')
      | _ => False) :
    WP P (.while cond body) Q env s :=
  WP.aci_loop (I env) h0 hstep

/-! ## `bb_concat` -/

def BbConcatSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (aop : Op) (a b : Nat) (args bs : Array Nat) (xss : List (List Nat)),
    FnSpec (State := State) Vbcf.prog "bb_concat"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧
        st.pool[a]? = some ⟨aop, args⟩ ∧ st.lv a ∧ ¬ IsLeaf aop ∧ mapOpt (bitsOf st) args.toList = some xss ∧
        st.pool[b]? = some ⟨.bvFromBool, bs⟩∧ st.lv b )
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧ BbOK s (bs.toList = xss.reverse.flatten) r s')

theorem bb_concat_spec : BbConcatSpec (State := State) := by
  intro W sb X c0 c prems params st aop a b args bs xss
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbConcat) rfl
  rintro vs s ⟨rfl, h, hR, hn, hal, hl, hxss, hnb, hb⟩
  simp [bbConcat, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbConcat) rfl
  simp only [bbConcat, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hsz, hargs⟩ := hR.core.bb_args hn hl
  obtain ⟨hszb, hargsb⟩ := hR.core.bb_args hnb (by decide)
  have hxl := mapOpt_length hxss
  simp only [Array.length_toList] at hxl
  rule_assign [(hR.core.rdN hn hl).1, (hR.core.rdN hn hl).2.1]
  rule_assign [(hR.core.rdN hnb).1, (hR.core.rdN hnb).2.1]
  rule_assign
  apply WP.bb_loop (fun env0 => BbInvW s env0 "k" ["x", "nx", "j", "pos"] args.size
    (fun k ws => ∃ pos, ws[3]? = some (BitVec.ofNat 32 pos) ∧ pos ≤ bs.size ∧
      bs.toList.take pos = (xss.drop k).reverse.flatten))
  · refine ⟨rfl, args.size, [0#32, 0#32, 0#32, 0#32], rfl, by simp [bbSets, Env.set], Nat.le_refl _,
      0, rfl, by omega, ?_⟩
    rw [List.drop_of_length_le (by omega)]; simp
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, pos, hwp, hpos, htake⟩
  obtain ⟨w1, w2, w3, w4, rfl⟩ := len_shape 4 hws
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hwp
  subst hwp
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
  · subst hk0
    apply WP.rule_ret
    rule_simp
    refine ⟨rfl, fun he => ?_⟩
    have hpe : pos = bs.size := by
      by_cases e : pos = bs.size
      · exact e
      · simp [e] at he
    subst hpe
    rwa [show bs.size = bs.toList.length by simp, List.take_length] at htake
  rule_assign [bb_uv_sub (show k < 2 ^ 32 by omega) (show 1 ≤ k by omega)]
  have hk' : k - 1 < args.size := by omega
  obtain ⟨xa, hxa, hxk⟩ := bb_bits_at hxss hk'
  have hxkl := hargs (k - 1) hk'
  obtain ⟨hxsz, hxargs⟩ := hR.core.bb_args hxa (by decide)
  rule_assign [(hR.core.rdN hn hl).2.2 (k - 1) hk']
  rule_assign [(hR.core.rdN hxa).1, (hR.core.rdN hxa).2.1]
  rule_assign
  have hxk' : xss[k - 1] = xa.toList := by
    rw [List.getElem?_eq_getElem (by omega)] at hxk; simpa using hxk
  apply WP.bb_loop_last (fun env1 => BbInvW s' env1 "j" ["pos"] xa.size
    (fun j ws => ∃ pos, ws[0]? = some (BitVec.ofNat 32 pos) ∧ pos ≤ bs.size ∧
      bs.toList.take pos = (xss.drop k).reverse.flatten ++ xa.toList.take j))
  · exact ⟨rfl, 0, [BitVec.ofNat 32 pos], rfl, by simp [bbSets, Env.set], by omega, pos, rfl, hpos,
      by simpa using htake⟩
  rintro env s'' ⟨rfl, j, ws, hws, rfl, hj, pos', hwp, hpos', htake'⟩
  obtain ⟨w5, rfl⟩ := len_shape 1 hws
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hwp
  subst hwp
  simp only [bbSets, List.zip_cons_cons, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · simp only [LoopQ]
    refine ⟨rfl, k - 1, [BitVec.ofNat 32 (st.id args[k - 1]), BitVec.ofNat 32 xa.size,
      BitVec.ofNat 32 j, BitVec.ofNat 32 pos'], rfl, by simp [bbSets, Env.set], by omega, pos', rfl,
      hpos', ?_⟩
    rw [htake', bb_flatten_drop (xss := xss) (k := k - 1) (by omega), show k - 1 + 1 = k by omega,
      hxk', List.take_of_length_le (l := xa.toList) (by simp; omega)]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun hpl => ?_⟩
  have hbp := hargsb pos' hpl
  have hxj := hxargs j hlt
  apply WP.guard_lit
  rule_simp [(hR.core.rdN hnb).2.2 pos' hpl, (hR.core.rdN hxa).2.2 j hlt]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun he => ?_⟩
  rule_assign
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, j + 1, [BitVec.ofNat 32 (pos' + 1)], rfl, by simp [bbSets, Env.set], by omega,
    pos' + 1, rfl, by omega, ?_⟩
  rw [List.take_succ_eq_append_getElem (by simpa using hpl), htake',
    List.take_succ_eq_append_getElem (by simpa using hlt), List.append_assoc]
  simp [he]

/-! ## `bb_extract` -/

def BbExtractSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (hi lo x b : Nat) (xs bs : Array Nat),
    FnSpec (State := State) Vbcf.prog "bb_extract"
      (fun vs s => vs = [.ptr sb 0, uv hi, uv lo, uv (st.id x), uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ hi < 256 ∧ lo < 256 ∧
        st.pool[x]? = some ⟨.bvFromBool, xs⟩ ∧ st.lv x ∧ st.pool[b]? = some ⟨.bvFromBool, bs⟩∧ st.lv b )
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (bs.toList = (xs.toList.drop lo).take (hi - lo + 1)) r s')

theorem bb_extract_spec : BbExtractSpec (State := State) := by
  intro W sb X c0 c prems params st hi lo x b xs bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbExtract) rfl
  rintro vs s ⟨rfl, h, hR, hhi, hlo, hnx, hxl, hnb, hb⟩
  simp [bbExtract, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbExtract) rfl
  simp only [bbExtract, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hszx, hargsx⟩ := hR.core.bb_args hnx (by decide)
  obtain ⟨hszb, hargsb⟩ := hR.core.bb_args hnb (by decide)
  have hoff := hR.core.off_lt hxl
  rule_assign [(hR.core.rdN hnx).1, (hR.core.rdN hnx).2.1]
  rule_assign [(hR.core.rdN hnb).1, (hR.core.rdN hnb).2.1]
  rule_assign
  apply WP.seq_mid_env (fun env0 env' s' => s' = s ∧ env' = env0.set "cnt" (uv (hi - lo + 1)))
  · apply WP.ite
    rule_simp
    refine ⟨fun hgt => ?_, fun hle => ?_⟩
    · apply WP.assign
      rule_simp [bb_uv_sub (show hi < 2 ^ 32 by omega) (show lo ≤ hi by omega), LoopQ]
    · apply WP.skip
      rule_simp [LoopQ, show hi - lo = 0 by omega]
  rintro env1 s1 ⟨rfl, rfl⟩
  apply WP.seq_mid_env (fun env0 env' s' => s' = s1 ∧ env' = env0.set "avail" (uv (xs.size - lo)))
  · apply WP.ite
    rule_simp
    refine ⟨fun hgt => ?_, fun hle => ?_⟩
    · apply WP.assign
      rule_simp [bb_uv_sub (show xs.size < 2 ^ 32 by omega) (show lo ≤ xs.size by omega), LoopQ]
    · apply WP.skip
      rule_simp [LoopQ, show xs.size - lo = 0 by omega]
  rintro env2 s2 ⟨rfl, rfl⟩
  apply WP.seq_mid_env (fun env0 env' s' => s' = s2 ∧
    env' = env0.set "cnt" (uv (min (hi - lo + 1) (xs.size - lo))))
  · apply WP.ite
    rule_simp
    refine ⟨fun hgt => ?_, fun hle => ?_⟩
    · apply WP.assign
      rule_simp [LoopQ, show min (hi - lo + 1) (xs.size - lo) = xs.size - lo by omega]
    · apply WP.skip
      rule_simp [LoopQ, show min (hi - lo + 1) (xs.size - lo) = hi - lo + 1 by omega]
  rintro env3 s3 ⟨rfl, rfl⟩
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hlen => ?_⟩
  have hTl : ((xs.toList.drop lo).take (hi - lo + 1)).length = bs.size := by simp; omega
  apply WP.bb_loop (fun env0 => BbInv s3 env0 "i" [] bs.size
    (fun i => bs.toList.drop i = ((xs.toList.drop lo).take (hi - lo + 1)).drop i →
      bs.toList = (xs.toList.drop lo).take (hi - lo + 1)))
  · exact ⟨rfl, 0, [], rfl, by simp [bbSets, Env.set], by omega, fun h => by simpa using h⟩
  rintro env s' ⟨rfl, i, ws, hws, rfl, hi', hres⟩
  obtain rfl := len_shape 0 hws
  simp only [bbSets, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    exact hres (by rw [List.drop_of_length_le (by simp; omega), List.drop_of_length_le (by omega)])
  have hli : lo + i < xs.size := by omega
  have hbi := hargsb i hlt
  have hxi := hargsx (lo + i) hli
  have e1 : (st.id x + 1 + lo + i) % 4294967296 = st.id x + 1 + lo + i := by omega
  have e2 : rd c.pool (st.id x + 1 + lo + i) = some (uv (st.id xs[lo + i])) := by
    rw [Nat.add_assoc (st.id x + 1)]; exact (hR.core.rdN hnx).2.2 (lo + i) hli
  apply WP.guard_lit
  rule_simp [(hR.core.rdN hnb).2.2 i hlt, e1, e2]
  refine ⟨fun _ => by simp [LoopQ, RetQ, BbOK.zero], fun he => ?_⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨rfl, i + 1, [], rfl, by simp [bbSets, Env.set], by omega, fun hd => hres ?_⟩
  refine bb_drop_eq_step (by simpa using hlt) (by omega) ?_ hd
  simp [he]

/-! ## `bb_sext` -/

def BbSextSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (x b e : Nat) (xs bs : Array Nat),
    FnSpec (State := State) Vbcf.prog "bb_sext"
      (fun vs s => vs = [.ptr sb 0, uv (st.id x), uv (st.id b), uv e] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ e < 256 ∧
        st.pool[x]? = some ⟨.bvFromBool, xs⟩ ∧ st.lv x ∧ st.pool[b]? = some ⟨.bvFromBool, bs⟩∧ st.lv b )
      (fun _ s rv s' => ∃ r, rv = some (.u32 r) ∧
        BbOK s (Bcf.bbSext xs.toList bs.toList e = true) r s')

theorem bb_sext_spec : BbSextSpec (State := State) := by
  intro W sb X c0 c prems params st x b e xs bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbSext) rfl
  rintro vs s ⟨rfl, h, hR, he, hnx, hxl, hnb, hb⟩
  simp [bbSext, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbSext) rfl
  simp only [bbSext, Stmt.block, initLocals, List.map, Ty.zero]
  obtain ⟨hszx, hargsx⟩ := hR.core.bb_args hnx (by decide)
  obtain ⟨hszb, hargsb⟩ := hR.core.bb_args hnb (by decide)
  have hoff := hR.core.off_lt hxl
  rule_assign [(hR.core.rdN hnx).1, (hR.core.rdN hnx).2.1]
  rule_assign [(hR.core.rdN hnb).1, (hR.core.rdN hnb).2.1]
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hx0 => ?_⟩
  have hx1 : 0 < xs.size := by
    rw [Nat.pos_iff_ne_zero]; intro e; exact hx0 (Array.size_eq_zero_iff.mp e)
  clear hx0
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp [RetQ, BbOK.zero], fun hlen => ?_⟩
  have hlast := hargsx (xs.size - 1) (by omega)
  have e3 : rd c.pool (st.id x + xs.size) = some (uv (st.id xs[xs.size - 1])) := by
    have := (hR.core.rdN hnx).2.2 (xs.size - 1) (by omega)
    rwa [show st.id x + 1 + (xs.size - 1) = st.id x + xs.size by omega] at this
  -- the target list
  have hT : ∀ (i : Nat) (hi : i < bs.size),
      ∃ hiT : i < (xs.toList ++ List.replicate e xs[xs.size - 1]).length,
        (xs.toList ++ List.replicate e xs[xs.size - 1])[i] =
          if hix : i < xs.size then xs[i] else xs[xs.size - 1] := by
    intro i hi
    refine ⟨by simp; omega, ?_⟩
    split
    · rename_i hix; rw [List.getElem_append_left (by simpa using hix)]; simp
    · rename_i hix; rw [List.getElem_append_right (by simp; omega)]; simp
  apply WP.bb_loop (fun env0 => BbInv s env0 "i" [] bs.size
    (fun i => bs.toList.drop i = (xs.toList ++ List.replicate e xs[xs.size - 1]).drop i →
      bs.toList = xs.toList ++ List.replicate e xs[xs.size - 1]))
  · exact ⟨rfl, 0, [], rfl, by simp [bbSets, Env.set], by omega, fun h => by simpa using h⟩
  rintro env s' ⟨rfl, i, ws, hws, rfl, hi', hres⟩
  obtain rfl := len_shape 0 hws
  simp only [bbSets, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · apply WP.rule_ret; rule_simp [BbOK]
    have hbT := hres (by rw [List.drop_of_length_le (by simp; omega),
      List.drop_of_length_le (by simp; omega)])
    have hgl : xs.toList.getLast? = some xs[xs.size - 1] := by
      rw [List.getLast?_eq_getElem?]; simp
    simp [Bcf.bbSext, hgl, hbT]
  have hbi := hargsb i hlt
  obtain ⟨hiT, hTi⟩ := hT i hlt
  apply WP.seq
  apply WP.ite
  by_cases hix : i < xs.size
  · have hxi := hargsx i hix
    rule_simp [hix]
    apply WP.ite
    rule_simp [(hR.core.rdN hnb).2.2 i hlt, (hR.core.rdN hnx).2.2 i hix]
    refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ, BbOK.zero], fun heq => ?_⟩
    apply WP.skip
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, i + 1, [], rfl, by simp [bbSets, Env.set], by omega, fun hd => hres ?_⟩
    refine bb_drop_eq_step (by simpa using hlt) hiT ?_ hd
    rw [hTi, dite_eq_left hix]; simpa using heq
  · rule_simp [hix]
    apply WP.ite
    rule_simp [(hR.core.rdN hnb).2.2 i hlt, e3]
    refine ⟨fun _ => by apply WP.ret; simp [evalE, LoopQ, RetQ, BbOK.zero], fun heq => ?_⟩
    apply WP.skip
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, i + 1, [], rfl, by simp [bbSets, Env.set], by omega, fun hd => hres ?_⟩
    refine bb_drop_eq_step (by simpa using hlt) hiT ?_ hd
    rw [hTi, dite_eq_right hix]; simpa using heq

end Vbcf.Proof
