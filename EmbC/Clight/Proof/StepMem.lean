import EmbC.Clight.Proof.StepCont

/-!
# Simulation of memory-writing statements
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight


theorem storeField_rel {P : Prog} {ge : CC.CGenv} {ctx : LCtx} {m : Mem} {j : MemoryInjection}
    {cm : CC.Mem} (hx : XCtx P ge ctx m j cm) {b : Nat} {blk : Block} {s : String}
    {d : StructDef} {f : String} {i : Nat} {t : Ty} {v : Val} {w : CC.Val}
    (hblk : m.block? b = some blk) (he : blk.elem = .struct s) (hd : P.findStruct s = some d)
    (hf : d.field? f = some (i, t)) (hi : i < blk.cells.size) (hty : ValTy m v t)
    (hv : valRel P m j v w) (hrep : Representable P (m.setCell b i v)) :
    ∃ co off cm', (compositeEnv P).get (CC.identOfString s) = some co ∧
      CC.fieldOffset (compositeEnv P) (CC.identOfString f) co.co_members = .OK (off, .Full) ∧
      0 ≤ off ∧ off ≤ CC.Integers.Ptrofs.max_unsigned ∧ t.isStruct = false ∧
      CC.Mem.store (chunkOf t) cm (j.block b) off w = some cm' ∧
      memoryRel P j (m.setCell b i v) cm' ∧ ConstRel P ge j (m.setCell b i v) cm' := by
  obtain ⟨v0, hv0⟩ : ∃ v0, blk.cells[i]? = some v0 := ⟨_, Array.getElem?_eq_getElem hi⟩
  obtain ⟨co, off, hco, hoff, h0, hle, hmax, hts, hfi, ⟨chunk, w0, ha, hl, _⟩, -⟩ :=
    struct_field_info hx hblk he hd hf hv0
  have hck := chunk_eq_of_accessMode hts ha; subst hck
  obtain ⟨hvalid, hstride, hperm, -⟩ := hx.mem.2.2.1 b blk hblk
  obtain ⟨cm', hst⟩ := store_of_load hl hperm h0 hle w
  have hb : b < m.blocks.size := block?_lt hblk
  have hs := (setCell_size m b i v).symm
  have hoffmax : off ≤ CC.Integers.Ptrofs.max_unsigned :=
    Int.le_trans (Int.le_add_of_nonneg_right (Int.le_of_lt (sizeChunk_chunkOf_pos _)))
      (Int.le_trans hle hmax)
  refine ⟨co, off, cm', hco, hoff, h0, hoffmax, hts, hst, memoryRel_setCell hx.mem hblk hrep hst ?_,
    constRel_size (Nat.le_of_eq hs.symm) (frame_store hb hst hx.const)⟩
  obtain ⟨d', co', e1, e2, e3, e4, e5⟩ := memRel_struct hx.mem hblk he
  rw [hd] at e1; cases e1
  rw [hco] at e2; cases e2
  have hdm := (findStruct_mem hd).1
  refine blockRel_intro (by rw [store_validBlock hst]; exact hvalid) hstride ?_ ?_ ?_
  · have : blockByteSize P ⟨blk.elem, blk.cells.setIfInBounds i v⟩ = blockByteSize P blk := by
      simp [blockByteSize]
    rw [this]; exact CC.Mem.rangePerm_store hst _ _ _ _ _ hperm
  · intro hns; simp only [he, Ty.isStruct] at hns; cases hns
  · intro s' he'
    simp only [he] at he'; cases he'
    refine ⟨d, co, hd, hco, e3, e4, fun i' f' t' v' hf' hv' => ?_⟩
    simp only [Array.getElem?_setIfInBounds] at hv'
    by_cases hii : i = i'
    · subst hii
      simp only [hi, ite_true, Option.some.injEq] at hv'
      subst hv'
      rw [hfi] at hf'; cases hf'
      refine ⟨off, hoff, chunkOf t, w, ha, ?_, valRel_size hs hv⟩
      rw [CC.Mem.load_store_same hst, loadResult_rel hv hty]
    · simp only [hii, ite_false] at hv'
      obtain ⟨off', hoff', hcr⟩ := e5 i' f' t' v' hf' hv'
      refine ⟨off', hoff', cellRel_store_other hs hst ?_
        (hx.scal d hdm _ (List.mem_of_getElem? hf')) hcr⟩
      right
      have hsc := hx.scal d hdm
      have hnd := hx.ids d hdm
      have ea := hoff; have eb := hoff'
      unfold CC.fieldOffset at ea eb
      rw [e4, members_eq] at ea eb
      rcases Nat.lt_or_gt_of_ne hii with h | h
      · exact .inr (field_disj _ d.fields 0 i i' f f' t t' off off' _ _ hsc hnd hfi hf' h ea eb)
      · exact .inl (field_disj _ d.fields 0 i' i f' f t' t off' off _ _ hsc hnd hf' hfi h eb ea)

section Mem

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont} {d : Nat} {σ σ' : LSt}
  {s' : CC.Stmt}

theorem exec_store (hs : SCtx P cp) {p i e : EmbC.Expr}
    (had : AdmFrom P (.exec (.store p i e) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.store p i e) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.store p i e) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.store p i e) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @store _ _ _ _ _ rp σp ty ri σi re _ hlp hpt hns hli hint hle hacc =>
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    by_cases hok : ¬ ∃ b off vi v index mem, evalE P env st.mem p = some (.ptr b off) ∧
        evalE P env st.mem i = some vi ∧ evalE P env st.mem e = some v ∧ vi.toIdx = some index ∧
        st.mem.storeArr b (off + index) v = some mem
    · have hn : Semantics.next P (.exec (.store p i e) env st k) = none := by
        simp only [Semantics.next, Semantics.nextCore]
        split
        · rename_i b off vi v hp hi he
          split
          · rfl
          · rename_i index hidx
            split
            · rfl
            · exact absurd ⟨_, _, _, _, _, _, hp, hi, he, hidx, ‹_›⟩ hok
        · rfl
      exact (step_none hn hstep).elim
    obtain ⟨b, off, vi, v, index, mem, hvp, hvi, hve, hidx, hst⟩ := Classical.not_not.mp hok
    have hn : Semantics.next P (.exec (.store p i e) env st k) =
        some (.silent (.exec .skip env { st with mem } k)) := by
      simp [Semantics.next, Semantics.nextCore, hvp, hvi, hve, hidx, hst]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    have sp := LE_static hlp
    have si := LE_static hli
    have se := LE_static hle
    simp only [capState_next] at si se
    obtain ⟨tya, -, wa, rela, runa⟩ := expr_sim hx hfits.2 hlp le _ henv hvp
    obtain ⟨leA, pA, fA, eA⟩ := runa.capture sp.1
    obtain ⟨tyb, -, wb, relb, runb⟩ := expr_sim hx hfits.2 hli leA _ (henv.frame hc fA) hvi
    rw [capState_next] at runb
    obtain ⟨leB, pB, fB, eB⟩ := runb.capture si.1
    obtain ⟨tye, -, w, hw, le1, pE, fE, eE⟩ :=
      expr_sim hx hfits.2 hle leB v ((henv.frame hc fA).frame hc fB) hve
    rw [capState_next] at fE eE
    rw [hpt] at tya
    obtain ⟨hel, hb, hlt, rfl⟩ := ptr_operand tya rela
    obtain ⟨k', hk', hidxw⟩ := idxW_of relb tyb hint
    rw [hidx] at hk'; cases hk'
    obtain ⟨blk, hblk, hns', hhas, hlt', rfl⟩ := storeArr_eq hst
    have hte := hel blk hblk; subst hte
    have hstr := stride_eq hx.mem hblk
    obtain ⟨hnn, hmax⟩ := arr_offset_fits hx.fits hblk hns' (Nat.le_of_lt hlt')
    have hfits' := (had.silent hn).here
    obtain ⟨cm', hstore, hmem', hconst'⟩ := storeArr_rel hx.mem hx.const hblk hns' hlt'
      (ValTy.of_hasTy hhas) hw hfits'.1.1
    have hu : v ≠ .undef := by
      intro h; subst h
      have : ∀ t, st.mem.hasTy .undef t = false := fun t => by cases t <;> rfl
      rw [this] at hhas; cases hhas
    have hcast := cast_accepts hw tye hacc hu cm
    have hgrow := MemGrow.setCell st.mem b (off + index) v
    have fAll : Frame (fnContext P fn) σ.next σ'.next le le1 :=
      Frame.trans (Frame.trans fA fB (Nat.le_succ_of_le sp.1) (by omega)) fE
        (by omega) se.1
    refine goal_plus (had.silent hn) (hg.update hgrow (Extends.refl _ _) hmem' hconst')
      (match_normal hfn (hk.mono hgrow (Extends.refl _ _))
        ((henv.frame hc fAll).mono hgrow (Extends.refl _ _))) ?_
    refine tplus_of_star_plus (tstar_trans0 (pA.seq_star K)
      (tstar_trans0 (pB.seq_star K) (pE.seq_star K))) (tplus_one ?_)
    have ep := eA le1 (Agree.frame_left hc (Frame.trans fB fE (by omega) se.1) (Nat.le_refl _))
    have ei := eB le1 (Agree.frame_left hc fE (Nat.le_refl _))
    have hadd := ptr_add_eval hx.cenv ep ei (by show CC.typeof rp.ex = _; rw [sp.2, hpt]; rfl)
      (by show IdxW wb (CC.typeof ri.ex) index; rw [si.2]; exact hidxw) hstr
    have hoff : (((off + index) * j.stride b : Nat) : CC.Z) =
        ((off + index : Nat) : CC.Z) * byteSize P blk.elem := by
      rw [Int.natCast_mul, hstr]
    have hun := ptrofs_unsigned_repr' (Int.mul_nonneg (Int.natCast_nonneg _) hnn) hmax
    rw [← hoff] at hun
    rw [type_ptr]
    rw [← se.2] at hcast
    simp only [CC.doStep, CC.doEvalLvalue, hadd, eE le1 (Agree.refl _ _ _)]
    simp only [CC.typeof] at hcast ⊢
    simp only [hcast, CC.doAssignLoc, accessMode_type hns', CC.Mem.storev, hun]
    rw [hoff, hstore]

end Mem

end EmbC.Clight.Proof

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

section Mem2

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont} {d : Nat} {σ σ' : LSt}
  {s' : CC.Stmt}

theorem exec_setField (hs : SCtx P cp) {p : EmbC.Expr} {f : String} {e : EmbC.Expr}
    (had : AdmFrom P (.exec (.setField p f e) env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.setField p f e) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.setField p f e) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.setField p f e) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @setField _ _ _ _ _ rp σp sn ty re _ hlp hpt hft hle hacc =>
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    by_cases hok : ¬ ∃ b v mem, evalE P env st.mem p = some (.ptr b 0) ∧
        evalE P env st.mem e = some v ∧ st.mem.storeField P b f v = some mem
    · have hn : Semantics.next P (.exec (.setField p f e) env st k) = none := by
        simp only [Semantics.next, Semantics.nextCore]
        split
        · rename_i b off v hp he
          split
          · rename_i h0
            subst h0
            split
            · rfl
            · exact absurd ⟨_, _, _, hp, he, ‹_›⟩ hok
          · rfl
        · rfl
      exact (step_none hn hstep).elim
    obtain ⟨b, v, mem, hvp, hve, hst⟩ := Classical.not_not.mp hok
    have hn : Semantics.next P (.exec (.setField p f e) env st k) =
        some (.silent (.exec .skip env { st with mem } k)) := by
      simp [Semantics.next, Semantics.nextCore, hvp, hve, hst]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    have sp := LE_static hlp
    have se := LE_static hle
    simp only [capState_next] at se
    obtain ⟨tya, -, wa, rela, runa⟩ := expr_sim hx hfits.2 hlp le _ henv hvp
    obtain ⟨leA, pA, fA, eA⟩ := runa.capture sp.1
    obtain ⟨tye, -, w, hw, le1, pE, fE, eE⟩ :=
      expr_sim hx hfits.2 hle leA v (henv.frame hc fA) hve
    rw [capState_next] at fE eE
    rw [hpt] at tya
    obtain ⟨hel, hb, -, rfl⟩ := ptr_operand tya rela
    obtain ⟨blk, i, t', hslot, hhas, hlt', rfl⟩ := storeField_eq hst
    obtain ⟨s'', dd, hblk, he, hd, hf⟩ := fieldSlot_inv hslot
    have := hel blk hblk; rw [he] at this; cases this
    have htt : t' = ty := by
      rw [hpt] at hft
      simp only [fieldTy, hx.prog, hd, hf, Option.map_some, Option.some.injEq] at hft
      exact hft
    subst htt
    have hfits' := (had.silent hn).here
    obtain ⟨co, off, cm', hco, hoff, h0, hmax, hts, hstore, hmem', hconst'⟩ :=
      storeField_rel hx hblk he hd hf hlt' (ValTy.of_hasTy hhas) hw hfits'.1.1
    have hu : v ≠ .undef := by
      intro h; subst h
      have : ∀ t, st.mem.hasTy .undef t = false := fun t => by cases t <;> rfl
      rw [this] at hhas; cases hhas
    have hcast := cast_accepts hw tye hacc hu cm
    have hgrow := MemGrow.setCell st.mem b i v
    have fAll : Frame (fnContext P fn) σ.next σ'.next le le1 :=
      Frame.trans fA fE (Nat.le_succ_of_le sp.1) se.1
    refine goal_plus (had.silent hn) (hg.update hgrow (Extends.refl _ _) hmem' hconst')
      (match_normal hfn (hk.mono hgrow (Extends.refl _ _))
        ((henv.frame hc fAll).mono hgrow (Extends.refl _ _))) ?_
    refine tplus_of_star_plus (tstar_trans0 (pA.seq_star K) (pE.seq_star K)) (tplus_one ?_)
    have ep := eA le1 (Agree.frame_left hc fE (Nat.le_refl _))
    have ep' : CC.doEvalExpr cp.globalenv CC.emptyEnv le1 cm (capExpr (fnContext P fn) σp rp).ex =
        some (.Vptr (j.block b) (CC.Integers.Ptrofs.repr 0)) := by rw [ep]; simp
    obtain ⟨e1, e2⟩ := field_lval hx.cenv ep' hco hoff
    rw [← se.2] at hcast
    simp only [CC.doStep, CC.doEvalLvalue, e1, e2, eE le1 (Agree.refl _ _ _)]
    simp only [CC.typeof] at hcast ⊢
    simp only [hcast, CC.doAssignLoc, accessMode_type hts, CC.Mem.storev,
      ptrofs_unsigned_repr' h0 hmax, hstore]

end Mem2

end EmbC.Clight.Proof
