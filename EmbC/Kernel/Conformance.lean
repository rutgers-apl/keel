import EmbC.Kernel

/-! Facts derived from the contracts embedded in `Oracle.step`. -/

namespace EmbC

namespace Oracle

/-- A certified invocation refuses exactly the calls outside its precondition. -/
theorem step_none_iff_not_defined {P : Prog} {State : Type} (o : Oracle P State)
    (call : Kernel.Call) (state : State) :
    (o.step call state).val = none ↔ ¬ Kernel.Defined P call := by
  have hc := (o.step call state).property
  rcases call with ⟨operation, args, before⟩
  dsimp only at hc
  split at hc
  all_goals subst_vars
  all_goals repeat' split at hc
  all_goals try simp_all [Kernel.Defined]
  all_goals try (intro hn; rw [hn] at hc; simp at hc)
  all_goals try omega
  all_goals repeat' split
  all_goals try simp_all
  all_goals try omega
  all_goals rcases ‹_ ∨ _› with h | h
  all_goals simp_all

/-- Every realizable reply is a response to a valid call. -/
theorem Returns.defined {P : Prog} {call : Kernel.Call} {reply : Kernel.Reply}
    (h : Returns P call reply) : Kernel.Defined P call := by
  obtain ⟨State, o, next, hr⟩ := h
  apply Classical.byContradiction
  intro hd
  have hn := (step_none_iff_not_defined o call o.state).mpr hd
  rw [hr] at hn
  contradiction

end Oracle

namespace Kernel

theorem run_none_iff_not_defined {State : Type} {P : Prog}
    (ext : Ext) (args : List Val) (st : KernelState P State) :
    run P ext args st = none ↔ ¬ Defined P ⟨ext, args, st.mem⟩ := by
  simpa only [run, Option.map_eq_none_iff] using
    Oracle.step_none_iff_not_defined st.oracle ⟨ext, args, st.mem⟩ st.oracle.state

end Kernel

namespace Ext

theorem run_none_iff_not_defined {State : Type} {P : Prog}
    (ext : Ext) (args : List Val) (st : KernelState P State) :
    Ext.run P ext args st = none ↔ ¬ Kernel.Defined P ⟨ext, args, st.mem⟩ :=
  Kernel.run_none_iff_not_defined ext args st

theorem run_defined {State : Type} {P : Prog} {ext : Ext} {args : List Val}
    {st : KernelState P State} (hd : Kernel.Defined P ⟨ext, args, st.mem⟩) :
    ∃ rv after, Ext.run P ext args st = some (rv, after) := by
  cases hr : Ext.run P ext args st with
  | none => exact ((run_none_iff_not_defined ext args st).mp hr hd).elim
  | some response => exact ⟨response.1, response.2, rfl⟩

theorem run_answer {State : Type} {P : Prog} {ext : Ext} {args : List Val}
    {st : KernelState P State} (hd : Kernel.Defined P ⟨ext, args, st.mem⟩) :
    Ext.run P ext args st = some (answer P ext args st) := by
  obtain ⟨rv, after, hr⟩ := run_defined hd
  simp [answer, hr]

theorem answer_spec {State : Type} {P : Prog} {ext : Ext} {args : List Val}
    {st : KernelState P State} (hd : Kernel.Defined P ⟨ext, args, st.mem⟩) :
    Oracle.Returns P ⟨ext, args, st.mem⟩
      ⟨(answer P ext args st).1, (answer P ext args st).2.mem⟩ :=
  run_spec (run_answer hd)

end Ext

end EmbC

namespace EmbC.Oracle.Returns

theorem kvcalloc {P : Prog} {before after : Mem} {t : Ty}
    {n : BitVec 64} {rv : Option Val}
    (h : Oracle.Returns P ⟨.kvcalloc t, [.u64 n], before⟩ ⟨rv, after⟩) :
    (rv = some .null ∧ after = before) ∨
    (rv = some (.ptr before.blocks.size 0) ∧
      after = (before.alloc t (Array.replicate n.toNat t.zero)).2) := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.kvcalloc t, [.u64 n], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  split at hc
  · simp at hc
  · rcases hc with ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩
    · exact .inl h
    · exact .inr h

theorem kzalloc {P : Prog} {before after : Mem} {name : String} {rv : Option Val}
    (h : Oracle.Returns P ⟨.kzalloc name, [], before⟩ ⟨rv, after⟩) :
    ∃ d, P.findStruct name = some d ∧
      ((rv = some .null ∧ after = before) ∨
       (rv = some (.ptr before.blocks.size 0) ∧
        after = (before.alloc (.struct name) d.zeroCells).2)) := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.kzalloc name, [], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  split at hc
  · simp at hc
  · rename_i d hd
    refine ⟨d, hd, ?_⟩
    rcases hc with ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩
    · exact .inl h
    · exact .inr h

theorem kvrealloc_null {P : Prog} {before after : Mem} {t : Ty}
    {n : BitVec 64} {rv : Option Val}
    (h : Oracle.Returns P ⟨.kvrealloc t, [.null, .u64 n], before⟩ ⟨rv, after⟩) :
    (rv = some .null ∧ after = before) ∨
    (rv = some (.ptr before.blocks.size 0) ∧
      after = (before.alloc t (Array.replicate n.toNat Val.undef)).2) := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.kvrealloc t, [.null, .u64 n], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  split at hc
  · simp at hc
  · rcases hc with ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩
    · exact .inl h
    · exact .inr h

theorem kvrealloc_ptr {P : Prog} {before after : Mem} {t : Ty}
    {n : BitVec 64} {rv : Option Val} {b off : Nat}
    (h : Oracle.Returns P ⟨.kvrealloc t, [.ptr b off, .u64 n], before⟩ ⟨rv, after⟩) :
    ∃ blk, before.block? b = some blk ∧
      ((rv = some .null ∧ after = before) ∨
       (rv = some (.ptr before.blocks.size 0) ∧
        after = ((before.free b).alloc t (reallocCells blk.cells n.toNat)).2)) := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.kvrealloc t, [.ptr b off, .u64 n], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  split at hc
  · simp at hc
  · split at hc
    · simp at hc
    · split at hc
      · simp at hc
      · rename_i blk hb
        split at hc
        · simp at hc
        · refine ⟨blk, hb, ?_⟩
          rcases hc with ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩
          · exact .inl h
          · exact .inr h

theorem kvfree_null {P : Prog} {before after : Mem} {rv : Option Val}
    (h : Oracle.Returns P ⟨.kvfree, [.null], before⟩ ⟨rv, after⟩) :
    rv = none ∧ after = before := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.kvfree, [.null], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  exact hc.choose_spec.1

theorem kvfree_ptr {P : Prog} {before after : Mem} {rv : Option Val} {b off : Nat}
    (h : Oracle.Returns P ⟨.kvfree, [.ptr b off], before⟩ ⟨rv, after⟩) :
    rv = none ∧ after = before.free b := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.kvfree, [.ptr b off], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  split at hc
  · simp at hc
  · split at hc
    · simp at hc
    · exact hc.choose_spec.1

theorem copyFromBpfptr {P : Prog} {before after : Mem} {rv : Option Val}
    {b off : Nat} {n : BitVec 64}
    (h : Oracle.Returns P ⟨.copyFromBpfptr, [.ptr b off, .uptr, .u64 n], before⟩ ⟨rv, after⟩) :
    (rv = some (.u32 1) ∧ after = before.fill b off (List.replicate n.toNat .undef)) ∨
    ∃ words : List (BitVec 32), words.length = n.toNat ∧ rv = some (.u32 0) ∧
      after = before.fill b off (words.map .u32) := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.copyFromBpfptr, [.ptr b off, .uptr, .u64 n], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  split at hc
  · simp at hc
  · split at hc
    · simp at hc
    · rcases hc with ⟨_, ⟨h, _⟩ | ⟨words, hn, h, _⟩⟩
      · exact .inl h
      · exact .inr ⟨words, hn, h⟩

theorem signalPending {P : Prog} {before after : Mem} {rv : Option Val}
    (h : Oracle.Returns P ⟨.signalPending, [], before⟩ ⟨rv, after⟩) :
    (rv = some (.u32 0) ∨ rv = some (.u32 1)) ∧ after = before := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.signalPending, [], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  rcases hc with ⟨_, ⟨⟨h, hm⟩, _⟩ | ⟨⟨h, hm⟩, _⟩⟩
  · exact ⟨.inl h, hm⟩
  · exact ⟨.inr h, hm⟩

theorem condResched {P : Prog} {before after : Mem} {rv : Option Val}
    (h : Oracle.Returns P ⟨.condResched, [], before⟩ ⟨rv, after⟩) :
    rv = none ∧ after = before := by
  rcases h with ⟨State, o, next, hr⟩
  have hc := (o.step ⟨.condResched, [], before⟩ o.state).property
  simp only [hr, Option.some.injEq, Prod.mk.injEq, Kernel.Reply.mk.injEq] at hc
  exact hc.choose_spec.1

end EmbC.Oracle.Returns

namespace EmbC
namespace Oracle

private def quietAnswer (P : Prog) (call : Kernel.Call) : Option (Kernel.Reply × Unit) :=
  let m := call.before
  match call.operation, call.args with
  | .kvcalloc t, [.u64 n] =>
    if n = 0 ∨ t.isStruct then none else some (⟨some .null, m⟩, ())
  | .kzalloc name, [] =>
    match P.findStruct name with
    | none => none
    | some _ => some (⟨some .null, m⟩, ())
  | .kvrealloc t, [pointer, .u64 n] =>
    if n = 0 ∨ t.isStruct then none else
    match pointer with
    | .null => some (⟨some .null, m⟩, ())
    | .ptr b off =>
      if off ≠ 0 then none else
      match m.block? b with
      | none => none
      | some block =>
        if block.elem ≠ t then none else some (⟨some .null, m⟩, ())
    | _ => none
  | .kvfree, [.null] => some (⟨none, m⟩, ())
  | .kvfree, [.ptr b off] =>
    if off ≠ 0 then none else
    match m.block? b with
    | none => none
    | some _ => some (⟨none, m.free b⟩, ())
  | .copyFromBpfptr, [.ptr b off, .uptr, .u64 n] =>
    match m.block? b with
    | none => none
    | some block =>
      if block.elem ≠ .u32 ∨ off + n.toNat > block.cells.size then none else
      some (⟨some (.u32 1), m.fill b off (List.replicate n.toNat .undef)⟩, ())
  | .signalPending, [] => some (⟨some (.u32 0), m⟩, ())
  | .condResched, [] => some (⟨none, m⟩, ())
  | _, _ => none

private def quiet (P : Prog) : Oracle P Unit where
  state := ()
  step call _ := ⟨quietAnswer P call, by
    rcases call with ⟨operation, args, before⟩
    dsimp only
    split
    all_goals repeat' split
    all_goals simp_all [quietAnswer]
  ⟩

/-- The intrinsic interface admits a certified responder for every program. -/
theorem exists_oracle (P : Prog) : Nonempty (Oracle P Unit) := ⟨quiet P⟩

/-- The existing field's certified result type, inferred without restating its contract. -/
abbrev Response {P : Prog} {State : Type} (o : Oracle P State)
    (call : Kernel.Call) : Type :=
  (fun {α : Type} (_ : α) => α) (o.step call o.state)

/-- Override one call with another certified response. Other calls use the
same certified transformer; no environment schedule is introduced. -/
noncomputable def withResponse {P : Prog} {State : Type} (o : Oracle P State)
    (call : Kernel.Call) (response : Response o call) : Oracle P State := by
  classical
  exact { o with step := fun call' state =>
    if h : call' = call then h ▸ response else o.step call' state }

/-- Every response inhabiting the intrinsic result type is publicly realizable. -/
theorem Returns.of_response {P : Prog} {State : Type} {o : Oracle P State}
    {call : Kernel.Call} {reply : Kernel.Reply} {next : State}
    (response : Response o call) (hr : response.val = some (reply, next)) :
    Returns P call reply := by
  exact ⟨State, o.withResponse call response, next, by simp [withResponse, hr]⟩

end Oracle

namespace Kernel

theorem Defined.exists_reply {P : Prog} {call : Call} (hd : Defined P call) :
    ∃ reply, Oracle.Returns P call reply := by
  obtain ⟨o⟩ := Oracle.exists_oracle P
  cases hr : (o.step call o.state).val with
  | none => exact ((Oracle.step_none_iff_not_defined o call o.state).mp hr hd).elim
  | some response =>
    exact ⟨response.1, Unit, o, response.2, hr⟩

end Kernel
end EmbC
