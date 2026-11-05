import EmbC.Clight.Proof.LowerStmt

/-!
# Fresh temporaries are distinct from each other and from declared variables
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

/-- Freshness facts about a lowering context. -/
structure FreshOK (ctx : LCtx) : Prop where
  ne_decl : ∀ n (d : Var × Ty), d ∈ ctx.vars → freshId ctx n ≠ CC.identOfString d.1
  inj : ∀ n n', freshId ctx n = freshId ctx n' → n = n'

theorem foldl_max_ge : ∀ (l : List (Var × Ty)) (n : Nat),
    n ≤ l.foldl (fun n d => max n d.1.length) n ∧
      ∀ d ∈ l, d.1.length ≤ l.foldl (fun n d => max n d.1.length) n
  | [], n => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | d :: l, n => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max n d.1.length)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun d' hd' => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 d' hd'

theorem repr_ascii (n : Nat) : Ascii (Nat.repr n) := by
  intro c hc
  simp only [Nat.repr, String.toList_ofList] at hc
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  have h2 : c.val ≤ '9'.val := this.2
  have : c.toNat = c.val.toNat := rfl
  simp only [Char.toNat] at *
  have h3 : ('9' : Char).val.toNat = 57 := rfl
  have : c.val.toNat ≤ 57 := by
    rw [← h3]; exact (UInt32.le_iff_toNat_le).mp h2
  omega

theorem freshOK_fnContext {P : Prog} {fn : Fn}
    (hnames : ∀ d ∈ fn.params ++ fn.locals, Ascii d.1) : FreshOK (fnContext P fn) := by
  have hpfx : Ascii (LCtx.pfx (fnContext P fn)) := by
    intro c hc
    simp only [LCtx.pfx, fnContext, String.toList_ofList] at hc
    rw [List.eq_of_mem_replicate hc]; decide
  have hasc : ∀ n : Nat, Ascii (LCtx.pfx (fnContext P fn) ++ toString n) := by
    intro n c hc
    rw [String.toList_append] at hc
    rcases List.mem_append.mp hc with h | h
    · exact hpfx c h
    · exact repr_ascii n c h
  refine ⟨fun n d hd heq => ?_, fun n n' h => ?_⟩
  · have hd' : d ∈ fn.params ++ fn.locals := hd
    have := identOfString_inj_ascii (hasc n) (hnames d hd') heq
    have hl := congrArg String.length this
    rw [String.length_append] at hl
    have hp : (LCtx.pfx (fnContext P fn)).length =
        (fn.params ++ fn.locals).foldl (fun n d => max n d.1.length) 0 + 1 := by
      simp [LCtx.pfx, fnContext]
    have := (foldl_max_ge (fn.params ++ fn.locals) 0).2 d hd'
    omega
  · have := identOfString_inj_ascii (hasc n) (hasc n') h
    rw [String.append_right_inj] at this
    exact Nat.repr_inj.mp this

end EmbC.Clight.Proof
