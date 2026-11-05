import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Alloc
import Vbcf.Proof.Spec

/-!
# Vbcf proofs: `push`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

theorem reallocCells_size (old : Array Val) (n : Nat) : (reallocCells old n).size = n := by
  simp [reallocCells]; omega

theorem reallocCells_get (old : Array Val) (n i : Nat) (hi : i < old.size) (hn : i < n) :
    (reallocCells old n)[i]? = old[i]? := by
  simp [reallocCells, Array.getElem?_append]
  have : i < min n old.size := by omega
  simp [this, hi]

/-- Where `push` stands once there is room for one more word. -/
def PushMid (W : World) (sb : Nat) (c : CMem) (v : BitVec 32) : (Post prog State) := fun o env' s' =>
  match o with
  | .normal =>
    (∃ ns nc, env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("v", .u32, .u32 v),
      ("ns", .ptr .u32, ns), ("ncap", .u32, nc)]) ∧
    ∃ c2 b, Holds W s'.mem sb c2 ∧ StkOK c2 ∧ StkFrame c c2 ∧ c2.k.stk = some (b, 0) ∧
      c2.k.sp = c.k.sp ∧ c.k.sp.toNat < c2.k.scap.toNat ∧
      (∀ i, i < c.k.sp.toNat → c2.stk[i]? = c.stk[i]?)
  | .ret rv =>
    ∃ c2, Holds W s'.mem sb c2 ∧ StkOK c2 ∧ StkFrame c c2 ∧
      (∀ i, i < c.k.sp.toNat → c2.stk[i]? = c.stk[i]?) ∧ rv = some (.u32 0#32) ∧
      c2.k.sp = c.k.sp
  | .brk => False

/-- `push(st, v)`: on success the stack has `v` on top and is otherwise as
before; on failure (out of work or memory) the stack below `sp` is as before. -/
theorem push_spec (W : World) (sb : Nat) (c : CMem) (v : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "push"
      (fun vs s => vs = [.ptr sb 0, .u32 v] ∧ Holds W s.mem sb c ∧ StkOK c)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧ StkOK c' ∧ StkFrame c c' ∧
        (∀ i, i < c.k.sp.toNat → c'.stk[i]? = c.stk[i]?) ∧
        ((rv = some (.u32 0) ∧ c'.k.sp = c.k.sp) ∨
         (rv = some (.u32 1) ∧ c'.k.sp = c.k.sp + 1#32 ∧
           c'.stk[c.k.sp.toNat]? = some (.u32 v)))) := by
  have hs := prog_ck
  apply FnSpec.intro (fn := push) rfl
  rintro vs st ⟨rfl, h, hok⟩
  refine ⟨[("st", .ptr (.struct "ck"), .ptr sb 0), ("v", .u32, .u32 v)], ?_, ?_⟩
  · simp [push, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [push, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]
  apply WP.seq
  apply WP.ite
  ck_simp
  constructor
  · intro hw
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro st h
    apply WP.ret
    ck_simp [retPost]
    exact ⟨_, h, ⟨hok.null, hok.size, hok.cap⟩, by constructor <;> rfl, fun _ _ => rfl, rfl⟩
  · intro hw
    apply WP.skip
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro st h
    apply WP.seq
    refine WP.mono (Q := PushMid W sb c v) ?_ ?_
    · -- make room
      apply WP.ite
      ck_simp
      constructor
      · intro hfull
        have hsc := hok.cap
        -- the allocation and installation, for any new capacity `nc`
        have key : ∀ nc : BitVec 32, nc ≠ 0#32 → c.k.scap.toNat < nc.toNat →
            nc.toNat ≤ 2 * maxPool →
            WP prog [cstms|
                if (st->work < ncap) { st->err = ERR_LIMIT; return 0; }
                st->work = st->work - ncap;
                if (st->mem < ncap) { st->err = ERR_LIMIT; return 0; }
                st->mem = st->mem - ncap;
                ns = kvrealloc(st->stk, array_size((u64)ncap, sizeof(u32)));
                if (ns == NULL) { st->err = ERR_NOMEM; return 0; }
                st->stk = ns;
                st->scap = ncap;]
              (PushMid W sb c v)
              [("st", .ptr (.struct "ck"), .ptr sb 0), ("v", .u32, .u32 v),
               ("ns", .ptr .u32, .null), ("ncap", .u32, .u32 nc)] st := by
          intro nc hnc hgt hle
          have hn : nc.setWidth 64 ≠ 0#64 := by
            intro e
            have h1 := congrArg BitVec.toNat e
            have h2 := nc.isLt
            simp at h1
            exact hnc (BitVec.eq_of_toNat_eq (by simp; omega))
          simp only [Stmt.block]
          -- pay for the new capacity
          apply WP.seq
          apply WP.ite
          ck_simp
          constructor
          · intro _
            apply WP.seq
            apply WP.ck_setField hs h (by rfl)
            ck_simp
            intro st' h'
            apply WP.ret
            embc_simp [PushMid]
            exact ⟨_, h', ⟨hok.null, hok.size, hok.cap⟩, by constructor <;> rfl, fun _ _ => rfl, rfl⟩
          intro _
          apply WP.skip
          apply WP.seq
          apply WP.ck_setField hs h (by rfl)
          ck_simp
          intro st h
          -- pay for it from the memory budget too
          apply WP.seq
          apply WP.ite
          ck_simp
          constructor
          · intro _
            apply WP.seq
            apply WP.ck_setField hs h (by rfl)
            ck_simp
            intro st' h'
            apply WP.ret
            embc_simp [PushMid]
            exact ⟨_, h', ⟨hok.null, hok.size, hok.cap⟩, by constructor <;> rfl, fun _ _ => rfl, rfl⟩
          intro _
          apply WP.skip
          apply WP.seq
          apply WP.ck_setField hs h (by rfl)
          ck_simp
          intro st h
          have hrun := h.realloc_run (P := prog) .stk hn
          simp only [CK.ptr] at hrun
          apply WP.seq
          apply WP.ecall
          ck_simp [hrun]
          by_cases horc : (reallocResponse (P := Vbcf.prog) c.k.stk hn st).1 ≠ some .null
          · simp only [ne_eq, Classical.not_not] at horc
            simp only [horc, ↓reduceIte]
            have hN : nc.toNat % 18446744073709551616 = nc.toNat := by have := nc.isLt; omega
            obtain ⟨hnew, hck⟩ := h.grow_blocks .stk (nc.toNat % 18446744073709551616)
            obtain ⟨hst, hh⟩ := h.grow hs .stk (nc.toNat % 18446744073709551616)
            simp only [Arr.field] at hst hh
            embc_simp [Mem.hasTy_ptr hnew rfl]
            apply WP.seq
            apply WP.ite
            embc_simp [hnew]
            apply WP.skip
            apply WP.seq
            apply WP.setField
            embc_simp [hst]
            apply WP.ck_setField hs hh (by rfl)
            embc_simp [CK.setU32]
            intro st' h'
            simp only [PushMid]
            refine ⟨⟨_, _, rfl⟩, _, _, h', ⟨?_, ?_, ?_⟩, ?_, rfl, rfl, ?_, ?_⟩
            · intro e; simp [CK.setPtr, CMem.setArr] at e
            · intro b' o' _
              simp [CMem.setArr, reallocCells_size, hN]
            · show c.k.sp.toNat ≤ nc.toNat ∧ nc.toNat ≤ 2 * maxPool
              rw [hfull]; exact ⟨by omega, hle⟩
            · constructor <;> rfl
            · show c.k.sp.toNat < nc.toNat
              rw [hfull]; exact hgt
            · intro i hi
              show (reallocCells _ _)[i]? = _
              simp only [CMem.old, CK.ptr]
              cases hstk : c.k.stk with
              | none =>
                have := hok.null hstk
                rw [hfull, this] at hi; simp at hi
              | some bo =>
                simp only []
                have hsz := hok.size bo.1 bo.2 hstk
                exact reallocCells_get _ _ _ (by show i < c.stk.size; rw [hsz, ← hfull]; exact hi)
                  (by rw [hN]; rw [hfull] at hi; omega)
          · simp only [ne_eq, Classical.not_not] at horc
            simp only [horc, ↓reduceIte]
            embc_simp
            apply WP.seq
            apply WP.ite
            embc_simp
            apply WP.seq
            apply WP.ck_setField hs h (by rfl)
            ck_simp
            intro st' h'
            apply WP.ret
            embc_simp [PushMid]
            exact ⟨_, h', ⟨hok.null, hok.size, hok.cap⟩, by constructor <;> rfl, fun _ _ => rfl, rfl⟩
        apply WP.seq
        apply WP.ite
        ck_simp
        constructor
        · intro hbig
          apply WP.seq
          apply WP.ck_setField hs h (by rfl)
          ck_simp
          intro st' h'
          apply WP.ret
          embc_simp [PushMid]
          exact ⟨_, h', ⟨hok.null, hok.size, hok.cap⟩, by constructor <;> rfl, fun _ _ => rfl, rfl⟩
        · intro hsmall
          have hs30 : c.k.scap.toNat < 1073741824 := by
            simpa [BitVec.lt_def, BitVec.le_def] using hsmall
          have hmul : (c.k.scap * 2#32).toNat = c.k.scap.toNat * 2 := by
            rw [BitVec.toNat_mul]; simp; omega
          apply WP.skip
          apply WP.seq
          apply WP.assign
          ck_simp
          apply WP.seq
          apply WP.ite
          ck_simp
          constructor
          · intro hz
            have hz' : c.k.scap.toNat = 0 := by
              have := congrArg BitVec.toNat hz
              rw [hmul] at this; simp at this; omega
            apply WP.assign
            ck_simp
            exact key 256#32 (by decide) (by rw [hz']; decide) (by decide)
          · intro hnz
            have hnz' : c.k.scap.toNat ≠ 0 := by
              intro e
              apply hnz
              apply BitVec.eq_of_toNat_eq
              rw [hmul, e]; rfl
            apply WP.skip
            exact key (c.k.scap * 2#32) hnz (by rw [hmul]; omega) (by rw [hmul]; simp [maxPool]; omega)
      · intro hnf
        apply WP.skip
        have hlt : c.k.sp.toNat < c.k.scap.toNat := by
          have := hok.cap.1
          have : c.k.sp.toNat ≠ c.k.scap.toNat := fun e => hnf (BitVec.eq_of_toNat_eq e)
          omega
        have hnn : c.k.stk ≠ none := by
          intro e; have := hok.null e; simp [this] at hlt
        obtain ⟨⟨b, o⟩, hb⟩ := Option.ne_none_iff_exists'.mp hnn
        obtain ⟨rfl, -⟩ := h.arr .stk b o hb
        exact ⟨⟨_, _, rfl⟩, _, b, h, ⟨hok.null, hok.size, hok.cap⟩, by constructor <;> rfl, hb, rfl,
          hlt, fun _ _ => rfl⟩
    · -- store the word
      intro o env' s' hq
      cases o with
      | brk => exact hq.elim
      | ret rv =>
        obtain ⟨c2, h2, hok2, hfr, hpre, hrv, hsp⟩ := hq
        subst hrv
        simp only [retPost, Mem.hasTy_u32, true_and]
        exact ⟨c2, h2, hok2, hfr, hpre, by simp [hsp]⟩
      | normal =>
        obtain ⟨⟨ns, nc, rfl⟩, c2, b, h, hok2, hfr, hstk, hsp, hlt, hpre⟩ := hq
        have hsz := hok2.size b 0 hstk
        apply WP.seq
        apply WP.ck_store .stk h (by rfl) hstk
        ck_simp [hstk, hsp]
        refine ⟨by omega, ?_⟩
        intro st h
        apply WP.seq
        apply WP.ck_setField hs h (by rfl)
        ck_simp [hsp]
        intro st h
        apply WP.ret
        ck_simp [retPost]
        refine ⟨_, h, ⟨?_, ?_, ?_⟩, ?_, ?_, rfl, ?_⟩
        · exact hok2.null
        · intro b' o' hb'
          simp only [Array.size_setIfInBounds]
          exact hok2.size b' o' hb'
        · have h1 := hok2.cap.2
          have h2 : (c.k.sp + 1#32).toNat = c.k.sp.toNat + 1 := by
            rw [BitVec.toNat_add]; simp [maxPool] at h1 ⊢; omega
          show (c.k.sp + 1#32).toNat ≤ c2.k.scap.toNat ∧ _
          exact ⟨by omega, h1⟩
        · constructor <;> first | rfl | (cases hfr; assumption)
        · intro i hi
          show (c2.stk.setIfInBounds c.k.sp.toNat (Val.u32 v))[i]? = _
          rw [Array.getElem?_setIfInBounds]
          have : ¬ c.k.sp.toNat = i := by omega
          simp only [this, ↓reduceIte]
          exact hpre i hi
        · show (c2.stk.setIfInBounds c.k.sp.toNat (Val.u32 v))[c.k.sp.toNat]? = _
          rw [Array.getElem?_setIfInBounds]
          simp; omega

end Vbcf.Proof
