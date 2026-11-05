import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Access

/-!
# Vbcf proofs: `words_eq` and `ck_hash`

Both functions only read.  Their specifications are stated against the two
facts they need (`HasCK` for the struct, `HasArr` for the pool block) rather
than against `Holds`, because `ck_hgrow` calls `ck_hput` (and so `ck_hash`)
in a state where `Holds` does not hold: the old table is still live but no
longer referenced by the struct.  `Holds.poolArr` gives the `HasArr` fact in
the ordinary case.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- Cell `i` holds an initialised 32-bit word. -/
def IsW (cells : Array EmbC.Val) (i : Nat) : Prop := ∃ w, cells[i]? = some (.u32 w)

theorem U.isW {cells : Array EmbC.Val} {i w : Nat} (h : U cells i w) : IsW cells i := ⟨_, h⟩

section
variable {W : World} {m : Mem} {sb : Nat} {c : CMem}

theorem Holds.poolArr (h : Holds W m sb c) {b : Nat} (hp : c.k.pool = some (b, 0)) :
    HasArr m b c.pool := (h.arr .pool b 0 hp).2.2.2

theorem Holds.htabArr (h : Holds W m sb c) {b : Nat} (hp : c.k.htab = some (b, 0)) :
    HasArr m b c.htab := (h.arr .htab b 0 hp).2.2.2

end

theorem HasArr.hasTy {m : Mem} {b : Nat} {cells : Array EmbC.Val} (h : HasArr m b cells) (o : Nat) :
    m.hasTy (.ptr b o) (.ptr .u32) = true := Mem.hasTy_ptr h rfl

/-! ## `words_eq` -/

/-- `words_eq(a, b, n)`: reads only; returns 1 iff the two `n`-cell ranges are
equal.  The cells must be initialised words. -/
theorem words_eq_spec (ba oa bb ob : Nat) (ca cb : Array EmbC.Val) (n : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "words_eq"
      (fun vs s => vs = [.ptr ba oa, .ptr bb ob, .u32 n] ∧ HasArr s.mem ba ca ∧ HasArr s.mem bb cb ∧
        (∀ j, j < n.toNat → IsW ca (oa + j)) ∧ (∀ j, j < n.toNat → IsW cb (ob + j)))
      (fun _ s rv s' => s' = s ∧
        ((rv = some (.u32 1#32) ∧ ∀ j, j < n.toNat → ca[oa + j]? = cb[ob + j]?) ∨
         (rv = some (.u32 0#32) ∧ ∃ j, j < n.toNat ∧ ca[oa + j]? ≠ cb[ob + j]?))) := by
  apply FnSpec.intro' (fn := wordsEq) rfl
  rintro vs st ⟨rfl, ha, hb, hwa, hwb⟩
  simp [wordsEq, bindParams, ha.hasTy, hb.hasTy]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.while (I := fun env st' => st' = st ∧ ∃ i : BitVec 32,
    env = [("a", .ptr .u32, .ptr ba oa), ("b", .ptr .u32, .ptr bb ob), ("n", .u32, .u32 n),
           ("i", .u32, .u32 i)] ∧
    i.toNat ≤ n.toNat ∧ ∀ j, j < i.toNat → ca[oa + j]? = cb[ob + j]?)
  · exact ⟨rfl, 0, rfl, by simp, by simp⟩
  · rintro env st' ⟨rfl, i, rfl, hin, hpre⟩
    embc_simp
    constructor
    · intro hge
      have hge' : n.toNat ≤ i.toNat := BitVec.le_def.mp hge
      apply WP.ret
      embc_simp [retPost]
      exact fun j hj => hpre j (by omega)
    · intro hlt
      have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
      obtain ⟨x, hx⟩ := hwa _ hlt'
      obtain ⟨y, hy⟩ := hwb _ hlt'
      apply WP.seq
      apply WP.ite
      embc_simp [ha.loadArr, hb.loadArr, rd_u32 hx, rd_u32 hy]
      constructor
      · intro hne
        apply WP.ret
        embc_simp [retPost]
        exact ⟨i.toNat, hlt', by rw [hx, hy]; simpa using hne⟩
      · intro heq
        apply WP.skip
        apply WP.assign
        embc_simp
        have hn := n.isLt
        refine ⟨by omega, ?_⟩
        intro j hj
        by_cases hji : j < i.toNat
        · exact hpre j hji
        · have : j = i.toNat := by omega
          subst this; rw [hx, hy, heq]

/-! ## `ck_hash` -/

/-- The mixing loop of `hashW`. -/
def hashStep (h w : BitVec 32) : BitVec 32 := (h ^^^ w) * 0x01000193#32

/-- The final avalanche of `hashW`. -/
def hashFin (h : BitVec 32) : BitVec 32 :=
  let h := h ^^^ (h >>> 15)
  let h := h * 0x2c1b3c6d#32
  h ^^^ (h >>> 12)

theorem hashW_eq (ws : List (BitVec 32)) :
    hashW ws = hashFin (ws.foldl hashStep 0x811c9dc5#32) := rfl

/-- `ck_hash(st, off, n)`: reads only; returns `hashW` of the `n` words at
`off` in the pool. -/
theorem ck_hash_spec (sb : Nat) (k : CK) (pb : Nat) (cells : Array EmbC.Val) (off n : BitVec 32)
    (ws : List (BitVec 32)) :
    FnSpec (State := State) Vbcf.prog "ck_hash"
      (fun vs s => vs = [.ptr sb 0, .u32 off, .u32 n] ∧ HasCK s.mem sb k ∧ k.pool = some (pb, 0) ∧
        HasArr s.mem pb cells ∧ ws.length = n.toNat ∧ off.toNat + n.toNat ≤ 2 ^ 32 ∧
        ∀ j w, ws[j]? = some w → cells[off.toNat + j]? = some (.u32 w))
      (fun _ s rv s' => s' = s ∧ rv = some (.u32 (hashW ws))) := by
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckHash) rfl
  rintro vs st ⟨rfl, hck, hpool, harr, hlen, hfit, hcells⟩
  simp [ckHash, bindParams, Mem.hasTy_ptr hck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.assign
  embc_simp
  apply WP.seq
  apply WP.while (I := fun env st' => st' = st ∧ ∃ i : BitVec 32,
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("off", .u32, .u32 off), ("n", .u32, .u32 n),
           ("h", .u32, .u32 ((ws.take i.toNat).foldl hashStep 0x811c9dc5#32)),
           ("i", .u32, .u32 i)] ∧
    i.toNat ≤ n.toNat)
  · exact ⟨rfl, 0, rfl, by simp⟩
  · rintro env st' ⟨rfl, i, rfl, hin⟩
    embc_simp
    constructor
    · intro hge
      have hge' : n.toNat ≤ i.toNat := BitVec.le_def.mp hge
      have htake : ws.take i.toNat = ws := List.take_of_length_le (by omega)
      apply WP.seq
      apply WP.assign
      embc_simp
      apply WP.seq
      apply WP.assign
      embc_simp
      apply WP.seq
      apply WP.assign
      embc_simp
      apply WP.ret
      embc_simp [retPost, htake, hashW_eq, hashFin]
    · intro hlt
      have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
      have hw : ws[i.toNat]? = some (ws[i.toNat]'(by omega)) := List.getElem?_eq_getElem (by omega)
      have hidx : (off + i).toNat = off.toNat + i.toNat := bv_add_toNat (by omega)
      apply WP.seq
      apply WP.assign
      embc_simp [HasCK.ld_pool hs hck, hpool, harr.loadArr, hidx, rd_u32 (hcells _ _ hw)]
      apply WP.assign
      embc_simp
      have hn := n.isLt
      have h1 : (i + 1#32).toNat = i.toNat + 1 := bv_add_toNat (by simp; omega)
      refine ⟨_, ⟨?_, rfl⟩, by omega⟩
      rw [h1, List.take_add_one, hw]
      simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil, hashStep]

/-! ## The same two specifications, against `Holds` -/

/-- A specification still holds from a stronger precondition. -/
theorem FnSpec.of_pre {P : Prog} {f : String} {pre pre' : List EmbC.Val → (KernelState P State) → Prop}
    {post : List EmbC.Val → (KernelState P State) → Option EmbC.Val → (KernelState P State) → Prop} (h : FnSpec (State := State) P f pre post)
    (hp : ∀ vs st, pre' vs st → pre vs st) : FnSpec (State := State) P f pre' post :=
  fun fuel vs st hpre => h fuel vs st (hp vs st hpre)

/-- `words_eq` on two ranges of the pool. -/
theorem words_eq_pool_spec (W : World) (sb : Nat) (c : CMem) (b oa ob : Nat) (n : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "words_eq"
      (fun vs s => vs = [.ptr b oa, .ptr b ob, .u32 n] ∧ Holds W s.mem sb c ∧
        c.k.pool = some (b, 0) ∧
        (∀ j, j < n.toNat → IsW c.pool (oa + j)) ∧ (∀ j, j < n.toNat → IsW c.pool (ob + j)))
      (fun _ s rv s' => s' = s ∧
        ((rv = some (.u32 1#32) ∧ ∀ j, j < n.toNat → c.pool[oa + j]? = c.pool[ob + j]?) ∨
         (rv = some (.u32 0#32) ∧ ∃ j, j < n.toNat ∧ c.pool[oa + j]? ≠ c.pool[ob + j]?))) :=
  FnSpec.of_pre (words_eq_spec b oa b ob c.pool c.pool n)
    (fun _ _ ⟨hv, h, hp, ha, hb⟩ => ⟨hv, h.poolArr hp, h.poolArr hp, ha, hb⟩)

/-- `ck_hash` on a range of the pool. -/
theorem ck_hash_pool_spec (W : World) (sb : Nat) (c : CMem) (b : Nat) (off n : BitVec 32)
    (ws : List (BitVec 32)) :
    FnSpec (State := State) Vbcf.prog "ck_hash"
      (fun vs s => vs = [.ptr sb 0, .u32 off, .u32 n] ∧ Holds W s.mem sb c ∧
        c.k.pool = some (b, 0) ∧ ws.length = n.toNat ∧ off.toNat + n.toNat ≤ 2 ^ 32 ∧
        ∀ j w, ws[j]? = some w → c.pool[off.toNat + j]? = some (.u32 w))
      (fun _ s rv s' => s' = s ∧ rv = some (.u32 (hashW ws))) :=
  FnSpec.of_pre (ck_hash_spec sb c.k b c.pool off n ws)
    (fun _ _ ⟨hv, h, hp, hl, hf, hc⟩ => ⟨hv, h.ck, hp, h.poolArr hp, hl, hf, hc⟩)

end Vbcf.Proof
