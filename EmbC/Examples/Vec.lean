import EmbC.DSL
import EmbC.Logic

/-!
# Stage 1 examples: two small functions, written, specified and proved

* `words_eq` compares two `u32` arrays (a loop, array reads).
* `vec_push` appends to a growable `u32` vector (struct fields, `kvrealloc`,
  its failure path, array writes).

Both are the kind of code the checker needs: the first for comparing nodes
when interning, the second for growing the expression pool.
-/

namespace EmbC.Examples
open EmbC

variable {State : Type}

/-! ## The code -/

def vecS : StructDef := c_struct% vec { u32 *data; u32 len; u32 cap; }

def wordsEq : Fn := c_fn% u32 words_eq(u32 *a, u32 *b, u32 n) {
  u32 i;
  while (i < n) {
    if (a[i] != b[i]) { return 0; }
    i = i + 1;
  }
  return 1;
}

def vecPush : Fn := c_fn% u32 vec_push(struct vec *v, u32 x) {
  u32 *nd; u32 ncap;
  if (v->len == v->cap) {
    if (v->cap >= 1073741824) { return 1; }
    ncap = v->cap * 2;
    if (ncap == 0) { ncap = 16; }
    nd = kvrealloc(v->data, array_size((u64)ncap, sizeof(u32)));
    if (nd == NULL) { return 1; }
    v->data = nd;
    v->cap = ncap;
  }
  v->data[v->len] = x;
  v->len = v->len + 1;
  return 0;
}

/-! ## `words_eq` -/

/-- Block `b` is a live `u32` array holding `xs` from offset `off`. -/
def ArrAt (m : Mem) (b off : Nat) (xs : List (BitVec 32)) : Prop :=
  ∃ blk, m.block? b = some blk ∧ blk.elem = .u32 ∧
    ∀ j x, xs[j]? = some x → blk.cells[off + j]? = some (.u32 x)

theorem ArrAt.load {m : Mem} {b off : Nat} {xs : List (BitVec 32)} (h : ArrAt m b off xs)
    {j : Nat} {x : BitVec 32} (hj : xs[j]? = some x) : m.loadArr b (off + j) = some (.u32 x) := by
  obtain ⟨blk, hb, he, hc⟩ := h
  exact Mem.loadArr_eq hb (by simp [he, Ty.isStruct]) (hc j x hj) (by simp)

/-- `words_eq(a, b, n)` returns 1 exactly when the two `n`-word arrays are
equal, and changes nothing. -/
theorem wordsEq_spec (P : Prog) (hf : P.findFn "words_eq" = some wordsEq)
    (xs ys : List (BitVec 32)) :
    FnSpec (State := State) P "words_eq"
      (fun vs st => ∃ ba oa bb ob n, vs = [.ptr ba oa, .ptr bb ob, .u32 n] ∧
        ArrAt st.mem ba oa xs ∧ ArrAt st.mem bb ob ys ∧
        xs.length = n.toNat ∧ ys.length = n.toNat)
      (fun _ st rv st' => st'.mem = st.mem ∧ rv = some (.u32 (if xs = ys then 1 else 0))) := by
  apply FnSpec.intro hf
  rintro vs st ⟨ba, oa, bb, ob, n, rfl, ha, hb, hxn, hyn⟩
  have hta : st.mem.hasTy (.ptr ba oa) (.ptr .u32) = true := by
    obtain ⟨blk, h1, h2, -⟩ := ha; exact Mem.hasTy_ptr h1 h2
  have htb : st.mem.hasTy (.ptr bb ob) (.ptr .u32) = true := by
    obtain ⟨blk, h1, h2, -⟩ := hb; exact Mem.hasTy_ptr h1 h2
  refine ⟨[("a", .ptr .u32, .ptr ba oa), ("b", .ptr .u32, .ptr bb ob), ("n", .u32, .u32 n)], ?_, ?_⟩
  · simp [wordsEq, bindParams, hta, htb]
  simp only [wordsEq, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]
  apply WP.seq
  apply WP.while (I := fun env st' => st' = st ∧ ∃ i : BitVec 32,
    env = [("a", .ptr .u32, .ptr ba oa), ("b", .ptr .u32, .ptr bb ob), ("n", .u32, .u32 n),
           ("i", .u32, .u32 i)] ∧
    i.toNat ≤ n.toNat ∧ ∀ j, j < i.toNat → xs[j]? = ys[j]?)
  · exact ⟨rfl, 0, rfl, by simp, by simp⟩
  · rintro env st' ⟨rfl, i, rfl, hin, hpre⟩
    embc_simp
    constructor
    · -- loop exit: every index agrees
      intro hge
      have hge' : n.toNat ≤ i.toNat := BitVec.le_def.mp hge
      apply WP.ret
      embc_simp [retPost]
      have : xs = ys := by
        apply List.ext_getElem?
        intro j
        by_cases hj : j < i.toNat
        · exact hpre j hj
        · have h1 : xs.length ≤ j := by omega
          have h2 : ys.length ≤ j := by omega
          rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
      simp [this]
    · -- loop body
      intro hlt
      have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
      obtain ⟨x, hx⟩ : ∃ x, xs[i.toNat]? = some x :=
        ⟨xs[i.toNat]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨y, hy⟩ : ∃ y, ys[i.toNat]? = some y :=
        ⟨ys[i.toNat]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      apply WP.seq
      apply WP.ite
      embc_simp [ha.load hx, hb.load hy]
      constructor
      · intro hne
        apply WP.ret
        embc_simp [retPost]
        have : xs ≠ ys := by
          intro h; subst h; rw [hx] at hy; simp at hy; exact hne hy
        simp [this]
      · intro heq
        apply WP.skip
        apply WP.assign
        embc_simp
        have hn := n.isLt
        refine ⟨by omega, ?_⟩
        · intro j hj
          by_cases hji : j < i.toNat
          · exact hpre j hji
          · have : j = i.toNat := by omega
            subst this; rw [hx, hy, heq]

/-! ## `vec_push` -/

/-- The `struct vec` in block `vb` represents the list `xs`: its length
field is `xs.length`, and if it has a data block, that block has `cap` cells
of which the first `xs.length` hold `xs`. -/
def IsVec (m : Mem) (vb : Nat) (xs : List (BitVec 32)) : Prop :=
  ∃ (d : Val) (len cap : BitVec 32),
    m.block? vb = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap]) ∧
    len.toNat = xs.length ∧ len.toNat ≤ cap.toNat ∧
    ((d = .null ∧ cap = 0) ∨
     ∃ (db : Nat) (cells : Array Val), d = .ptr db 0 ∧ db ≠ vb ∧
       m.block? db = some (Block.mk .u32 cells) ∧
       cells.size = cap.toNat ∧ ∀ (j : Nat) (x : BitVec 32), xs[j]? = some x → cells[j]? = some (Val.u32 x))

/-- The data block a vec currently points to. -/
def vecData (m : Mem) (vb : Nat) : Option Nat :=
  match m.block? vb with
  | some blk =>
    match blk.cells[0]? with
    | some (Val.ptr b _) => some b
    | _ => none
  | none => none

section
variable {P : Prog} {m : Mem} {vb : Nat} {d : Val} {len cap : BitVec 32}

theorem vec_slots (hs : P.findStruct "vec" = some vecS)
    (hblk : m.block? vb = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap])) :
    m.fieldSlot P vb "data" = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap], 0, .ptr .u32) ∧
    m.fieldSlot P vb "len" = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap], 1, .u32) ∧
    m.fieldSlot P vb "cap" = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap], 2, .u32) := by
  simp [Mem.fieldSlot, hblk, hs, vecS, StructDef.field?, fieldIn]

theorem vec_loads (hs : P.findStruct "vec" = some vecS)
    (hblk : m.block? vb = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap]))
    (hd : d ≠ .undef) :
    m.loadField P vb "data" = some d ∧ m.loadField P vb "len" = some (.u32 len) ∧
    m.loadField P vb "cap" = some (.u32 cap) := by
  obtain ⟨h0, h1, h2⟩ := vec_slots hs hblk
  exact ⟨Mem.loadField_eq h0 (by simp) hd, Mem.loadField_eq h1 (by simp) (by simp),
    Mem.loadField_eq h2 (by simp) (by simp)⟩

end

/-- The vec has room for one more element: a data block `db` of `cap` cells
with `len < cap`. -/
def HasRoom (m : Mem) (vb db : Nat) (xs : List (BitVec 32)) : Prop :=
  ∃ (cells : Array Val) (len cap : BitVec 32),
    m.block? vb = some (Block.mk (.struct "vec") #[.ptr db 0, .u32 len, .u32 cap]) ∧
    len.toNat = xs.length ∧ len.toNat < cap.toNat ∧ db ≠ vb ∧
    m.block? db = some (Block.mk .u32 cells) ∧ cells.size = cap.toNat ∧
    ∀ (j : Nat) (x : BitVec 32), xs[j]? = some x → cells[j]? = some (Val.u32 x)

/-- Everything outside the vec is left alone, and no block number is reused. -/
def VecFrame (m m' : Mem) (vb : Nat) : Prop :=
  m.blocks.size ≤ m'.blocks.size ∧
  ∀ b blk, b ≠ vb → vecData m vb ≠ some b → m.block? b = some blk → m'.block? b = some blk

/-- Where the function stands after the "make room" step: there is room, the
rest of memory is as it was in `m0`, and the data block is either the
original one or a block that did not exist in `m0`. -/
def Mid (m0 m : Mem) (vb : Nat) (xs : List (BitVec 32)) : Prop :=
  ∃ db, HasRoom m vb db xs ∧ VecFrame m0 m vb ∧ (vecData m0 vb = some db ∨ m0.block? db = none)

/-- The store-and-bump tail of `vec_push`. -/
theorem push_tail {P : Prog} (hs : P.findStruct "vec" = some vecS) {m0 : Mem} {st : KernelState P State}
    {vb : Nat} {x : BitVec 32} {xs : List (BitVec 32)} {nd nc : Val}
    (hmid : Mid m0 st.mem vb xs) :
    WP P [cstms| v->data[v->len] = x; v->len = v->len + 1; return 0;]
      (retPost (some .u32) fun rv st' =>
        rv = some (.u32 0) ∧ IsVec st'.mem vb (xs ++ [x]) ∧ VecFrame m0 st'.mem vb)
      [("v", .ptr (.struct "vec"), .ptr vb 0), ("x", .u32, .u32 x), ("nd", .ptr .u32, nd),
       ("ncap", .u32, nc)] st := by
  obtain ⟨db, ⟨cells, len, cap, hblk, hlen, hlt, hne, hdb, hsz, hcont⟩, ⟨hfs, hfr⟩, hfresh⟩ := hmid
  obtain ⟨ld, ll, lc⟩ := vec_loads hs hblk (by simp)
  have hst : st.mem.storeArr db len.toNat (.u32 x)
      = some (st.mem.setCell db len.toNat (.u32 x)) :=
    Mem.storeArr_eq hdb rfl (by simp) (by simp; omega)
  simp only [Stmt.block]
  apply WP.seq
  apply WP.store
  embc_simp [ld, ll, hst]
  generalize hm1 : st.mem.setCell db len.toNat (.u32 x) = m1
  have hb1 : ∀ b', m1.block? b' =
      if b' = db then some (Block.mk .u32 (cells.setIfInBounds len.toNat (.u32 x)))
      else st.mem.block? b' := fun b' => by rw [← hm1]; exact Mem.block?_setCell b' hdb
  have hblk1 : m1.block? vb
      = some (Block.mk (.struct "vec") #[.ptr db 0, .u32 len, .u32 cap]) := by
    rw [hb1]; simp [Ne.symm hne, hblk]
  obtain ⟨-, sl1, -⟩ := vec_slots hs hblk1
  obtain ⟨-, ll1, -⟩ := vec_loads hs hblk1 (by simp)
  have hsf := Mem.storeField_eq (v := .u32 (len + 1#32)) sl1 (by simp) (by simp)
  apply WP.seq
  apply WP.setField
  embc_simp [ll1, hsf]
  apply WP.ret
  embc_simp [retPost]
  have hcl := cap.isLt
  have hb2 := fun b' => Mem.block?_setCell (i := 1) (v := .u32 (len + 1#32)) b' hblk1
  refine ⟨⟨.ptr db 0, len + 1#32, cap, ?_, ?_, ?_, Or.inr ⟨db, cells.setIfInBounds len.toNat (.u32 x), rfl, hne, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · rw [hb2]; simp
  · rw [BitVec.toNat_add]; simp; omega
  · rw [BitVec.toNat_add]; simp; omega
  · rw [hb2, hb1]; simp [hne]
  · simp [hsz]
  · intro j y hj
    rw [Array.getElem?_setIfInBounds]
    by_cases hjl : j < xs.length
    · rw [List.getElem?_append_left hjl] at hj
      have : ¬ len.toNat = j := by omega
      simp [this, hcont j y hj]
    · have hjl' : j = xs.length := by
        have := (List.getElem?_eq_some_iff.mp hj).1
        simp at this; omega
      subst hjl'
      simp at hj
      simp [hlen, hj]; omega
  · simp [← hm1]; exact hfs
  · intro b blk hbv hbd hb0
    have hbdb : b ≠ db := by
      rcases hfresh with h | h
      · intro e; subst e; exact hbd h
      · intro e; subst e; rw [h] at hb0; cases hb0
    rw [hb2, hb1]; simp [hbv, hbdb]; exact hfr b blk hbv hbd hb0

/-- What the "make room" step guarantees: it falls through with room made,
or it returns 1 with memory untouched. -/
def Qmid {P : Prog} (m0 : Mem) (vb : Nat) (x : BitVec 32)
    (xs : List (BitVec 32)) : Post P State := fun o env' st' =>
  match o with
  | .normal =>
    (∃ nd nc : Val, env' = [("v", .ptr (.struct "vec"), .ptr vb 0), ("x", .u32, .u32 x),
      ("nd", .ptr .u32, nd), ("ncap", .u32, nc)]) ∧ Mid m0 st'.mem vb xs
  | .ret rv => rv = some (.u32 1) ∧ st'.mem = m0
  | .brk => False

/-- After a successful `kvrealloc` returned block `b'`: install it. -/
theorem grow_install {P : Prog} (hs : P.findStruct "vec" = some vecS) {m0 : Mem} {st : KernelState P State}
    {vb b' : Nat} {x : BitVec 32} {xs : List (BitVec 32)} {d : Val} {len cap nc : BitVec 32}
    {cells' : Array Val}
    (hblk : st.mem.block? vb = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap]))
    (hb' : st.mem.block? b' = some (Block.mk .u32 cells'))
    (hne : b' ≠ vb) (hlen : len.toNat = xs.length) (hlt : len.toNat < nc.toNat)
    (hsz : cells'.size = nc.toNat)
    (hcont : ∀ (j : Nat) (x : BitVec 32), xs[j]? = some x → cells'[j]? = some (Val.u32 x))
    (hfs : m0.blocks.size ≤ st.mem.blocks.size)
    (hfr : ∀ b blk, b ≠ vb → vecData m0 vb ≠ some b → m0.block? b = some blk →
      st.mem.block? b = some blk)
    (hnew : m0.block? b' = none) :
    WP P [cstms| if (nd == NULL) { return 1; } v->data = nd; v->cap = ncap;]
      (Qmid m0 vb x xs)
      [("v", .ptr (.struct "vec"), .ptr vb 0), ("x", .u32, .u32 x),
       ("nd", .ptr .u32, .ptr b' 0), ("ncap", .u32, .u32 nc)] st := by
  obtain ⟨sd, -, -⟩ := vec_slots hs hblk
  have hsf := Mem.storeField_eq (v := .ptr b' 0) sd (Mem.hasTy_ptr hb' rfl) (by simp)
  simp only [Stmt.block]
  apply WP.seq
  apply WP.ite
  embc_simp [hb']
  apply WP.skip
  apply WP.seq
  apply WP.setField
  embc_simp [hsf]
  generalize hm1 : st.mem.setCell vb 0 (.ptr b' 0) = m1
  have hb1 : ∀ b, m1.block? b =
      if b = vb then some (Block.mk (.struct "vec") #[.ptr b' 0, .u32 len, .u32 cap])
      else st.mem.block? b := fun b => by
    rw [← hm1, Mem.block?_setCell b hblk]; simp
  have hblk1 := hb1 vb
  simp only [↓reduceIte] at hblk1
  obtain ⟨-, -, sc⟩ := vec_slots hs hblk1
  have hsf1 := Mem.storeField_eq (v := .u32 nc) sc (by simp) (by simp)
  apply WP.setField
  embc_simp [hsf1]
  have hb2 := fun b => Mem.block?_setCell (i := 2) (v := .u32 nc) b hblk1
  refine ⟨⟨_, _, rfl⟩, b', ⟨cells', len, nc, ?_, hlen, hlt, hne, ?_, hsz, hcont⟩, ⟨?_, ?_⟩, Or.inr hnew⟩
  · rw [hb2]; simp
  · rw [hb2, hb1]; simp [hne, hb']
  · simp [← hm1]; exact hfs
  · intro b blk hbv hbd hb0
    rw [hb2, hb1]; simp [hbv]; exact hfr b blk hbv hbd hb0

/-- Ask the kernel for a bigger block and, if it obliges, install it. -/
theorem grow_rest {P : Prog} (hs : P.findStruct "vec" = some vecS) {st : KernelState P State}
    {vb : Nat} {x : BitVec 32} {xs : List (BitVec 32)} {d : Val} {len cap nc : BitVec 32}
    (hblk : st.mem.block? vb = some (Block.mk (.struct "vec") #[d, .u32 len, .u32 cap]))
    (hlen : len.toNat = xs.length) (hcap : len.toNat ≤ cap.toNat) (hgt : cap.toNat < nc.toNat)
    (hd : (d = .null ∧ cap = 0) ∨
      ∃ (db : Nat) (cells : Array Val), d = .ptr db 0 ∧ db ≠ vb ∧
        st.mem.block? db = some (Block.mk .u32 cells) ∧
        cells.size = cap.toNat ∧
        ∀ (j : Nat) (x : BitVec 32), xs[j]? = some x → cells[j]? = some (Val.u32 x)) :
    WP P [cstms|
        nd = kvrealloc(v->data, array_size((u64)ncap, sizeof(u32)));
        if (nd == NULL) { return 1; }
        v->data = nd;
        v->cap = ncap;]
      (Qmid st.mem vb x xs)
      [("v", .ptr (.struct "vec"), .ptr vb 0), ("x", .u32, .u32 x),
       ("nd", .ptr .u32, .null), ("ncap", .u32, .u32 nc)] st := by
  have hn : nc.setWidth 64 ≠ 0#64 := by
    intro h
    have := congrArg BitVec.toNat h
    simp at this; omega
  have hvb := Mem.block?_lt hblk
  rcases hd with ⟨rfl, rfl⟩ | ⟨db, cells, rfl, hne, hdb, hsz, hcont⟩
  · obtain ⟨ld, -, -⟩ := vec_loads hs hblk (by simp)
    simp only [Stmt.block]
    apply WP.seq
    apply WP.ecall
    embc_simp [ld]
    obtain ⟨rv, after, hr⟩ := Ext.run_defined (P := P) (st := st)
      (show Kernel.Defined P ⟨.kvrealloc .u32, [.null, .u64 (nc.setWidth 64)], st.mem⟩
        from ⟨hn, rfl, trivial⟩)
    simp only [hr]
    rcases after with ⟨afterMem, afterWorld⟩
    rcases kvrealloc_null hn rfl hr with ⟨rfl, hm⟩ | ⟨rfl, hm⟩
    · dsimp only at hm
      subst afterMem
      embc_simp
      apply WP.seq
      apply WP.ite
      embc_simp
      apply WP.ret
      embc_simp [Qmid]
    · dsimp only at hm
      subst afterMem
      generalize hm1 : (st.mem.alloc Ty.u32
        (Array.replicate (nc.toNat % 18446744073709551616) Val.undef)).snd = m1
      have hb1 : ∀ b, m1.block? b = if b = st.mem.blocks.size
          then some (Block.mk .u32 (Array.replicate (nc.toNat % 18446744073709551616) Val.undef))
          else st.mem.block? b := fun b => by rw [← hm1]; exact Mem.block?_alloc b
      have hnew := hb1 st.mem.blocks.size
      simp only [↓reduceIte] at hnew
      embc_simp [hm1, Mem.hasTy_ptr hnew rfl]
      have hncl := nc.isLt
      refine grow_install hs (st := ⟨m1, afterWorld⟩) (m0 := st.mem) (d := .null) (len := len) (cap := 0)
        ?_ hnew ?_ hlen ?_ ?_ ?_ ?_ ?_ Mem.block?_size
      · rw [hb1]; simp [Nat.ne_of_lt hvb, hblk]
      · omega
      · simp at hcap hgt; omega
      · simp; omega
      · intro j y hj
        have : xs = [] := by simp at hcap; exact List.length_eq_zero_iff.mp (by omega)
        subst this; simp at hj
      · simp [← hm1]
      · intro b blk _ _ hb0
        rw [hb1]; simp [Nat.ne_of_lt (Mem.block?_lt hb0), hb0]
  · obtain ⟨ld, -, -⟩ := vec_loads hs hblk (by simp)
    simp only [Stmt.block]
    apply WP.seq
    apply WP.ecall
    embc_simp [ld]
    obtain ⟨rv, after, hr⟩ := Ext.run_defined (P := P) (st := st)
      (show Kernel.Defined P
        ⟨.kvrealloc .u32, [.ptr db 0, .u64 (nc.setWidth 64)], st.mem⟩
        from ⟨hn, rfl, rfl, _, hdb, rfl⟩)
    simp only [hr]
    rcases after with ⟨afterMem, afterWorld⟩
    rcases kvrealloc_ptr hn rfl hdb rfl hr with ⟨rfl, hm⟩ | ⟨rfl, hm⟩
    · dsimp only at hm
      subst afterMem
      embc_simp
      apply WP.seq
      apply WP.ite
      embc_simp [hdb]
      apply WP.ret
      embc_simp [Qmid]
    · dsimp only at hm
      subst afterMem
      generalize hm1 : ((st.mem.free db).alloc Ty.u32
        (reallocCells cells (nc.toNat % 18446744073709551616))).snd = m1
      have hb1 : ∀ b, m1.block? b = if b = st.mem.blocks.size
          then some (Block.mk .u32 (reallocCells cells (nc.toNat % 18446744073709551616)))
          else if b = db then none else st.mem.block? b := fun b => by
        rw [← hm1, Mem.block?_alloc, Mem.block?_free]; simp
      have hnew := hb1 st.mem.blocks.size
      simp only [↓reduceIte] at hnew
      embc_simp [hm1, Mem.hasTy_ptr hnew rfl]
      have hncl := nc.isLt
      refine grow_install hs (st := ⟨m1, afterWorld⟩) (m0 := st.mem) (d := .ptr db 0) (len := len) (cap := cap)
        ?_ hnew ?_ hlen ?_ ?_ ?_ ?_ ?_ Mem.block?_size
      · rw [hb1]; simp [Nat.ne_of_lt hvb, Ne.symm hne, hblk]
      · omega
      · omega
      · simp [reallocCells]; omega
      · intro j y hj
        have hc := hcont j y hj
        have hj' : j < cells.size := by
          rcases Nat.lt_or_ge j cells.size with h | h
          · exact h
          · rw [Array.getElem?_eq_none h] at hc; cases hc
        simp [reallocCells, Array.getElem?_append]
        have h1 : j < min (nc.toNat % 18446744073709551616) cells.size := by omega
        simp [h1]
        rw [Array.getElem?_eq_getElem hj'] at hc
        exact Option.some.inj hc
      · simp [← hm1]
      · intro b blk hbv hbd hb0
        have hbdb : b ≠ db := by
          intro e; subst e; exact hbd (by simp [vecData, hblk])
        rw [hb1]; simp [Nat.ne_of_lt (Mem.block?_lt hb0), hbdb, hb0]

/-- `vec_push(v, x)` either appends `x` and returns 0, or (out of memory, or
at the size limit) leaves memory exactly as it was and returns 1.  It never
touches a block that is not part of the vector. -/
theorem vecPush_spec (P : Prog) (hf : P.findFn "vec_push" = some vecPush)
    (hs : P.findStruct "vec" = some vecS) (xs : List (BitVec 32)) (vb : Nat) (x : BitVec 32) :
    FnSpec (State := State) P "vec_push"
      (fun vs st => vs = [.ptr vb 0, .u32 x] ∧ IsVec st.mem vb xs)
      (fun _ st rv st' =>
        (rv = some (.u32 0) ∧ IsVec st'.mem vb (xs ++ [x]) ∧ VecFrame st.mem st'.mem vb) ∨
        (rv = some (.u32 1) ∧ st'.mem = st.mem)) := by
  apply FnSpec.intro hf
  rintro vs st ⟨rfl, d, len, cap, hblk, hlen, hcap, hd⟩
  have hdu : d ≠ .undef := by
    rcases hd with ⟨rfl, -⟩ | ⟨_, _, rfl, -⟩ <;> simp
  obtain ⟨ld, ll, lc⟩ := vec_loads hs hblk hdu
  refine ⟨[("v", .ptr (.struct "vec"), .ptr vb 0), ("x", .u32, .u32 x)], ?_, ?_⟩
  · simp [vecPush, bindParams, Mem.hasTy_ptr hblk rfl]
  simp only [vecPush, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]
  apply WP.seq
  refine WP.mono (Q := Qmid st.mem vb x xs) ?_ ?_
  · -- make room
    apply WP.ite
    embc_simp [ll, lc]
    constructor
    · intro hfull
      apply WP.seq
      apply WP.ite
      embc_simp [lc]
      constructor
      · intro hbig
        apply WP.ret
        embc_simp [Qmid]
      · intro hsmall
        have hc30 : cap.toNat < 1073741824 := by simpa [BitVec.lt_def] using hsmall
        apply WP.skip
        apply WP.seq
        apply WP.assign
        embc_simp [lc]
        apply WP.seq
        apply WP.ite
        embc_simp
        constructor
        · intro hz
          have hz' := congrArg BitVec.toNat hz
          simp [BitVec.toNat_mul] at hz'
          apply WP.assign
          embc_simp
          exact grow_rest hs hblk hlen hcap (by simp; omega) hd
        · intro hnz
          have hnz' : (cap * 2#32).toNat ≠ 0 := fun h => hnz (BitVec.eq_of_toNat_eq (by simpa using h))
          apply WP.skip
          refine grow_rest hs hblk hlen hcap ?_ hd
          simp [BitVec.toNat_mul] at hnz' ⊢; omega
    · intro hnf
      apply WP.skip
      have hlc : len.toNat ≠ cap.toNat := fun h => hnf (BitVec.eq_of_toNat_eq h)
      rcases hd with ⟨rfl, rfl⟩ | ⟨db, cells, rfl, hne', hdb, hsz, hcont⟩
      · simp at hcap hlc; omega
      · exact ⟨⟨_, _, rfl⟩, db, ⟨cells, len, cap, hblk, hlen, by omega, hne', hdb, hsz, hcont⟩,
          ⟨Nat.le_refl _, fun b blk _ _ h => h⟩, Or.inl (by simp [vecData, hblk])⟩
  · -- store and bump
    intro o env' st' h
    cases o with
    | normal =>
      obtain ⟨⟨nd, nc, rfl⟩, hmid⟩ := h
      refine WP.mono (push_tail hs hmid) ?_
      intro o env'' st''
      cases o <;> simp [retPost]
      rename_i rv
      cases rv <;> simp
      intro h1 h2 h3 h4
      exact ⟨h1, Or.inl ⟨h2, h3, h4⟩⟩
    | brk => exact h.elim
    | ret rv =>
      obtain ⟨rfl, hm⟩ := h
      simp [retPost, hm]

/-! ## A caller: `vec_push2`

Proved from `vec_push`'s specification alone, through the call rule. -/

def vecPush2 : Fn := c_fn% u32 vec_push2(struct vec *v, u32 x, u32 y) {
  u32 r;
  r = vec_push(v, x);
  if (r != 0) { return r; }
  r = vec_push(v, y);
  return r;
}

/-- `vec_push2` appends both elements and returns 0, or returns 1 having
appended none or only the first. -/
theorem vecPush2_spec (P : Prog) (hf2 : P.findFn "vec_push2" = some vecPush2)
    (hf : P.findFn "vec_push" = some vecPush) (hs : P.findStruct "vec" = some vecS)
    (xs : List (BitVec 32)) (vb : Nat) (x y : BitVec 32) :
    FnSpec (State := State) P "vec_push2"
      (fun vs st => vs = [.ptr vb 0, .u32 x, .u32 y] ∧ IsVec st.mem vb xs)
      (fun _ _ rv st' =>
        (rv = some (.u32 0) ∧ IsVec st'.mem vb (xs ++ [x, y])) ∨
        (rv = some (.u32 1) ∧ (IsVec st'.mem vb xs ∨ IsVec st'.mem vb (xs ++ [x])))) := by
  apply FnSpec.intro hf2
  rintro vs st ⟨rfl, hv⟩
  have hty : st.mem.hasTy (.ptr vb 0) (.ptr (.struct "vec")) = true := by
    obtain ⟨d, len, cap, hblk, -⟩ := hv; exact Mem.hasTy_ptr hblk rfl
  refine ⟨[("v", .ptr (.struct "vec"), .ptr vb 0), ("x", .u32, .u32 x), ("y", .u32, .u32 y)],
    ?_, ?_⟩
  · simp [vecPush2, bindParams, hty]
  simp only [vecPush2, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]
  apply WP.seq
  apply WP.call (vecPush_spec P hf hs xs vb x)
  embc_simp
  refine ⟨hv, ?_⟩
  intro rv st1 hpost
  rcases hpost with ⟨rfl, hv1, -⟩ | ⟨rfl, hm⟩
  · embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.skip
    apply WP.seq
    apply WP.call (vecPush_spec P hf hs (xs ++ [x]) vb y)
    embc_simp
    refine ⟨hv1, ?_⟩
    intro rv st2 hpost2
    rcases hpost2 with ⟨rfl, hv2, -⟩ | ⟨rfl, hm2⟩
    · embc_simp
      apply WP.ret
      embc_simp [retPost]
      simpa using hv2
    · embc_simp
      apply WP.ret
      embc_simp [retPost]
      right; rw [hm2]; exact hv1
  · embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.ret
    embc_simp [retPost]
    left; rw [hm]; exact hv

/-! ## The program, and the theorems instantiated for it -/

def prog : Prog := { structs := [vecS], fns := [wordsEq, vecPush, vecPush2] }

theorem prog_wordsEq (xs ys : List (BitVec 32)) :
    FnSpec (State := State) prog "words_eq"
      (fun vs st => ∃ ba oa bb ob n, vs = [.ptr ba oa, .ptr bb ob, .u32 n] ∧
        ArrAt st.mem ba oa xs ∧ ArrAt st.mem bb ob ys ∧
        xs.length = n.toNat ∧ ys.length = n.toNat)
      (fun _ st rv st' => st'.mem = st.mem ∧ rv = some (.u32 (if xs = ys then 1 else 0))) :=
  wordsEq_spec prog rfl xs ys

theorem prog_vecPush2 (xs : List (BitVec 32)) (vb : Nat) (x y : BitVec 32) :
    FnSpec (State := State) prog "vec_push2"
      (fun vs st => vs = [.ptr vb 0, .u32 x, .u32 y] ∧ IsVec st.mem vb xs)
      (fun _ _ rv st' =>
        (rv = some (.u32 0) ∧ IsVec st'.mem vb (xs ++ [x, y])) ∨
        (rv = some (.u32 1) ∧ (IsVec st'.mem vb xs ∨ IsVec st'.mem vb (xs ++ [x])))) :=
  vecPush2_spec prog rfl rfl rfl xs vb x y

end EmbC.Examples
