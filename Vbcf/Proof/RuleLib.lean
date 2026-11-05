import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Builders
import Vbcf.Proof.Core1

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## 1. Words

Every `u32` a rule handles is kept as `BitVec.ofNat 32 n` for a natural number `n`:
an id is `BitVec.ofNat 32 (offs st.pool i)`, a header `BitVec.ofNat 32 (hdrW n)`, a
parameter word `BitVec.ofNat 32 x`.  The lemmas below are in `rule_simp`'s simp set;
their side conditions are closed by `omega` from bounds in the context. -/

theorem uv_inj {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    (BitVec.ofNat 32 a = BitVec.ofNat 32 b) ↔ a = b := bv_ofNat_inj ha hb

theorem uv_le {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    (BitVec.ofNat 32 a ≤ BitVec.ofNat 32 b) ↔ a ≤ b := by
  rw [BitVec.le_def, bv_toNat_ofNat ha, bv_toNat_ofNat hb]

theorem uv_lt {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    (BitVec.ofNat 32 a < BitVec.ofNat 32 b) ↔ a < b := by
  rw [BitVec.lt_def, bv_toNat_ofNat ha, bv_toNat_ofNat hb]

theorem uv_toNat {n : Nat} (h : n < 4294967296) : (BitVec.ofNat 32 n).toNat = n :=
  bv_toNat_ofNat h

theorem mod32 {n : Nat} (h : n < 4294967296) : n % 4294967296 = n := Nat.mod_eq_of_lt h

/-- Sums of words are kept as the word of the sum. -/
theorem uv_add (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem and_hi16 {a : Nat} (ha : a < 4294967296) : a &&& 4294901760 = a / 65536 * 65536 := by
  have e1 : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
  have e2 : a / 65536 * 65536 = (a >>> 16) <<< 16 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [e1, e2]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  by_cases hj : 16 ≤ j
  · by_cases hj2 : j < 32
    · simp [hj, show j - 16 < 16 by omega, show 16 + (j - 16) = j by omega]
    · have h1 : a.testBit j = false := by
        apply Nat.testBit_lt_two_pow
        calc a < 2 ^ 32 := ha
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      simp [h1, hj, show ¬ j - 16 < 16 by omega]
  · simp [hj]

theorem or_lo_hi (a : Nat) :
    a % 256 ||| a / 65536 * 65536 = a % 256 + a / 65536 * 65536 := by
  have e2 : a / 65536 * 65536 = (a / 65536) <<< 16 := by rw [Nat.shiftLeft_eq]
  rw [e2, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : a % 256 < 2 ^ 16)]
  omega

/-- `code | (hdr & 0xffff0000)`: the header with its arity field cleared. -/
theorem uv_or_hi {a : Nat} (ha : a < 4294967296) :
    BitVec.ofNat 32 (a % 256) ||| (BitVec.ofNat 32 a &&& 4294901760#32) =
      BitVec.ofNat 32 (a % 256 + a / 65536 * 65536) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a % 256 < 2 ^ 32), Nat.mod_eq_of_lt (by omega : a < 2 ^ 32)]
  show a % 256 ||| (a &&& 4294901760) = (a % 256 + a / 65536 * 65536) % 2 ^ 32
  rw [and_hi16 ha, or_lo_hi a, Nat.mod_eq_of_lt (by omega : a % 256 + a / 65536 * 65536 < 2 ^ 32)]

/-- `hdr & 0xff` on a word. -/
theorem uv_and_ff (a : Nat) : BitVec.ofNat 32 a &&& 255#32 = BitVec.ofNat 32 (a % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [bv_and_ff, BitVec.toNat_ofNat]
  omega


/-- Lifts `if` out of a `u32` result (what `||` and `&&` evaluate to). -/
theorem ite_some_u32 {p : Prop} [Decidable p] (a b : BitVec 32) :
    (if p then some (EmbC.Val.u32 a) else some (EmbC.Val.u32 b)) =
      some (EmbC.Val.u32 (if p then a else b)) := by
  split <;> rfl

/-- A guard whose condition is `||`/`&&`: cases on the truth value. -/
theorem ite_u32_eq_zero {p : Prop} [Decidable p] (a b : BitVec 32) :
    ((if p then a else b) = 0#32) ↔ (p ∧ a = 0#32) ∨ (¬ p ∧ b = 0#32) := by
  split <;> simp_all

/-- `(hdr & 0xff) == CODE`, on the header of any node (no side condition on the node). -/
theorem hdr_code_eq (n : Node) (k : Nat) (hk : k < 256) :
    (BitVec.ofNat 32 (hdrW n) &&& 255#32 = BitVec.ofNat 32 k) ↔ opC n.op = k := by
  have h1 := opC_lt n.op
  rw [← BitVec.toNat_inj, bv_and_ff, BitVec.toNat_ofNat, bv_toNat_ofNat (by omega)]
  unfold hdrW
  omega

/-- The code byte of any header word. -/
theorem hdrW_mod256 (n : Node) : hdrW n % 256 = opC n.op := by
  have h1 := opC_lt n.op
  unfold hdrW; omega

theorem opC_lt32 (op : Op) : opC op < 4294967296 := Nat.lt_trans (opC_lt op) (by decide)

/-- `(hdr >> 8) & 0xff`, on the header of a fitting node. -/
theorem hdr_len_bv {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    BitVec.ofNat 32 (hdrW n) >>> 8 &&& 255#32 = BitVec.ofNat 32 (tailLen n) := by
  have h1 := hf.tailLen
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_shr_8, bv_toNat_ofNat (hdrW_lt hf), hdrW_len hf, bv_toNat_ofNat (by omega)]

/-! ## 2. Pool extension

A builder call extends the view (`VExt`, `View.lean`): live nodes stay live and keep
their ids, and the Lean pool only grows. -/

/-! ## 3. Ids: nodes of the pool seen from C

A rule sees the Lean state through a view `st : VSt`; the id of a live Lean index `i`
is `st.id i`.  All of this needs only `VInv`, so it can be used by helper functions too.
Where a lemma reads a node, its liveness is an auto-parameter (`vlv`, by assumption). -/

section ids
variable {posOf : Nat → Nat} {c : CMem} {st : VSt}

theorem VInv.id_toNat (hc : VInv posOf c st) {i : Nat} (hi : st.lv i) :
    (BitVec.ofNat 32 (st.id i)).toNat = st.id i := by
  have := hc.off_lt hi
  exact bv_toNat_ofNat (by omega)

theorem VInv.id_mod (hc : VInv posOf c st) {i : Nat} (hi : st.lv i) :
    st.id i % 4294967296 = st.id i := by
  have := hc.off_lt hi
  omega

theorem VInv.id_add_toNat (hc : VInv posOf c st) {i k : Nat} (hi : st.lv i)
    (hk : k < 2147483648) :
    (BitVec.ofNat 32 (st.id i + k)).toNat = st.id i + k := by
  have := hc.off_lt hi
  exact bv_toNat_ofNat (by omega)

theorem VInv.id_add_mod (hc : VInv posOf c st) {i k : Nat} (hi : st.lv i)
    (hk : k < 2147483648) : (st.id i + k) % 4294967296 = st.id i + k := by
  have := hc.off_lt hi
  omega

theorem VInv.id_add2_toNat (hc : VInv posOf c st) {i j k : Nat} (hi : st.lv i)
    (hk : j + k < 2147483648) :
    (BitVec.ofNat 32 (st.id i + j + k)).toNat = st.id i + j + k := by
  have := hc.off_lt hi
  exact bv_toNat_ofNat (by omega)

theorem VInv.id_add2_mod (hc : VInv posOf c st) {i j k : Nat} (hi : st.lv i)
    (hk : j + k < 2147483648) :
    (st.id i + j + k) % 4294967296 = st.id i + j + k := by
  have := hc.off_lt hi
  omega

/-- Equality of ids is equality of indices. -/
theorem VInv.id_inj (hc : VInv posOf c st) {i j : Nat} (hi : st.lv i) (hj : st.lv j) :
    (BitVec.ofNat 32 (st.id i) = BitVec.ofNat 32 (st.id j)) ↔ i = j := by
  have h1 := hc.off_lt hi
  have h2 := hc.off_lt hj
  rw [bv_ofNat_inj (by omega) (by omega)]
  exact ⟨st.id_inj hi hj, fun e => e ▸ rfl⟩

/-- An id is never `NOID`. -/
theorem VInv.id_ne_noid (hc : VInv posOf c st) {i : Nat} (hi : st.lv i) :
    (BitVec.ofNat 32 (st.id i) = 4294967295#32) ↔ False := by
  have h1 := hc.off_lt hi
  rw [show (4294967295#32 : BitVec 32) = BitVec.ofNat 32 4294967295 from rfl,
    bv_ofNat_inj (by omega) (by omega)]
  exact ⟨fun e => by omega, False.elim⟩

/-- The id as a word, from the `toNat` form the specifications use. -/
theorem id_of_toNat {n : Nat} {r : BitVec 32} (h : r.toNat = n) : r = BitVec.ofNat 32 n := by
  rw [← h]; exact (bv_ofNat_toNat r).symm

/-! ### Reading a node

`rdHdr`, `rd1`, `rd2`, `rd3`, `rdN` are what `rule_simp` needs to evaluate `st->pool[p]`,
`st->pool[p + 1]`, …: pass the one that fits the node as a simp argument. -/

theorem VInv.rdHdr (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW n)) := rd_u32 (hc.hdr hn hi)

theorem VInv.rdArg (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    (hl : ¬ IsLeaf n.op) {k : Nat} (hk : k < n.args.size) (hi : st.lv i := by vlv) :
    rd c.pool (st.id i + 1 + k) = some (uv (st.id n.args[k])) :=
  rd_u32 (hc.arg hn hl hk hi)

/-- Cells of a one-argument node. -/
theorem VInv.rd1 (hc : VInv posOf c st) {i : Nat} {op : Op} {a : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hl : ¬ IsLeaf op := by decide) (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, #[a]⟩)) ∧
    rd c.pool (st.id i + 1) = some (uv (st.id a)) :=
  ⟨hc.rdHdr hn hi, hc.rdArg hn hl (k := 0) (by simp) hi⟩

/-- Cells of a two-argument node. -/
theorem VInv.rd2 (hc : VInv posOf c st) {i : Nat} {op : Op} {a b : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hl : ¬ IsLeaf op := by decide)
    (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, #[a, b]⟩)) ∧
    rd c.pool (st.id i + 1) = some (uv (st.id a)) ∧
    rd c.pool (st.id i + 2) = some (uv (st.id b)) :=
  ⟨hc.rdHdr hn hi, hc.rdArg hn hl (k := 0) (by simp) hi, hc.rdArg hn hl (k := 1) (by simp) hi⟩

/-- Cells of a three-argument node. -/
theorem VInv.rd3 (hc : VInv posOf c st) {i : Nat} {op : Op} {a b d : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b, d]⟩) (hl : ¬ IsLeaf op := by decide)
    (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, #[a, b, d]⟩)) ∧
    rd c.pool (st.id i + 1) = some (uv (st.id a)) ∧
    rd c.pool (st.id i + 2) = some (uv (st.id b)) ∧
    rd c.pool (st.id i + 3) = some (uv (st.id d)) :=
  ⟨hc.rdHdr hn hi, hc.rdArg hn hl (k := 0) (by simp) hi, hc.rdArg hn hl (k := 1) (by simp) hi,
    hc.rdArg hn hl (k := 2) (by simp) hi⟩

/-- Cells of an n-ary node: the header, its arity field, and argument `k` at `p + 1 + k`. -/
theorem VInv.rdN (hc : VInv posOf c st) {i : Nat} {op : Op} {args : Array Nat}
    (hn : st.pool[i]? = some ⟨op, args⟩) (hl : ¬ IsLeaf op := by decide) (hi : st.lv i := by vlv) :
    rd c.pool (st.id i) = some (uv (hdrW ⟨op, args⟩)) ∧
    (BitVec.ofNat 32 (hdrW ⟨op, args⟩) >>> 8 &&& 255#32 = BitVec.ofNat 32 args.size) ∧
    ∀ (k : Nat) (hk : k < args.size),
      rd c.pool (st.id i + 1 + k) = some (uv (st.id args[k])) := by
  refine ⟨hc.rdHdr hn hi, ?_, fun k hk => hc.rdArg hn hl hk hi⟩
  rw [hdr_len_bv (hc.fits i _ hn), tailLen_of_not_leaf hl]

/-! ### The shape of a node, from its operator

After a header test has established `hop : n.op = .eq` (say),
`obtain ⟨a, b, rfl, ha, hb⟩ := hc.args2 hn hop` replaces `n` by `⟨.eq, #[a, b]⟩`; the
arguments of a live node are live. -/

theorem array_eq_one {a : Array Nat} (h : a.size = 1) : ∃ x, a = #[x] := by
  rcases a with ⟨l⟩
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩ <;> simp at h
  exact ⟨x, rfl⟩

theorem array_eq_two {a : Array Nat} (h : a.size = 2) : ∃ x y, a = #[x, y] := by
  rcases a with ⟨l⟩
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩ <;> simp at h
  exact ⟨x, y, rfl⟩

theorem array_eq_three {a : Array Nat} (h : a.size = 3) : ∃ x y z, a = #[x, y, z] := by
  rcases a with ⟨l⟩
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, l⟩⟩⟩⟩ <;> simp at h
  exact ⟨x, y, z, rfl⟩

theorem VInv.args1 (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hf : fixedArity op = true := by rfl)
    (hm : minArity op = 1 := by rfl) (hi : st.lv i := by vlv) :
    ∃ a, n = ⟨op, #[a]⟩ ∧ st.lv a := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  obtain ⟨a, rfl⟩ := array_eq_one (a := args) (by rw [ht.fixedArity hf, hm])
  exact ⟨a, rfl, st.closed i _ hi hn a (by simp)⟩

theorem VInv.args2 (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hf : fixedArity op = true := by rfl)
    (hm : minArity op = 2 := by rfl) (hi : st.lv i := by vlv) :
    ∃ a b, n = ⟨op, #[a, b]⟩ ∧ st.lv a ∧ st.lv b := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  obtain ⟨a, b, rfl⟩ := array_eq_two (a := args) (by rw [ht.fixedArity hf, hm])
  exact ⟨a, b, rfl, st.closed i _ hi hn a (by simp), st.closed i _ hi hn b (by simp)⟩

theorem VInv.args3 (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hf : fixedArity op = true := by rfl)
    (hm : minArity op = 3 := by rfl) (hi : st.lv i := by vlv) :
    ∃ a b d, n = ⟨op, #[a, b, d]⟩ ∧ st.lv a ∧ st.lv b ∧ st.lv d := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  obtain ⟨a, b, d, rfl⟩ := array_eq_three (a := args) (by rw [ht.fixedArity hf, hm])
  exact ⟨a, b, d, rfl, st.closed i _ hi hn a (by simp), st.closed i _ hi hn b (by simp),
    st.closed i _ hi hn d (by simp)⟩

/-- An n-ary node: `obtain ⟨args, rfl, hsz, hmin, hargs⟩ := hc.argsN hn hop`. -/
theorem VInv.argsN (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hl : ¬ IsLeaf op := by decide) (hi : st.lv i := by vlv) :
    ∃ args, n = ⟨op, args⟩ ∧ args.size ≤ 255 ∧ minArity op ≤ args.size ∧
      ∀ (k : Nat) (hk : k < args.size), st.lv args[k] := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  have hf := (hc.fits i _ hn).tailLen
  rw [tailLen_of_not_leaf hl] at hf
  exact ⟨args, rfl, by simp only at hf; omega, ht.minArity,
    fun k hk => st.closed i _ hi hn _ (by simp)⟩

theorem VInv.poolPtr_of_node {W : World} {m : Mem} {sb : Nat} (hc : VInv posOf c st)
    (h : Holds W m sb c) {i : Nat} (hi : st.lv i) : ∃ b, c.k.pool = some (b, 0) :=
  hc.cinv.poolPtr_of_nonempty h (by have := st.σ_lt hi; omega)

/-- A child of a live node is live. -/
theorem VInv.arg_lv (_hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    (a : Nat) (ha : a ∈ n.args) (hi : st.lv i := by vlv) : st.lv a := st.closed i n hi hn a ha

/-- The type of a node, as `ty_of` computes it from the header. -/
theorem VInv.tyOf (hc : VInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n) :
    ∃ t, st.tys[i]? = some t ∧ tyOfB (BitVec.ofNat 32 (hdrW n)) = BitVec.ofNat 32 (tyW t) ∧
      TyFits t := by
  have hf := hc.fits i n hn
  obtain ⟨t, ht, he, hfit⟩ := hc.ok.tyOfM_hdrW hn hf
  exact ⟨t, ht, by rw [tyOfB_eq, bv_toNat_ofNat (hdrW_lt hf), he], hfit⟩

/-! ### Interning through the view -/

/-- The C side pushed the renamed node `n` (into C-side state `cs'`, represented by
`c'`): the Lean side pushes `n`, for an extension of the view. -/
theorem VInv.push_tr (hc : VInv posOf c st) {n : Node} (hargs : ∀ a ∈ n.args, st.lv a)
    {c' : CMem} {cs' : St} {x : Nat} (hp : pushNode st.cs (n.ren st.σ) = some (cs', x))
    (hc' : CoreInv posOf c' cs') :
    ∃ (st' : VSt) (i : Nat), pushNode st.toSt n = some (st'.toSt, i) ∧ st'.lv i ∧
      st'.id i = offs cs'.pool x ∧ VExt st st' ∧ VInv posOf c' st' := by
  obtain ⟨st', i, hcs, hpush, hi, hσ, he⟩ := st.push hc.cinv.ok hargs hp
  refine ⟨st', i, hpush, hi, by unfold VSt.id; rw [hcs, hσ], he, ⟨by rw [hcs]; exact hc', ?_⟩⟩
  have hfn : Fits posOf n := by
    have := hc'.rep.fits x _ (pushNode_get hp)
    exact fits_ren.mp this
  intro j m hm
  rcases pushNode_pool hpush with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e] at hm; exact hc.fitsAll j m hm
  · rw [e, Array.getElem?_push] at hm
    split at hm
    · simp only [Option.some.injEq] at hm; subst hm; exact hfn
    · exact hc.fitsAll j m hm

/-- The renamed node with literal arguments. -/
theorem ren_lit1 (σ : Nat → Nat) (op : Op) (a : Nat) :
    (⟨op, #[a]⟩ : Node).ren σ = ⟨op, #[σ a]⟩ := by simp [Node.ren]
theorem ren_lit2 (σ : Nat → Nat) (op : Op) (a b : Nat) :
    (⟨op, #[a, b]⟩ : Node).ren σ = ⟨op, #[σ a, σ b]⟩ := by simp [Node.ren]
theorem ren_lit3 (σ : Nat → Nat) (op : Op) (a b d : Nat) :
    (⟨op, #[a, b, d]⟩ : Node).ren σ = ⟨op, #[σ a, σ b, σ d]⟩ := by simp [Node.ren]
theorem ren_list (σ : Nat → Nat) (op : Op) (is : List Nat) :
    (⟨op, is.toArray⟩ : Node).ren σ = ⟨op, (is.map σ).toArray⟩ := by simp [Node.ren]
theorem ren_leaf (σ : Nat → Nat) (op : Op) : (⟨op, #[]⟩ : Node).ren σ = ⟨op, #[]⟩ := by
  simp [Node.ren]

end ids

/-! ### The same, on the C-side state (for helpers that work there, like `lin_f`) -/

section idsC
variable {posOf : Nat → Nat} {c : CMem} {st : St}

theorem CoreInv.id_toNat (hc : CoreInv posOf c st) {i : Nat} (hi : i < st.pool.size) :
    (BitVec.ofNat 32 (offs st.pool i)).toNat = offs st.pool i := by
  have := hc.off_lt hi
  exact bv_toNat_ofNat (by omega)

theorem CoreInv.id_mod (hc : CoreInv posOf c st) {i : Nat} (hi : i < st.pool.size) :
    offs st.pool i % 4294967296 = offs st.pool i := by
  have := hc.off_lt hi
  omega

theorem CoreInv.id_add_toNat (hc : CoreInv posOf c st) {i k : Nat} (hi : i < st.pool.size)
    (hk : k < 2147483648) :
    (BitVec.ofNat 32 (offs st.pool i + k)).toNat = offs st.pool i + k := by
  have := hc.off_lt hi
  exact bv_toNat_ofNat (by omega)

theorem CoreInv.id_add_mod (hc : CoreInv posOf c st) {i k : Nat} (hi : i < st.pool.size)
    (hk : k < 2147483648) : (offs st.pool i + k) % 4294967296 = offs st.pool i + k := by
  have := hc.off_lt hi
  omega

theorem CoreInv.id_add2_toNat (hc : CoreInv posOf c st) {i j k : Nat} (hi : i < st.pool.size)
    (hk : j + k < 2147483648) :
    (BitVec.ofNat 32 (offs st.pool i + j + k)).toNat = offs st.pool i + j + k := by
  have := hc.off_lt hi
  exact bv_toNat_ofNat (by omega)

theorem CoreInv.id_add2_mod (hc : CoreInv posOf c st) {i j k : Nat} (hi : i < st.pool.size)
    (hk : j + k < 2147483648) :
    (offs st.pool i + j + k) % 4294967296 = offs st.pool i + j + k := by
  have := hc.off_lt hi
  omega

/-! ### Reading a node

`rdHdr`, `rd1`, `rd2`, `rd3`, `rdN` are what `rule_simp` needs to evaluate `st->pool[p]`,
`st->pool[p + 1]`, …: pass the one that fits the node as a simp argument. -/

/-- Equality of ids is equality of indices. -/
theorem CoreInv.id_inj (hc : CoreInv posOf c st) {i j : Nat} (hi : i < st.pool.size)
    (hj : j < st.pool.size) :
    (BitVec.ofNat 32 (offs st.pool i) = BitVec.ofNat 32 (offs st.pool j)) ↔ i = j := by
  have h1 := hc.off_lt hi
  have h2 := hc.off_lt hj
  rw [bv_ofNat_inj (by omega) (by omega)]
  exact ⟨offs_inj (Nat.le_of_lt hi) (Nat.le_of_lt hj), fun e => e ▸ rfl⟩

/-- An id is never `NOID`. -/
theorem CoreInv.id_ne_noid (hc : CoreInv posOf c st) {i : Nat} (hi : i < st.pool.size) :
    (BitVec.ofNat 32 (offs st.pool i) = 4294967295#32) ↔ False := by
  have h1 := hc.off_lt hi
  rw [show (4294967295#32 : BitVec 32) = BitVec.ofNat 32 4294967295 from rfl,
    bv_ofNat_inj (by omega) (by omega)]
  exact ⟨fun e => by omega, False.elim⟩

theorem CoreInv.rdHdr (hc : CoreInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n) :
    rd c.pool (offs st.pool i) = some (uv (hdrW n)) := rd_u32 (hc.rep.hdr hn)

theorem CoreInv.rdArg (hc : CoreInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    (hl : ¬ IsLeaf n.op) {k : Nat} (hk : k < n.args.size) :
    rd c.pool (offs st.pool i + 1 + k) = some (uv (offs st.pool n.args[k])) :=
  rd_u32 (hc.rep.arg hn hl hk)

/-- Cells of a one-argument node. -/
theorem CoreInv.rd1 (hc : CoreInv posOf c st) {i : Nat} {op : Op} {a : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hl : ¬ IsLeaf op := by decide) :
    rd c.pool (offs st.pool i) = some (uv (hdrW ⟨op, #[a]⟩)) ∧
    rd c.pool (offs st.pool i + 1) = some (uv (offs st.pool a)) :=
  ⟨hc.rdHdr hn, hc.rdArg hn hl (k := 0) (by simp)⟩

/-- Cells of a two-argument node. -/
theorem CoreInv.rd2 (hc : CoreInv posOf c st) {i : Nat} {op : Op} {a b : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hl : ¬ IsLeaf op := by decide) :
    rd c.pool (offs st.pool i) = some (uv (hdrW ⟨op, #[a, b]⟩)) ∧
    rd c.pool (offs st.pool i + 1) = some (uv (offs st.pool a)) ∧
    rd c.pool (offs st.pool i + 2) = some (uv (offs st.pool b)) :=
  ⟨hc.rdHdr hn, hc.rdArg hn hl (k := 0) (by simp), hc.rdArg hn hl (k := 1) (by simp)⟩

/-- Cells of a three-argument node. -/
theorem CoreInv.rd3 (hc : CoreInv posOf c st) {i : Nat} {op : Op} {a b d : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b, d]⟩) (hl : ¬ IsLeaf op := by decide) :
    rd c.pool (offs st.pool i) = some (uv (hdrW ⟨op, #[a, b, d]⟩)) ∧
    rd c.pool (offs st.pool i + 1) = some (uv (offs st.pool a)) ∧
    rd c.pool (offs st.pool i + 2) = some (uv (offs st.pool b)) ∧
    rd c.pool (offs st.pool i + 3) = some (uv (offs st.pool d)) :=
  ⟨hc.rdHdr hn, hc.rdArg hn hl (k := 0) (by simp), hc.rdArg hn hl (k := 1) (by simp),
    hc.rdArg hn hl (k := 2) (by simp)⟩

/-- Cells of an n-ary node: the header, its arity field, and argument `k` at `p + 1 + k`. -/
theorem CoreInv.rdN (hc : CoreInv posOf c st) {i : Nat} {op : Op} {args : Array Nat}
    (hn : st.pool[i]? = some ⟨op, args⟩) (hl : ¬ IsLeaf op := by decide) :
    rd c.pool (offs st.pool i) = some (uv (hdrW ⟨op, args⟩)) ∧
    (BitVec.ofNat 32 (hdrW ⟨op, args⟩) >>> 8 &&& 255#32 = BitVec.ofNat 32 args.size) ∧
    ∀ (k : Nat) (hk : k < args.size),
      rd c.pool (offs st.pool i + 1 + k) = some (uv (offs st.pool args[k])) := by
  refine ⟨hc.rdHdr hn, ?_, fun k hk => hc.rdArg hn hl hk⟩
  rw [hdr_len_bv (hc.rep.fits i _ hn), tailLen_of_not_leaf hl]

/-! ### The shape of a node, from its operator

After a header test has established `hop : n.op = .eq` (say),
`obtain ⟨a, b, rfl, ha, hb⟩ := hc.args2 hn hop` replaces `n` by `⟨.eq, #[a, b]⟩`. -/

theorem CoreInv.args1 (hc : CoreInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hf : fixedArity op = true := by rfl)
    (hm : minArity op = 1 := by rfl) : ∃ a, n = ⟨op, #[a]⟩ ∧ a < st.pool.size := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  obtain ⟨a, rfl⟩ := array_eq_one (a := args) (by rw [ht.fixedArity hf, hm])
  exact ⟨a, rfl, ht.args_lt a (by simp)⟩

theorem CoreInv.args2 (hc : CoreInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hf : fixedArity op = true := by rfl)
    (hm : minArity op = 2 := by rfl) :
    ∃ a b, n = ⟨op, #[a, b]⟩ ∧ a < st.pool.size ∧ b < st.pool.size := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  obtain ⟨a, b, rfl⟩ := array_eq_two (a := args) (by rw [ht.fixedArity hf, hm])
  exact ⟨a, b, rfl, ht.args_lt a (by simp), ht.args_lt b (by simp)⟩

theorem CoreInv.args3 (hc : CoreInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hf : fixedArity op = true := by rfl)
    (hm : minArity op = 3 := by rfl) :
    ∃ a b d, n = ⟨op, #[a, b, d]⟩ ∧ a < st.pool.size ∧ b < st.pool.size ∧ d < st.pool.size := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  obtain ⟨a, b, d, rfl⟩ := array_eq_three (a := args) (by rw [ht.fixedArity hf, hm])
  exact ⟨a, b, d, rfl, ht.args_lt a (by simp), ht.args_lt b (by simp), ht.args_lt d (by simp)⟩

/-- An n-ary node: `obtain ⟨args, rfl, hsz, hmin, hargs⟩ := hc.argsN hn hop`. -/
theorem CoreInv.argsN (hc : CoreInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n)
    {op : Op} (hop : n.op = op) (hl : ¬ IsLeaf op := by decide) :
    ∃ args, n = ⟨op, args⟩ ∧ args.size ≤ 255 ∧ minArity op ≤ args.size ∧
      ∀ (k : Nat) (hk : k < args.size), args[k] < st.pool.size := by
  obtain ⟨op', args⟩ := n
  simp only at hop; subst hop
  have ht := hc.ok.typed hn
  have hf := (hc.rep.fits i _ hn).tailLen
  rw [tailLen_of_not_leaf hl] at hf
  exact ⟨args, rfl, by simp only at hf; omega, ht.minArity, fun k hk => ht.args_lt _ (by simp)⟩

/-- The type of a node, as `ty_of` computes it from the header. -/
theorem CoreInv.tyOf (hc : CoreInv posOf c st) {i : Nat} {n : Node} (hn : st.pool[i]? = some n) :
    ∃ t, st.tys[i]? = some t ∧ tyOfB (BitVec.ofNat 32 (hdrW n)) = BitVec.ofNat 32 (tyW t) ∧
      TyFits t := by
  have hf := hc.rep.fits i n hn
  obtain ⟨t, ht, he, hfit⟩ := hc.ok.tyOfM_hdrW hn hf
  exact ⟨t, ht, by rw [tyOfB_eq, bv_toNat_ofNat (hdrW_lt hf), he], hfit⟩

end idsC

/-! ## 4. The rule context

`hR : RCtx W X c0 prems params c st` is everything a rule knows about the current C
state `c` and Lean state `st`: the invariant, the premise buffer, the parameter words,
and what has been left alone since the rule was entered (in state `c0`).  A rule proof
keeps exactly two hypotheses about the current state, `h : Holds …` and `hR`; every
builder call returns new ones. -/

structure RCtx (W : World) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem) (st : VSt) :
    Prop where
  inv : RInv W X c st
  prem : PremsAt c st prems
  par : ParamsAt W c params
  frame : StepFrame c0 c

section wevInv
variable {W : World} {X : Ctx} {c0 c : CMem} {posOf : Nat → Nat} {st : VSt}
  {prems params : List Nat} {wk er : BitVec 32} {vl : BitVec 64}

theorem VInv.wev (h : VInv posOf c st) : VInv posOf (c.wev wk er vl) st :=
  ⟨h.cinv.wev, h.fitsAll⟩

theorem RInv.wev (h : RInv W X c st) : RInv W X (c.wev wk er vl) st :=
  ⟨h.core.wev, h.poolPtr, h.ttNode, h.ffNode, h.tt, h.ff, h.goal, h.proofPtr, h.nexpr,
    h.nexprBound, h.ei, h.eiOut, h.premPtr, h.premSize, h.premCells, h.floor⟩

theorem RCtx.wev (hR : RCtx W X c0 prems params c st) :
    RCtx W X c0 prems params (c.wev wk er vl) st :=
  ⟨hR.inv.wev, hR.prem, hR.par, ⟨hR.frame.facts, hR.frame.factsPtr, hR.frame.flen,
    hR.frame.fcap, hR.frame.proof, hR.frame.nexpr, hR.frame.lr, hR.frame.lrPtr, hR.frame.lo,
    hR.frame.live⟩⟩

end wevInv

/-- The block of the pool (when it is allocated). -/
def poolB (c : CMem) : Nat := match c.k.pool with | some (b, _) => b | none => 0
/-- The block of the premise buffer. -/
def premB (c : CMem) : Nat := match c.k.prem with | some (b, _) => b | none => 0
/-- The offset of the current step's parameters in the proof block. -/
def parO (c : CMem) : Nat := match c.k.par with | some (_, o) => o | none => 0
/-- The block of the scratch stack. -/
def stkB (c : CMem) : Nat := match c.k.stk with | some (b, _) => b | none => 0

section rctx
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {m : Mem}

theorem RCtx.core (hR : RCtx W X c0 prems params c st) : VInv X.posOf c st := hR.inv.core

/-! ### Pointers -/

theorem RCtx.pool_eq (hR : RCtx W X c0 prems params c st) : c.k.pool = some (poolB c, 0) := by
  obtain ⟨b, hb⟩ := hR.inv.poolPtr
  simp [poolB, hb]

theorem RCtx.prem_eq (hR : RCtx W X c0 prems params c st) : c.k.prem = some (premB c, 0) := by
  obtain ⟨b, hb⟩ := hR.inv.premPtr
  simp [premB, hb]

theorem RCtx.par_eq (hR : RCtx W X c0 prems params c st) : c.k.par = some (W.pb, parO c) := by
  obtain ⟨_, o, ho, _⟩ := hR.par
  simp [parO, ho]

/-- Reading the pool block (the side condition is closed by `rule_disch` from `hR`). -/
theorem Holds.ld_poolB (h : Holds W m sb c) (hp : c.k.pool = some (poolB c, 0)) (i : Nat) :
    m.loadArr (poolB c) i = rd c.pool i := h.rd_pool hp i

/-- Reading the premise block. -/
theorem Holds.ld_premB (h : Holds W m sb c) (hp : c.k.prem = some (premB c, 0)) (i : Nat) :
    m.loadArr (premB c) i = rd c.prem i := h.rd_prem hp i

/-- Reading the scratch stack. -/
theorem Holds.ld_stkB (h : Holds W m sb c) (hp : c.k.stk = some (stkB c, 0)) (i : Nat) :
    m.loadArr (stkB c) i = rd c.stk i := h.rd_stk hp i

/-! ### Premises and parameters -/

theorem RCtx.prem_lt (hR : RCtx W X c0 prems params c st) {j : Nat} (hj : j < prems.length) :
    st.lv prems[j] := (hR.prem.2 j _ (List.getElem?_eq_getElem hj)).1

/-- `st->prem[j]`. -/
theorem RCtx.rd_prem (hR : RCtx W X c0 prems params c st) {j : Nat} (hj : j < prems.length) :
    rd c.prem j = some (uv (st.id prems[j])) :=
  rd_u32 (hR.prem.2 j _ (List.getElem?_eq_getElem hj)).2

theorem RCtx.par_lt (hR : RCtx W X c0 prems params c st) {j : Nat} (hj : j < params.length) :
    params[j] < 4294967296 := by
  obtain ⟨_, o, _, _, hc⟩ := hR.par
  exact (hc j _ (List.getElem?_eq_getElem hj)).1

/-- `st->par[j]`. -/
theorem RCtx.rd_par (hR : RCtx W X c0 prems params c st) {j : Nat} (hj : j < params.length) :
    rd c.proof (parO c + j) = some (uv params[j]) := by
  obtain ⟨_, o, ho, _, hc⟩ := hR.par
  have : parO c = o := by simp [parO, ho]
  rw [this]
  exact rd_u32 (hc j _ (List.getElem?_eq_getElem hj)).2

/-- `st->par[0]` (`simp` has turned `parO c + 0` into `parO c`). -/
theorem RCtx.rd_par0 (hR : RCtx W X c0 prems params c st) (hj : 0 < params.length) :
    rd c.proof (parO c) = some (uv params[0]) := hR.rd_par hj

/-- Bounds for a known premise list: `have hp := hR.prems1`, `have ⟨hp, hq⟩ := hR.prems2`. -/
theorem RCtx.prems1 {p : Nat} (hR : RCtx W X c0 [p] params c st) : st.lv p :=
  hR.prem_lt (j := 0) (by simp)

theorem RCtx.prems2 {p q : Nat} (hR : RCtx W X c0 [p, q] params c st) :
    st.lv p ∧ st.lv q :=
  ⟨hR.prem_lt (j := 0) (by simp), hR.prem_lt (j := 1) (by simp)⟩

theorem RCtx.prems3 {p q r : Nat} (hR : RCtx W X c0 [p, q, r] params c st) :
    st.lv p ∧ st.lv q ∧ st.lv r :=
  ⟨hR.prem_lt (j := 0) (by simp), hR.prem_lt (j := 1) (by simp), hR.prem_lt (j := 2) (by simp)⟩

/-- Bounds for a known parameter list. -/
theorem RCtx.params1 {x : Nat} (hR : RCtx W X c0 prems [x] c st) : x < 4294967296 :=
  hR.par_lt (j := 0) (by simp)

theorem RCtx.params2 {x y : Nat} (hR : RCtx W X c0 prems [x, y] c st) :
    x < 4294967296 ∧ y < 4294967296 :=
  ⟨hR.par_lt (j := 0) (by simp), hR.par_lt (j := 1) (by simp)⟩

/-! ### The built-in nodes and the goal -/

theorem RCtx.tt_lt (hR : RCtx W X c0 prems params c st) : st.lv X.bi.tt := hR.inv.tt.1

theorem RCtx.ff_lt (hR : RCtx W X c0 prems params c st) : st.lv X.bi.ff := hR.inv.ff.1

theorem RCtx.goal_lt (hR : RCtx W X c0 prems params c st) : st.lv X.goal := hR.inv.goal.1

/-- `st->tt`. -/
theorem RCtx.tt_eq (hR : RCtx W X c0 prems params c st) :
    c.k.tt = BitVec.ofNat 32 (st.id X.bi.tt) := id_of_toNat hR.inv.tt.2

/-- `st->ff`. -/
theorem RCtx.ff_eq (hR : RCtx W X c0 prems params c st) :
    c.k.ff = BitVec.ofNat 32 (st.id X.bi.ff) := id_of_toNat hR.inv.ff.2

/-- `st->goal`. -/
theorem RCtx.goal_eq (hR : RCtx W X c0 prems params c st) :
    c.k.goal = BitVec.ofNat 32 (st.id X.goal) := id_of_toNat hR.inv.goal.2

end rctx

/-! ## 5. The postcondition of a rule, and entering a rule

`RuleQ` is the postcondition of the body of a rule function, as a named definition
(so that `simp` leaves it alone).  The only way out of a rule is `return e`, and what
has to hold then is `RuleRet … r s`, where `r` is the returned word. -/

/-- What must hold when a rule returns the word `r` in state `s'`. -/
def RuleRet (W : World) (sb : Nat) (c0 : CMem) (X : Ctx) (res : Option (St × Nat))
    (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧
    (r ≠ noid → ∃ (st' : VSt) (f : Nat), res = some (st'.toSt, f) ∧ RInv W X c' st' ∧ st'.lv f ∧
      r.toNat = st'.id f ∧ StepFrame c0 c')

/-- The postcondition of a rule body: it returns a `u32` satisfying `RuleRet`. -/
def RuleQ (W : World) (sb : Nat) (c0 : CMem) (X : Ctx) (res : Option (St × Nat)) : (Post prog State) :=
  fun o _ s' =>
    match o with
    | .ret (some (.u32 r)) => RuleRet W sb c0 X res r s'
    | _ => False

/-- Entering a rule: from `RuleSpec (State := State)` to a `WP` for the body with postcondition `RuleQ`.
Used by `rule_begin`. -/
theorem RuleSpec.intro {name : String} {fn : Fn}
    {rule : Ctx → St → List Nat → List Nat → Option (St × Nat)}
    (hf : Vbcf.prog.findFn name = some fn)
    (hp : fn.params = [("st", .ptr (.struct "ck")), ("np", .u32), ("na", .u32)])
    (hr : fn.ret = some .u32)
    (H : ∀ (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : VSt) (prems params : List Nat)
        (s : (KernelState prog State)),
      Holds W s.mem sb c → RCtx W X c prems params c st → c.k.sp = 0#32 →
      prems.length ≤ 255 → params.length ≤ 255 →
      WP Vbcf.prog fn.body (RuleQ W sb c X (rule X st prems params))
        ([("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv prems.length),
          ("na", .u32, uv params.length)] ++ initLocals fn.locals) s) :
    RuleSpec (State := State) name rule := by
  intro W sb c X st prems params
  apply FnSpec.intro hf
  rintro vs s ⟨rfl, h, hinv, hprem, hpar, hsp⟩
  refine ⟨[("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv prems.length),
    ("na", .u32, uv params.length)], ?_, ?_⟩
  · rw [hp]; simp [bindParams, Mem.hasTy_ptr h.ck rfl]
  · refine WP.mono (H W sb c X st prems params s h
      ⟨hinv, hprem, hpar, StepFrame.refl c⟩ hsp hprem.1 hpar.1) ?_
    intro o env' s' hq
    rw [hr]
    unfold RuleQ at hq
    split at hq
    · rename_i r
      obtain ⟨c', h', hres⟩ := hq
      exact ⟨rfl, c', r, rfl, h', hres⟩
    · exact hq.elim

/-- `Q` is a postcondition under which `return r` needs `R r s`.  Instances: `RuleQ`
itself, and `LoopQ I Q` (the body of a loop inside a rule).  The statement lemmas
below are stated for any such `Q`, so they work the same inside and outside loops. -/
class RetsTo {P : Prog} (Q : (Post P State)) (R : outParam (BitVec 32 → (KernelState P State) → Prop)) : Prop where
  ret : ∀ (r : BitVec 32) (env : Env) (s : (KernelState P State)), R r s → Q (.ret (some (.u32 r))) env s

instance {W : World} {sb : Nat} {c0 : CMem} {X : Ctx} {res : Option (St × Nat)} :
    RetsTo (State := State) (RuleQ W sb c0 X res) (RuleRet W sb c0 X res) := ⟨fun _ _ _ h => h⟩

/-- The postcondition of a loop body with invariant `I` inside a function with
postcondition `Q`.  (`break` is not supported; use `WP.while` directly for that.) -/
def LoopQ {P : Prog} (I : Env → (KernelState P State) → Prop) (Q : (Post P State)) : (Post P State) := fun o env' s' =>
  match o with
  | .normal => I env' s'
  | .brk => False
  | .ret r => Q (.ret r) env' s'

instance {P : Prog} {I : Env → (KernelState P State) → Prop} {Q : (Post P State)} {R : BitVec 32 → (KernelState P State) → Prop} [RetsTo Q R] :
    RetsTo (LoopQ I Q) R := ⟨fun r env s h => RetsTo.ret (Q := Q) r env s h⟩

section ret
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt} {sb : Nat}
  {res : Option (St × Nat)} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)}

/-- Returning `NOID` is always allowed. -/
theorem RuleRet.fail (h : Holds W s.mem sb c) : RuleRet W sb c0 X res 4294967295#32 s :=
  ⟨c, h, fun hne => absurd rfl hne⟩

/-- Returning the id of node `f`, when the Lean rule gives `(st, f)`. -/
theorem RCtx.ret (hR : RCtx W X c0 prems params c st) (h : Holds W s.mem sb c) {f : Nat}
    (hf : st.lv f) (hres : res = some (st.toSt, f)) :
    RuleRet W sb c0 X res (BitVec.ofNat 32 (st.id f)) s :=
  ⟨c, h, fun _ => ⟨st, f, hres, hR.inv, hf, hR.core.id_toNat hf, hR.frame⟩⟩

/-- `return NOID;` -/
theorem WP.rule_fail {nm : String} [RetsTo Q (RuleRet W sb c0 X res)] (h : Holds W s.mem sb c) :
    WP Vbcf.prog (.ret (some (.named nm 4294967295#32))) Q env s := by
  apply WP.ret
  simp only [evalE]
  exact RetsTo.ret _ _ _ (RuleRet.fail h)

/-- `return e;` -/
theorem WP.rule_ret {e : Expr} {R : BitVec 32 → (KernelState prog State) → Prop} [RetsTo Q R]
    (H : match evalE Vbcf.prog env s.mem e with
      | some (.u32 r) => R r s
      | _ => False) :
    WP Vbcf.prog (.ret (some e)) Q env s := by
  apply WP.ret
  split at H
  · rename_i r hr
    rw [hr]; exact RetsTo.ret _ _ _ H
  · exact H.elim

/-- `if (cond) { return NOID; } rest` -/
theorem WP.rule_guard {cond : Expr} {rest : Stmt} {nm : String}
    [RetsTo Q (RuleRet W sb c0 X res)] (h : Holds W s.mem sb c)
    (H : match evalE Vbcf.prog env s.mem cond with
      | some (.u32 v) => v = 0 → WP Vbcf.prog rest Q env s
      | _ => False) :
    WP Vbcf.prog (.seq (.ite cond (.ret (some (.named nm 4294967295#32))) .skip) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun _ => ?_, fun he => ?_⟩
    · apply WP.ret
      simp only [evalE]
      exact RetsTo.ret (Q := Q) _ _ _ (RuleRet.fail h)
    · apply WP.skip
      exact H he
  · exact H.elim

/-- The arity gate `if (np != K || na != L) { return NOID; } rest`. -/
theorem WP.rule_arity {rest : Stmt} {nm : String} {k l : BitVec 32} {np na : Nat}
    [RetsTo Q (RuleRet W sb c0 X res)] (h : Holds W s.mem sb c)
    (enp : env.get "np" = some (uv np)) (ena : env.get "na" = some (uv na))
    (hnp : np ≤ 255) (hna : na ≤ 255)
    (H : np = k.toNat → na = l.toNat → WP Vbcf.prog rest Q env s) :
    WP Vbcf.prog (.seq (.ite (.lor (.bin .ne (.var "np") (.lit32 k)) (.bin .ne (.var "na") (.lit32 l)))
      (.ret (some (.named nm 4294967295#32))) .skip) rest) Q env s := by
  apply WP.rule_guard h
  have e1 : (BitVec.ofNat 32 np = k) ↔ np = k.toNat := ofNat_eq_iff (by omega)
  have e2 : (BitVec.ofNat 32 na = l) ↔ na = l.toNat := ofNat_eq_iff (by omega)
  simp only [evalE, enp, ena, evalBin, evalArith]
  by_cases h1 : BitVec.ofNat 32 np = k
  · by_cases h2 : BitVec.ofNat 32 na = l
    · simp [Val.ofBool, h1, h2]
      exact H (e1.mp h1) (e2.mp h2)
    · simp [Val.ofBool, h1, h2]
  · simp [Val.ofBool, h1]

end ret

/-- The shape of a list of known length: `LenShape 2 l` is `∃ a b, l = [a, b]`. -/
def LenShape {α : Type} : Nat → List α → Prop
  | 0, l => l = []
  | 1, l => ∃ a, l = [a]
  | 2, l => ∃ a b, l = [a, b]
  | 3, l => ∃ a b c, l = [a, b, c]
  | 4, l => ∃ a b c d, l = [a, b, c, d]
  | _, _ => True

theorem len_shape {α : Type} {l : List α} (k : Nat) (h : l.length = k) : LenShape k l := by
  subst h
  match l with
  | [] => exact rfl
  | [a] => exact ⟨a, rfl⟩
  | [a, b] => exact ⟨a, b, rfl⟩
  | [a, b, c] => exact ⟨a, b, c, rfl⟩
  | [a, b, c, d] => exact ⟨a, b, c, d, rfl⟩
  | _ :: _ :: _ :: _ :: _ :: _ => exact trivial

/-! ### Statements that are not specific to rules -/

/-- `x = e; rest` -/
theorem WP.assign_seq {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {x : Var} {e : Expr}
    {rest : Stmt}
    (H : match evalE P env s.mem e with
      | none => False
      | some v =>
        match env.assign s.mem x v with
        | none => False
        | some env' => WP P rest Q env' s) :
    WP P (.seq (.assign x e) rest) Q env s := by
  apply WP.seq
  apply WP.assign
  split at H
  · exact H.elim
  · rename_i v hv
    rw [hv]; dsimp only
    split at H
    · exact H.elim
    · rename_i env' he
      rw [he]; exact H

/-- `x = e;` as the last statement of a loop body: the invariant must hold again. -/
theorem WP.assign_loop {P : Prog} {Q : (Post P State)} {I : Env → (KernelState P State) → Prop} {env : Env} {s : (KernelState P State)}
    {x : Var} {e : Expr}
    (H : match evalE P env s.mem e with
      | none => False
      | some v =>
        match env.assign s.mem x v with
        | none => False
        | some env' => I env' s) :
    WP P (.assign x e) (LoopQ I Q) env s := by
  apply WP.assign
  split at H
  · exact H.elim
  · rename_i v hv
    rw [hv]; dsimp only
    split at H
    · exact H.elim
    · rename_i env' he
      rw [he]; exact H

/-- `if (cond) { a } rest` where `a` may `return`: the branch is proved with the
postcondition `LoopQ (WP rest) Q`, i.e. falling off its end means running `rest`. -/
theorem WP.ite_seq {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {c : Expr} {a rest : Stmt}
    (H : match evalE P env s.mem c with
      | some (.u32 v) =>
        (v ≠ 0 → WP P a (LoopQ (fun env' s' => WP P rest Q env' s') Q) env s) ∧
        (v = 0 → WP P rest Q env s)
      | _ => False) :
    WP P (.seq (.ite c a .skip) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun hne => WP.mono (H.1 hne) ?_, fun he => ?_⟩
    · intro o env' s' hq
      cases o with
      | normal => exact hq
      | brk => exact hq.elim
      | ret r => exact hq
    · apply WP.skip
      exact H.2 he
  · exact H.elim

/-- `while (cond) body; rest` with invariant `I`.  Inside the body the postcondition is
`LoopQ I Q`: falling off the end must re-establish `I`, and `return` is as in `Q`. -/
theorem WP.loop_seq {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {cond : Expr}
    {body rest : Stmt} (I : Env → (KernelState P State) → Prop) (h0 : I env s)
    (hstep : ∀ env s, I env s →
      match evalE P env s.mem cond with
      | some (.u32 v) => (v = 0 → WP P rest Q env s) ∧ (v ≠ 0 → WP P body (LoopQ I Q) env s)
      | _ => False) :
    WP P (.seq (.while cond body) rest) Q env s := by
  apply WP.seq
  apply WP.while I h0
  intro env s hI
  have H := hstep env s hI
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨H.1, fun hne => WP.mono (H.2 hne) ?_⟩
    intro o env' s' hq
    cases o with
    | normal => exact hq
    | brk => exact hq.elim
    | ret r => exact hq
  · exact H.elim

/-- Weakening the postcondition of a function specification. -/
theorem FnSpec.post_mono {P : Prog} {f : String} {pre : List EmbC.Val → (KernelState P State) → Prop}
    {post post' : List EmbC.Val → (KernelState P State) → Option EmbC.Val → (KernelState P State) → Prop}
    (h : FnSpec (State := State) P f pre post) (hp : ∀ vs s rv s', pre vs s → post vs s rv s' → post' vs s rv s') :
    FnSpec (State := State) P f pre post' := by
  intro fuel vs s hpre
  have := h fuel vs s hpre
  split <;> simp_all

/-- `x = f(args); rest` for a function with a proved specification. -/
theorem WP.call_seq {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {x : Var} {f : String}
    {args : List Expr} {rest : Stmt} {vs : List EmbC.Val}
    {pre : List EmbC.Val → (KernelState P State) → Prop} {post : List EmbC.Val → (KernelState P State) → Option EmbC.Val → (KernelState P State) → Prop}
    (hspec : FnSpec (State := State) P f pre post)
    (hargs : evalArgs P env s.mem args = some vs) (hpre : pre vs s)
    (H : ∀ rv s', post vs s rv s' →
      match assignDst env s'.mem (some x) rv with
      | none => False
      | some env' => WP P rest Q env' s') :
    WP P (.seq (.call (some x) f args) rest) Q env s := by
  apply WP.seq
  apply WP.call hspec
  rw [hargs]
  exact ⟨hpre, H⟩

/-! ## 6. Calls

### Carrying the rule context across a call -/

section frames
variable {W : World} {X : Ctx} {c0 c c' : CMem} {prems params : List Nat} {st st' : VSt}
  {sb : Nat} {m : Mem}

/-- A change of the scratch stack only (`push`) keeps the rule context
(from `RInv.stkFrame` and friends in `Builders1`). -/
theorem RCtx.after_push (hR : RCtx W X c0 prems params c st) (hfr : StkFrame c c')
    (hok : StkOK c') : RCtx W X c0 prems params c' st where
  inv := hR.inv.stkFrame hfr hok
  prem := hR.prem.stkFrame hfr
  par := hR.par.stkFrame hfr
  frame := hR.frame.trans (StepFrame.ofStkFrame hfr)

/-- A successful builder call keeps the rule context, for the extended view
(from `RInv.build` and friends in `Builders1`). -/
theorem RCtx.after_build (hR : RCtx W X c0 prems params c st) (h' : Holds W m sb c')
    (hfr : PoolFrame c c') (hc : VInv X.posOf c' st') (he : VExt st st') :
    RCtx W X c0 prems params c' st' where
  inv := hR.inv.build h' hfr hc.cinv he hc.fitsAll
  prem := hR.prem.ext hfr he
  par := hR.par.frame hfr
  frame := hR.frame.trans (StepFrame.ofPoolFrame hfr)

/-- The scratch stack holds the ids of the live Lean indices `is` from `base` on. -/
def StkIds (c : CMem) (st : VSt) (base : Nat) (is : List Nat) : Prop :=
  ∀ (j : Nat) (i : Nat), is[j]? = some i → st.lv i ∧ U c.stk (base + j) (st.id i)

/-- Ids on the scratch stack survive a builder call. -/
theorem StkIds.ext {base : Nat} {is : List Nat} (hids : StkIds c st base is)
    (hext : VExt st st') (hs : c'.stk = c.stk) : StkIds c' st' base is := by
  intro j i hj
  obtain ⟨hi, hU⟩ := hids j i hj
  exact ⟨hext.lt hi, by rw [hs, hext.id hi]; exact hU⟩

/-- The C-side form (`mkn`'s precondition). -/
theorem StkIds.toC {base : Nat} {is : List Nat} (hids : StkIds c st base is) :
    StkIdsC c st.cs base (is.map st.σ) := by
  intro j x hj
  rw [List.getElem?_map] at hj
  cases hji : is[j]? with
  | none => rw [hji] at hj; cases hj
  | some i =>
    rw [hji] at hj
    simp only [Option.map, Option.some.injEq] at hj
    subst hj
    obtain ⟨hi, hU⟩ := hids j i hji
    exact ⟨st.σ_lt hi, hU⟩

/-- From the C-side form, for live indices. -/
theorem StkIds.ofC {base : Nat} {is : List Nat} (hids : StkIdsC c st.cs base (is.map st.σ))
    (hlv : ∀ a ∈ is, st.lv a) : StkIds c st base is := by
  intro j i hj
  have hj' : (is.map st.σ)[j]? = some (st.σ i) := by rw [List.getElem?_map, hj]; rfl
  exact ⟨hlv i (List.mem_of_getElem? hj), (hids j _ hj').2⟩

theorem StkIds.lv {base : Nat} {is : List Nat} (hids : StkIds c st base is) :
    ∀ a ∈ is, st.lv a := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  exact (hids j _ (List.getElem?_eq_getElem hj)).1

/-- `StkIds` only looks at the cells `base .. base + is.length`. -/
theorem StkIds.congr {base : Nat} {is : List Nat} (h : StkIds c st base is)
    (hc : ∀ j, j < is.length → c'.stk[base + j]? = c.stk[base + j]?) : StkIds c' st base is := by
  intro j i hj
  obtain ⟨hi, hu⟩ := h j i hj
  refine ⟨hi, ?_⟩
  unfold U; rw [hc j (lt_length_of_getElem? hj)]; exact hu

/-- In particular it survives pushes above it. -/
theorem StkIds.of_low {base sp : Nat} {is : List Nat}
    (h : StkIds c st base is) (hsp : base + is.length ≤ sp)
    (hc : ∀ j, j < sp → c'.stk[j]? = c.stk[j]?) : StkIds c' st base is :=
  h.congr (fun j hj => hc _ (by omega))

theorem StkIds.nil (c : CMem) (st : VSt) (base : Nat) : StkIds c st base [] := by
  intro j i hj; simp at hj

theorem StkIds.append {base : Nat} {is js : List Nat}
    (h : StkIds c st base is) (h' : StkIds c st (base + is.length) js) :
    StkIds c st base (is ++ js) := by
  intro j i hj
  by_cases hlt : j < is.length
  · rw [List.getElem?_append_left hlt] at hj; exact h j i hj
  · rw [List.getElem?_append_right (by omega)] at hj
    have := h' (j - is.length) i hj
    rwa [show base + is.length + (j - is.length) = base + j by omega] at this

theorem StkIds.single {base i : Nat} (hi : st.lv i)
    (hu : U c.stk base (st.id i)) : StkIds c st base [i] := by
  intro j x hj
  match j with
  | 0 => simp at hj; subst hj; exact ⟨hi, hu⟩
  | j + 1 => simp at hj

end frames

/-! ### Builder calls

Every builder (`mk_eq`, `mk_not`, `mk1`…`mk3`, `mkn`, `mk0`, `mkval`) has a lemma
`WP.rule_<name>` for the statement `x = <name>(st, …); rest`.  Its hypothesis is: the
arguments evaluate to the expected words (closed by `rule_simp`), and the rest of the
function is correct for every outcome `Built … c' r` of the call.  The C function works
on the view's C-side state; `VInv.push_tr` carries its result back to the Lean state. -/

/-- The outcome of a builder call made in C state `c`, view `st`: it returned
`r` and left C state `c'`.  Either `r` is `NOID`, or the Lean builder succeeded
(`P st' i`), the rule context holds for `c'` and an extension `st'` of the view, the
scratch stack is untouched, and `r` is the id of `i`. -/
def Built (W : World) (X : Ctx) (c0 : CMem) (prems params : List Nat) (c : CMem) (st : VSt)
    (P : St → Nat → Prop) (c' : CMem) (r : BitVec 32) : Prop :=
  r = 4294967295#32 ∨
  ∃ (st' : VSt) (i : Nat), P st'.toSt i ∧ RCtx W X c0 prems params c' st' ∧ VExt st st' ∧
    (c'.stk = c.stk ∧ c'.k.sp = c.k.sp) ∧ st'.lv i ∧
    r = BitVec.ofNat 32 (st'.id i)

-- `BuildPost`, the common shape of the builders' postconditions, is in `Builders1.lean`.

section build
variable {W : World} {X : Ctx} {c0 c c' : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {P : St → Nat → Prop} {r : BitVec 32}
  {res : Option (St × Nat)}

/-- After `if (r == NOID) { return NOID; }`: the builder succeeded. -/
theorem Built.ok (hB : Built W X c0 prems params c st P c' r) (hne : ¬ r = 4294967295#32) :
    ∃ (st' : VSt) (i : Nat), P st'.toSt i ∧ RCtx W X c0 prems params c' st' ∧ VExt st st' ∧
      (c'.stk = c.stk ∧ c'.k.sp = c.k.sp) ∧ st'.lv i ∧
      r = BitVec.ofNat 32 (st'.id i) := by
  rcases hB with h | h
  · exact absurd h hne
  · exact h

/-- `return r;` right after the builder call: it is enough that the Lean rule returns
what the Lean builder returns. -/
theorem Built.ret (hB : Built W X c0 prems params c st P c' r) (h : Holds W s.mem sb c')
    (hres : ∀ st' i, P st' i → res = some (st', i)) : RuleRet W sb c0 X res r s := by
  rcases hB with rfl | ⟨st', i, hP, hR, -, -, hi, rfl⟩
  · exact RuleRet.fail h
  · exact hR.ret h hi (hres st'.toSt i hP)

/-- The generic builder call.  `htr` carries the C-side result back to the view. -/
theorem WP.rule_build {f : String} {args : List Expr} {x : Var} {rest : Stmt} {vs : List EmbC.Val}
    {pre : List EmbC.Val → (KernelState prog State) → Prop}
    {post : List EmbC.Val → (KernelState prog State) → Option EmbC.Val → (KernelState prog State) → Prop} {P' : St → Nat → Prop}
    (hspec : FnSpec (State := State) Vbcf.prog f pre post)
    (hR : RCtx W X c0 prems params c st)
    (hpost : ∀ rv s', post vs s rv s' → BuildPost W sb c X.posOf st.cs P' rv s')
    (htr : ∀ c' cs' x, CoreInv X.posOf c' cs' → P' cs' x →
      ∃ (st' : VSt) (i : Nat), P st'.toSt i ∧ st'.lv i ∧ st'.id i = offs cs'.pool x ∧
        VExt st st' ∧ VInv X.posOf c' st')
    (hargs : evalArgs Vbcf.prog env s.mem args = some vs) (hpre : pre vs s)
    (H : ∀ s' c' r, Holds W s'.mem sb c' → Built W X c0 prems params c st P c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) f args) rest) Q env s := by
  apply WP.call_seq hspec hargs hpre
  intro rv s' hp
  obtain ⟨c', r, rfl, h', hfr, hcase⟩ := hpost rv s' hp
  refine H s' c' r h' ?_
  rcases hcase with ⟨hr, -⟩ | ⟨cs', x', hPi, hc, hri, -⟩
  · exact Or.inl hr
  · obtain ⟨st', i, hP, hi, hid, he, hv⟩ := htr c' cs' x' hc hPi
    exact Or.inr ⟨st', i, hP, hR.after_build h' hfr hv he, he, ⟨hfr.stk, hfr.sp⟩, hi,
      by rw [hid]; exact id_of_toNat hri⟩

/-- `htr` for a builder that interns the renamed node `n`. -/
theorem push_htr (hR : RCtx W X c0 prems params c st) {n : Node} (hargs : ∀ a ∈ n.args, st.lv a) :
    ∀ c' cs' x, CoreInv X.posOf c' cs' → pushNode st.cs (n.ren st.σ) = some (cs', x) →
      ∃ (st' : VSt) (i : Nat), pushNode st.toSt n = some (st'.toSt, i) ∧ st'.lv i ∧
        st'.id i = offs cs'.pool x ∧ VExt st st' ∧ VInv X.posOf c' st' :=
  fun _ _ _ hc hp => hR.core.push_tr hargs hp hc

/-- `htr` for a builder called with a raw header `hd` and the live arguments `is`. -/
theorem raw_htr (hR : RCtx W X c0 prems params c st) {hd : Nat} {is : List Nat}
    (hlv : ∀ a ∈ is, st.lv a) :
    ∀ c' cs' x, CoreInv X.posOf c' cs' →
      (∃ n', hdrW n' = hd + (is.map st.σ).length * 256 ∧ Fits X.posOf n' ∧
        n'.args = (is.map st.σ).toArray ∧ pushNode st.cs n' = some (cs', x)) →
      ∃ (st' : VSt) (i : Nat), (∃ n, hdrW n = hd + is.length * 256 ∧ Fits X.posOf n ∧
          n.args = is.toArray ∧ pushNode st n = some (st'.toSt, i)) ∧ st'.lv i ∧
        st'.id i = offs cs'.pool x ∧ VExt st st' ∧ VInv X.posOf c' st' := by
  rintro c' cs' x hc ⟨n', hh, hf, ha, hp⟩
  have hren : (⟨n'.op, is.toArray⟩ : Node).ren st.σ = n' := by
    rw [ren_list, ← ha]
  obtain ⟨st', i, hpush, hi, hid, he, hv⟩ :=
    push_htr hR (n := ⟨n'.op, is.toArray⟩) (by simpa using hlv) c' cs' x hc
      (by rw [hren]; exact hp)
  refine ⟨st', i, ⟨⟨n'.op, is.toArray⟩, ?_, ?_, rfl, hpush⟩, hi, hid, he, hv⟩
  · rw [← hdrW_ren st.σ, hren, hh, List.length_map]
  · rw [← fits_ren (σ := st.σ), hren]; exact hf

end build

/-! ### Headers of built nodes -/

theorem isLeaf_iff_opC {op : Op} :
    IsLeaf op ↔ opC op = 0x18 ∨ opC op = 0x19 ∨ opC op = 0x08 ∨ opC op = 0x09 := by
  cases op <;> simp [IsLeaf, isLeaf, opC]

/-- The header word a builder is called with for operator `op`: code and parameters,
arity bits zero. -/
def opHdr (op : Op) : Nat := opC op + (opLo op + opHi op * 256) * 65536

theorem opHdr_nonLeaf {op : Op} (hl : ¬ IsLeaf op) (hlo : opLo op < 256) (hhi : opHi op < 256) :
    NonLeafHdr (opHdr op) := by
  have h1 := opC_lt op
  rw [isLeaf_iff_opC] at hl
  unfold NonLeafHdr opHdr
  omega

theorem opHdr_lt {op : Op} (hlo : opLo op < 256) (hhi : opHi op < 256) :
    opHdr op < 4294967296 := by
  have h1 := opC_lt op
  unfold opHdr; omega

/-- A fitting node whose header is `opHdr op` plus its arity is an application of `op`. -/
theorem node_of_hdr {posOf : Nat → Nat} {n : Node} {op : Op} {args : Array Nat}
    (hf : Fits posOf n) (hargs : n.args = args) (hh : hdrW n = opHdr op + args.size * 256)
    (hl : ¬ IsLeaf op) (hlo : opLo op < 256) (hhi : opHi op < 256) : n = ⟨op, args⟩ := by
  have _ := hhi
  obtain ⟨op', args'⟩ := n
  simp only at hargs; subst hargs
  have h1 := opC_lt op
  have hc : opC op' = opC op := by
    have := hdrW_code hf
    simp only at this
    rw [← this, hh]; unfold opHdr; omega
  have hl' : ¬ IsLeaf op' := by rw [isLeaf_iff_opC, hc, ← isLeaf_iff_opC]; exact hl
  have hsz : args'.size < 256 := by
    have := hf.tailLen
    rwa [tailLen_of_not_leaf hl'] at this
  have hlo' : opLo op' = opLo op := by
    have := hdrW_lo hf
    simp only at this
    rw [← this, hh]; unfold opHdr; omega
  have hhi' : opHi op' = opHi op := by
    have := hdrW_hi hf
    simp only at this
    rw [← this, hh]; unfold opHdr; omega
  rw [isLeaf_iff_opC] at hl hl'
  have : op' = op := op_eq_of_enc hc hlo' hhi'
    (by rw [opData_eq_zero (by omega) (by omega) (by omega),
      opData_eq_zero (by omega) (by omega) (by omega)])
  rw [this]

/-- Two fitting non-leaf nodes with the same header have the same operator. -/
theorem op_eq_of_hdrW {posOf : Nat → Nat} {n n' : Node} (hf : Fits posOf n) (hf' : Fits posOf n')
    (hl : ¬ IsLeaf n.op) (e : hdrW n = hdrW n') : n.op = n'.op := by
  obtain ⟨hc, -, hlo, hhi⟩ := hdrW_inj hf hf' e
  rw [isLeaf_iff_opC] at hl
  apply op_eq_of_enc hc hlo hhi
  rw [opData_eq_zero (by omega) (by omega) (by omega),
    opData_eq_zero (by omega) (by omega) (by omega)]

/-- A fitting node whose header has a non-leaf code is not a leaf. -/
theorem not_leaf_of_hdrW {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n)
    (h : hdrW n % 256 ≠ 0x18 ∧ hdrW n % 256 ≠ 0x19 ∧ hdrW n % 256 ≠ 0x08 ∧ hdrW n % 256 ≠ 0x09) :
    ¬ IsLeaf n.op := by
  rw [isLeaf_iff_opC, ← hdrW_code hf]; omega

section build2
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {args : List Expr} {rest : Stmt}

/-- `MkPost` in the common shape, keeping the node abstract (header known as a number). -/
theorem MkPost.build {posOf : Nat → Nat} {hd : Nat} {is : List Nat} {rv : Option EmbC.Val}
    {s' : (KernelState prog State)} {cs : St} (hp : MkPost posOf W sb c cs hd is rv s') :
    BuildPost W sb c posOf cs (fun cs' i => ∃ n, hdrW n = hd + is.length * 256 ∧ Fits posOf n ∧
      n.args = is.toArray ∧ pushNode cs n = some (cs', i)) rv s' := by
  obtain ⟨c', r, hrv, h', hfr, hcase⟩ := hp
  refine ⟨c', r, hrv, h', hfr, ?_⟩
  rcases hcase with hc | ⟨n, st', i, hh, hf, ha, hpn, hc, hr, hne⟩
  · exact Or.inl hc
  · exact Or.inr ⟨st', i, ⟨n, hh, hf, ha, hpn⟩, hc, hr, hne⟩

/-- `MkPost` in the common shape, for a known operator. -/
theorem MkPost.build_op {posOf : Nat → Nat} {op : Op} {is : List Nat} {rv : Option EmbC.Val}
    {s' : (KernelState prog State)} {cs : St} (hl : ¬ IsLeaf op) (hlo : opLo op < 256) (hhi : opHi op < 256)
    (hp : MkPost posOf W sb c cs (opHdr op) is rv s') :
    BuildPost W sb c posOf cs (fun cs' i => pushNode cs ⟨op, is.toArray⟩ = some (cs', i)) rv s' := by
  obtain ⟨c', r, hrv, h', hfr, hcase⟩ := hp
  refine ⟨c', r, hrv, h', hfr, ?_⟩
  rcases hcase with hc | ⟨n, st', i, hh, hf, ha, hpn, hc, hr, hne⟩
  · exact Or.inl hc
  · have : n = ⟨op, is.toArray⟩ := node_of_hdr hf ha (by simpa using hh) hl hlo hhi
    exact Or.inr ⟨st', i, this ▸ hpn, hc, hr, hne⟩

/-- `x = mk_eq(st, a, b); rest`, where `a`, `b` evaluate to the ids of `ia`, `ib`. -/
theorem WP.rule_mk_eq (hEq : MkEqSpec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (ia ib : Nat) (hia : st.lv ia)
    (hib : st.lv ib)
    (H : evalArgs Vbcf.prog env s.mem args =
        some [.ptr sb 0, uv (st.id ia), uv (st.id ib)] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st (fun st' i => Bcf.mkEq st ia ib = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mk_eq" args) rest) Q env s :=
  WP.rule_build (hEq W sb c X.posOf st.cs _ _ (st.σ ia) (st.σ ib)) hR (fun _ _ hp => hp)
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨.eq, #[ia, ib]⟩) (by simp [hia, hib]) c' cs' x hc
        (by rw [ren_lit2]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv, st.σ_lt hia, hR.core.id_toNat hia, st.σ_lt hib, hR.core.id_toNat hib⟩
    H.2

/-- `x = mk_not(st, a); rest`, where `a` evaluates to the id of `ia`. -/
theorem WP.rule_mk_not (hNot : MkNotSpec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (ia : Nat) (hia : st.lv ia)
    (H : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, uv (st.id ia)] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st (fun st' i => Bcf.mkNot st ia = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mk_not" args) rest) Q env s :=
  WP.rule_build (hNot W sb c X.posOf st.cs _ (st.σ ia)) hR (fun _ _ hp => hp)
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨.boolNot, #[ia]⟩) (by simp [hia]) c' cs' x hc
        (by rw [ren_lit1]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv, st.σ_lt hia, hR.core.id_toNat hia⟩ H.2

/-- `x = mk1(st, HDR, a); rest` for a known operator `op` (`HDR` must evaluate to
`opHdr op`; `rule_simp` computes that for a constant header). -/
theorem WP.rule_mk1 (hMk : Mk1Spec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (op : Op) (hd : BitVec 32) (ia : Nat) (hia : st.lv ia)
    (hl : ¬ IsLeaf op := by decide) (hlo : opLo op < 256 := by decide)
    (hhi : opHi op < 256 := by decide) (hhd : hd.toNat = opHdr op := by decide)
    (H : evalArgs Vbcf.prog env s.mem args =
        some [.ptr sb 0, .u32 hd, uv (st.id ia)] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st (fun st' i => pushNode st ⟨op, #[ia]⟩ = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mk1" args) rest) Q env s := by
  have e := hhd
  exact WP.rule_build (hMk W sb c X.posOf st.cs _ _ (st.σ ia)) hR
    (fun _ _ hp => MkPost.build_op (is := [st.σ ia]) hl hlo hhi (by rw [e] at hp; exact hp))
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨op, #[ia]⟩) (by simp [hia]) c' cs' x hc (by rw [ren_lit1]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv, by rw [e]; exact opHdr_nonLeaf hl hlo hhi, st.σ_lt hia,
      hR.core.id_toNat hia⟩ H.2

/-- `x = mk2(st, HDR, a, b); rest` for a known operator `op`. -/
theorem WP.rule_mk2 (hMk : Mk2Spec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (op : Op) (hd : BitVec 32) (ia ib : Nat) (hia : st.lv ia)
    (hib : st.lv ib)
    (hl : ¬ IsLeaf op := by decide) (hlo : opLo op < 256 := by decide)
    (hhi : opHi op < 256 := by decide) (hhd : hd.toNat = opHdr op := by decide)
    (H : evalArgs Vbcf.prog env s.mem args =
        some [.ptr sb 0, .u32 hd, uv (st.id ia), uv (st.id ib)] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st
          (fun st' i => pushNode st ⟨op, #[ia, ib]⟩ = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mk2" args) rest) Q env s := by
  have e := hhd
  exact WP.rule_build (hMk W sb c X.posOf st.cs _ _ _ (st.σ ia) (st.σ ib)) hR
    (fun _ _ hp => MkPost.build_op (is := [st.σ ia, st.σ ib]) hl hlo hhi (by rw [e] at hp; exact hp))
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨op, #[ia, ib]⟩) (by simp [hia, hib]) c' cs' x hc
        (by rw [ren_lit2]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv, by rw [e]; exact opHdr_nonLeaf hl hlo hhi, st.σ_lt hia,
      hR.core.id_toNat hia, st.σ_lt hib, hR.core.id_toNat hib⟩ H.2

/-- `x = mk3(st, HDR, a, b, d); rest` for a known operator `op`. -/
theorem WP.rule_mk3 (hMk : Mk3Spec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (op : Op) (hd : BitVec 32) (ia ib id : Nat)
    (hia : st.lv ia) (hib : st.lv ib) (hid : st.lv id)
    (hl : ¬ IsLeaf op := by decide) (hlo : opLo op < 256 := by decide)
    (hhi : opHi op < 256 := by decide) (hhd : hd.toNat = opHdr op := by decide)
    (H : evalArgs Vbcf.prog env s.mem args =
        some [.ptr sb 0, .u32 hd, uv (st.id ia), uv (st.id ib),
          uv (st.id id)] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st
          (fun st' i => pushNode st ⟨op, #[ia, ib, id]⟩ = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mk3" args) rest) Q env s := by
  have e := hhd
  exact WP.rule_build (hMk W sb c X.posOf st.cs _ _ _ _ (st.σ ia) (st.σ ib) (st.σ id)) hR
    (fun _ _ hp => MkPost.build_op (is := [st.σ ia, st.σ ib, st.σ id]) hl hlo hhi
      (by rw [e] at hp; exact hp))
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨op, #[ia, ib, id]⟩) (by simp [hia, hib, hid]) c' cs' x hc
        (by rw [ren_lit3]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv, by rw [e]; exact opHdr_nonLeaf hl hlo hhi, st.σ_lt hia,
      hR.core.id_toNat hia, st.σ_lt hib, hR.core.id_toNat hib, st.σ_lt hid,
      hR.core.id_toNat hid⟩ H.2

/-- `x = mkn(st, hdr, base, n); rest` with an arbitrary non-leaf header word `hd`: the
arguments are the ids `is` on the scratch stack from `base` on.  The node built is
only known through its header (see `WP.rule_mkn` for a known operator). -/
theorem WP.rule_mkn_raw (hMkn : MknSpec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (hd : Nat) (base : Nat) (is : List Nat)
    (hhd : NonLeafHdr hd) (hids : StkIds c st base is) (hsp : base + is.length ≤ c.k.sp.toNat)
    (H : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, uv hd, uv base, uv is.length] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st (fun st' i => ∃ n, hdrW n = hd + is.length * 256 ∧
          Fits X.posOf n ∧ n.args = is.toArray ∧ pushNode st n = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mkn" args) rest) Q env s := by
  have hlt := c.k.sp.isLt
  have e := bv_toNat_ofNat hhd.1
  have e1 : (BitVec.ofNat 32 base).toNat = base := bv_toNat_ofNat (by omega)
  have e2 : (BitVec.ofNat 32 is.length).toNat = is.length := bv_toNat_ofNat (by omega)
  have e3 : (is.map st.σ).length = is.length := List.length_map _
  exact WP.rule_build (hMkn W sb c X.posOf st.cs _ _ _ (is.map st.σ)) hR
    (fun _ _ hp => MkPost.build (by rw [e] at hp; exact hp)) (raw_htr hR hids.lv)
    H.1 ⟨rfl, h, hR.core.cinv, by rw [e]; exact hhd, by rw [e3, e2], by rw [e1, e2]; exact hsp,
      by rw [e1]; exact hids.toC⟩ H.2

/-- `x = mkn(st, HDR, base, n); rest` for a known operator `op`. -/
theorem WP.rule_mkn (hMkn : MknSpec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (op : Op) (hd : BitVec 32) (base : Nat) (is : List Nat)
    (hids : StkIds c st base is) (hsp : base + is.length ≤ c.k.sp.toNat)
    (hl : ¬ IsLeaf op := by decide) (hlo : opLo op < 256 := by decide)
    (hhi : opHi op < 256 := by decide) (hhd : hd.toNat = opHdr op := by decide)
    (H : evalArgs Vbcf.prog env s.mem args =
        some [.ptr sb 0, .u32 hd, uv base, uv is.length] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st
          (fun st' i => pushNode st ⟨op, is.toArray⟩ = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mkn" args) rest) Q env s := by
  have hlt := c.k.sp.isLt
  have e := hhd
  have e1 : (BitVec.ofNat 32 base).toNat = base := bv_toNat_ofNat (by omega)
  have e2 : (BitVec.ofNat 32 is.length).toNat = is.length := bv_toNat_ofNat (by omega)
  have e3 : (is.map st.σ).length = is.length := List.length_map _
  exact WP.rule_build (hMkn W sb c X.posOf st.cs _ _ _ (is.map st.σ)) hR
    (fun _ _ hp => MkPost.build_op hl hlo hhi (by rw [e] at hp; exact hp))
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨op, is.toArray⟩) (by simpa using hids.lv) c' cs' x hc
        (by rw [ren_list]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv, by rw [e]; exact opHdr_nonLeaf hl hlo hhi, by rw [e3, e2],
      by rw [e1, e2]; exact hsp, by rw [e1]; exact hids.toC⟩ H.2

end build2

section build3
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {args : List Expr} {rest : Stmt}
  {wk er : BitVec 32} {vl : BitVec 64}

/-- `x = mk0(st, HDR_TRUE or HDR_FALSE); rest`. -/
theorem WP.rule_mk0 (hMk : Mk0BoolSpec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (b : Bool)
    (H : evalArgs Vbcf.prog env s.mem args =
        some [.ptr sb 0, .u32 (if b then 0x10009#32 else 0x9#32)] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st
          (fun st' i => pushNode st ⟨.boolVal b, #[]⟩ = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mk0" args) rest) Q env s :=
  WP.rule_build (hMk W sb c X.posOf st.cs b) hR (fun _ _ hp => hp)
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨.boolVal b, #[]⟩) (by simp) c' cs' x hc (by rw [ren_leaf]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv⟩ H.2

/-- `x = mkval(st, w, v); rest`. -/
theorem WP.rule_mkval (hMk : MkvalSpec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (w : BitVec 32) (v : BitVec 64)
    (hfit : w.toNat ≤ 32 → v.toNat < 2 ^ 32)
    (H : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, .u32 w, .u64 v] ∧
      ∀ s' c' r, Holds W s'.mem sb c' →
        Built W X c0 prems params c st
          (fun st' i => pushNode st ⟨.bvVal w.toNat v.toNat, #[]⟩ = some (st', i)) c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "mkval" args) rest) Q env s :=
  WP.rule_build (hMk W sb c X.posOf st.cs w v) hR (fun _ _ hp => hp)
    (fun c' cs' x hc hp =>
      push_htr hR (n := ⟨.bvVal w.toNat v.toNat, #[]⟩) (by simp) c' cs' x hc
        (by rw [ren_leaf]; exact hp))
    H.1 ⟨rfl, h, hR.core.cinv, hfit⟩ H.2

/-! ### Read-only calls -/

/-- The result `r` of `expr_at(st, p)`. -/
def EiRes (X : Ctx) (st : VSt) (p : Nat) (r : BitVec 32) : Prop :=
  match X.ei p with
  | none => r = 4294967295#32
  | some i => st.lv i ∧ r = BitVec.ofNat 32 (st.id i)

/-- After `if (a == NOID) { return NOID; }`: the position names a node. -/
theorem EiRes.ok {p : Nat} {r : BitVec 32} (he : EiRes X st p r) (hne : ¬ r = 4294967295#32) :
    ∃ i, X.ei p = some i ∧ st.lv i ∧ r = BitVec.ofNat 32 (st.id i) := by
  unfold EiRes at he
  split at he
  · exact absurd he hne
  · rename_i i hi
    exact ⟨i, hi, he⟩

/-- `x = expr_at(st, e); rest`, where `e` evaluates to the word `p`. -/
theorem WP.rule_expr_at (hEA : ExprAtSpec' (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (p : Nat) (hp : p < 4294967296)
    (H : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, uv p] ∧
      ∀ r, EiRes X st p r →
        match env.assign s.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s) :
    WP Vbcf.prog (.seq (.call (some x) "expr_at" args) rest) Q env s := by
  apply WP.call_seq (hEA W sb c X st (BitVec.ofNat 32 p)) H.1 ⟨rfl, h, hR.inv, hR.inv.nexprBound⟩
  rintro rv s' ⟨rfl, r, rfl, hr⟩
  refine H.2 r ?_
  rw [bv_toNat_ofNat hp] at hr
  unfold EiRes
  split at hr
  · rename_i he; simp only [he]; exact hr
  · rename_i i he; simp only [he]; exact ⟨hr.1, id_of_toNat hr.2.1⟩

/-- `x = ty_of(e); rest`: `x` becomes `tyOfB` of the word `e` evaluates to.  For the
header of a pool node, `hR.core.tyOf hn` says what that is. -/
theorem WP.rule_ty_of {tyOfW : BitVec 32 → BitVec 32} (hTy : TyOfSpec (State := State) tyOfW)
    (H : match evalArgs Vbcf.prog env s.mem args with
      | some [.u32 hd] =>
        (match env.assign s.mem x (.u32 (tyOfW hd)) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s)
      | _ => False) :
    WP Vbcf.prog (.seq (.call (some x) "ty_of" args) rest) Q env s := by
  split at H
  · rename_i hd hargs
    apply WP.call_seq (hTy hd) hargs rfl
    rintro rv s' ⟨rfl, rfl⟩
    exact H
  · exact H.elim

/-- The result `r` of `find_not(st, a)` for the node `n`.  The C checker only knows the
live nodes: where the Lean checker finds a dead node, the C finds none. -/
def FindRes (st : VSt) (n : Node) (r : BitVec 32) : Prop :=
  match findNode st.toSt n with
  | none => r = 4294967295#32
  | some i => (st.lv i ∧ st.pool[i]? = some n ∧ r = BitVec.ofNat 32 (st.id i)) ∨
      (¬ st.lv i ∧ r = 4294967295#32)

/-- `x = find_not(st, a); rest`, where `a` evaluates to the id of `ia`.  Afterwards
only `work` and `err` have changed, and the result is exact unless `err` is set. -/
theorem WP.rule_find_not (hFind : FindNotSpec (State := State)) (h : Holds W s.mem sb c)
    (hR : RCtx W X c0 prems params c st) (ia : Nat) (hia : st.lv ia)
    (H : evalArgs Vbcf.prog env s.mem args = some [.ptr sb 0, uv (st.id ia)] ∧
      ∀ r s' wk er, Holds W s'.mem sb (c.wev wk er c.k.val) →
        (er = 0#32 → FindRes st ⟨.boolNot, #[ia]⟩ r) →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "find_not" args) rest) Q env s := by
  apply WP.call_seq (hFind W sb c X.posOf st.cs _ (st.σ ia)) H.1
    ⟨rfl, h, hR.core.cinv, st.σ_lt hia, hR.core.id_toNat hia⟩
  rintro rv s' ⟨wk, er, r, rfl, h', hr⟩
  refine H.2 r s' wk er h' (fun he => ?_)
  rcases hr with hne | hr
  · exact absurd he hne
  have hargs : ∀ a ∈ (⟨.boolNot, #[ia]⟩ : Node).args, st.lv a := by simp [hia]
  have hren := ren_lit1 st.σ .boolNot ia
  unfold FindRes
  split at hr
  · rename_i hf
    rw [← hren] at hf
    cases hl : findNode st.toSt ⟨.boolNot, #[ia]⟩ with
    | none => simp only []; exact hr
    | some j =>
      simp only []
      exact Or.inr ⟨st.find_none hR.core.cinv.ok hf hl, hr⟩
  · rename_i x hf
    rw [← hren] at hf
    obtain ⟨j, hj, hσ, hn, hl⟩ := st.find_some hR.core.cinv.ok hargs hf
    rw [hl]
    simp only []
    refine Or.inl ⟨hj, hn, id_of_toNat ?_⟩
    rw [hr.1]; unfold VSt.id; rw [hσ]

/-! ### The scratch stack -/

/-- The outcome of `ok = push(st, v)` made in C state `c`: the rule context still
holds (for the same view), the stack below the old `sp` is unchanged, and either
`ok = 0`, or `ok = 1` and `v` is the new top. -/
def Pushed (W : World) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt) (c : CMem)
    (v : BitVec 32) (c' : CMem) (ok : BitVec 32) : Prop :=
  RCtx W X c0 prems params c' st ∧ (∀ i, i < c.k.sp.toNat → c'.stk[i]? = c.stk[i]?) ∧
  ((ok = 0#32 ∧ c'.k.sp = c.k.sp) ∨
   (ok = 1#32 ∧ c'.k.sp = c.k.sp + 1#32 ∧ c'.k.sp.toNat = c.k.sp.toNat + 1 ∧
     c'.stk[c.k.sp.toNat]? = some (.u32 v)))

/-- `x = push(st, e); rest`. -/
theorem WP.rule_push (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    (H : match evalArgs Vbcf.prog env s.mem args with
      | some [.ptr b o, .u32 v] => b = sb ∧ o = 0 ∧
        ∀ s' c' ok, Holds W s'.mem sb c' → Pushed W X c0 prems params st c v c' ok →
          match env.assign s'.mem x (.u32 ok) with
          | none => False
          | some env' => WP Vbcf.prog rest Q env' s'
      | _ => False) :
    WP Vbcf.prog (.seq (.call (some x) "push" args) rest) Q env s := by
  split at H
  · rename_i b o v hargs
    obtain ⟨rfl, rfl, H⟩ := H
    apply WP.call_seq (push_spec W b c v) hargs ⟨rfl, h, hR.core.stk⟩
    rintro rv s' ⟨c', h', hok, hfr, hpre, hcase⟩
    have hR' := hR.after_push hfr hok
    rcases hcase with ⟨rfl, hsp⟩ | ⟨rfl, hsp, htop⟩
    · exact H s' c' 0#32 h' ⟨hR', hpre, Or.inl ⟨rfl, hsp⟩⟩
    · refine H s' c' 1#32 h' ⟨hR', hpre, Or.inr ⟨rfl, hsp, ?_, htop⟩⟩
      have h1 := hok.cap
      have h2 := hR.core.stk.cap
      simp only [maxPool] at h1 h2
      rw [hsp, BitVec.toNat_add]
      simp
      omega
  · exact H.elim

/-- `x = spend(st, e); rest`: only `work` and `err` change. -/
theorem WP.rule_spend (h : Holds W s.mem sb c) (_hR : RCtx W X c0 prems params c st)
    (H : match evalArgs Vbcf.prog env s.mem args with
      | some [.ptr b o, .u32 _k] => b = sb ∧ o = 0 ∧
        ∀ s' wk er ok, Holds W s'.mem sb (c.wev wk er c.k.val) → (ok = 0#32 ∨ ok = 1#32) →
          match env.assign s'.mem x (.u32 ok) with
          | none => False
          | some env' => WP Vbcf.prog rest Q env' s'
      | _ => False) :
    WP Vbcf.prog (.seq (.call (some x) "spend" args) rest) Q env s := by
  split at H
  · rename_i b o k hargs
    obtain ⟨rfl, rfl, H⟩ := H
    apply WP.call_seq (spend_spec W b c k) hargs ⟨rfl, h⟩
    rintro rv s' ⟨rfl, h'⟩
    rw [spendM_wev] at h'
    exact H s' _ _ _ h' (spendM_fst c k)
  · exact H.elim

/-- The ids `is` are on the stack from `base` up to `sp`. -/
def StkTop (c : CMem) (st : VSt) (base : Nat) (is : List Nat) : Prop :=
  c.k.sp.toNat = base + is.length ∧ StkIds c st base is

theorem StkTop.wev {base : Nat} {is : List Nat} (h : StkTop c st base is) :
    StkTop (c.wev wk er vl) st base is := ⟨h.1, h.2⟩

theorem StkTop.nil {base : Nat} (h : c.k.sp.toNat = base) : StkTop c st base [] :=
  ⟨by simpa using h, fun j i hj => by simp at hj⟩

/-- A successful `push` of the id of `i` extends the list on the stack. -/
theorem StkTop.push {c' : CMem} {base : Nat} {is : List Nat} {i : Nat} {ok : BitVec 32}
    (ht : StkTop c st base is)
    (hP : Pushed W X c0 prems params st c (BitVec.ofNat 32 (st.id i)) c' ok)
    (hok : ¬ ok = 0#32) (hi : st.lv i) : StkTop c' st base (is ++ [i]) := by
  obtain ⟨-, hpre, hcase⟩ := hP
  rcases hcase with ⟨h0, -⟩ | ⟨-, -, hsp, htop⟩
  · exact absurd h0 hok
  · refine ⟨by rw [hsp, ht.1]; simp; omega, ?_⟩
    intro j a hj
    rcases Nat.lt_or_ge j is.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hj
      obtain ⟨ha, hU⟩ := ht.2 j a hj
      exact ⟨ha, by unfold U; rw [hpre _ (by rw [ht.1]; omega)]; exact hU⟩
    · rw [List.getElem?_append_right hge] at hj
      have hj0 : j = is.length := by
        rcases Nat.lt_or_ge (j - is.length) 1 with h1 | h1
        · omega
        · rw [List.getElem?_eq_none (by simpa using h1)] at hj; cases hj
      subst hj0
      simp at hj
      subst hj
      exact ⟨hi, by unfold U; rw [← ht.1]; exact htop⟩

/-- The second half of a list on the stack. -/
theorem StkIds.drop_left {c : CMem} {st : VSt} {base : Nat} {is js : List Nat}
    (h : StkIds c st base (is ++ js)) : StkIds c st (base + is.length) js := by
  intro j i hj
  have := h (is.length + j) i (by rw [List.getElem?_append_right (by omega)]; simpa using hj)
  rwa [show base + (is.length + j) = base + is.length + j by omega] at this

/-- A list on the stack survives a builder call. -/
theorem StkTop.built {c' : CMem} {st' : VSt} {base : Nat} {is : List Nat}
    (ht : StkTop c st base is) (hext : VExt st st')
    (hs : c'.stk = c.stk ∧ c'.k.sp = c.k.sp) : StkTop c' st' base is :=
  ⟨by rw [hs.2]; exact ht.1, ht.2.ext hext hs.1⟩

end build3

/-! ## 7. Tactics

Conventions: `hs : Vbcf.prog.findStruct "ck" = some ckS`, `h : Holds W s.mem sb c` and
`hR : RCtx W X c0 prems params c st` for the *current* state.  `rule_begin` introduces
them; after a call, name the new ones `h` and `hR` again. -/

/-- Closes the side conditions of `rule_simp`'s conditional rewrites: index bounds
(`i < st.pool.size`, `k < args.size`) by assumption or `omega`. -/
macro "rule_disch" : tactic =>
  `(tactic| first
    | assumption
    | omega
    | exact RCtx.tt_lt $(Lean.mkIdent `hR)
    | exact RCtx.ff_lt $(Lean.mkIdent `hR)
    | exact RCtx.goal_lt $(Lean.mkIdent `hR)
    | exact RCtx.pool_eq $(Lean.mkIdent `hR)
    | exact opC_lt32 _
    | exact RCtx.prem_eq $(Lean.mkIdent `hR)
    | decide
    | (simp; done)
    | fail "rule_disch: side condition not closed")

open Lean in
/-- `rule_simp [facts]`: evaluate the C expressions in the goal in the current state.
Knows the struct fields, the premise and parameter words, `st->tt`/`ff`/`goal`, id
arithmetic and comparisons, and header tests; `facts` are the cells of the nodes being
read (`hR.core.rd2 hn`, …). -/
macro "rule_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let h := mkIdent `h
  let hs := mkIdent `hs
  let hR := mkIdent `hR
  `(tactic| simp (disch := rule_disch) [EmbC.evalE, EmbC.evalBin, EmbC.evalArith, EmbC.evalCast, EmbC.evalArgs, EmbC.ptrEq,
      EmbC.Env.get, EmbC.Env.ty, EmbC.Env.set, EmbC.Env.assign, EmbC.Val.toIdx, EmbC.Val.ofBool,
      CK.setU32, CMem.arr, CMem.setArr, CK.ptr,
      HasCK.ld_pool $hs (Holds.ck $h), HasCK.ld_plen $hs (Holds.ck $h),
      HasCK.ld_pcap $hs (Holds.ck $h), HasCK.ld_htab $hs (Holds.ck $h),
      HasCK.ld_hcap $hs (Holds.ck $h), HasCK.ld_hcnt $hs (Holds.ck $h),
      HasCK.ld_facts $hs (Holds.ck $h), HasCK.ld_flen $hs (Holds.ck $h),
      HasCK.ld_fcap $hs (Holds.ck $h), HasCK.ld_nexpr $hs (Holds.ck $h),
      HasCK.ld_stk $hs (Holds.ck $h), HasCK.ld_sp $hs (Holds.ck $h),
      HasCK.ld_scap $hs (Holds.ck $h), HasCK.ld_prem $hs (Holds.ck $h),
      HasCK.ld_par $hs (Holds.ck $h), HasCK.ld_proof $hs (Holds.ck $h),
      HasCK.ld_tt $hs (Holds.ck $h), HasCK.ld_ff $hs (Holds.ck $h),
      HasCK.ld_goal $hs (Holds.ck $h), HasCK.ld_err $hs (Holds.ck $h),
      HasCK.ld_work $hs (Holds.ck $h), HasCK.ld_val $hs (Holds.ck $h),
      HasCK.ld_mem $hs (Holds.ck $h),
      RCtx.pool_eq $hR, Holds.ld_poolB $h, RCtx.prem_eq $hR, Holds.ld_premB $h, Holds.ld_stkB $h,
      RCtx.par_eq $hR, Holds.loadProof $h,
      RCtx.rd_prem $hR, RCtx.rd_par $hR, RCtx.rd_par0 $hR,
      RCtx.tt_eq $hR, RCtx.ff_eq $hR, RCtx.goal_eq $hR,
      VInv.id_toNat (RCtx.core $hR), VInv.id_mod (RCtx.core $hR),
      VInv.id_add_toNat (RCtx.core $hR), VInv.id_add_mod (RCtx.core $hR),
      VInv.id_add2_toNat (RCtx.core $hR), VInv.id_add2_mod (RCtx.core $hR),
      VInv.id_inj (RCtx.core $hR), VInv.id_ne_noid (RCtx.core $hR),
      CoreInv.id_toNat (VInv.cinv (RCtx.core $hR)), CoreInv.id_mod (VInv.cinv (RCtx.core $hR)),
      CoreInv.id_add_toNat (VInv.cinv (RCtx.core $hR)), CoreInv.id_add_mod (VInv.cinv (RCtx.core $hR)),
      CoreInv.id_add2_toNat (VInv.cinv (RCtx.core $hR)), CoreInv.id_add2_mod (VInv.cinv (RCtx.core $hR)),
      CoreInv.id_inj (VInv.cinv (RCtx.core $hR)), CoreInv.id_ne_noid (VInv.cinv (RCtx.core $hR)),
      uv_inj, uv_le, uv_lt, uv_toNat, mod32, uv_add, uv_and_ff, uv_or_hi, hdr_code_eq, hdrW_mod256, ite_some_u32, ite_u32_eq_zero,
      opC_bvVar_iff, opC_bvVal_iff, opC_bvIte_iff, opC_bvNeg_iff, opC_bvNot_iff,
      opC_bvExtract_iff, opC_bvSignExtend_iff, opC_bvZeroExtend_iff, opC_bvSize_iff,
      opC_bvRepeat_iff, opC_bvSub_iff, opC_bvShl_iff, opC_bvLshr_iff, opC_bvAshr_iff,
      opC_bvUdiv_iff, opC_bvUrem_iff, opC_bvSdiv_iff, opC_bvSmod_iff, opC_bvAdd_iff,
      opC_bvMul_iff, opC_bvOr_iff, opC_bvAnd_iff, opC_bvXor_iff, opC_bvConcat_iff,
      opC_bvFromBool_iff, opC_boolVal_iff, opC_boolVar_iff, opC_boolNot_iff,
      opC_boolBitof_iff, opC_eq_iff, opC_distinct_iff, opC_ugt_iff, opC_uge_iff, opC_sgt_iff,
      opC_sge_iff, opC_ult_iff, opC_ule_iff, opC_slt_iff, opC_sle_iff, opC_implies_iff,
      opC_boolIte_iff, opC_conj_iff, opC_disj_iff, opC_boolXor_iff, opC_listVal_iff, $ts,*])

macro "rule_simp" : tactic => `(tactic| rule_simp [])

open Lean in
/-- `rule_begin fn`: start the proof of `RuleSpec "name" rule` for the C function `fn`.
Leaves a `WP` goal for the body, with `W sb c X st prems params s` and
`h hR hsp hnp hna hs` in the context. -/
macro "rule_begin" fn:ident : tactic =>
  `(tactic|
    (apply RuleSpec.intro (fn := $fn) rfl rfl rfl
     intro $(mkIdent `W) $(mkIdent `sb) $(mkIdent `c) $(mkIdent `X) $(mkIdent `st)
       $(mkIdent `prems) $(mkIdent `params) $(mkIdent `s) $(mkIdent `h) $(mkIdent `hR)
       $(mkIdent `hsp) $(mkIdent `hnp) $(mkIdent `hna)
     have $(mkIdent `hs) := prog_ck
     simp only [$fn:ident, Stmt.block, initLocals, List.map, List.cons_append, List.nil_append,
       Ty.zero]))

open Lean in
/-- `rule_arity pat₁ pat₂`: the gate `if (np != K || na != L) { return NOID; }`.  The two
`rcases` patterns name the premises and the parameters, for example
`rule_arity ⟨p, q, rfl⟩ rfl` for `K = 2`, `L = 0` and `rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩` for
`K = L = 1`. -/
macro "rule_arity" p1:Lean.Parser.Tactic.rcasesPatMed p2:Lean.Parser.Tactic.rcasesPatMed : tactic =>
  `(tactic|
    (apply WP.rule_arity $(mkIdent `h) (by simp [Env.get]) (by simp [Env.get]) $(mkIdent `hnp)
       $(mkIdent `hna)
     intro hk hl
     obtain $p1 := len_shape _ hk
     obtain $p2 := len_shape _ hl
     clear hk hl $(mkIdent `hnp) $(mkIdent `hna)))

open Lean in
/-- `rule_guard [facts]`: the statement `if (cond) { return NOID; }`.  Leaves
`¬cond' → WP rest`, where `cond'` is what `rule_simp [facts]` makes of the condition. -/
macro "rule_guard" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (apply WP.rule_guard $(mkIdent `h); rule_simp [$ts,*]))
macro "rule_guard" : tactic => `(tactic| rule_guard [])

/-- `rule_assign [facts]`: the statement `x = e;`. -/
macro "rule_assign" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (apply WP.assign_seq; rule_simp [$ts,*]))
macro "rule_assign" : tactic => `(tactic| rule_assign [])

/-- `rule_ret [facts]`: the statement `return e;`.  Leaves `RuleRet … r s` for the
returned word `r`; close it with `hR.ret h hf hrule` (or `RuleRet.fail h`). -/
macro "rule_ret" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (apply WP.rule_ret; rule_simp [$ts,*]))
macro "rule_ret" : tactic => `(tactic| rule_ret [])

/-! ## 8. Small facts used by the basic rules -/

/-- `x == 0` on a word. -/
theorem uv_eq_zero_iff {n : Nat} (h : n < 4294967296) : (BitVec.ofNat 32 n = 0#32) ↔ n = 0 := by
  rw [show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl, uv_inj h (by omega)]

/-- The type word `ty_of` returns is `TY_BOOL` exactly for `bool`. -/
theorem uv_tyW_eq_bool {t : Bcf.Ty} (hf : TyFits t) :
    (BitVec.ofNat 32 (tyW t) = 4096#32) ↔ t = .bool := by
  cases t with
  | bool => simp
  | bv w =>
    simp only [TyFits] at hf
    simp only [tyW_bv, reduceCtorEq, iff_false]
    rw [show (4096#32 : BitVec 32) = BitVec.ofNat 32 4096 from rfl, uv_inj (by omega) (by omega)]
    omega
  | list e k =>
    simp only [TyFits] at hf
    simp only [tyW, reduceCtorEq, iff_false]
    rw [show (4096#32 : BitVec 32) = BitVec.ofNat 32 4096 from rfl, uv_inj (by split <;> omega) (by omega)]
    split <;> omega

/-- The type word is `≥ TY_LIST` exactly for list types. -/
theorem uv_tyW_ge_list {t : Bcf.Ty} (hf : TyFits t) :
    (8192#32 ≤ BitVec.ofNat 32 (tyW t)) ↔ t.isScalar = false := by
  rw [show (8192#32 : BitVec 32) = BitVec.ofNat 32 8192 from rfl]
  cases t with
  | bool => simp only [tyW_bool, Ty.isScalar]; rw [uv_le (by omega) (by omega)]; simp
  | bv w =>
    simp only [TyFits] at hf
    simp only [tyW_bv, Ty.isScalar]; rw [uv_le (by omega) (by omega)]; simp; omega
  | list e k =>
    simp only [TyFits] at hf
    simp only [tyW, Ty.isScalar]; rw [uv_le (by omega) (by split <;> omega)]; simp; split <;> omega

/-- An `eq` node from `isEqNode`. -/
theorem isEqNode_some {n : Node} {a b : Nat} (h : isEqNode n = some (a, b)) :
    n = ⟨.eq, #[a, b]⟩ := by
  obtain ⟨op, args⟩ := n
  cases op <;> simp [isEqNode] at h
  obtain ⟨hsz, h1, h2⟩ := h
  obtain ⟨x, y, rfl⟩ := array_eq_two hsz
  simp at h1 h2
  subst h1 h2
  rfl

/-- The first half of a list on the stack. -/
theorem StkIds.append_left {c : CMem} {st : VSt} {base : Nat} {is js : List Nat}
    (h : StkIds c st base (is ++ js)) : StkIds c st base is := by
  intro j i hj
  exact h j i (by rw [List.getElem?_append_left (lt_length_of_getElem? hj)]; exact hj)

/-- A node is its operator applied to its arguments. -/
theorem node_eq_of_args {n : Node} {args : Array Nat} (h : n.args = args) : n = ⟨n.op, args⟩ := by
  cases n; simp only at h; subst h; rfl

end Vbcf.Proof
