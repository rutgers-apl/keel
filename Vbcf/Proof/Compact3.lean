import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact2
import Vbcf.Proof.Hash

/-!
# Vbcf proofs: `ck_compact`, part 3 — the forwarding table and the program text

`ck_compact` keeps its forwarding table `fw` in a local variable: a block
that is neither part of the world at entry nor owned by the struct.
`World.addAux W fb blk` records it as an auxiliary block, and `Holds` for
that world describes the memory while `fw` is live.  Every specification
used inside `ck_compact` holds for an arbitrary world, so it applies to
`W.addAux fb blk` unchanged.

The loops of `ck_compact` are named here (`cpRoots` … `cpRefill`, the text
as `c_fn%` produced it), so that each can get its own lemma.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-! ## The auxiliary block -/

/-- `W` with block `b` holding `blk` as a local of the running function. -/
def World.addAux (W : World) (b : Nat) (blk : Block) : World :=
  ⟨W.base, W.pb, fun b' => if b' = b then some blk else W.aux b'⟩

@[simp] theorem World.addAux_base (W : World) (b : Nat) (blk : Block) :
    (W.addAux b blk).base = W.base := rfl
@[simp] theorem World.addAux_pb (W : World) (b : Nat) (blk : Block) :
    (W.addAux b blk).pb = W.pb := rfl
theorem World.addAux_self (W : World) (b : Nat) (blk : Block) :
    (W.addAux b blk).aux b = some blk := by simp [World.addAux]
theorem World.addAux_ne (W : World) {b b' : Nat} (blk : Block) (h : b' ≠ b) :
    (W.addAux b blk).aux b' = W.aux b' := by simp [World.addAux, h]

section
variable {W : World} {m : Mem} {sb : Nat} {c : CMem}

/-- `fw = kvcalloc(…)`: the fresh block becomes the auxiliary block. -/
theorem Holds.allocAux (h : Holds W m sb c) (cells : Array EmbC.Val) :
    Holds (W.addAux m.blocks.size ⟨.u32, cells⟩) (m.alloc .u32 cells).2 sb c := by
  have hb := fun b' => Mem.block?_alloc (m := m) (t := .u32) (cells := cells) b'
  have hsb := h.sb_lt
  have hown : ∀ a b o, c.k.ptr a = some (b, o) → b < m.blocks.size :=
    fun a b o hp => Mem.block?_lt (h.arr a b o hp).2.2.2
  have hbase : W.base.blocks.size ≤ sb := h.sbNew
  refine ⟨?_, h.sbNew, h.pbOld, ?_, h.proofPtr, h.parPtr, ?_, h.sep, ?_, ?_, ?_⟩
  · show (m.alloc _ _).2.block? sb = _
    rw [hb]; simp only [Nat.ne_of_lt hsb, ↓reduceIte]; exact h.ck
  · show (m.alloc _ _).2.block? W.pb = _
    rw [hb]; simp only [show W.pb ≠ m.blocks.size by have := h.pbOld; omega, ↓reduceIte]; exact h.proof
  · intro a b o hp
    obtain ⟨h1, h2, h3, h4⟩ := h.arr a b o hp
    refine ⟨h1, h2, h3, ?_⟩
    show (m.alloc _ _).2.block? b = _
    rw [hb]; simp only [Nat.ne_of_lt (hown a b o hp), ↓reduceIte]; exact h4
  · intro b hlt hne
    simp only [World.addAux_base, World.addAux_pb] at hlt hne
    rw [hb]; simp only [show b ≠ m.blocks.size by omega, ↓reduceIte]; exact h.out b hlt hne
  · intro b hge hne hno
    rw [hb]
    by_cases e : b = m.blocks.size
    · subst e; simp only [↓reduceIte]; rw [World.addAux_self]
    · simp only [e, ↓reduceIte]; rw [World.addAux_ne _ _ e]; exact h.exact b hge hne hno
  · intro b hb'
    by_cases e : b = m.blocks.size
    · subst e
      exact ⟨by simp only [World.addAux_base]; omega, by omega,
        fun a o hp => by have := hown a _ o hp; omega⟩
    · rw [World.addAux_ne _ _ e] at hb'
      exact h.auxNew b hb'

theorem Holds.aux_arr {fb : Nat} {cells : Array EmbC.Val} (h : Holds (W.addAux fb ⟨.u32, cells⟩) m sb c) :
    HasArr m fb cells := by
  have hne : (W.addAux fb ⟨.u32, cells⟩).aux fb ≠ none := by rw [World.addAux_self]; simp
  obtain ⟨h1, h2, h3⟩ := h.auxNew fb hne
  have := h.exact fb h1 h2 h3
  rw [World.addAux_self] at this
  exact this

/-- Reading the forwarding table. -/
theorem Holds.rd_aux {fb : Nat} {cells : Array EmbC.Val} (h : Holds (W.addAux fb ⟨.u32, cells⟩) m sb c)
    (i : Nat) : m.loadArr fb i = rd cells i := h.aux_arr.loadArr i

/-- Writing a cell of the forwarding table. -/
theorem Holds.storeAux {fb : Nat} {cells : Array EmbC.Val} (h : Holds (W.addAux fb ⟨.u32, cells⟩) m sb c)
    {i : Nat} (hi : i < cells.size) (x : BitVec 32) :
    m.storeArr fb i (.u32 x) = some (m.setCell fb i (.u32 x)) ∧
    Holds (W.addAux fb ⟨.u32, cells.setIfInBounds i (.u32 x)⟩) (m.setCell fb i (.u32 x)) sb c := by
  have harr := h.aux_arr
  have hne : (W.addAux fb ⟨.u32, cells⟩).aux fb ≠ none := by rw [World.addAux_self]; simp
  obtain ⟨hfb1, hfb2, hfb3⟩ := h.auxNew fb hne
  have hb := fun b' => Mem.block?_setCell (i := i) (v := .u32 x) b' harr
  have hpb : W.pb ≠ fb := by
    have := h.pbOld; simp only [World.addAux_base, World.addAux_pb] at hfb1 this; omega
  refine ⟨Mem.storeArr_eq harr rfl (by simp) hi, ?_, h.sbNew, h.pbOld, ?_, h.proofPtr, h.parPtr,
    ?_, h.sep, ?_, ?_, ?_⟩
  · show (m.setCell fb i _).block? sb = _
    rw [hb]; simp only [Ne.symm hfb2, ↓reduceIte]; exact h.ck
  · show (m.setCell fb i _).block? W.pb = _
    rw [hb]; simp only [hpb, ↓reduceIte]; exact h.proof
  · intro a b o hp
    obtain ⟨h1, h2, h3, h4⟩ := h.arr a b o hp
    refine ⟨h1, h2, h3, ?_⟩
    show (m.setCell fb i _).block? b = _
    have : b ≠ fb := fun e => hfb3 a o (by rw [← e]; exact hp)
    rw [hb]; simp only [this, ↓reduceIte]; exact h4
  · intro b hlt hne'
    have : b ≠ fb := by simp only [World.addAux_base] at hfb1 hlt; omega
    rw [hb]; simp only [this, ↓reduceIte]; exact h.out b hlt hne'
  · intro b hge hne' hno
    rw [hb]
    by_cases e : b = fb
    · subst e; simp only [↓reduceIte]; rw [World.addAux_self]
    · simp only [e, ↓reduceIte]; rw [World.addAux_ne _ _ e]
      have := h.exact b hge hne' hno
      rw [World.addAux_ne _ _ e] at this; exact this
  · intro b hb'
    by_cases e : b = fb
    · subst e; exact ⟨hfb1, hfb2, hfb3⟩
    · have := h.auxNew b (by rw [World.addAux_ne _ _ e]; rw [World.addAux_ne _ _ e] at hb'; exact hb')
      exact this

/-- `kvfree(fw)`: back to the world without the auxiliary block. -/
theorem Holds.freeAux {fb : Nat} {blk : Block} (h : Holds (W.addAux fb blk) m sb c)
    (hW : W.aux fb = none) : m.block? fb = some blk ∧ Holds W (m.free fb) sb c := by
  have hne : (W.addAux fb blk).aux fb ≠ none := by rw [World.addAux_self]; simp
  obtain ⟨hfb1, hfb2, hfb3⟩ := h.auxNew fb hne
  have hblk : m.block? fb = some blk := by
    have := h.exact fb hfb1 hfb2 hfb3
    rw [World.addAux_self] at this; exact this
  have hb := fun b' => Mem.block?_free (m := m) (b := fb) b'
  have hpb : W.pb ≠ fb := by
    have := h.pbOld; simp only [World.addAux_base, World.addAux_pb] at hfb1 this; omega
  refine ⟨hblk, ?_, h.sbNew, h.pbOld, ?_, h.proofPtr, h.parPtr, ?_, h.sep, ?_, ?_, ?_⟩
  · show (m.free fb).block? sb = _
    rw [hb]; simp only [Ne.symm hfb2, ↓reduceIte]; exact h.ck
  · show (m.free fb).block? W.pb = _
    rw [hb]; simp only [hpb, ↓reduceIte]; exact h.proof
  · intro a b o hp
    obtain ⟨h1, h2, h3, h4⟩ := h.arr a b o hp
    refine ⟨h1, h2, h3, ?_⟩
    show (m.free fb).block? b = _
    have : b ≠ fb := fun e => hfb3 a o (by rw [← e]; exact hp)
    rw [hb]; simp only [this, ↓reduceIte]; exact h4
  · intro b hlt hne'
    have : b ≠ fb := by simp only [World.addAux_base] at hfb1 hlt; omega
    rw [hb]; simp only [this, ↓reduceIte]; exact h.out b hlt hne'
  · intro b hge hne' hno
    rw [hb]
    by_cases e : b = fb
    · subst e; simp only [↓reduceIte]; exact hW.symm
    · simp only [e, ↓reduceIte]
      have := h.exact b hge hne' hno
      rw [World.addAux_ne _ _ e] at this; exact this
  · intro b hb'
    have e : b ≠ fb := fun e => by subst e; exact hb' hW
    have := h.auxNew b (by rw [World.addAux_ne _ _ e]; exact hb')
    exact this

/-- Re-describing the auxiliary block (its contents are the only thing that differs). -/
theorem Holds.reAux {fb : Nat} {blk blk' : Block} (h : Holds (W.addAux fb blk) m sb c)
    (he : blk' = blk) : Holds (W.addAux fb blk') m sb c := by rw [he]; exact h

end

/-! ## The environment and the postcondition -/

/-- The locals of `ck_compact`. -/
def cpEnv (sb : Nat) (lo plen n : BitVec 32) (fw : EmbC.Val) (j r o hdr code ar i c cur nodes ok : BitVec 32)
    (nt : EmbC.Val) (hc : BitVec 64) : Env :=
  [("st", (Ty.struct "ck").ptr, .ptr sb 0), ("lo", .u32, .u32 lo), ("plen", .u32, .u32 plen),
    ("n", .u32, .u32 n), ("fw", Ty.u32.ptr, fw), ("j", .u32, .u32 j), ("r", .u32, .u32 r),
    ("o", .u32, .u32 o), ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 code), ("ar", .u32, .u32 ar),
    ("i", .u32, .u32 i), ("c", .u32, .u32 c), ("cur", .u32, .u32 cur), ("nodes", .u32, .u32 nodes),
    ("ok", .u32, .u32 ok), ("nt", Ty.u32.ptr, nt), ("hc", .u64, .u64 hc)]

/-- What `ck_compact` promises (`CkCompactSpec (State := State)`), as a named predicate. -/
def CpPost (W : World) (sb : Nat) (ws : Array (BitVec 32)) (X : Ctx) (st : VSt) (off : Nat)
    (rest : List Step) : Option EmbC.Val → (KernelState prog State) → Prop := fun rv s' =>
  ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧
    (r ≠ 0#32 → ∃ st' : VSt, st'.toSt = st.toSt ∧ SInv W ws X c' st' off rest)

/-- `CpPost` for a returned word. -/
def CpRet (W : World) (sb : Nat) (ws : Array (BitVec 32)) (X : Ctx) (st : VSt) (off : Nat)
    (rest : List Step) : BitVec 32 → (KernelState prog State) → Prop := fun r s' =>
  CpPost W sb ws X st off rest (some (.u32 r)) s'

instance {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {st : VSt} {off : Nat}
    {rest : List Step} :
    RetsTo (State := State) (retPost (some .u32) (CpPost W sb ws X st off rest)) (CpRet W sb ws X st off rest) :=
  ⟨fun _ _ _ h => ⟨rfl, h⟩⟩

/-- `kvfree(fw); return 0;` -/
theorem WP.cp_fail {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {st : VSt} {off : Nat}
    {rest : List Step} {Q : (Post prog State)}
    (hQ : ∀ e s', CpRet W sb ws X st off rest 0#32 s' → Q (.ret (some (.u32 0#32))) e s')
    {s : (KernelState prog State)} {c : CMem} {fb : Nat} {blk : Block}
    (h : Holds (W.addAux fb blk) s.mem sb c) (hW : W.aux fb = none)
    {lo plen n j r o hdr code ar i cc cur nodes ok : BitVec 32} {nt : EmbC.Val} {hc : BitVec 64} :
    WP prog (.seq (.ecall none .kvfree [.var "fw"]) (.ret (some (.lit32 0#32)))) Q
      (cpEnv sb lo plen n (.ptr fb 0) j r o hdr code ar i cc cur nodes ok nt hc) s := by
  obtain ⟨hblk, h'⟩ := h.freeAux hW
  apply WP.seq
  apply WP.ecall
  embc_simp [cpEnv, kvfree_run hblk]
  apply WP.ret
  embc_simp
  exact hQ _ _ ⟨_, _, rfl, h', fun h0 => absurd rfl h0⟩

/-! ## The loops -/

/-- Loop 1: mark the nodes of the facts still cited later. -/
def cpRoots : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "j") (EmbC.Expr.field (EmbC.Expr.var "st") "flen"))
    (EmbC.Stmt.seq
      (EmbC.Stmt.ite
        (EmbC.Expr.bin
          (EmbC.BinOp.ge)
          (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "lr") (EmbC.Expr.var "j"))
          (EmbC.Expr.field (EmbC.Expr.var "st") "flen"))
        (EmbC.Stmt.seq
          (EmbC.Stmt.assign "r" (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "facts") (EmbC.Expr.var "j")))
          (EmbC.Stmt.ite
            (EmbC.Expr.land
              (EmbC.Expr.bin (EmbC.BinOp.ge) (EmbC.Expr.var "r") (EmbC.Expr.var "lo"))
              (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "r") (EmbC.Expr.var "plen")))
            (EmbC.Stmt.ite
              (EmbC.Expr.bin
                (EmbC.BinOp.eq)
                (EmbC.Expr.index
                  (EmbC.Expr.var "fw")
                  (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "r") (EmbC.Expr.var "lo")))
                (EmbC.Expr.lit32 0x00000000#32))
              (EmbC.Stmt.seq
                (EmbC.Stmt.store
                  (EmbC.Expr.var "fw")
                  (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "r") (EmbC.Expr.var "lo"))
                  (EmbC.Expr.named "NOID" 0xffffffff#32))
                (EmbC.Stmt.seq
                  (EmbC.Stmt.call (some "ok") "push" [EmbC.Expr.var "st", EmbC.Expr.var "r"])
                  (EmbC.Stmt.ite
                    (EmbC.Expr.bin (EmbC.BinOp.eq) (EmbC.Expr.var "ok") (EmbC.Expr.lit32 0x00000000#32))
                    (EmbC.Stmt.seq
                      (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
                      (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32))))
                    (EmbC.Stmt.skip))))
              (EmbC.Stmt.skip))
            (EmbC.Stmt.skip)))
        (EmbC.Stmt.skip))
      (EmbC.Stmt.assign "j" (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "j") (EmbC.Expr.lit32 0x00000001#32))))

/-- Loop 2: mark everything reachable (worklist on the scratch stack). -/
def cpMark : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin (EmbC.BinOp.gt) (EmbC.Expr.field (EmbC.Expr.var "st") "sp") (EmbC.Expr.lit32 0x00000000#32))
    (EmbC.Stmt.seq
      (EmbC.Stmt.setField
        (EmbC.Expr.var "st")
        "sp"
        (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.field (EmbC.Expr.var "st") "sp") (EmbC.Expr.lit32 0x00000001#32)))
      (EmbC.Stmt.seq
        (EmbC.Stmt.assign
          "o"
          (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "stk") (EmbC.Expr.field (EmbC.Expr.var "st") "sp")))
        (EmbC.Stmt.seq
          (EmbC.Stmt.assign "hdr" (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "pool") (EmbC.Expr.var "o")))
          (EmbC.Stmt.seq
            (EmbC.Stmt.assign
              "code"
              (EmbC.Expr.bin (EmbC.BinOp.band) (EmbC.Expr.var "hdr") (EmbC.Expr.lit32 0x000000ff#32)))
            (EmbC.Stmt.ite
              (EmbC.Expr.land
                (EmbC.Expr.land
                  (EmbC.Expr.land
                    (EmbC.Expr.bin (EmbC.BinOp.ne) (EmbC.Expr.var "code") (EmbC.Expr.named "BV_VAR" 0x00000018#32))
                    (EmbC.Expr.bin (EmbC.BinOp.ne) (EmbC.Expr.var "code") (EmbC.Expr.named "BOOL_VAR" 0x00000019#32)))
                  (EmbC.Expr.bin (EmbC.BinOp.ne) (EmbC.Expr.var "code") (EmbC.Expr.named "BV_VAL" 0x00000008#32)))
                (EmbC.Expr.bin (EmbC.BinOp.ne) (EmbC.Expr.var "code") (EmbC.Expr.named "BOOL_VAL" 0x00000009#32)))
              (EmbC.Stmt.seq
                (EmbC.Stmt.assign
                  "ar"
                  (EmbC.Expr.bin
                    (EmbC.BinOp.band)
                    (EmbC.Expr.bin (EmbC.BinOp.shr) (EmbC.Expr.var "hdr") (EmbC.Expr.lit32 0x00000008#32))
                    (EmbC.Expr.lit32 0x000000ff#32)))
                (EmbC.Stmt.seq
                  (EmbC.Stmt.ite
                    (EmbC.Expr.bin
                      (EmbC.BinOp.lt)
                      (EmbC.Expr.bin
                        (EmbC.BinOp.sub)
                        (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "plen") (EmbC.Expr.var "o"))
                        (EmbC.Expr.lit32 0x00000001#32))
                      (EmbC.Expr.var "ar"))
                    (EmbC.Stmt.seq
                      (EmbC.Stmt.setField (EmbC.Expr.var "st") "err" (EmbC.Expr.named "ERR_LIMIT" 0x00000002#32))
                      (EmbC.Stmt.seq
                        (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
                        (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32)))))
                    (EmbC.Stmt.skip))
                  (EmbC.Stmt.seq
                    (EmbC.Stmt.assign "i" (EmbC.Expr.lit32 0x00000000#32))
                    (EmbC.Stmt.while
                      (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "i") (EmbC.Expr.var "ar"))
                      (EmbC.Stmt.seq
                        (EmbC.Stmt.assign
                          "c"
                          (EmbC.Expr.index
                            (EmbC.Expr.field (EmbC.Expr.var "st") "pool")
                            (EmbC.Expr.bin
                              (EmbC.BinOp.add)
                              (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "o") (EmbC.Expr.lit32 0x00000001#32))
                              (EmbC.Expr.var "i"))))
                        (EmbC.Stmt.seq
                          (EmbC.Stmt.ite
                            (EmbC.Expr.land
                              (EmbC.Expr.bin (EmbC.BinOp.ge) (EmbC.Expr.var "c") (EmbC.Expr.var "lo"))
                              (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "c") (EmbC.Expr.var "o")))
                            (EmbC.Stmt.ite
                              (EmbC.Expr.bin
                                (EmbC.BinOp.eq)
                                (EmbC.Expr.index
                                  (EmbC.Expr.var "fw")
                                  (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "c") (EmbC.Expr.var "lo")))
                                (EmbC.Expr.lit32 0x00000000#32))
                              (EmbC.Stmt.seq
                                (EmbC.Stmt.store
                                  (EmbC.Expr.var "fw")
                                  (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "c") (EmbC.Expr.var "lo"))
                                  (EmbC.Expr.named "NOID" 0xffffffff#32))
                                (EmbC.Stmt.seq
                                  (EmbC.Stmt.call (some "ok") "push" [EmbC.Expr.var "st", EmbC.Expr.var "c"])
                                  (EmbC.Stmt.ite
                                    (EmbC.Expr.bin (EmbC.BinOp.eq) (EmbC.Expr.var "ok") (EmbC.Expr.lit32 0x00000000#32))
                                    (EmbC.Stmt.seq
                                      (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
                                      (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32))))
                                    (EmbC.Stmt.skip))))
                              (EmbC.Stmt.skip))
                            (EmbC.Stmt.skip))
                          (EmbC.Stmt.assign
                            "i"
                            (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "i") (EmbC.Expr.lit32 0x00000001#32)))))))))
              (EmbC.Stmt.skip))))))

/-- Loop 3: slide the marked nodes down. -/
def cpSlide : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "o") (EmbC.Expr.var "plen"))
    (EmbC.Stmt.seq
      (EmbC.Stmt.assign "hdr" (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "pool") (EmbC.Expr.var "o")))
      (EmbC.Stmt.seq
        (EmbC.Stmt.assign
          "ar"
          (EmbC.Expr.bin
            (EmbC.BinOp.band)
            (EmbC.Expr.bin (EmbC.BinOp.shr) (EmbC.Expr.var "hdr") (EmbC.Expr.lit32 0x00000008#32))
            (EmbC.Expr.lit32 0x000000ff#32)))
        (EmbC.Stmt.seq
          (EmbC.Stmt.ite
            (EmbC.Expr.bin
              (EmbC.BinOp.lt)
              (EmbC.Expr.bin
                (EmbC.BinOp.sub)
                (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "plen") (EmbC.Expr.var "o"))
                (EmbC.Expr.lit32 0x00000001#32))
              (EmbC.Expr.var "ar"))
            (EmbC.Stmt.seq
              (EmbC.Stmt.setField (EmbC.Expr.var "st") "err" (EmbC.Expr.named "ERR_LIMIT" 0x00000002#32))
              (EmbC.Stmt.seq
                (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
                (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32)))))
            (EmbC.Stmt.skip))
          (EmbC.Stmt.seq
            (EmbC.Stmt.ite
              (EmbC.Expr.bin
                (EmbC.BinOp.ne)
                (EmbC.Expr.index
                  (EmbC.Expr.var "fw")
                  (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "o") (EmbC.Expr.var "lo")))
                (EmbC.Expr.lit32 0x00000000#32))
              (EmbC.Stmt.seq
                (EmbC.Stmt.store
                  (EmbC.Expr.field (EmbC.Expr.var "st") "pool")
                  (EmbC.Expr.var "cur")
                  (EmbC.Expr.var "hdr"))
                (EmbC.Stmt.seq
                  (EmbC.Stmt.assign
                    "code"
                    (EmbC.Expr.bin (EmbC.BinOp.band) (EmbC.Expr.var "hdr") (EmbC.Expr.lit32 0x000000ff#32)))
                  (EmbC.Stmt.seq
                    (EmbC.Stmt.assign "i" (EmbC.Expr.lit32 0x00000000#32))
                    (EmbC.Stmt.seq
                      (EmbC.Stmt.while
                        (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "i") (EmbC.Expr.var "ar"))
                        (EmbC.Stmt.seq
                          (EmbC.Stmt.assign
                            "c"
                            (EmbC.Expr.index
                              (EmbC.Expr.field (EmbC.Expr.var "st") "pool")
                              (EmbC.Expr.bin
                                (EmbC.BinOp.add)
                                (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "o") (EmbC.Expr.lit32 0x00000001#32))
                                (EmbC.Expr.var "i"))))
                          (EmbC.Stmt.seq
                            (EmbC.Stmt.ite
                              (EmbC.Expr.land
                                (EmbC.Expr.land
                                  (EmbC.Expr.land
                                    (EmbC.Expr.land
                                      (EmbC.Expr.land
                                        (EmbC.Expr.bin
                                          (EmbC.BinOp.ne)
                                          (EmbC.Expr.var "code")
                                          (EmbC.Expr.named "BV_VAR" 0x00000018#32))
                                        (EmbC.Expr.bin
                                          (EmbC.BinOp.ne)
                                          (EmbC.Expr.var "code")
                                          (EmbC.Expr.named "BOOL_VAR" 0x00000019#32)))
                                      (EmbC.Expr.bin
                                        (EmbC.BinOp.ne)
                                        (EmbC.Expr.var "code")
                                        (EmbC.Expr.named "BV_VAL" 0x00000008#32)))
                                    (EmbC.Expr.bin
                                      (EmbC.BinOp.ne)
                                      (EmbC.Expr.var "code")
                                      (EmbC.Expr.named "BOOL_VAL" 0x00000009#32)))
                                  (EmbC.Expr.bin (EmbC.BinOp.ge) (EmbC.Expr.var "c") (EmbC.Expr.var "lo")))
                                (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "c") (EmbC.Expr.var "o")))
                              (EmbC.Stmt.assign
                                "c"
                                (EmbC.Expr.index
                                  (EmbC.Expr.var "fw")
                                  (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "c") (EmbC.Expr.var "lo"))))
                              (EmbC.Stmt.skip))
                            (EmbC.Stmt.seq
                              (EmbC.Stmt.store
                                (EmbC.Expr.field (EmbC.Expr.var "st") "pool")
                                (EmbC.Expr.bin
                                  (EmbC.BinOp.add)
                                  (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "cur") (EmbC.Expr.lit32 0x00000001#32))
                                  (EmbC.Expr.var "i"))
                                (EmbC.Expr.var "c"))
                              (EmbC.Stmt.assign
                                "i"
                                (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "i") (EmbC.Expr.lit32 0x00000001#32)))))))
                      (EmbC.Stmt.seq
                        (EmbC.Stmt.store
                          (EmbC.Expr.var "fw")
                          (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "o") (EmbC.Expr.var "lo"))
                          (EmbC.Expr.var "cur"))
                        (EmbC.Stmt.seq
                          (EmbC.Stmt.assign
                            "cur"
                            (EmbC.Expr.bin
                              (EmbC.BinOp.add)
                              (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "cur") (EmbC.Expr.lit32 0x00000001#32))
                              (EmbC.Expr.var "ar")))
                          (EmbC.Stmt.assign
                            "nodes"
                            (EmbC.Expr.bin
                              (EmbC.BinOp.add)
                              (EmbC.Expr.var "nodes")
                              (EmbC.Expr.lit32 0x00000001#32)))))))))
              (EmbC.Stmt.skip))
            (EmbC.Stmt.assign
              "o"
              (EmbC.Expr.bin
                (EmbC.BinOp.add)
                (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "o") (EmbC.Expr.lit32 0x00000001#32))
                (EmbC.Expr.var "ar")))))))

/-- Loop 4: remap the facts. -/
def cpRemap : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "j") (EmbC.Expr.field (EmbC.Expr.var "st") "flen"))
    (EmbC.Stmt.seq
      (EmbC.Stmt.assign "r" (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "facts") (EmbC.Expr.var "j")))
      (EmbC.Stmt.seq
        (EmbC.Stmt.ite
          (EmbC.Expr.land
            (EmbC.Expr.bin (EmbC.BinOp.ge) (EmbC.Expr.var "r") (EmbC.Expr.var "lo"))
            (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "r") (EmbC.Expr.var "plen")))
          (EmbC.Stmt.seq
            (EmbC.Stmt.assign
              "c"
              (EmbC.Expr.index
                (EmbC.Expr.var "fw")
                (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "r") (EmbC.Expr.var "lo"))))
            (EmbC.Stmt.seq
              (EmbC.Stmt.ite
                (EmbC.Expr.bin (EmbC.BinOp.eq) (EmbC.Expr.var "c") (EmbC.Expr.lit32 0x00000000#32))
                (EmbC.Stmt.assign "c" (EmbC.Expr.named "NOID" 0xffffffff#32))
                (EmbC.Stmt.skip))
              (EmbC.Stmt.store (EmbC.Expr.field (EmbC.Expr.var "st") "facts") (EmbC.Expr.var "j") (EmbC.Expr.var "c"))))
          (EmbC.Stmt.skip))
        (EmbC.Stmt.assign "j" (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "j") (EmbC.Expr.lit32 0x00000001#32)))))

/-- Loop 5: count the nodes below `lo`. -/
def cpCount : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "o") (EmbC.Expr.var "lo"))
    (EmbC.Stmt.seq
      (EmbC.Stmt.assign
        "ar"
        (EmbC.Expr.bin
          (EmbC.BinOp.band)
          (EmbC.Expr.bin
            (EmbC.BinOp.shr)
            (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "pool") (EmbC.Expr.var "o"))
            (EmbC.Expr.lit32 0x00000008#32))
          (EmbC.Expr.lit32 0x000000ff#32)))
      (EmbC.Stmt.seq
        (EmbC.Stmt.ite
          (EmbC.Expr.bin
            (EmbC.BinOp.lt)
            (EmbC.Expr.bin
              (EmbC.BinOp.sub)
              (EmbC.Expr.bin (EmbC.BinOp.sub) (EmbC.Expr.var "lo") (EmbC.Expr.var "o"))
              (EmbC.Expr.lit32 0x00000001#32))
            (EmbC.Expr.var "ar"))
          (EmbC.Stmt.seq
            (EmbC.Stmt.setField (EmbC.Expr.var "st") "err" (EmbC.Expr.named "ERR_LIMIT" 0x00000002#32))
            (EmbC.Stmt.seq
              (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
              (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32)))))
          (EmbC.Stmt.skip))
        (EmbC.Stmt.seq
          (EmbC.Stmt.assign
            "o"
            (EmbC.Expr.bin
              (EmbC.BinOp.add)
              (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "o") (EmbC.Expr.lit32 0x00000001#32))
              (EmbC.Expr.var "ar")))
          (EmbC.Stmt.assign
            "nodes"
            (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "nodes") (EmbC.Expr.lit32 0x00000001#32))))))

/-- Loop 6: size the new table. -/
def cpGrow : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin
      (EmbC.BinOp.lt)
      (EmbC.Expr.var "hc")
      (EmbC.Expr.bin
        (EmbC.BinOp.mul)
        (EmbC.Expr.lit64 0x0000000000000004#64)
        (EmbC.Expr.cast (EmbC.Ty.u64) (EmbC.Expr.var "nodes"))))
    (EmbC.Stmt.seq
      (EmbC.Stmt.call (some "ok") "tick" [EmbC.Expr.var "st"])
      (EmbC.Stmt.seq
        (EmbC.Stmt.ite
          (EmbC.Expr.bin (EmbC.BinOp.eq) (EmbC.Expr.var "ok") (EmbC.Expr.lit32 0x00000000#32))
          (EmbC.Stmt.seq
            (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
            (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32))))
          (EmbC.Stmt.skip))
        (EmbC.Stmt.assign
          "hc"
          (EmbC.Expr.bin (EmbC.BinOp.mul) (EmbC.Expr.var "hc") (EmbC.Expr.lit64 0x0000000000000002#64)))))

/-- Loop 7: refill the table. -/
def cpRefill : Stmt :=
  EmbC.Stmt.while
    (EmbC.Expr.bin (EmbC.BinOp.lt) (EmbC.Expr.var "o") (EmbC.Expr.var "cur"))
    (EmbC.Stmt.seq
      (EmbC.Stmt.call (some "ok") "ck_hput" [EmbC.Expr.var "st", EmbC.Expr.var "o"])
      (EmbC.Stmt.seq
        (EmbC.Stmt.ite
          (EmbC.Expr.bin (EmbC.BinOp.eq) (EmbC.Expr.var "ok") (EmbC.Expr.lit32 0x00000000#32))
          (EmbC.Stmt.seq
            (EmbC.Stmt.ecall none (EmbC.Ext.kvfree) [EmbC.Expr.var "fw"])
            (EmbC.Stmt.ret (some (EmbC.Expr.lit32 0x00000000#32))))
          (EmbC.Stmt.skip))
        (EmbC.Stmt.assign
          "o"
          (EmbC.Expr.bin
            (EmbC.BinOp.add)
            (EmbC.Expr.bin (EmbC.BinOp.add) (EmbC.Expr.var "o") (EmbC.Expr.lit32 0x00000001#32))
            (EmbC.Expr.bin
              (EmbC.BinOp.band)
              (EmbC.Expr.bin
                (EmbC.BinOp.shr)
                (EmbC.Expr.index (EmbC.Expr.field (EmbC.Expr.var "st") "pool") (EmbC.Expr.var "o"))
                (EmbC.Expr.lit32 0x00000008#32))
              (EmbC.Expr.lit32 0x000000ff#32))))))

end Vbcf.Proof
