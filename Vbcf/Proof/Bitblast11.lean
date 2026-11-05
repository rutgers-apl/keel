import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast10

/-!
# Vbcf proofs: the Bitblast family, part 11 — `bbTerm` one operator at a time
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


section term
variable {st : VSt} {bi : Builtins} {a : Nat} {bs : List Nat} {args : Array Nat}
  {xss : List (List Nat)}

theorem bbTerm_var {w id : Nat} (hn : st.pool[a]? = some ⟨.bvVar w id, args⟩) :
    Bcf.bbTerm st bi a bs = Bcf.bbVar st a bs := by
  simp [Bcf.bbTerm, hn]

theorem bbTerm_val {w v : Nat} (hn : st.pool[a]? = some ⟨.bvVal w v, args⟩) :
    Bcf.bbTerm st bi a bs = Bcf.bbVal bi v bs := by
  simp [Bcf.bbTerm, hn]

theorem bbTerm_ite {w c t e : Nat} {ts es : Array Nat}
    (hn : st.pool[a]? = some ⟨.bvIte w, #[c, t, e]⟩) (ht : st.pool[t]? = some ⟨.bvFromBool, ts⟩)
    (he : st.pool[e]? = some ⟨.bvFromBool, es⟩) :
    Bcf.bbTerm st bi a bs = Bcf.bbIte st c ts.toList es.toList bs := by
  simp [Bcf.bbTerm, hn, bitsOf, ht, he]

theorem bbTerm_and {w : Nat} (hn : st.pool[a]? = some ⟨.bvAnd w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some xss) :
    Bcf.bbTerm st bi a bs = Bcf.bbBitwise st .conj xss 0 bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_or {w : Nat} (hn : st.pool[a]? = some ⟨.bvOr w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some xss) :
    Bcf.bbTerm st bi a bs = Bcf.bbBitwise st .disj xss 0 bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_xor {w : Nat} (hn : st.pool[a]? = some ⟨.bvXor w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some xss) :
    Bcf.bbTerm st bi a bs = Bcf.bbBitwise st .boolXor xss 0 bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_concat {w : Nat} (hn : st.pool[a]? = some ⟨.bvConcat w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some xss) :
    Bcf.bbTerm st bi a bs = (bs == xss.reverse.flatten) := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_add {w : Nat} (hn : st.pool[a]? = some ⟨.bvAdd w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some xss) :
    Bcf.bbTerm st bi a bs = bbAddRev st bi xss.reverse bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_extract {hi lo : Nat} {xs : List Nat} (hn : st.pool[a]? = some ⟨.bvExtract hi lo, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs]) :
    Bcf.bbTerm st bi a bs = (bs == (xs.drop lo).take (hi - lo + 1)) := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_sext {w e : Nat} {xs : List Nat} (hn : st.pool[a]? = some ⟨.bvSignExtend w e, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs]) :
    Bcf.bbTerm st bi a bs = Bcf.bbSext xs bs e := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_not {w : Nat} {xs : List Nat} (hn : st.pool[a]? = some ⟨.bvNot w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs]) :
    Bcf.bbTerm st bi a bs = zipAll (fun b x => isNotOf st b x) bs xs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_neg {w : Nat} {xs : List Nat} (hn : st.pool[a]? = some ⟨.bvNeg w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs]) :
    Bcf.bbTerm st bi a bs = Bcf.bbNeg st bi xs bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_sub {w : Nat} {xs ys : List Nat} (hn : st.pool[a]? = some ⟨.bvSub w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs, ys]) :
    Bcf.bbTerm st bi a bs = Bcf.bbSub st bi xs ys bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_shl {w : Nat} {xs ys : List Nat} (hn : st.pool[a]? = some ⟨.bvShl w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs, ys]) :
    Bcf.bbTerm st bi a bs = Bcf.bbShift st bi (isFalseNode st) (Bcf.bbLshStage st) xs ys bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_lshr {w : Nat} {xs ys : List Nat} (hn : st.pool[a]? = some ⟨.bvLshr w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs, ys]) :
    Bcf.bbTerm st bi a bs =
      Bcf.bbShift st bi (isFalseNode st) (Bcf.bbRshStage st (isFalseNode st)) xs ys bs := by
  simp [Bcf.bbTerm, hn, hm]

theorem bbTerm_ashr {w : Nat} {xs ys : List Nat} (hn : st.pool[a]? = some ⟨.bvAshr w, args⟩)
    (hm : mapOpt (bitsOf st) args.toList = some [xs, ys]) :
    Bcf.bbTerm st bi a bs =
      Bcf.bbShift st bi (isLastOf xs) (Bcf.bbRshStage st (isLastOf xs)) xs ys bs := by
  simp [Bcf.bbTerm, hn, hm]

end term

/-- Bits of every argument give the `mapOpt`. -/
theorem bb_mapOpt_bits {st : St} :
    ∀ (l : List Nat), (∀ (k : Nat) (hk : k < l.length), ∃ xa, st.pool[l[k]]? = some ⟨.bvFromBool, xa⟩) →
    ∃ xss, mapOpt (bitsOf st) l = some xss
  | [], _ => ⟨[], rfl⟩
  | x :: l, H => by
    obtain ⟨xa, hxa⟩ := H 0 (by simp)
    obtain ⟨xss, hxss⟩ := bb_mapOpt_bits l (fun k hk => H (k + 1) (by simp; omega))
    simp only [List.getElem_cons_zero] at hxa
    exact ⟨xa.toList :: xss, by simp [mapOpt, bitsOf, hxa, hxss]⟩

theorem bb_shr24 {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    BitVec.ofNat 32 (hdrW n) >>> 24 = BitVec.ofNat 32 (opHi n.op) := by
  have := hdrW_lt hf; have := hf.hi
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_24, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega), hdrW_hi hf]

theorem bb_mapOpt_one {st : St} {x : Nat} {xa : Array Nat}
    (h : st.pool[x]? = some ⟨.bvFromBool, xa⟩) : mapOpt (bitsOf st) [x] = some [xa.toList] := by
  simp [mapOpt, bitsOf, h]

theorem bb_mapOpt_two {st : St} {x y : Nat} {xa ya : Array Nat}
    (h : st.pool[x]? = some ⟨.bvFromBool, xa⟩) (h' : st.pool[y]? = some ⟨.bvFromBool, ya⟩) :
    mapOpt (bitsOf st) [x, y] = some [xa.toList, ya.toList] := by
  simp [mapOpt, bitsOf, h, h']

end Vbcf.Proof
