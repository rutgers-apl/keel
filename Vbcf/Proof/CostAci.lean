import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostCore

/-!
# Vbcf cost proofs: `aci_absorb` and the helpers it calls

`aci_absorb` is the pattern for a recursive traversal: it recurses with a
depth counter and spends a unit of work on every entry, so its cost is
amortised against the work counter, proved by induction on the depth
(`FnCost.rec`).  A call that searched (returned 0 or 1) hands back enough
of its tick to pay for the loop iteration that made it (`slackOr`).  The
helpers are loop-free. Their direct cost proofs count function entry and
administrative transitions, using `wpc_auto`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000

theorem aci_is_val_cost (sb A : Nat) (id w : BitVec 32) (v : BitVec 64) :
    FnCost (State := State) prog "aci_is_val" (BudPre sb [.ptr sb 0, .u32 id, .u32 w, .u64 v])
      (Amort sb A (allow 15) 0 noSlack) := by
  apply FnCost.intro (fn := aciIsVal) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body aciIsVal
  wpc_auto
  wpc_done

fncost_register "aci_is_val" aciIsVal aci_is_val_cost

theorem mask64_cost (sb A : Nat) (w : BitVec 32) :
    FnCost (State := State) prog "mask64" (BudPre sb [.u32 w]) (Amort sb A (allow 5) 0 noSlack) := by
  apply FnCost.intro (fn := mask64) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body mask64
  wpc_auto
  wpc_done

fncost_register "mask64" mask64 mask64_cost

theorem aci_is_ones_cost (sb A : Nat) (id w : BitVec 32) :
    FnCost (State := State) prog "aci_is_ones" (BudPre sb [.ptr sb 0, .u32 id, .u32 w]) (Amort sb A (allow 33) 0 noSlack) := by
  apply FnCost.intro (fn := aciIsOnes) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body aciIsOnes
  wpc_auto
  wpc_done

fncost_register "aci_is_ones" aciIsOnes aci_is_ones_cost

theorem aci_zero_cost (sb A : Nat) (rop id : BitVec 32) :
    FnCost (State := State) prog "aci_zero" (BudPre sb [.ptr sb 0, .u32 rop, .u32 id]) (Amort sb A (allow 53) 0 noSlack) := by
  apply FnCost.intro (fn := aciZero) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body aciZero
  wpc_auto
  wpc_done

fncost_register "aci_zero" aciZero aci_zero_cost

/-! ## `aci_absorb` -/

theorem evalArgs_cons {P : Prog} {env : Env} {m : Mem} {e : Expr} {es : List Expr} {vs : List Val}
    (h : evalArgs P env m (e :: es) = some vs) :
    ∃ v vs', evalE P env m e = some v ∧ evalArgs P env m es = some vs' ∧ vs = v :: vs' := by
  simp only [evalArgs] at h
  split at h
  · rename_i v vs' h1 h2; simp only [Option.some.injEq] at h; exact ⟨v, vs', h1, h2, h.symm⟩
  · simp at h

/-- `aci_absorb`'s arguments; the node may be any value (the call gets stuck
unless it is a `u32`). -/
def AbsArgs (sb : Nat) (vs : List Val) : Prop :=
  ∃ (rop : BitVec 32) (x : Val) (d : BitVec 32), vs = [.ptr sb 0, .u32 rop, x, .u32 d]

/-- The measure of the recursion: the depth argument. -/
def depthArg : List Val → Nat
  | [_, _, _, .u32 d] => d.toNat
  | _ => 0

theorem aci_absorb_cost (sb A : Nat) (hA : 100 ≤ A) :
    FnCost (State := State) prog "aci_absorb"
      (fun vs st => AbsArgs sb vs ∧ ∃ w mm : BitVec 32, Budget st.mem sb w mm)
      (Amort sb A (allow 20) 0 (slackOr 0#32 1#32 30)) := by
  apply FnCost.rec (fun vs _ => depthArg vs)
  intro m IH
  apply FnCost.intro (fn := aciAbsorb) rfl
  rintro vs st ⟨⟨⟨rop, x, d, rfl⟩, w, mm, hb⟩, hm⟩
  simp only [depthArg] at hm
  cases x with
  | u32 i =>
    have hA6 : 6 ≤ A := by omega
    fncost_body aciAbsorb
    -- if (depth == 0) return NOID;
    apply WPC.seq
    apply WPC.ite
    embc_simp
    constructor
    · intro hd
      wpc_auto
      wpc_done
    intro hd
    apply WPC.skip
    wpc_simp
    -- r = tick(st);
    apply WPC.seq
    apply WPC.call (tick_cost sb A hA6)
    embc_simp
    refine ⟨⟨rfl, w, mm, hb⟩, ?_⟩
    rintro rv st1 c1 ⟨w1, mm1, hb1, hc1, hm1⟩
    rw [hb.wk] at hc1
    rw [hb.mk] at hm1
    split
    · trivial
    rename_i env1 hasg1
    obtain ⟨r1, rfl, rfl⟩ := assignDst_u32' hasg1 rfl
    wpc_simp
    -- if (r == 0) return NOID;
    apply WPC.seq
    apply WPC.ite
    embc_simp
    constructor
    · intro hr0
      subst hr0
      simp only [slackUnless_apply, ↓reduceIte] at hc1
      wpc_auto
      wpc_done
    intro hr1
    simp only [slackUnless_apply, Option.some.injEq, Val.u32.injEq, hr1, ↓reduceIte] at hc1
    apply WPC.skip
    wpc_simp
    -- r = aci_zero(st, rop, i);
    apply WPC.seq
    apply WPC.call (aci_zero_cost sb A rop i)
    embc_simp
    refine ⟨⟨rfl, w1, mm1, hb1⟩, ?_⟩
    rintro rv st2 c2 ⟨w2, mm2, hb2, hc2, hm2⟩
    rw [hb1.wk] at hc2
    rw [hb1.mk] at hm2
    split
    · trivial
    rename_i env2 hasg2
    obtain ⟨r2, rfl, rfl⟩ := assignDst_u32' hasg2 rfl
    wpc_simp
    -- if (r != 0) return 1;
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    -- if ((st->pool[i] & ACI_OPMASK) != rop) return 0;
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    -- n = (st->pool[i] >> 8) & 0xff;
    apply WPC.seq
    apply WPC.assign_band (by rfl)
    intro n hn
    wpc_simp
    have hn' : n.toNat ≤ 255 := by simpa using hn
    -- the children: each that returns 0 pays for its iteration
    apply WPC.seq
    apply WPC.while
      (I := fun env' st' k => ∃ (kk r' : BitVec 32),
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("rop", .u32, .u32 rop), ("i", .u32, .u32 i),
          ("depth", .u32, .u32 d), ("r", .u32, .u32 r'), ("n", .u32, .u32 n), ("k", .u32, .u32 kk)] ∧
        kk.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w2.toNat ∧ k.m + mm'.toNat ≤ mm2.toNat)
      (μ := fun env' _ => n.toNat - envU32 env' "k")
    · exact ⟨0#32, r2, rfl, by simp, w2, mm2, hb2, by simp, by simp⟩
    rintro env' st' k ⟨kk, r', rfl, hkn, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · -- all children searched: return 0
      wpc_auto
      wpc_done
    have hlt' : kk.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hk1 : (kk + 1#32).toNat = kk.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    -- r = aci_absorb(st, rop, st->pool[i + 1 + k], depth - 1);
    apply WPC.seq
    apply WPC.call IH
    split
    · trivial
    rename_i vs3 hv0
    obtain ⟨a1, t1, h1, hv1, rfl⟩ := evalArgs_cons hv0
    obtain ⟨a2, t2, h2, hv2, rfl⟩ := evalArgs_cons hv1
    obtain ⟨a3, t3, -, hv3, rfl⟩ := evalArgs_cons hv2
    obtain ⟨a4, t4, h4, hv4, rfl⟩ := evalArgs_cons hv3
    simp [evalArgs] at hv4
    subst hv4
    simp [evalE, Env.get] at h1 h2
    simp [evalE, evalBin, evalArith, Env.get] at h4
    subst h1 h2 h4
    have hd0 : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
    have hd1 : (d - 1#32).toNat < d.toNat := by rw [BitVec.toNat_sub]; simp; omega
    refine ⟨⟨⟨⟨rop, a3, d - 1#32, rfl⟩, w', mm', hb'⟩, by simp [depthArg]; omega⟩, ?_⟩
    rintro rv st3 c3 ⟨w3, mm3, hb3, hc3, hm3⟩
    rw [hb'.wk] at hc3
    rw [hb'.mk] at hm3
    split
    · trivial
    rename_i env3 hasg3
    obtain ⟨r3, rfl, rfl⟩ := assignDst_u32' hasg3 rfl
    wpc_simp
    -- if (r != 0) return r;
    apply WPC.seq
    apply WPC.ite
    embc_simp
    constructor
    · intro hr3
      -- a child found an absorbing element, or failed: return its answer
      wpc_auto
      wpc_done
    intro hr3
    subst hr3
    simp only [slackOr_apply, Option.some.injEq, Val.u32.injEq, BitVec.reduceEq, true_or,
      ↓reduceIte] at hc3
    apply WPC.skip
    wpc_simp
    apply WPC.assign
    embc_simp
    have hmk : (kk.toNat + 1) % 4294967296 = kk.toNat + 1 := by omega
    rw [hmk]
    refine ⟨?_, by omega, w3, mm3, hb3, ?_, ?_⟩
    · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hk1]
      omega
    · cost_arith
    · cost_arith
  | _ => simp [aciAbsorb, bindParams]

end Vbcf.Proof
