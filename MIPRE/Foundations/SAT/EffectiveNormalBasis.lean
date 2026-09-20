/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.NormalElementProg
import MIPRE.Foundations.SAT.EffectiveSelfDual

/-!
# The effective self-dual normal basis theorem

Starting only with the unary odd degree, the program constructs Shoup's quotient
field, a normal element by fixed-space projections, its self-dualized Frobenius
orbit, and all multiplication-table bits. No abstract choice of a normal element
occurs in the program. The existing Shoup axiom is the sole nonstandard assumption.
-/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def shoupSelfDualNormalBasis (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier :=
  shoupSelfDualBasis k hk hodd (shoupNormalBasis k hk hodd) (shoupNormalBasis_normal k hk hodd)

theorem shoupSelfDualNormalBasis_selfDual (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    IsSelfDualBasis (shoupSelfDualNormalBasis k hk hodd) :=
  shoupSelfDualBasis_selfDual k hk hodd _ _

theorem shoupSelfDualNormalBasis_normal (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    IsNormalBasis (shoupSelfDualNormalBasis k hk hodd) :=
  shoupSelfDualBasis_normal k hk hodd _ _

/-- The uniform unary-degree basis constructor. -/
def shoupSelfDualNormalBasisProg : PolyTimeFun Unary (List BitStr) :=
  shoupSelfDualizeProg.comp ((PolyTimeFun.id _).pair shoupNormalBasisProg)

theorem shoupSelfDualNormalBasisProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    shoupSelfDualNormalBasisProg (unary k) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupSelfDualNormalBasis k hk hodd i)) := by
  change shoupSelfDualizeProg (unary k, shoupNormalBasisProg (unary k)) = _
  rw [shoupNormalBasisProg_correct k hk hodd,
    shoupSelfDualizeProg_correct k hk hodd _ (shoupNormalBasis_normal k hk hodd)]
  rfl

/-- Basis vectors in the polynomial representation, followed by products in the new basis. -/
def shoupSelfDualNormalDataProg : PolyTimeFun Unary (List BitStr × List (List BitStr)) :=
  shoupSelfDualNormalBasisProg.pair (shoupMultiplicationTableProg.comp
    ((PolyTimeFun.id _).pair shoupSelfDualNormalBasisProg))

theorem shoupSelfDualNormalDataProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    shoupSelfDualNormalDataProg (unary k) =
      (List.ofFn (fun i => (shoupBinField k hk).toBits (shoupSelfDualNormalBasis k hk hodd i)),
        List.ofFn (fun i => List.ofFn (fun j => vectorBits
          ((shoupSelfDualNormalBasis k hk hodd).equivFun
            (shoupSelfDualNormalBasis k hk hodd i * shoupSelfDualNormalBasis k hk hodd j))))) := by
  change (shoupSelfDualNormalBasisProg (unary k),
    shoupMultiplicationTableProg (unary k, shoupSelfDualNormalBasisProg (unary k))) = _
  rw [shoupSelfDualNormalBasisProg_correct k hk hodd, shoupMultiplicationTableProg_correct]

/-- The complete construction, including all table entries, takes polynomial time in degree. -/
theorem shoupSelfDualNormalDataProg_time_le : ∃ R : Polynomial ℕ, ∀ k : ℕ,
    ∃ t ≤ R.eval k, shoupSelfDualNormalDataProg.code.Runs (encode (unary k))
      (encode (shoupSelfDualNormalDataProg (unary k))) t := by
  refine ⟨shoupSelfDualNormalDataProg.timeBound.comp (2 * Polynomial.X + 1), fun k => ?_⟩
  obtain ⟨t, ht, hr⟩ := shoupSelfDualNormalDataProg.computes (unary k)
  exact ⟨t, by simpa [esize_unary] using ht, hr⟩

/-- The algorithmic self-dual normal basis theorem, with its exact ambient output and runtime. -/
theorem effective_selfDualNormalBasis : ∃ R : Polynomial ℕ, ∀ k : ℕ, ∀ hk : 1 ≤ k,
    Odd k → ∃ b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier,
      IsSelfDualBasis b ∧ IsNormalBasis b ∧
      ∃ t ≤ R.eval k, shoupSelfDualNormalDataProg.code.Runs (encode (unary k))
        (encode (List.ofFn (fun i => (shoupBinField k hk).toBits (b i)),
          List.ofFn (fun i => List.ofFn (fun j => vectorBits (b.equivFun (b i * b j)))))) t := by
  obtain ⟨R, hR⟩ := shoupSelfDualNormalDataProg_time_le
  refine ⟨R, fun k hk hodd => ?_⟩
  letI : NeZero k := ⟨by omega⟩
  refine ⟨shoupSelfDualNormalBasis k hk hodd, shoupSelfDualNormalBasis_selfDual k hk hodd,
    shoupSelfDualNormalBasis_normal k hk hodd, ?_⟩
  obtain ⟨t, ht, hr⟩ := hR k
  exact ⟨t, ht, by simpa only [shoupSelfDualNormalDataProg_correct k hk hodd] using hr⟩

end MIPRE.SAT

end
