/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourcePaddingQueryProg
import MIPRE.Foundations.Introspection.AuxiliarySourceBudget
import MIPRE.Foundations.Introspection.SourceCompilerCorrect

/-! # Legal source calls implement the padded query interface

An attained padded prefix restricts to an attained source prefix. The common
exponent-five clock therefore answers every source call used to construct
the padded factor and matrix, including the runtime dimension call.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding.Program
open Cost LowDegree.BinaryLinear AuxiliaryProgram

def sourceFamily {ℓ : ℕ} (V : Verifier ℓ) (n : ℕ) (w : Bool) :=
  V.sampler.cl (2 ^ n) (Player.ofBool w)

def queryContext {ℓ : ℕ} (V : Verifier ℓ) (lam n : ℕ) (w : Bool) (j : ℕ)
    {Q : ℕ} (u : Fin Q → CL.𝔽₂) : AuxiliarySource.Context :=
  (unary (ansBound 5 lam n), V.sampler.prog, 2 ^ n, w, j + 1, CL.toBits u)

theorem queryContext_dimension (U : ClockedUniversalMachine) {ℓ lam n : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (w : Bool) (j : ℕ) {Q : ℕ} (u : Fin Q → CL.𝔽₂) :
    dimension U (queryContext V lam n w j u) = V.sampler.dim (2 ^ n) := by
  apply dimension_correct
  simpa only [queryContext, AuxiliarySource.source, AuxiliarySource.index,
    AuxiliarySource.budget, Cost.PolyTimeFun.comp_apply, Cost.PolyTimeFun.fst_apply,
    Cost.PolyTimeFun.snd_apply, length_unary, SourceCompiler.dimensionResult] using
      SourceCompiler.bounded_dimensionResult V hV hn

theorem source_prefix_attained {ℓ n Q : ℕ} (V : Verifier ℓ)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (j : ℕ) (u : Fin Q → CL.𝔽₂)
    (hu : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x) :
    ∃ x, (CL.toBits u).take (V.sampler.dim (2 ^ n)) =
      CL.toBits (((V.sampler.cl (2 ^ n) (Player.ofBool w)).truncate j).eval x) := by
  obtain ⟨x, hx⟩ := pull_attained_prefix (firstEmbedding hQ) (sourceFamily V n) w j u hu
  refine ⟨x, ?_⟩
  rw [← toBits_pull_first hQ, hx]
  rfl

theorem factorFromContext_legal (U : ClockedUniversalMachine) {ℓ lam n Q : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (j : ℕ) (hj : j < ℓ)
    (hjR : Nat.size (j + 1) ≤ (2 ^ n) ^ lam) (u : Fin Q → CL.𝔽₂)
    (hu : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x) :
    factorFromContext U (queryContext V lam n w j u) =
      CL.indicatorBits ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).factorOfPrefix j u) := by
  rw [factorFromContext_correct U _ _ (by simpa [queryContext, AuxiliarySource.inputPrefix] using hQ)
    (queryContext_dimension U V hV hn w j u)]
  apply factor_correct U hQ (sourceFamily V n) (by omega) w j _ u rfl rfl
  have hc := AuxiliarySource.bounded_factor_result V hV hn (Player.ofBool w) (j + 1)
    ((CL.toBits u).take (V.sampler.dim (2 ^ n))) (by omega) (by omega) hjR
    (by simpa using source_prefix_attained V hQ w j u hu)
  have hr := AuxiliarySource.factor_correct U _ (unary (ansBound 5 lam n))
    V.sampler.prog (2 ^ n) w (j + 1) ((CL.toBits u).take (V.sampler.dim (2 ^ n)))
    (by simpa only [length_unary] using hc)
  simpa only [queryContext, sourceContext_apply, length_unary, Nat.add_sub_cancel,
    ofBits_take_first hQ, sourceFamily] using hr

theorem linear_legal (U : ClockedUniversalMachine) {ℓ lam n Q : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (j : ℕ) (hj : j < ℓ)
    (hjR : Nat.size (j + 1) ≤ (2 ^ n) ^ lam) (u y : Fin Q → CL.𝔽₂)
    (hu : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x) :
    linear U (CL.toBits y, unary (V.sampler.dim (2 ^ n)), queryContext V lam n w j u) =
      CL.toBits ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).mapOfPrefix j u y) := by
  rw [depthFamily_mapOfPrefix]
  apply linear_correct U hQ _ u y _ rfl
  have hc := AuxiliarySource.bounded_linear_result V hV hn (Player.ofBool w) (j + 1)
    ((CL.toBits u).take (V.sampler.dim (2 ^ n)))
    ((CL.toBits y).take (V.sampler.dim (2 ^ n))) (by omega) (by omega) hjR
    (by simpa using source_prefix_attained V hQ w j u hu)
    (by simp [CL.length_toBits, Nat.min_eq_left hQ])
  have hr := AuxiliarySource.linear_correct U _ _ (unary (ansBound 5 lam n))
    V.sampler.prog (2 ^ n) w (j + 1) ((CL.toBits u).take (V.sampler.dim (2 ^ n)))
    (by simpa only [length_unary] using hc)
  simpa only [queryContext, sourceContext_apply, length_unary, toBits_pull_first,
    Nat.add_sub_cancel, ofBits_take_first hQ, sourceFamily] using hr

theorem matrixFromContext_legal (U : ClockedUniversalMachine) {ℓ lam n Q : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (j : ℕ) (hj : j < ℓ)
    (hjR : Nat.size (j + 1) ≤ (2 ^ n) ^ lam) (u : Fin Q → CL.𝔽₂)
    (hu : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x) :
    matrixFromContext U (queryContext V lam n w j u) =
      matrixBits (LinearMap.toMatrix'
        ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).mapOfPrefix j u)) := by
  rw [matrixFromContext_correct U _ _ (by simpa [queryContext, AuxiliarySource.inputPrefix] using hQ)
    (queryContext_dimension U V hV hn w j u)]
  apply matrix_correct U (unary (V.sampler.dim (2 ^ n)), queryContext V lam n w j u)
    _ (CL.length_toBits u)
  intro y
  exact linear_legal U V hV hn hQ w j hj hjR u y hu

end MIPRE.Introspection.SourcePadding.Program
end
