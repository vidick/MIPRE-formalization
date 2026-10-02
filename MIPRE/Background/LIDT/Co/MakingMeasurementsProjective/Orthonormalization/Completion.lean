/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/Completion.lean, to the symmetric
model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Statements
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Orthonormalization.RestrictSome
public import MIPRE.Background.LIDT.Co.Test.StrategyCore
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz

@[expose] public section

/-!
# Option completion in the orthonormalization argument

The auxiliary algebra used when the orthonormalization theorem is applied to the completion of a
submeasurement by a fresh failure outcome, comparing the completed measurement with the
restriction obtained by discarding this outcome: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/Completion.lean`
in the port of `planning/c6b-plan.md` (milestone M8, section "Port conventions").

Both lemmas take a symmetric model `S : SymModel 𝔓 K` and a local submeasurement in `𝔓`. The
vendored hypotheses `hperm : PermInvState ψ` and `hψ : ψ.IsNormalized` of
`optionCompletion_bipartiteSSCRel` are dropped: the swap step is `S.ev_L_eq_ev_R` and
`S.ev 1 = 1` is a theorem. The vendored `A.liftLeft` is `A.map S.L`. The vendored proof bounds
the overlap of the totals through `Preliminaries.qBipartiteSSCDefect_postprocess_le` at the
constant readout; here the same bound, `∑ₐ ⟨Ψ, (Aₐ ⊗ Aₐ) Ψ⟩ ≤ ⟨Ψ, (T ⊗ T) Ψ⟩` for the total
`T`, is the positivity of the off-diagonal overlaps, as in step 2 of
`SymModel.one_sub_sum_norm_sq_completion_le` (`Co/Doubling/Orthonormalization.lean`).

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MakingMeasurementsProjective

open MIPStarRE.LDT (avgOver uniformDistribution)

namespace Orthonormalization
namespace Completion

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Completing a submeasurement by a fresh failure outcome preserves bipartite
strong self-consistency up to the paper's factor `2`: the original diagonal gap
controls the original outcomes, and the same gap controls the residual `none`
outcome after applying the swap symmetry of the model. -/
theorem optionCompletion_bipartiteSSCRel {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) (ζ : ℝ) :
    S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily A) ζ →
      S.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily (optionCompletion A).toSubMeas) (2 * ζ) := by
  intro hssc
  have havg : ∀ f : Unit → ℝ, avgOver (uniformDistribution Unit) f = f () := fun f => by
    simp [avgOver, uniformDistribution]
  have horig : S.qBipartiteSSCDefect A ≤ ζ := by
    have := hssc.overlapBound
    rwa [SymModel.bipartiteSSCError, havg] at this
  have hζ : 0 ≤ ζ := (S.qBipartiteSSCDefect_nonneg A).trans horig
  set t := A.total
  set b : 𝔓 → 𝔓 → ℝ := fun x y => S.ev (S.L x * S.R y) with hb
  -- the overlap of the totals dominates the diagonal overlaps
  have htt : ∑ a, b (A.outcome a) (A.outcome a) ≤ b t t := by
    have : b t t = ∑ a, ∑ a', b (A.outcome a) (A.outcome a') := by
      simp only [hb, t, ← A.sum_eq_total, map_sum, Finset.sum_mul_sum, S.ev_sum]
    rw [this]
    exact Finset.sum_le_sum fun a _ => Finset.single_le_sum
      (fun a' _ => S.ev_nonneg_of_psd _ (S.opTensor_nonneg (A.outcome_pos a) (A.outcome_pos a')))
      (Finset.mem_univ a)
  -- the overlap of the residual, by the swap symmetry
  have hnone : b (1 - t) (1 - t) = 1 - 2 * S.ev (S.L t) + b t t := by
    have h1 : S.L (1 - t) * S.R (1 - t) = 1 - S.L t - S.R t + S.L t * S.R t := by
      rw [map_sub, map_sub, map_one, map_one]
      noncomm_ring
    simp only [hb, h1, VecState.ev_add, VecState.ev_sub, VecState.ev_one_of_isNormalized,
      ← S.ev_L_eq_ev_R]
    ring
  have hsum : ∑ o, b ((optionCompletion A).outcome o) ((optionCompletion A).outcome o) =
      b (1 - t) (1 - t) + ∑ a, b (A.outcome a) (A.outcome a) :=
    Fintype.sum_option _
  have hdef : S.ev (S.L t) - ∑ a, b (A.outcome a) (A.outcome a) ≤ ζ :=
    (le_max_right _ _).trans horig
  refine ⟨?_⟩
  rw [SymModel.bipartiteSSCError, havg]
  refine max_le (by positivity) ?_
  change S.ev (S.L 1) - ∑ o, b ((optionCompletion A).outcome o) ((optionCompletion A).outcome o)
    ≤ 2 * ζ
  rw [S.leftTensor_one, VecState.ev_one_of_isNormalized, hsum, hnone]
  linarith

/-- Discarding the extra `none` outcome from the option-completed measurement can
only decrease the `qSDD` sum: one simply drops a nonnegative summand. -/
theorem qSDD_liftLeft_restrictSomeProjSubMeas_le {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) (P : ProjSubMeas (Option Outcome) 𝔓) :
    S.qSDD (A.map S.L) ((restrictSomeProjSubMeas P).toSubMeas.map S.L) ≤
      S.qSDD ((optionCompletion A).toSubMeas.map S.L) (P.toSubMeas.map S.L) := by
  simp only [VecState.qSDD, VecState.qSDDCore]
  rw [Fintype.sum_option]
  exact le_add_of_nonneg_left (S.ev_adjoint_self_nonneg _)

end Completion
end Orthonormalization

end MIPRE.LIDT.Co.MakingMeasurementsProjective

end
