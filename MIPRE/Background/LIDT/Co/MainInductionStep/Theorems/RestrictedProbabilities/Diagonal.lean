/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/RestrictedProbabilities/Diagonal.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.RestrictedProbabilities.Base

@[expose] public section

/-!
# Section 6 — Diagonal restricted probability bounds

The diagonal-line part of the restricted-probability bookkeeping for the main induction step:
the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Diagonal.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is the
symmetric model `strategy.state : SymModel 𝔓 K`; the vendored `qBipartiteConsDefect
strategy.state A B` and `bipartiteConsError strategy.state 𝒟 A B` are
`strategy.state.qBipartiteConsDefect A B` and `strategy.state.bipartiteConsError 𝒟 A B`
(`Co/Test/Defs.lean`), and errors are real numbers (the vendored `Error := ℝ`). The restricted
strategy keeps the state, so every restricted defect is a defect of `strategy.state`.

The restricted diagonal measurement read at the base point is the ambient one on the appended
line (`restrictDiagonalMeasurement_postprocess_zero`, Co `MainInductionStep/Defs.lean`), so
`restrictedDiagonalSampleError_eq` reduces to the identification of the appended line, as in the
vendored proof; the vendored final `simp` calls are that lemma and one rewrite. The `try rfl`
steps of the vendored file are gone.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Fq zeroCoord appendPoint embedCoord avgOver
  avgOver_congr avgOver_const_mul avgOver_uniform_comm avgOver_uniform_prod uniformDistribution
  DiagonalLine RestrictedDiagonalSample extendRestrictedDirection)
open MIPStarRE.LDT.MainInductionStep (sliceTransverseDirectionWeight
  weighted_embedded_average_le_full_average avgOver_uniform_restrictedDiagonalSample_append)
open MIPRE.LIDT.Co (SymStrat diagonalPointAnswerFamily diagonalLineAnswerFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The `j`-restricted diagonal defect of the `x`-restricted strategy at the sample `s` is the
ambient defect at the embedded index and the sample with the height appended to its base. -/
theorem restrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    strategy.state.qBipartiteConsDefect
      (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
        (xRestrictedStrategy params strategy x) j s)
      (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
        (xRestrictedStrategy params strategy x) j s) =
    strategy.state.qBipartiteConsDefect
      (diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := fun hk => hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) :=
    congrArg (DiagonalLine.mk _) hdir
  refine congrArg (strategy.state.qBipartiteConsDefect _) ?_
  refine (restrictDiagonalMeasurement_postprocess_zero params strategy x _).trans ?_
  rw [hline]
  rfl

/-- Per-index diagonal-line consistency defect of the restricted `x`-slice strategy
at embedded index `j`, averaged over the restricted diagonal sample space. -/
noncomputable def diagonalSliceIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params)
    (j : Fin params.m) : ℝ :=
  strategy.state.bipartiteConsError
    (uniformDistribution (RestrictedDiagonalSample params j))
    (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
      (xRestrictedStrategy params strategy x) j)
    (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
      (xRestrictedStrategy params strategy x) j)

/-- Per-index diagonal-line consistency defect of the ambient `(m+1)`-dimensional
strategy at index `j`, averaged over the ambient restricted diagonal sample space. -/
noncomputable def diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (j : Fin params.next.m) : ℝ :=
  strategy.state.bipartiteConsError
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (diagonalPointAnswerFamily strategy j)
    (diagonalLineAnswerFamily strategy j)

/-- Averaging the restricted per-index diagonal error over the slice height gives the ambient
per-index error at the embedded index. -/
theorem diagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => diagonalSliceIndexError params strategy x j) =
      diagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → ℝ := fun s =>
    strategy.state.qBipartiteConsDefect
      (diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => diagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) :=
        avgOver_congr _ _ _ fun x => avgOver_congr _ _ _ fun s =>
          restrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) :=
        (avgOver_uniform_prod (α := Fq params) (β := RestrictedDiagonalSample params j)
          (fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = diagonalIndexError params strategy (embedCoord params j) :=
        avgOver_uniform_restrictedDiagonalSample_append params j g

/-- The average over slice heights of the restricted diagonal failure probability is the
average over embedded indices of the ambient per-index error. -/
theorem averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => diagonalSliceIndexError params strategy x j)) := by
        refine avgOver_congr _ _ _ fun x => ?_
        simp [RestrictedSymStrat.diagonalFailureProbability, avgOver, uniformDistribution,
          Fintype.card_fin, diagonalSliceIndexError, Finset.mul_sum]
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => diagonalSliceIndexError params strategy x j)) :=
        avgOver_uniform_comm (fun x j => diagonalSliceIndexError params strategy x j)
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => diagonalIndexError params strategy (embedCoord params j)) :=
        avgOver_congr _ _ _ fun j =>
          diagonalSliceIndexErrorAverage_eq_diagonalIndexError params strategy j

/-- The weighted average of the restricted diagonal slice errors is bounded by
the ambient diagonal-line test error. -/
theorem weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma := by
  rw [avgOver_const_mul,
    averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices params strategy]
  refine (weighted_embedded_average_le_full_average params (diagonalIndexError params strategy)
    fun j => strategy.state.bipartiteConsError_nonneg _ _ _).trans ?_
  refine le_of_eq_of_le ?_ hgood.diagonalLineTest
  simp [SymStrat.diagonalFailureProbability, diagonalIndexError, avgOver, uniformDistribution,
    Fintype.card_fin, Finset.mul_sum]

end MIPRE.LIDT.Co.MainInductionStep

end
