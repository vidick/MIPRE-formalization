/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Completion.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Core

@[expose] public section

/-!
# Preliminary comparison theorems: bipartite self-consistency (completion)

Completion-transfer lemmas for bipartite self-consistency: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Completion.lean` in
the port of `planning/c6b-plan.md` (milestone M3, section "Port conventions"). The constant
`Unit`-family reductions identify `sddError` and `sscError` with their pointwise forms, and the
later lemmas compare a submeasurement with its completion.

The vendored state of `constFamily_sdd_unit`, `constFamily_ssc_unit` and
`completion_self_distance` is a state on one space, so they take a vector state
`V : VecState K` and submeasurements of joint operators in `K →L[ℂ] K`.
`evaluateAt_completeAtOutcome` mentions no state and is generic over the ordered `⋆`-ring of
`evaluateAt` and `completeAtOutcome`. `qBipartiteConsDefect_completeAtOutcome_right_le` is
stated over `ψ : QuantumState (ιA × ιB)` with local measurements on two different spaces; it
takes a symmetric model `S : SymModel 𝔓 K`, with both measurements in `𝔓`, as every bipartite
defect of the port does (section "Port conventions", same-space and bipartite quantities). Its
proof bounds the matching mass of the completion below by monotonicity of `S.opTensor`, where
the vendored proof computes it exactly.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Parameters FieldModel Point Distribution avgOver uniformDistribution)

section State

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For a constant `Unit`-indexed family, `sddError` reduces to `qSDD`. -/
theorem constFamily_sdd_unit {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B : SubMeas Outcome (K →L[ℂ] K)) :
    V.sddError (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) =
      V.qSDD A B := by
  simp [VecState.sddError, avgOver, uniformDistribution, constSubMeasFamily]

/-- For a constant `Unit`-indexed family, `sscError` reduces to `qSSCDefect`. -/
theorem constFamily_ssc_unit {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : SubMeas Outcome (K →L[ℂ] K)) :
    V.sscError (uniformDistribution Unit) (constSubMeasFamily A) =
      V.qSSCDefect A := by
  simp [VecState.sscError, avgOver, uniformDistribution, constSubMeasFamily]

/-- Completing `B` at `a0` changes only the missing mass, so the self-distance is
exactly the squared residual mass. -/
theorem completion_self_distance {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (B : SubMeas Outcome (K →L[ℂ] K)) (a0 : Outcome) :
    V.qSDD B (completeAtOutcome B a0).toSubMeas =
      V.ev ((1 - B.total) * (1 - B.total)) := by
  have hR : star (1 - B.total) = 1 - B.total :=
    (IsSelfAdjoint.of_nonneg (sub_nonneg.mpr B.total_le_one)).star_eq
  refine (Finset.sum_eq_single a0 (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ a0) h)).trans
    ?_
  · simp [completeAtOutcome, ha, V.ev_zero]
  · simp only [completeAtOutcome, ↓reduceDIte, sub_add_cancel_left, star_neg, neg_mul_neg, hR]

end State

section Evaluation

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- Evaluating a completed polynomial submeasurement at a point is the same as
completing the evaluated submeasurement at the induced outcome. -/
theorem evaluateAt_completeAtOutcome
    (params : Parameters) [FieldModel params.q]
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) R)
    (h0 : MIPStarRE.LDT.Polynomial params)
    (u : Point params) :
    evaluateAt params u (completeAtOutcome H h0).toSubMeas =
      (completeAtOutcome (evaluateAt params u H) (h0 u)).toSubMeas := by
  classical
  refine SubMeas.ext (fun b => ?_) rfl
  simp only [evaluateAt, SubMeas.postprocess_outcome, completeAtOutcome]
  rw [Finset.sum_congr rfl fun h _ =>
    (show (if hh : h = h0 then H.outcome h + (1 - H.total) else H.outcome h) =
      H.outcome h + if h = h0 then 1 - H.total else 0 by split_ifs <;> simp),
    Finset.sum_add_distrib, Finset.sum_ite_eq']
  by_cases hb : b = h0 u
  · subst hb
    simp [postprocess_total]
  · simp [hb, Ne.symm hb]

end Evaluation

section Model

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Completing the right submeasurement can increase the bipartite consistency
defect by at most the residual completion mass `1 - B.total`. -/
theorem qBipartiteConsDefect_completeAtOutcome_right_le {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : Measurement Outcome 𝔓)
    (B : SubMeas Outcome 𝔓)
    (a0 : Outcome) :
    S.qBipartiteConsDefect A.toSubMeas (completeAtOutcome B a0).toSubMeas ≤
      S.qBipartiteConsDefect A.toSubMeas B + S.ev (S.R (1 - B.total)) := by
  have hR : 0 ≤ 1 - B.total := sub_nonneg.mpr B.total_le_one
  have hmatch : S.qBipartiteMatchMass A.toSubMeas B ≤
      S.qBipartiteMatchMass A.toSubMeas (completeAtOutcome B a0).toSubMeas :=
    Finset.sum_le_sum fun a _ => S.ev_mono _ _ <| S.opTensor_mono_right (A.outcome_pos a) <| by
      by_cases ha : a = a0
      · simpa [completeAtOutcome, ha] using hR
      · simp [completeAtOutcome, ha]
  have htotal :
      S.ev (S.opTensor A.total (completeAtOutcome B a0).total) =
        S.ev (S.opTensor A.total B.total) + S.ev (S.R (1 - B.total)) := by
    rw [(completeAtOutcome B a0).total_eq_one, A.total_eq_one]
    show S.ev (S.L 1 * S.R 1) = S.ev (S.L 1 * S.R B.total) + _
    rw [S.leftTensor_one, one_mul, one_mul, ← S.ev_add, ← map_add S.R, add_sub_cancel]
  have hB : S.ev (S.opTensor A.total B.total) - S.qBipartiteMatchMass A.toSubMeas B ≤
      S.qBipartiteConsDefect A.toSubMeas B := le_max_right 0 _
  exact max_le (add_nonneg (S.qBipartiteConsDefect_nonneg _ _)
    (S.ev_nonneg_of_psd _ (S.rightTensor_nonneg hR))) (by
      show S.ev (S.opTensor A.total (completeAtOutcome B a0).total) - _ ≤ _
      linarith)

end Model

end MIPRE.LIDT.Co.Preliminaries

end
