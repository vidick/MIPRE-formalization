/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/CommonHelpers.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Families
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final

@[expose] public section

/-!
# Shared helpers for the self-improvement results

Four small lemmas reused across the self-improvement result files: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/CommonHelpers.lean` in the
port of `planning/c6b-plan.md` (milestone M10, section "Port conventions").

- `averagedPointOperator_le_one`: the averaged point operator `A_g = E_u A^u_{g(u)}` is at most
  the identity of `𝔓`.
- `bipartiteSSCRel_uniform_const`: lift a bipartite strong self-consistency from `Unit` to any
  nonempty question type. It is bipartite, so it takes the model `(S : SymModel 𝔓 K)` and a local
  submeasurement `A : SubMeas Outcome 𝔓`.
- `sddRel_uniform_const`: the same for the state-dependent distance. It uses only the state, so
  it takes a vector state `(V : VecState K)` and joint submeasurements
  `A B : SubMeas Outcome (K →L[ℂ] K)` (the vendored state is on an arbitrary carrier `κ`).
  Callers pass `strategy.state.toVecState` and should give the lifted submeasurements
  explicitly, not leave them to unification (the pitfall recorded with M3).
- `cons_rel_uniform_full_total_match_mass_lower_bound`: from `ConsRel` with complete families,
  `1 - δ ≤ E_q ∑_a ⟨Ψ, A^q_a ⊗ B^q_a Ψ⟩`. The vendored hypothesis `hψ : ψ.IsNormalized` is
  dropped: it is a theorem of the model (`VecState.ev_one_of_isNormalized`).

The vendored file imports `SelfImprovement/Theorems/Thresholds/Final.lean`, wholly classical and
without a Co file; so does this one.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Distribution avgOver uniformDistribution
  avgOver_mono avgOver_sub avgOver_uniform_const)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Shared scalar bounds -/

/-- Internal helper: the averaged point operator for any polynomial is bounded by `1`. -/
theorem averagedPointOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (g : MIPStarRE.LDT.Polynomial params) :
    averagedPointOperator params strategy g ≤ 1 :=
  averageOperatorOverDistribution_uniform_le_one _ fun u =>
    Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u)

/-- Internal helper: lift bipartite SSC from `Unit` to any nonempty question type. -/
theorem bipartiteSSCRel_uniform_const
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : SubMeas Outcome 𝔓) (δ : ℝ) :
    S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily A) δ →
      S.BipartiteSSCRel (uniformDistribution Question) (fun _ : Question => A) δ := by
  rintro ⟨hssc⟩
  refine ⟨le_of_eq_of_le ?_ hssc⟩
  exact (avgOver_uniform_const (α := Question) _).trans (avgOver_uniform_const (α := Unit) _).symm

/-- Internal helper: lift SDD from `Unit` to any nonempty question type. -/
theorem sddRel_uniform_const
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (V : VecState K)
    (A B : SubMeas Outcome (K →L[ℂ] K)) (δ : ℝ) :
    V.SDDRel (uniformDistribution Unit) (constSubMeasFamily A) (constSubMeasFamily B) δ →
      V.SDDRel (uniformDistribution Question) (fun _ : Question => A)
        (fun _ : Question => B) δ := by
  rintro ⟨hsdd⟩
  refine ⟨le_of_eq_of_le ?_ hsdd⟩
  exact (avgOver_uniform_const (α := Question) _).trans (avgOver_uniform_const (α := Unit) _).symm

/-- Internal helper: from `ConsRel` with total-1 families,
derive `1 - δ ≤ avgOver matchMass`. Used by `input_consistency_match_mass_lower_bound`. (The
vendored hypothesis `hψ : ψ.IsNormalized` is a theorem of the model.) -/
theorem cons_rel_uniform_full_total_match_mass_lower_bound
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A B : IdxSubMeas Question Outcome 𝔓)
    (δ : ℝ)
    (hA_total : ∀ q : Question, (A q).total = 1)
    (hB_total : ∀ q : Question, (B q).total = 1)
    (hcons : S.ConsRel (uniformDistribution Question) A B δ) :
    1 - δ ≤ avgOver (uniformDistribution Question)
      (fun q => S.qBipartiteMatchMass (A q) (B q)) := by
  let 𝒟 := uniformDistribution Question
  have hdefect_point (q : Question) :
      1 - S.qBipartiteMatchMass (A q) (B q) ≤ S.qBipartiteConsDefect (A q) (B q) := by
    have htotal : S.ev (S.opTensor (A q).total (B q).total) = 1 := by
      rw [hA_total q, hB_total q, SymModel.opTensor, map_one, map_one, one_mul,
        S.ev_one_of_isNormalized]
    unfold SymModel.qBipartiteConsDefect
    rw [htotal]
    exact le_max_right 0 _
  have havg_defect :
      avgOver 𝒟 (fun q => 1 - S.qBipartiteMatchMass (A q) (B q)) ≤ δ :=
    (avgOver_mono 𝒟 _ _ hdefect_point).trans hcons.offDiagonalBound
  rw [avgOver_sub 𝒟 (fun _ => 1), avgOver_uniform_const] at havg_defect
  linarith

end MIPRE.LIDT.Co.SelfImprovement

end
