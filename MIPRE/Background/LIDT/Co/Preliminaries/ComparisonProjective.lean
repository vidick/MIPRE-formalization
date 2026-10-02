/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/ComparisonProjective.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.ComparisonCore
public import MIPRE.Background.LIDT.Co.Preliminaries.ConsistencyBridges
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.Core

@[expose] public section

/-!
# Preliminary comparison theorems: projective converse

Projective-case converse of `prop:simeq-to-approx`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ComparisonProjective.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions"). As in the vendored file, the
lemma lives in a sibling module of `ComparisonCore`, and imports `ComparisonCore`,
`ConsistencyBridges` and `SwitchSandwichPrep.Core` explicitly.

As in `Co/Preliminaries/Defs.lean`, the declarations live in `MIPRE.LIDT.Co.Preliminaries` and
take the symmetric model `S : SymModel 𝔓 K` as an ordinary explicit argument in place of the
vendored state `ψ`; the projective measurements are local, with operators in `𝔓`.

For projective `A`, `B` the per-outcome square `(A_a ⊗ I - I ⊗ B_a)²` is
`A_a ⊗ I + I ⊗ B_a - 2 A_a ⊗ B_a`, because the two placements commute
(`SymModel.L_comm_R`) and each placement is idempotent; summing over outcomes gives
`qSDD = 2 (⟨1⟩ - qMatchMass) = 2 qConsDefect`. The vendored proof instead obtains
`ev (B ⊗ … · A ⊗ …) = ev (A ⊗ … · B ⊗ …)` from `ev_mul_comm_of_psd`, and the diagonal masses
from `projSubMeas_diagMass_eq_mass` on two auxiliary projective submeasurements; here the
commutation is an operator identity and the diagonal masses are the placed totals.

In the symmetric model both tensor factors are `𝔓`, and the general placements
`leftPlacedSubMeas`, `rightPlacedSubMeas`, `IdxSubMeas.placeLeft`, `placeRight` are the lifts
by `rfl` (`Co/Basic/SubMeasurementFamilies.lean`). So the `_heterogeneous` statements, whose
measurements act on the same algebra `𝔓`, follow from the same-space ones by definitional
unfolding.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_const_mul avgOver_congr)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For projective measurements `A`, `B`, twice the consistency defect of the lifts
`A_a ⊗ I` and `I ⊗ B_a` equals their squared state-dependent distance. -/
theorem two_questionConsistency_eq_questionSDD_of_projective
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : ProjMeas Outcome 𝔓) :
    2 * S.qConsDefect (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) =
      S.qSDD (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) := by
  have hterm : ∀ a, S.ev (star (S.L (A.outcome a) - S.R (B.outcome a)) *
      (S.L (A.outcome a) - S.R (B.outcome a))) =
        S.ev (S.L (A.outcome a)) + S.ev (S.R (B.outcome a)) -
          2 * S.ev (S.L (A.outcome a) * S.R (B.outcome a)) := fun a => by
    have hX : star (S.L (A.outcome a) - S.R (B.outcome a)) =
        S.L (A.outcome a) - S.R (B.outcome a) :=
      ((IsSelfAdjoint.of_nonneg (S.leftTensor_nonneg (A.outcome_pos a))).sub
        (IsSelfAdjoint.of_nonneg (S.rightTensor_nonneg (B.outcome_pos a)))).star_eq
    rw [hX, sub_mul, mul_sub, mul_sub, ← (S.L_comm_R (A.outcome a) (B.outcome a)).eq,
      S.leftTensor_mul_leftTensor, S.rightTensor_mul_rightTensor, A.proj, B.proj,
      S.ev_sub, S.ev_sub, S.ev_sub]
    ring
  have hL : ∑ a, S.ev (S.L (A.outcome a)) = S.ev 1 := by
    rw [← S.ev_sum, S.leftTensor_finset_sum, A.sum_eq_total, A.total_eq_one, S.leftTensor_one]
  have hR : ∑ a, S.ev (S.R (B.outcome a)) = S.ev 1 := by
    rw [← S.ev_sum, S.rightTensor_finset_sum, B.sum_eq_total, B.total_eq_one, S.rightTensor_one]
  have hSDD : S.qSDD (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) =
      2 * (S.ev 1 - S.qMatchMass (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S)) := by
    show ∑ a, S.ev (star (S.L (A.outcome a) - S.R (B.outcome a)) *
        (S.L (A.outcome a) - S.R (B.outcome a))) =
      2 * (S.ev 1 - ∑ a, S.ev (S.L (A.outcome a) * S.R (B.outcome a)))
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hL, hR]
    ring
  have hgap : 0 ≤ S.ev 1 - S.qMatchMass (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) := by
    have := S.qSDD_nonneg (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S)
    linarith
  have hCons : S.qConsDefect (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) =
      S.ev 1 - S.qMatchMass (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) := by
    show max 0 (S.ev (S.L A.total * S.R B.total) - _) = _
    rw [A.total_eq_one, B.total_eq_one, S.leftTensor_one, S.rightTensor_one, mul_one]
    exact max_eq_right hgap
  rw [hCons, hSDD]

/-- Projective converse of `prop:simeq-to-approx` (Proposition 4.9 of
`references/ldt-paper/preliminaries.tex` in `LionSR/MIPStarRE`, lines 426--455).

For projective measurements `A`, `B`, the `≈` relation at strength `2·δ` implies
the `≃` relation at strength `δ`, making the paper's implication an iff in the
projective case (the forward direction is `simeqToApprox`). -/
theorem approxToSimeq {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxProjMeas Question Outcome 𝔓) (δ : ℝ) :
    BipartiteSDDRel S 𝒟
        (IdxProjMeas.toIdxSubMeas A)
        (IdxProjMeas.toIdxSubMeas B) (2 * δ) →
      S.ConsRel 𝒟
        (IdxProjMeas.toIdxSubMeas A)
        (IdxProjMeas.toIdxSubMeas B) δ := by
  intro ⟨happrox⟩
  constructor
  have h : 2 * S.bipartiteConsError 𝒟 (IdxProjMeas.toIdxSubMeas A)
      (IdxProjMeas.toIdxSubMeas B) =
        S.sddError 𝒟 (IdxSubMeas.liftLeft S (IdxProjMeas.toIdxSubMeas A))
          (IdxSubMeas.liftRight S (IdxProjMeas.toIdxSubMeas B)) := by
    rw [SymModel.bipartiteConsError, ← avgOver_const_mul]
    exact avgOver_congr _ _ _ fun q =>
      two_questionConsistency_eq_questionSDD_of_projective S (A q) (B q)
  linarith

/-- For projective measurements `A`, `B`, twice the consistency defect of the placed families
`A_a ⊗ I` and `I ⊗ B_a` equals their squared state-dependent distance. In the symmetric model
the placements are the lifts, so this is
`two_questionConsistency_eq_questionSDD_of_projective`. -/
theorem two_questionConsistency_eq_questionSDD_of_projective_heterogeneous
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : ProjMeas Outcome 𝔓) (B : ProjMeas Outcome 𝔓) :
    2 * S.qConsDefect
        (S.leftPlacedSubMeas A.toSubMeas)
        (S.rightPlacedSubMeas B.toSubMeas) =
      S.qSDD
        (S.leftPlacedSubMeas A.toSubMeas)
        (S.rightPlacedSubMeas B.toSubMeas) :=
  two_questionConsistency_eq_questionSDD_of_projective S A B

/-- Heterogeneous projective converse of `prop:simeq-to-approx`.

For projective measurements acting on different tensor factors, a
state-dependent-distance estimate at strength `2·δ` for the placed families
implies the corresponding bipartite consistency statement at strength `δ`. -/
theorem approxToSimeq_heterogeneous {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxProjMeas Question Outcome 𝔓) (B : IdxProjMeas Question Outcome 𝔓)
    (δ : ℝ) :
    S.SDDRel 𝒟
        (IdxSubMeas.placeLeft S (IdxProjMeas.toIdxSubMeas A))
        (IdxSubMeas.placeRight S (IdxProjMeas.toIdxSubMeas B))
        (2 * δ) →
      S.ConsRel 𝒟
        (IdxProjMeas.toIdxSubMeas A)
        (IdxProjMeas.toIdxSubMeas B) δ :=
  fun h => approxToSimeq S 𝒟 A B δ ⟨h.squaredDistanceBound⟩

end MIPRE.LIDT.Co.Preliminaries

end
