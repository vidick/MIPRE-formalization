/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Core/
CompletePart.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Statements
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.Extensions
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Core.CompletePart

@[expose] public section

/-!
# Section 12 pasting: complete and incomplete part self-consistency

State-dependent-distance consequences for the complete and incomplete parts of the pasted slice
family: the counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Core/CompletePart.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position, as in `Co/Pasting/Statements.lean`; the
slice family is an `IdxPolyFamily params 𝔓`. The vendored hypotheses `PermInvState ψbi` of
`gCompleteSelfConsistency`, `gBotSelfConsistency_ofCompleteSelfConsistency` and
`gBotSelfConsistency` were unused there and are dropped (section "Swap symmetry is a theorem").

Each placed projector `X` contributes `ev((L X - R X)^* (L X - R X)) = 2 (ev L X - ev(L X R X))`
(`Preliminaries.ev_adjoint_self_leftTensor_sub_rightTensor`), so the complete-part bound is the
matching-mass monotonicity under the readout `g ↦ ()`
(`Preliminaries.qMatchMass_leftRight_postprocess_ge`), in place of the vendored entrywise
Kronecker expansions; and the incomplete part has the same distance as the complete part because
`L (1 - T) - R (1 - T) = R T - L T`.

## Not ported

- `first_construction_scalar_inequality`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_mono uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion)
open MIPRE.LIDT.Co (SymModel SubMeas IdxSubMeas IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `lem:q-sdd-complete-part-slice-bound`: the complete part `G^x` of a slice is no farther from
its right placement than the slice measurement itself. -/
theorem qSDD_completePart_le_slice
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (x : Fq params) :
    S.qSDD
        ((completePartSubMeas params family x).liftLeft S)
        ((completePartSubMeas params family x).liftRight S)
      ≤
    S.qSDD
        (((family.meas x).toSubMeas).liftLeft S)
        (((family.meas x).toSubMeas).liftRight S) := by
  set P := family.meas x with hP
  -- A placed projector contributes `2 (ev L X - ev (L X R X))`.
  have hproj : ∀ X : 𝔓, 0 ≤ X → X * X = X →
      S.ev (star (S.L X - S.R X) * (S.L X - S.R X)) =
        2 * (S.ev (S.L X) - S.ev (S.opTensor X X)) := by
    intro X hX0 hXX
    rw [Preliminaries.ev_adjoint_self_leftTensor_sub_rightTensor S (IsSelfAdjoint.of_nonneg hX0),
      hXX]
  have hcomplete :
      S.qSDD ((completePartSubMeas params family x).liftLeft S)
          ((completePartSubMeas params family x).liftRight S) =
        2 * (S.ev (S.L P.total) - S.ev (S.opTensor P.total P.total)) := by
    change ∑ u : Unit, S.ev (star (S.L ((completePartSubMeas params family x).outcome u) -
        S.R ((completePartSubMeas params family x).outcome u)) *
        (S.L ((completePartSubMeas params family x).outcome u) -
          S.R ((completePartSubMeas params family x).outcome u))) = _
    rw [Fintype.sum_unique, completePartSubMeas_outcome_unit, completePartSubMeas_total,
      hproj _ P.total_nonneg (ProjSubMeas.total_proj P)]
  have horig :
      S.qSDD (((family.meas x).toSubMeas).liftLeft S) (((family.meas x).toSubMeas).liftRight S) =
        2 * (S.ev (S.L P.total) - ∑ g, S.ev (S.opTensor (P.outcome g) (P.outcome g))) := by
    change ∑ g, S.ev (star (S.L (P.outcome g) - S.R (P.outcome g)) *
        (S.L (P.outcome g) - S.R (P.outcome g))) = _
    rw [Finset.sum_congr rfl fun g _ => hproj _ (P.outcome_pos g) (P.proj g), ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← S.ev_sum, S.leftTensor_finset_sum, P.sum_eq_total]
  have hmatch :
      ∑ g, S.ev (S.opTensor (P.outcome g) (P.outcome g)) ≤ S.ev (S.opTensor P.total P.total) := by
    have h := Preliminaries.qMatchMass_leftRight_postprocess_ge S P.toSubMeas P.toSubMeas
      (fun _ => ())
    change ∑ u : Unit, S.ev (S.L ((completePartSubMeas params family x).outcome u) *
        S.R ((completePartSubMeas params family x).outcome u)) ≥
      ∑ g, S.ev (S.L (P.outcome g) * S.R (P.outcome g)) at h
    rwa [Fintype.sum_unique, completePartSubMeas_outcome_unit, completePartSubMeas_total] at h
  rw [hcomplete, horig]
  linarith

/-- `lem:g-complete-self-consistency`.
This is exactly the slice strong self-consistency hypothesis, stated under
the Section 12 statement name. -/
theorem gCompleteSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent S zeta) :
    GCompleteSelfConsistencyStatement params S family zeta :=
  ⟨hself.sliceSelfConsistency⟩

/-- Internal form of `cor:g-bot-self-consistency` after applying
`lem:g-complete-self-consistency`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:537-558`
uses `lem:g-complete-self-consistency` internally.  The paper-facing theorem
`gBotSelfConsistency` below derives that input from strong self-consistency
rather than exposing it as a public hypothesis. -/
theorem gBotSelfConsistency_ofCompleteSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hcomplete : GCompleteSelfConsistencyStatement params S family zeta) :
    GBotSelfConsistencyStatement params S family zeta := by
  refine ⟨⟨le_trans ?_ hcomplete.completePartSelfConsistency.squaredDistanceBound⟩⟩
  refine avgOver_mono _ _ _ fun x =>
    le_of_eq_of_le ?_ (qSDD_completePart_le_slice params S family x)
  -- `L (1 - T) - R (1 - T) = -(L T - R T)`, and the defect is even.
  set T := (completePartSubMeas params family x).total
  have hdiff : S.L (1 - T) - S.R (1 - T) = -(S.L T - S.R T) := by
    rw [← S.leftTensor_sub, ← S.rightTensor_sub, S.leftTensor_one, S.rightTensor_one]
    abel
  change ∑ u : Unit, S.ev (star (S.L (1 - T) - S.R (1 - T)) * (S.L (1 - T) - S.R (1 - T))) =
    ∑ u : Unit, S.ev (star (S.L ((completePartSubMeas params family x).outcome u) -
        S.R ((completePartSubMeas params family x).outcome u)) *
      (S.L ((completePartSubMeas params family x).outcome u) -
        S.R ((completePartSubMeas params family x).outcome u)))
  rw [Fintype.sum_unique, Fintype.sum_unique, completePartSubMeas_outcome_unit, hdiff, star_neg,
    neg_mul_neg]

/-- `cor:g-bot-self-consistency`, source-facing form. -/
theorem gBotSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent S zeta) :
    GBotSelfConsistencyStatement params S family zeta :=
  gBotSelfConsistency_ofCompleteSelfConsistency params S family zeta
    (gCompleteSelfConsistency params S family zeta hself)

end MIPRE.LIDT.Co.Pasting

end
