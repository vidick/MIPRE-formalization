/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooSetup/Infrastructure.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Core.CompletePart
public import MIPStarRE.LDT.Pasting.SwitcherooSetup.Infrastructure

@[expose] public section

/-!
# Section 12 pasting: switcheroo infrastructure

Initial switcheroo infrastructure and aggregate expansion helpers: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooSetup/Infrastructure.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position, and the switcheroo families of
`Co/Pasting/Sandwich/Switcheroo.lean` are called as `X S params …`. The slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.
The two state-free lemmas on projective submeasurements are generic:
`projSubMeas_sandwich_sum_le_one` holds in any star-ordered ring and `projSubMeas_total_sq` in
any C*-algebra with its order, so they serve `𝔓` and `K →L[ℂ] K` alike.

`switcherooAggregate_qSDDOp_expand` computes the defect in the local algebra, from
`(L a - L b)^* (L a - L b) = L ((a - b)^* (a - b))`, in place of the vendored expansion on the
joint space.

## Not ported

- `avgOver_abs_le_avgOver_abs`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr avgOver_uniform_prod
  avgOver_uniform_const uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel SubMeas ProjSubMeas IdxSubMeas IdxProjSubMeas IdxPolyFamily)

section Generic

/-- A projective sandwich family with middle operator bounded by `1` sums to at
most `1`. -/
theorem projSubMeas_sandwich_sum_le_one
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    {Outcome : Type*} [Fintype Outcome]
    (A : ProjSubMeas Outcome R)
    (B : R)
    (hB : B ≤ 1) :
    ∑ a : Outcome, A.outcome a * B * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, A.outcome a * B * A.outcome a
      ≤ ∑ a : Outcome, A.outcome a * 1 * A.outcome a :=
          Finset.sum_le_sum fun a _ => IsSelfAdjoint.conjugate_le_conjugate hB
            (A.outcome_hermitian a)
    _ = ∑ a : Outcome, A.outcome a :=
          Finset.sum_congr rfl fun a _ => by rw [mul_one, A.proj a]
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

/-- The total operator of a projective submeasurement is idempotent. -/
theorem projSubMeas_total_sq
    {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome R) :
    P.toSubMeas.total * P.toSubMeas.total = P.toSubMeas.total :=
  ProjSubMeas.total_proj P

end Generic

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Switcheroo infrastructure -/

/-- Convert the one-question switcheroo self-consistency input into the
bipartite form used by `switchSandwich`. -/
theorem switcherooSelfConsistency_bip
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (omega : ℝ)
    (hselfM : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft S params M)
      (switcherooSelfConsistencyRight S params M)
      omega) :
    Preliminaries.BipartiteSDDRel S
      (uniformDistribution (SliceQuestion params))
      (IdxProjSubMeas.toIdxSubMeas M)
      (IdxProjSubMeas.toIdxSubMeas M)
      omega :=
  ⟨hselfM.squaredDistanceBound⟩

/-- Lift slicewise complete-part self-consistency to the slice-pair distribution.

This states the `G^x` self-consistency input in the form used by the
switcheroo tensor-bound steps. -/
theorem switcherooCompletePartSelfConsistency_pairBound
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hselfG : GCompleteSelfConsistencyStatement params S family zeta) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => S.qSDDCore
          (fun g => S.L ((family.meas q.1).outcome g))
          (fun g => S.R ((family.meas q.1).outcome g))) ≤
      zeta := by
  have hprod := avgOver_uniform_prod (α := SliceQuestion params) (β := SliceQuestion params)
    (fun x _y => S.qSDDCore
      (fun g => S.L ((family.meas x).outcome g))
      (fun g => S.R ((family.meas x).outcome g)))
  refine le_of_eq_of_le (hprod.trans ?_)
    hselfG.completePartSelfConsistency.squaredDistanceBound
  exact avgOver_congr _ _ _ fun x => avgOver_uniform_const _

/-- Read the switcheroo point-product commutation hypothesis as an average
`qSDDCore` bound. -/
theorem switcherooPointProductCommutation_coreBound
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (chi : ℝ)
    (hcomm : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft S params family M)
      (switcherooPointProductRight S params family M)
      chi) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => S.qSDDCore
          (fun go => (switcherooPointProductLeft S params family M q).outcome go)
          (fun go => (switcherooPointProductRight S params family M q).outcome go)) ≤
      chi :=
  hcomm.squaredDistanceBound

/-- Expand a single-question switcheroo `qSDDOp` term into its four scalar
components. -/
theorem switcherooAggregate_qSDDOp_expand
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    S.qSDDOp
      (switcherooAggregateLeft S params family M q)
      (switcherooAggregateRight S params family M q)
      =
        ∑ o : Outcome,
          (S.ev
              (S.L
                ((M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o)) +
            S.ev
              (S.L
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total)) -
            S.ev
              (S.L
                ((M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total)) -
            S.ev
              (S.L
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o))) := by
  set G : 𝔓 := (completePartSubMeas params family q.1).total
  have hGsq : G * G = G := ProjSubMeas.total_proj (family.meas q.1)
  have hG : IsSelfAdjoint G := IsSelfAdjoint.of_nonneg (family.meas q.1).total_nonneg
  change ∑ o, S.ev (star (S.L (G * (M q.2).outcome o) - S.L ((M q.2).outcome o * G)) *
      (S.L (G * (M q.2).outcome o) - S.L ((M q.2).outcome o * G))) = _
  refine Finset.sum_congr rfl fun o _ => ?_
  set Mo : 𝔓 := (M q.2).outcome o
  have hMosq : Mo * Mo = Mo := (M q.2).proj o
  have hMo : IsSelfAdjoint Mo := (M q.2).outcome_hermitian o
  -- The defect of `G Mo` against `Mo G`, computed in the local algebra.
  have hlocal : star (G * Mo - Mo * G) * (G * Mo - Mo * G) =
      Mo * G * Mo + G * Mo * G - Mo * G * Mo * G - G * Mo * G * Mo := by
    rw [star_sub, star_mul, star_mul, hG.star_eq, hMo.star_eq]
    calc (Mo * G - G * Mo) * (G * Mo - Mo * G)
        = Mo * (G * G) * Mo + G * (Mo * Mo) * G - Mo * G * Mo * G - G * Mo * G * Mo := by
          noncomm_ring
      _ = _ := by rw [hGsq, hMosq]
  rw [S.leftTensor_sub, S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor, hlocal,
    map_sub S.L, map_sub S.L, map_add S.L, S.ev_sub, S.ev_sub, S.ev_add]

end MIPRE.LIDT.Co.Pasting

end
