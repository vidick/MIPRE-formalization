/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooContraction/Split.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooSetup.Terms

@[expose] public section

/-!
# Section 12 pasting: switcheroo split contraction

The split-form contraction and the first mixed-term transfer: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooContraction/Split.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.
The vendored hypothesis `hnorm : ψbi.IsNormalized` of
`switcherooAggregateFourthTerm_split_close_once_commuted` and
`switcherooAggregateFourthTerm_once_commuted_close_mixed` is dropped, normalization being a
theorem of the model (section "Swap symmetry is a theorem"): callers pass
`params S family M chi hcomm` and `params S family M zeta hselfG`.

The two contraction witnesses place operators by `leftTensor (ι₂ := ι)` without a state in the
vendored file; here they take the model as an explicit first argument
(`switcherooAggregateFourthTerm_split_contraction S params family M q`, and the same for
`switcherooAggregateFourthTerm_once_commuted_contraction_left`), as M3's and M7's placement
lemmas do. Both are proved in the local algebra `𝔓` and pushed through `S.L` by
`S.leftTensor_le_one`, in place of the vendored `conjTranspose_opTensor` and `opTensor_mono_left`
with the identity on the second factor; the Hermitian facts come from `IsSelfAdjoint.of_nonneg`
rather than `Matrix.PosSemidef`.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Distribution avgOver uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel SubMeas ProjSubMeas IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Shared switcheroo contraction helper definitions -/

/-- The `g`-indexed sandwich family used in the once-commuted contraction bounds. -/
noncomputable def switcherooAggregateFourthTermX
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    MIPStarRE.LDT.Polynomial params → 𝔓 :=
  fun g => ∑ o : Outcome, (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o

/-- The complete-part total operator is Hermitian. -/
theorem switcherooCompletePartTotal_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (q : SlicePairQuestion params) :
    star (completePartSubMeas params family q.1).total =
      (completePartSubMeas params family q.1).total :=
  (IsSelfAdjoint.of_nonneg (completePartSubMeas params family q.1).total_nonneg).star_eq

/-- The complete-part total operator is idempotent. -/
theorem switcherooCompletePartTotal_sq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total *
        (completePartSubMeas params family q.1).total =
      (completePartSubMeas params family q.1).total :=
  projSubMeas_total_sq (family.meas q.1)

/-- The complete-part total operator is bounded by the identity. -/
theorem switcherooCompletePartTotal_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total ≤ 1 :=
  (completePartSubMeas params family q.1).total_le_one

/-- Every outcome of the external projective family is Hermitian. -/
theorem switcherooMeasuredOutcome_hermitian
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params)
    (o : Outcome) :
    star ((M q.2).outcome o) = (M q.2).outcome o :=
  (M q.2).outcome_hermitian o

/-- Every slice outcome of the completed family is Hermitian. -/
theorem switcherooSliceOutcome_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (q : SlicePairQuestion params)
    (g : MIPStarRE.LDT.Polynomial params) :
    star ((family.meas q.1).outcome g) = (family.meas q.1).outcome g :=
  (family.meas q.1).outcome_hermitian g

/-- The shared `X_g` sandwich family is Hermitian pointwise. -/
theorem switcherooAggregateFourthTermX_hermitian
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params)
    (g : MIPStarRE.LDT.Polynomial params) :
    star (switcherooAggregateFourthTermX params family M q g) =
      switcherooAggregateFourthTermX params family M q g := by
  unfold switcherooAggregateFourthTermX
  rw [star_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [star_mul, star_mul, switcherooMeasuredOutcome_hermitian params M q o,
    switcherooSliceOutcome_hermitian params family q g, mul_assoc]

/-- The shared `X_g` sandwich family is positive pointwise. -/
theorem switcherooAggregateFourthTermX_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params)
    (g : MIPStarRE.LDT.Polynomial params) :
    0 ≤ switcherooAggregateFourthTermX params family M q g :=
  Finset.sum_nonneg fun o _ => IsSelfAdjoint.conjugate_nonneg
    ((family.meas q.1).outcome_pos g) (switcherooMeasuredOutcome_hermitian params M q o)

/-- The shared `X_g` sandwich family is bounded by the identity pointwise. -/
theorem switcherooAggregateFourthTermX_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params)
    (g : MIPStarRE.LDT.Polynomial params) :
    switcherooAggregateFourthTermX params family M q g ≤ 1 :=
  projSubMeas_sandwich_sum_le_one (M q.2) ((family.meas q.1).outcome g)
    ((family.meas q.1).outcome_le_one g)

/-- The shared `X_g` sandwich family satisfies `X_g^2 ≤ X_g`. -/
theorem switcherooAggregateFourthTermX_sq_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params)
    (g : MIPStarRE.LDT.Polynomial params) :
    switcherooAggregateFourthTermX params family M q g *
        switcherooAggregateFourthTermX params family M q g ≤
      switcherooAggregateFourthTermX params family M q g :=
  MIPRE.LIDT.Co.sq_le_self
    (switcherooAggregateFourthTermX_nonneg params family M q g)
    (switcherooAggregateFourthTermX_le_one params family M q g)

/-- Summing the shared `X_g` family collapses to the middle sandwich term. -/
theorem switcherooAggregateFourthTermX_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    ∑ g : MIPStarRE.LDT.Polynomial params, switcherooAggregateFourthTermX params family M q g =
      ∑ o : Outcome,
        (M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o := by
  unfold switcherooAggregateFourthTermX
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, (family.meas q.1).sum_eq_total]
  rfl

/-- The middle sandwich sum used in the contraction bounds is a contraction. -/
theorem switcherooAggregateFourthTerm_middle_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    ∑ o : Outcome,
        (M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o ≤ 1 :=
  projSubMeas_sandwich_sum_le_one (M q.2) ((completePartSubMeas params family q.1).total)
    (switcherooCompletePartTotal_le_one params family q)

/-- Contraction witness for the first `sqrt chi` switcheroo transfer. -/
theorem switcherooAggregateFourthTerm_split_contraction
    (S : SymModel 𝔓 K)
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    (∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
        S.L
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1) *
        star (S.L
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1))) ≤ 1 := by
  set G : 𝔓 := (completePartSubMeas params family q.1).total
  set Gq : MIPStarRE.LDT.Polynomial params → 𝔓 := (family.meas q.1).outcome
  set Mo : Outcome → 𝔓 := (M q.2).outcome
  have hG : star G = G := switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := switcherooCompletePartTotal_sq params family q
  have hMo : ∀ o, star (Mo o) = Mo o := switcherooMeasuredOutcome_hermitian params M q
  have hGq : ∀ g, star (Gq g) = Gq g := switcherooSliceOutcome_hermitian params family q
  -- The sum, computed in the local algebra.
  have hlocal : ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      G * Mo go.2 * Gq go.1 * star (G * Mo go.2 * Gq go.1) =
        G * (∑ o : Outcome, Mo o * G * Mo o) * G := by
    have hterm : ∀ go : MIPStarRE.LDT.Polynomial params × Outcome,
        G * Mo go.2 * Gq go.1 * star (G * Mo go.2 * Gq go.1) =
          G * Mo go.2 * Gq go.1 * Mo go.2 * G := fun go => by
      rw [star_mul, star_mul, hG, hMo, hGq]
      simp only [mul_assoc]
      rw [← mul_assoc (Gq go.1) (Gq go.1), (family.meas q.1).proj go.1]
    simp only [hterm]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun o _ => ?_
    dsimp only
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, (family.meas q.1).sum_eq_total]
    change G * Mo o * G * Mo o * G = _
    simp only [mul_assoc]
  have hmid : ∑ o : Outcome, Mo o * G * Mo o ≤ 1 :=
    switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  have hsandwich : G * (∑ o : Outcome, Mo o * G * Mo o) * G ≤ 1 :=
    calc G * (∑ o : Outcome, Mo o * G * Mo o) * G ≤ G * 1 * G :=
          IsSelfAdjoint.conjugate_le_conjugate hmid hG
      _ = G := by rw [mul_one, hGsq]
      _ ≤ 1 := switcherooCompletePartTotal_le_one params family q
  simp only [S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  rw [S.leftTensor_finset_sum, hlocal]
  exact S.leftTensor_le_one hsandwich

/-- The first `sqrt chi` step in the fourth-term switcheroo chain. -/
theorem switcherooAggregateFourthTerm_split_close_once_commuted
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
    |switcherooAggregateFourthTerm params S family M -
        avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
            S.ev
              (S.L
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1)))| ≤
      Real.sqrt chi := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params × Outcome → K →L[ℂ] K :=
    fun q go => (switcherooPointProductLeft S params family M q).outcome go
  let B : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params × Outcome → K →L[ℂ] K :=
    fun q go => (switcherooPointProductRight S params family M q).outcome go
  let C : SlicePairQuestion params →
      MIPStarRE.LDT.Polynomial params × Outcome → Unit → K →L[ℂ] K :=
    fun q go _ =>
      S.L
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome go.2 *
          (family.meas q.1).outcome go.1)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 :=
    uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAB : avgOver 𝒟q (fun q => S.toVecState.qSDDCore (A q) (B q)) ≤ chi :=
    switcherooPointProductCommutation_coreBound params S family M chi hcomm
  have hC : ∀ q,
      (∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
          (∑ u : Unit, C q go u) * star (∑ u : Unit, C q go u)) ≤ 1 := fun q => by
    simp only [Fintype.sum_unique]
    exact switcherooAggregateFourthTerm_split_contraction S params family M q
  have hclose :=
    Preliminaries.closenessOfInnerProduct_left S.toVecState 𝒟q h𝒟q A B C chi hAB hC
  have hleft : (fun q => ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      ∑ u : Unit, S.ev (C q go u * A q go)) = fun q =>
        ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
          S.ev
            (S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2)) := by
    funext q
    refine Finset.sum_congr rfl fun go _ => ?_
    rw [Fintype.sum_unique]
    change S.ev (S.L _ * S.L ((family.meas q.1).outcome go.1 * (M q.2).outcome go.2)) = _
    rw [S.leftTensor_mul_leftTensor]
    simp only [mul_assoc]
  have hright : (fun q => ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
      ∑ u : Unit, S.ev (C q go u * B q go)) = fun q =>
        ∑ go : MIPStarRE.LDT.Polynomial params × Outcome,
          S.ev
            (S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1)) := by
    funext q
    refine Finset.sum_congr rfl fun go _ => ?_
    rw [Fintype.sum_unique]
    change S.ev (S.L _ * S.L ((M q.2).outcome go.2 * (family.meas q.1).outcome go.1)) = _
    rw [S.leftTensor_mul_leftTensor]
    simp only [mul_assoc]
  rw [hleft, hright, ← switcherooAggregateFourthTerm_eq_split params S family M] at hclose
  exact hclose

/-- Left-action contraction witness for the first `sqrt zeta` transfer. -/
theorem switcherooAggregateFourthTerm_once_commuted_contraction_left
    (S : SymModel 𝔓 K)
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (q : SlicePairQuestion params) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
        (∑ o : Outcome,
            S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o)) *
          star (∑ o : Outcome,
            S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))) ≤ 1 := by
  set G : 𝔓 := (completePartSubMeas params family q.1).total
  set X : MIPStarRE.LDT.Polynomial params → 𝔓 := switcherooAggregateFourthTermX params family M q
  have hG : star G = G := switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := switcherooCompletePartTotal_sq params family q
  have hX : ∀ g, star (X g) = X g := switcherooAggregateFourthTermX_hermitian params family M q
  have hXsq : ∀ g, X g * X g ≤ X g := switcherooAggregateFourthTermX_sq_le params family M q
  have hrow : ∀ g, ∑ o : Outcome,
      G * (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o = G * X g :=
    fun g => by
      simp only [X, switcherooAggregateFourthTermX, Finset.mul_sum, mul_assoc]
  -- The sum, bounded in the local algebra.
  have hlocal : ∑ g, G * X g * star (G * X g) ≤ 1 :=
    calc ∑ g, G * X g * star (G * X g)
        = ∑ g, G * (X g * X g) * G := Finset.sum_congr rfl fun g _ => by
          rw [star_mul, hX, hG]; simp only [mul_assoc]
      _ ≤ ∑ g, G * X g * G := Finset.sum_le_sum fun g _ =>
          IsSelfAdjoint.conjugate_le_conjugate (hXsq g) hG
      _ = G * (∑ g, X g) * G := by rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ G * 1 * G := by
          refine IsSelfAdjoint.conjugate_le_conjugate ?_ hG
          rw [switcherooAggregateFourthTermX_sum params family M q]
          exact switcherooAggregateFourthTerm_middle_sum_le_one params family M q
      _ = G := by rw [mul_one, hGsq]
      _ ≤ 1 := switcherooCompletePartTotal_le_one params family q
  simp only [S.leftTensor_finset_sum, hrow, S.leftTensor_conjTranspose,
    S.leftTensor_mul_leftTensor]
  exact S.leftTensor_le_one hlocal

/-- The first `sqrt zeta` step in the fourth-term switcheroo chain. -/
theorem switcherooAggregateFourthTerm_once_commuted_close_mixed
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta : ℝ)
    (hselfG : GCompleteSelfConsistencyStatement params S family zeta) :
    |avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
          S.ev
            (S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o *
                (family.meas q.1).outcome g))) -
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ g : MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
          S.ev
            (S.L
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o) *
              S.R ((family.meas q.1).outcome g)))| ≤
      Real.sqrt zeta := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun q g => S.L ((family.meas q.1).outcome g)
  let B : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun q g => S.R ((family.meas q.1).outcome g)
  let C : SlicePairQuestion params → MIPStarRE.LDT.Polynomial params → Outcome → K →L[ℂ] K :=
    fun q g o =>
      S.L
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome o *
          (family.meas q.1).outcome g *
          (M q.2).outcome o)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 :=
    uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAB : avgOver 𝒟q (fun q => S.toVecState.qSDDCore (A q) (B q)) ≤ zeta :=
    switcherooCompletePartSelfConsistency_pairBound params S family zeta hselfG
  have hC : ∀ q,
      (∑ g : MIPStarRE.LDT.Polynomial params,
          (∑ o : Outcome, C q g o) * star (∑ o : Outcome, C q g o)) ≤ 1 := fun q =>
    switcherooAggregateFourthTerm_once_commuted_contraction_left S params family M q
  have hclose :=
    Preliminaries.closenessOfInnerProduct_left S.toVecState 𝒟q h𝒟q A B C zeta hAB hC
  simpa only [𝒟q, A, B, C, S.leftTensor_mul_leftTensor] using hclose

end MIPRE.LIDT.Co.Pasting

end
