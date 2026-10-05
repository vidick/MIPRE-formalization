/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Doubling.FinitePair
public import MIPRE.Background.LIDT.Co.Basic.OperatorExpectations
public import MIPRE.Background.LIDT.Co.Test.Defs
public import MIPRE.Background.Orthonormalization.FinitePairOrtho
public import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Statements
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Orthonormalization.RestrictSome

@[expose] public section

/-!
# Orthonormalization in a symmetric model of a finite pair, and membership

Theorem G and Proposition H of `reports/c6b-paper-proofs.md`, §4 (Lemmas 14 and 15), stated for
any symmetric model whose bipartite reading is a finite pair, and specialized to the doubled model
`Doubling.model hM hψ` of `Co/Doubling/Model.lean`.

**Theorem G** (`SymModel.orthonormalization_of_isFinitePair`, in-core orthonormalization with the
vendored constant): in a symmetric model `S` whose bipartite reading `S.toBipartite` is a finite
pair whose first player's operators contain no nonzero abelian projection, a submeasurement `X`
of the local algebra whose bipartite strong self-consistency defect is at most `ζ > 0` is within
`orthonormalizationError ζ = 100 ζ^{1/4}` of a projective submeasurement `P` of the same algebra:
`∑_a ‖(L X_a − L P_a) Ψ‖² ≤ 100 ζ^{1/4}`. `SymModel.orthonormalization_of_isFinitePair_sddRel`
states it in the vendored relations (`BipartiteSSCRel` to `SDDRel` at the one-point
distribution), the shape of the vendored `MakingMeasurementsProjective.orthonormalization`, which
milestone M8 ports. For the doubled model, `Doubling.orthonormalization_model` (both algebras of
`M` without abelian projections), `Doubling.orthonormalization_model_sddRel` and
`Doubling.orthonormalization_of_isDyadicPair` (a dyadic pair, whose algebras have no abelian
projection) specialize it. The proof (Lemma 14) completes `X` by the outcome `none`
(`MakingMeasurementsProjective.optionCompletion`), bounds the one-sided defect of the completion by
twice the bipartite defect of `X` (`SymModel.one_sub_sum_norm_sq_completion_le`), applies the
orthonormalization tier `povm_orthogonalization_finitePair` at `ε = 3 min(ζ, 1)`, and drops the
outcome `none` (`MakingMeasurementsProjective.restrictSomeProjSubMeas`): `27 min(ζ, 1) ≤
100 ζ^{1/4}`. The hypothesis `ζ > 0` is the strictness of the tier's hypothesis; the case `ζ = 0`
is not covered (report §4.7).

The completion and its restriction carry the names of their vendored counterparts and live in
the ports of those files, `Co/MakingMeasurementsProjective/Statements.lean` and
`Co/MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean`, which this file imports.

**Proposition H** (membership): every continuous functional calculus of a local self-adjoint
operator stays local.

* In a finite pair, the first player's operators are a commutant, closed under the functional
  calculus (`Doubling.cfc_mem_opsA`, `Doubling.cfc_mem_opsB`);
* in a symmetric model with an injective placement, for instance the doubled model
  (`Doubling.model_L_injective`), the functional calculus of the local C⋆-algebra is the
  functional calculus of the operators: `L (cfc f x) = cfc f (L x)` (`SymModel.L_cfc`,
  `SymModel.R_cfc`), so that `cfc f (L x)` is the placement of a local element
  (`SymModel.cfc_L_mem_range`) and, in the doubled model, order facts about it pull back along
  `Doubling.L_nonneg_iff` (Theorem A.4).

The other two items of Proposition H are not statements here: ring operations stay in `Loc M` by
typing, and the orthonormalized measurement is supplied in `Loc M` by Theorem G; the semidefinite
witness `Z` is supplied by the summed form (`planning/c6b-plan.md`, M9).
-/

open scoped InnerProductSpace CStarAlgebra
open MIPRE.OperatorMatrix

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Distribution avgOver uniformDistribution)
open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizationError)
open MIPRE.Orthonormalization (povm_orthogonalization_finitePair)

/-! ### The arithmetic of Theorem G -/

namespace Doubling

/-- The tier's strict hypothesis at `ε = 3 min(ζ, 1)`: if `1 − s ≤ 2ζ`, `0 ≤ s` and `ζ > 0`, then
`1 − 3 min(ζ, 1) < s`. -/
theorem one_sub_three_mul_min_lt {s ζ : ℝ} (hs : 1 - s ≤ 2 * ζ) (hs0 : 0 ≤ s) (hζ : 0 < ζ) :
    1 - 3 * min ζ 1 < s := by
  rcases le_total ζ 1 with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- `27 min(ζ, 1) ≤ 100 ζ^{1/4}` for `ζ ≥ 0`. -/
theorem twentySeven_mul_min_le_orthonormalizationError {ζ : ℝ} (hζ : 0 ≤ ζ) :
    27 * min ζ 1 ≤ orthonormalizationError ζ := by
  have hpow : min ζ 1 ≤ ζ ^ (1 / 4 : ℝ) := by
    rcases le_total ζ 1 with h | h
    · exact (min_le_left _ _).trans (Real.self_le_rpow_of_le_one hζ h (by norm_num))
    · exact (min_le_right _ _).trans (Real.one_le_rpow h (by norm_num))
  have h0 : 0 ≤ ζ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hζ _
  change 27 * min ζ 1 ≤ 100 * ζ ^ (1 / 4 : ℝ)
  linarith

/-- A unital `⋆`-monomorphism of C⋆-algebras commutes with the real functional calculus of
self-adjoint elements, for every function (both sides vanish when the function is not continuous
on the spectrum, which the monomorphism preserves). -/
theorem map_cfc_of_injective {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (f : ℝ → ℝ) {x : A} (hx : IsSelfAdjoint x) :
    φ (cfc f x) = cfc f (φ x) := by
  by_cases hf : ContinuousOn f (spectrum ℝ x)
  · exact φ.map_cfc f x hf
  · have hspec : spectrum ℝ (φ x) = spectrum ℝ x := hx.map_spectrum_real φ hφ
    rw [cfc_apply_of_not_continuousOn x hf, map_zero,
      cfc_apply_of_not_continuousOn (φ x) (hspec ▸ hf)]

end Doubling

/-! ### Theorem G and Proposition H in a symmetric model -/

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-- The second placement has the same state norms as the first: `‖R y Ψ‖ = ‖L y Ψ‖`. -/
theorem norm_R_apply_Ψ (y : 𝔓) : ‖S.R y S.Ψ‖ = ‖S.L y S.Ψ‖ := by
  rw [R_apply, flip_apply, S.J_Ψ, LinearIsometryEquiv.norm_map]

/-- The bipartite self-overlap of a self-adjoint local element is at most its one-sided state
norm: `⟨Ψ, (y ⊗ y) Ψ⟩ ≤ ‖L y Ψ‖²`. -/
theorem ev_L_mul_R_self_le {y : 𝔓} (hy : IsSelfAdjoint y) :
    S.ev (S.L y * S.R y) ≤ ‖S.L y S.Ψ‖ ^ 2 := by
  have h := S.abs_ev_star_mul_le (S.L y) (S.R y)
  rw [← map_star, hy.star_eq, norm_R_apply_Ψ] at h
  exact (le_abs_self _).trans (h.trans_eq (sq _).symm)

open MakingMeasurementsProjective (optionCompletion restrictSomeProjSubMeas) in
/-- **The one-sided defect of the completion is at most twice the bipartite defect**
(Lemma 14, steps 1–3, of `reports/c6b-paper-proofs.md`, §4): for a submeasurement `X`,
`1 − ∑_õ ‖L X̃_õ Ψ‖² ≤ 2 · qBipartiteSSCDefect X`, where `X̃` is the completion of `X` by `none`. -/
theorem one_sub_sum_norm_sq_completion_le {Outcome : Type*} [Fintype Outcome]
    (X : SubMeas Outcome 𝔓) :
    1 - ∑ o, ‖S.L ((optionCompletion X).outcome o) S.Ψ‖ ^ 2 ≤ 2 * S.qBipartiteSSCDefect X := by
  classical
  set t := X.total
  set b : 𝔓 → 𝔓 → ℝ := fun x y => S.ev (S.L x * S.R y) with hb
  have hb0 : ∀ a a', 0 ≤ b (X.outcome a) (X.outcome a') := fun a a' =>
    S.ev_nonneg_of_psd _ (S.opTensor_nonneg (X.outcome_pos a) (X.outcome_pos a'))
  -- each overlap is at most the one-sided norm
  have hle : ∀ o, b ((optionCompletion X).outcome o) ((optionCompletion X).outcome o) ≤
      ‖S.L ((optionCompletion X).outcome o) S.Ψ‖ ^ 2 := fun o =>
    S.ev_L_mul_R_self_le (IsSelfAdjoint.of_nonneg ((optionCompletion X).outcome_pos o))
  -- the overlap of the totals dominates the diagonal overlaps
  have htt : ∑ a, b (X.outcome a) (X.outcome a) ≤ b t t := by
    have : b t t = ∑ a, ∑ a', b (X.outcome a) (X.outcome a') := by
      simp only [hb, t, ← X.sum_eq_total, map_sum, Finset.sum_mul_sum, S.ev_sum]
    rw [this]
    exact Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (fun a' _ => hb0 a a') (Finset.mem_univ a)
  -- the overlap of the residual
  have hnone : b (1 - t) (1 - t) = 1 - 2 * S.ev (S.L t) + b t t := by
    have h1 : S.L (1 - t) * S.R (1 - t) = 1 - S.L t - S.R t + S.L t * S.R t := by
      rw [map_sub, map_sub, map_one, map_one]
      noncomm_ring
    simp only [hb, h1, VecState.ev_add, VecState.ev_sub, VecState.ev_one_of_isNormalized,
      ← S.ev_L_eq_ev_R]
    ring
  have hsum : ∑ o, b ((optionCompletion X).outcome o) ((optionCompletion X).outcome o) =
      b (1 - t) (1 - t) + ∑ a, b (X.outcome a) (X.outcome a) :=
    Fintype.sum_option _
  have hdef : S.ev (S.L t) - ∑ a, b (X.outcome a) (X.outcome a) ≤ S.qBipartiteSSCDefect X :=
    le_max_right _ _
  have := Finset.sum_le_sum fun o (_ : o ∈ Finset.univ) => hle o
  linarith

open MakingMeasurementsProjective (optionCompletion restrictSomeProjSubMeas) in
/-- **Orthonormalization in a symmetric model of a finite pair** (Theorem G of
`reports/c6b-paper-proofs.md`, §4, Lemma 14): if the bipartite reading of `S` is a finite pair
whose first player's operators contain no nonzero abelian projection, a submeasurement `X` of the
local algebra with bipartite strong self-consistency defect at most `ζ > 0` is within
`orthonormalizationError ζ = 100 ζ^{1/4}` of a projective submeasurement `P` of the local algebra:
`∑_a ‖(L X_a − L P_a) Ψ‖² ≤ 100 ζ^{1/4}`. -/
theorem orthonormalization_of_isFinitePair (hS : S.toBipartite.IsFinitePair)
    (hA : NoAbelianProj S.toBipartite.opsA) {Outcome : Type*} [Fintype Outcome]
    (X : SubMeas Outcome 𝔓) {ζ : ℝ} (hζ : 0 < ζ) (hX : S.qBipartiteSSCDefect X ≤ ζ) :
    ∃ P : ProjSubMeas Outcome 𝔓,
      ∑ a, ‖(S.L (X.outcome a) - S.L (P.outcome a)) S.Ψ‖ ^ 2 ≤ orthonormalizationError ζ := by
  -- the tier's hypothesis for the completion, at `ε = 3 min(ζ, 1)`
  have hlt := Doubling.one_sub_three_mul_min_lt ((S.one_sub_sum_norm_sq_completion_le X).trans
    (mul_le_mul_of_nonneg_left hX zero_le_two)) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hζ
  obtain ⟨Q, hQ, hQlt⟩ := povm_orthogonalization_finitePair S.toBipartite hS
    S.toBipartite_ψ_norm hA (optionCompletion X).toPOVMIn _ hlt
  -- drop the outcome `none`
  refine ⟨restrictSomeProjSubMeas ⟨(ProjMeas.ofIsPVMIn Q hQ).toSubMeas, hQ.idem⟩, ?_⟩
  have hdrop : ∑ a, ‖(S.L (X.outcome a) - S.L (Q (some a))) S.Ψ‖ ^ 2 ≤
      ∑ o, ‖S.L ((optionCompletion X).outcome o - Q o) S.Ψ‖ ^ 2 := by
    rw [Fintype.sum_option]
    simp only [map_sub]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hQlt' : ∑ o, ‖S.L ((optionCompletion X).outcome o - Q o) S.Ψ‖ ^ 2 < 9 * (3 * min ζ 1) :=
    hQlt
  have hmin := Doubling.twentySeven_mul_min_le_orthonormalizationError hζ.le
  change ∑ a, ‖(S.L (X.outcome a) - S.L (Q (some a))) S.Ψ‖ ^ 2 ≤ _
  linarith

/-- **Orthonormalization in a symmetric model of a finite pair, in the vendored relations**
(Theorem G, the shape of the vendored `MakingMeasurementsProjective.orthonormalization`): a
bipartite strong self-consistency relation at `ζ > 0` for a constant family yields a projective
submeasurement whose left placement is within `orthonormalizationError ζ` in the state-dependent
distance. -/
theorem orthonormalization_of_isFinitePair_sddRel (hS : S.toBipartite.IsFinitePair)
    (hA : NoAbelianProj S.toBipartite.opsA) {Outcome : Type*} [Fintype Outcome]
    (X : SubMeas Outcome 𝔓) {ζ : ℝ} (hζ : 0 < ζ)
    (hX : S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily X) ζ) :
    ∃ P : ProjSubMeas Outcome 𝔓,
      S.SDDRel (uniformDistribution Unit) (constSubMeasFamily (X.map S.L))
        (constSubMeasFamily (P.toSubMeas.map S.L)) (orthonormalizationError ζ) := by
  have havg : ∀ f : Unit → ℝ, avgOver (uniformDistribution Unit) f = f () := fun f => by
    simp [avgOver, uniformDistribution]
  have hX' : S.qBipartiteSSCDefect X ≤ ζ := by
    have := hX.overlapBound
    rwa [SymModel.bipartiteSSCError, havg] at this
  obtain ⟨P, hP⟩ := S.orthonormalization_of_isFinitePair hS hA X hζ hX'
  refine ⟨P, ⟨?_⟩⟩
  rw [VecState.sddError, havg]
  refine le_of_eq_of_le ?_ hP
  simp only [VecState.qSDD, VecState.qSDDCore, constSubMeasFamily, SubMeas.map_outcome,
    VecState.ev_adjoint_self_eq_norm_sq]

/-- **The local functional calculus is the operator functional calculus** (Proposition H of
`reports/c6b-paper-proofs.md`, §4): if the first placement is injective,
`L (cfc f x) = cfc f (L x)` for a self-adjoint local element `x` and every `f : ℝ → ℝ`. -/
theorem L_cfc (hL : Function.Injective S.L) (f : ℝ → ℝ) {x : 𝔓} (hx : IsSelfAdjoint x) :
    S.L (cfc f x) = cfc f (S.L x) :=
  Doubling.map_cfc_of_injective S.L hL f hx

/-- The local functional calculus is the operator functional calculus for the second placement:
`R (cfc f x) = cfc f (R x)`, if the first placement is injective. -/
theorem R_cfc (hL : Function.Injective S.L) (f : ℝ → ℝ) {x : 𝔓} (hx : IsSelfAdjoint x) :
    S.R (cfc f x) = cfc f (S.R x) :=
  Doubling.map_cfc_of_injective S.R (fun _ _ h => hL (S.flip.injective h)) f hx

/-- **The functional calculus of a placed local operator is placed** (Proposition H): if the
first placement is injective, it is the placement of the local functional calculus. -/
theorem cfc_L_mem_range (hL : Function.Injective S.L) (f : ℝ → ℝ) {x : 𝔓}
    (hx : IsSelfAdjoint x) : cfc f (S.L x) ∈ Set.range S.L :=
  ⟨cfc f x, S.L_cfc hL f hx⟩

end SymModel

namespace Doubling

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-! ### Proposition H in a finite pair -/

/-- **The functional calculus stays in the first player's operators** of a finite pair
(Proposition H of `reports/c6b-paper-proofs.md`, §4): they are the commutant of the second
player's (`IsFinitePair.coe_centralizer_opsB`), a closed `⋆`-subalgebra. -/
theorem cfc_mem_opsA (hM : M.IsFinitePair) (f : ℝ → ℝ) {T : M.H →L[ℂ] M.H} (hT : T ∈ M.opsA) :
    cfc f T ∈ M.opsA := by
  rw [← hM.coe_centralizer_opsB] at hT ⊢
  exact cfc_mem (s := StarSubalgebra.centralizer ℂ M.opsB) f hT

/-- **The functional calculus stays in the second player's operators** of a finite pair. -/
theorem cfc_mem_opsB (hM : M.IsFinitePair) (f : ℝ → ℝ) {T : M.H →L[ℂ] M.H} (hT : T ∈ M.opsB) :
    cfc f T ∈ M.opsB := by
  rw [← hM.coe_centralizer_opsA] at hT ⊢
  exact cfc_mem (s := StarSubalgebra.centralizer ℂ M.opsA) f hT

/-! The functional calculus of the doubled local algebra is that of its C⋆-algebra structure; the
shortcut instances below make the real scalars, and so the real functional calculus, go through
`CStarAlgebra (Loc M)` rather than through the product (`Prod.algebra`), whose real algebra the
continuous functional calculus of a C⋆-algebra does not unify with. -/

/-- The doubled local algebra is a real normed algebra, through its C⋆-algebra structure
(shortcut). -/
noncomputable instance (priority := high) instNormedAlgebraRealLoc : NormedAlgebra ℝ (Loc M) :=
  NormedAlgebra.complexToReal

/-- The real algebra structure of the doubled local algebra, through its C⋆-algebra structure
(shortcut). -/
noncomputable instance (priority := high) instAlgebraRealLoc : Algebra ℝ (Loc M) :=
  NormedAlgebra.toAlgebra

/-- The real continuous functional calculus of the doubled local algebra, that of a C⋆-algebra
(shortcut). -/
noncomputable instance (priority := high) instCFCLoc :
    ContinuousFunctionalCalculus ℝ (Loc M) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

variable (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1)

/-- The first placement of the doubled model is injective, so `SymModel.L_cfc`,
`SymModel.R_cfc` and `SymModel.cfc_L_mem_range` apply to it. -/
theorem model_L_injective : Function.Injective (model hM hψ).L :=
  (isFinitePair hM hψ).injA

/-- The second placement of the doubled model is injective. -/
theorem model_R_injective : Function.Injective (model hM hψ).R :=
  (isFinitePair hM hψ).injB

/-! ### Theorem G in the doubled model -/

/-- **Orthonormalization in the doubled model** (Theorem G of `reports/c6b-paper-proofs.md`, §4,
Lemma 14): if neither algebra of the finite pair `M` has a nonzero abelian projection, a
submeasurement `X` of the doubled local algebra with bipartite strong self-consistency defect at
most `ζ > 0` is within `orthonormalizationError ζ = 100 ζ^{1/4}` of a projective submeasurement `P`
of the doubled local algebra: `∑_a ‖(L X_a − L P_a) Ψ‖² ≤ 100 ζ^{1/4}`. -/
theorem orthonormalization_model (hA : NoAbelianProj M.opsA) (hB : NoAbelianProj M.opsB)
    {Outcome : Type*} [Fintype Outcome] (X : SubMeas Outcome (Loc M)) {ζ : ℝ} (hζ : 0 < ζ)
    (hX : (model hM hψ).qBipartiteSSCDefect X ≤ ζ) :
    ∃ P : ProjSubMeas Outcome (Loc M),
      ∑ a, ‖((model hM hψ).L (X.outcome a) - (model hM hψ).L (P.outcome a)) (model hM hψ).Ψ‖ ^ 2
        ≤ orthonormalizationError ζ :=
  (model hM hψ).orthonormalization_of_isFinitePair (isFinitePair hM hψ)
    ((noAbelianProj_iff hM hψ).2 ⟨hA, hB⟩).1 X hζ hX

/-- **Orthonormalization in the doubled model of a dyadic pair** (Theorem G): the algebras of a
dyadic pair have no abelian projection (`IsDyadicPair.noAbelianProj_opsA`). -/
theorem orthonormalization_of_isDyadicPair (h : M.IsDyadicPair) (hψ : ‖M.ψ‖ = 1)
    {Outcome : Type*} [Fintype Outcome] (X : SubMeas Outcome (Loc M)) {ζ : ℝ} (hζ : 0 < ζ)
    (hX : (model h.isFinitePair hψ).qBipartiteSSCDefect X ≤ ζ) :
    ∃ P : ProjSubMeas Outcome (Loc M),
      ∑ a, ‖((model h.isFinitePair hψ).L (X.outcome a) -
          (model h.isFinitePair hψ).L (P.outcome a)) (model h.isFinitePair hψ).Ψ‖ ^ 2
        ≤ orthonormalizationError ζ :=
  orthonormalization_model h.isFinitePair hψ h.noAbelianProj_opsA h.noAbelianProj_opsB X hζ hX

/-- **Orthonormalization in the doubled model, in the vendored relations** (Theorem G, the model
form of the vendored `MakingMeasurementsProjective.orthonormalization`): a bipartite strong
self-consistency relation at `ζ > 0` for a constant family yields a projective submeasurement
whose left placement is within `orthonormalizationError ζ` in the state-dependent distance. -/
theorem orthonormalization_model_sddRel (hA : NoAbelianProj M.opsA) (hB : NoAbelianProj M.opsB)
    {Outcome : Type*} [Fintype Outcome] (X : SubMeas Outcome (Loc M)) {ζ : ℝ} (hζ : 0 < ζ)
    (hX : (model hM hψ).BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily X) ζ) :
    ∃ P : ProjSubMeas Outcome (Loc M),
      (model hM hψ).SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (X.map (model hM hψ).L))
        (constSubMeasFamily (P.toSubMeas.map (model hM hψ).L))
        (orthonormalizationError ζ) :=
  (model hM hψ).orthonormalization_of_isFinitePair_sddRel (isFinitePair hM hψ)
    ((noAbelianProj_iff hM hψ).2 ⟨hA, hB⟩).1 X hζ hX

end Doubling

end MIPRE.LIDT.Co

end
