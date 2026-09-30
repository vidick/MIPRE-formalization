/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Expanded
public import MIPRE.Background.QLD.Swap
public import MIPRE.Foundations.KrausDilation
public import MIPRE.Foundations.ModelCalculus
public import MIPRE.Foundations.ModelReading
public import MIPRE.Foundations.Sandwich

@[expose] public section

/-!
# Combining the two bases: the joint point measurement

Blueprint `lem:qld-combined-points`, the paper's `lem:qld-4-10`. The expansion stage left two
measurements per content --- one in each basis --- that *approximately commute*
(`lem:qld-expanded-points`). This stage turns them into a single projective measurement returning
both values at once.

## The route, and how it differs from the paper's

The paper builds the sandwich `R^w_{a,b} = M^Z_b M^X_a M^Z_b`, proves it approximately
self-consistent and approximately linear in the two probes, *orthonormalizes* it
(`cor:ortho-from-consistency`), and then applies the quantum linearity test
(`thm:linearity`) to the resulting observables. Three of those four steps are unnecessary here,
and the reason is that the strategy is **projective**, which the paper also assumes:

* the sandwich is then already a POVM, and its terms are already `(X_a Z_b)⋆ (X_a Z_b)`;
* the joint measurement is its **Naimark dilation**, which is projective by construction --- no
  orthonormalization, and no `thm:linearity`;
* the compression identity of the dilation carries every estimate about the sandwich to the
  dilated measurement unchanged, so the estimates are proved once, about `R`.

What remains is the analytic content: the sandwich is close to the ordered product
(`hatSand_close`, one commutation), the ordered products are cross-party consistent, and the
sandwich is therefore self-consistent. The commutation input arrives at the level of the
**observables**, and Parseval is what moves it to the level of the measurement elements
(`sum_stateSqNorm_hatComm`).

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The expanded state is the
register model `M.reg (Anc F m)` (`MIPRE/Background/QLD/Expanded.lean`), the hatted measurements
are POVMs in `Matrix (Anc F m) (Anc F m) 𝒜` (and `ℬ`), and the commutation input is a state norm
there; Parseval is the one of a complex inner product space (`sum_norm_trSum2_sq`), applied to the
vectors `π(X) ψ`. The joint measurement is the **Halmos dilation with the explicit Kraus family**
`(a, b) ↦ X_a Z_b` (`QLD.sandDil`, from `MIPRE/Foundations/HalmosDilation.lean`): the Naimark
matrix of that family at `inl (0, 0)` is a partial isometry, and the dilated projections live on a
register `(F × F) ⊕ (F × F)` adjoined to each player at the basis state `|inl (0, 0)⟩`
(`BipartiteModel.jointModel`). The two-sided compression `BipartiteModel.bornProb_expand_basisVec`
carries every estimate back to the sandwiches, so `combined_points` is stated as **agreement
bounds of the sandwiches in `M.reg (Anc F m)`**, with the dilation kept inside the proofs; its
constants are those of the matrix statement's dilated deviations, halved, the summed deviation of
a projective pair being twice its disagreement. The dilated measurement itself, which the pasting
lemma of `lem:qld-pairs-of-lines` needs, is `BipartiteModel.exists_projective_joint` (the model
form of `MIPRE.exists_projective_joint`) and, at the content-indexed data of the Pauli basis test,
`combined_points_dilated`. On a unit vector `ψ : dA × dB → ℂ` the statements are read at the
tensor-product model `BipartiteModel.tensor ψ` with the families `POVM.toIn`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder InnerProductSpace

/-! ## The Halmos dilation of the sandwich -/

namespace QLD

section SandDilation

variable {R : Type*} [Ring R] [StarRing R] {A : Type*} [Fintype A] [DecidableEq A]
  {X Z : A → R}

/-- **The Kraus family of the sandwich**, `(a, b) ↦ X_a Z_b`: its Gram operators are the
sandwiches `Z_b X_a Z_b`, and they sum to one. -/
theorem sum_star_mul_sandKraus (hX : IsPVMIn X) (hZ : IsPVMIn Z) :
    ∑ q : A × A, star (X q.1 * Z q.2) * (X q.1 * Z q.2) = 1 := by
  rw [← hX.sum_sand hZ]
  exact Finset.sum_congr rfl fun q _ => (hX.sand_eq_gram hZ q).symm

/-- **The dilated joint measurement**: the Halmos projections of the Naimark matrix of the Kraus
family `(a, b) ↦ X_a Z_b` at `p₀`, on the register `(A × A) ⊕ (A × A)`. -/
def sandDil (X Z : A → R) (p₀ : A × A) (p : A × A) :
    Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) R :=
  Halmos.proj (Halmos.naimark (fun q : A × A => X q.1 * Z q.2) p₀) p

/-- **The dilated joint measurement is projective.** -/
theorem isPVMIn_sandDil (hX : IsPVMIn X) (hZ : IsPVMIn Z) (p₀ : A × A) :
    IsPVMIn (sandDil X Z p₀) :=
  Halmos.isPVMIn_proj (Halmos.naimark_mul_conjTranspose_mul' (sum_star_mul_sandKraus hX hZ) p₀)

/-- **The dilated joint measurement compresses to the sandwich** at `|inl p₀⟩`. -/
theorem sandDil_inl_inl (hX : IsPVMIn X) (hZ : IsPVMIn Z) (p₀ p : A × A) :
    sandDil X Z p₀ p (Sum.inl p₀) (Sum.inl p₀) = sand X Z p := by
  rw [sandDil, Halmos.proj_naimark_inl_inl' (sum_star_mul_sandKraus hX hZ), ← hX.sand_eq_gram hZ]

end SandDilation

end QLD

/-! ## The dilated joint measurement in a bipartite model -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (N : BipartiteModel 𝒞 𝒜 ℬ)
  {A : Type*} [Fintype A] [DecidableEq A]

/-- **The model of the dilated joint measurement**: `N` extended by one dilation register
`(A × A) ⊕ (A × A)` for each player, both in the basis state `|inl p₀⟩`. -/
abbrev jointModel (p₀ : A × A) :=
  N.expand (basisVec (Sum.inl p₀ : (A × A) ⊕ (A × A)) (Sum.inl p₀ : (A × A) ⊕ (A × A)))

/-- **The two-sided compression**: a Born probability of the joint model is the Born probability
of the two reference entries. -/
theorem jointModel_bornProb (p₀ : A × A) (X : Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) 𝒜)
    (Y : Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) ℬ) :
    (N.jointModel p₀).bornProb X Y
      = N.bornProb (X (Sum.inl p₀) (Sum.inl p₀)) (Y (Sum.inl p₀) (Sum.inl p₀)) :=
  N.bornProb_expand_basisVec _ _ X Y

/-- The squared state norm of a projection of the joint model is the expectation of its reference
entry. -/
theorem jointModel_stateSqNorm (p₀ : A × A)
    {Q : Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) 𝒜} (hQ : IsStarProjection Q) :
    (N.jointModel p₀).stateSqNorm Q = N.bornProb (Q (Sum.inl p₀) (Sum.inl p₀)) 1 := by
  rw [stateSqNorm_eq_bornProb_one, hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq,
    jointModel_bornProb, one_apply_eq]

/-- The same for the second player. -/
theorem jointModel_swap_stateSqNorm (p₀ : A × A)
    {Q : Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) ℬ} (hQ : IsStarProjection Q) :
    (N.jointModel p₀).swap.stateSqNorm Q = N.bornProb 1 (Q (Sum.inl p₀) (Sum.inl p₀)) := by
  rw [stateSqNorm_eq_bornProb_one, hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq,
    bornProb_swap, jointModel_bornProb, one_apply_eq]

/-- A second-player operator with an inert dilation register has the state norm it had. -/
theorem jointModel_swap_stateSqNorm_smulKron_one (p₀ : A × A) (Y : ℬ) :
    (N.jointModel p₀).swap.stateSqNorm (smulKron Y 1) = N.swap.stateSqNorm Y := by
  rw [swap_stateSqNorm_expand_smulKron_one, norm_basisVec, one_pow, one_mul]

/-- **The deviation of a dilated projective measurement from a second-player family with an inert
register**, summed: the expectations of the compressions, the second player's squared norms, and
twice the agreement of the compressions with the family. -/
theorem jointModel_sum_xSqNorm_smulKron (hψ : ‖N.ψ‖ = 1) (p₀ : A × A) {κ : Type*} [Fintype κ]
    {Q : κ → Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) 𝒜} (hQ : IsPVMIn Q) (S : κ → ℬ) :
    ∑ k, (N.jointModel p₀).xSqNorm (Q k) (smulKron (S k) 1)
      = 1 + ∑ k, N.swap.stateSqNorm (S k)
        - 2 * ∑ k, N.bornProb (Q k (Sum.inl p₀) (Sum.inl p₀)) (S k) := by
  have hterm : ∀ k, (N.jointModel p₀).xSqNorm (Q k) (smulKron (S k) 1)
      = N.bornProb (Q k (Sum.inl p₀) (Sum.inl p₀)) 1 + N.swap.stateSqNorm (S k)
        - 2 * N.bornProb (Q k (Sum.inl p₀) (Sum.inl p₀)) (S k) := by
    intro k
    rw [(N.jointModel p₀).xSqNorm_eq (hQ.star_eq k), N.jointModel_stateSqNorm p₀
      (hQ.isStarProjection k), N.jointModel_swap_stateSqNorm_smulKron_one, N.jointModel_bornProb,
      smulKron_apply, one_apply_eq, one_smul]
  have hone : ∑ k, N.bornProb (Q k (Sum.inl p₀) (Sum.inl p₀)) 1 = 1 := by
    rw [← N.bornProb_sum_left, ← Matrix.sum_apply, ← Matrix.sum_apply, hQ.sum_eq_one,
      one_apply_eq, bornProb, map_one, map_one, mul_one, N.qform_one hψ]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hone, ← Finset.mul_sum]

private theorem xSqNorm_smulKron_le (p₀ : A × A)
    (a : Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) 𝒜) (b₁ b₂ : ℬ) :
    (N.jointModel p₀).xSqNorm a (smulKron b₂ 1)
      ≤ 2 * (N.jointModel p₀).xSqNorm a (smulKron b₁ 1) + 2 * N.swap.stateSqNorm (b₁ - b₂) := by
  have hsplit : (N.jointModel p₀).πA a - (N.jointModel p₀).πB (smulKron b₂ 1)
      = ((N.jointModel p₀).πA a - (N.jointModel p₀).πB (smulKron b₁ 1))
        + (N.jointModel p₀).πB (smulKron (b₁ - b₂) 1) := by
    rw [← smulKron_sub_left, map_sub]
    abel
  have htri : (N.jointModel p₀).xNorm a (smulKron b₂ 1)
      ≤ (N.jointModel p₀).xNorm a (smulKron b₁ 1)
        + (N.jointModel p₀).snorm ((N.jointModel p₀).πB (smulKron (b₁ - b₂) 1)) := by
    rw [xNorm, xNorm, hsplit]
    exact (N.jointModel p₀).snorm_add_le _ _
  have hsw : (N.jointModel p₀).snorm ((N.jointModel p₀).πB (smulKron (b₁ - b₂) 1)) ^ 2
      = N.swap.stateSqNorm (b₁ - b₂) :=
    N.jointModel_swap_stateSqNorm_smulKron_one p₀ (b₁ - b₂)
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq, ← hsw]
  nlinarith [(N.jointModel p₀).xNorm_nonneg a (smulKron b₂ 1),
    (N.jointModel p₀).xNorm_nonneg a (smulKron b₁ 1),
    (N.jointModel p₀).snorm_nonneg ((N.jointModel p₀).πB (smulKron (b₁ - b₂) 1)),
    sq_nonneg ((N.jointModel p₀).xNorm a (smulKron b₁ 1)
      - (N.jointModel p₀).snorm ((N.jointModel p₀).πB (smulKron (b₁ - b₂) 1)))]

/-- **Two approximately commuting projective measurements on each party admit a joint projective
measurement**, on each party's algebra enlarged by one dilation register, which is self-consistent
across the parties and consistent with *both* ordered products of the originals --- all at errors
independent of the number of outcomes. The model form of `MIPRE.exists_projective_joint`, with
the same constants: the joint measurement is the Halmos dilation `QLD.sandDil` of the sandwich
`Z_b X_a Z_b`, whose reference entry is the sandwich (the third and fourth conclusions), which is
what carries every estimate (`jointModel_bornProb`). -/
theorem exists_projective_joint [PartialOrder ℬ] [StarOrderedRing ℬ] {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hψ : ‖N.ψ‖ = 1) (p₀ : A × A)
    {X Z : ι → A → 𝒜} {X' Z' : ι → A → ℬ}
    (hX : ∀ i, IsPVMIn (X i)) (hZ : ∀ i, IsPVMIn (Z i))
    (hX' : ∀ i, IsPVMIn (X' i)) (hZ' : ∀ i, IsPVMIn (Z' i))
    {cA cB α β : ℝ}
    (hcA : ∑ i, w i * ∑ p : A × A, N.stateSqNorm (X i p.1 * Z i p.2 - Z i p.2 * X i p.1) ≤ cA)
    (hcB : ∑ i, w i * ∑ p : A × A,
        N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) ≤ cB)
    (hα : ∑ i, w i * ∑ a : A, N.xSqNorm (X i a) (X' i a) ≤ α)
    (hβ : ∑ i, w i * ∑ b : A, N.xSqNorm (Z i b) (Z' i b) ≤ β) :
    ∃ (QA : ι → A × A → Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) 𝒜)
      (QB : ι → A × A → Matrix ((A × A) ⊕ (A × A)) ((A × A) ⊕ (A × A)) ℬ),
      (∀ i, IsPVMIn (QA i)) ∧ (∀ i, IsPVMIn (QB i))
      ∧ (∀ i p, QA i p (Sum.inl p₀) (Sum.inl p₀) = sand (X i) (Z i) p)
      ∧ (∀ i p, QB i p (Sum.inl p₀) (Sum.inl p₀) = sand (X' i) (Z' i) p)
      ∧ (∑ i, w i * ∑ p : A × A, (N.jointModel p₀).xSqNorm (QA i p) (QB i p)
          ≤ 2 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2))
      ∧ (∑ i, w i * ∑ p : A × A,
            (N.jointModel p₀).xSqNorm (QA i p) (smulKron (Z' i p.2 * X' i p.1) 1)
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 2 * cB)
      ∧ (∑ i, w i * ∑ p : A × A,
            (N.jointModel p₀).xSqNorm (QA i p) (smulKron (X' i p.1 * Z' i p.2) 1)
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 8 * cB) := by
  classical
  set Γ : ℝ := Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2 with hΓ
  set γ : ι → ℝ := fun i => 1 - ∑ p : A × A,
    N.bornProb (sand (X i) (Z i) p) (sand (X' i) (Z' i) p) with hγ
  -- the chain
  have hγsum : ∑ i, w i * γ i ≤ Γ := by
    have hsum : ∑ i, w i * γ i = 1 - ∑ i, w i * ∑ p : A × A,
        N.bornProb (sand (X i) (Z i) p) (sand (X' i) (Z' i) p) := by
      simp only [hγ, mul_sub, mul_one, Finset.sum_sub_distrib, hw1]
    rw [hsum]
    exact N.one_sub_sum_bornProb_sand_le hw0 hw1 hψ hX hZ hX' hZ' hcA hcB hα hβ
  -- the two dilations
  have hPA : ∀ i, IsPVMIn (QLD.sandDil (X i) (Z i) p₀) := fun i =>
    QLD.isPVMIn_sandDil (hX i) (hZ i) p₀
  have hPB : ∀ i, IsPVMIn (QLD.sandDil (X' i) (Z' i) p₀) := fun i =>
    QLD.isPVMIn_sandDil (hX' i) (hZ' i) p₀
  have hkA : ∀ i p, QLD.sandDil (X i) (Z i) p₀ p (Sum.inl p₀) (Sum.inl p₀) = sand (X i) (Z i) p :=
    fun i p => QLD.sandDil_inl_inl (hX i) (hZ i) p₀ p
  have hkB : ∀ i p, QLD.sandDil (X' i) (Z' i) p₀ p (Sum.inl p₀) (Sum.inl p₀)
      = sand (X' i) (Z' i) p := fun i p => QLD.sandDil_inl_inl (hX' i) (hZ' i) p₀ p
  have hone : N.bornProb 1 1 = 1 := by
    rw [bornProb, map_one, map_one, mul_one, N.qform_one hψ]
  have hRone : ∀ i, ∑ p : A × A, N.bornProb (sand (X i) (Z i) p) 1 = 1 := fun i => by
    rw [← N.bornProb_sum_left, (hX i).sum_sand (hZ i), hone]
  have hR'one : ∀ i, ∑ p : A × A, N.bornProb 1 (sand (X' i) (Z' i) p) = 1 := fun i => by
    rw [← N.bornProb_sum_right, (hX' i).sum_sand (hZ' i), hone]
  -- item 1: the dilated pair's deviation is twice the sandwiches' disagreement
  have hitem1 : ∀ i, ∑ p : A × A, (N.jointModel p₀).xSqNorm (QLD.sandDil (X i) (Z i) p₀ p)
      (QLD.sandDil (X' i) (Z' i) p₀ p) = 2 * γ i := by
    intro i
    have hterm : ∀ p : A × A, (N.jointModel p₀).xSqNorm (QLD.sandDil (X i) (Z i) p₀ p)
        (QLD.sandDil (X' i) (Z' i) p₀ p) = N.bornProb (sand (X i) (Z i) p) 1
          + N.bornProb 1 (sand (X' i) (Z' i) p)
          - 2 * N.bornProb (sand (X i) (Z i) p) (sand (X' i) (Z' i) p) := by
      intro p
      rw [(N.jointModel p₀).xSqNorm_eq ((hPA i).star_eq p),
        N.jointModel_stateSqNorm p₀ ((hPA i).isStarProjection p),
        N.jointModel_swap_stateSqNorm p₀ ((hPB i).isStarProjection p), N.jointModel_bornProb,
        hkA, hkB]
    rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hRone, hR'one, ← Finset.mul_sum]
    simp only [hγ]
    ring
  -- item 1': against the undilated sandwich on the second player's side
  have hB1 : ∀ i, ∑ p : A × A, N.swap.stateSqNorm (sand (X' i) (Z' i) p) ≤ 1 := fun i =>
    N.swap.sum_stateSqNorm_le_one hψ (POVMIn.sand (hX' i) (hZ' i))
  have hitem1' : ∀ i, ∑ p : A × A, (N.jointModel p₀).xSqNorm (QLD.sandDil (X i) (Z i) p₀ p)
      (smulKron (sand (X' i) (Z' i) p) 1) ≤ 2 * γ i := by
    intro i
    rw [N.jointModel_sum_xSqNorm_smulKron hψ p₀ (hPA i)]
    simp only [hkA, hγ]
    linarith [hB1 i]
  -- the sandwich is close to each ordered product, on the second player's side
  have hord1n : ∀ i p, N.swap.stateNorm (sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1)
      ≤ N.swap.stateNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by
    intro i p
    have heq : sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1
        = Z' i p.2 * (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by
      calc sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1
          = Z' i p.2 * X' i p.1 * Z' i p.2 - Z' i p.2 * Z' i p.2 * X' i p.1 := by
            rw [(hZ' i).idem]; rfl
        _ = Z' i p.2 * (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by noncomm_ring
    rw [heq]
    exact N.swap.stateNorm_mul_le
      (N.swap.bnd_πA_of_isStarProjection ((hZ' i).isStarProjection p.2)) _
  have hord1 : ∀ i p, N.swap.stateSqNorm (sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1)
      ≤ N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := fun i p =>
    pow_le_pow_left₀ (N.swap.stateNorm_nonneg _) (hord1n i p) 2
  have hord2 : ∀ i p, N.swap.stateSqNorm (sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2)
      ≤ 4 * N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by
    intro i p
    have hsplit : sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2
        = (sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1)
          - (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by abel
    have htri : N.swap.stateNorm (sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2)
        ≤ 2 * N.swap.stateNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by
      rw [hsplit, stateNorm, map_sub]
      refine le_trans (N.swap.snorm_sub_le _ _) ?_
      have h1 := hord1n i p
      rw [stateNorm] at h1
      rw [stateNorm]
      linarith
    have h0 := N.swap.stateNorm_nonneg (sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2)
    rw [stateSqNorm, stateSqNorm]
    nlinarith
  -- items 2 and 3
  have hitem2 : ∀ i, ∑ p : A × A, (N.jointModel p₀).xSqNorm (QLD.sandDil (X i) (Z i) p₀ p)
        (smulKron (Z' i p.2 * X' i p.1) 1)
      ≤ 4 * γ i + 2 * ∑ p : A × A,
        N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by
    intro i
    refine le_trans (Finset.sum_le_sum fun p _ =>
      (N.xSqNorm_smulKron_le p₀ _ (sand (X' i) (Z' i) p) _).trans
        (add_le_add_left (mul_le_mul_of_nonneg_left (hord1 i p) (by norm_num)) _)) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith [hitem1' i]
  have hitem3 : ∀ i, ∑ p : A × A, (N.jointModel p₀).xSqNorm (QLD.sandDil (X i) (Z i) p₀ p)
        (smulKron (X' i p.1 * Z' i p.2) 1)
      ≤ 4 * γ i + 8 * ∑ p : A × A,
        N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by
    intro i
    refine le_trans (Finset.sum_le_sum fun p _ =>
      (N.xSqNorm_smulKron_le p₀ _ (sand (X' i) (Z' i) p) _).trans
        (add_le_add_left (mul_le_mul_of_nonneg_left (hord2 i p) (by norm_num)) _)) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.mul_sum (s := univ)
      (f := fun p : A × A => 4 * N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1))]
    have h8 : ∑ p : A × A, 2 * (4 * N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1))
        = 8 * ∑ p : A × A, N.swap.stateSqNorm (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    linarith [hitem1' i]
  have hw2 : ∀ (f g : ι → ℝ) (a b : ℝ), ∑ i, w i * (a * f i + b * g i)
      = a * ∑ i, w i * f i + b * ∑ i, w i * g i := by
    intro f g a b
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i => QLD.sandDil (X i) (Z i) p₀, fun i => QLD.sandDil (X' i) (Z' i) p₀, hPA, hPB,
    hkA, hkB, ?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun i _ => by rw [hitem1 i]]
    have h := hw2 γ γ 2 0
    simp only [zero_mul, add_zero] at h
    rw [h]
    linarith
  · refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hitem2 i) (hw0 i)) ?_
    rw [hw2]
    linarith
  · refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hitem3 i) (hw0 i)) ?_
    rw [hw2]
    linarith

end BipartiteModel

namespace QLD

open MIPRE.LowDegree MIPRE.LIDT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

set_option linter.unusedSectionVars false

section Combined

/-! ## The hatted point measurement, indexed by the point

`hatPOVM` is indexed by a content, but it depends on it only through the point of the relevant
basis --- not through the probes, the seed or the diagonal direction. Saying so once, by
re-indexing, is what lets the probe average be separated from the point average later. -/

section Hat

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- **The hatted point measurement at a point**: the strategy's point measurement at `u`,
convolved with the ancilla's syndrome measurement there. -/
def hatPtPOVM (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) :
    POVMIn F (Matrix (Anc F m) (Anc F m) R) :=
  (kronIn ((P (.point W u)).map rdVal) (synPOVM W u) (isPVM_synPOVM W u)).map
    fun p => p.1 + p.2

theorem hatPOVM_eq (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R)
    (W : Bas) (c : Content F m) : hatPOVM hm P W c = hatPtPOVM P W (c.pt W) := by
  rw [hatPOVM, ptValPOVM, Content.omega_pt, hatPtPOVM]
  rfl

/-- The elements of the hatted point measurement. -/
def hatMats (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) (a : F) :
    Matrix (Anc F m) (Anc F m) R :=
  (hatPtPOVM P W u).op a

/-! ## The hatted observable at an arbitrary probe

`hatObs` is the hatted point observable at the probe the content itself carries. The transform
needs the whole family, one observable for each `r in F_q`, and `hatObsAt_self` is the
identification at the content's own probe. -/

/-- The hatted point measurement's binary observable at the probe `r`. -/
def hatObsAt (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) (r : F) :
    Matrix (Anc F m) (Anc F m) R :=
  ∑ a : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • hatMats P W u a

end Hat

/-- **Fourier inversion over one copy of the field**, in any complex vector space. -/
private theorem sum_sgn_smul_sum_sgn_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Y : F → V) (a : F) :
    (Fintype.card F : ℂ)⁻¹ • ∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) •
      ∑ b : F, sgn (Algebra.trace (ZMod 2) F (b * r)) • Y b = Y a := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hswap : (∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) •
      ∑ b : F, sgn (Algebra.trace (ZMod 2) F (b * r)) • Y b)
      = ∑ b : F, (∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * (a + b)))) • Y b := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← sgn_add, ← map_add, ← add_mul, mul_comm (a + b) r]
  rw [hswap, Finset.sum_eq_single_of_mem a (Finset.mem_univ a) fun b _ hb => ?_]
  · rw [Weyl.add_self, sum_sgn_trMul_zero, smul_smul, inv_mul_cancel₀ hq, one_smul]
  · rw [sum_sgn_trMul (x := a + b) fun h => hb ((Weyl.add_eq_zero_iff a b).mp h).symm,
      zero_smul]

/-- **The one-field transform sees through a coarse-graining**, for a POVM in any ordered
`⋆`-algebra. -/
private theorem sum_sgn_smul_map_op {R' : Type*} [Ring R'] [StarRing R'] [Algebra ℂ R']
    [PartialOrder R'] [StarOrderedRing R'] {X : Type*} [Fintype X] (Q : POVMIn X R')
    (f : X → F) (r : F) :
    ∑ a : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • (Q.map f).op a
      = ∑ x : X, sgn (Algebra.trace (ZMod 2) F (f x * r)) • Q.op x := by
  rw [← Finset.sum_fiberwise (univ : Finset X) f
    fun x => sgn (Algebra.trace (ZMod 2) F (f x * r)) • Q.op x]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [POVMIn.map_op, Finset.smul_sum]
  exact Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]

private theorem smulKron_smul_left_comb {R' α : Type*} [Ring R'] [Algebra ℂ R'] (c : ℂ) (X : R')
    (P : Matrix α α ℂ) : smulKron (c • X) P = c • smulKron X P := by
  ext a b
  simp only [smulKron_apply, Matrix.smul_apply]
  exact smul_comm (P a b) c X

section Hat2

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- **The measurement is the transform of its observables.** -/
theorem trFourier_hatObsAt (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (u : Point F m) (a : F) :
    (Fintype.card F : ℂ)⁻¹ • ∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • hatObsAt P W u r
      = hatMats P W u a :=
  sum_sgn_smul_sum_sgn_smul (hatMats P W u) a

/-- A product family's transform splits: the hatted observable is the strategy's observable
tensored with the ancilla's. -/
theorem hatObsAt_eq (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m)
    (r : F) :
    hatObsAt P W u r
      = smulKron (∑ a : F, sgn (Algebra.trace (ZMod 2) F (a * r))
            • ((P (.point W u)).map rdVal).op a)
          (trObs (fun a : F => (((synPOVM W u).mats a).val)) r) := by
  rw [hatObsAt]
  simp only [hatMats, hatPtPOVM]
  rw [sum_sgn_smul_map_op, Fintype.sum_prod_type, trObs, smulKron_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smulKron_smul_left_comb, smulKron_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [kronIn_op, smulKron_smul_right, smul_smul, ← sgn_add, ← map_add, ← add_mul]

end Hat2

/-- The strategy's factor, at the content's own probe, is `ptObs`. -/
theorem trObs_ptVal {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R]
    [StarOrderedRing R] (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R)
    (W : Bas) (c : Content F m) :
    ∑ a : F, sgn (Algebra.trace (ZMod 2) F (a * c.omega.r W))
        • ((P (.point W (c.pt W))).map rdVal).op a
      = ptObs hm P W c := by
  classical
  rw [sum_sgn_smul_map_op, ptObs, POVMIn.obs2_map]
  refine Finset.sum_congr rfl fun ans _ => ?_
  congr 1
  cases ans <;> simp [rdVal, rdProbeAt, rdProbe, prb]

/-- The ancilla's factor is the Weyl operator at `r . ind_m(u)`: the syndrome projectors are the
spectral projectors of the Weyl family, so their signed sum is the operator itself. -/
theorem trObs_synPOVM (W : Bas) (u : Point F m) (r : F) :
    trObs (fun a : F => (((synPOVM (F := F) (m := m) W u).mats a).val)) r
      = weylOf W (r • indVec u) := by
  classical
  rw [trObs, eq_sum_proj (w := weylOf (F := F) (m := m) W) (r • indVec u),
    ← Finset.sum_fiberwise (univ : Finset (Anc F m)) (fun e => dotF e (indVec u))
      (fun e => sgn (trDot (r • indVec u) e) • proj (weylOf (F := F) (m := m) W) e)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [synPOVM_mats, syn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  rw [trDot, ← (Finset.mem_filter.mp he).2, dotF]
  congr 2
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

section Hat3

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- **At the content's own probe, the transform is `hatObs`.** -/
theorem hatObsAt_self (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R)
    (W : Bas) (c : Content F m) :
    hatObsAt P W (c.pt W) (c.omega.r W) = hatObs hm P W c := by
  rw [hatObsAt_eq, trObs_ptVal hm, trObs_synPOVM, hatObs, ancVec, Content.omega_pt]

/-! ## Parseval: from the observables' commutator to the elements'

The commutation input of `lem:qld-expanded-points` is about the *observables*, one pair for each
`(r, s)`. What the sandwich needs is the commutator of the measurement *elements*, one pair for
each `(a, b)`. Parseval exchanges the two at no cost: the sum over outcomes of the one is the
average over probes of the other. -/

/-- The commutator of the two bases' hatted measurement elements. -/
def hatComm (P : Question F m → POVMIn (Answer F m d) R) (x z : Point F m) (a b : F) :
    Matrix (Anc F m) (Anc F m) R :=
  hatMats P .X x a * hatMats P .Z z b - hatMats P .Z z b * hatMats P .X x a

/-- The commutator of the two bases' hatted observables. -/
def hatObsComm (P : Question F m → POVMIn (Answer F m d) R) (x z : Point F m) (r s : F) :
    Matrix (Anc F m) (Anc F m) R :=
  hatObsAt P .X x r * hatObsAt P .Z z s - hatObsAt P .Z z s * hatObsAt P .X x r

/-- **The elements' commutator is the transform of the observables'**: the two-field transform
against the characters `(r, s) ↦ (-1)^{tr(a r) + tr(b s)}`. -/
theorem hatComm_eq_fourierOf (P : Question F m → POVMIn (Answer F m d) R) (x z : Point F m)
    (a b : F) :
    hatComm P x z a b
      = ((Fintype.card F : ℂ)⁻¹ * (Fintype.card F : ℂ)⁻¹) • ∑ p : F × F,
          sgn (Algebra.trace (ZMod 2) F (a * p.1) + Algebra.trace (ZMod 2) F (b * p.2))
            • hatObsComm P x z p.1 p.2 := by
  set q : ℂ := (Fintype.card F : ℂ)⁻¹ with hq
  have hA := trFourier_hatObsAt P .X x a
  have hB := trFourier_hatObsAt P .Z z b
  rw [hatComm, ← hA, ← hB, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, Finset.sum_mul_sum,
    Finset.sum_mul_sum, Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun j i => (sgn (Algebra.trace (ZMod 2) F (b * j)) •
    hatObsAt P .Z z j) * (sgn (Algebra.trace (ZMod 2) F (a * i)) • hatObsAt P .X x i))]
  rw [← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, hatObsComm, smul_sub, sgn_add, mul_comm
    (sgn (Algebra.trace (ZMod 2) F (b * s)))]

end Hat3

/-- **Parseval, for the commutator.** -/
theorem sum_stateSqNorm_hatComm [StarModule ℂ 𝒜] [StarProper 𝒜] (M : BipartiteModel 𝒞 𝒜 ℬ)
    (P : Question F m → POVMIn (Answer F m d) 𝒜) (x z : Point F m) :
    ∑ p : F × F, (M.reg (Anc F m)).stateSqNorm (hatComm P x z p.1 p.2)
      = ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * ∑ p : F × F, (M.reg (Anc F m)).stateSqNorm (hatObsComm P x z p.1 p.2) := by
  classical
  set N := M.reg (Anc F m) with hN
  have hvec : ∀ ab : F × F, N.π (N.πA (hatComm P x z ab.1 ab.2)) N.ψ
      = ((Fintype.card F : ℂ)⁻¹ * (Fintype.card F : ℂ)⁻¹) • ∑ p : F × F,
          sgn (Algebra.trace (ZMod 2) F (ab.1 * p.1) + Algebra.trace (ZMod 2) F (ab.2 * p.2))
            • N.π (N.πA (hatObsComm P x z p.1 p.2)) N.ψ := by
    intro ab
    rw [hatComm_eq_fourierOf, map_smul, map_sum, map_smul, map_sum,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply]
  have hnorm : ∀ X : Matrix (Anc F m) (Anc F m) 𝒜, N.stateSqNorm X = ‖N.π (N.πA X) N.ψ‖ ^ 2 :=
    fun X => rfl
  have hpar := sum_norm_trSum2_sq (fun p : F × F => N.π (N.πA (hatObsComm P x z p.1 p.2)) N.ψ)
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc : ‖((Fintype.card F : ℂ)⁻¹ * (Fintype.card F : ℂ)⁻¹)‖ ^ 2
      = ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    ring
  simp_rw [hnorm]
  rw [Finset.sum_congr rfl fun ab _ => by rw [hvec ab, norm_smul, mul_pow, hc], ← Finset.mul_sum,
    hpar]
  field_simp

/-! ## Projectivity

The sandwich is a POVM only because the `Z`-side hatted measurement is *projective*, so the
strategy has to be; every strategy of the Pauli basis test is. Projectivity passes through the
convolution: a product of projective measurements is projective, and so is a coarse-graining of
one. -/

/-- **The hatted point measurement is projective** when the strategy is. -/
theorem isPVM_hatMats {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R]
    {P : Question F m → POVMIn (Answer F m d) R}
    (hP : ∀ q, IsPVMIn (P q).op) (W : Bas) (u : Point F m) :
    IsPVMIn (hatMats P W u) :=
  POVMIn.isPVMIn_map (isPVMIn_kronIn (POVMIn.isPVMIn_map (hP (.point W u)) rdVal) _ _) _

/-! ## Splitting the content

The content average includes the uniform average over the two probes `(r_X, r_Z)`, independently
of everything else it carries. That is exactly what Parseval needs: the sum over *outcomes* of the
elements' commutator is the *average over probes* of the observables' (`sum_stateSqNorm_hatComm`),
and the content average of the second is the content average of the commutator at the content's
own probes --- which is what `lem:qld-expanded-points` bounds. -/

/-- The content, split into what the measurements see and the two probes. -/
def contentEquiv : Content F m ≃ ((Point F m × Point F m × F × Point F m) × (F × F)) where
  toFun c := ((c.uX, c.uZ, c.s, c.v), (c.rX, c.rZ))
  invFun p := ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_content_split {M : Type*} [AddCommMonoid M] (f : Content F m → M) :
    ∑ c : Content F m, f c
      = ∑ k : Point F m × Point F m × F × Point F m, ∑ p : F × F,
          f ⟨k.1, k.2.1, k.2.2.1, k.2.2.2, p.1, p.2⟩ := by
  classical
  rw [Fintype.sum_equiv contentEquiv f (fun q => f (contentEquiv.symm q)) fun c => rfl,
    ← Finset.univ_product_univ, Finset.sum_product]
  rfl

/-- The same, with the content's fields as separate arguments: the form the consumers use. -/
theorem sum_content_split' {M : Type*} [AddCommMonoid M]
    (f : Point F m → Point F m → F → Point F m → F → F → M) :
    ∑ c : Content F m, f c.uX c.uZ c.s c.v c.rX c.rZ
      = ∑ k : Point F m × Point F m × F × Point F m, ∑ p : F × F,
          f k.1 k.2.1 k.2.2.1 k.2.2.2 p.1 p.2 :=
  sum_content_split fun c => f c.uX c.uZ c.s c.v c.rX c.rZ

/-- **The probe average is free.** Averaging a probe-independent quantity over the content's own
probes changes nothing, so a bound stated at the content's probes is a bound on the average over
all probes --- which is the form Parseval produces. -/
theorem sum_content_avg_probe (g : Point F m → Point F m → F → F → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ * ∑ p : F × F, g c.uX c.uZ p.1 p.2)
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * g c.uX c.uZ c.rX c.rZ := by
  classical
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_content_split' (F := F) (m := m) fun x z _ _ _ _ =>
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ * ∑ p : F × F, g x z p.1 p.2),
    sum_content_split' (F := F) (m := m) fun x z _ _ r t =>
      (Fintype.card (Content F m) : ℝ)⁻¹ * g x z r t]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  field_simp

/-! ## The element-level commutator bound -/

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

set_option maxHeartbeats 1600000 in
/-- **The elements of the two bases' hatted point measurements commute on the expanded state**, on
average over the content, at the constant of `lem:qld-obs-commutation`. This is
`hatObs_commutation` moved from the observables to the measurement elements by Parseval, which
costs nothing --- the probe average the transform introduces is the one the content already
carries. -/
theorem sum_content_hatComm_le [StarModule ℂ 𝒜] [StarProper 𝒜] (hM : ‖M.ψ‖ = 1)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        (M.reg (Anc F m)).stateSqNorm (hatComm PA c.uX c.uZ p.1 p.2)
      ≤ 57676416 * ε := by
  classical
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
    rw [sum_stateSqNorm_hatComm M PA c.uX c.uZ],
    sum_content_avg_probe fun x z r s =>
      (M.reg (Anc F m)).stateSqNorm (hatObsComm PA x z r s)]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c (_ : c ∈ univ) => ?_))
    (hatObs_commutation (PB := PB) hM hPA hfail)
  congr 1
  show (M.reg (Anc F m)).stateSqNorm (hatObsComm PA c.uX c.uZ c.rX c.rZ)
    = (M.reg (Anc F m)).stateSqNorm (hatObs hm PA .X c * hatObs hm PA .Z c
        - hatObs hm PA .Z c * hatObs hm PA .X c)
  rw [hatObsComm,
    show hatObsAt PA .X c.uX c.rX = hatObs hm PA .X c from hatObsAt_self hm PA .X c,
    show hatObsAt PA .Z c.uZ c.rZ = hatObs hm PA .Z c from hatObsAt_self hm PA .Z c]

/-- The same for the other player, by the game's symmetry in the two players: the second player's
state norm on the expanded model. -/
theorem sum_content_hatComm_le_B [StarModule ℂ ℬ] [StarProper ℬ] (hM : ‖M.ψ‖ = 1)
    (hPB : ∀ q, IsPVMIn (PB q).op) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        (M.reg (Anc F m)).swap.stateSqNorm (hatComm PB c.uX c.uZ p.1 p.2)
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le (hm := hm) (M := M.swap) (PA := PB) (PB := PA)
    (swapVec_unit hM) hPB (povmValue_swapped_le hfail)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) h
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hatVec_swapVec]

/-! ## The cross-party consistency, at the points -/

/-- `lem:qld-expanded-points`'s first item, re-indexed by the point. -/
theorem hatPOVM_mats_eq {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R] (hm : m ∣ Fintype.card F)
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (c : Content F m) (a : F) :
    (hatPOVM hm P W c).op a = hatMats P W (c.pt W) a := by
  rw [hatPOVM_eq hm P W c]
  rfl

theorem sum_content_hatMats_consistency [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
    [StarProper ℬ] (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a) (hatMats PB W (c.pt W) a)
      ≤ 172 * ε := by
  have h := hatPOVM_consistency (PB := PB) hM hfail W
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
        rw [hatPOVM_mats_eq hm PA W c a, hatPOVM_mats_eq hm PB W c a])] at h
  exact h

/-! ## The lemma -/

/-- **The error of `lem:qld-combined-points`**, the paper's `delta_Q(eps) = poly(eps)`. The square
roots are the three Cauchy--Schwarz steps of the sandwich's self-consistency chain; the linear term
is the `Z`-consistency, which enters without one. -/
def deltaQ (ε : ℝ) : ℝ :=
  2 * Real.sqrt (57676416 * ε) + Real.sqrt (86 * ε) + 86 * ε

theorem sum_uniform_content : ∑ _c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ = 1 := by
  have hpos : 0 < Fintype.card (Content F m) :=
    Fintype.card_pos_iff.mpr ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne')

theorem deltaQ_eq (ε : ℝ) :
    Real.sqrt (57676416 * ε) + Real.sqrt (57676416 * ε) + Real.sqrt (172 * ε / 2)
      + 172 * ε / 2 = deltaQ ε := by
  rw [deltaQ, show (172 : ℝ) * ε / 2 = 86 * ε from by ring]
  ring

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-combined-points`, the dilated measurement.** For each pair of points `(x, z)` there
is a *projective* measurement in each player's algebra of the expanded model, enlarged by one
dilation register `(F × F) ⊕ (F × F)` in the state `|inl (0, 0)⟩`, which returns the `X`-value at
`x` and the `Z`-value at `z` at once; it is self-consistent across the two parties on average over
the content, and consistent with **both** ordered products of the expanded point measurements. The
measurement is the Halmos dilation of the sandwich `M-hat^{Z,z}_b M-hat^{X,x}_a M-hat^{Z,z}_b`, and
the third and fourth conclusions record the compression identity, which is what carries the
estimates. This is the form the pasting lemma of `lem:qld-pairs-of-lines` consumes; the agreement
form of the same estimates, in the expanded model itself, is `combined_points`. -/
theorem combined_points_dilated [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) :
    ∃ (QA : Content F m → F × F →
        Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) 𝒜))
      (QB : Content F m → F × F →
        Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) ℬ)),
      (∀ c, IsPVMIn (QA c)) ∧ (∀ c, IsPVMIn (QB c))
      ∧ (∀ c p, QA c p (Sum.inl ((0 : F), (0 : F))) (Sum.inl ((0 : F), (0 : F)))
          = sand (hatMats PA .X c.uX) (hatMats PA .Z c.uZ) p)
      ∧ (∀ c p, QB c p (Sum.inl ((0 : F), (0 : F))) (Sum.inl ((0 : F), (0 : F)))
          = sand (hatMats PB .X c.uX) (hatMats PB .Z c.uZ) p)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
            ((M.reg (Anc F m)).jointModel ((0 : F), (0 : F))).xSqNorm (QA c p) (QB c p)
          ≤ 2 * deltaQ ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
            ((M.reg (Anc F m)).jointModel ((0 : F), (0 : F))).xSqNorm (QA c p)
              (smulKron (hatMats PB .Z c.uZ p.2 * hatMats PB .X c.uX p.1) 1)
          ≤ 4 * deltaQ ε + 115352832 * ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
            ((M.reg (Anc F m)).jointModel ((0 : F), (0 : F))).xSqNorm (QA c p)
              (smulKron (hatMats PB .X c.uX p.1 * hatMats PB .Z c.uZ p.2) 1)
          ≤ 4 * deltaQ ε + 461411328 * ε) := by
  classical
  obtain ⟨QA, QB, hQA, hQB, hkA, hkB, h1, h2, h3⟩ :=
    (M.reg (Anc F m)).exists_projective_joint (A := F) (ι := Content F m)
      (w := fun _ : Content F m => (Fintype.card (Content F m) : ℝ)⁻¹)
      (fun _ => by positivity) sum_uniform_content (hatVec_unit hM) ((0 : F), (0 : F))
      (X := fun c : Content F m => hatMats PA .X c.uX)
      (Z := fun c : Content F m => hatMats PA .Z c.uZ)
      (X' := fun c : Content F m => hatMats PB .X c.uX)
      (Z' := fun c : Content F m => hatMats PB .Z c.uZ)
      (fun c => isPVM_hatMats hPA .X c.uX) (fun c => isPVM_hatMats hPA .Z c.uZ)
      (fun c => isPVM_hatMats hPB .X c.uX) (fun c => isPVM_hatMats hPB .Z c.uZ)
      (cA := 57676416 * ε) (cB := 57676416 * ε) (α := 172 * ε) (β := 172 * ε)
      (sum_content_hatComm_le (PB := PB) hM hPA hfail)
      (sum_content_hatComm_le_B (PA := PA) hM hPB hfail)
      (sum_content_hatMats_consistency (PB := PB) hM hfail .X)
      (sum_content_hatMats_consistency (PB := PB) hM hfail .Z)
  refine ⟨QA, QB, hQA, hQB, hkA, hkB, ?_, ?_, ?_⟩
  · rw [← deltaQ_eq]; exact h1
  · rw [← deltaQ_eq, show (115352832 : ℝ) * ε = 2 * (57676416 * ε) from by ring]; exact h2
  · rw [← deltaQ_eq, show (461411328 : ℝ) * ε = 8 * (57676416 * ε) from by ring]; exact h3

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-combined-points`**, as agreement bounds of the sandwiches in the expanded model. The
sandwich `R_{a,b} = M-hat^{Z,z}_b M-hat^{X,x}_a M-hat^{Z,z}_b` is a POVM in each player's algebra
of `M.reg (Anc F m)` (`POVMIn.sand`); on average over the content the two players' sandwiches
disagree with probability at most `delta_Q`, and the first player's sandwich disagrees with each
ordered product of the second player's expanded point measurements at most half the constants of
the matrix statement. The constants are those of the dilated measurement of
`combined_points_dilated`, halved: the summed deviation of a projective pair is twice its
disagreement, and the dilation compresses to the sandwich (`BipartiteModel.jointModel_bornProb`),
so the dilation stays inside the proof. -/
theorem combined_points [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) :
    (1 - ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        (M.reg (Anc F m)).bornProb (sand (hatMats PA .X c.uX) (hatMats PA .Z c.uZ) p)
          (sand (hatMats PB .X c.uX) (hatMats PB .Z c.uZ) p)
        ≤ deltaQ ε)
      ∧ (1 - ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
          (M.reg (Anc F m)).bornProb (sand (hatMats PA .X c.uX) (hatMats PA .Z c.uZ) p)
            (hatMats PB .Z c.uZ p.2 * hatMats PB .X c.uX p.1)
          ≤ (4 * deltaQ ε + 115352832 * ε) / 2)
      ∧ (1 - ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
          (M.reg (Anc F m)).bornProb (sand (hatMats PA .X c.uX) (hatMats PA .Z c.uZ) p)
            (hatMats PB .X c.uX p.1 * hatMats PB .Z c.uZ p.2)
          ≤ (4 * deltaQ ε + 461411328 * ε) / 2) := by
  classical
  set N := M.reg (Anc F m) with hN
  have hN1 : ‖N.ψ‖ = 1 := hatVec_unit hM
  obtain ⟨QA, QB, hQA, hQB, hkA, hkB, h1, h2, h3⟩ :=
    combined_points_dilated (PA := PA) (PB := PB) hM hfail hPA hPB
  -- the ordered products are complete, on the second player's side
  have hordZX : ∀ c : Content F m, ∑ p : F × F,
      N.swap.stateSqNorm (hatMats PB .Z c.uZ p.2 * hatMats PB .X c.uX p.1) = 1 := by
    intro c
    rw [← N.swap.sum_stateSqNorm_ord hN1 (isPVM_hatMats hPB .Z c.uZ) (isPVM_hatMats hPB .X c.uX)]
    exact Fintype.sum_equiv (Equiv.prodComm F F) _ _ fun p => rfl
  have hordXZ : ∀ c : Content F m, ∑ p : F × F,
      N.swap.stateSqNorm (hatMats PB .X c.uX p.1 * hatMats PB .Z c.uZ p.2) = 1 := fun c =>
    N.swap.sum_stateSqNorm_ord hN1 (isPVM_hatMats hPB .X c.uX) (isPVM_hatMats hPB .Z c.uZ)
  -- the dilated deviation against a complete family is twice the disagreement of the compression
  have hread : ∀ (S : Content F m → F × F → Matrix (Anc F m) (Anc F m) ℬ),
      (∀ c, ∑ p : F × F, N.swap.stateSqNorm (S c p) = 1) →
      ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
          (N.jointModel ((0 : F), (0 : F))).xSqNorm (QA c p) (smulKron (S c p) 1)
        = 2 * (1 - ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
            N.bornProb (sand (hatMats PA .X c.uX) (hatMats PA .Z c.uZ) p) (S c p)) := by
    intro S hS
    rw [Finset.sum_congr rfl fun c _ => by
      rw [N.jointModel_sum_xSqNorm_smulKron hN1 _ (hQA c), hS c]]
    simp only [hkA]
    rw [mul_sub, mul_one, Finset.mul_sum, ← sum_uniform_content (F := F) (m := m), Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← deltaQ_eq]
    exact N.one_sub_sum_bornProb_sand_le (A := F) (ι := Content F m)
      (w := fun _ : Content F m => (Fintype.card (Content F m) : ℝ)⁻¹)
      (fun _ => by positivity) sum_uniform_content hN1
      (X := fun c : Content F m => hatMats PA .X c.uX)
      (Z := fun c : Content F m => hatMats PA .Z c.uZ)
      (X' := fun c : Content F m => hatMats PB .X c.uX)
      (Z' := fun c : Content F m => hatMats PB .Z c.uZ)
      (fun c => isPVM_hatMats hPA .X c.uX) (fun c => isPVM_hatMats hPA .Z c.uZ)
      (fun c => isPVM_hatMats hPB .X c.uX) (fun c => isPVM_hatMats hPB .Z c.uZ)
      (sum_content_hatComm_le (PB := PB) hM hPA hfail)
      (sum_content_hatComm_le_B (PA := PA) hM hPB hfail)
      (sum_content_hatMats_consistency (PB := PB) hM hfail .X)
      (sum_content_hatMats_consistency (PB := PB) hM hfail .Z)
  · have h := hread (fun c p => hatMats PB .Z c.uZ p.2 * hatMats PB .X c.uX p.1) hordZX
    rw [h] at h2
    linarith
  · have h := hread (fun c p => hatMats PB .X c.uX p.1 * hatMats PB .Z c.uZ p.2) hordXZ
    rw [h] at h3
    linarith

/-! ## The padded point measurement

Blueprint `lem:qld-padded-points`. A point of the padded space `F_q^{4m}` is
`u = (x, z, alpha, beta, w)`, and the measurement returns the *combined* value
`alpha g_X(x) + beta g_Z(z)`: the combined point measurement of
`lem:qld-combined-points`, coarse-grained along the linear form `(a, b) |-> alpha a + beta b`.
It depends on `u` only through `(x, z, alpha, beta)`, which is what ``independent of the dummy
coordinates'' means, and it is indexed by those here.

The two conclusions are free for opposite reasons. Self-consistency survives the coarse-graining
at no cost because both families are *projective*, so the deviation and the agreement determine
each other and agreement only increases (`BipartiteModel.sum_xSqNorm_map_le`). Consistency with the
ordered products does *not* survive it unaided --- the fibres have `q` elements and a triangle
inequality would cost exactly that factor --- and what saves it is Parseval over `F_q`
(`BipartiteModel.sum_avg_xSqNorm_fibre_eq`), whose zero-probe term vanishes because the deviation
family sums to zero: both `sum_{a,b} Q-hat_{a,b}` and `sum_{a,b} M-hat^Z_b M-hat^X_a` are the
identity. The measurement is the dilated one of `combined_points_dilated`, coarse-grained, so the
statement is in the model of the dilation. -/

/-- Bob's ordered product, `Z` then `X`. -/
def hatOrdZX {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
    [StarOrderedRing R] [StarProper R] (P : Question F m → POVMIn (Answer F m d) R)
    (x z : Point F m) (p : F × F) : Matrix (Anc F m) (Anc F m) R :=
  hatMats P .Z z p.2 * hatMats P .X x p.1

/-- Bob's ordered product, `X` then `Z`. -/
def hatOrdXZ {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
    [StarOrderedRing R] [StarProper R] (P : Question F m → POVMIn (Answer F m d) R)
    (x z : Point F m) (p : F × F) : Matrix (Anc F m) (Anc F m) R :=
  hatMats P .X x p.1 * hatMats P .Z z p.2

theorem sum_hatOrdZX {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R]
    {P : Question F m → POVMIn (Answer F m d) R}
    (hP : ∀ q, IsPVMIn (P q).op) (x z : Point F m) :
    ∑ p : F × F, hatOrdZX P x z p = 1 := by
  rw [sum_prod_swap (fun p : F × F => hatOrdZX P x z p)]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
      (∑ a : F, hatOrdZX P x z (a, b)) = hatMats P .Z z b from by
    rw [show (∑ a : F, hatOrdZX P x z (a, b))
        = hatMats P .Z z b * ∑ a : F, hatMats P .X x a from by
      rw [Finset.mul_sum]
      rfl, (isPVM_hatMats hP .X x).sum_eq_one, mul_one]]
  exact (isPVM_hatMats hP .Z z).sum_eq_one

theorem sum_hatOrdXZ {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R]
    {P : Question F m → POVMIn (Answer F m d) R}
    (hP : ∀ q, IsPVMIn (P q).op) (x z : Point F m) :
    ∑ p : F × F, hatOrdXZ P x z p = 1 := by
  rw [sum_prod_id (fun p : F × F => hatOrdXZ P x z p)]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => show
      (∑ b : F, hatOrdXZ P x z (a, b)) = hatMats P .X x a from by
    rw [show (∑ b : F, hatOrdXZ P x z (a, b))
        = hatMats P .X x a * ∑ b : F, hatMats P .Z z b from by
      rw [Finset.mul_sum]
      rfl, (isPVM_hatMats hP .Z z).sum_eq_one, mul_one]]
  exact (isPVM_hatMats hP .X x).sum_eq_one

/-- **Parseval for the padded coarse-graining.** On average over `(alpha, beta)` the summed
deviation of the two families coarse-grained along `(a, b) |-> alpha a + beta b` is `1 - 1/q`
times the families' own --- in particular no worse, although the fibres have `q` elements. The
two normalizations are what make the zero probe drop out. This is
`BipartiteModel.sum_avg_xSqNorm_fibre_eq` (`MIPRE/Foundations/ModelCalculus.lean`). -/
theorem sum_avg_xSqNorm_fibre_eq {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
    [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
    (N : BipartiteModel 𝒞' 𝒜' ℬ') {Q : F × F → 𝒜'} {B : F × F → ℬ'}
    (hQ : ∑ p : F × F, Q p = 1) (hB : ∑ p : F × F, B p = 1) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ v : F, N.xSqNorm
          (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, Q p)
          (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, B p)
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, N.xSqNorm (Q p) (B p) :=
  N.sum_avg_xSqNorm_fibre_eq hQ hB

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-padded-points`.** The padded space's point measurement: the combined `XZ`
measurement coarse-grained along `(a, b) |-> alpha a + beta b`, so that it returns the single
field element `alpha g_X(x) + beta g_Z(z)`. It is indexed by `(x, z, alpha, beta)` --- which is
what ``independent of the dummy coordinates'' means --- projective, self-consistent, and
consistent with both ordered products of the expanded point measurements, coarse-grained the same
way. -/
theorem padded_points [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) :
    ∃ (QA : Content F m → F × F → F →
        Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) 𝒜))
      (QB : Content F m → F × F → F →
        Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) ℬ)),
      (∀ c ab, IsPVMIn (QA c ab)) ∧ (∀ c ab, IsPVMIn (QB c ab))
      ∧ (∀ ab : F × F, ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
            ∑ v : F, ((M.reg (Anc F m)).jointModel ((0 : F), (0 : F))).xSqNorm
              (QA c ab v) (QB c ab v)
          ≤ 2 * deltaQ ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
            ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
              ∑ v : F, ((M.reg (Anc F m)).jointModel ((0 : F), (0 : F))).xSqNorm (QA c ab v)
                (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v,
                  smulKron (hatOrdZX PB c.uX c.uZ p) 1)
          ≤ 4 * deltaQ ε + 115352832 * ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
            ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
              ∑ v : F, ((M.reg (Anc F m)).jointModel ((0 : F), (0 : F))).xSqNorm (QA c ab v)
                (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v,
                  smulKron (hatOrdXZ PB c.uX c.uZ p) 1)
          ≤ 4 * deltaQ ε + 461411328 * ε) := by
  classical
  obtain ⟨QA0, QB0, hQA, hQB, -, -, h1, h2, h3⟩ :=
    combined_points_dilated (PA := PA) (PB := PB) hM hfail hPA hPB
  set N₃ := (M.reg (Anc F m)).jointModel ((0 : F), (0 : F)) with hN₃
  have hN₃1 : ‖N₃.ψ‖ = 1 := by
    rw [hN₃, BipartiteModel.norm_expand_state, norm_basisVec, one_mul]
    exact hatVec_unit hM
  have hq2 : (1 : ℝ) - (Fintype.card F : ℝ)⁻¹ ≤ 1 := by
    have : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
    linarith
  -- Bob's ordered products sum to the identity, which is what kills the zero probe
  have hZX : ∀ c : Content F m, ∑ p : F × F,
      smulKron (hatOrdZX PB c.uX c.uZ p) (1 : Matrix ((F × F) ⊕ (F × F)) _ ℂ) = 1 := by
    intro c
    rw [← smulKron_sum_left, sum_hatOrdZX hPB, smulKron_one_one]
  have hXZ : ∀ c : Content F m, ∑ p : F × F,
      smulKron (hatOrdXZ PB c.uX c.uZ p) (1 : Matrix ((F × F) ⊕ (F × F)) _ ℂ) = 1 := by
    intro c
    rw [← smulKron_sum_left, sum_hatOrdXZ hPB, smulKron_one_one]
  refine ⟨fun c ab v => ∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, QA0 c p,
    fun c ab v => ∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, QB0 c p,
    fun c ab => (hQA c).coarse _, fun c ab => (hQB c).coarse _, ?_, ?_, ?_⟩
  · -- item 1: coarse-graining costs nothing, both families being projective
    intro ab
    refine le_trans (Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) h1
    have hmap := N₃.sum_xSqNorm_map_le (A := F × F) (C := F) hN₃1
      (hQA c).toPOVMIn (hQB c).toPOVMIn (hQA c) (hQB c)
      (fun p : F × F => ab.1 * p.1 + ab.2 * p.2)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun v _ => ?_)) hmap
    rw [POVMIn.map_op, POVMIn.map_op]
    rfl
  · -- item 2: Parseval, and the zero probe drops out
    refine le_trans (Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) h2
    rw [N₃.sum_avg_xSqNorm_fibre_eq (hQA c).sum_eq_one (hZX c)]
    refine le_trans (mul_le_mul_of_nonneg_right hq2 (Finset.sum_nonneg fun p _ =>
      N₃.xSqNorm_nonneg _ _)) (le_of_eq ?_)
    rw [one_mul]
    rfl
  · -- item 3: the same, at the other order
    refine le_trans (Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) h3
    rw [N₃.sum_avg_xSqNorm_fibre_eq (hQA c).sum_eq_one (hXZ c)]
    refine le_trans (mul_le_mul_of_nonneg_right hq2 (Finset.sum_nonneg fun p _ =>
      N₃.xSqNorm_nonneg _ _)) (le_of_eq ?_)
    rw [one_mul]
    rfl

end Combined

end QLD

end MIPRE

end

end
