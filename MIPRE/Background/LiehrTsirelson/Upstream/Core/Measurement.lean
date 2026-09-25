/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core/Measurement.lean, from a snapshot of the `main` branch supplied on 2026-09-25
(archive, no commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core.Game

/-!
# POVMs, PVMs, outcome maps, coarse-graining, and the canonical Born probability

Sources:

* `Blueprint/Nodes/B04-Naimark-Synchronous/Math.tex`, `definition:001`
  (POVM: positive semidefinite operators summing to `Id`; *projective* if each
  effect is a projection);
* `Blueprint/Nodes/B03-Measurement-Calculus/Math.tex`,
  `def:measurement-coarse-graining` (`M_{[f(·)=b]} = ∑_{a : f a = b} M_a`);
* `Blueprint/Nodes/B23-Games/Parts/01-GamesAndStrategies.tex`,
  `def:tensor-product-value` (the Born expectation `⟨ψ| A^x_a ⊗ B^y_b |ψ⟩`);
* `Blueprint/Nodes/B05-NPA-Core/Math.tex`, `def:n7b` (the commuting expectation
  `⟨ψ, A^x_a B^y_b ψ⟩`).

## Representation decisions (see `API_REVIEW.md` §2–§4)

* One finite Hilbert space representation: `FinH d = EuclideanSpace ℂ (Fin d)`,
  with bipartite space `EuclideanSpace ℂ (Fin dA × Fin dB)`.
* One operator representation: `H →L[ℂ] H`, for the finite-dimensional *and* the
  arbitrary-Hilbert-space layers.  Matrices enter only through Mathlib's star
  algebra equivalence `Matrix.toEuclideanCLM`, and every transported fact below
  is proved.
* One Born-probability construction, `born`, used by both strategy classes.
-/

open scoped Matrix Kronecker ComplexOrder

namespace Tsirelson

noncomputable section

/-! ## The canonical Born probability -/

section Born

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The **canonical Born probability**: the real part of `⟪ψ, T ψ⟫`.

This is the *only* Born construction in the core.  Both `TensorStrategy.corr`
and `CommutingStrategy.corr` are defined through it, differing only in which
operator they feed in.  Realness is not assumed: `born_coe` proves that for a
positive `T` the complex expectation *equals* this real number, so the packet
never switches between a complex equality and a real-part definition. -/
def born (ψ : H) (T : H →L[ℂ] H) : ℝ := (inner ℂ ψ (T ψ)).re

/-- For a positive operator the complex expectation is literally the stored real
number: the Born value loses no imaginary part. -/
theorem born_coe {ψ : H} {T : H →L[ℂ] H} (hT : T.IsPositive) :
    ((born ψ T : ℝ) : ℂ) = inner ℂ ψ (T ψ) := by
  have h : (0 : ℂ) ≤ inner ℂ ψ (T ψ) := hT.inner_nonneg_right ψ
  have him : (inner ℂ ψ (T ψ)).im = 0 := by simpa using h.2.symm
  apply Complex.ext <;> simp [born, him]

theorem born_nonneg {ψ : H} {T : H →L[ℂ] H} (hT : T.IsPositive) : 0 ≤ born ψ T :=
  hT.re_inner_nonneg_right ψ

theorem born_sum {ι : Type*} [Fintype ι] (ψ : H) (T : ι → (H →L[ℂ] H)) :
    born ψ (∑ i, T i) = ∑ i, born ψ (T i) := by
  simp [born, sum_apply]

theorem born_one (ψ : H) : born ψ 1 = ‖ψ‖ ^ 2 := by
  simp [born, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem born_sub (ψ : H) (S T : H →L[ℂ] H) :
    born ψ (S - T) = born ψ S - born ψ T := by
  simp [born]

/-- A Born value of an effect dominated by the identity, on a unit vector, is at
most one. -/
theorem born_le_one_of_one_sub_isPositive {ψ : H} {T : H →L[ℂ] H} (hψ : ‖ψ‖ = 1)
    (hT' : (1 - T).IsPositive) : born ψ T ≤ 1 := by
  have h := born_nonneg (ψ := ψ) hT'
  rw [born_sub, born_one, hψ] at h
  linarith

end Born

/-! ## Positive operators: auxiliary facts -/

section PositiveAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A finite family of positive operators summing to zero vanishes termwise.

Over `ℂ` an operator whose quadratic form vanishes identically is zero
(`inner_map_self_eq_zero`), so it suffices to kill the quadratic form. -/
theorem eq_zero_of_sum_isPositive_eq_zero {ι : Type*} {s : Finset ι}
    {T : ι → (H →L[ℂ] H)} (hpos : ∀ i ∈ s, (T i).IsPositive)
    (hsum : ∑ i ∈ s, T i = 0) {j : ι} (hj : j ∈ s) : T j = 0 := by
  have key : ∀ x : H, (inner ℂ ((T j) x) x : ℂ) = 0 := by
    intro x
    have hx : (∑ i ∈ s, T i) x = 0 := by rw [hsum]; simp
    have happ : ∑ i ∈ s, (inner ℂ ((T i) x) x : ℂ) = 0 := by
      have := congrArg (fun v => (inner ℂ v x : ℂ)) hx
      simpa [sum_apply, sum_inner] using this
    have hre : ∑ i ∈ s, (inner ℂ ((T i) x) x).re = 0 := by
      simpa using congrArg Complex.re happ
    have hnn : ∀ i ∈ s, 0 ≤ (inner ℂ ((T i) x) x).re := fun i hi =>
      (hpos i hi).re_inner_nonneg_left x
    have hzero : (inner ℂ ((T j) x) x).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre j hj
    have him : (inner ℂ ((T j) x) x).im = 0 := by
      simpa using ((hpos j hj).inner_nonneg_left x).2.symm
    apply Complex.ext <;> simp [hzero, him]
  have h0 : ((T j : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0 := (inner_map_self_eq_zero _).mp key
  exact ContinuousLinearMap.coe_injective (by simpa using h0)

end PositiveAux

/-! ## POVMs and PVMs -/

/-- A **POVM** on a complex Hilbert space `H` with outcomes in a finite set `A`:
a family of positive operators summing to the identity.

This is B04 `definition:001` verbatim.  Self-adjointness is *derived* from
positivity, not stored, so the mathematical notion is unchanged. -/
structure POVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Type*) [Fintype A] where
  /-- The effect operator attached to each outcome. -/
  effect : A → (H →L[ℂ] H)
  /-- Every effect is a positive operator. -/
  positive : ∀ a, (effect a).IsPositive
  /-- The effects resolve the identity. -/
  sum_eq_one : ∑ a, effect a = 1

namespace POVM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A A' : Type*} [Fintype A] [Fintype A']

theorem effect_isSelfAdjoint (M : POVM H A) (a : A) : IsSelfAdjoint (M.effect a) :=
  (M.positive a).isSelfAdjoint

/-- Each effect is dominated by the identity. -/
theorem one_sub_effect_isPositive (M : POVM H A) (a : A) : (1 - M.effect a).IsPositive := by
  classical
  have hsplit : M.effect a + ∑ b ∈ Finset.univ.erase a, M.effect b = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    exact M.sum_eq_one
  rw [← eq_sub_of_add_eq' hsplit]
  exact ContinuousLinearMap.isPositive_sum _ fun b _ => M.positive b

/-- The Born probabilities of a POVM on a unit vector lie in `[0,1]`. -/
theorem born_effect_mem_Icc (M : POVM H A) {ψ : H} (hψ : ‖ψ‖ = 1) (a : A) :
    born ψ (M.effect a) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨born_nonneg (M.positive a),
    born_le_one_of_one_sub_isPositive hψ (M.one_sub_effect_isPositive a)⟩

/-- **Coarse-graining** at the level of effects: B03's `M_{[f(·)=b]}`. -/
def coarseGrain [DecidableEq A'] (M : POVM H A) (f : A → A') (b : A') : H →L[ℂ] H :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a

omit [Fintype A'] in
theorem coarseGrain_isPositive [DecidableEq A'] (M : POVM H A) (f : A → A') (b : A') :
    (M.coarseGrain f b).IsPositive :=
  ContinuousLinearMap.isPositive_sum _ fun a _ => M.positive a

theorem sum_coarseGrain [DecidableEq A'] (M : POVM H A) (f : A → A') :
    ∑ b, M.coarseGrain f b = 1 := by
  rw [← M.sum_eq_one]
  exact Finset.sum_fiberwise _ _ _

/-- **Outcome mapping**: the pushforward measurement along `f : A → A'`, whose
effects are the coarse-grained families.  The measurement laws are preserved by
proof, not by assumption. -/
def mapOutcome [DecidableEq A'] (M : POVM H A) (f : A → A') : POVM H A' where
  effect := M.coarseGrain f
  positive := M.coarseGrain_isPositive f
  sum_eq_one := M.sum_coarseGrain f

@[simp] theorem mapOutcome_effect [DecidableEq A'] (M : POVM H A) (f : A → A') (b : A') :
    (M.mapOutcome f).effect b = M.coarseGrain f b := rfl

end POVM

/-- A **PVM**: a POVM whose effects are idempotent, i.e. a projective measurement
in the sense of B04 `definition:001` and B23 `def:projective-strategy`.

Mutual orthogonality is *proved* (`PVM.orthogonal`), not stored; that is what
makes `PVM.mapOutcome` land in `PVM` again. -/
structure PVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Type*) [Fintype A] extends POVM H A where
  /-- Each effect is idempotent, hence an orthogonal projection. -/
  idempotent : ∀ a, effect a * effect a = effect a

namespace PVM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A A' : Type*} [Fintype A] [Fintype A']

/-- Distinct effects of a projective measurement are orthogonal.

For `a ≠ b`, each `P a * P c * P a` is positive and they sum over `c ≠ a` to
`P a * (1 - P a) * P a = 0`; a positive family summing to zero vanishes
termwise, so `P a * P b * P a = 0`.  The C*-identity then gives
`P b * P a = 0`, and taking adjoints gives `P a * P b = 0`. -/
theorem orthogonal (M : PVM H A) {a b : A} (hab : a ≠ b) :
    M.effect a * M.effect b = 0 := by
  classical
  let P : A → (H →L[ℂ] H) := M.effect
  have hsa : ∀ c, IsSelfAdjoint (P c) := fun c => M.toPOVM.effect_isSelfAdjoint c
  have hadj : ContinuousLinearMap.adjoint (P a) = P a := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa a
  have hconj_pos : ∀ c, (P a * P c * P a).IsPositive := by
    intro c
    have h := (M.positive c).conj_adjoint (P a)
    rw [hadj] at h
    have heq : P a * P c * P a = P a ∘L (P c ∘L P a) := by
      simp only [← ContinuousLinearMap.mul_def]
      exact mul_assoc _ _ _
    rw [heq]
    exact h
  have h1 : ∑ c ∈ Finset.univ.erase a, P c = 1 - P a := by
    have hsplit : P a + ∑ c ∈ Finset.univ.erase a, P c = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ a)]
      exact M.sum_eq_one
    exact eq_sub_of_add_eq' hsplit
  have hsum : ∑ c ∈ Finset.univ.erase a, (P a * P c * P a) = 0 := by
    have hfac : ∑ c ∈ Finset.univ.erase a, (P a * P c * P a)
        = P a * (∑ c ∈ Finset.univ.erase a, P c) * P a := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hfac, h1, mul_sub, mul_one, M.idempotent a, sub_self, zero_mul]
  have hzero : P a * P b * P a = 0 :=
    eq_zero_of_sum_isPositive_eq_zero (fun c _ => hconj_pos c) hsum
      (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩)
  have hba : P b * P a = 0 := by
    refine CStarRing.star_mul_self_eq_zero_iff _ |>.mp ?_
    rw [star_mul, (hsa a).star_eq, (hsa b).star_eq]
    calc P a * P b * (P b * P a)
        = P a * (P b * P b) * P a := by
          rw [mul_assoc (P a) (P b), ← mul_assoc (P b) (P b), ← mul_assoc]
      _ = P a * P b * P a := by rw [M.idempotent b]
      _ = 0 := hzero
  have := congrArg (fun T : H →L[ℂ] H => star T) hba
  simpa [star_mul, (hsa a).star_eq, (hsa b).star_eq] using this

omit [Fintype A'] in
theorem coarseGrain_idempotent [DecidableEq A'] (M : PVM H A) (f : A → A') (b : A') :
    M.toPOVM.coarseGrain f b * M.toPOVM.coarseGrain f b = M.toPOVM.coarseGrain f b := by
  classical
  simp only [POVM.coarseGrain]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum,
    Finset.sum_eq_single a (fun c _ hca => M.orthogonal (Ne.symm hca)) (fun hna => absurd ha hna)]
  exact M.idempotent a

/-- B03's coarse-grained effect family for a projective measurement. -/
def coarseGrain [DecidableEq A'] (M : PVM H A) (f : A → A') (b : A') : H →L[ℂ] H :=
  M.toPOVM.coarseGrain f b

/-- Coarse-graining a projective measurement gives a projective measurement. -/
def mapOutcome [DecidableEq A'] (M : PVM H A) (f : A → A') : PVM H A' where
  toPOVM := M.toPOVM.mapOutcome f
  idempotent := M.coarseGrain_idempotent f

@[simp] theorem mapOutcome_effect [DecidableEq A'] (M : PVM H A) (f : A → A') (b : A') :
    (M.mapOutcome f).effect b = M.coarseGrain f b := rfl

end PVM

/-! ## Finite-dimensional spaces and the tensor-leg operator -/

/-- The single finite-dimensional Hilbert space representation used by the core. -/
abbrev FinH (d : ℕ) : Type := EuclideanSpace ℂ (Fin d)

/-- The matrix of a finite-dimensional operator, through Mathlib's star algebra
equivalence. -/
def toMat {m : ℕ} (S : FinH m →L[ℂ] FinH m) : Matrix (Fin m) (Fin m) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm S

/-- The tensor product `S ⊗ T` of two finite-dimensional operators, acting on the
bipartite space `EuclideanSpace ℂ (Fin m × Fin n)`. -/
def kronCLM {m n : ℕ} (S : FinH m →L[ℂ] FinH m) (T : FinH n →L[ℂ] FinH n) :
    EuclideanSpace ℂ (Fin m × Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m × Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (toMat S ⊗ₖ toMat T)

/-- Positivity transports along `Matrix.toEuclideanCLM`.

**Note.** This must be stated for a general index type: the Kronecker product has
index type `Fin m × Fin n`, which is not syntactically `Fin k`.  Stating it only
for `Fin n` makes the unifier diverge instead of failing cleanly. -/
theorem isPositive_toEuclideanCLM_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) M).IsPositive ↔ M.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.isPositive_toEuclideanLin_iff]

theorem posSemidef_toMat {m : ℕ} {S : FinH m →L[ℂ] FinH m} (hS : S.IsPositive) :
    (toMat S).PosSemidef := by
  rw [toMat, ← isPositive_toEuclideanCLM_iff, StarAlgEquiv.apply_symm_apply]
  exact hS

theorem kronCLM_isPositive {m n : ℕ} {S : FinH m →L[ℂ] FinH m} {T : FinH n →L[ℂ] FinH n}
    (hS : S.IsPositive) (hT : T.IsPositive) : (kronCLM S T).IsPositive := by
  rw [kronCLM, isPositive_toEuclideanCLM_iff]
  exact (posSemidef_toMat hS).kronecker (posSemidef_toMat hT)

@[simp] theorem toMat_one {m : ℕ} : toMat (1 : FinH m →L[ℂ] FinH m) = 1 := by
  rw [toMat, map_one]

@[simp] theorem kronCLM_one_one {m n : ℕ} :
    kronCLM (1 : FinH m →L[ℂ] FinH m) (1 : FinH n →L[ℂ] FinH n) = 1 := by
  rw [kronCLM, toMat_one, toMat_one, Matrix.one_kronecker_one, map_one]

theorem sum_kronecker_gen {ι : Type*} [Fintype ι] {m n : ℕ}
    (M : ι → Matrix (Fin m) (Fin m) ℂ) (N : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, M i) ⊗ₖ N = ∑ i, (M i ⊗ₖ N) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

theorem kronecker_sum_gen {ι : Type*} [Fintype ι] {m n : ℕ}
    (M : Matrix (Fin m) (Fin m) ℂ) (N : ι → Matrix (Fin n) (Fin n) ℂ) :
    M ⊗ₖ (∑ i, N i) = ∑ i, (M ⊗ₖ N i) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

theorem kronCLM_sum_left {m n : ℕ} {ι : Type*} [Fintype ι] (S : ι → (FinH m →L[ℂ] FinH m))
    (T : FinH n →L[ℂ] FinH n) :
    kronCLM (∑ i, S i) T = ∑ i, kronCLM (S i) T := by
  simp only [kronCLM, toMat, map_sum, sum_kronecker_gen]

theorem kronCLM_sum_right {m n : ℕ} {ι : Type*} [Fintype ι] (S : FinH m →L[ℂ] FinH m)
    (T : ι → (FinH n →L[ℂ] FinH n)) :
    kronCLM S (∑ i, T i) = ∑ i, kronCLM S (T i) := by
  simp only [kronCLM, toMat, map_sum, kronecker_sum_gen]

/-- Positivity of a product of **commuting** positive operators, used for the
commuting-operator Born probabilities. -/
theorem isPositive_mul_of_commute {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {S T : H →L[ℂ] H}
    (hS : S.IsPositive) (hT : T.IsPositive) (h : Commute S T) : (S * T).IsPositive := by
  rw [← ContinuousLinearMap.nonneg_iff_isPositive]
  exact h.mul_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive _).2 hS)
    ((ContinuousLinearMap.nonneg_iff_isPositive _).2 hT)

end

end Tsirelson
