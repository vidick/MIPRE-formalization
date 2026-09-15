/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Basic.lean
-/
/-
# POVMs, PVMs, normal states, and the statements of Section 1

Formalization target: M. de la Salle, *Orthogonalization of Positive Operator
Valued Measures*, arXiv:2103.14126v2 (`manuscript/arXiv2103.14126v2.tex`).
This file states the results of Section 1 over Mathlib's `VonNeumannAlgebra`;
every declaration is anchored to a `\label` of the paper and is reviewed
adversarially (FIDELITY.md) before any proof is attempted. Encoding decisions
E1–E8 are in PLAN.md §2; intentional deviations in DIFFERENCES.md.

Conventions: `M : VonNeumannAlgebra H` is a von Neumann algebra on the
complex Hilbert space `H` (a star-subalgebra of `H →L[ℂ] H` equal to its
double commutant). "Positive operator" is Mathlib's `IsPositive`
(self-adjoint with `⟪Tx, x⟫ ≥ 0`), "projection" is `IsStarProjection`
(self-adjoint idempotent). A POVM with output set `ι` is a family of
positive operators of `M` summing to `1`; a PVM is a POVM made of
projections. States are `ℂ`-linear functionals on `B(H)` whose defining
properties (positivity, normalization, normality) are required on `M` only,
so they are exactly the normal states of `M` (DIFFERENCES.md D1).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Normal

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A POVM in `M` with output set `ι`: a finite family of positive operators
of `M` summing to `1` ("partition of unity" / "POVM", Section 1). -/
def IsPOVM (M : VonNeumannAlgebra H) {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) : Prop :=
  (∀ i, a i ∈ M) ∧ (∀ i, (a i).IsPositive) ∧ ∑ i, a i = 1

/-- A PVM in `M`: a family of projections of `M` summing to `1` ("PVM if in
addition all the `t_i`'s are projections", Section 1; pairwise orthogonality
follows and is not part of the definition). -/
def IsPVM (M : VonNeumannAlgebra H) {ι : Type*} [Fintype ι] (p : ι → H →L[ℂ] H) : Prop :=
  (∀ i, p i ∈ M) ∧ (∀ i, IsStarProjection (p i)) ∧ ∑ i, p i = 1

/-- A normal state on the von Neumann algebra `M` (Section 2: "a linear map
`φ : M → ℂ` that is positive (`φ(x*x) ≥ 0` for every `x ∈ M`), normalized by
`φ(1) = 1` and weak-* continuous"). Weak-* continuity of a positive functional
is rendered, as in the sister project, by continuity along bounded strongly
convergent nets of elements of `M` (`CommutingRepetition.VN.TendstoStrongBdd`).
The functional is carried on all of `B(H)`; only its values on `M` are
constrained (DIFFERENCES.md D1). -/
structure NormalState (M : VonNeumannAlgebra H) where
  /-- The underlying linear functional. -/
  toLinearMap : (H →L[ℂ] H) →ₗ[ℂ] ℂ
  map_one' : toLinearMap 1 = 1
  nonneg' : ∀ x ∈ M, 0 ≤ toLinearMap (star x * x)
  normal' : ∀ {κ : Type u} (l : Filter κ) (T : κ → H →L[ℂ] H) (L : H →L[ℂ] H),
    (∀ k, T k ∈ M) → L ∈ M → CommutingRepetition.VN.TendstoStrongBdd l T L →
      Tendsto (fun k => toLinearMap (T k)) l (𝓝 (toLinearMap L))

namespace NormalState

variable {M : VonNeumannAlgebra H}

instance instCoeFun : CoeFun (NormalState M) (fun _ => (H →L[ℂ] H) → ℂ) := ⟨fun φ => φ.toLinearMap⟩

/-- The square of the seminorm `‖a‖_φ = √φ(a*a)` of Section 1 (defined there
for elements of the algebra and a normal state; a real number, `.re` is
lossless by positivity, DIFFERENCES.md D2). -/
noncomputable def normSq (φ : NormalState M) (x : H →L[ℂ] H) : ℝ :=
  (φ (star x * x)).re

end NormalState

/-- **Theorem 1.2** (`thm:orthonormalization`), the main result: a POVM `(a_i)`
in a von Neumann algebra `M` with a normal state `φ` such that
`φ(∑ a_i²) > 1 − ε` is `9ε`-close to a PVM `(p_i) ⊂ M`:
`φ(∑ |a_i − p_i|²) < 9ε`, where `|a_i − p_i|² = (a_i − p_i)*(a_i − p_i)`. -/
theorem povm_orthogonalization (M : VonNeumannAlgebra H) (φ : NormalState M)
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  sorry

/-- **Theorem 1.1** (`thm:orthonormalization_Hilbert`), the Hilbert-space form:
for a POVM `(a_i)` on `H`, a unit vector `ξ` and `ε ∈ [0,1]` with
`∑ ‖a_i ξ‖² > 1 − ε`, there is an orthogonal decomposition `H = ⊕ H_i`
(given by its projections `p_i`, `H_i = range p_i`) such that (1) with `ξ_i`
the orthogonal projection of `ξ` on `H_i`, `∑ ‖a_i ξ − ξ_i‖² < 9ε`, and
(2) every `b ∈ B(H)` commuting with each `a_i` preserves each `H_i`. -/
theorem povm_orthogonalization_hilbert {ι : Type*} [Fintype ι]
    (a : ι → H →L[ℂ] H) (ha : (∀ i, (a i).IsPositive) ∧ ∑ i, a i = 1)
    (ξ : H) (hξ : ‖ξ‖ = 1) (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (h : 1 - ε < ∑ i, ‖a i ξ‖ ^ 2) :
    ∃ p : ι → H →L[ℂ] H, (∀ i, IsStarProjection (p i)) ∧ ∑ i, p i = 1 ∧
      (∑ i, ‖a i ξ - p i ξ‖ ^ 2 < 9 * ε) ∧
      ∀ b : H →L[ℂ] H, (∀ i, Commute b (a i)) → ∀ i, ∀ v : H, p i v = v → p i (b v) = b v := by
  sorry

/-! ### Proof-side helpers for Remark 1.3

The converse bound of Remark 1.3 is the triangle inequality for the seminorm
`‖(b_i)‖_φ = √(∑ φ(b_i* b_i))` of tuples, for a functional positive on `M` only:
`p_i = a_i + (p_i − a_i)` gives `1 = ∑ φ(p_i* p_i) ≤ (√φ(∑ a_i²) + √φ(∑ |a_i − p_i|²))²`.
The helpers below (Cauchy–Schwarz in discriminant form and the squared triangle
inequality) are proof-side only; they encode no statement of the paper. -/

namespace Converse

variable {M : VonNeumannAlgebra H}

/-- Scalar multiples of elements of `M` lie in `M`. -/
theorem smul_mem_vn (M : VonNeumannAlgebra H) (c : ℂ) {z : H →L[ℂ] H} (hz : z ∈ M) :
    c • z ∈ M := by
  rw [Algebra.smul_def]
  exact mul_mem (VonNeumannAlgebra.mem_carrier.mp (M.toStarSubalgebra.algebraMap_mem c)) hz

/-- Real arithmetic behind the discriminant argument: if `0 ≤ s² A − s t B + t² D` for all
real `s, t`, with `A, D ≥ 0`, then `B ≤ 2 √A √D`. -/
theorem le_two_mul_sqrt_mul_sqrt {A B D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (h : ∀ s t : ℝ, 0 ≤ s ^ 2 * A - s * t * B + t ^ 2 * D) :
    B ≤ 2 * (Real.sqrt A * Real.sqrt D) := by
  refine not_lt.mp fun hcon => ?_
  have hB : 0 < B := lt_of_le_of_lt (by positivity) hcon
  rcases hD.lt_or_eq with hDpos | hD0
  · -- `s = 2D`, `t = B`: `0 ≤ D (4 A D − B²)`, hence `B² ≤ 4 A D = (2 √A √D)²`.
    have h1 := h (2 * D) B
    have h2 : B ^ 2 ≤ 4 * (A * D) := by nlinarith [h1, hDpos]
    have hsq : (2 * (Real.sqrt A * Real.sqrt D)) ^ 2 = 4 * (A * D) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hD]; ring
    have hc : 0 ≤ 2 * (Real.sqrt A * Real.sqrt D) := by positivity
    nlinarith [mul_pos (sub_pos.mpr hcon) (sub_pos.mpr hcon),
      mul_nonneg (sub_pos.mpr hcon).le hc, hsq, h2]
  · -- `D = 0`, `s = B`, `t = A + 1`: `0 ≤ −B²`.
    subst hD0
    have h1 := h B (A + 1)
    nlinarith [h1, mul_pos hB hB]

/-- **Cauchy–Schwarz (real form)** for a functional positive on `M`: for `x, y ∈ M`,
`Re φ(x* y) + Re φ(y* x) ≤ 2 ‖x‖_φ ‖y‖_φ`. -/
theorem re_add_re_le_of_mem {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x))
    {x y : H →L[ℂ] H} (hx : x ∈ M) (hy : y ∈ M) :
    (φ (star x * y)).re + (φ (star y * x)).re
      ≤ 2 * (Real.sqrt (φ (star x * x)).re * Real.sqrt (φ (star y * y)).re) := by
  refine le_two_mul_sqrt_mul_sqrt (Complex.nonneg_iff.mp (hφ x hx)).1
    (Complex.nonneg_iff.mp (hφ y hy)).1 fun s t => ?_
  have hz : (s : ℂ) • x - (t : ℂ) • y ∈ M :=
    sub_mem (smul_mem_vn M _ hx) (smul_mem_vn M _ hy)
  -- expand `0 ≤ φ((s x − t y)* (s x − t y))` and take real parts
  have h0 := (Complex.nonneg_iff.mp (hφ _ hz)).1
  rw [star_sub, star_smul, star_smul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_ofReal] at h0
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, map_sub,
    map_smul, smul_eq_mul, Complex.sub_re, mul_assoc, Complex.re_ofReal_mul] at h0
  nlinarith [h0]

/-- Expansion of `Re φ((x + y)* (x + y))`. -/
theorem re_map_star_add_mul_add {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (x y : H →L[ℂ] H) :
    (φ (star (x + y) * (x + y))).re
      = (φ (star x * x)).re + (φ (star x * y)).re + (φ (star y * x)).re
        + (φ (star y * y)).re := by
  have hstar : star (x + y) * (x + y)
      = star x * x + star x * y + star y * x + star y * y := by
    rw [star_add]
    noncomm_ring
  rw [hstar, map_add, map_add, map_add]
  simp

/-- **Triangle inequality (squared form)** for the seminorm of tuples, for a functional
positive on `M` only: if all `b_i, c_i ∈ M`, then
`∑ ‖b_i + c_i‖_φ² ≤ (√(∑ ‖b_i‖_φ²) + √(∑ ‖c_i‖_φ²))²`. -/
theorem sum_re_add_le {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x))
    {ι : Type*} [Fintype ι] (b c : ι → H →L[ℂ] H) (hb : ∀ i, b i ∈ M) (hc : ∀ i, c i ∈ M) :
    ∑ i, (φ (star (b i + c i) * (b i + c i))).re
      ≤ (Real.sqrt (∑ i, (φ (star (b i) * b i)).re)
          + Real.sqrt (∑ i, (φ (star (c i) * c i)).re)) ^ 2 := by
  have hFnn : ∀ i, 0 ≤ (φ (star (b i) * b i)).re := fun i =>
    (Complex.nonneg_iff.mp (hφ _ (hb i))).1
  have hGnn : ∀ i, 0 ≤ (φ (star (c i) * c i)).re := fun i =>
    (Complex.nonneg_iff.mp (hφ _ (hc i))).1
  -- Step 1: coordinatewise bound.
  have step1 : ∀ i ∈ (Finset.univ : Finset ι),
      (φ (star (b i + c i) * (b i + c i))).re
        ≤ (φ (star (b i) * b i)).re
          + 2 * (Real.sqrt ((φ (star (b i) * b i)).re) * Real.sqrt ((φ (star (c i) * c i)).re))
          + (φ (star (c i) * c i)).re := by
    intro i _
    rw [re_map_star_add_mul_add (φ := φ) (b i) (c i)]
    have := re_add_re_le_of_mem hφ (hb i) (hc i)
    linarith
  -- Step 2: sum the coordinatewise bounds.
  have step2 : ∑ i, (φ (star (b i + c i) * (b i + c i))).re
      ≤ ∑ i, (φ (star (b i) * b i)).re
        + 2 * (∑ i, Real.sqrt ((φ (star (b i) * b i)).re)
                      * Real.sqrt ((φ (star (c i) * c i)).re))
        + ∑ i, (φ (star (c i) * c i)).re := by
    calc ∑ i, (φ (star (b i + c i) * (b i + c i))).re
        ≤ ∑ i, ((φ (star (b i) * b i)).re
            + 2 * (Real.sqrt ((φ (star (b i) * b i)).re)
                    * Real.sqrt ((φ (star (c i) * c i)).re))
            + (φ (star (c i) * c i)).re) := Finset.sum_le_sum step1
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Step 3: discrete Cauchy–Schwarz on the cross term.
  have step3 : (∑ i, Real.sqrt ((φ (star (b i) * b i)).re)
                        * Real.sqrt ((φ (star (c i) * c i)).re))
      ≤ Real.sqrt (∑ i, (φ (star (b i) * b i)).re)
          * Real.sqrt (∑ i, (φ (star (c i) * c i)).re) :=
    Real.sum_sqrt_mul_sqrt_le Finset.univ hFnn hGnn
  have hBn : 0 ≤ ∑ i, (φ (star (b i) * b i)).re := Finset.sum_nonneg fun i _ => hFnn i
  have hCn : 0 ≤ ∑ i, (φ (star (c i) * c i)).re := Finset.sum_nonneg fun i _ => hGnn i
  nlinarith [step2, step3, Real.sq_sqrt hBn, Real.sq_sqrt hCn]

/-- Real arithmetic of Remark 1.3: from `1 ≤ (√A + √D)²` with `0 ≤ A`, `0 ≤ D ≤ δ`,
conclude `1 − 2 √δ ≤ A` (via `√A ≥ 1 − √δ`, then squaring when `1 − √δ ≥ 0`). -/
theorem one_sub_two_sqrt_le {A D δ : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hDδ : D ≤ δ)
    (h : 1 ≤ (Real.sqrt A + Real.sqrt D) ^ 2) : 1 - 2 * Real.sqrt δ ≤ A := by
  have hδ : 0 ≤ δ := hD.trans hDδ
  have hsD : Real.sqrt D ≤ Real.sqrt δ := Real.sqrt_le_sqrt hDδ
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hsδ : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  -- `1 ≤ √A + √D ≤ √A + √δ`
  have hsum : 1 ≤ Real.sqrt A + Real.sqrt D := by
    have h1 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_one, Real.sqrt_sq (by positivity)] at h1
  rcases le_or_gt (1 - Real.sqrt δ) 0 with h0 | h0
  · -- `1 − 2√δ ≤ 1 − √δ ≤ 0 ≤ A`
    linarith
  · -- `0 < 1 − √δ ≤ √A`, so `(1 − √δ)² ≤ (√A)² = A`
    have h2 : (1 - Real.sqrt δ) * (1 - Real.sqrt δ) ≤ Real.sqrt A * Real.sqrt A :=
      mul_le_mul (by linarith) (by linarith) h0.le hsA
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hδ, h2]

end Converse

/-- **Remark 1.3**, first display, second inequality (`rem:9epsilon_optimal`):
conversely, if a PVM `(p_i)` satisfies `∑ φ(|a_i − p_i|²) ≤ δ` then
`φ(∑ a_i²) ≥ 1 − 2√δ` (the display's sharper intermediate bound
`(1 − √φ(∑|a_i − p_i|²))²` is not stated; the `ℓ∞²` example of the remark is
not formalized). -/
theorem povm_sq_ge_of_close_pvm (M : VonNeumannAlgebra H) (φ : NormalState M)
    {ι : Type*} [Fintype ι] (a p : ι → H →L[ℂ] H) (ha : IsPOVM M a) (hp : IsPVM M p)
    (δ : ℝ) (hδ : (φ (∑ i, star (a i - p i) * (a i - p i))).re ≤ δ) :
    1 - 2 * Real.sqrt δ ≤ (φ (∑ i, a i * a i)).re := by
  have hφ : ∀ x ∈ M, 0 ≤ φ.toLinearMap (star x * x) := φ.nonneg'
  have haM : ∀ i, a i ∈ M := ha.1
  have hpM : ∀ i, p i ∈ M := hp.1
  have hsa : ∀ i, star (a i) = a i := fun i => (ha.2.1 i).isSelfAdjoint.star_eq
  -- the squared triangle inequality with `b_i = a_i`, `c_i = p_i − a_i`, so `b_i + c_i = p_i`
  have htri := Converse.sum_re_add_le hφ a (fun i => p i - a i) haM
    (fun i => sub_mem (hpM i) (haM i))
  simp only [add_sub_cancel] at htri
  -- `∑ φ(p_i* p_i) = φ(∑ p_i) = φ(1) = 1`
  have hP : ∑ i, (φ.toLinearMap (star (p i) * p i)).re = 1 := by
    have hpp : ∀ i, star (p i) * p i = p i := fun i => by
      rw [(hp.2.1 i).isSelfAdjoint.star_eq, (hp.2.1 i).isIdempotentElem.eq]
    simp only [hpp]
    rw [← Complex.re_sum, ← map_sum, hp.2.2, φ.map_one', Complex.one_re]
  -- `∑ φ(a_i* a_i) = φ(∑ a_i²)`
  have hA : ∑ i, (φ.toLinearMap (star (a i) * a i)).re = (φ (∑ i, a i * a i)).re := by
    simp only [hsa]
    rw [map_sum, Complex.re_sum]
  -- `∑ φ(|p_i − a_i|²) = φ(∑ |a_i − p_i|²)`
  have hD : ∑ i, (φ.toLinearMap (star (p i - a i) * (p i - a i))).re
      = (φ (∑ i, star (a i - p i) * (a i - p i))).re := by
    rw [map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← neg_sub (a i) (p i), star_neg, neg_mul_neg]
  have hAnn : 0 ≤ (φ (∑ i, a i * a i)).re := by
    rw [← hA]
    exact Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.mp (hφ _ (haM i))).1
  have hDnn : 0 ≤ (φ (∑ i, star (a i - p i) * (a i - p i))).re := by
    rw [← hD]
    exact Finset.sum_nonneg fun i _ =>
      (Complex.nonneg_iff.mp (hφ _ (sub_mem (hpM i) (haM i)))).1
  rw [hA, hP, hD] at htri
  exact Converse.one_sub_two_sqrt_le hAnn hDnn hδ htri

/-- **Theorem 1.4** (`thm:pvm_almost_commute`): almost commuting PVMs are close
to commuting PVMs. If `(p_i)`, `(q_j)` are PVMs in `M` with
`∑_{i,j} ‖p_i q_j − q_j p_i‖_φ² < ε`, there is a PVM `(p'_i)` in `M` with
`[p'_i, q_j] = 0` for all `i, j` and `∑_i ‖p_i − p'_i‖_φ² < 10ε`. -/
theorem pvm_almost_commute (M : VonNeumannAlgebra H) (φ : NormalState M)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → H →L[ℂ] H) (q : κ → H →L[ℂ] H)
    (hp : IsPVM M p) (hq : IsPVM M q) (ε : ℝ)
    (h : ∑ i, ∑ j, φ.normSq (p i * q j - q j * p i) < ε) :
    ∃ p' : ι → H →L[ℂ] H, IsPVM M p' ∧ (∀ i j, Commute (p' i) (q j)) ∧
      ∑ i, φ.normSq (p i - p' i) < 10 * ε := by
  sorry

/-- **Corollary 1.5** (`cor:almost_commuting`): for unitaries `u, v ∈ M` of
finite orders `n, m` with `(nm)⁻¹ ∑_{i=1}^{n} ∑_{j=1}^{m} ‖u^i v^j − v^j u^i‖_φ² < ε`,
there is a unitary `v' ∈ M` commuting with `u` such that
`m⁻¹ ∑_{j=1}^{m} ‖v^j − v'^j‖_φ² < 10ε`. (The paper's display normalizes the
conclusion by `n` while summing powers of `v`; the average over the `m`
powers of the approximated unitary `v` is what Theorem 1.4 and the Fourier
dictionary of the paper yield — DIFFERENCES.md D5.) -/
theorem almost_commuting_unitaries (M : VonNeumannAlgebra H) (φ : NormalState M)
    (u v : H →L[ℂ] H) (hu : u ∈ M) (hv : v ∈ M)
    (hu' : u ∈ unitary (H →L[ℂ] H)) (hv' : v ∈ unitary (H →L[ℂ] H))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hun : u ^ n = 1) (hvm : v ^ m = 1) (ε : ℝ)
    (h : ((n : ℝ) * m)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        φ.normSq (u ^ (i + 1) * v ^ (j + 1) - v ^ (j + 1) * u ^ (i + 1)) < ε) :
    ∃ v' : H →L[ℂ] H, v' ∈ M ∧ v' ∈ unitary (H →L[ℂ] H) ∧ Commute u v' ∧
      (m : ℝ)⁻¹ * ∑ j ∈ Finset.range m, φ.normSq (v ^ (j + 1) - v' ^ (j + 1)) < 10 * ε := by
  sorry

end Orthogonalization
