/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Defs
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.WOTCompact
public import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM

@[expose] public section

/-!
# The centre-valued expectation of a von Neumann algebra with a vector trace

The vendored orthonormalization theorem (de la Salle's Theorem 1.2,
`MIPRE/Background/Orthonormalization/Orthogonalization/`) is unconditional for II₁ factors only:
its finite case needs a centre-valued trace with comparison (`IsCenterValuedTrace`, field H3 of the
structure-theory interface), and for a factor that trace is the scalar `x ↦ τ(x) • 1`
(`MvN/II1Factor.lean`). The II₁ tier of C6b (`planning/mipco-track.md`, Phase 6) needs it for the
algebras of a finite pair, which are not factors. This file constructs the centre-valued
expectation `E` of a von Neumann algebra `M` with a faithful tracial vector functional
`τ(a) = ∑ₖ ⟪gₖ, a gₖ⟫` of finitely many vectors, with no factor, type or separability hypothesis,
from which `MIPRE/Background/Orthonormalization/CenterTraceClauses.lean` derives every clause of
`IsCenterValuedTrace M 1 E` except the two comparison clauses, which are
`MIPRE/Background/Orthonormalization/CenterComparison.lean`.

* **Construction.** For `x ∈ M`, `E x` is the point of minimal 2-norm `∑ₖ ‖y gₖ‖²` of the set of
  `y ∈ M` with `‖y‖ ≤ ‖x‖` and the same pairings `τ(y c) = τ(x c)` with the central elements `c`.
  That set is compact and convex in the weak operator topology, the 2-norm is lower
  semicontinuous there (`lowerSemicontinuous_sum_norm_sq`), and the minimizer is unique by the
  parallelogram law and faithfulness. Conjugation by a unitary of `M` preserves the set and, by
  traciality, the 2-norm, so it fixes the minimizer, which therefore commutes with every unitary
  of `M`, hence with `M` (`commute_of_forall_unitary`): it is central
  (`exists_isCentralIn_mem_of_conj_invariant`). The central element with given pairings is
  unique (`eq_of_isCentralIn_of_pairing`), which gives linearity; `E` is extended to `B(H)`
  arbitrarily, since only its values on `M` are constrained.
* **Positivity.** The same minimization inside the positive cone, which is closed, convex and
  invariant under unitary conjugation, gives a positive central element with the pairings of a
  positive `x`, which is `E x` by uniqueness.

No bicommutant theorem is used: `M` is a Mathlib `VonNeumannAlgebra`, which carries `M″ = M` as a
field, and every closedness statement is the vendored weak-operator toolkit (`MvN/WOTCompact.lean`).
The mathematics is `reports/c6b-paper-proofs.md`, section "The centre-valued trace", Lemmas 1–16.
-/

namespace MIPRE.Orthonormalization

open scoped ComplexOrder InnerProductSpace
open Filter Orthogonalization.MvN

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The vector functional** `τ(a) = ∑ₖ ⟪gₖ, a gₖ⟫` of finitely many vectors, on all of `B(H)`. -/
noncomputable def vecFunctional {d : ℕ} (g : Fin d → H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun a := ∑ k, ⟪g k, a (g k)⟫_ℂ
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum]

omit [CompleteSpace H] in
theorem vecFunctional_apply {d : ℕ} (g : Fin d → H) (a : H →L[ℂ] H) :
    vecFunctional g a = ∑ k, ⟪g k, a (g k)⟫_ℂ := rfl

/-- **A centre-valued expectation** of `M` for the vector functional of `g`: a linear map on
`B(H)` which on `M` takes values in the centre, preserves the pairings `x ↦ τ(x c)` with the
central elements `c`, is contractive and is positive. Only its values on `M` are constrained. -/
structure IsCenterExpectation (M : VonNeumannAlgebra H) {d : ℕ} (g : Fin d → H)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) : Prop where
  /-- Values in the centre. -/
  mem_center : ∀ x ∈ M, IsCentralIn M 1 (E x)
  /-- The pairings with the centre are preserved. -/
  pairing : ∀ x ∈ M, ∀ c, IsCentralIn M 1 c →
    vecFunctional g (E x * c) = vecFunctional g (x * c)
  /-- Contractivity. -/
  norm_le : ∀ x ∈ M, ‖E x‖ ≤ ‖x‖
  /-- Positivity. -/
  nonneg : ∀ x ∈ M, 0 ≤ x → 0 ≤ E x

variable {M : VonNeumannAlgebra H} {d : ℕ} {g : Fin d → H}

/-! ### The centre and the 2-norm -/

/-- At the projection `1`, `IsCentralIn` says that `c` is an element of `M` commuting with `M`. -/
theorem isCentralIn_one_iff {c : H →L[ℂ] H} :
    IsCentralIn M 1 c ↔ c ∈ M ∧ ∀ y ∈ M, Commute c y :=
  ⟨fun h => ⟨h.1, fun y hy => h.2.2 y hy (by rw [one_mul, mul_one])⟩,
    fun h => ⟨h.1, by rw [one_mul, mul_one], fun y hy _ => h.2 y hy⟩⟩

/-- `1` is central. -/
theorem isCentralIn_one_one : IsCentralIn M 1 1 :=
  isCentralIn_one_iff.mpr ⟨one_mem M, fun y _ => Commute.one_left y⟩

/-- The centre is closed under addition. -/
theorem isCentralIn_one_add {c c' : H →L[ℂ] H} (hc : IsCentralIn M 1 c)
    (hc' : IsCentralIn M 1 c') : IsCentralIn M 1 (c + c') := by
  rw [isCentralIn_one_iff] at *
  exact ⟨add_mem hc.1 hc'.1, fun y hy => (hc.2 y hy).add_left (hc'.2 y hy)⟩

/-- The centre is closed under multiplication. -/
theorem isCentralIn_one_mul {c c' : H →L[ℂ] H} (hc : IsCentralIn M 1 c)
    (hc' : IsCentralIn M 1 c') : IsCentralIn M 1 (c * c') := by
  rw [isCentralIn_one_iff] at *
  exact ⟨mul_mem hc.1 hc'.1, fun y hy => (hc.2 y hy).mul_left (hc'.2 y hy)⟩

/-- The centre is closed under the adjoint, since `M` is. -/
theorem isCentralIn_one_star {c : H →L[ℂ] H} (hc : IsCentralIn M 1 c) :
    IsCentralIn M 1 (star c) := by
  rw [isCentralIn_one_iff] at *
  refine ⟨star_mem hc.1, fun y hy => ?_⟩
  simpa only [star_star] using (hc.2 (star y) (star_mem hy)).star_star

-- The next two are the `p = 1` cases of the vendored `IsCentralIn.sub` and `IsCentralIn.smul`
-- (`MvN/Perturb.lean`), restated here to keep that module out of this file's imports.

/-- The centre is closed under subtraction. -/
private theorem isCentralIn_one_sub {c c' : H →L[ℂ] H} (hc : IsCentralIn M 1 c)
    (hc' : IsCentralIn M 1 c') : IsCentralIn M 1 (c - c') := by
  rw [isCentralIn_one_iff] at *
  exact ⟨sub_mem hc.1 hc'.1, fun y hy => (hc.2 y hy).sub_left (hc'.2 y hy)⟩

/-- The centre is closed under scalar multiplication. -/
private theorem isCentralIn_one_smul {c : H →L[ℂ] H} (hc : IsCentralIn M 1 c) (a : ℂ) :
    IsCentralIn M 1 (a • c) := by
  rw [isCentralIn_one_iff] at *
  exact ⟨Orthogonalization.Blocks.smul_mem_vn M a hc.1, fun y hy => (hc.2 y hy).smul_left a⟩

/-- `τ(y* y)` is the 2-norm `∑ₖ ‖y gₖ‖²`. -/
theorem vecFunctional_star_mul_self (y : H →L[ℂ] H) :
    vecFunctional g (star y * y) = ((∑ k, ‖y (g k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [vecFunctional_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The vector functional is positive. -/
theorem vecFunctional_star_mul_self_nonneg (y : H →L[ℂ] H) :
    0 ≤ vecFunctional g (star y * y) := by
  rw [vecFunctional_star_mul_self]
  exact Complex.zero_le_real.mpr (Finset.sum_nonneg fun k _ => sq_nonneg _)

/-- The 2-norm is faithful on `M`: an element of `M` of 2-norm `0` vanishes at every `gₖ`. -/
theorem eq_zero_of_sum_norm_sq_eq_zero (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0)
    {y : H →L[ℂ] H} (hy : y ∈ M) (h : ∑ k, ‖y (g k)‖ ^ 2 = 0) : y = 0 :=
  hsep y hy fun k => by
    have hk := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by positivity).mp h k
      (Finset.mem_univ k)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hk)

/-- The vector functional of a family separating `M` is faithful on `M`. -/
theorem eq_zero_of_vecFunctional_star_mul_self_eq_zero
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) {y : H →L[ℂ] H} (hy : y ∈ M)
    (h : vecFunctional g (star y * y) = 0) : y = 0 := by
  rw [vecFunctional_star_mul_self, Complex.ofReal_eq_zero] at h
  exact eq_zero_of_sum_norm_sq_eq_zero hsep hy h

/-- **A central element is determined by its pairings with the centre**, for a faithful vector
functional: `τ((z - z') (z - z')*) = 0` forces `z = z'`. -/
theorem eq_of_isCentralIn_of_pairing (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0)
    {z z' : H →L[ℂ] H} (hz : IsCentralIn M 1 z) (hz' : IsCentralIn M 1 z')
    (h : ∀ c, IsCentralIn M 1 c → vecFunctional g (z * c) = vecFunctional g (z' * c)) :
    z = z' := by
  -- pair `z - z'` with the central element `(z - z')*`
  have hw : IsCentralIn M 1 (star (z - z')) := isCentralIn_one_star (isCentralIn_one_sub hz hz')
  rw [← sub_eq_zero, ← star_eq_zero]
  refine eq_zero_of_vecFunctional_star_mul_self_eq_zero hsep hw.1 ?_
  rw [star_star, sub_mul, map_sub, h _ hw, sub_self]

omit [CompleteSpace H] in
/-- **The parallelogram law for the 2-norm**, at the midpoint of `y` and `y'`. -/
private theorem sum_norm_sq_midpoint (y y' : H →L[ℂ] H) :
    ∑ k, ‖((2⁻¹ : ℝ) • (y + y')) (g k)‖ ^ 2 = 2⁻¹ * ∑ k, ‖y (g k)‖ ^ 2 +
      2⁻¹ * ∑ k, ‖y' (g k)‖ ^ 2 - 4⁻¹ * ∑ k, ‖(y - y') (g k)‖ ^ 2 := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, add_apply, sub_apply, norm_smul, mul_pow,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  linear_combination (4⁻¹ : ℝ) * parallelogram_law_with_norm ℂ (y (g k)) (y' (g k))

/-- **Conjugation by a unitary of `M` preserves the pairings with the centre**, by traciality:
`τ(u y u* c) = τ((y u* c) u) = τ(y u* u c) = τ(y c)`. -/
private theorem vecFunctional_conj_mul
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    {u y c : H →L[ℂ] H} (hu : u ∈ unitary (H →L[ℂ] H)) (huM : u ∈ M) (hy : y ∈ M)
    (hc : IsCentralIn M 1 c) :
    vecFunctional g (u * y * star u * c) = vecFunctional g (y * c) := by
  have hc' := isCentralIn_one_iff.mp hc
  calc vecFunctional g (u * y * star u * c) = vecFunctional g (u * (y * star u * c)) := by
        simp only [mul_assoc]
    _ = vecFunctional g (y * star u * c * u) :=
        htr _ huM _ (mul_mem (mul_mem hy (star_mem huM)) hc'.1)
    _ = vecFunctional g (y * (star u * u) * c) := by
        rw [mul_assoc _ c, (hc'.2 u huM).eq]
        simp only [mul_assoc]
    _ = vecFunctional g (y * c) := by rw [Unitary.star_mul_self_of_mem hu, mul_one]

/-- **Conjugation by a unitary of `M` preserves the 2-norm on `M`**, by traciality:
`τ((u y u*)* (u y u*)) = τ(u (y* y) u*) = τ(y* y)`. -/
private theorem sum_norm_sq_conj
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    {u y : H →L[ℂ] H} (hu : u ∈ unitary (H →L[ℂ] H)) (huM : u ∈ M) (hy : y ∈ M) :
    ∑ k, ‖(u * y * star u) (g k)‖ ^ 2 = ∑ k, ‖y (g k)‖ ^ 2 := by
  have h := vecFunctional_conj_mul htr hu huM (mul_mem (star_mem hy) hy) isCentralIn_one_one
  have e : u * (star y * y) * star u * 1 = star (u * y * star u) * (u * y * star u) := by
    simp only [star_mul, star_star, mul_one, mul_assoc]
    rw [← mul_assoc (star u) u, Unitary.star_mul_self_of_mem hu, one_mul]
  rw [e, mul_one, vecFunctional_star_mul_self, vecFunctional_star_mul_self] at h
  exact_mod_cast h

/-! ### Lower semicontinuity of the 2-norm -/

/-- **The 2-norm `∑ₖ ‖A gₖ‖²` is lower semicontinuous in the weak operator topology**: at each `A`
it is touched from below by the continuous `A' ↦ ∑ₖ (2 Re ⟪A gₖ, A' gₖ⟫ - ‖A gₖ‖²)`, a minorant
since `‖A' gₖ - A gₖ‖² ≥ 0`. -/
theorem lowerSemicontinuous_sum_norm_sq (g : Fin d → H) :
    LowerSemicontinuous fun A : H →WOT[ℂ] H => ∑ k, ‖A (g k)‖ ^ 2 := by
  intro A y hy
  let φ : (H →WOT[ℂ] H) → ℝ := fun A' =>
    ∑ k, (2 * RCLike.re ⟪A (g k), A' (g k)⟫_ℂ - ‖A (g k)‖ ^ 2)
  have hφc : Continuous φ := continuous_finsetSum _ fun k _ =>
    (continuous_const.mul (RCLike.continuous_re.comp (continuous_inner_apply _ _))).sub
      continuous_const
  have hφA : y < φ A := by
    refine hy.trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [inner_self_eq_norm_sq]
    ring
  have hφle : ∀ A', φ A' ≤ ∑ k, ‖A' (g k)‖ ^ 2 := fun A' => Finset.sum_le_sum fun k _ => by
    have := norm_sub_sq (𝕜 := ℂ) (A (g k)) (A' (g k))
    nlinarith [sq_nonneg ‖A (g k) - A' (g k)‖]
  filter_upwards [hφc.continuousAt.eventually (lt_mem_nhds hφA)] with A' hA'
  exact hA'.trans_le (hφle A')

/-! ### Commuting with the unitaries of `M` -/

open scoped ComplexStarModule in
/-- A self-adjoint contraction `a` of `M` is the real part of the unitary `a + i √(1 - a²)` of `M`
(Mathlib's `selfAdjoint.unitarySelfAddISMul`), so an operator commuting with the unitaries of `M`
commutes with `a`. The positivity of `1 - a²`, which puts `√(1 - a²)` in `M`, is the inline
argument of Mathlib's `IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary`. -/
private theorem commute_of_forall_unitary_of_norm_le_one {z : H →L[ℂ] H}
    (hz : ∀ u ∈ unitary (H →L[ℂ] H), u ∈ M → Commute z u) {a : H →L[ℂ] H} (haM : a ∈ M)
    (ha : IsSelfAdjoint a) (hna : ‖a‖ ≤ 1) : Commute z a := by
  have h0 : 0 ≤ 1 - a ^ 2 := by
    rwa [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2), sq, ha.norm_mul_self,
      sq_le_one_iff₀ (by positivity)]
  have hsM : Complex.I • CFC.sqrt (1 - a ^ 2) ∈ M := Orthogonalization.Blocks.smul_mem_vn M _
    (Orthogonalization.Blocks.sqrt_mem M (sub_mem (one_mem M) (pow_mem haM 2)) h0)
  -- the unitary `u = a + i √(1 - a²)`, with `u* = a - i √(1 - a²)` and `ℜ u = a`
  let a' : selfAdjoint (H →L[ℂ] H) := ⟨a, selfAdjoint.mem_iff.mpr ha.star_eq⟩
  have hna' : ‖a'‖ ≤ 1 := hna
  let u := selfAdjoint.unitarySelfAddISMul a' hna'
  have hu : star (u : H →L[ℂ] H) = a - Complex.I • CFC.sqrt (1 - a ^ 2) :=
    selfAdjoint.star_coe_unitarySelfAddISMul a' hna'
  have h1 := hz u u.2 (add_mem haM hsM)
  have h2 := hz _ (Unitary.star_mem u.2) (hu ▸ sub_mem haM hsM)
  have h3 : (2⁻¹ : ℝ) • ((u : H →L[ℂ] H) + star (u : H →L[ℂ] H)) = a :=
    (realPart_apply_coe _).symm.trans
      (congrArg Subtype.val (selfAdjoint.realPart_unitarySelfAddISMul a' hna'))
  rw [← h3]
  exact (h1.add_right h2).smul_right _

open scoped ComplexStarModule in
/-- **An operator commuting with every unitary of `M` commutes with `M`**: a self-adjoint element
of `M` is a multiple of a self-adjoint contraction, which is the real part of a unitary of `M`,
and every element of `M` is `ℜ x + i ℑ x`. -/
theorem commute_of_forall_unitary {z : H →L[ℂ] H}
    (hz : ∀ u ∈ unitary (H →L[ℂ] H), u ∈ M → Commute z u) {x : H →L[ℂ] H} (hx : x ∈ M) :
    Commute z x := by
  -- self-adjoint elements, rescaled to norm `1`
  have hsa : ∀ a ∈ M, IsSelfAdjoint a → Commute z a := by
    intro a haM ha
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Commute.zero_right z
    have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hb := commute_of_forall_unitary_of_norm_le_one hz
      (Orthogonalization.Blocks.smul_mem_vn M ((‖a‖⁻¹ : ℝ) : ℂ) haM)
      (IsSelfAdjoint.smul (Complex.conj_ofReal _) ha)
      (by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hpos.ne'])
    have e : a = ((‖a‖ : ℝ) : ℂ) • (((‖a‖⁻¹ : ℝ) : ℂ) • a) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]
    rw [e]
    exact hb.smul_right _
  -- the real and imaginary parts
  have hre : ((ℜ x : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) ∈ M := by
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact Orthogonalization.Blocks.smul_mem_vn M _ (add_mem hx (star_mem hx))
  have him : ((ℑ x : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) ∈ M := by
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact Orthogonalization.Blocks.smul_mem_vn M _
      (Orthogonalization.Blocks.smul_mem_vn M _ (sub_mem hx (star_mem hx)))
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact (hsa _ hre (ℜ x).prop).add_right ((hsa _ him (ℑ x).prop).smul_right _)

/-! ### The central point of minimal 2-norm -/

section CentralPoint

open ContinuousLinearMapWOT

/-- The pairing `A ↦ τ(A c)` with a fixed operator is continuous in the weak operator topology: it
is a finite sum of matrix coefficients `⟪gₖ, A (c gₖ)⟫`. -/
theorem continuous_vecFunctional_mul (g : Fin d → H) (c : H →L[ℂ] H) :
    Continuous fun A : H →WOT[ℂ] H => vecFunctional g (toCLM A * c) := by
  simp only [vecFunctional_apply, mul_apply_eq_comp, toCLM_apply]
  exact continuous_finsetSum _ fun k _ => continuous_inner_apply _ _

/-- **A central point of minimal 2-norm**: for `x ∈ M` and a set `D ∋ x` of operators that is
closed in the weak operator topology, closed under midpoints and invariant under conjugation of
its elements of `M` by the unitaries of `M`, some central `z ∈ D` has `‖z‖ ≤ ‖x‖` and the pairings
`τ(z c) = τ(x c)` with the centre. It is the minimizer of the 2-norm over the weak-operator
compact set `C` of the `y ∈ M ∩ D` with `‖y‖ ≤ ‖x‖` and the pairings of `x`: the minimizer is
unique by the parallelogram law, and conjugation by a unitary `u` of `M` preserves `C` and the
2-norm, so it fixes the minimizer, which therefore commutes with `u`. -/
theorem exists_isCentralIn_mem_of_conj_invariant
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) {x : H →L[ℂ] H} (hx : x ∈ M)
    {D : Set (H →L[ℂ] H)} (hxD : x ∈ D) (hDc : IsClosed {A : H →WOT[ℂ] H | toCLM A ∈ D})
    (hDm : ∀ a ∈ D, ∀ b ∈ D, (2⁻¹ : ℝ) • (a + b) ∈ D)
    (hDu : ∀ y ∈ D, y ∈ M → ∀ u ∈ unitary (H →L[ℂ] H), u ∈ M → u * y * star u ∈ D) :
    ∃ z ∈ D, IsCentralIn M 1 z ∧ ‖z‖ ≤ ‖x‖ ∧
      ∀ c, IsCentralIn M 1 c → vecFunctional g (z * c) = vecFunctional g (x * c) := by
  -- the constraint set, closed and bounded, hence compact, in the weak operator topology
  set P : (H →L[ℂ] H) → Prop := fun y => y ∈ M ∧ y ∈ D ∧ ‖y‖ ≤ ‖x‖ ∧
    ∀ c, IsCentralIn M 1 c → vecFunctional g (y * c) = vecFunctional g (x * c)
  set C : Set (H →WOT[ℂ] H) := {A | P (toCLM A)}
  have hCc : IsClosed C := by
    have h4 : IsClosed {A : H →WOT[ℂ] H |
        ∀ c, IsCentralIn M 1 c → vecFunctional g (toCLM A * c) = vecFunctional g (x * c)} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun c => isClosed_iInter fun _ =>
        isClosed_eq (continuous_vecFunctional_mul g c) continuous_const
    exact (isClosed_setOf_mem M).inter (hDc.inter ((isCompact_setOf_norm_le _).isClosed.inter h4))
  have hxC : ofCLM x ∈ C := ⟨hx, hxD, le_rfl, fun c _ => rfl⟩
  -- a minimizer `y₀` of the 2-norm on `C`
  obtain ⟨A₀, hA₀, hmin⟩ := ((lowerSemicontinuous_sum_norm_sq g).lowerSemicontinuousOn C)
    |>.exists_isMinOn ⟨_, hxC⟩ (isCompact_of_isClosed_of_norm_le hCc fun A hA => hA.2.2.1)
  set y₀ := toCLM A₀
  have hmin' : ∀ y, P y → ∑ k, ‖y₀ (g k)‖ ^ 2 ≤ ∑ k, ‖y (g k)‖ ^ 2 := fun y hy =>
    isMinOn_iff.mp hmin (ofCLM y) hy
  -- it is the only point of `C` of 2-norm at most its own: the midpoint is in `C`
  have huniq : ∀ y, P y → ∑ k, ‖y (g k)‖ ^ 2 ≤ ∑ k, ‖y₀ (g k)‖ ^ 2 → y = y₀ := by
    intro y hy hle
    have hm : P ((2⁻¹ : ℝ) • (y + y₀)) := by
      refine ⟨?_, hDm _ hy.2.1 _ hA₀.2.1, ?_, fun c hc => ?_⟩
      · rw [← Complex.coe_smul]
        exact Orthogonalization.Blocks.smul_mem_vn M _ (add_mem hy.1 hA₀.1)
      · calc ‖(2⁻¹ : ℝ) • (y + y₀)‖ ≤ 2⁻¹ * (‖y‖ + ‖y₀‖) := by
              rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
              gcongr
              exact norm_add_le _ _
          _ ≤ ‖x‖ := by linarith [hy.2.2.1, hA₀.2.2.1]
      · rw [smul_mul_assoc, LinearMap.map_smul_of_tower, add_mul, map_add, hy.2.2.2 c hc,
          hA₀.2.2.2 c hc, ← two_smul ℝ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    have h1 := hmin' _ hm
    rw [sum_norm_sq_midpoint] at h1
    have h2 : ∑ k, ‖(y - y₀) (g k)‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun k _ => by positivity)
    exact sub_eq_zero.mp (eq_zero_of_sum_norm_sq_eq_zero hsep (sub_mem hy.1 hA₀.1) h2)
  -- so it is fixed by the conjugations by the unitaries of `M`, and commutes with them
  have hcomm : ∀ u ∈ unitary (H →L[ℂ] H), u ∈ M → Commute y₀ u := by
    intro u hu huM
    have hconj : P (u * y₀ * star u) := by
      refine ⟨mul_mem (mul_mem huM hA₀.1) (star_mem huM), hDu _ hA₀.2.1 hA₀.1 u hu huM, ?_,
        fun c hc => (vecFunctional_conj_mul htr hu huM hA₀.1 hc).trans (hA₀.2.2.2 c hc)⟩
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
        CStarRing.norm_mem_unitary_mul _ hu]
      exact hA₀.2.2.1
    have h := huniq _ hconj (sum_norm_sq_conj htr hu huM hA₀.1).le
    calc y₀ * u = u * y₀ * star u * u := by rw [h]
      _ = u * y₀ := by rw [mul_assoc, Unitary.star_mul_self_of_mem hu, mul_one]
  exact ⟨y₀, hA₀.2.1, isCentralIn_one_iff.mpr ⟨hA₀.1, fun y hy =>
    commute_of_forall_unitary hcomm hy⟩, hA₀.2.2.1, hA₀.2.2.2⟩

end CentralPoint

/-! ### The centre-valued expectation -/

/-- **Existence of the centre-valued expectation** for a von Neumann algebra whose vector
functional is tracial and faithful: the point of minimal 2-norm, among the elements of `M` of
norm at most `‖x‖` with the pairings of `x`, is central. -/
theorem exists_isCenterExpectation (M : VonNeumannAlgebra H) (g : Fin d → H)
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∃ E, IsCenterExpectation M g E := by
  -- on `M`, the central point of minimal 2-norm, with no constraint beyond the norm and pairings
  have hex : ∀ x ∈ M, ∃ z, IsCentralIn M 1 z ∧ ‖z‖ ≤ ‖x‖ ∧
      ∀ c, IsCentralIn M 1 c → vecFunctional g (z * c) = vecFunctional g (x * c) := by
    intro x hx
    obtain ⟨z, -, hz⟩ := exists_isCentralIn_mem_of_conj_invariant htr hsep hx (Set.mem_univ x)
      (by simp only [Set.mem_univ, Set.ofPred_true]; exact isClosed_univ)
      (fun _ _ _ _ => Set.mem_univ _) fun _ _ _ _ _ _ => Set.mem_univ _
    exact ⟨z, hz⟩
  -- `M` as a subspace of `B(H)`, on which the choice is linear by uniqueness
  let p : Submodule ℂ (H →L[ℂ] H) :=
    { carrier := M
      add_mem' := add_mem
      zero_mem' := zero_mem M
      smul_mem' := fun a _ hx => Orthogonalization.Blocks.smul_mem_vn M a hx }
  choose f hf using fun x : p => hex x.1 x.2
  let E₀ : p →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := f
      map_add' := fun x y => eq_of_isCentralIn_of_pairing hsep (hf (x + y)).1
        (isCentralIn_one_add (hf x).1 (hf y).1) fun c hc => by
          rw [(hf (x + y)).2.2 c hc, Submodule.coe_add, add_mul, add_mul, map_add, map_add,
            (hf x).2.2 c hc, (hf y).2.2 c hc]
      map_smul' := fun a x => eq_of_isCentralIn_of_pairing hsep (hf (a • x)).1
        (isCentralIn_one_smul (hf x).1 a) fun c hc => by
          rw [(hf (a • x)).2.2 c hc, Submodule.coe_smul, RingHom.id_apply, smul_mul_assoc,
            smul_mul_assoc, map_smul, map_smul, (hf x).2.2 c hc] }
  -- any linear extension to `B(H)`
  obtain ⟨E, hE⟩ := LinearMap.exists_extend E₀
  have hEx : ∀ x (hx : x ∈ M), E x = f ⟨x, hx⟩ := fun x hx => LinearMap.congr_fun hE ⟨x, hx⟩
  refine ⟨E, fun x hx => ?_, fun x hx c hc => ?_, fun x hx => ?_, fun x hx hx0 => ?_⟩
  · rw [hEx x hx]
    exact (hf _).1
  · rw [hEx x hx]
    exact (hf _).2.2 c hc
  · rw [hEx x hx]
    exact (hf _).2.1
  · -- the central point of the positive cone has the pairings of `x`, so it is `E x`
    obtain ⟨z, hz0, hz, -, hzc⟩ := exists_isCentralIn_mem_of_conj_invariant (D := {y | 0 ≤ y})
      htr hsep hx hx0 isClosed_setOf_nonneg
      (fun a ha b hb => show 0 ≤ (2⁻¹ : ℝ) • (a + b) from
        smul_nonneg (by norm_num) (add_nonneg ha hb))
      fun y hy _ u _ _ => star_right_conjugate_nonneg hy u
    rw [hEx x hx, ← eq_of_isCentralIn_of_pairing hsep hz (hf _).1 fun c hc =>
      (hzc c hc).trans ((hf ⟨x, hx⟩).2.2 c hc).symm]
    exact hz0

end MIPRE.Orthonormalization

end
