/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Amplify.lean
-/
/-
# Matrix amplification of a standard tracial algebra (Stage B, WP-B3)

For `d > 0` and a standard tracial algebra `M`, the matrix algebra
`M_d(M) = Matrix (Fin d) (Fin d) M.A` with the normalized trace
`τ_d(X) = d⁻¹ ∑ᵢ τ(X i i)` is again a standard tracial algebra: its
GNS space is the ℓ²-sum of `d²` copies of `L²(M)` with `ι` scaled by
`d^{-1/2}`, the left representation acts by matrix multiplication on
the row index through `M.L`, and the right representation acts on the
column index through `M.R`.

Infrastructure (no manuscript anchor of its own): this is the
amplification step used by the resolver-corner construction (nodes
1.2.5.1–1.2.5.6) — the finite corner `N` of thm common-resolver-arena
lives in a matrix amplification of `M`, and the corner-trace
normalization of `ResolverArena.Cornered` (`emb_trace`, with
`t_Q = d` for a single matrix unit) is visible here as
`τ_d(e₀₀ ⊗ m) = d⁻¹ τ(m)`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped BigOperators InnerProductSpace

universe u

variable (M : StdTracialAlgebra.{u}) (d : ℕ)

/-- The amplified GNS space: a `d × d` matrix of copies of `L²(M)`,
with the ℓ²-norm. -/
abbrev AmpH := PiLp 2 fun _ : Fin d × Fin d => M.H

@[simp] theorem AmpH.coord (w : AmpH M d) (p : Fin d × Fin d) :
    WithLp.ofLp w p = w p := rfl

/-- The normalized amplified trace `τ_d(X) = d⁻¹ ∑ᵢ τ(X i i)`. -/
noncomputable def ampτ : Matrix (Fin d) (Fin d) M.A →ₗ[ℂ] ℂ where
  toFun X := (d : ℂ)⁻¹ * ∑ i : Fin d, M.τ (X i i)
  map_add' X Y := by
    simp [Matrix.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c X := by
    simp [Matrix.smul_apply, Finset.mul_sum, smul_eq_mul]
    ring

@[simp] theorem ampτ_apply (X : Matrix (Fin d) (Fin d) M.A) :
    ampτ M d X = (d : ℂ)⁻¹ * ∑ i : Fin d, M.τ (X i i) := rfl

/-- The amplified GNS embedding, scaled by `d^{-1/2}` so that the
`ampτ`-inner-product identity holds with the unweighted ℓ²-inner
product. -/
noncomputable def ampι : Matrix (Fin d) (Fin d) M.A →ₗ[ℂ] AmpH M d where
  toFun X := (PiLp.continuousLinearEquiv 2 ℂ _).symm
    fun p : Fin d × Fin d =>
      (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι (X p.1 p.2)
  map_add' X Y := by
    rw [← map_add]
    congr 1
    funext p
    simp [Matrix.add_apply, smul_add]
  map_smul' c X := by
    rw [← map_smul]
    congr 1
    funext p
    simp [Matrix.smul_apply, smul_comm c]

@[simp] theorem ampι_apply (X : Matrix (Fin d) (Fin d) M.A)
    (p : Fin d × Fin d) :
    ampι M d X p = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι (X p.1 p.2) := rfl

/-- Left multiplication by a matrix, acting on the row index of the
amplified GNS space through `M.L`. -/
noncomputable def ampLCLM (X : Matrix (Fin d) (Fin d) M.A) :
    AmpH M d →L[ℂ] AmpH M d :=
  (((PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin d × Fin d => M.H)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun p : Fin d × Fin d =>
      ∑ j : Fin d, (M.L (X p.1 j)).comp
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin d × Fin d => M.H) (j, p.2)))).comp
    (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin d × Fin d => M.H)).toContinuousLinearMap

@[simp] theorem ampLCLM_apply (X : Matrix (Fin d) (Fin d) M.A)
    (v : AmpH M d) (p : Fin d × Fin d) :
    ampLCLM M d X v p = ∑ j : Fin d, M.L (X p.1 j) (v (j, p.2)) := by
  simp [ampLCLM]

/-- Right multiplication by a matrix, acting on the column index of
the amplified GNS space through `M.R`. -/
noncomputable def ampRCLM (P : (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ) :
    AmpH M d →L[ℂ] AmpH M d :=
  (((PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin d × Fin d => M.H)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun p : Fin d × Fin d =>
      ∑ j : Fin d, (M.R (MulOpposite.op ((MulOpposite.unop P) j p.2))).comp
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin d × Fin d => M.H) (p.1, j)))).comp
    (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin d × Fin d => M.H)).toContinuousLinearMap

@[simp] theorem ampRCLM_apply (P : (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ)
    (v : AmpH M d) (p : Fin d × Fin d) :
    ampRCLM M d P v p
      = ∑ j : Fin d,
          M.R (MulOpposite.op ((MulOpposite.unop P) j p.2)) (v (p.1, j)) := by
  simp [ampRCLM]

theorem ampLCLM_one : ampLCLM M d 1 = 1 := by
  ext v p
  rw [ampLCLM_apply]
  calc ∑ j : Fin d, M.L ((1 : Matrix (Fin d) (Fin d) M.A) p.1 j) (v (j, p.2))
      = ∑ j : Fin d, if p.1 = j then v (j, p.2) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : p.1 = j <;> simp [Matrix.one_apply, h]
    _ = v (p.1, p.2) := by simp
    _ = v p := rfl

theorem ampLCLM_mul (X Y : Matrix (Fin d) (Fin d) M.A) :
    ampLCLM M d (X * Y) = (ampLCLM M d X).comp (ampLCLM M d Y) := by
  ext v p
  rw [ContinuousLinearMap.comp_apply, ampLCLM_apply]
  calc ∑ j : Fin d, M.L ((X * Y) p.1 j) (v (j, p.2))
      = ∑ j : Fin d, ∑ l : Fin d,
          M.L (X p.1 l) (M.L (Y l j) (v (j, p.2))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, map_sum, ContinuousLinearMap.sum_apply]
        exact Finset.sum_congr rfl fun l _ => by
          rw [map_mul, ContinuousLinearMap.mul_apply]
    _ = ∑ l : Fin d, ∑ j : Fin d,
          M.L (X p.1 l) (M.L (Y l j) (v (j, p.2))) := Finset.sum_comm
    _ = (ampLCLM M d X) (ampLCLM M d Y v) p := by
        rw [ampLCLM_apply]
        exact Finset.sum_congr rfl fun l _ => by
          rw [ampLCLM_apply, map_sum]

theorem ampLCLM_add (X Y : Matrix (Fin d) (Fin d) M.A) :
    ampLCLM M d (X + Y) = ampLCLM M d X + ampLCLM M d Y := by
  ext v p
  simp [Matrix.add_apply, Finset.sum_add_distrib]

theorem ampLCLM_smul (c : ℂ) (X : Matrix (Fin d) (Fin d) M.A) :
    ampLCLM M d (c • X) = c • ampLCLM M d X := by
  ext v p
  simp [Matrix.smul_apply, Finset.smul_sum]

theorem ampLCLM_star (X : Matrix (Fin d) (Fin d) M.A) :
    ampLCLM M d (star X) = star (ampLCLM M d X) := by
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have lhs :
      ∑ p : Fin d × Fin d, ⟪ampLCLM M d (star X) v p, w p⟫_ℂ
        = ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d,
            ⟪v (j, i), M.L (X j k) (w (k, i))⟫_ℂ := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    rw [ampLCLM_apply, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : M.L ((star X) (k, i).1 j) = star (M.L (X j k)) := by
      rw [Matrix.star_apply, map_star]
    rw [h1, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have rhs :
      ∑ q : Fin d × Fin d, ⟪v q, ampLCLM M d X w q⟫_ℂ
        = ∑ j : Fin d, ∑ i : Fin d, ∑ k : Fin d,
            ⟪v (j, i), M.L (X j k) (w (k, i))⟫_ℂ := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [ampLCLM_apply, inner_sum]
  rw [lhs, rhs]
  calc ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        ⟪v (j, i), M.L (X j k) (w (k, i))⟫_ℂ
      = ∑ i : Fin d, ∑ k : Fin d, ∑ j : Fin d,
          ⟪v (j, i), M.L (X j k) (w (k, i))⟫_ℂ := Finset.sum_comm
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
          ⟪v (j, i), M.L (X j k) (w (k, i))⟫_ℂ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ j : Fin d, ∑ i : Fin d, ∑ k : Fin d,
          ⟪v (j, i), M.L (X j k) (w (k, i))⟫_ℂ := Finset.sum_comm

theorem ampRCLM_one : ampRCLM M d 1 = 1 := by
  ext v p
  rw [ampRCLM_apply]
  calc ∑ j : Fin d,
        M.R (MulOpposite.op
          ((MulOpposite.unop (1 : (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ)) j p.2))
          (v (p.1, j))
      = ∑ j : Fin d, if j = p.2 then v (p.1, j) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : j = p.2 <;> simp [Matrix.one_apply, h]
    _ = v (p.1, p.2) := by simp
    _ = v p := rfl

theorem ampRCLM_mul (P Q : (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ) :
    ampRCLM M d (P * Q) = (ampRCLM M d P).comp (ampRCLM M d Q) := by
  ext v p
  rw [ContinuousLinearMap.comp_apply, ampRCLM_apply]
  calc ∑ j : Fin d,
        M.R (MulOpposite.op ((MulOpposite.unop (P * Q)) j p.2)) (v (p.1, j))
      = ∑ j : Fin d, ∑ l : Fin d,
          M.R (MulOpposite.op ((MulOpposite.unop P) l p.2))
            (M.R (MulOpposite.op ((MulOpposite.unop Q) j l)) (v (p.1, j))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hunop : (MulOpposite.unop (P * Q)) j p.2
            = ∑ l : Fin d,
                (MulOpposite.unop Q) j l * (MulOpposite.unop P) l p.2 := by
          rw [MulOpposite.unop_mul, Matrix.mul_apply]
        rw [hunop, Finset.op_sum, map_sum,
          ContinuousLinearMap.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [MulOpposite.op_mul, map_mul, ContinuousLinearMap.mul_apply]
    _ = ∑ l : Fin d, ∑ j : Fin d,
          M.R (MulOpposite.op ((MulOpposite.unop P) l p.2))
            (M.R (MulOpposite.op ((MulOpposite.unop Q) j l))
              (v (p.1, j))) := Finset.sum_comm
    _ = (ampRCLM M d P) (ampRCLM M d Q v) p := by
        rw [ampRCLM_apply]
        exact Finset.sum_congr rfl fun l _ => by
          rw [ampRCLM_apply, map_sum]

theorem ampRCLM_add (P Q : (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ) :
    ampRCLM M d (P + Q) = ampRCLM M d P + ampRCLM M d Q := by
  ext v p
  simp [Matrix.add_apply, Finset.sum_add_distrib]

theorem ampRCLM_smul (c : ℂ) (P : (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ) :
    ampRCLM M d (c • P) = c • ampRCLM M d P := by
  ext v p
  simp [Matrix.smul_apply, Finset.smul_sum]

theorem ampRCLM_star (P : (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ) :
    ampRCLM M d (star P) = star (ampRCLM M d P) := by
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have lhs :
      ∑ p : Fin d × Fin d, ⟪ampRCLM M d (star P) v p, w p⟫_ℂ
        = ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d,
            ⟪v (k, j),
              M.R (MulOpposite.op ((MulOpposite.unop P) i j)) (w (k, i))⟫_ℂ := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    rw [ampRCLM_apply, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : M.R (MulOpposite.op ((MulOpposite.unop (star P)) j (k, i).2))
        = star (M.R (MulOpposite.op ((MulOpposite.unop P) i j))) := by
      rw [MulOpposite.unop_star, Matrix.star_apply, ← map_star,
        MulOpposite.op_star]
    rw [h1, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have rhs :
      ∑ q : Fin d × Fin d, ⟪v q, ampRCLM M d P w q⟫_ℂ
        = ∑ k : Fin d, ∑ j : Fin d, ∑ i : Fin d,
            ⟪v (k, j),
              M.R (MulOpposite.op ((MulOpposite.unop P) i j)) (w (k, i))⟫_ℂ := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ampRCLM_apply, inner_sum]
  rw [lhs, rhs]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- The amplified left representation as a `⋆`-algebra homomorphism. -/
noncomputable def ampLhom :
    Matrix (Fin d) (Fin d) M.A →⋆ₐ[ℂ] (AmpH M d →L[ℂ] AmpH M d) where
  toFun := ampLCLM M d
  map_one' := ampLCLM_one M d
  map_mul' X Y := by
    rw [ampLCLM_mul]; rfl
  map_zero' := by
    ext v p
    simp
  map_add' := ampLCLM_add M d
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, ampLCLM_smul, ampLCLM_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := ampLCLM_star M d

/-- The amplified right representation as a `⋆`-algebra homomorphism
on the opposite algebra. -/
noncomputable def ampRhom :
    (Matrix (Fin d) (Fin d) M.A)ᵐᵒᵖ →⋆ₐ[ℂ] (AmpH M d →L[ℂ] AmpH M d) where
  toFun := ampRCLM M d
  map_one' := ampRCLM_one M d
  map_mul' P Q := by
    rw [ampRCLM_mul]; rfl
  map_zero' := by
    ext v p
    simp
  map_add' := ampRCLM_add M d
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, ampRCLM_smul, ampRCLM_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := ampRCLM_star M d

theorem ampι_dense : DenseRange (ampι M d) := by
  have hfac : ⇑(ampι M d)
      = (fun f : Fin d × Fin d → M.H =>
          (PiLp.continuousLinearEquiv 2 ℂ
            (fun _ : Fin d × Fin d => M.H)).symm f)
        ∘ (fun X : Matrix (Fin d) (Fin d) M.A =>
            fun p : Fin d × Fin d =>
              (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι (X p.1 p.2)) := rfl
  rw [hfac]
  refine DenseRange.comp ?_ ?_
    (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous
  · exact (PiLp.continuousLinearEquiv 2 ℂ _).symm.surjective.denseRange
  · have hcoord : ∀ p : Fin d × Fin d, DenseRange
        (fun a : M.A => (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι a) := by
      intro p
      have hd : 0 < d := p.1.pos
      have hc : (((Real.sqrt d)⁻¹ : ℝ) : ℂ) ≠ 0 := by
        have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
        simp [Complex.ofReal_ne_zero, ne_of_gt hs]
      exact DenseRange.comp
        (Function.Surjective.denseRange fun v =>
          ⟨(((Real.sqrt d)⁻¹ : ℝ) : ℂ)⁻¹ • v, by
            rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩)
        M.ι_dense (continuous_const_smul _)
    have hrange : Set.range
        (fun X : Matrix (Fin d) (Fin d) M.A =>
          fun p : Fin d × Fin d =>
            (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι (X p.1 p.2))
        = Set.univ.pi fun _ : Fin d × Fin d =>
            Set.range (fun a : M.A =>
              (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι a) := by
      ext f
      constructor
      · rintro ⟨X, rfl⟩ p _
        exact ⟨X p.1 p.2, rfl⟩
      · intro hf
        choose g hg using fun p : Fin d × Fin d => hf p (Set.mem_univ p)
        exact ⟨fun k i => g (k, i), by
          funext p
          exact (hg p).trans (by rfl)⟩
    rw [DenseRange, hrange]
    exact dense_pi Set.univ fun p _ => hcoord p

theorem ampι_inner (X Y : Matrix (Fin d) (Fin d) M.A) :
    ⟪ampι M d X, ampι M d Y⟫_ℂ = ampτ M d (star X * Y) := by
  rw [PiLp.inner_apply, ampτ_apply]
  have step : ∀ p : Fin d × Fin d,
      ⟪ampι M d X p, ampι M d Y p⟫_ℂ
        = ((d : ℂ)⁻¹) * M.τ (star (X p.1 p.2) * Y p.1 p.2) := by
    intro p
    rw [ampι_apply, ampι_apply, inner_smul_left, inner_smul_right,
      M.ι_inner, Complex.conj_ofReal, ← mul_assoc]
    congr 1
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun p _ => step p, ← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.star_apply]

/-- **The matrix amplification** `M_d(M)` as a standard tracial
algebra (Stage B, WP-B3). -/
noncomputable def amplify [NeZero d] : StdTracialAlgebra.{u} where
  A := Matrix (Fin d) (Fin d) M.A
  τ := ampτ M d
  τ_one := by
    rw [ampτ_apply]
    have h1 : ∀ i : Fin d, M.τ ((1 : Matrix (Fin d) (Fin d) M.A) i i) = 1 := by
      intro i
      rw [Matrix.one_apply_eq, M.τ_one]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  τ_mul_comm X Y := by
    rw [ampτ_apply, ampτ_apply]
    congr 1
    have hXY : ∀ i : Fin d, M.τ ((X * Y) i i)
        = ∑ j : Fin d, M.τ (X i j * Y j i) := by
      intro i
      rw [Matrix.mul_apply, map_sum]
    have hYX : ∀ j : Fin d, M.τ ((Y * X) j j)
        = ∑ i : Fin d, M.τ (Y j i * X i j) := by
      intro j
      rw [Matrix.mul_apply, map_sum]
    rw [Finset.sum_congr rfl fun i _ => hXY i,
      Finset.sum_congr rfl fun j _ => hYX j, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun i _ => M.τ_mul_comm _ _
  τ_star X := by
    rw [ampτ_apply, ampτ_apply]
    have h1 : ∀ i : Fin d, M.τ ((star X) i i) = star (M.τ (X i i)) := by
      intro i
      rw [Matrix.star_apply, M.τ_star]
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← star_sum, star_mul',
      star_inv₀, star_natCast, mul_comm]
  H := AmpH M d
  ι := ampι M d
  ι_dense := ampι_dense M d
  ι_inner := ampι_inner M d
  L := ampLhom M d
  R := ampRhom M d
  L_apply X Y := by
    show ampLCLM M d X (ampι M d Y) = ampι M d (X * Y)
    ext p
    rw [ampLCLM_apply, ampι_apply]
    have h1 : ∀ j : Fin d,
        M.L (X p.1 j) (ampι M d Y (j, p.2))
          = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι (X p.1 j * Y j p.2) := by
      intro j
      rw [ampι_apply, map_smul, M.L_apply]
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.smul_sum,
      ← map_sum, Matrix.mul_apply]
  R_apply Y X := by
    show ampRCLM M d (MulOpposite.op Y) (ampι M d X) = ampι M d (X * Y)
    ext p
    rw [ampRCLM_apply, ampι_apply]
    have h1 : ∀ j : Fin d,
        M.R (MulOpposite.op ((MulOpposite.unop (MulOpposite.op Y)) j p.2))
            (ampι M d X (p.1, j))
          = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • M.ι (X p.1 j * Y j p.2) := by
      intro j
      rw [MulOpposite.unop_op, ampι_apply, map_smul, M.R_apply]
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.smul_sum,
      ← map_sum, Matrix.mul_apply]
  LR_commute X Y := by
    show Commute (ampLCLM M d X) (ampRCLM M d (MulOpposite.op Y))
    refine ContinuousLinearMap.ext fun v => ?_
    have hL : ∀ (u : AmpH M d),
        (ampLCLM M d X * ampRCLM M d (MulOpposite.op Y)) u
          = ampLCLM M d X (ampRCLM M d (MulOpposite.op Y) u) := fun _ => rfl
    have hR : ∀ (u : AmpH M d),
        (ampRCLM M d (MulOpposite.op Y) * ampLCLM M d X) u
          = ampRCLM M d (MulOpposite.op Y) (ampLCLM M d X u) := fun _ => rfl
    rw [hL, hR]
    ext p
    rw [ampLCLM_apply, ampRCLM_apply]
    have hLside : ∀ j : Fin d,
        M.L (X p.1 j) (ampRCLM M d (MulOpposite.op Y) v (j, p.2))
          = ∑ l : Fin d,
              M.L (X p.1 j)
                (M.R (MulOpposite.op (Y l p.2)) (v (j, l))) := by
      intro j
      rw [ampRCLM_apply, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [MulOpposite.unop_op]
    have hRside : ∀ l : Fin d,
        M.R (MulOpposite.op ((MulOpposite.unop (MulOpposite.op Y)) l p.2))
            (ampLCLM M d X v (p.1, l))
          = ∑ j : Fin d,
              M.R (MulOpposite.op (Y l p.2))
                (M.L (X p.1 j) (v (j, l))) := by
      intro l
      rw [MulOpposite.unop_op, ampLCLM_apply, map_sum]
    rw [Finset.sum_congr rfl fun j _ => hLside j,
      Finset.sum_congr rfl fun l _ => hRside l, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    have hc := M.LR_commute (X p.1 j) (Y l p.2)
    calc M.L (X p.1 j) (M.R (MulOpposite.op (Y l p.2)) (v (j, l)))
        = (M.L (X p.1 j) * M.R (MulOpposite.op (Y l p.2))) (v (j, l)) := rfl
      _ = (M.R (MulOpposite.op (Y l p.2)) * M.L (X p.1 j)) (v (j, l)) := by
          rw [hc.eq]
      _ = M.R (MulOpposite.op (Y l p.2)) (M.L (X p.1 j) (v (j, l))) := rfl

end StdTracialAlgebra

end CommutingRepetition
