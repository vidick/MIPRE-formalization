/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/ModulusStability.lean
-/
/-
# Stability of the left modulus (Stage E of `PLAN-modulus-family.md`)

Proof layer of the von Neumann root `exists_modulusFamily` (node 1.3.1,
06_otqcs.tex lem otqcs-modulus / appendix lem absolute-value-L2).

* **The `L²`-Lipschitz property of the absolute value** for bounded self-adjoint
  `S, S'` in the block algebra `M₂(R(M)′)` with the unnormalized trace
  `τ₂ T = ⟪e₀Ω, T e₀Ω⟫ + ⟪e₁Ω, T e₁Ω⟫`: with `S = S₊ − S₋`, `|S| = S₊ + S₋`,
  `‖S − S'‖₂² − ‖|S| − |S'|‖₂² = 2 τ₂(S₊S'₋ + S₋S'₊ + S'₊S₋ + S'₋S₊) ≥ 0`,
  since `τ₂(AB) = τ₂(√A B √A) ≥ 0` for positive `A, B` (traciality of `τ₂` on
  the block algebra).
* Applied to `X = [[0, B], [B*, 0]]`, whose modulus is `diag(|B*|, |B|)`, this
  gives the **bounded stability** `‖(|B*| − |B'*|)Ω‖² ≤ 2‖(B − B')Ω‖²` for
  `B, B' ∈ R(M)′`.
* **Truncation**: `Bₙ := gₙ(E) C*` has `BₙΩ = P[0,aₙ] x → x` and
  `|Bₙ*| = ψₙ(E)`, so `|Bₙ*|Ω → hvec`; passing to the limit gives the
  manuscript's `‖hvec x − hvec y‖² ≤ 2‖x − y‖²`.
Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.LeftModulusData

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace GraphMod

open scoped InnerProductSpace Topology
open Filter Block BorelCalc

set_option linter.unusedSectionVars false

universe u

variable (M : StdTracialAlgebra.{u})

local notation "Ω" => M.traceVector

/-! ### The unnormalized trace on `M₂(R(M)′)` -/

/-- `τ₂ T = ∑ᵣ ⟪eᵣΩ, T eᵣΩ⟫`. -/
noncomputable def τ₂ (T : BH M (Fin 2) →L[ℂ] BH M (Fin 2)) : ℂ :=
  ∑ r : Fin 2, ⟪embed M (Fin 2) r Ω, T (embed M (Fin 2) r Ω)⟫_ℂ

theorem τ₂_eq (T : BH M (Fin 2) →L[ℂ] BH M (Fin 2)) :
    τ₂ M T = ∑ r : Fin 2, ⟪Ω, entry M (Fin 2) T r r Ω⟫_ℂ := by
  unfold τ₂
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [inner_embed_left]
  rfl

theorem τ₂_add (T T' : BH M (Fin 2) →L[ℂ] BH M (Fin 2)) : τ₂ M (T + T') = τ₂ M T + τ₂ M T' := by
  unfold τ₂
  simp only [ContinuousLinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]

theorem τ₂_sub (T T' : BH M (Fin 2) →L[ℂ] BH M (Fin 2)) : τ₂ M (T - T') = τ₂ M T - τ₂ M T' := by
  unfold τ₂
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]

theorem τ₂_re_nonneg {T : BH M (Fin 2) →L[ℂ] BH M (Fin 2)} (hT : 0 ≤ T) : 0 ≤ (τ₂ M T).re := by
  unfold τ₂
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun r _ => Resolver.Douglas.re_inner_nonneg_of_nonneg hT _

theorem re_τ₂_star_mul_self (T : BH M (Fin 2) →L[ℂ] BH M (Fin 2)) :
    (τ₂ M (star T * T)).re = ∑ r : Fin 2, ‖T (embed M (Fin 2) r Ω)‖ ^ 2 := by
  unfold τ₂
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Resolver.Douglas.mulA, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (T (embed M (Fin 2) r Ω))

/-- Traciality of `τ₂` on the block algebra. -/
theorem τ₂_mul_comm {T T' : BH M (Fin 2) →L[ℂ] BH M (Fin 2)} (hT : T ∈ blockAlg M (Fin 2))
    (hT' : T' ∈ blockAlg M (Fin 2)) : τ₂ M (T * T') = τ₂ M (T' * T) := by
  rw [τ₂_eq, τ₂_eq]
  simp only [entry_mul, sumCLM, inner_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact M.traceState_mul_comm_vn (hT b a) (hT' a b)

theorem blockAlg_strong_closed :
    ∀ (T : ℕ → BH M (Fin 2) →L[ℂ] BH M (Fin 2)) (L : BH M (Fin 2) →L[ℂ] BH M (Fin 2)),
      (∀ n, T n ∈ blockAlg M (Fin 2)) → (∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (L ξ))) →
        L ∈ blockAlg M (Fin 2) := by
  intro T L hT hL
  rw [mem_blockAlg_iff_comm]
  intro b
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [Resolver.Douglas.mulA, Resolver.Douglas.mulA]
  have h1 : Tendsto (fun n => Rt M (Fin 2) b (T n ξ)) atTop (𝓝 (Rt M (Fin 2) b (L ξ))) :=
    ((Rt M (Fin 2) b).continuous.tendsto _).comp (hL ξ)
  have h2 : Tendsto (fun n => Rt M (Fin 2) b (T n ξ)) atTop (𝓝 (L (Rt M (Fin 2) b ξ))) :=
    (hL (Rt M (Fin 2) b ξ)).congr fun n => by
      rw [← Resolver.Douglas.mulA, ← (mem_blockAlg_iff_comm M (Fin 2)).mp (hT n) b,
        Resolver.Douglas.mulA]
  exact tendsto_nhds_unique h1 h2

/-! ### Square roots, positive and negative parts -/

section Parts

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- The positive square root `√A = cfc √ A`. -/
noncomputable def sqrtOp (A : 𝓗 →L[ℂ] 𝓗) : 𝓗 →L[ℂ] 𝓗 := cfc Real.sqrt A

theorem sqrtOp_nonneg (A : 𝓗 →L[ℂ] 𝓗) : 0 ≤ sqrtOp A :=
  cfc_nonneg fun t _ => Real.sqrt_nonneg t

theorem sqrtOp_sa (A : 𝓗 →L[ℂ] 𝓗) : IsSelfAdjoint (sqrtOp A) := cfc_predicate _ _

theorem sqrtOp_mul_self {A : 𝓗 →L[ℂ] 𝓗} (hA : 0 ≤ A) : sqrtOp A * sqrtOp A = A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [sqrtOp, ← cfc_mul Real.sqrt Real.sqrt A,
    cfc_congr (g := fun t : ℝ => t) fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hA ht),
    cfc_id' ℝ A hsa]

/-- Uniqueness of the positive square root. -/
theorem sqrtOp_eq_of_mul_self {A D : 𝓗 →L[ℂ] 𝓗} (hD : 0 ≤ D) (h : D * D = A) : sqrtOp A = D := by
  have hsa : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg hD
  rw [sqrtOp, ← h, ← cfc_id' ℝ D hsa, ← cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) D,
    ← cfc_comp' Real.sqrt (fun t : ℝ => t * t) D (Real.continuous_sqrt.continuousOn)
      (by fun_prop) hsa]
  rw [cfc_congr (g := fun t : ℝ => t) fun t ht => ?_, cfc_id' ℝ D hsa]
  show Real.sqrt (t * t) = t
  exact Real.sqrt_mul_self (spectrum_nonneg_of_nonneg hD ht)

/-- The positive part `S₊ = max(S, 0)`. -/
noncomputable def posPart (S : 𝓗 →L[ℂ] 𝓗) : 𝓗 →L[ℂ] 𝓗 := cfc (fun t : ℝ => max t 0) S

/-- The negative part `S₋ = max(−S, 0)`. -/
noncomputable def negPart (S : 𝓗 →L[ℂ] 𝓗) : 𝓗 →L[ℂ] 𝓗 := cfc (fun t : ℝ => max (-t) 0) S

/-- The absolute value `|S|`. -/
noncomputable def absPart (S : 𝓗 →L[ℂ] 𝓗) : 𝓗 →L[ℂ] 𝓗 := cfc (fun t : ℝ => |t|) S

theorem posPart_nonneg (S : 𝓗 →L[ℂ] 𝓗) : 0 ≤ posPart S :=
  cfc_nonneg fun t _ => le_max_right _ _

theorem negPart_nonneg (S : 𝓗 →L[ℂ] 𝓗) : 0 ≤ negPart S :=
  cfc_nonneg fun t _ => le_max_right _ _

theorem absPart_nonneg (S : 𝓗 →L[ℂ] 𝓗) : 0 ≤ absPart S :=
  cfc_nonneg fun t _ => abs_nonneg t

theorem absPart_sa (S : 𝓗 →L[ℂ] 𝓗) : IsSelfAdjoint (absPart S) := cfc_predicate _ _

variable {S : 𝓗 →L[ℂ] 𝓗} (hS : IsSelfAdjoint S)
include hS

theorem posPart_sub_negPart : posPart S - negPart S = S := by
  rw [posPart, negPart, ← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) S]
  have : (fun t : ℝ => max t 0 - max (-t) 0) = fun t => t := by
    funext t
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  rw [this, cfc_id' ℝ S hS]

theorem absPart_eq : absPart S = posPart S + negPart S := by
  rw [absPart, posPart, negPart,
    ← cfc_add (f := fun t : ℝ => max t 0) (g := fun t : ℝ => max (-t) 0) (a := S)]
  congr 1
  funext t
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring

theorem posPart_mul_negPart : posPart S * negPart S = 0 := by
  rw [posPart, negPart, ← cfc_mul (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) S]
  have : (fun t : ℝ => max t 0 * max (-t) 0) = 0 := by
    funext t
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, zero_mul]; rfl
    · rw [max_eq_right (neg_nonpos.mpr h), mul_zero]; rfl
  rw [this, cfc_zero ℝ S]

theorem negPart_mul_posPart : negPart S * posPart S = 0 := by
  rw [posPart, negPart, ← cfc_mul (fun t : ℝ => max (-t) 0) (fun t : ℝ => max t 0) S]
  have : (fun t : ℝ => max (-t) 0 * max t 0) = 0 := by
    funext t
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, mul_zero]; rfl
    · rw [max_eq_right (neg_nonpos.mpr h), zero_mul]; rfl
  rw [this, cfc_zero ℝ S]

theorem absPart_mul_self : absPart S * absPart S = S * S := by
  rw [absPart, ← cfc_mul (fun t : ℝ => |t|) (fun t : ℝ => |t|) S]
  have : (fun t : ℝ => |t| * |t|) = fun t => t * t := by funext t; exact abs_mul_abs_self t
  rw [this, cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) S, cfc_id' ℝ S hS]

theorem absPart_eq_sqrtOp : absPart S = sqrtOp (S * S) :=
  (sqrtOp_eq_of_mul_self (absPart_nonneg S) (absPart_mul_self hS)).symm

end Parts

/-- The noncommutative ring identity behind the Lipschitz property. -/
theorem parts_identity {R : Type*} [Ring R] (P N P' N' : R) (h1 : P * N = 0) (h2 : N * P = 0)
    (h3 : P' * N' = 0) (h4 : N' * P' = 0) :
    (P - N - (P' - N')) * (P - N - (P' - N')) - (P + N - (P' + N')) * (P + N - (P' + N'))
      = 2 * (P * N' + N * P' + P' * N + N' * P) := by
  have : (P - N - (P' - N')) * (P - N - (P' - N')) - (P + N - (P' + N')) * (P + N - (P' + N'))
      = 2 * (P * N' + N * P' + P' * N + N' * P) - 2 * (P * N + N * P + P' * N' + N' * P') := by
    noncomm_ring
  rw [this, h1, h2, h3, h4]
  simp only [add_zero, mul_zero, sub_zero]

/-! ### The `L²`-Lipschitz property of the absolute value -/

theorem re_τ₂_mul_nonneg {A B : BH M (Fin 2) →L[ℂ] BH M (Fin 2)} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAm : A ∈ blockAlg M (Fin 2)) (hBm : B ∈ blockAlg M (Fin 2)) : 0 ≤ (τ₂ M (A * B)).re := by
  have hsq := sqrtOp_mul_self hA
  have hsa : IsSelfAdjoint (sqrtOp A) := sqrtOp_sa A
  have hsqm : sqrtOp A ∈ blockAlg M (Fin 2) :=
    BorelCalc.cfc_mem A (IsSelfAdjoint.of_nonneg hA) _ (blockAlg_strong_closed M) hAm _
  have hpos : 0 ≤ sqrtOp A * B * sqrtOp A := by
    have := ((ContinuousLinearMap.nonneg_iff_isPositive B).mp hB).conj_adjoint (sqrtOp A)
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hsa] at this
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr this
  calc (0 : ℝ) ≤ (τ₂ M (sqrtOp A * B * sqrtOp A)).re := τ₂_re_nonneg M hpos
    _ = (τ₂ M (A * B)).re := by
        rw [τ₂_mul_comm M (mul_mem hsqm hBm) hsqm, ← mul_assoc, hsq]

theorem posPart_mem {S : BH M (Fin 2) →L[ℂ] BH M (Fin 2)} (hS : IsSelfAdjoint S)
    (hSm : S ∈ blockAlg M (Fin 2)) : posPart S ∈ blockAlg M (Fin 2) :=
  BorelCalc.cfc_mem S hS _ (blockAlg_strong_closed M) hSm _

theorem negPart_mem {S : BH M (Fin 2) →L[ℂ] BH M (Fin 2)} (hS : IsSelfAdjoint S)
    (hSm : S ∈ blockAlg M (Fin 2)) : negPart S ∈ blockAlg M (Fin 2) :=
  BorelCalc.cfc_mem S hS _ (blockAlg_strong_closed M) hSm _

/-- **`L²`-Lipschitz property of `|·|`** on `M₂(R(M)′)`:
`‖|S| − |S'|‖₂² ≤ ‖S − S'‖₂²`. -/
theorem re_τ₂_absPart_sub_le {S S' : BH M (Fin 2) →L[ℂ] BH M (Fin 2)} (hS : IsSelfAdjoint S)
    (hS' : IsSelfAdjoint S') (hSm : S ∈ blockAlg M (Fin 2)) (hS'm : S' ∈ blockAlg M (Fin 2)) :
    (τ₂ M ((absPart S - absPart S') * (absPart S - absPart S'))).re
      ≤ (τ₂ M ((S - S') * (S - S'))).re := by
  have key := parts_identity (posPart S) (negPart S) (posPart S') (negPart S')
    (posPart_mul_negPart hS) (negPart_mul_posPart hS) (posPart_mul_negPart hS')
    (negPart_mul_posPart hS')
  rw [posPart_sub_negPart hS, posPart_sub_negPart hS', ← absPart_eq hS, ← absPart_eq hS'] at key
  have h2 : (2 : BH M (Fin 2) →L[ℂ] BH M (Fin 2)) * (posPart S * negPart S' + negPart S * posPart S'
      + posPart S' * negPart S + negPart S' * posPart S)
      = (posPart S * negPart S' + negPart S * posPart S' + posPart S' * negPart S
        + negPart S' * posPart S) + (posPart S * negPart S' + negPart S * posPart S'
        + posPart S' * negPart S + negPart S' * posPart S) := two_mul _
  have hnn : 0 ≤ (τ₂ M (posPart S * negPart S' + negPart S * posPart S'
      + posPart S' * negPart S + negPart S' * posPart S)).re := by
    rw [τ₂_add, τ₂_add, τ₂_add, Complex.add_re, Complex.add_re, Complex.add_re]
    have a1 := re_τ₂_mul_nonneg M (posPart_nonneg S) (negPart_nonneg S') (posPart_mem M hS hSm)
      (negPart_mem M hS' hS'm)
    have a2 := re_τ₂_mul_nonneg M (negPart_nonneg S) (posPart_nonneg S') (negPart_mem M hS hSm)
      (posPart_mem M hS' hS'm)
    have a3 := re_τ₂_mul_nonneg M (posPart_nonneg S') (negPart_nonneg S) (posPart_mem M hS' hS'm)
      (negPart_mem M hS hSm)
    have a4 := re_τ₂_mul_nonneg M (negPart_nonneg S') (posPart_nonneg S) (negPart_mem M hS' hS'm)
      (posPart_mem M hS hSm)
    linarith
  have hdiff : (τ₂ M ((S - S') * (S - S') - (absPart S - absPart S') * (absPart S - absPart S'))).re
      = (τ₂ M (2 * (posPart S * negPart S' + negPart S * posPart S' + posPart S' * negPart S
        + negPart S' * posPart S))).re := by rw [key]
  rw [τ₂_sub, Complex.sub_re, h2, τ₂_add, Complex.add_re] at hdiff
  linarith

/-! ### The modulus of `[[0, B], [B*, 0]]` -/

/-- `X_B = [[0, B], [B*, 0]]`. -/
noncomputable def Xop (B : M.H →L[ℂ] M.H) : BH M (Fin 2) →L[ℂ] BH M (Fin 2) :=
  place M (Fin 2) 0 1 B + place M (Fin 2) 1 0 (star B)

theorem Xop_mem {B : M.H →L[ℂ] M.H} (hB : B ∈ M.vnAlg) : Xop M B ∈ blockAlg M (Fin 2) :=
  add_mem (place_mem M (Fin 2) 0 1 hB) (place_mem M (Fin 2) 1 0 (star_mem hB))

theorem Xop_sa (B : M.H →L[ℂ] M.H) : IsSelfAdjoint (Xop M B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', Xop, map_add, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, star_place, star_place, star_star, add_comm]

/-- The block-diagonal operator `diag(A, A')`. -/
noncomputable def diag (A A' : M.H →L[ℂ] M.H) : BH M (Fin 2) →L[ℂ] BH M (Fin 2) :=
  place M (Fin 2) 0 0 A + place M (Fin 2) 1 1 A'

theorem Xop_mul_Xop (B : M.H →L[ℂ] M.H) : Xop M B * Xop M B = diag M (B * star B) (star B * B) := by
  simp [Xop, diag, add_mul, mul_add, place_mul_place, add_comm]

theorem diag_mul_diag (A A' C C' : M.H →L[ℂ] M.H) :
    diag M A A' * diag M C C' = diag M (A * C) (A' * C') := by
  simp [diag, add_mul, mul_add, place_mul_place]

theorem diag_sub (A A' C C' : M.H →L[ℂ] M.H) :
    diag M A A' - diag M C C' = diag M (A - C) (A' - C') := by
  simp only [diag, map_sub]; abel

theorem place_diag_nonneg (r : Fin 2) {A : M.H →L[ℂ] M.H} (hA : 0 ≤ A) :
    0 ≤ place M (Fin 2) r r A := by
  have hsa : IsSelfAdjoint (place M (Fin 2) r r A) := by
    rw [IsSelfAdjoint, star_place, (IsSelfAdjoint.of_nonneg hA).star_eq]
  refine Resolver.Douglas.nonneg_of_re_inner hsa fun w => ?_
  rw [place_apply_vec, inner_embed_left, ← BorelCalc.inner_sa (IsSelfAdjoint.of_nonneg hA)]
  exact Resolver.Douglas.re_inner_nonneg_of_nonneg hA _

theorem diag_nonneg {A A' : M.H →L[ℂ] M.H} (hA : 0 ≤ A) (hA' : 0 ≤ A') : 0 ≤ diag M A A' :=
  add_nonneg (place_diag_nonneg M 0 hA) (place_diag_nonneg M 1 hA')

/-- `|X_B| = diag(|B*|, |B|)`. -/
theorem absPart_Xop (B : M.H →L[ℂ] M.H) :
    absPart (Xop M B) = diag M (sqrtOp (B * star B)) (sqrtOp (star B * B)) := by
  have h1 : sqrtOp (B * star B) * sqrtOp (B * star B) = B * star B :=
    sqrtOp_mul_self (mul_star_self_nonneg B)
  have h2 : sqrtOp (star B * B) * sqrtOp (star B * B) = star B * B :=
    sqrtOp_mul_self (star_mul_self_nonneg B)
  have hD : 0 ≤ diag M (sqrtOp (B * star B)) (sqrtOp (star B * B)) :=
    diag_nonneg M (sqrtOp_nonneg _) (sqrtOp_nonneg _)
  have hDD : diag M (sqrtOp (B * star B)) (sqrtOp (star B * B)) *
      diag M (sqrtOp (B * star B)) (sqrtOp (star B * B)) = Xop M B * Xop M B := by
    rw [diag_mul_diag, h1, h2, Xop_mul_Xop]
  rw [absPart_eq_sqrtOp (Xop_sa M B)]
  exact sqrtOp_eq_of_mul_self hD hDD

theorem diag_embed_zero (A A' : M.H →L[ℂ] M.H) (v : M.H) :
    diag M A A' (embed M (Fin 2) 0 v) = embed M (Fin 2) 0 (A v) := by
  simp [diag, place_apply_vec, embed_apply]

theorem diag_embed_one (A A' : M.H →L[ℂ] M.H) (v : M.H) :
    diag M A A' (embed M (Fin 2) 1 v) = embed M (Fin 2) 1 (A' v) := by
  simp [diag, place_apply_vec, embed_apply]

theorem Xop_embed_zero (B : M.H →L[ℂ] M.H) (v : M.H) :
    Xop M B (embed M (Fin 2) 0 v) = embed M (Fin 2) 1 (star B v) := by
  simp [Xop, place_apply_vec, embed_apply]

theorem Xop_embed_one (B : M.H →L[ℂ] M.H) (v : M.H) :
    Xop M B (embed M (Fin 2) 1 v) = embed M (Fin 2) 0 (B v) := by
  simp [Xop, place_apply_vec, embed_apply]

theorem norm_embed (r : Fin 2) (v : M.H) : ‖embed M (Fin 2) r v‖ = ‖v‖ := by
  have h : ‖embed M (Fin 2) r v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_embed_left, embed_apply, if_pos rfl,
      inner_self_eq_norm_sq (𝕜 := ℂ)]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **Bounded stability**: `‖(|B*| − |B'*|)Ω‖² ≤ 2‖(B − B')Ω‖²` for `B, B' ∈ R(M)′`. -/
theorem bounded_stability {B B' : M.H →L[ℂ] M.H} (hB : B ∈ M.vnAlg) (hB' : B' ∈ M.vnAlg) :
    ‖(sqrtOp (B * star B) - sqrtOp (B' * star B')) Ω‖ ^ 2 ≤ 2 * ‖(B - B') Ω‖ ^ 2 := by
  have hX : IsSelfAdjoint (Xop M B) := Xop_sa M B
  have hX' : IsSelfAdjoint (Xop M B') := Xop_sa M B'
  have h := re_τ₂_absPart_sub_le M hX hX' (Xop_mem M hB) (Xop_mem M hB')
  -- the left side
  have hL : (τ₂ M ((absPart (Xop M B) - absPart (Xop M B')) *
      (absPart (Xop M B) - absPart (Xop M B')))).re
      = ‖(sqrtOp (B * star B) - sqrtOp (B' * star B')) Ω‖ ^ 2
        + ‖(sqrtOp (star B * B) - sqrtOp (star B' * B')) Ω‖ ^ 2 := by
    have hsa : IsSelfAdjoint (absPart (Xop M B) - absPart (Xop M B')) :=
      (absPart_sa _).sub (absPart_sa _)
    have e := re_τ₂_star_mul_self M (absPart (Xop M B) - absPart (Xop M B'))
    rw [hsa.star_eq] at e
    rw [e, Fin.sum_univ_two, absPart_Xop, absPart_Xop, diag_sub, diag_embed_zero, diag_embed_one,
      norm_embed, norm_embed]
  -- the right side
  have hR : (τ₂ M ((Xop M B - Xop M B') * (Xop M B - Xop M B'))).re = 2 * ‖(B - B') Ω‖ ^ 2 := by
    have hsa : IsSelfAdjoint (Xop M B - Xop M B') := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub, ← ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.star_eq_adjoint, hX.star_eq, hX'.star_eq]
    have e := re_τ₂_star_mul_self M (Xop M B - Xop M B')
    rw [hsa.star_eq] at e
    rw [e, Fin.sum_univ_two]
    have e0 : (Xop M B - Xop M B') (embed M (Fin 2) 0 Ω) = embed M (Fin 2) 1 (star (B - B') Ω) := by
      rw [ContinuousLinearMap.sub_apply, Xop_embed_zero, Xop_embed_zero, ← map_sub, star_sub,
        ContinuousLinearMap.sub_apply]
    have e1 : (Xop M B - Xop M B') (embed M (Fin 2) 1 Ω) = embed M (Fin 2) 0 ((B - B') Ω) := by
      rw [ContinuousLinearMap.sub_apply, Xop_embed_one, Xop_embed_one, ← map_sub,
        ContinuousLinearMap.sub_apply]
    rw [e0, e1, norm_embed, norm_embed, ← M.J_apply_traceVector (sub_mem hB hB'), M.norm_J]
    ring
  rw [hL, hR] at h
  linarith [sq_nonneg ‖(sqrtOp (star B * B) - sqrtOp (star B' * B')) Ω‖]

/-! ### Truncation and the stability of the left modulus -/

variable (x : M.H)

local notation "bE" => BorelCalc.bfc (Eop M x) (Eop_sa M x)
local notation "PE" => BorelCalc.P (Eop M x) (Eop_sa M x)

/-- The bounded truncation `Bₙ = gₙ(E) C*` of left multiplication by `x`. -/
noncomputable def Bn (n : ℕ) : M.H →L[ℂ] M.H := bE (gn n) * star (Cop M x)

theorem Bn_mem (n : ℕ) : Bn M x n ∈ M.vnAlg := mul_mem (bE_mem M x (gn_bdd n)) (star_Cop_mem M x)

theorem star_Cop_traceVector : star (Cop M x) Ω = (1 - Eop M x) x := by
  have h1 := star_Cop_ι M x 1
  have hRop1 : M.Rop 1 x = x := by
    show M.R (MulOpposite.op 1) x = x
    rw [MulOpposite.op_one, map_one, Resolver.Douglas.oneA]
  rw [hRop1] at h1
  exact h1

theorem gn_mul_one_sub_clamp (n : ℕ) :
    (fun t => gn n t * (1 - clamp t)) = (Set.Icc 0 (aN n)).indicator 1 := by
  rw [← one_sub_clamp_mul_gn n]
  funext t
  ring

/-- `BₙΩ = P[0,aₙ] x`. -/
theorem Bn_traceVector (n : ℕ) : Bn M x n Ω = PE (Set.Icc 0 (aN n)) x := by
  rw [Bn, Resolver.Douglas.mulA, star_Cop_traceVector, ← Resolver.Douglas.mulA,
    bE_mul_one_sub_Eop M x (gn_bdd n), gn_mul_one_sub_clamp, BorelCalc.P]

/-- `Bₙ Bₙ* = ψₙ(E)²`. -/
theorem Bn_mul_star (n : ℕ) : Bn M x n * star (Bn M x n) = bE (ψn n) * bE (ψn n) := by
  have hfun : (gn n * fun t => clamp t * (1 - clamp t)) * gn n = ψn n * ψn n := by
    funext t
    have := congrFun (ψn_mul_ψn n) t
    simp only [Pi.mul_apply] at this ⊢
    rw [this]; ring
  have hb : Bdd fun t => clamp t * (1 - clamp t) := clamp_bdd.mul one_sub_clamp_bdd
  rw [Bn, star_mul, star_star, (BorelCalc.bfc_isSelfAdjoint _ _ (gn_bdd n)).star_eq,
    show bE (gn n) * star (Cop M x) * (Cop M x * bE (gn n))
      = bE (gn n) * (star (Cop M x) * Cop M x) * bE (gn n) by noncomm_ring,
    star_Cop_mul_Cop, one_sub_Eop_eq, Eop_mul_bE M x one_sub_clamp_bdd,
    ← BorelCalc.bfc_mul _ _ (gn_bdd n) hb, ← BorelCalc.bfc_mul _ _ ((gn_bdd n).mul hb) (gn_bdd n),
    hfun, BorelCalc.bfc_mul _ _ (ψn_bdd n) (ψn_bdd n)]

/-- `|Bₙ*| = ψₙ(E)`. -/
theorem sqrtOp_Bn (n : ℕ) : sqrtOp (Bn M x n * star (Bn M x n)) = bE (ψn n) :=
  sqrtOp_eq_of_mul_self (BorelCalc.bfc_nonneg _ _ (ψn_bdd n) (ψn_nonneg n)) (Bn_mul_star M x n).symm

/-- **Stability of the left modulus** (06_otqcs.tex, lem otqcs-modulus):
`‖hvec x − hvec y‖² ≤ 2 ‖x − y‖²`. -/
theorem stability (y : M.H) : ‖hvec M x - hvec M y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 := by
  have hn : ∀ n, ‖bE (ψn n) Ω - BorelCalc.bfc (Eop M y) (Eop_sa M y) (ψn n) Ω‖ ^ 2
      ≤ 2 * ‖PE (Set.Icc 0 (aN n)) x - BorelCalc.P (Eop M y) (Eop_sa M y) (Set.Icc 0 (aN n)) y‖ ^ 2 := by
    intro n
    have h := bounded_stability M (Bn_mem M x n) (Bn_mem M y n)
    rwa [sqrtOp_Bn, sqrtOp_Bn, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      Bn_traceVector, Bn_traceVector] at h
  refine le_of_tendsto_of_tendsto' (((hvec_tendsto M x).sub (hvec_tendsto M y)).norm.pow 2) ?_ hn
  have hx := BorelCalc.P_tendsto_iUnion (Eop M x) (Eop_sa M x) (fun n => measurableSet_Icc)
    monotone_Icc_aN x
  have hy := BorelCalc.P_tendsto_iUnion (Eop M y) (Eop_sa M y) (fun n => measurableSet_Icc)
    monotone_Icc_aN y
  rw [iUnion_Icc_aN, PE_Ico, ContinuousLinearMap.one_apply] at hx hy
  exact tendsto_const_nhds.mul ((hx.sub hy).norm.pow 2)

end GraphMod

end CommutingRepetition
