/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Weyl
import MIPRE.Foundations.CL.Canonical

/-!
# Fourier formulas for a linear-map measurement

The two identities of `lem:pauli-linear-fourier`, in characteristic two. The
formulas hold for either Weyl family, and more generally for any operator family
with its Fourier-defined spectral operators. Orthogonality is the actual dot
product perpendicular subspace, not a canonical direct-sum complement.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}

local instance : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2

/-- Restrict the trace character to a linear subspace, viewed over the binary field. -/
def subspaceTrace (S : Submodule F (Fin n → F)) (c : Fin n → F) :
    S →ₗ[ZMod 2] ZMod 2 :=
  (trDotL c).comp (S.subtype.restrictScalars (ZMod 2))

@[simp] theorem subspaceTrace_apply (S : Submodule F (Fin n → F)) (c : Fin n → F) (v : S) :
    subspaceTrace S c v = trDot v.1 c := rfl

/-- The trace annihilator of an `F`-subspace is its ordinary dot-product perpendicular. -/
theorem subspaceTrace_eq_zero_iff (S : Submodule F (Fin n → F)) (c : Fin n → F) :
    subspaceTrace S c = 0 ↔ c ∈ CL.perp S := by
  rw [CL.mem_perp]
  constructor
  · intro h y hy
    by_contra hne
    apply trMulL_ne_zero (x := dotF y c) hne
    ext r
    change Algebra.trace (ZMod 2) F (r * dotF y c) = 0
    have he := LinearMap.congr_fun h ⟨r • y, S.smul_mem r hy⟩
    simpa only [subspaceTrace_apply, LinearMap.zero_apply, trDot_smul] using he
  · intro h
    ext v
    change Algebra.trace (ZMod 2) F (∑ i, v.1 i * c i) = 0
    rw [h v.1 v.2, map_zero]

/-- Character cancellation on a subspace. -/
theorem sum_subspace_sign (S : Submodule F (Fin n → F)) (c : Fin n → F) :
    (∑ v : S, sgn (trDot v.1 c)) =
      if c ∈ CL.perp S then (Fintype.card S : ℂ) else 0 := by
  classical
  by_cases hc : c ∈ CL.perp S
  · rw [if_pos hc]
    have hzero := (subspaceTrace_eq_zero_iff S c).mpr hc
    have he (v : S) : trDot v.1 c = 0 := LinearMap.congr_fun hzero v
    simp only [he, sgn_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg hc]
    exact sum_sgn_linear (subspaceTrace S c) (mt (subspaceTrace_eq_zero_iff S c).mp hc)

/-- On a fiber, every trace character perpendicular to the kernel is constant. -/
theorem trDot_eq_of_same_fiber (L : (Fin n → F) →ₗ[F] (Fin n → F))
    {v x y : Fin n → F} (hv : v ∈ CL.perp L.ker) (hxy : L x = L y) :
    trDot v x = trDot v y := by
  have hk : x - y ∈ L.ker := by simp [LinearMap.mem_ker, map_sub, hxy]
  have hdot := (CL.mem_perp.mp hv) (x - y) hk
  have ht : trDot (x - y) v = 0 := by rw [trDot, hdot, map_zero]
  have hchar : x - y = x + y := by
    ext i
    exact CharTwo.sub_eq_add _ _
  rw [hchar, trDot_add_left] at ht
  rw [trDot_comm v x, trDot_comm v y]
  exact CharTwo.add_eq_zero.mp ht

/-- Pick a preimage only to state the Fourier coefficients; this is not an executable choice. -/
def linearPreimage (L : (Fin n → F) →ₗ[F] (Fin n → F)) (a : Fin n → F) : Fin n → F :=
  if h : ∃ x, L x = a then h.choose else 0

theorem linearPreimage_image (L : (Fin n → F) →ₗ[F] (Fin n → F)) (x : Fin n → F) :
    L (linearPreimage L (L x)) = L x := by
  have hx : ∃ y, L y = L x := ⟨x, rfl⟩
  rw [linearPreimage, dif_pos hx]
  exact hx.choose_spec

/-- Expand an allowed Pauli operator in the projectors of the linear-map measurement. -/
theorem linear_measurement_fourier
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (v : Fin n → F) (hv : v ∈ CL.perp L.ker) :
    w v = ∑ a : Fin n → F, sgn (trDot v (linearPreimage L a)) • synOf w L a := by
  rw [eq_sum_proj (w := w) v]
  have hc (e : Fin n → F) : trDot v e = trDot v (linearPreimage L (L e)) :=
    trDot_eq_of_same_fiber L hv (linearPreimage_image L e).symm
  simp_rw [synOf, Finset.smul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun e (_ : e ∈ (univ : Finset (Fin n → F))) => mem_univ (L e))
      (fun e => sgn (trDot v e) • proj w e)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e he
  rw [hc, (Finset.mem_filter.mp he).2]

/-- Recover the projector on a fiber by averaging only over the kernel's perpendicular. -/
theorem linear_measurement_fourier_inverse
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (x : Fin n → F) :
    (Fintype.card (CL.perp L.ker) : ℂ)⁻¹ •
      ∑ v : CL.perp L.ker, sgn (trDot v.1 x) • w v.1 = synOf w L (L x) := by
  classical
  have hcard : (Fintype.card (CL.perp L.ker) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := CL.perp L.ker)).ne'
  have he (z : Fin n → F) : x + z ∈ CL.perp (CL.perp L.ker) ↔ L z = L x := by
    rw [CL.perp_perp, LinearMap.mem_ker, map_add]
    exact (Weyl.add_eq_zero_iff_vec _ _).trans eq_comm
  rw [Finset.sum_congr rfl fun v (_ : v ∈ univ) => by
    rw [eq_sum_proj (w := w) v.1, Finset.smul_sum]]
  rw [Finset.sum_comm]
  simp_rw [smul_smul, ← sgn_add, ← trDot_add_right]
  rw [Finset.sum_congr rfl fun z (_ : z ∈ univ) => by
    rw [← Finset.sum_smul, sum_subspace_sign]]
  simp only [he]
  rw [Finset.smul_sum]
  unfold synOf
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : L z = L x
  · rw [if_pos hz, smul_smul, inv_mul_cancel₀ hcard, one_smul, if_pos hz]
  · rw [if_neg hz, zero_smul, smul_zero, if_neg hz]

end MIPRE.Introspection

end
