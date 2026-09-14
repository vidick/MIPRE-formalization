/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ValueApprox.Gaussian
import MIPRE.Foundations.ValueApprox.Norms

/-!
# Gaussian-rational unitaries and projective measurements are dense

* `exists_unitary_entriesIn_norm_smul_sub_le`: up to a unit phase, every unitary is within `η`
  (in operator norm) of a unitary with Gaussian-rational entries — the Cayley transform of an
  entrywise rounding of the skew-Hermitian Cayley preimage;
* `IsPVM.exists_entriesIn_norm_sub_le`: every projective measurement is within `η`, element by
  element, of a projective measurement with Gaussian-rational entries — conjugate the coordinate
  pattern of `IsPVM.exists_unitary_pattern` by the approximating unitary.

This is the density half of `lem:value-lower-approx`, and the point where the Lean route departs
from the paper's: the paper rounds the measurement operators themselves and repairs the result
into a POVM (its Claims "Stability" and "Density"); here the rounding happens at the level of the
skew-Hermitian generator, so that the rounded object is an exact projective measurement and no
repair is needed.
-/

namespace MIPRE.ValueApprox

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Up to a unit phase `z`, every unitary `U` is within `η` of a Gaussian-rational unitary. -/
theorem exists_unitary_entriesIn_norm_smul_sub_le {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ V : Matrix n n ℂ, V ∈ Matrix.unitaryGroup n ℂ ∧
      EntriesIn GaussianRat V ∧ ‖z • U - V‖ ≤ η := by
  obtain ⟨z, hz, hz1⟩ := exists_norm_eq_one_isUnit_one_add_smul U
  obtain ⟨S, hS, hSU⟩ := exists_isSkewHermitian_cayley_eq (smul_mem_unitaryGroup hU hz) hz1
  have hδ : 0 < η / (2 * (Fintype.card n + 1)) := by positivity
  obtain ⟨T, hT, hTK, hTη⟩ := hS.exists_entriesIn_norm_sub_le hδ
  refine ⟨z, hz, cayley T, cayley_mem_unitaryGroup hT, hTK.cayley, ?_⟩
  have hST : ‖S - T‖ ≤ η / 2 := by
    have hc : (0 : ℝ) ≤ Fintype.card n := by positivity
    calc ‖S - T‖ ≤ Fintype.card n * (η / (2 * (Fintype.card n + 1))) :=
          l2_opNorm_le_card_mul_of_entry_le hδ.le fun i j => by
            rw [Matrix.sub_apply]
            exact hTη i j
      _ ≤ η / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  calc ‖z • U - cayley T‖ = ‖cayley S - cayley T‖ := by rw [hSU]
    _ ≤ 2 * ‖S - T‖ := norm_cayley_sub_cayley_le hS hT
    _ ≤ 2 * (η / 2) := by gcongr
    _ = η := by ring

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Every projective measurement is within `η`, element by element, of a projective measurement
with Gaussian-rational entries. -/
theorem IsPVM.exists_entriesIn_norm_sub_le {M : A → Matrix n n ℂ} (hM : IsPVM M) {η : ℝ}
    (hη : 0 < η) :
    ∃ M' : A → Matrix n n ℂ, IsPVM M' ∧ (∀ a, EntriesIn GaussianRat (M' a)) ∧
      ∀ a, ‖M a - M' a‖ ≤ η := by
  obtain ⟨U, r, hUr⟩ := hM.exists_unitary_pattern
  obtain ⟨z, hz, V, hV, hVK, hVη⟩ :=
    exists_unitary_entriesIn_norm_smul_sub_le U.2 (half_pos hη)
  refine ⟨fun a => V * patternProj r a * Vᴴ, (isPVM_patternProj r).conj ⟨V, hV⟩, fun a =>
    (hVK.mul (EntriesIn.patternProj r a)).mul (hVK.conjTranspose fun _ => GaussianRat.star_mem),
    fun a => ?_⟩
  rw [hUr a, Matrix.star_eq_conjTranspose,
    ← smul_mul_mul_conjTranspose_smul (U : Matrix n n ℂ) (patternProj r a) hz]
  calc ‖z • (U : Matrix n n ℂ) * patternProj r a * (z • (U : Matrix n n ℂ))ᴴ -
        V * patternProj r a * Vᴴ‖
      ≤ 2 * ‖z • (U : Matrix n n ℂ) - V‖ :=
        norm_mul_mul_conjTranspose_sub_le
          (norm_le_one_of_mem_unitaryGroup (smul_mem_unitaryGroup U.2 hz))
          (norm_le_one_of_mem_unitaryGroup hV) ((isPVM_patternProj r).norm_le_one a)
    _ ≤ 2 * (η / 2) := by gcongr
    _ = η := by ring

end MIPRE.ValueApprox
