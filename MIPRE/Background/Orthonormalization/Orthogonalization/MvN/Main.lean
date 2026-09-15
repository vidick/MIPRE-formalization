/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Main.lean
-/
/-
# Tier T3: assembly of Theorem 1.2 under the structure-theory interface

The proof map of PLAN.md §9.3, `G ∘ (S ∘ finite, III)`:

* `orthAtN_of_isFiniteProj`: the finite case (`MvN/Finite.lean`) for any finite
  output set;
* `orthAtN_of_isSemifiniteAt`: step S — the net of finite projections of a
  semifinite summand (interface field H2) and the semifinite reduction
  (`MvN/Semifinite.lean`);
* `orthAtN_one_of_structure`: the type decomposition (H1) glues the semifinite
  summand and the type III summand (`MvN/TypeIII.lean`, from H4).

The conditional statement of Theorem 1.2 itself, `povm_orthogonalization_of_structure`
(FIDELITY.md, tier T3 statement layer; statement byte-identical to the signed
`povm_orthogonalization` with the binder `hS`), is proved at the end from
`orthAtN_one_of_structure`.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Finite
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.TypeIII

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder
open Filter Topology CommutingRepetition.VN Blocks

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Theorem 1.2 at a finite projection** for the functionals normal on `M`, any finite
output set, under the interface. -/
theorem orthAtN_of_isFiniteProj (hS : MvNStructureTheory.{u}) (M : VonNeumannAlgebra H)
    {p : H →L[ℂ] H} (hp : IsFiniteProj M p) (ι : Type*) [Fintype ι] : OrthAtN M p ι :=
  orthAtP_of_equiv M p (Fintype.equivFin ι) _ (orthAtN_fin_of_isFiniteProj hS M hp _)

/-- **Step S**: Theorem 1.2 at a semifinite central projection `z`, from the increasing
net of finite projections converging to `z` (interface field H2, Takesaki V.1.37) and
the semifinite reduction. -/
theorem orthAtN_of_isSemifiniteAt (hS : MvNStructureTheory.{u}) (M : VonNeumannAlgebra H)
    {z : H →L[ℂ] H} (hz : IsCentralProj M z) (hsf : IsSemifiniteAt M z) (ι : Type*)
    [Fintype ι] : OrthAtN M z ι := by
  obtain ⟨κ, _, _, _, p, -, hp, hlim⟩ := hS.semifinite_net M z hz hsf
  exact orthAtN_of_net M hz p (fun α => ⟨(hp α).1.1, (hp α).1.2.1, (hp α).2⟩) hlim ι
    (fun α => orthAtN_of_isFiniteProj hS M (hp α).1 ι)

/-- **Theorem 1.2 for the functionals normal on `M`**, under the interface: the type
decomposition `1 = z + (1 − z)` (H1) into a semifinite and a type III summand, each
handled by its case, and the gluing of `Blocks/Glue.lean`. -/
theorem orthAtN_one_of_structure (hS : MvNStructureTheory.{u}) (M : VonNeumannAlgebra H)
    (ι : Type*) [Fintype ι] : OrthAtN M 1 ι := by
  obtain ⟨z, hz, hsf, hIII⟩ := hS.type_decomposition M
  have hz' : IsCentralProj M (1 - z) :=
    ⟨hz.isStarProjection.one_sub, sub_mem (one_mem M) hz.mem,
      fun x hx => (Commute.one_left x).sub_left (hz.commute x hx)⟩
  have hzz : z * (1 - z) = 0 := by
    rw [mul_sub, mul_one, hz.isStarProjection.isIdempotentElem.eq, sub_self]
  have hzz' : (1 - z) * z = 0 := by
    rw [sub_mul, one_mul, hz.isStarProjection.isIdempotentElem.eq, sub_self]
  refine orthAtN_one_of_blocks M (κ := Fin 2) (fun j => if j = 0 then z else 1 - z)
    ?_ ?_ ?_ ι ?_
  · intro j
    by_cases hj : j = 0 <;> simp only [hj, if_true, if_false, Fin.isValue] <;>
      first | exact hz | exact hz'
  · intro j k hjk
    fin_cases j <;> fin_cases k <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
      if_true, if_false, one_ne_zero] at hjk ⊢
    · exact absurd rfl hjk
    · exact hzz
    · exact hzz'
    · exact absurd rfl hjk
  · simp only [Fin.sum_univ_two, Fin.isValue, if_true, one_ne_zero, if_false, add_sub_cancel]
  · intro j
    by_cases hj : j = 0
    · simp only [hj, if_true]
      exact orthAtN_of_isSemifiniteAt hS M hz hsf ι
    · simp only [hj, if_false]
      exact orthAtN_of_typeIII M hz' (hS.halving M (1 - z) hz' hIII) ι

end Orthogonalization.MvN

namespace Orthogonalization

open scoped BigOperators ComplexOrder
open MvN

universe u

/-- **Theorem 1.2, conditional form** (`thm:orthonormalization`; tier T3): the
statement of `povm_orthogonalization` for every von Neumann algebra, under the
structure-theory interface `MvNStructureTheory` (PLAN.md §9). -/
theorem povm_orthogonalization_of_structure (hS : MvNStructureTheory.{u})
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (φ : NormalState M)
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  obtain ⟨p, hpM, hp, -, hsum, hlt⟩ := orthAtN_one_of_structure hS M ι φ.toLinearMap
    (NormalState.isNormalOn φ) φ.nonneg' φ.map_one' a ha.1
    (fun i => (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (ha.2.1 i)) ha.2.2 ε hε
  exact ⟨p, ⟨hpM, hp, hsum⟩, hlt⟩

end Orthogonalization
