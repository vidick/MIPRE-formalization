/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RegisterEPR
import MIPRE.Foundations.SampledGame
import MIPRE.Foundations.CL.Closure

/-! # Exact classical readout of an EPR register

The last step of introspection reads the two original questions from the same
uniform EPR seed. This works for arbitrary question maps, in particular for
conditionally linear maps; linearity of the complete map is not required.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

set_option linter.unusedSectionVars false

/-- The computational-basis projector onto a fibre of a question map. -/
def readout (f : I → X) (x : X) : Matrix I I ℂ :=
  diagonal fun i => if f i = x then 1 else 0

/-- Reading a function of a classical basis label is a projective measurement. -/
theorem readout_isPVM (f : I → X) : IsPVM (readout f) where
  isSelfAdjoint x := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hf : f i = x <;> simp [readout, hf]
    · simp [readout, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  idem x := by
    rw [readout, diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  sum_eq_one := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [readout, Matrix.sum_apply]
    · simp [readout, Matrix.sum_apply, hij]

/-- EPR readouts have exactly the pushforward of the common uniform seed law. -/
theorem bornProb_registerEPR_readout (f : I → X) (g : I → Y) (x : X) (y : Y) :
    bornProb (registerEPR I) (readout f x) (readout g y) = SampledGame.dist f g x y := by
  have hs : ((Real.sqrt (Fintype.card I) : ℝ)⁻¹) ^ 2 =
      (Fintype.card I : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [bornProb, readout, readout, diagonal_kronecker_diagonal, dotProduct, Complex.re_sum]
  simp only [mulVec_diagonal]
  have ht (i j : I) :
      (star (registerEPR I (i, j)) *
        (((if f i = x then (1 : ℂ) else 0) * (if g j = y then (1 : ℂ) else 0)) *
          registerEPR I (i, j))).re =
        if i = j then
          (Fintype.card I : ℝ)⁻¹ * (if f i = x ∧ g i = y then 1 else 0) else 0 := by
    by_cases hij : i = j
    · subst j
      by_cases hf : f i = x <;> by_cases hg : g i = y
      · simp only [registerEPR, hf, hg, and_self, if_true, one_mul]
        rw [Complex.star_def, Complex.conj_ofReal,
          ← Complex.ofReal_mul, Complex.ofReal_re, ← sq, hs, mul_one]
      all_goals simp [registerEPR, hf, hg]
    · simp [registerEPR, hij]
  simp only [Pi.star_apply, Fintype.sum_prod_type, ht,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [SampledGame.dist, Prod.mk.injEq, Finset.mul_sum]

/-- The computational readout is the usual coarse-grained Pauli-Z measurement. -/
theorem readout_eq_synOf {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
    (f : (ι → F) → X) (x : X) : readout f x = Weyl.synOf Weyl.wZ f x := by
  ext i j
  rw [Weyl.synOf, Matrix.sum_apply]
  simp only [Weyl.proj_wZ, Weyl.zProj_apply]
  by_cases hij : i = j
  · subst j
    by_cases hf : f i = x
    · rw [Finset.sum_eq_single_of_mem i (by simp [hf])]
      · simp [readout, hf]
      · intro z _ hzi
        simp [Ne.symm hzi]
    · have hz : ∀ z ∈ univ.filter (fun z => f z = x),
          (if i = i then if i = z then (1 : ℂ) else 0 else 0) = 0 := by
        intro z hz
        have hzi : i ≠ z := by
          intro h
          subst z
          exact hf (Finset.mem_filter.mp hz).2
        simp [hzi]
      rw [Finset.sum_eq_zero hz]
      simp [readout, hf]
  · simp [readout, hij]

/-- In a CL sampler the EPR readout law is the sampler's actual question law. -/
theorem sampled_dist_eq_clDist {F ι : Type*} [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (L R : (ι → F) → (ι → F)) (x y : ι → F) :
    SampledGame.dist L R x y = CL.clDist L R x y := by
  rw [SampledGame.dist_eq_card]
  unfold CL.clDist
  congr 2
  apply congrArg Finset.card
  ext s
  simp

end MIPRE.Introspection

end
