/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal
public import MIPRE.Foundations.Introspection.Readout

@[expose] public section

/-! # The actual probability law of a CL prefix

The weight is the pushforward of the uniform computational seed. Its Born
and normalized-trace descriptions are proved, rather than supplied as extra
premises. Restriction to the actual prefix image is a normalized distribution.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

section Readout

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

/-- The law of a function of a uniform finite seed. -/
def readoutWeight (f : I → X) (x : X) : ℝ :=
  SampledGame.dist f (fun _ => ()) x ()

theorem readoutWeight_eq_card (f : I → X) (x : X) :
    readoutWeight f x = ((univ.filter (fun i => f i = x)).card : ℝ) / Fintype.card I := by
  simp only [readoutWeight, SampledGame.dist_eq_card, and_true]

theorem readoutWeight_nonneg (f : I → X) (x : X) : 0 ≤ readoutWeight f x :=
  SampledGame.dist_nonneg f (fun _ => ()) x ()

theorem sum_readoutWeight [Nonempty I] (f : I → X) : ∑ x, readoutWeight f x = 1 := by
  simpa only [readoutWeight, Fintype.sum_unique] using SampledGame.sum_dist f (fun _ => ())

theorem readout_const_unit : readout (fun _ : I => ()) () = 1 := by
  ext i j
  simp [readout]

/-- The squared norm selected by a prefix projector is its actual uniform
seed probability. -/
theorem stateSqNorm_registerEPR_readout (f : I → X) (x : X) :
    stateSqNorm (registerEPR I) (readout f x) = readoutWeight f x := by
  rw [stateSqNorm_eq_qform, (readout_isPVM f).isSelfAdjoint, (readout_isPVM f).idem]
  change bornProb (registerEPR I) (readout f x) 1 = _
  rw [← readout_const_unit, bornProb_registerEPR_readout]
  rfl

end Readout

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The actual possible outputs of the truncated CL sampler. -/
def prefixOutcomes (P : CL.CLFun F ι ℓ) (k : ℕ) : Finset (ι → F) :=
  univ.image (P.truncate k).eval

/-- The paper's prefix distribution, before restricting to its support. -/
def prefixWeight (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) : ℝ :=
  readoutWeight (P.truncate k).eval y

theorem prefixWeight_eq_card (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixWeight P k y =
      ((univ.filter (fun z => (P.truncate k).eval z = y)).card : ℝ) / Fintype.card (ι → F) :=
  readoutWeight_eq_card _ _

theorem prefixWeight_nonneg (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    0 ≤ prefixWeight P k y := readoutWeight_nonneg _ _

theorem sum_prefixWeight (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ∑ y, prefixWeight P k y = 1 := sum_readoutWeight _

theorem prefixWeight_pos_iff (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    0 < prefixWeight P k y ↔ y ∈ prefixOutcomes P k := by
  have hc : (0 : ℝ) < Fintype.card (ι → F) := by exact_mod_cast Fintype.card_pos
  rw [prefixWeight_eq_card, div_pos_iff_of_pos_right hc, Nat.cast_pos, Finset.card_pos]
  simp [prefixOutcomes, Finset.Nonempty]

theorem prefixWeight_eq_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (hy : y ∉ prefixOutcomes P k) : prefixWeight P k y = 0 := by
  have hn := (prefixWeight_pos_iff P k y).not.mpr hy
  exact le_antisymm (le_of_not_gt hn) (prefixWeight_nonneg P k y)

/-- Restricting the prefix law to attainable outputs preserves normalization. -/
theorem sum_prefixWeight_supported (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ∑ y : ↥(prefixOutcomes P k), prefixWeight P k y = 1 := by
  rw [Finset.sum_coe_sort]
  calc
    _ = ∑ y, prefixWeight P k y := Finset.sum_subset (subset_univ _) (by
      intro y _ hy
      exact prefixWeight_eq_zero P k y hy)
    _ = 1 := sum_prefixWeight P k

/-- The concrete honest prefix measurement has exactly the actual CL law. -/
theorem hidingPrefixOp_weight [Algebra (ZMod 2) F]
    (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    stateSqNorm (registerEPR (ι → F)) (Honest.hidingPrefixOp P k (some y)) =
      prefixWeight P k y := by
  rw [Honest.hidingPrefixOp_some]
  exact stateSqNorm_registerEPR_readout _ _

end MIPRE.Introspection

end

end
