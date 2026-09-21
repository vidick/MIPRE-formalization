/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Sandwich
import MIPRE.Foundations.Distances

/-!
# Dilating a POVM strategy to a projective one

A strategy built by a rigidity argument arrives as a family of POVMs on each party's register ---
averages of sandwiches, coarse-grainings, mixtures --- while the soundness theorems take
`TensorProductStrategy`, whose measurements are projective. Naimark's theorem closes the gap: each
family of POVMs is the compression, by one question-independent isometry `ancillaEmbed d a₀`, of a
projective family on `d × A` (`exists_projective_dilation`). This file packages that for a whole
two-party strategy and records the two facts a consumer needs:

* `povmValue_extVec2`: on the twice-extended state `extVec2 ψ a₀ b₀` a strategy has the value
  of its compression on `ψ`, so the dilated projective strategy has the value of the POVM strategy
  it came from;
* `inconsistency_extVec2`: likewise for the inconsistency of two measurement families, so a
  conclusion about the dilated strategy on the extended state reads back, through
  `POVM.compress`, as a conclusion about compressions on the original state.

`ancCompress a₀` is the compression of a single matrix and `POVM.compress a₀` of a POVM; the
latter is a POVM because the isometry preserves positivity and sends the identity to the identity.
`exists_projective_dilation_povm` is Naimark for a question-indexed family of bundled POVMs.
`MIPRE.Background.LIDT.Adapter.Registers` combines these with the reindexing of that file to state
the seeded low individual degree test's soundness for a POVM strategy.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## Compression by an inert ancilla -/

section Compress

variable {d Anc : Type*} [Fintype d] [DecidableEq d] [Fintype Anc] [DecidableEq Anc]

/-- The compression of an operator on `d × Anc` by the ancilla state `|a₀⟩`. -/
def ancCompress (a₀ : Anc) (X : Matrix (d × Anc) (d × Anc) ℂ) : Matrix d d ℂ :=
  (ancillaEmbed d a₀)ᴴ * (X * ancillaEmbed d a₀)

theorem ancCompress_posSemidef (a₀ : Anc) {X : Matrix (d × Anc) (d × Anc) ℂ}
    (hX : X.PosSemidef) : (ancCompress a₀ X).PosSemidef := by
  rw [ancCompress, ← Matrix.mul_assoc]
  exact hX.conjTranspose_mul_mul_same _

theorem ancCompress_one (a₀ : Anc) :
    ancCompress a₀ (1 : Matrix (d × Anc) (d × Anc) ℂ) = 1 := by
  rw [ancCompress, Matrix.one_mul, ancillaEmbed_isometry]

theorem ancCompress_sum {ι : Type*} (a₀ : Anc) (s : Finset ι)
    (X : ι → Matrix (d × Anc) (d × Anc) ℂ) :
    ancCompress a₀ (∑ i ∈ s, X i) = ∑ i ∈ s, ancCompress a₀ (X i) := by
  simp only [ancCompress, Matrix.sum_mul, Matrix.mul_sum]

theorem ancCompress_conjTranspose (a₀ : Anc) (X : Matrix (d × Anc) (d × Anc) ℂ) :
    (ancCompress a₀ X)ᴴ = ancCompress a₀ Xᴴ := by
  rw [ancCompress, ancCompress, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

variable {A : Type*} [Fintype A]

/-- **The compression of a POVM is a POVM.** -/
def POVM.compress (a₀ : Anc) (M : POVM A (d × Anc)) : POVM A d where
  mats a := ⟨ancCompress a₀ (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, ancCompress_conjTranspose,
      ← Matrix.star_eq_conjTranspose, selfAdjoint.mem_iff.mp (M.mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      (ancCompress_posSemidef a₀ (M.posSemidef a)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, ancCompress a₀ (M.mats a).val = 1
    rw [← ancCompress_sum, POVM.sum_val, ancCompress_one]

@[simp] theorem POVM.compress_mats (a₀ : Anc) (M : POVM A (d × Anc)) (a : A) :
    ((M.compress a₀).mats a).val = ancCompress a₀ (M.mats a).val := rfl

/-- Compression commutes with relabelling the outcomes. -/
theorem POVM.map_compress {B : Type*} [Fintype B] [DecidableEq B] (a₀ : Anc) (f : A → B)
    (M : POVM A (d × Anc)) : (M.map f).compress a₀ = (M.compress a₀).map f :=
  POVM.ext' fun b => by
    rw [POVM.compress_mats, POVM.map_mats, POVM.map_mats, ancCompress_sum]
    rfl

end Compress

/-! ## The Born rule on the twice-extended state -/

section Ext

variable {dA dB Anc Bnc : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

omit [DecidableEq dA] [DecidableEq dB] in
/-- The Born probability, in the form the definitions of the value and the inconsistency use. -/
theorem bornProb_def (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    (star ψ ⬝ᵥ ((EA ⊗ₖ EB) *ᵥ ψ)).re = bornProb ψ EA EB := rfl

/-- `bornProb_extVec2`, with the compressions named. -/
theorem bornProb_extVec2_ancCompress (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (EA : Matrix (dA × Anc) (dA × Anc) ℂ) (EB : Matrix (dB × Bnc) (dB × Bnc) ℂ) :
    bornProb (extVec2 ψ a₀ b₀) EA EB
      = bornProb ψ (ancCompress a₀ EA) (ancCompress b₀ EB) :=
  bornProb_extVec2 ψ a₀ b₀ EA EB

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **A strategy on the twice-extended state has the value of its compression.** -/
theorem povmValue_extVec2 (G : Game X Y A B) (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (MA : X → POVM A (dA × Anc)) (MB : Y → POVM B (dB × Bnc)) :
    povmValue G (extVec2 ψ a₀ b₀) MA MB
      = povmValue G ψ (fun x => (MA x).compress a₀) (fun y => (MB y).compress b₀) := by
  unfold povmValue condWin
  simp only [POVM.compress_mats, bornProb_extVec2_ancCompress]

/-- **Inconsistency on the twice-extended state is inconsistency of the compressions.** -/
theorem inconsistency_extVec2 [DecidableEq A] (μ : X → ℝ) (ψ : dA × dB → ℂ) (a₀ : Anc)
    (b₀ : Bnc) (M : X → POVM A (dA × Anc)) (N : X → POVM A (dB × Bnc)) :
    inconsistency μ (extVec2 ψ a₀ b₀) M N
      = inconsistency μ ψ (fun x => (M x).compress a₀) (fun x => (N x).compress b₀) := by
  unfold inconsistency
  simp only [bornProb_def, POVM.compress_mats, bornProb_extVec2_ancCompress]

end Ext

/-! ## Naimark dilation of a POVM strategy -/

section Dilate

variable {X A d : Type*} [Fintype A] [DecidableEq A] [Fintype d] [DecidableEq d]

/-- **Naimark dilation of a question-indexed family of POVMs**: a projective family on `d × A`
whose compression by `|a₀⟩` is the given family, question by question. -/
theorem exists_projective_dilation_povm (M : X → POVM A d) (a₀ : A) :
    ∃ P : ProjectiveMeasurement X A (Matrix (d × A) (d × A) ℂ),
      ∀ x, (P.toPOVM x).compress a₀ = M x := by
  obtain ⟨P, hsa, hidem, hsum, hcomp⟩ := exists_projective_dilation a₀
    (E := fun x a => ((M x).mats a).val) (fun x a => (M x).posSemidef a)
    (fun x => POVM.sum_val (M x))
  exact ⟨⟨P, hsa, hidem, hsum⟩, fun x => POVM.ext' fun a => hcomp x a⟩

end Dilate

end MIPRE
