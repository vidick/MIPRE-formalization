/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundCopy
import MIPRE.Background.AnswerReduction.TypedGame
import MIPRE.Foundations.GameAdapt
import MIPRE.Foundations.SampledGame

/-!
# Soundness of answer reduction: the per-seed low-degree games

Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`, `def:ar-seed-index`).
A strategy for the typed answer-reduced game, restricted to one copy of the low-degree test at a
role pair where that copy is tested and to one seed of the input sampler, is a strategy for the
seeded CL test of the copy's parameters (`copyStrategy`): its question maps a CL question to the
typed question whose PCP half the copy's presentation computes (`Regs.embedQ`) and whose oracle
half the seed's role family gives, and its answers are parsed and read as answers of the copy's
test. The seeds are indexed by the full seed of the input sampler, as the blueprint's
`def:ar-seed-index` asks.

The per-seed failures average to at most a constant times the typed failure
(`sum_one_sub_value_copyStrategy_le`): the copy's nine type pairs are a fixed fraction of the
typed game's, and the copy's registers of a uniform PCP vector carry a uniform sample
(`Regs.sum_sampleOf`).
-/

noncomputable section

namespace MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)

/-- The seeded test's distribution is the push-forward of the uniform sample. -/
theorem clGame_μ (x y : Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y =
      SampledGame.dist (fun sm : Sample F m => sm.question hm sm.tyA)
        (fun sm : Sample F m => sm.question hm sm.tyB) x y := by
  simp only [clGame, SampledGame.dist, Finset.mul_sum]
  refine Finset.sum_congr rfl fun sm _ => ?_
  congr 1
  split_ifs <;> rfl

/-- **The seeded test's failure is the average failure over samples.** -/
theorem one_sub_value_clGame (T : TensorProductStrategy (clGame (d := d) (ldc := ldc) hm)) :
    1 - T.value = (∑ sm : Sample F m, T.failAt (sm.question hm sm.tyA) (sm.question hm sm.tyB))
      / Fintype.card (Sample F m) := by
  rw [T.one_sub_value_eq_sum_failAt]
  simp_rw [clGame_μ]
  exact SampledGame.sum_dist_mul _ _ T.failAt

end MIPRE.LIDT.CL

end
