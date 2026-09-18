/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.CLGame

/-!
# The seeded-CL adapter, part 5: both tests' distributions, as counts

The reduction's remaining obligation is a push-forward bound between the two tests' question
distributions, and both are defined as sums over a `Sample` type against an indicator. So the
first thing to do is to turn each into a *count*, after which the bound is arithmetic on
cardinalities rather than on sums.

* `clGame`'s distribution is uniform over its samples, so it is the number of samples producing
  the question pair, over the total (`clGame_μ_eq`).
* `lidtGame`'s is not uniform — its three subtests are weighted `1/3` each and its diagonal
  directions carry a factor `q^{-(j+1)}` — so the best that can be said in general is that it is
  the sum of the weights of the samples producing the pair (`lidtGame_μ_eq`). That sum is a
  singleton for the point and axis-parallel shapes and a geometric series over the admissible
  `j` for the diagonal one, which is where the `q^{χ s}` against `q^{j+1}` matching of
  `planning/lidt-cl-adapter.md` lives.
-/

namespace MIPRE.LIDT.Adapter

open Finset MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]

/-- **The canonical-line test's distribution, as a sum of sample weights.** -/
theorem lidtGame_μ_eq (x y : Question F m) :
    (lidtGame F m d).μ x y
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m => s.questions = (x, y)), s.weight := by
  classical
  show ∑ s : Sample F m, s.weight * (if s.questions = (x, y) then 1 else 0) = _
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun s _ => by
    by_cases h : s.questions = (x, y)
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]

/-- **The seeded test's distribution, as a count.** It is uniform over its samples, so the
weight of a question pair is the number of samples producing it over the total. -/
theorem clGame_μ_eq (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y
      = ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y))).card : ℝ)
          / (Fintype.card (CL.Sample F m) : ℝ) := by
  classical
  show ∑ sm : CL.Sample F m, (Fintype.card (CL.Sample F m) : ℝ)⁻¹ *
    (if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0) = _
  rw [← Finset.mul_sum, Finset.sum_boole, div_eq_inv_mul]

omit [DecidableEq F] [NeZero m] in
/-- The seeded test has at least one sample, so its total is nonzero. -/
theorem card_clSample_pos : 0 < Fintype.card (CL.Sample F m) :=
  Fintype.card_pos_iff.mpr ⟨⟨.point, .point, 0, 0, 0⟩⟩

end MIPRE.LIDT.Adapter
