/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean (statement stub of MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt {α : Type*} [Fintype α] [DecidableEq α]
    (L : Finset α)
    {f : α → ℝ}
    {d : ℕ} {ζ : ℝ}
    (hL_card : L.card = d)
    (hcard_gt : d < Fintype.card α)
    (hr_bound : (Fintype.card α : ℝ) ≤ (1 + 2 * Real.sqrt ζ) * d)
    (hf_ordering : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l)
    (htotal : (∑ x, f x) ≤ 1 + 2 * Real.sqrt ζ)
    (hζ_nonneg : 0 ≤ ζ)
    (hζ_le : ζ ≤ 1 / 4) :
    (∑ s ∈ (Lᶜ : Finset α), f s) ≤ 4 * Real.sqrt ζ := by sorry
