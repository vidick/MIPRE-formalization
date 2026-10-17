/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean (statement stub of MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {d : ℕ} (hd : d ≤ Fintype.card α) :
    ∃ L : Finset α, L.card = d ∧
      ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l := by sorry
