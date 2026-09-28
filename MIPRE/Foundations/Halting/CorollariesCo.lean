/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Corollaries
public import MIPRE.Foundations.Halting.ReductionCo

@[expose] public section

/-!
# `coRE ⊆ MIP^co`, hence `MIP^co = coRE`, conditionally on co-soundness

Blueprint `thm:mipco-eq-core` (`planning/mipco-track.md`, Phase 0), the commuting-operator
counterpart of `Halting/Corollaries.lean`:

* `core_subset_mipco_of_reduction`, `mipco_eq_core_of_reduction`: from the halting reduction
  to the commuting-operator value as a proposition (`HaltingReductionCommuting`), `coRE ⊆ MIP^co`
  by composing the many-one reduction of the complement of a co-r.e. language to halting on
  the empty input (`exists_code_halts_of_isRE`) with the reduction; with `MIPCo.isCoRE`,
  `MIP^co = coRE`.
* `core_subset_mipco_of`, `mipco_eq_core_of`: the same from a `GapCompression` that is sound
  for the commuting-operator value (`GapCompression.CoSound`), through
  `halting_reduction_commuting_of`.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)

/-- **`coRE ⊆ MIP^co`, given the halting reduction to the commuting-operator value**: the
complement of a co-r.e. language reduces to halting on the empty input, and the reduction
sends halting machines to `ω_co ≤ 1/2` and the others to `ω_co = 1`. -/
theorem core_subset_mipco_of_reduction (hred : HaltingReductionCommuting) {L : Set BitStr}
    (h : IsCoRE L) : MIPCo L := by
  obtain ⟨r, hr, hrL⟩ := Halting.exists_code_halts_of_isRE h
  obtain ⟨g, hg, hgap⟩ := hred
  refine ⟨fun x => g (r x), hg.comp hr, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact (hgap (r x)).2 fun hd => absurd hx ((hrL x).1 hd)
  · exact (hgap (r x)).1 ((hrL x).2 hx)

/-- **`MIP^co = coRE`, given the halting reduction to the commuting-operator value.** -/
theorem mipco_eq_core_of_reduction (hred : HaltingReductionCommuting) : MIPCo = IsCoRE :=
  funext fun _ => propext ⟨MIPCo.isCoRE, core_subset_mipco_of_reduction hred⟩

namespace Halting

variable (G : GapCompression) (U : UniversalMachine)

include U in
/-- **`coRE ⊆ MIP^co`**, from a gap compression that is sound for the commuting-operator
value. -/
theorem core_subset_mipco_of (hco : G.CoSound) {L : Set BitStr} (h : IsCoRE L) : MIPCo L :=
  core_subset_mipco_of_reduction (halting_reduction_commuting_of G U hco) h

include U in
/-- **`MIP^co = coRE`** (blueprint `thm:mipco-eq-core`), from a gap compression that is sound
for the commuting-operator value. -/
theorem mipco_eq_core_of (hco : G.CoSound) : MIPCo = IsCoRE :=
  mipco_eq_core_of_reduction (halting_reduction_commuting_of G U hco)

end Halting

end MIPRE

end
