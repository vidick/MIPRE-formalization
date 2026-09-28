/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Corollaries
import MIPRE.Foundations.Tsirelson.UpperRE

/-!
# The commuting-operator instances: `MIP^co ⊆ coRE`, and `MIP^co = coRE` from co-soundness

The value model `ValueModel.commuting` (`ω_co`, `Foundations/ValueModel.lean`) is r.e. from
above (`ValueModel.commuting_upperRE`, blueprint `lem:valco-upper-re`, through the
Positivstellensatz certificates of `Tsirelson/UpperRE.lean`), which is the one fact about it
the generic development needs. This module instantiates that development
(`planning/mipco-track.md`, Phase 0):

* `MIPCo.isCoRE`: `MIP^co ⊆ coRE` (blueprint `lem:mipco-sub-core`), with no hypothesis —
  `MIPClass.isCoRE` at the upper semidecider, the role Lin's proof gives to the NPA hierarchy
  (`Lin25`, `lem:MIPcoincoRE`);
* `Halting.halting_reduction_commuting_of`: the halting reduction to `ω_co` (blueprint
  `thm:halting-co`) from a gap compression sound in the commuting-operator model
  (`GapCompression.Sound ValueModel.commuting`), which is `halting_reduction_upper_of`;
* `Halting.core_subset_mipco_of`, `Halting.mipco_eq_core_of`: `MIP^co = coRE` (blueprint
  `thm:mipco-eq-core`) from the same hypothesis. `MIPRE/MIPCo.lean` states them for the
  compression of the main theorem.
-/

namespace MIPRE

open Cost

/-- **`MIP^co ⊆ coRE`** (blueprint `lem:mipco-sub-core`): the complement of a language in
`MIP^co` is the preimage, under its computable map, of the set of descriptions with
`ω_co < 1`, which the upper semidecider enumerates. -/
theorem MIPCo.isCoRE {L : Set BitStr} (h : MIPCo L) : IsCoRE L :=
  MIPClass.isCoRE ValueModel.commuting_upperRE h

/-- The complement of a language in `MIP^co` is the halting set of a program of the ambient
model. -/
theorem MIPCo.exists_cosemidecider {L : Set BitStr} (h : MIPCo L) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∉ L :=
  MIPClass.exists_cosemidecider ValueModel.commuting_upperRE h

namespace Halting

variable (G : GapCompression) (U : UniversalMachine)

include U in
/-- **The halting reduction to the commuting-operator value** (blueprint `thm:halting-co`), from
a gap compression sound in the commuting-operator model: `ω_co ≤ 1/2` on machines that halt on
the empty input, `ω_co = 1` on the others. -/
theorem halting_reduction_commuting_of (hco : G.Sound .commuting) :
    ValueModel.commuting.HaltingReductionCoRE :=
  halting_reduction_upper_of G U .commuting ValueModel.commuting_upperRE hco

include U in
/-- **`coRE ⊆ MIP^co`**, from a gap compression sound in the commuting-operator model. -/
theorem core_subset_mipco_of (hco : G.Sound .commuting) {L : Set BitStr} (h : IsCoRE L) :
    MIPCo L :=
  core_subset_mipclass_of_reduction .commuting (halting_reduction_commuting_of G U hco) h

include U in
/-- **`MIP^co = coRE`** (blueprint `thm:mipco-eq-core`), from a gap compression sound in the
commuting-operator model. -/
theorem mipco_eq_core_of (hco : G.Sound .commuting) : MIPCo = IsCoRE :=
  mipclass_eq_core_of_reduction .commuting ValueModel.commuting_upperRE
    (halting_reduction_commuting_of G U hco)

end Halting

end MIPRE
