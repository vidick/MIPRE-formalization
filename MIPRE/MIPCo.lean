/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.MainTheorem
public import MIPRE.Foundations.ClassMIPCo

@[expose] public section

/-!
# `MIP^co = coRE`, conditionally on the commuting-operator soundness of compression

Lin's theorem (`Lin25`, blueprint `thm:mipco-eq-core`), with one hypothesis left open: that
the gap compression of the main theorem, `MIPRE.gapCompression`, is sound in the
commuting-operator value model (`GapCompression.Sound ValueModel.commuting`, blueprint
`def:compression-co-sound`) — the model-`co` case of the soundness clause of Lin's gap
compression theorem. Everything else is proved, once for both values, in the value-model
development (`Foundations/ValueModel.lean` and the halting reduction): the nested
compressibility criterion, the tabulation and the semidecider, the class transfer, and
`MIP^co ⊆ coRE` unconditionally (`MIPRE.MIPCo.isCoRE`). `planning/mipco-track.md` says what
discharging the hypothesis takes.

This module sits beside `MIPRE/MainTheorem.lean`, which `MIPRE/Foundations/` does not import,
because the hypothesis is about its `gapCompression`.
-/

namespace MIPRE

/-- **The halting reduction to the commuting-operator value**, given the commuting-operator
soundness of the compression of the main theorem. -/
theorem halting_reduction_commuting (hco : gapCompression.Sound .commuting) :
    ValueModel.commuting.HaltingReductionCoRE :=
  Halting.halting_reduction_commuting_of gapCompression Cost.selfUniversal hco

/-- **`coRE ⊆ MIP^co`**, given the commuting-operator soundness of compression. -/
theorem core_subset_mipco (hco : gapCompression.Sound .commuting) {L : Set Cost.BitStr}
    (h : IsCoRE L) : MIPCo L :=
  Halting.core_subset_mipclass_of_reduction .commuting (halting_reduction_commuting hco) h

/-- **`MIP^co = coRE`** (blueprint `thm:mipco-eq-core`), given the commuting-operator soundness
of compression; `MIP^co ⊆ coRE` needs no hypothesis (`MIPCo.isCoRE`). -/
theorem mipco_eq_core (hco : gapCompression.Sound .commuting) : MIPCo = IsCoRE :=
  Halting.mipclass_eq_core_of_reduction .commuting ValueModel.commuting_upperRE
    (halting_reduction_commuting hco)

end MIPRE

end
