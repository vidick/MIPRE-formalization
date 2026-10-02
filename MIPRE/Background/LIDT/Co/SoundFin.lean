/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.FinModel
public import MIPRE.Background.LIDT.Co.Bridge.Main
public import MIPRE.Background.LIDT.Co.Chain.Simultaneous

@[expose] public section

/-!
# The seeded CL test is sound in every dyadic pair

The end of the commuting-operator port of the low-individual-degree test (`planning/c6b-plan.md`,
milestone M14): `MIPRE.LIDT.Simul.SoundFin` (blueprint `def:lidt-sound-fin`), the target of Phase 6
of `planning/mipco-track.md`, holds. In a dyadic pair `M`, the canonical-line theorem holds
(`MIPRE.LIDT.Co.Bridge.soundLidtIn_of_isDyadicPair`, through the port's main theorem
`MIPRE.LIDT.Co.Test.mainFormal`), and the canonical-line theorem in `M` gives the simultaneous
contract `SoundIn M` (`MIPRE.LIDT.Co.Chain.soundIn_of_soundLidtIn`).

This is a module of its own, rather than a theorem of `FinModel.lean`, because `FinModel.lean` is
imported by the consumers of the hypothesis (answer reduction, the Pauli basis test), which do not
need the port.

## Not ported

This file has no vendored counterpart: the vendored tree proves soundness for tensor-product
strategies only, and its consumer is `MIPRE.LIDT.Simul.soundIn_tensor`.

## New here

- `MIPRE.LIDT.Simul.soundFin`: `SoundFin`.
-/

namespace MIPRE.LIDT.Simul

/-- **The seeded CL test is sound in every dyadic pair** (blueprint `thm:lidt-sound-fin`): for
every bipartite model `M` whose two algebras are each other's commutants, carry faithful tracial
states and have unital dyadic matrix units, `SoundIn M`. The canonical-line theorem holds in `M`
(`Co.Bridge.soundLidtIn_of_isDyadicPair`, the commuting-operator port of the vendored soundness
proof), and it gives the simultaneous contract (`Co.Chain.soundIn_of_soundLidtIn`). -/
theorem soundFin : SoundFin := fun _ hM =>
  Co.Chain.soundIn_of_soundLidtIn (Co.Bridge.soundLidtIn_of_isDyadicPair hM)

end MIPRE.LIDT.Simul

end
