/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Adapter.Reduction
import MIPRE.Background.LIDT.Soundness

/-!
# Axiom audit for the low individual degree test

The soundness theorem, proved through the vendored MIPStarRE development, must not
depend on anything beyond the three standard axioms; this file fails to build otherwise.

The seeded-CL adapter of `MIPRE/Background/LIDT/Adapter/` is this project's own mathematics
rather than vendored, but it lives under `MIPRE/Background/` and its guards are cheapest here,
where the imports are already paid for. `scripts/lean-coverage.py` reads all three guard files
and checks that the names guarded are exactly the names the blueprint marks with a proof-level
`\leanok`, so which file a name sits in does not change what is claimed.
-/

/--
info: 'MIPRE.LIDT.lowIndividualDegree_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.lowIndividualDegree_soundness

/-! ## The seeded-CL adapter

Blueprint `lem:lidt-cl-adapter-maps`, `lem:lidt-cl-adapter-weights`,
`lem:lidt-cl-adapter-params` and `thm:lidt-cl-soundness-one`. The headline theorem is the one
worth printing in full: it says the seeded CL theorem at `ldc = 1` rests on the vendored
canonical-line theorem and nothing else. -/

/--
info: 'MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL

/--
info: 'MIPRE.LIDT.Adapter.clSoundness_ldc_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.Adapter.clSoundness_ldc_one

/--
info: 'MIPRE.LIDT.Adapter.hD_qmap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.Adapter.hD_qmap

/--
info: 'MIPRE.LIDT.Adapter.qmap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.Adapter.qmap

/--
info: 'MIPRE.LIDT.Adapter.amap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.Adapter.amap

/--
info: 'MIPRE.LIDT.Adapter.pushforward_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.Adapter.pushforward_le

/--
info: 'MIPRE.LIDT.lidtError_le_deltaCL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.lidtError_le_deltaCL

/--
info: 'MIPRE.LIDT.deltaCL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.deltaCL

/--
info: 'MIPRE.LIDT.clK' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.clK
