/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.Commuting
import MIPRE.Background.Repetition.Entangled
import MIPRE.Background.Repetition.TracialDensity

/-!
# Axiom audit for the direct parallel repetition theorems

The theorems proved through the vendored developments must not depend on anything beyond
the three standard axioms; this file fails to build otherwise.
-/

/--
info: 'MIPRE.Repetition.commutingOperatorValue_repeat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Repetition.commutingOperatorValue_repeat_le

/--
info: 'MIPRE.Repetition.tracialDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Repetition.tracialDensity

/--
info: 'MIPRE.Repetition.quantumValue_repeat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Repetition.quantumValue_repeat_le

-- Blueprint `lem:povm-value-eq` carries a proof-level `\leanok`, so the bridge it names is
-- guarded here beside the three theorems of the vendored development, where the imports are
-- already paid for.
/--
info: 'MIPRE.Repetition.quantumValue_eq_entangledValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Repetition.quantumValue_eq_entangledValue
