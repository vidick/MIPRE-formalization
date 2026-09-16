/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.Commuting
import MIPRE.Background.Repetition.Entangled
import MIPRE.Background.Repetition.TracialDensity
import MIPRE.Background.Repetition.TensorPower
import MIPRE.Background.Repetition.Soundness
import MIPRE.Background.Repetition.Verifier

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

-- Blueprint `lem:tensor-power-pcc` (game-level completeness of direct repetition).
/--
info: 'MIPRE.tensorFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.tensorFamily

/--
info: 'MIPRE.SyncStrategy.tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.SyncStrategy.tensorPow

/--
info: 'MIPRE.SyncStrategy.value_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.SyncStrategy.value_tensorPow

/--
info: 'MIPRE.SyncStrategy.isPCC_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.SyncStrategy.isPCC_tensorPow

/--
info: 'MIPRE.SyncStrategy.tensorPowDoubled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.SyncStrategy.tensorPowDoubled

/--
info: 'MIPRE.exists_perfectPCC_repeat_doubled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.exists_perfectPCC_repeat_doubled

-- Blueprint `lem:repetition-sound-bound` (the vendored bound in the pipeline's form).
/--
info: 'MIPRE.Repetition.repConst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Repetition.repConst

/--
info: 'MIPRE.Repetition.card_answers_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Repetition.card_answers_le

/--
info: 'MIPRE.Repetition.quantumValue_repeat_le_soundBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Repetition.quantumValue_repeat_le_soundBound


-- Blueprint `thm:parallel-repetition`, inhabited (`MIPRE/Background/Repetition/Verifier.lean`).
/--
info: 'MIPRE.repetition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.repetition
