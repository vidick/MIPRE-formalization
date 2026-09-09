/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Soundness

/-!
# Axiom audit for the low individual degree test

The soundness theorem, proved through the vendored MIPStarRE development, must not
depend on anything beyond the three standard axioms; this file fails to build otherwise.
-/

/--
info: 'MIPRE.LIDT.lowIndividualDegree_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.LIDT.lowIndividualDegree_soundness
