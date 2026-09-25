/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LiehrTsirelson.Main

/-!
# Axiom audit for the `lukasliehr/MIPRE` bridge

The three terminal propositions of the vendored `Upstream/MainStatement.lean` are proved in
`Main.lean` from `MIPRE.separation`; this file fails to build if one of the proofs acquires
an axiom beyond the three standard ones. It is deliberately not among the guard files that
`scripts/lean-coverage.py` matches against the blueprint's proof-level marks: the statements
are upstream's, not the paper's, and the blueprint cites them in a remark
(`rem:liehr-statements`) rather than claiming them as nodes.
-/

/--
info: 'MIPRE.Liehr.quantitativeSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Liehr.quantitativeSeparation

/--
info: 'MIPRE.Liehr.negativeTsirelson' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Liehr.negativeTsirelson

/--
info: 'MIPRE.Liehr.gameValueSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MIPRE.Liehr.gameValueSeparation
