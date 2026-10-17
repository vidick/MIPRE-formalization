/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDegreeFactors.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime-power degree decomposition

This list is used only in the proof of the all-degrees constructor. The
executable constructor computes the same prime-power factors by bounded unary
arithmetic. Indices outside the prime support contribute the neutral factor one.
-/

namespace MIPRE.LowDegree.BinaryDegreeFactors

/-- Prime-power degree factors in ascending base order, including neutral factors. -/
def degreeFactors (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n + 1) => (i : ℕ) ^ n.factorization (i : ℕ))

end MIPRE.LowDegree.BinaryDegreeFactors
