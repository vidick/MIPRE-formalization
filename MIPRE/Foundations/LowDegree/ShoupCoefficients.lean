/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.Shoup
import MIPRE.Foundations.LowDegree.BinaryPolynomial

/-!
# Coefficient interface to Shoup's construction

The field consumers use the lower coefficients of the monic polynomial.
Keeping this adapter separate lets generic arithmetic and the future constructor
use the same coefficient algorithms without importing the Shoup interface.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost

/-- Shoup's output normalized to the `k` lower coefficients; the leading monic
coefficient is implicit. This construction retains Shoup's unary input bound. -/
noncomputable def shoupLowerCoeffs : PolyTimeFun Unary BitStr :=
  takeBitsProg.comp ((PolyTimeFun.id _).pair shoupIrreducible)

theorem shoupLowerCoeffs_length (k : ℕ) (hk : 1 ≤ k) :
    (shoupLowerCoeffs (unary k)).length = k := by
  have h := natDegree_lt_length (shoupIrreducible (unary k)) (shoupIrreducible_monic k hk)
  rw [shoupIrreducible_natDegree k hk] at h
  simp [shoupLowerCoeffs, min_eq_left (by omega : k ≤ (shoupIrreducible (unary k)).length)]

theorem shoupLowerCoeffs_poly (k : ℕ) (hk : 1 ≤ k) :
    polyOfBits (shoupLowerCoeffs (unary k) ++ [true]) = polyOfBits (shoupIrreducible (unary k)) := by
  have h := normalize_monic (shoupIrreducible (unary k)) (shoupIrreducible_monic k hk)
  rw [shoupIrreducible_natDegree k hk] at h
  simpa [shoupLowerCoeffs] using h

end MIPRE.LowDegree.BinaryPolynomial
