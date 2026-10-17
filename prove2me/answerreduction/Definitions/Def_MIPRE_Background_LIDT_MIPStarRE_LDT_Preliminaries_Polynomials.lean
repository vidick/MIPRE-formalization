/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/Polynomials.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial preliminaries

Packages the paper's low-individual-degree polynomial class together
with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing
multivariate polynomial theorems.

## References

* `references/ldt-paper/preliminaries.tex`, Section 3 (Preliminaries)
-/

open Finset Fintype

open scoped BigOperators

namespace MIPStarRE.LDT.Preliminaries

open MvPolynomial

/-- `\polyfunc{m}{q}{d}` from the paper's definition of low-individual-degree
polynomials. This is Mathlib's `MvPolynomial.restrictDegree` submodule. -/
noncomputable abbrev polyFunc (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.restrictDegree (Fin m) K d

/-- The uniform agreement probability of two polynomials on `K^m`, written as a
finite cardinality ratio over `K^m`. -/
noncomputable def polynomialAgreementProbability (m : ℕ) (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] (g h : MvPolynomial (Fin m) K) : ℚ≥0 :=
  #{x ∈ (Finset.univ : Finset (Fin m → K)) |
      MvPolynomial.eval x g = MvPolynomial.eval x h} /
    (Fintype.card K ^ m : ℚ≥0)

end MIPStarRE.LDT.Preliminaries
