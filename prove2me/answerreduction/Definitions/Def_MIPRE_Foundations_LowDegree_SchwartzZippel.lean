/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SchwartzZippel.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

/-!
# The Schwartz–Zippel lemma, in the form the low-degree machinery uses

Blueprint `lem:schwartz-zippel`: two *unequal* polynomials `f, g : 𝔽_q^m → 𝔽_q` of total
degree at most `d` agree at a uniformly random point with probability at most `d / q`.

Mathlib proves the lemma for a single nonzero polynomial and a product of arbitrary finite
subsets (`MvPolynomial.schwartz_zippel_totalDegree`, `schwartz_zippel_sum_degreeOf`).
Everything here is the specialization the paper and the blueprint actually quote:

* the subsets are all of `F`, so the denominator is `q ^ m` rather than `∏ #(S i)`;
* the event is `f = g` rather than `f - g = 0`;
* the bound is stated over `ℝ`, which is where the low-degree machinery's error terms live.

Three forms, because three different consumers want three different shapes:

* `prob_agree_le_totalDegree` — the blueprint's statement, a probability over `ℝ`;
* `prob_agree_le_individualDegree` — the individual-degree variant the blueprint asks for
  alongside it (`m * d / q`, since a polynomial of individual degree `d` in `m` variables
  has total degree at most `m * d`, and this route avoids that lossy step);
* `card_agree_le_of_natDegree` — the univariate case as a count rather than a probability,
  which is the form `lem:lidt-sync-transfer` uses ("two distinct univariate polynomials of
  degree `d` agree at no more than `d` of the `q` points").

The `ℚ≥0`-valued intermediate is kept private: it is Mathlib's shape, not ours.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- The points of `𝔽_q^m` at which two polynomials agree. -/
def agree (f g : MvPolynomial (Fin m) F) : Finset (Fin m → F) :=
  {x ∈ univ | eval x f = eval x g}

@[simp] theorem mem_agree {f g : MvPolynomial (Fin m) F} {x : Fin m → F} :
    x ∈ agree f g ↔ eval x f = eval x g := by
  simp [agree]

/-- `agree f g` is the zero set of `f - g`, in the shape Mathlib's lemma states. -/
theorem agree_eq_filter (f g : MvPolynomial (Fin m) F) :
    agree f g = {x ∈ Fintype.piFinset fun _ : Fin m => (univ : Finset F) | eval x (f - g) = 0} := by
  ext x
  simp [agree, sub_eq_zero]

end MIPRE.LowDegree

end
