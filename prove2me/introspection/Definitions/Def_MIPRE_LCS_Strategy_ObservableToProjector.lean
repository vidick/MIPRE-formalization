/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Strategy/ObservableToProjector.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable

/-!
# Conversion from Observables to Projectors

This module defines the mapping from observables (self-adjoint involutive operators)
to projector measurement systems and proves their fundamental algebraic properties.

Given an observable $O$, we define two projectors $P_0, P_1$ corresponding to
the outcomes $\{0, 1\} \subseteq \mathbb{F}_2$:
- $P_0 = \frac{1}{2}(I + O)$
- $P_1 = \frac{1}{2}(I - O)$

These projectors form a complete binary measurement system.
-/

namespace MIPRE.LCS

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

/-- Converts an observable $O$ and an outcome $a \in \{0, 1\}$ to a projector
$P = (1/2)(I + (-1)^a O)$. -/
noncomputable def observableToProjector
  (O : R) (a : ZMod 2) : R :=
  (1 / 2 : ℂ) • (1 + observableSign a • O)

end MIPRE.LCS
