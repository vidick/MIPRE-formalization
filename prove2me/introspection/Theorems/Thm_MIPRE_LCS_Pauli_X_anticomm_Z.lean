/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Pauli.lean (statement stub of MIPRE.LCS.Pauli.X_anticomm_Z);
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
import Definitions.Def_MIPRE_LCS_Pauli

open MIPRE
open MIPRE.LCS
open MIPRE.LCS.Pauli
open Matrix
open scoped Kronecker

theorem MIPRE.LCS.Pauli.X_anticomm_Z : X * Z = -(Z * X) := by sorry
