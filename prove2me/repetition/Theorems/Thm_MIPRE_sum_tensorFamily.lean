/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/TensorFamily.lean (statement stub of MIPRE.sum_tensorFamily);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Definitions.Def_MIPRE_Foundations_TensorFamily

open MIPRE
open Matrix
variable {k : ℕ} {ι : Type*}

theorem MIPRE.sum_tensorFamily {A : Type*} [Fintype A] (M : Fin k → A → Matrix ι ι ℂ) :
    ∑ a : Fin k → A, tensorFamily (fun i => M i (a i)) = tensorFamily fun i => ∑ a, M i a := by sorry
