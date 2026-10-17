/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Strategy.lean (statement stub of MIPRE.LIDT.Adapter.hD_axis);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}

theorem MIPRE.LIDT.Adapter.hD_axis (u : Point F m) (i : Fin m) (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.axisLine (Line.through u (Pi.single i 1))))
      (qmap hm σ c (.point u)) a b = true) :
    (lidtGame F m d).D (.axisLine (Line.through u (Pi.single i 1))) (.point u)
      (amap c (.axisLine (Line.through u (Pi.single i 1))) a) (amap c (.point u) b) = true := by sorry
