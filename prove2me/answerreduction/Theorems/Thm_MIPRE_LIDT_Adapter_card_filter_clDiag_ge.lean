/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (statement stub of MIPRE.LIDT.Adapter.card_filter_clDiag_ge);
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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]

theorem MIPRE.LIDT.Adapter.card_filter_clDiag_ge (hm : m ∣ Fintype.card F) (xp : Point F m) (s₀ : F)
    (w : Point F m) (hw : ∀ k : Fin m, (k : ℕ) < ((chi hm s₀ : ℕ)) → w k = 0) :
    Fintype.card F ^ ((chi hm s₀ : ℕ))
      ≤ (Finset.univ.filter (fun sm : CL.Sample F m =>
          (sm.question hm sm.tyA, sm.question hm sm.tyB)
            = ((CL.Question.dline (rep w xp) s₀ w : CL.Question F m),
                CL.Question.point xp))).card := by sorry
