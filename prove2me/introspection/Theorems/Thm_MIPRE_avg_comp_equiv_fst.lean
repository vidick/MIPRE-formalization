/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Blocks.lean (statement stub of MIPRE.avg_comp_equiv_fst);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Blocks

open MIPRE
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty γ]

theorem MIPRE.avg_comp_equiv_fst (e : α ≃ β × γ) (f : β → ℝ) :
    ∑ a : α, (Fintype.card α : ℝ)⁻¹ * f (e a).1 = ∑ b : β, (Fintype.card β : ℝ)⁻¹ * f b := by sorry
