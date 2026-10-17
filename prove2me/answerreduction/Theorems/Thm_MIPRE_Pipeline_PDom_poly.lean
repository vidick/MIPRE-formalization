/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/PowDom.lean (statement stub of MIPRE.Pipeline.PDom.poly);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom

open MIPRE
open MIPRE.Pipeline
open MIPRE.Cost
variable {W X K : ℕ}

theorem MIPRE.Pipeline.PDom.poly (hX : 1 ≤ X) (P : Polynomial ℕ) {c m e y : ℕ} (h : PDom W X K c m e y) :
    PDom W X K ((∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i + 1) * (c + 2) ^ P.natDegree)
      (m * P.natDegree) (e * P.natDegree) (P.eval y) := by sorry
