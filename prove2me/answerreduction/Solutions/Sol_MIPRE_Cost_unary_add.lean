/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Fold.lean (solution of MIPRE.Cost.unary_add);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost
open Polynomial
theorem _root_.solution (a b : ℕ) : unary (a + b) = unary a ++ unary b := by
  rw [unary, unary, unary, List.replicate_add]
end MIPRE.Cost
