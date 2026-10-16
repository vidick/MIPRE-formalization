/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Toolkit.lean (solution of MIPRE.Cost.hardcode_wellScoped);
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
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost
open Polynomial
theorem _root_.solution {p : Prog} (hp : p.WellScoped 1) (d : Data) :
    (hardcode p d).WellScoped 1 :=
  ⟨⟨trivial, Nat.zero_lt_one⟩, hp.mono (by omega) _⟩
end MIPRE.Cost
