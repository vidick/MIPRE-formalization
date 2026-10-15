/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Machine.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Machine does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Machine

/-!
# The evaluation machine

A small-step abstract machine (CEK style) for the ambient language: a configuration is a
control (a program to evaluate, or a value being returned), an environment and a stack of
continuation frames. It is the common core of the two "universal" artifacts of the
project:

* Mathlib-computability of ambient evaluation (`Cost/Partrec.lean`): the step function,
  transported to `Data`, is primitive recursive and evaluation is its `PFun.fix`;
* the self-interpreter of the ambient model in the ambient model (route β of the
  universal-machine gate): a program implementing the step function inside a `loop`.

The machine charges the cost of each `Eval` rule at a designated step (`stepCost`), so
that the accumulated cost of a run is exactly the cost of the `Eval` derivation. The two
directions of the correspondence are `eval_steps` (a derivation yields a run of the
machine) and `eval_of_steps` (a halting run of the machine yields a derivation).
-/

namespace MIPRE.Cost

namespace Machine

theorem costSum_add (c : Cfg) (m n : ℕ) :
    costSum c (m + n) = costSum c m + costSum (step^[m] c) n := by
  induction m generalizing c with
  | zero => simp [costSum]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, costSum, ih (step c), costSum,
      Function.iterate_succ_apply]
    omega

namespace Steps

end Steps

/-! ## Forward: derivations give machine runs -/

/-! ## Backward: halting runs give derivations -/

end Machine

end MIPRE.Cost
