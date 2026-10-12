/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineBound.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

/-!
# Size bounds along machine runs

Along the run of the evaluation machine that simulates a derivation `Eval env p r t`, every
configuration stays bounded (`CfgBound`): values have size at most `V` (where `t ≤ V` and
the initial values are at most `V`, since every value produced is the result of a
sub-derivation of cost at most `t`), environments have length at most `L + 2 t`, programs
are subterms of the initial ones, and the stack gains at most `t` frames
(`eval_steps_bound`). Consequently the data encoding of every configuration along the run
has size polynomial in the sizes of the program, the input and the cost
(`size_toData_le`). This is what bounds the cost of the self-interpreter.
-/

namespace MIPRE.Cost

namespace Machine

/-! ## Bounds on configurations -/

/-- Bounds on a frame: values of size at most `V`, an environment of length at most `L`,
a program of size at most `P`. -/
def FrameBound (V L P : ℕ) : Frame → Prop
  | .cons1 t env => esize t ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V
  | .cons2 a => a.size ≤ V
  | .let1 b env => esize b ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V
  | .loop1 b env => esize b ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V

/-- Bounds on a configuration: values of size at most `V`, environments of length at most
`L`, programs of size at most `P`, a stack of length at most `K`. -/
structure CfgBound (V L P K : ℕ) (c : Cfg) : Prop where
  ctrl_val : ∀ v, c.ctrl = .ret v → v.size ≤ V
  ctrl_prog : ∀ p, c.ctrl = .ev p → esize p ≤ P
  env_len : c.env.length ≤ L
  env_val : ∀ v ∈ c.env, v.size ≤ V
  kont_len : c.kont.length ≤ K
  frames : ∀ f ∈ c.kont, FrameBound V L P f

/-! ## Program subterms -/

/-! ## Chaining bounds along runs -/

/-! ## Size of the encoded configurations -/

/-- Size of the encoding of a configuration satisfying `CfgBound V L P K`. -/
def cfgSizeBound (V L P K : ℕ) : ℕ :=
  V + P + L * V + L + K * (V + P + L * V + L + 10) + K + 8

/-! ## Runs from the empty stack are bounded forever -/

/-! ## The number of steps of a run -/

/-! ## Cost sums -/

end Machine

end MIPRE.Cost
