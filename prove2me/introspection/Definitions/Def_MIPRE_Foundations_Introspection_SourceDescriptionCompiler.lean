/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourceDescriptionCompiler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Cost_Growth

/-! # Uniformly bounded source descriptions for polynomial-time compilers

The compiler accepts arbitrary source descriptions. Each description exceeding
the supplied binary parameter is replaced by a fixed program before compilation.
This leaves every bounded verifier unchanged and gives a uniform polynomial
output-size bound in the parameter, including at zero.
-/

noncomputable section
namespace MIPRE.Introspection.SourceDescriptionCompiler
open Cost Cost.PolyTimeFun Polynomial

abbrev Input := (Prog × Prog) × ℕ

/-- Actual program encoding size, computed in binary after a linear-size count. -/
def programSize : PolyTimeFun Prog ℕ := unaryToBin.comp (encodedSizeU Prog)

@[simp] theorem programSize_apply (p : Prog) : programSize p = esize p := by
  simp [programSize]

/-- Only an oversized description is replaced. The cutoff stays binary. -/
def clampProgram : PolyTimeFun (Prog × ℕ) Prog :=
  ite (leNat.comp ((programSize.comp fst).pair snd)) fst (const Prog.nil)

@[simp] theorem clampProgram_apply (p : Prog) (lam : ℕ) :
    clampProgram (p, lam) = if esize p ≤ lam then p else Prog.nil := by
  simp [clampProgram, PolyTimeFun.ite_apply]

/-- Clamp sampler and decider independently while retaining the parameter. -/
def clamp : PolyTimeFun Input Input :=
  ((clampProgram.comp ((fst.comp fst).pair snd)).pair
    (clampProgram.comp ((snd.comp fst).pair snd))).pair snd

@[simp] theorem clamp_apply (S D : Prog) (lam : ℕ) :
    clamp ((S, D), lam) = ((clampProgram (S, lam), clampProgram (D, lam)), lam) := rfl

variable {β : Type*} [SizedEncoding β]

/-- The final transformation is itself a single polynomial-time function. -/
def compiler (F : PolyTimeFun Input β) : PolyTimeFun Input β := F.comp clamp

end MIPRE.Introspection.SourceDescriptionCompiler
