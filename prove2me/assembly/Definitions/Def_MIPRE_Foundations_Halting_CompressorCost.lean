/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/CompressorCost.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_LambdaBound
import Definitions.Def_MIPRE_Foundations_Halting_Absorb
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Theorems.Thm_MIPRE_Cost_hardcode_size

/-!
# The compressor's output is bounded: the accounting

Obligation O4, the accounting half: the verifier the compressor's output denotes is
`n`-bounded at every level `n` past a threshold depending on `G` and `U` alone — the field
`CompressorSpec.isBounded_compr` — and the parameter `λ(n)` it carries satisfies the growth
conditions `lam_ge` and `ansBound_le`.

The parameter is `λ(n) = 2 ^ (2 · size n)`, a `1` followed by zeros, so that the compressor can
write it in binary in time polynomial in `log n`; it is at least `(n + 1) ^ 2`, which is what
freezing the described verifier at index `2n + 1` needs (`Verifier.freeze_isBounded` through
`CompressorSpec.lam_ge`).

`Verifier.IsBounded n` has three clauses at every index `m ≥ 2` and a size clause, and each is
absorbed by `PolyBounded.absorb` or `PolyBounded.absorb_log` (`Halting/Absorb.lean`) once the
cost is written as a polynomially bounded function of the largest of the index, the level and
the input size:

* the sampler is `G.sampler (λ(n))`, whose dimension and running time at index `m` are
  `G.bound (m + λ(n))` (`GapCompression.sampler_dim`, `sampler_time`);
* the decider is the wrapper around `haltProg` with `(c, n, λ(n))` hardcoded, whose cost on an
  input `d` is `Prog.wrapCoreCost` (`Halting/WrapperCost.lean`) with the inner cost
  `innerBound`: the preparation (`prepBound`), the universal machine on the compressed decider,
  and the compressed decider's own time `G.bound (m + λ(n)) · (|d| + 1) ^ G.deg`
  (`GapCompression.decider_time`);
* the size is that of the compressed sampler's program, polynomial in `log n`, and of the
  wrapper's description, which carries `c` — the slack `2|c| ≤ n` of the criterion is what
  leaves room for it.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.Prog.ProgD

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The parameter -/

/-- **The parameter the output carries at level `n`**: `2 ^ (2 · size n)`. -/
def lamOf (n : ℕ) : ℕ := 2 ^ (2 * Nat.size n)

theorem size_lamOf (n : ℕ) : Nat.size (lamOf n) = 2 * Nat.size n + 1 := by
  rw [lamOf, Nat.size_pow]

theorem esize_lamOf_le (n : ℕ) : esize (lamOf n) ≤ 8 * Nat.size n + 5 := by
  have := esize_nat_le (lamOf n)
  rw [size_lamOf] at this
  omega

/-! ## The output's verifier -/

/-- The decider program the output carries: `haltProg` with `(c, n, λ)` hardcoded. -/
def outDec (c : Prog) (n lam : ℕ) : Prog := hardcode (haltProg G U) (encode (c, n, lam))

theorem esize_outDec (c : Prog) (n lam : ℕ) :
    esize (outDec G U c n lam) = esize (haltProg G U) + esize c + esize n + esize lam + 37 := by
  rw [outDec, hardcode_size]
  have : (encode (c, n, lam) : Data).size = esize c + (esize n + esize lam + 1) + 1 := rfl
  omega

/-! ## The sampler clauses -/

/-- The dimension and running-time bound of the compressed sampler at `λ(n)`, index `m`, as
a polynomially bounded function of the largest of `m` and `n`. -/
noncomputable def sampZ (z : ℕ) : ℕ := G.bound.eval (z + lamOf z)

/-! ## The size clause -/

/-- The size of the output's verifier, beyond the description `c` it carries, as a function of
`size n`. -/
noncomputable def sizeZ (s : ℕ) : ℕ :=
  G.samplerProg.timeBound.eval (8 * s + 5) + 12 * s +
    (esize (haltProg G U) + 2 * esize U.univ + wrapNodes + 43)

/-! ## The decider clause

The output's decider is the wrapper around `outDec`; its cost on an input `d` at index `m` is
`Prog.wrapCoreCost` with the inner cost `innerBound` below. Both are then bounded by a
polynomially bounded function `decZ` of the largest of the index `m`, the level `n` and the
input size `|d|`, and absorbed. -/

/-- The inner decider's cost at index `m` on an input of size `t`: for a description of size
`s` of a string of length `L`, at level `n` and parameter `lam` of size `l`. The sizes of the
binary numerals `m` and `n` appear as `4 · size + 1`, so that the bound is monotone. -/
noncomputable def innerBound (s n L lam l m t : ℕ) : ℕ :=
  3 * prepBound G U s n L l + 2 * (s + (4 * Nat.size n + 1) + l + 2) +
    3 * ((4 * Nat.size m + 1) + t + 1) +
    U.bound.eval (G.compress.timeBound.eval (fBound G U L n + l + 2) +
      ((4 * Nat.size m + 1) + t + 1) + G.bound.eval (m + lam) * (t + 1) ^ G.deg) + 15

/-! ### Monotonicity and polynomial boundedness of the bounds -/

section Bounds

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

end Bounds

/-! `PolyBounded` for each bound, with every argument the same `z`. -/

section Poly

end Poly

/-! ### The master bound, and the clause -/

section Master

/-- The size of the compressed sampler's program, in `z`. -/
noncomputable def sigZ (z : ℕ) : ℕ := G.samplerProg.timeBound.eval (8 * Nat.size z + 5)
/-- The size of the output's inner decider `outDec`, in `z`. -/
def deltaZ (z : ℕ) : ℕ :=
  esize (haltProg G U) + z + (4 * Nat.size z + 1) + (8 * Nat.size z + 5) + 37
/-- The inner cost, in `z`. -/
noncomputable def iotaZ (z : ℕ) : ℕ :=
  innerBound G U z z (z + 1) (lamOf z) (8 * Nat.size z + 5) z z
/-- `wrapHeadZ`, in `z`. -/
noncomputable def headZ (z : ℕ) : ℕ :=
  sigZ G z + (4 * Nat.size z + 1) + (encode CL.Sampler.Query.dimension : Data).size +
    (4 * sampZ G z + 1) + sampZ G z * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg +
    U.bound.eval (sigZ G z + ((4 * Nat.size z + 1) + (encode CL.Sampler.Query.dimension : Data).size + 1) +
      sampZ G z * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg) +
    (sampZ G z + 2) * ((sampZ G z + 1) * (4 * sampZ G z + 14) + 7 * (4 * sampZ G z + 1) +
      8 * sampZ G z + 90) + 10
/-- **The master bound**: `wrapCoreCost` with every atom replaced by its bound in `z`. -/
noncomputable def decZ (z : ℕ) : ℕ :=
  (60 * headZ G U z ^ 2 + 4) + 2 * (60 * (z + sampZ G z + 30) ^ 2) +
    (2 * (deltaZ G U z + (4 * Nat.size z + 1) + z + 2) +
      U.bound.eval (deltaZ G U z + ((4 * Nat.size z + 1) + z + 1) + iotaZ G U z)) + 20

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

end Master

/-! ## The output is bounded -/

/-! ## The growth of the parameter -/

/-! ## The specification, given the compressor's program -/

end MIPRE.Halting
