/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSampler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler

/-!
# The product of a typed sampler and a directly answered one: the presentations

The answer-reduced sampler (`sec:ar-verifier`, `ld_compiler.tex`) is the direct sum of the
oracularized sampler, whose queries are answered by a program, and the downsized PCP sampler,
whose queries a polynomial-time function answers outright. This file is the CL half of that
construction, for any two families of presentations on `𝔽₂^a` and `𝔽₂^b`:

* `prodCL L P Q` pads both to `L` levels and puts them side by side on `𝔽₂^{a + b}`, the first
  `a` coordinates for `P`;
* its three queries, in bits, are the two halves' queries concatenated (`toBits_eval_truncate_prodCL`,
  `toBits_mapOfPrefix_prodCL`, `indicatorBits_factorOfPrefix_prodCL`);
* beyond a presentation's own level its marginal is its full evaluation, its stage map zero and its
  factor space empty (`eval_truncate_of_le`, `mapOfPrefix_of_le`, `factorOfPrefix_of_le`).
-/

noncomputable section

namespace MIPRE.CL

open Finset Cost

namespace CLFun

variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ## Beyond the level -/

end CLFun

/-! ## Splitting vectors of `𝔽₂^{a + b}` -/

variable {a b : ℕ}

/-- The first `a` coordinates. -/
def leftPart (x : Fin (a + b) → 𝔽₂) : Fin a → 𝔽₂ := fun i => x (Fin.castAdd b i)

/-- The last `b` coordinates. -/
def rightPart (x : Fin (a + b) → 𝔽₂) : Fin b → 𝔽₂ := fun i => x (Fin.natAdd a i)

@[simp] theorem leftPart_append (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    leftPart (Fin.append v w) = v := by
  funext i; simp [leftPart]

@[simp] theorem rightPart_append (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    rightPart (Fin.append v w) = w := by
  funext i; simp [rightPart]

/-! ## The product presentation -/

namespace CLFun

variable {ℓa ℓb : ℕ}

/-- `P` and `Q` padded to `L` levels, side by side on `𝔽₂^{a + b}`: `P` on the first `a`
coordinates. -/
def prodCL (L : ℕ) (P : CLFun 𝔽₂ (Fin a) ℓa) (Q : CLFun 𝔽₂ (Fin b) ℓb) (ha : ℓa ≤ L)
    (hb : ℓb ≤ L) : CLFun 𝔽₂ (Fin (a + b)) L :=
  ((P.liftTo univ L ha).prod (Q.liftTo univ L hb)).reindex finSumFinEquiv

variable (L : ℕ) {P : CLFun 𝔽₂ (Fin a) ℓa} {Q : CLFun 𝔽₂ (Fin b) ℓb} (hP : P.ExactlyOn univ)
  (hQ : Q.ExactlyOn univ) (ha : ℓa ≤ L) (hb : ℓb ≤ L)

theorem sumElim_reindex (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    reindexEquiv finSumFinEquiv (Sum.elim v w) = Fin.append v w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem split_symm (x : Fin (a + b) → 𝔽₂) :
    (reindexEquiv finSumFinEquiv).symm x = Sum.elim (leftPart x) (rightPart x) := by
  funext p
  rcases p with i | i <;> rfl

end CLFun

end MIPRE.CL

end
