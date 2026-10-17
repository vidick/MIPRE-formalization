/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean (statement stub of MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryArtinSchreier
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]

theorem MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    Irreducible (quadratic
      (algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a))) := by sorry
