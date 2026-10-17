/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean (statement stub of MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible);
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

theorem MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible [Finite K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (t : ℕ)
    (hK : Module.finrank (ZMod 2) K = 2 ^ t)
    (a : K) (ha : Irreducible (quadratic a))
    (g : (ZMod 2)[X]) (hg : g.Monic) (hd : g.natDegree = 2 ^ t)
    (hz : aeval a g = 0) :
    let : Fact (Irreducible (g.comp (quadratic (0 : ZMod 2)))) :=
      ⟨comp_quadratic_irreducible t hK a ha g hg hd hz⟩
    Irreducible (quadratic
      (AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 3 +
        AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 2)) := by sorry
