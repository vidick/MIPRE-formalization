/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryRepresentation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-!
# Binary coefficient representations

The coefficient interpretation used by the public Shoup contract and by the
independent polynomial algorithms. This module does not assume that an
irreducible polynomial has already been constructed.
-/

namespace MIPRE.LowDegree

open Cost

/-- The polynomial over `𝔽₂` whose coefficient of `Tⁱ` is bit `i` of `l`, least significant
first --- the repository's little-endian bit convention (`Cost.bitsVal`, `bitsOfNat`). -/
noncomputable def polyOfBits (l : List Bool) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range l.length, Polynomial.monomial i (if l.getD i false then 1 else 0)

namespace BinaryPolynomial

end BinaryPolynomial

end MIPRE.LowDegree
