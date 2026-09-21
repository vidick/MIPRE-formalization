/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotientFrobenius
import Mathlib.Algebra.Squarefree.Basic

/-! # Squarefree binary quotients have bijective squaring -/

namespace MIPRE.LowDegree.BinaryQuotient

variable (f : Polynomial (ZMod 2))

/-- Squarefree divisibility rules out nilpotents in the binary quotient. -/
theorem square_injective (hs : Squarefree f) :
    Function.Injective (fun x : AdjoinRoot f => x * x) := by
  intro x y h
  change x * x = y * y at h
  have hz : (x - y) ^ 2 = 0 := by
    rw [← frobeniusLinear_apply, map_sub, frobeniusLinear_apply,
      frobeniusLinear_apply, pow_two, pow_two, h, sub_self]
  obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x - y)
  apply sub_eq_zero.mp
  rw [← hg]
  apply AdjoinRoot.mk_eq_zero.mpr
  apply hs.isRadical 2 g
  apply AdjoinRoot.mk_eq_zero.mp
  rw [map_pow, hg, hz]

/-- A monic quotient is finite in its specified power-basis coordinates, so
injective squaring is bijective. No field or irreducibility assumption is used. -/
theorem square_bijective (hf : f.Monic) (hs : Squarefree f) :
    Function.Bijective (fun x : AdjoinRoot f => x * x) := by
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (coordinateEquiv f hf).symm.toEquiv
  exact ⟨square_injective f hs, Finite.surjective_of_injective (square_injective f hs)⟩

end MIPRE.LowDegree.BinaryQuotient
