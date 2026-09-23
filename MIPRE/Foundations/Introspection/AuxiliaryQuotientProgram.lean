/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryMaskProgram
import MIPRE.Foundations.Introspection.AuxiliaryDualKernel

/-! # The executable coordinate-independent hiding comparison -/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryBits
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial

/-- Register mask, queried matrix, and the two full-register labels. -/
def quotient : PolyTimeFun (BitStr × List BitStr × BitStr × BitStr) Bool :=
  AuxiliaryDual.rowSpaceCheck.comp ((fst.comp snd).pair
    (mask.comp (fst.pair (xorBitsProg.comp (snd.comp snd)))))

theorem quotient_correct {n : ℕ} (S : Finset (Fin n)) (L : CL.RegLinear CL.𝔽₂ S)
    (x y : Fin n → CL.𝔽₂) :
    quotient (CL.indicatorBits S, matrixBits (LinearMap.toMatrix' L.toLinearMap),
      CL.toBits x, CL.toBits y) = true ↔
      AuxiliaryDual.registerDual L x = AuxiliaryDual.registerDual L y := by
  change AuxiliaryDual.rowSpaceCheck (matrixBits (LinearMap.toMatrix' L.toLinearMap),
    mask (CL.indicatorBits S, xorBits (CL.toBits x) (CL.toBits y))) = true ↔ _
  have hx : xorBits (CL.toBits x) (CL.toBits y) = CL.toBits (x + y) := xorBits_vectorBits _ _
  rw [hx, mask_correct, AuxiliaryDual.registerDual_eq_iff]
  have ha : x - y = x + y := by
    funext i
    exact CharTwo.sub_eq_add _ _
  rw [ha]
  change AuxiliaryDual.rowSpaceCheck (matrixBits (LinearMap.toMatrix' L.toLinearMap),
    vectorBits (CL.proj S (x + y))) = true ↔ _
  have hm : (LinearMap.toMatrix' L.toLinearMap).mulVecLin = L.toLinearMap :=
    Matrix.toLin'_toMatrix' L.toLinearMap
  rw [AuxiliaryDual.rowSpaceCheck_matrix, hm]

end MIPRE.Introspection.AuxiliaryBits
end
