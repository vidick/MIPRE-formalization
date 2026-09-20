/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.ExactPadding
import MIPRE.Foundations.Cost.BinaryArithmetic

/-!
# Effective parameters for exact succinct padding

Both dimensions and the exact gate count are computed from binary parameters
in polynomial time in their bit lengths. Only the logarithmically bounded
inner dimension is expanded to unary; the much larger gate count stays binary.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Desc

abbrev ParamInput := ℕ × ℕ × ℕ × ℕ

/-- Compute the common input width in unary from the four binary parameters. -/
noncomputable def innerDimParamsU : PolyTimeFun ParamInput Unary :=
  ceilPowerProg.comp (mU (eP.comp ((fst.comp snd).pair (snd.comp (snd.comp snd)))))

theorem innerDimParamsU_length (p : ParamInput) :
    (innerDimParamsU p).length = innerDim p.2.1 p.2.2.2 := by
  simp [innerDimParamsU, innerDim, mParam]

/-- Binary computation of the outer power-of-two dimension. -/
noncomputable def outerDimProg : PolyTimeFun ParamInput ℕ :=
  let small := ap₂ addU (ap₁ (nsmulU 6) innerDimParamsU) (const (unary 5))
  let total := ap₂ addUnary (roundUpProg gatePoly) small
  ap₁ pow2P (ap₁ sizeU (ap₁ predN total))

theorem outerDimProg_apply (p : ParamInput) :
    outerDimProg p = outerDim p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp only [outerDimProg, ap₁_apply, pow2P_apply, length_sizeU, predN_apply,
    ap₂_apply, addUnary_apply, roundUpProg_apply, length_addU, length_nsmulU,
    innerDimParamsU_length, const_apply, length_unary, outerDim, ceilPower]
  congr 3
  omega

/-- Binary computation of the exact gate count. -/
noncomputable def gateCountProg : PolyTimeFun ParamInput ℕ :=
  ap₂ subUnary outerDimProg
    (ap₂ addU (ap₁ (nsmulU 5) innerDimParamsU) (const (unary 5)))

theorem gateCountProg_apply (p : ParamInput) :
    gateCountProg p = gateCount p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [gateCountProg, outerDimProg_apply, innerDimParamsU_length, gateCount]

/-- The two padded-describer parameters, with an ambient polynomial-time program. -/
noncomputable def paddingParams : PolyTimeFun ParamInput (ℕ × ℕ) :=
  (unaryToBin.comp innerDimParamsU).pair gateCountProg

theorem paddingParams_apply (p : ParamInput) :
    paddingParams p = (innerDim p.2.1 p.2.2.2, gateCount p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp [paddingParams, innerDimParamsU_length, gateCountProg_apply]

end MIPRE.TM.CookLevin.Pad
