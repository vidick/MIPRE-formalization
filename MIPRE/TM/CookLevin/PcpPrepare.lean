/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.PcpParameters
import MIPRE.Foundations.SAT.Pcp

/-!
# Preparing the exact circuit from a PCP view

The point list supplies the unary output budget. Thus constructing the circuit
is globally polynomial in the actual verifier input, even when the binary
parameter values would demand a much larger correctly formatted view.
-/

namespace MIPRE.TM.CookLevin.Pad

-- The nested describer program has a deep ambient-code expression.
set_option maxRecDepth 4096

open SAT Cost Cost.PolyTimeFun Desc

/-- Number of input coordinates, in unary, without expanding a binary gate count. -/
noncomputable def inputCountU : PolyTimeFun ParamInput Unary :=
  ap₂ addU (ap₁ (nsmulU 5) innerDimParamsU) (const (unary 5))

theorem inputCountU_length (p : ParamInput) :
    (inputCountU p).length = 5 * innerDim p.2.1 p.2.2.2 + 5 := by
  simp [inputCountU, innerDimParamsU_length]

/-- The point's gate-coordinate tail determines the circuit-printing budget. -/
noncomputable def gateBudgetProg : PolyTimeFun PcpInput Unary :=
  let params : PolyTimeFun PcpInput ParamInput := snd.comp (fst.comp fst)
  drop.comp ((length.comp (fst.comp snd)).pair (inputCountU.comp params))

theorem gateBudgetProg_length (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    (gateBudgetProg (pcpInput D n T Q σ x y z ev)).length =
      z.length - (5 * innerDim T σ + 5) := by
  simp [gateBudgetProg, pcpInput, inputCountU_length]

theorem gateBudgetProg_exact (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (hf : ViewFormat (pcpParams n T Q σ) z ev) :
    (gateBudgetProg (pcpInput D n T Q σ x y z ev)).length = gateCount n T Q σ := by
  rw [gateBudgetProg_length, hf.length_z]
  change 5 * innerDim T σ + 5 + gateCount n T Q σ - (5 * innerDim T σ + 5) = _
  omega

/-- The verifier's uniform circuit constructor, using the supplied view budget. -/
noncomputable def pcpCircuitProg : PolyTimeFun PcpInput Circuit :=
  describeExact.comp (fst.pair gateBudgetProg)

theorem pcpCircuitProg_apply (p : PcpInput) :
    pcpCircuitProg p = describeExact (p.1, gateBudgetProg p) := rfl

/-- For a correctly formatted view, the constructor is independent of the
coordinate values and equals the fixed exact-size describer for the specification. -/
theorem pcpCircuitProg_eq_fixed (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (hf : ViewFormat (pcpParams n T Q σ) z ev) :
    pcpCircuitProg (pcpInput D n T Q σ x y z ev) =
      describeExact (((D, n, T, Q, σ), x, y), unary (gateCount n T Q σ)) := by
  rw [pcpCircuitProg_apply]
  have hb : gateBudgetProg (pcpInput D n T Q σ x y z ev) = unary (gateCount n T Q σ) := by
    apply List.ext_getElem
    · rw [gateBudgetProg_exact D n T Q σ x y z ev hf, length_unary]
    · intro i hi hj
      exact Subsingleton.elim _ _
  rw [hb]
  rfl

theorem pcpCircuitProg_wellFormed (p : PcpInput) : (pcpCircuitProg p).WellFormed := by
  rw [pcpCircuitProg_apply]
  exact describeExact_wellFormed p.1 (gateBudgetProg p)

theorem pcpCircuitProg_inputs (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    (pcpCircuitProg (pcpInput D n T Q σ x y z ev)).inputs = (5 * (pcpParams n T Q σ).m + 5) := by
  rw [pcpCircuitProg_apply]
  exact describeExact_inputs _ _

theorem pcpCircuitProg_size (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (hV : Valid D n T Q σ x y) (hf : ViewFormat (pcpParams n T Q σ) z ev) :
    (pcpCircuitProg (pcpInput D n T Q σ x y z ev)).size = (pcpParams n T Q σ).s := by
  rw [pcpCircuitProg_apply]
  exact describeExact_gateCount D n T Q σ x y hV _ (gateBudgetProg_exact D n T Q σ x y z ev hf)

theorem pcpCircuitProg_variables (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (hV : Valid D n T Q σ x y) (hf : ViewFormat (pcpParams n T Q σ) z ev) :
    (pcpCircuitProg (pcpInput D n T Q σ x y z ev)).inputs +
      (pcpCircuitProg (pcpInput D n T Q σ x y z ev)).size = (pcpParams n T Q σ).m' := by
  rw [pcpCircuitProg_inputs, pcpCircuitProg_size D n T Q σ x y z ev hV hf]
  rfl

theorem pcpCircuitProg_describes (D : Decider) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (hV : Valid D.prog n T Q σ x y) :
    (pcpCircuitProg (pcpInput D.prog n T Q σ x y z ev)).DescribesDecider
      (pcpParams n T Q σ).m (pcpParams n T Q σ).m D n x y T := by
  rw [pcpCircuitProg_apply]
  exact describeExact_describes D n T Q σ x y hV _

/-- The field degree in unary, for the existing Shoup modulus program. -/
noncomputable def fieldDegreeU : PolyTimeFun ParamInput Unary :=
  ap₂ addU (ap₁ (nsmulU 2) (sizeU.comp outerDimProg)) (const (unary 7))

theorem fieldDegreeU_length (p : ParamInput) :
    (fieldDegreeU p).length = (pcpParams p.1 p.2.1 p.2.2.1 p.2.2.2).k := by
  simp [fieldDegreeU, pcpParams, fieldDegree, outerDimProg_apply]

theorem fieldDegreeU_apply (p : ParamInput) :
    fieldDegreeU p = unary ((pcpParams p.1 p.2.1 p.2.2.1 p.2.2.2).k) := by
  apply List.ext_getElem
  · rw [fieldDegreeU_length, length_unary]
  · intro i hi hj
    exact Subsingleton.elim _ _

end MIPRE.TM.CookLevin.Pad
