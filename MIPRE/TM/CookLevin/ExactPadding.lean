/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.Padded
import MIPRE.Foundations.SAT.GatePadding

/-!
# Exact-size padded succinct descriptions

The common input width is a power of two, and the number of input and gate
variables is a second power of two. Circuit construction consumes a unary gate
budget: the target size can be polynomial in the *value* of `Q` and `σ`, so
printing it is not polynomial in their binary encodings alone. The PCP view
will supply this budget. Parameter computation is a separate obligation.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Desc

/-- The outer power-of-two variable count, including enough spare gates. -/
noncomputable def outerDim (n T Q σ : ℕ) : ℕ :=
  ceilPower (6 * innerDim T σ + 5 + roundUp gatePoly n T Q σ)

/-- The exact number of gates. -/
noncomputable def gateCount (n T Q σ : ℕ) : ℕ :=
  outerDim n T Q σ - (5 * innerDim T σ + 5)

theorem outerDim_isPow (n T Q σ : ℕ) : ∃ j, outerDim n T Q σ = 2 ^ j := ⟨_, rfl⟩

theorem innerDim_add_bound_le_gateCount (n T Q σ : ℕ) :
    innerDim T σ + roundUp gatePoly n T Q σ ≤ gateCount n T Q σ := by
  have h := le_ceilPower (6 * innerDim T σ + 5 + roundUp gatePoly n T Q σ)
  change _ ≤ outerDim n T Q σ at h
  unfold gateCount
  omega

theorem inputs_add_gateCount (n T Q σ : ℕ) :
    5 * innerDim T σ + 5 + gateCount n T Q σ = outerDim n T Q σ := by
  have h := le_ceilPower (6 * innerDim T σ + 5 + roundUp gatePoly n T Q σ)
  change _ ≤ outerDim n T Q σ at h
  unfold gateCount
  omega

theorem gateCount_le (n T Q σ : ℕ) :
    gateCount n T Q σ ≤ 7 * innerDim T σ + 6 + 2 * roundUp gatePoly n T Q σ := by
  have h := ceilPower_le_twice (6 * innerDim T σ + 5 + roundUp gatePoly n T Q σ)
  change outerDim n T Q σ ≤ _ at h
  have he := inputs_add_gateCount n T Q σ
  omega

/-- Both dimensions have a polynomial bound in the source runtime parameter. -/
theorem outerDim_polynomial : ∃ P : Polynomial ℕ, ∀ n T Q σ,
    outerDim n T Q σ ≤ P.eval (LOf n T Q σ) := by
  obtain ⟨c, hc⟩ := innerDim_le
  refine ⟨Polynomial.C (12 * c) * (Polynomial.X + 1) + 11 +
    Polynomial.C 2 * roundPoly gatePoly, fun n T Q σ => ?_⟩
  have hi := hc T σ
  have hσ := size_le_self σ
  have hi' : innerDim T σ ≤ c * (LOf n T Q σ + 1) := by
    apply hi.trans
    apply Nat.mul_le_mul_left
    unfold LOf
    omega
  have hs := roundUp_le gatePoly n T Q σ
  have ho := ceilPower_le_twice (6 * innerDim T σ + 5 + roundUp gatePoly n T Q σ)
  change outerDim n T Q σ ≤ _ at ho
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  nlinarith

/-- Add gates up to the supplied budget. A too-small budget leaves the circuit
unchanged; it never triggers an unbounded unary expansion. -/
noncomputable def describeExact : PolyTimeFun (DescInput × Unary) Circuit :=
  let C := describe.comp fst
  let gs := snd.comp (Circuit.partsProg.comp C)
  ap₂ Circuit.padGatesProg C (ap₂ drop snd (length.comp gs))

theorem describeExact_apply (p : DescInput) (u : Unary) :
    describeExact (p, u) = Circuit.padGates (describe p) (u.length - (describe p).size) := by
  simp [describeExact, Circuit.partsProg, Circuit.size]

theorem describeExact_wellFormed (p : DescInput) (u : Unary) :
    (describeExact (p, u)).WellFormed := by
  rw [describeExact_apply]
  exact Circuit.wellFormed_padGates (describe_wellFormed p) _

theorem describeExact_size (p : DescInput) (u : Unary) (h : (describe p).size ≤ u.length) :
    (describeExact (p, u)).size = u.length := by
  rw [describeExact_apply, Circuit.padGates_size]
  omega

theorem describeExact_inputs (p : DescInput) (u : Unary) :
    (describeExact (p, u)).inputs = 5 * innerDim p.1.2.2.1 p.1.2.2.2.2 + 5 := by
  rw [describeExact_apply, Circuit.padGates_inputs, describe_apply]
  rfl

theorem describeExact_formula5 (p : DescInput) (u : Unary) (ℓ r : ℕ) :
    (describeExact (p, u)).formula5 ℓ r = (describe p).formula5 ℓ r := by
  ext c
  simp only [Circuit.formula5, Set.mem_ofPred_eq, Circuit.evalBits, describeExact_apply,
    Circuit.eval_padGates (describe_wellFormed p)]

/-- The exact-size circuit describes the same accepting answer prefixes. -/
theorem describeExact_describes (D : Decider) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D.prog n T Q σ x y) (u : Unary) :
    (describeExact (((D.prog, n, T, Q, σ), x, y), u)).DescribesDecider
      (innerDim T σ) (innerDim T σ) D n x y T := by
  unfold Circuit.DescribesDecider
  rw [describeExact_formula5]
  exact describe_describes D n T Q σ x y hV

/-- The intended budget yields exactly the advertised gate count. -/
theorem describeExact_gateCount (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (u : Unary) (hu : u.length = gateCount n T Q σ) :
    (describeExact (((D, n, T, Q, σ), x, y), u)).size = gateCount n T Q σ := by
  rw [describeExact_size, hu]
  rw [hu]
  exact (describe_size_le D n T Q σ x y hV).trans
    (by have h := innerDim_add_bound_le_gateCount n T Q σ; omega)

/-- Input and gate variables together have the exact outer power-of-two count. -/
theorem describeExact_variables (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (u : Unary) (hu : u.length = gateCount n T Q σ) :
    (describeExact (((D, n, T, Q, σ), x, y), u)).inputs +
      (describeExact (((D, n, T, Q, σ), x, y), u)).size = outerDim n T Q σ := by
  rw [describeExact_inputs, describeExact_gateCount D n T Q σ x y hV u hu]
  exact inputs_add_gateCount n T Q σ

end MIPRE.TM.CookLevin.Pad
