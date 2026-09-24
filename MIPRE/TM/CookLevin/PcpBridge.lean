/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.PcpVerifier
import MIPRE.TM.CookLevin.PcpCircuit
import MIPRE.Foundations.SAT.PcpViewTests
import MIPRE.Foundations.SAT.QuotientField

/-! # The raw verifier and its fixed typed clause polynomial -/

noncomputable section

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial

set_option maxRecDepth 4096

def fixedCircuit (D : Prog) (n T Q σ : ℕ) (x y : BitStr) : Circuit :=
  describeExact (((D, n, T, Q, σ), x, y), unary (gateCount n T Q σ))

theorem fixedCircuit_wellFormed (D : Prog) (n T Q σ : ℕ) (x y : BitStr) :
    (fixedCircuit D n T Q σ x y).WellFormed := describeExact_wellFormed _ _

theorem fixedCircuit_inputs (D : Prog) (n T Q σ : ℕ) (x y : BitStr) :
    (fixedCircuit D n T Q σ x y).inputs = 5 * (pcpParams n T Q σ).m + 5 :=
  describeExact_inputs _ _

theorem fixedCircuit_variables (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) :
    (fixedCircuit D n T Q σ x y).inputs + (fixedCircuit D n T Q σ x y).size =
      (pcpParams n T Q σ).m' := by
  rw [pcpParams_outer]
  exact describeExact_variables D n T Q σ x y hV _ (length_unary _)

theorem fixedCircuit_describes (D : Decider) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D.prog n T Q σ x y) :
    (fixedCircuit D.prog n T Q σ x y).DescribesDecider
      (pcpParams n T Q σ).m (pcpParams n T Q σ).m D n x y T :=
  describeExact_describes D n T Q σ x y hV _

def clausePolynomial {F : Type*} [Field F] (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) : MvPolynomial (Fin (pcpParams n T Q σ).m') F :=
  (pcpParams n T Q σ).circuitArith (fixedCircuit D n T Q σ x y)
    (fixedCircuit_variables D n T Q σ x y hV)

theorem pcpParams_degree_pos (n T Q σ : ℕ) : 1 ≤ (pcpParams n T Q σ).k := by
  change 1 ≤ fieldDegree n T Q σ
  unfold fieldDegree
  omega

def pcpModulus (n T Q σ : ℕ) : BitStr := shoupLowerCoeffs (unary (pcpParams n T Q σ).k)

theorem pcpModulus_length (n T Q σ : ℕ) : (pcpModulus n T Q σ).length = (pcpParams n T Q σ).k :=
  shoupLowerCoeffs_length _ (pcpParams_degree_pos n T Q σ)

theorem pcpModulus_ne_nil (n T Q σ : ℕ) : pcpModulus n T Q σ ≠ [] := by
  intro h
  have hl := pcpModulus_length n T Q σ
  have hp := pcpParams_degree_pos n T Q σ
  rw [h, List.length_nil] at hl
  omega

theorem viewFormat_typed (P : PcpParams) (E : BinField P.k) (z : Fin P.m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    ViewFormat P (E.vecBits z) (E.vecBits α ++ E.vecBits β) where
  length_z := E.length_vecBits z
  length_ev := by simp; omega
  width_z b hb := E.width_vecBits z hb
  width_ev b hb := by
    rcases List.mem_append.mp hb with h | h
    · exact E.width_vecBits α h
    · exact E.width_vecBits β h

/-- The raw circuit value decodes to the fixed typed clause polynomial. -/
theorem verifierCircuitValue_typed (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (E : BinField (pcpParams n T Q σ).k) [CharP E.carrier 2]
    (root : E.carrier)
    (hroot : root ^ (pcpModulus n T Q σ).length = BinaryPolynomial.evalBits root (pcpModulus n T Q σ))
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (z : Fin (pcpParams n T Q σ).m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin ((pcpParams n T Q σ).m' + 1) → E.carrier) :
    BinaryPolynomial.evalBits root (verifierCircuitValue
      (pcpInput D n T Q σ x y (E.vecBits z) (E.vecBits α ++ E.vecBits β))) =
      eval z (clausePolynomial D n T Q σ x y hV) := by
  let C := fixedCircuit D n T Q σ x y
  have hC := fixedCircuit_wellFormed D n T Q σ x y
  have hI := fixedCircuit_inputs D n T Q σ x y
  have hvars := fixedCircuit_variables D n T Q σ x y hV
  have hf := viewFormat_typed (pcpParams n T Q σ) E z α β
  have he := E.eval_circuitBits_vecBits C hC (pcpModulus n T Q σ) (pcpModulus_ne_nil n T Q σ)
    (pcpModulus_length n T Q σ) root hroot hencode (z ∘ Fin.cast hvars)
  rw [E.vecBits_cast] at he
  rw [verifierCircuitValue_apply, verifierModulus_apply, pcpCircuitProg_eq_fixed D n T Q σ x y _ _ hf]
  change BinaryPolynomial.evalBits root (Circuit.circuitBits (pcpModulus n T Q σ)
    ((E.vecBits z).take (5 * (pcpParams n T Q σ).m + 5))
    ((E.vecBits z).drop (5 * (pcpParams n T Q σ).m + 5)) C.gates) = _
  rw [← hI]
  exact he.trans ((pcpParams n T Q σ).eval_circuitArith C hvars z).symm

/-- With faithful coefficient decoding, the executable field tests on a typed
view are the algebraic PCP tests for its fixed clause polynomial. -/
theorem verifierTests_typed_iff (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (E : BinField (pcpParams n T Q σ).k) [CharP E.carrier 2]
    (root : E.carrier)
    (hroot : root ^ (pcpModulus n T Q σ).length = BinaryPolynomial.evalBits root (pcpModulus n T Q σ))
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (faithful : ∀ a b : BitStr, a.length = (pcpParams n T Q σ).k →
      b.length = (pcpParams n T Q σ).k →
      (BinaryPolynomial.evalBits root a = BinaryPolynomial.evalBits root b ↔ a = b))
    (z : Fin (pcpParams n T Q σ).m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin ((pcpParams n T Q σ).m' + 1) → E.carrier) :
    verifierTests (pcpInput D n T Q σ x y (E.vecBits z) (E.vecBits α ++ E.vecBits β)) = true ↔
      PcpAlgebra.TypedAccepts (clausePolynomial D n T Q σ x y hV) z (α, β) := by
  have hp := pcpModulus_length n T Q σ
  have hf := viewFormat_typed (pcpParams n T Q σ) E z α β
  rw [verifierTests_apply, verifierModulus_apply]
  apply PcpViewTests.checks_typed_iff E (pcpParams n T Q σ) root
    (pcpModulus n T Q σ) (pcpModulus_ne_nil n T Q σ) hp hroot hencode
    (fun a b ha hb => faithful a b (ha.trans hp) (hb.trans hp))
  · rw [verifierCircuitValue_apply, verifierModulus_apply,
      pcpCircuitProg_eq_fixed D n T Q σ x y _ _ hf]
    exact Circuit.length_circuitBits (fixedCircuit D n T Q σ x y) _ _ _
  · exact verifierCircuitValue_typed D n T Q σ x y hV E root hroot hencode z α β

end MIPRE.TM.CookLevin.Pad

end
