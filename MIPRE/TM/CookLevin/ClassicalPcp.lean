/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.PcpBridge

/-!
# The effective classical PCP for deciders

The complete inhabitant uses Shoup's existing irreducible-polynomial contract.
Field elements have the polynomial-basis coefficient representation; the later
effective self-dual normal basis remains a separate algorithmic construction.
-/

noncomputable section

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost LowDegree

set_option maxRecDepth 4096

def parameterField (n T Q σ : ℕ) : BinField (pcpParams n T Q σ).k :=
  shoupAdmissibleField (pcpParams n T Q σ).k (pcpParams_odd n T Q σ)

instance parameterField_charP (n T Q σ : ℕ) : CharP (parameterField n T Q σ).carrier 2 :=
  shoupBinField_charP _ (pcpParams_degree_pos n T Q σ)

/-- On every low-degree proof view, raw acceptance is exactly the typed algebraic test. -/
theorem verifyPcp_rawView_iff (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y)
    (pf : PcpProof (pcpParams n T Q σ) (parameterField n T Q σ).carrier)
    (z : Fin (pcpParams n T Q σ).m' → (parameterField n T Q σ).carrier) :
    verifyPcp (pcpInput D n T Q σ x y
      (pf.rawView (parameterField n T Q σ) z).1 (pf.rawView (parameterField n T Q σ) z).2) = true ↔
      PcpAlgebra.TypedAccepts (clausePolynomial D n T Q σ x y hV) z (pf.ev z) := by
  have hf := viewFormat_rawView (parameterField n T Q σ) rfl pf z
  rw [verifyPcp_true_iff]
  simp only [hV, hf, true_and]
  exact verifierTests_typed_iff D n T Q σ x y hV (parameterField n T Q σ)
    (shoupRoot _ (pcpParams_degree_pos n T Q σ))
    (shoupRoot_equation _ (pcpParams_degree_pos n T Q σ))
    (shoupRoot_eval_toBits _ (pcpParams_degree_pos n T Q σ))
    (shoupRoot_eval_eq_iff _ (pcpParams_degree_pos n T Q σ)) z (pf.ev z).1 (pf.ev z).2

/-- Every accepted pair of answer prefixes admits the required raw PCP proof. -/
theorem classicalPcp_completeness (D : Decider) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D.prog n T Q σ x y) (ap bp : BitStr)
    (hap : ap.length ≤ T) (hbp : bp.length ≤ T) (hacc : D.AcceptsWithin n x y ap bp T) :
    ∃ pf : PcpProof (pcpParams n T Q σ) (parameterField n T Q σ).carrier,
      pf.g 0 = ldEnc (answerVec _ (pcpParams n T Q σ).m ap) ∧
      pf.g 1 = ldEnc (answerVec _ (pcpParams n T Q σ).m bp) ∧
      ∀ z, verifyPcp (pcpInput D.prog n T Q σ x y
        (pf.rawView (parameterField n T Q σ) z).1 (pf.rawView (parameterField n T Q σ) z).2) = true := by
  obtain ⟨pf, h₀, h₁, hv⟩ := (pcpParams n T Q σ).completeness_of_describes
    (F := (parameterField n T Q σ).carrier)
    (fixedCircuit D.prog n T Q σ x y) (fixedCircuit_wellFormed D.prog n T Q σ x y)
    (fixedCircuit_inputs D.prog n T Q σ x y) (fixedCircuit_variables D.prog n T Q σ x y hV)
    D n T x y ap bp (fixedCircuit_describes D n T Q σ x y hV) hap hbp hacc
  refine ⟨pf, h₀, h₁, fun z => ?_⟩
  exact (verifyPcp_rawView_iff D.prog n T Q σ x y hV pf z).mpr (hv z)

/-- Majority acceptance of any low-degree raw PCP proof decodes to accepted
answer prefixes and identifies both entire padded answer tapes. -/
theorem classicalPcp_soundness (D : Decider) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D.prog n T Q σ x y)
    (pf : PcpProof (pcpParams n T Q σ) (parameterField n T Q σ).carrier)
    (hmajority : (pcpParams n T Q σ).q ^ (pcpParams n T Q σ).m' <
      2 * (Finset.univ.filter
        (fun z : Fin (pcpParams n T Q σ).m' → (parameterField n T Q σ).carrier =>
          verifyPcp (pcpInput D.prog n T Q σ x y
            (pf.rawView (parameterField n T Q σ) z).1 (pf.rawView (parameterField n T Q σ) z).2) = true)).card) :
    ∃ ap bp : BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧ D.AcceptsWithin n x y ap bp T ∧
      coded (pf.g 0) = answerVec _ (pcpParams n T Q σ).m ap ∧
      coded (pf.g 1) = answerVec _ (pcpParams n T Q σ).m bp := by
  let S := Finset.univ.filter
    (fun z : Fin (pcpParams n T Q σ).m' → (parameterField n T Q σ).carrier =>
      verifyPcp (pcpInput D.prog n T Q σ x y
        (pf.rawView (parameterField n T Q σ) z).1 (pf.rawView (parameterField n T Q σ) z).2) = true)
  have hcard : Fintype.card (parameterField n T Q σ).carrier = (pcpParams n T Q σ).q :=
    (parameterField n T Q σ).card_carrier
  apply (pcpParams n T Q σ).soundness_of_describes
    (fixedCircuit D.prog n T Q σ x y) (fixedCircuit_wellFormed D.prog n T Q σ x y)
    (fixedCircuit_inputs D.prog n T Q σ x y) (fixedCircuit_variables D.prog n T Q σ x y hV)
    D n T x y (fixedCircuit_describes D n T Q σ x y hV) pf
    (by rw [hcard]; exact pcpParams_field_large n T Q σ) S
  · intro z hz
    exact (verifyPcp_rawView_iff D.prog n T Q σ x y hV pf z).mp (Finset.mem_filter.mp hz).2
  · rw [hcard]
    exact hmajority

set_option maxHeartbeats 800000 in
/-- The bespoke effective classical PCP theorem, with no additional proof assumptions. -/
def classicalPcpDecider : PcpDecider where
  params := pcpParams
  fld := shoupAdmissibleField
  verify := verifyPcp
  paramsProg := pcpParamsProg
  paramsProg_eq := pcpParamsProg_apply
  odd_k := pcpParams_odd
  two_mul_le := fun _ T _ σ => two_mul_le_innerDim T σ
  m'_isPow := fun n T Q σ => by rw [pcpParams_outer]; exact outerDim_isPow n T Q σ
  m'_dvd_q := pcpParams_outer_dvd
  m_isPow := fun _ T _ σ => innerDim_isPow T σ
  m_dvd_q := pcpParams_inner_dvd
  reject_invalid := verifyPcp_reject_invalid
  time_le := verifyPcp_time_le
  completeness := classicalPcp_completeness
  soundness := classicalPcp_soundness

end MIPRE.TM.CookLevin.Pad

end
