/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SamplingRegister

/-! # Sampling supplies the Introspect-prefix rigidity input

The actual Z/Sample and Sample/Introspect tests transfer extracted Pauli-Z
rigidity to every Introspect prefix. The only coarse-graining of a distance
is between two projective measurements on opposite parties, so the loss is
independent of the seed and answer alphabets.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

section Triangle

variable {H K Y : Type*} [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y]

/-- Replacing Bob's tested observable by its extracted ideal observable. -/
theorem sampling_replace_bob (ψ : H × K → ℂ)
    (S : Y → Matrix H H ℂ) (Z Q : Y → Matrix K K ℂ) {e η : ℝ}
    (hS : ∑ y, xSqNorm ψ (S y) (Z y) ≤ e)
    (hZ : ∑ y, snorm ψ (bOp (Z y - Q y)) ^ 2 ≤ η) :
    ∑ y, xSqNorm ψ (S y) (Q y) ≤ 2 * e + 2 * η := by
  have ht := sum_snorm_sq_triangle' ψ (fun y => aOp (S y))
    (fun y => bOp (Z y)) (fun y => bOp (Q y))
  simp only [← bOp_sub, ← xSqNorm_eq_snorm_sq] at ht
  linarith only [ht, hS, hZ]

/-- Two measurements compared against the same Sample measurement are close
on Bob's own state factor. -/
theorem sampling_common_alice (ψ : H × K → ℂ)
    (S : Y → Matrix H H ℂ) (I Q : Y → Matrix K K ℂ) {e η : ℝ}
    (hI : ∑ y, xSqNorm ψ (S y) (I y) ≤ e)
    (hQ : ∑ y, xSqNorm ψ (S y) (Q y) ≤ η) :
    ∑ y, snorm ψ (bOp (I y - Q y)) ^ 2 ≤ 2 * e + 2 * η := by
  have ht := sum_snorm_sq_triangle' ψ (fun y => bOp (I y))
    (fun y => aOp (S y)) (fun y => bOp (Q y))
  have hi : (∑ y, snorm ψ (bOp (I y) - aOp (S y)) ^ 2) =
      ∑ y, xSqNorm ψ (S y) (I y) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [snorm_sub_comm, ← xSqNorm_eq_snorm_sq]
  rw [hi] at ht
  simp only [← bOp_sub, ← xSqNorm_eq_snorm_sq] at ht
  linarith only [ht, hI, hQ]

end Triangle

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The actual parsed game and an extracted Bob Pauli-Z guarantee imply every
Bob Introspect-prefix guarantee needed in hiding rigidity. The sampled seed
measurement is projective; no projectivity of the Introspect measurement and
no assumption on the answer's CL-image membership are used. -/
theorem introspect_prefix_register_rigidity_bob
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
    (j : ℕ) :
    (∑ y, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) j .introspect)).mats y).val -
          (aOp (hidingPrefixOp (L w) j y) : Matrix ((ι → F) × K) _ ℂ))) ^ 2) ≤
      4 * η + 12 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hψ : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hsample := aux_pauli_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample w Z q hq
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_pauliZ_sample E X Z w))
    sampleSeed (pauliProjection projectPauli)
    (fun a b hab => check_sample_pauliZ_seed L X Z projectPauli D
      (fun p s => DP p s 0 q) w hab)
  have hseed := sampling_replace_bob (registerState (ι → F) ξ)
    (fun z => (((MA (QuestionType.sample w, 0)).map sampleSeed).mats z).val)
    (fun z => (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val)
    (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) hsample hZ
  have hcoarse := sum_xSqNorm_fibSum_le (norm_evec_eq_one_of_unit hψ)
    (isPVM_povm_map (MA (QuestionType.sample w, 0)) hS sampleSeed)
    (readout_isPVM (some : (ι → F) → Option (ι → F))).aOp
    (Option.map ((L w).truncate j).eval)
  simp only [sampledQuestionPrefix_mapped, idealZ_prefix_fibSum] at hcoarse
  have hprefix := hcoarse.trans hseed
  have hintro := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample .introspect w w (TypeGraph.adj_sample_introspect E X Z w)
    (sampledQuestionPrefix (L w) j) (reportedPrefix (L w) j .introspect)
    (fun a b hab => check_sample_introspect_prefix L X Z projectPauli D
      (fun p s => DP p s 0 0) w hL j hab)
  have ht := sampling_common_alice (registerState (ι → F) ξ)
    (fun y => (((MA (QuestionType.sample w, 0)).map
      (sampledQuestionPrefix (L w) j)).mats y).val)
    (fun y => (((MB (QuestionType.introspect w, 0)).map
      (reportedPrefix (L w) j .introspect)).mats y).val)
    (fun y => (aOp (hidingPrefixOp (L w) j y) : Matrix ((ι → F) × K) _ ℂ))
    hintro hprefix
  exact ht.trans_eq (by ring)

end MIPRE.Introspection.TypedEstimates

end
