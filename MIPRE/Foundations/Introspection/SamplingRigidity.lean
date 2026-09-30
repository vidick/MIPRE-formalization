/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.SamplingRegister

@[expose] public section

/-! # Sampling supplies the Introspect-prefix rigidity input

The actual Z/Sample and Sample/Introspect tests transfer extracted Pauli-Z
rigidity to every Introspect prefix. The only coarse-graining of a distance
is between two projective measurements on opposite parties, so the loss is
independent of the seed and answer alphabets.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the state is the register model
`Ξ.reg (ι → F)` of a normalized auxiliary model, and the honest Z readouts enter as `smulKron 1 _`.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
set_option linter.unusedSectionVars false

section Triangle

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {Y : Type*} [Fintype Y]

theorem sampling_replace_bob (S : Y → 𝒜) (Z Q : Y → ℬ) {e η : ℝ}
    (hS : ∑ y, Ψ.xSqNorm (S y) (Z y) ≤ e)
    (hZ : ∑ y, Ψ.snorm (Ψ.πB (Z y - Q y)) ^ 2 ≤ η) :
    ∑ y, Ψ.xSqNorm (S y) (Q y) ≤ 2 * e + 2 * η := by
  have ht := Ψ.sum_snorm_sq_triangle univ (fun y => Ψ.πA (S y))
    (fun y => Ψ.πB (Z y)) (fun y => Ψ.πB (Q y))
  simp only [← map_sub] at ht
  simp only [BipartiteModel.xSqNorm, BipartiteModel.xNorm] at hS ⊢
  linarith only [ht, hS, hZ]

theorem sampling_common_alice (S : Y → 𝒜) (I Q : Y → ℬ) {e η : ℝ}
    (hI : ∑ y, Ψ.xSqNorm (S y) (I y) ≤ e)
    (hQ : ∑ y, Ψ.xSqNorm (S y) (Q y) ≤ η) :
    ∑ y, Ψ.snorm (Ψ.πB (I y - Q y)) ^ 2 ≤ 2 * e + 2 * η := by
  have ht := Ψ.sum_snorm_sq_triangle univ (fun y => Ψ.πB (I y))
    (fun y => Ψ.πA (S y)) (fun y => Ψ.πB (Q y))
  simp only [Ψ.snorm_sub_comm (Ψ.πB (I _)) (Ψ.πA (S _))] at ht
  simp only [← map_sub] at ht
  simp only [BipartiteModel.xSqNorm, BipartiteModel.xNorm] at hI hQ
  linarith only [ht, hI, hQ]

end Triangle

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

theorem introspect_prefix_register_rigidity_bob [StarModule ℂ 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [StarProper ℬ]
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    {ε η : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVMIn (MA (QuestionType.sample w, 0)).op)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ η)
    (j : ℕ) :
    (∑ y, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) j .introspect)).op y -
          smulKron 1 (hidingPrefixOp (L w) j y))) ^ 2) ≤
      4 * η + 12 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hψ : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hsample := aux_pauli_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .sample w Z q hq
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_pauliZ_sample E X Z w))
    sampleSeed (pauliProjection projectPauli)
    (fun a b hab => check_sample_pauliZ_seed L X Z projectPauli D
      (fun p s => DP p s 0 q) w hab)
  have hseed := sampling_replace_bob (Ξ.reg (ι → F))
    (fun z => ((MA (QuestionType.sample w, 0)).map sampleSeed).op z)
    (fun z => ((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z)
    (fun z => smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z)) hsample hZ
  have hcoarse := (Ξ.reg (ι → F)).sum_xSqNorm_fibSum_le hψ
    (POVMIn.isPVMIn_map hS sampleSeed)
    (readout_isPVM (some : (ι → F) → Option (ι → F))).toIn.smulKron_one
    (Option.map ((L w).truncate j).eval)
  simp only [sampledQuestionPrefix_mapped, idealZ_prefix_fibSum] at hcoarse
  have hprefix := hcoarse.trans hseed
  have hintro := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .sample .introspect w w (TypeGraph.adj_sample_introspect E X Z w)
    (sampledQuestionPrefix (L w) j) (reportedPrefix (L w) j .introspect)
    (fun a b hab => check_sample_introspect_prefix L X Z projectPauli D
      (fun p s => DP p s 0 0) w hL j hab)
  have ht := sampling_common_alice (Ξ.reg (ι → F))
    (fun y => ((MA (QuestionType.sample w, 0)).map (sampledQuestionPrefix (L w) j)).op y)
    (fun y => ((MB (QuestionType.introspect w, 0)).map
      (reportedPrefix (L w) j .introspect)).op y)
    (fun y => smulKron 1 (hidingPrefixOp (L w) j y))
    hintro hprefix
  exact ht.trans_eq (by ring)

end MIPRE.Introspection.TypedEstimates

end

end
