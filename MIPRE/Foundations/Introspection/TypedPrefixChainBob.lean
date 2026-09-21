/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedPrefixChainEstimate

/-! # Bob's reported-prefix chain

The same actual oriented tests suffice for the right-party estimate: the loop
at each earlier endpoint supplies the common Alice measurement. No symmetry
of the supplied Pauli decision predicate is required.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
  (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
  (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
  (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
  {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)

include hψ hfail

/-- The actual next edge and the earlier loop compare Bob's two prefix
measurements with the same `8 |E| ε` loss. -/
theorem prefix_chain_step_estimate_bob (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val + 1) :
    (∑ z, stateSqNorm (swapVec ψ)
      (((((MB (.inr (prefixChainType j i, w), 0)).map
        (reportedPrefix (L w) m (prefixChainType j i))).mats z).val) -
      ((((MB (.inr (prefixChainType j (i + 1), w), 0)).map
        (reportedPrefix (L w) m (prefixChainType j (i + 1)))).mats z).val))) ≤
      8 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have h₁ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    ψ hψ MA MB hfail (prefixChainType j i) (prefixChainType j (i + 1)) w w
    (prefixChainType_adj X Z E w j i hi)
    (reportedPrefix (L w) m (prefixChainType j i))
    (reportedPrefix (L w) m (prefixChainType j (i + 1)))
    (fun a b hab => prefixChainType_check L X Z projectPauli D
      (fun p s => DP p s 0 0) w hL j m hm i hi hab)
  have h₂ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    ψ hψ MA MB hfail (prefixChainType j i) (prefixChainType j i) w w
    (TypeGraph.adj_self E X Z (.inr (prefixChainType j i, w)))
    (reportedPrefix (L w) m (prefixChainType j i))
    (reportedPrefix (L w) m (prefixChainType j i))
    (fun a b hab => congrArg (reportedPrefix (L w) m (prefixChainType j i))
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have htriangle := same_side_via_common_other (swapVec ψ)
    (fun z => ((((MB (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).mats z).val))
    (fun z => ((((MB (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j (i + 1)))).mats z).val))
    (fun z => ((((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).mats z).val))
  simp only [xSqNorm_eq_snorm_sq, snorm_swapVec_aOp_sub_bOp, ← xSqNorm_eq_sq] at htriangle
  simp only [xSqNorm_eq_snorm_sq] at h₁ h₂
  linarith only [htriangle, h₁, h₂]

/-- Bob's version of the actual prefix chain, in the right-party state norm
used by conditional normalizer replacement. -/
theorem hiding_introspect_prefix_estimate_bob (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) :
    (∑ z, snorm ψ (bOp
      (((((MB (QuestionType.hide w j, 0)).map
        (reportedPrefix (L w) m (.hide j))).mats z).val) -
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) m .introspect)).mats z).val))) ^ 2) ≤
      ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
  let Q : ℕ → Option (ι → F) → Matrix K K ℂ := fun i z =>
    ((((MB (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).mats z).val)
  have hstep (i : ℕ) (hi : i < ℓ - j.val + 1) :
      (∑ _u : Unit, (1 : ℝ) * ∑ z, stateSqNorm (swapVec ψ) (Q i z - Q (i + 1) z)) ≤
        8 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [Fintype.sum_unique, one_mul, Q] using
      prefix_chain_step_estimate_bob E X Z P L projectPauli D DP ψ hψ MA MB hfail
        w hL j m hm i hi
  have hchain := hiding_chain_uniform (swapVec ψ) (fun _ : Unit => (1 : ℝ))
    (by intro; norm_num) (fun i _ z => Q i z) (ℓ - j.val + 1) hstep
  simpa only [Fintype.sum_unique, one_mul, Q, prefixChainType_zero, prefixChainType_end,
    stateSqNorm, ← norm_stateVecB, norm_stateVecB_eq_snorm] using hchain

end MIPRE.Introspection.TypedEstimates

end
