/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ReadChainMaps

/-! # Quantitative transport of every dual readout from Hide to Read

The outcome map is chosen before applying the tested consistency estimate.
Consequently the bound is quadratic in the path length and independent of
the size of every answer fibre.
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

theorem dual_chain_step_estimate (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val) :
    (∑ z, stateSqNorm ψ
      (((((MA (.inr (prefixChainType j i, w), 0)).map
        (reportedDual (L w) m (prefixChainType j i))).mats z).val) -
      ((((MA (.inr (prefixChainType j (i + 1), w), 0)).map
        (reportedDual (L w) m (prefixChainType j (i + 1)))).mats z).val))) ≤
      8 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have h₁ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    ψ hψ MA MB hfail (prefixChainType j i) (prefixChainType j (i + 1)) w w
    (prefixChainType_adj X Z E w j i (by omega))
    (reportedDual (L w) m (prefixChainType j i))
    (reportedDual (L w) m (prefixChainType j (i + 1)))
    (fun a b hab => prefixChainType_check_dual L X Z projectPauli D
      (fun p s => DP p s 0 0) w hL j m hm i hi hab)
  have h₂ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    ψ hψ MA MB hfail (prefixChainType j (i + 1)) (prefixChainType j (i + 1)) w w
    (TypeGraph.adj_self E X Z (.inr (prefixChainType j (i + 1), w)))
    (reportedDual (L w) m (prefixChainType j (i + 1)))
    (reportedDual (L w) m (prefixChainType j (i + 1)))
    (fun a b hab => congrArg (reportedDual (L w) m (prefixChainType j (i + 1)))
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have ht := same_side_via_common_other ψ
    (fun z => ((((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedDual (L w) m (prefixChainType j i))).mats z).val))
    (fun z => ((((MA (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedDual (L w) m (prefixChainType j (i + 1)))).mats z).val))
    (fun z => ((((MB (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedDual (L w) m (prefixChainType j (i + 1)))).mats z).val))
  linarith only [ht, h₁, h₂]

/-- Transport one fixed dual readout from its hiding level to Alice's Read. -/
theorem hiding_read_dual_chain_estimate (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) :
    (∑ z, stateSqNorm ψ
      (((((MA (QuestionType.hide w j, 0)).map
        (reportedDual (L w) j.val (.hide j))).mats z).val) -
      ((((MA (QuestionType.read w, 0)).map
        (reportedDual (L w) j.val .read)).mats z).val))) ≤
      ((ℓ - j.val : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
  let Q : ℕ → Option ((ι → F) × (ι → F)) → Matrix H H ℂ := fun i z =>
    ((((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedDual (L w) j.val (prefixChainType j i))).mats z).val)
  have hstep (i : ℕ) (hi : i < ℓ - j.val) :
      (∑ _u : Unit, (1 : ℝ) * ∑ z, stateSqNorm ψ (Q i z - Q (i + 1) z)) ≤
        8 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [Fintype.sum_unique, one_mul, Q] using
      dual_chain_step_estimate E X Z P L projectPauli D DP ψ hψ MA MB hfail
        w hL j j.val le_rfl i hi
  have hc := hiding_chain_uniform ψ (fun _ : Unit => (1 : ℝ)) (by intro; norm_num)
    (fun i _ z => Q i z) (ℓ - j.val) hstep
  simpa only [Fintype.sum_unique, one_mul, Q, prefixChainType_zero, prefixChainType_read] using hc

end MIPRE.Introspection.TypedEstimates

end
