/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ReadChainMaps

@[expose] public section

/-! # Quantitative transport of every dual readout from Hide to Read

The outcome map is chosen before applying the tested consistency estimate.
Consequently the bound is quadratic in the path length and independent of
the size of every answer fibre.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the strategy is a pair of
POVM families in the two players' algebras, and the same-side distances are the model's
`stateSqNorm` of the first player's coarse-grained operators.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Classical
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]
variable (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
  (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
  (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
  (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
  {ε : ℝ} (hfail : 1 - Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)

include hΨ hfail

theorem dual_chain_step_estimate (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val) :
    (∑ z, Ψ.stateSqNorm
      ((((MA (.inr (prefixChainType j i, w), 0)).map
        (reportedDual (L w) m (prefixChainType j i))).op z) -
      (((MA (.inr (prefixChainType j (i + 1), w), 0)).map
        (reportedDual (L w) m (prefixChainType j (i + 1)))).op z))) ≤
      8 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have h₁ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    Ψ hΨ MA MB hfail (prefixChainType j i) (prefixChainType j (i + 1)) w w
    (prefixChainType_adj X Z E w j i (by omega))
    (reportedDual (L w) m (prefixChainType j i))
    (reportedDual (L w) m (prefixChainType j (i + 1)))
    (fun a b hab => prefixChainType_check_dual L X Z projectPauli D
      (fun p s => DP p s 0 0) w hL j m hm i hi hab)
  have h₂ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    Ψ hΨ MA MB hfail (prefixChainType j (i + 1)) (prefixChainType j (i + 1)) w w
    (TypeGraph.adj_self E X Z (.inr (prefixChainType j (i + 1), w)))
    (reportedDual (L w) m (prefixChainType j (i + 1)))
    (reportedDual (L w) m (prefixChainType j (i + 1)))
    (fun a b hab => congrArg (reportedDual (L w) m (prefixChainType j (i + 1)))
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have ht := same_side_via_common_other Ψ
    (fun z => (((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedDual (L w) m (prefixChainType j i))).op z))
    (fun z => (((MA (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedDual (L w) m (prefixChainType j (i + 1)))).op z))
    (fun z => (((MB (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedDual (L w) m (prefixChainType j (i + 1)))).op z))
  linarith only [ht, h₁, h₂]

/-- Transport one fixed dual readout from its hiding level to Alice's Read. -/
theorem hiding_read_dual_chain_estimate (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) :
    (∑ z, Ψ.stateSqNorm
      ((((MA (QuestionType.hide w j, 0)).map
        (reportedDual (L w) j.val (.hide j))).op z) -
      (((MA (QuestionType.read w, 0)).map
        (reportedDual (L w) j.val .read)).op z))) ≤
      ((ℓ - j.val : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
  let Q : ℕ → Option ((ι → F) × (ι → F)) → 𝒜 := fun i z =>
    (((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedDual (L w) j.val (prefixChainType j i))).op z)
  have hstep (i : ℕ) (hi : i < ℓ - j.val) :
      (∑ _u : Unit, (1 : ℝ) * ∑ z, Ψ.stateSqNorm (Q i z - Q (i + 1) z)) ≤
        8 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [Fintype.sum_unique, one_mul, Q] using
      dual_chain_step_estimate E X Z P L projectPauli D DP Ψ hΨ MA MB hfail
        w hL j j.val le_rfl i hi
  have hc := hiding_chain_uniform Ψ (fun _ : Unit => (1 : ℝ)) (by intro; norm_num)
    (fun i _ z => Q i z) (ℓ - j.val) hstep
  simpa only [Fintype.sum_unique, one_mul, Q, prefixChainType_zero, prefixChainType_read] using hc

end MIPRE.Introspection.TypedEstimates

end

end
