/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.TypedPrefixChainEstimate

@[expose] public section

/-! # Bob's reported-prefix chain

The same actual oriented tests suffice for the right-party estimate: the loop
at each earlier endpoint supplies the common Alice measurement. No symmetry
of the supplied Pauli decision predicate is required.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the right-party estimates are
the left-party ones in the exchanged model `Ψ.swap`.
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

/-- The actual next edge and the earlier loop compare Bob's two prefix
measurements with the same `8 |E| ε` loss. -/
theorem prefix_chain_step_estimate_bob (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val + 1) :
    (∑ z, Ψ.swap.stateSqNorm
      (((MB (.inr (prefixChainType j i, w), 0)).map
        (reportedPrefix (L w) m (prefixChainType j i))).op z -
      ((MB (.inr (prefixChainType j (i + 1), w), 0)).map
        (reportedPrefix (L w) m (prefixChainType j (i + 1)))).op z)) ≤
      8 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have h₁ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    Ψ hΨ MA MB hfail (prefixChainType j i) (prefixChainType j (i + 1)) w w
    (prefixChainType_adj X Z E w j i hi)
    (reportedPrefix (L w) m (prefixChainType j i))
    (reportedPrefix (L w) m (prefixChainType j (i + 1)))
    (fun a b hab => prefixChainType_check L X Z projectPauli D
      (fun p s => DP p s 0 0) w hL j m hm i hi hab)
  have h₂ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    Ψ hΨ MA MB hfail (prefixChainType j i) (prefixChainType j i) w w
    (TypeGraph.adj_self E X Z (.inr (prefixChainType j i, w)))
    (reportedPrefix (L w) m (prefixChainType j i))
    (reportedPrefix (L w) m (prefixChainType j i))
    (fun a b hab => congrArg (reportedPrefix (L w) m (prefixChainType j i))
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have htriangle := same_side_via_common_other Ψ.swap
    (fun z => ((MB (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).op z)
    (fun z => ((MB (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j (i + 1)))).op z)
    (fun z => ((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).op z)
  simp only [BipartiteModel.xSqNorm_swap] at htriangle
  linarith only [htriangle, h₁, h₂]

/-- Bob's version of the actual prefix chain, in the right-party state norm
used by conditional normalizer replacement. -/
theorem hiding_introspect_prefix_estimate_bob (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) :
    (∑ z, Ψ.snorm (Ψ.πB
      (((MB (QuestionType.hide w j, 0)).map
        (reportedPrefix (L w) m (.hide j))).op z -
      ((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) m .introspect)).op z)) ^ 2) ≤
      ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
  let Q : ℕ → Option (ι → F) → ℬ := fun i z =>
    ((MB (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).op z
  have hstep (i : ℕ) (hi : i < ℓ - j.val + 1) :
      (∑ _u : Unit, (1 : ℝ) * ∑ z, Ψ.swap.stateSqNorm (Q i z - Q (i + 1) z)) ≤
        8 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [Fintype.sum_unique, one_mul, Q] using
      prefix_chain_step_estimate_bob E X Z P L projectPauli D DP Ψ hΨ MA MB hfail
        w hL j m hm i hi
  have hchain := hiding_chain_uniform Ψ.swap (fun _ : Unit => (1 : ℝ))
    (by intro; norm_num) (fun i _ z => Q i z) (ℓ - j.val + 1) hstep
  simpa only [Fintype.sum_unique, one_mul, Q, prefixChainType_zero, prefixChainType_end,
    BipartiteModel.stateSqNorm, BipartiteModel.stateNorm, BipartiteModel.swap_toStateModel,
    BipartiteModel.swap_πA] using hchain

end MIPRE.Introspection.TypedEstimates

end

end
