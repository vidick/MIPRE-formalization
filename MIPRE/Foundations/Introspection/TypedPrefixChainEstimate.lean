/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.TypedPrefixChain

@[expose] public section

/-! # The quantitative hiding-prefix chain in the actual typed game

Every earlier reported question prefix propagates from Hide to Introspect.
The error depends quadratically on the number of remaining chain edges and
linearly on the actual ordered-edge count, with no answer-cardinality loss.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the state is a model `Ψ`,
the measurements `MA` are in the first player's algebra and `MB` in the second's, and the
estimates are the first player's state distances `Ψ.stateSqNorm`. The model enters only through
`aux_agreement_estimate`, `same_side_via_common_other` and `hiding_chain_uniform`, each of which
takes it explicitly, so the second player's chain (`TypedPrefixChainBob.lean`) is the same argument
in the swapped model `Ψ.swap`, whose state distance `Ψ.swap.stateSqNorm` is the second player's.
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
variable
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
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

/-- The actual next path edge and the loop at its later endpoint compare
the two Alice prefix measurements with loss `8 |E| ε`. -/
theorem prefix_chain_step_estimate (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val + 1) :
    (∑ z, Ψ.stateSqNorm
      (((MA (.inr (prefixChainType j i, w), 0)).map
        (reportedPrefix (L w) m (prefixChainType j i))).op z -
      ((MA (.inr (prefixChainType j (i + 1), w), 0)).map
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
    Ψ hΨ MA MB hfail (prefixChainType j (i + 1)) (prefixChainType j (i + 1)) w w
    (TypeGraph.adj_self E X Z (.inr (prefixChainType j (i + 1), w)))
    (reportedPrefix (L w) m (prefixChainType j (i + 1)))
    (reportedPrefix (L w) m (prefixChainType j (i + 1)))
    (fun a b hab => congrArg (reportedPrefix (L w) m (prefixChainType j (i + 1)))
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have htriangle := same_side_via_common_other Ψ
    (fun z => ((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).op z)
    (fun z => ((MA (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j (i + 1)))).op z)
    (fun z => ((MB (.inr (prefixChainType j (i + 1), w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j (i + 1)))).op z)
  linarith only [htriangle, h₁, h₂]

/-- Every prefix present at Hide `j` is close to the same Introspect prefix
on Alice's side, through the actual hiding chain and its consistency loops.
Malformed answers are included as the `none` outcome throughout. -/
theorem hiding_introspect_prefix_estimate (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) :
    (∑ z, Ψ.stateSqNorm
      (((MA (QuestionType.hide w j, 0)).map
        (reportedPrefix (L w) m (.hide j))).op z -
      ((MA (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) m .introspect)).op z)) ≤
      ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
  let Q : ℕ → Option (ι → F) → 𝒜 := fun i z =>
    ((MA (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).op z
  have hstep (i : ℕ) (hi : i < ℓ - j.val + 1) :
      (∑ _u : Unit, (1 : ℝ) * ∑ z, Ψ.stateSqNorm (Q i z - Q (i + 1) z)) ≤
        8 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [Fintype.sum_unique, one_mul, Q] using
      prefix_chain_step_estimate E X Z P L projectPauli D DP Ψ hΨ MA MB hfail w hL j m hm i hi
  have hchain := hiding_chain_uniform Ψ (fun _ : Unit => (1 : ℝ)) (by intro; norm_num)
    (fun i _ z => Q i z) (ℓ - j.val + 1) hstep
  simpa only [Fintype.sum_unique, one_mul, Q, prefixChainType_zero, prefixChainType_end]
    using hchain

end MIPRE.Introspection.TypedEstimates

end

end
