/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Orthonormalization.FinitePairOrtho
public import MIPRE.Foundations.DyadicPair

@[expose] public section

/-!
# Orthonormalization in a dyadic pair

The form of de la Salle's Theorem 1.2 that the orthonormalization sites of the C6b port call: in a
dyadic pair (`BipartiteModel.IsDyadicPair`, `MIPRE/Foundations/DyadicPair.lean`) neither player's
operators contain a nonzero abelian projection (Theorem K′ of `reports/c6b-paper-proofs.md`, §3),
which is the hypothesis `hII` of `povm_orthogonalization_finitePair`. So a POVM of either player's
algebra, nearly projective at the model's unit state, is close to a projective measurement of that
algebra, with no further hypothesis (`povm_orthogonalization_dyadicPair`, and
`povm_orthogonalization_dyadicPairB` for the second player, through the exchange of the players).
-/

namespace MIPRE.Orthonormalization

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- **Orthonormalization in a dyadic pair** (`cor:orthonormalization-dyadic-pair`): a POVM `P` of
the first player's algebra of a dyadic pair with `∑ₐ ‖π(πA(Pₐ)) ψ‖² > 1 - ε` at the model's unit
state is within `∑ₐ ‖π(πA(Pₐ - Qₐ)) ψ‖² < 9ε` of a projective measurement `Q` of that algebra. The
first player's operators contain no nonzero abelian projection
(`BipartiteModel.IsDyadicPair.eq_zero_of_abelianA`), so `povm_orthogonalization_finitePair`
applies. -/
theorem povm_orthogonalization_dyadicPair [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (M : BipartiteModel 𝒞 𝒜 ℬ) (hM : M.IsDyadicPair) (hψ : ‖M.ψ‖ = 1)
    {Λ : Type*} [Fintype Λ] (P : POVMIn Λ 𝒜) (ε : ℝ)
    (hε : 1 - ε < ∑ a, ‖M.π (M.πA (P.op a)) M.ψ‖ ^ 2) :
    ∃ Q : Λ → 𝒜, IsPVMIn Q ∧ ∑ a, ‖M.π (M.πA (P.op a - Q a)) M.ψ‖ ^ 2 < 9 * ε :=
  povm_orthogonalization_finitePair M hM.isFinitePair hψ (fun _ hr => hM.eq_zero_of_abelianA hr)
    P ε hε

/-- **Orthonormalization in a dyadic pair, for the second player**
(`cor:orthonormalization-dyadic-pair`): a POVM `P` of the second player's algebra of a dyadic pair
with `∑_b ‖π(πB(P_b)) ψ‖² > 1 - ε` at the model's unit state is within
`∑_b ‖π(πB(P_b - Q_b)) ψ‖² < 9ε` of a projective measurement `Q` of that algebra:
`povm_orthogonalization_dyadicPair` for the model with the players exchanged. -/
theorem povm_orthogonalization_dyadicPairB [PartialOrder ℬ] [StarOrderedRing ℬ]
    (M : BipartiteModel 𝒞 𝒜 ℬ) (hM : M.IsDyadicPair) (hψ : ‖M.ψ‖ = 1)
    {Λ : Type*} [Fintype Λ] (P : POVMIn Λ ℬ) (ε : ℝ)
    (hε : 1 - ε < ∑ b, ‖M.π (M.πB (P.op b)) M.ψ‖ ^ 2) :
    ∃ Q : Λ → ℬ, IsPVMIn Q ∧ ∑ b, ‖M.π (M.πB (P.op b - Q b)) M.ψ‖ ^ 2 < 9 * ε :=
  povm_orthogonalization_dyadicPair M.swap hM.swap hψ P ε hε

end MIPRE.Orthonormalization

end
