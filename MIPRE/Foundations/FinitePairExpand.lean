/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.FinitePair
public import MIPRE.Foundations.AmplCommutant

@[expose] public section

/-!
# Finite pairs are closed under ancilla extensions and under the exchange of the players

The Pauli basis analysis applies the low-individual-degree hypothesis in the ancilla extensions
`M.expand e` of the model it works in (`QLD.soundIn_of_lidt`), and the answer-reduction and Pauli
basis analyses are stated for both orders of the players. So the class of finite pairs
(`MIPRE/Foundations/FinitePair.lean`) has to be closed under both, which this file shows
(`lem:finite-pair-expand`).

* **Extensions.** The players' operators of `M.expand e` are `X ⊗ 1_β` and `1_α ⊗ Y` for matrices
  `X` over `𝒜` and `Y` over `ℬ`. An operator commuting with every `1_α ⊗ Y` commutes with the
  register's matrix units and with `f ⊗ 1` for every operator `f` of the second player, so it is
  `X ⊗ 1_β` with entries in the commutant of the second player's operators
  (`OperatorMatrix.exists_eq_toCLM_liftLeft`), which are the first player's; and symmetrically.
  The trace of the first player's algebra is the normalized trace of the matrices,
  `τ'(X ⊗ 1) = |α|⁻¹ ∑ᵢ τ(Xᵢᵢ)`, given by the vectors `|α|^{-1/2} gₖ ⊗ eᵢ ⊗ e_{b₀}`; it is
  tracial because `τ` is, and faithful because the vectors of `τ` separate the entries.
* **The exchange of the players** swaps the two conditions.
-/

namespace MIPRE.BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-- **A finite pair with the players exchanged is a finite pair.** -/
theorem IsFinitePair.swap (h : M.IsFinitePair) : M.swap.IsFinitePair := by
  sorry

/-- **An ancilla extension of a finite pair is a finite pair** (`lem:finite-pair-expand`), for
nonempty registers. -/
theorem IsFinitePair.expand (h : M.IsFinitePair) {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β] (e : α × β → ℂ) :
    (M.expand e).IsFinitePair := by
  sorry

end MIPRE.BipartiteModel

end
