/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Bridge.Defect

@[expose] public section

/-!
# Bridge, part 7, over models: consistency

The model counterpart of the repository's matrix bridge
`MIPRE/Background/LIDT/Bridge/Consistency.lean` (not a vendored file; it serves the tensor
instance and stays), in the port of `planning/c6b-plan.md` (milestone M14, unit M14-2).

The repository's inconsistency of two families of POVMs in a bipartite model
`M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ`,
`M.inconsistency μ P Q = ∑ₓ μ x ∑_{a ≠ b} bornProb (P^x_a, Q^x_b)`
(`MIPRE/Foundations/ModelStrategy.lean`), versus the port's two-space consistency error
`bipartiteConsError M 𝒟 A B`, an average of `max 0 (bornProb (A_tot, B_tot) − ∑ₐ bornProb (A_a,
B_a))` over a weighted distribution (`Co/Test/StrategyBiProj/Measurements.lean`). For complete
measurements, uniform distributions and a unit vector, the two agree once questions and outcomes
are matched along equivalences (`inconsistency_eq_bipartiteConsError`). The proof is the matrix
bridge's, with `ev ψ (opTensor X Y)` read as `M.bornProb X Y`: the uniform weights through
`bipartiteConsError_uniform`, each defect as its off-diagonal mass through
`qBipartiteConsDefect_eq_offDiagonal` (`Co/Bridge/Defect.lean`), and the questions and outcomes
reindexed by `Fintype.sum_equiv`.

**Departure.** The matrix statement takes a tensor-product strategy `S` and reads the defect at the
pure state `(toProjStrat S).state` of its vector. Here the state is the model `M` itself and the
strategy enters only through its unit vector, so the theorem takes `hψ : ‖M.ψ‖ = 1` in place of
`S` (a projective strategy `S : M.ProjStrat G` supplies `S.ψ_unit`); it holds for any two families
of POVMs of `M`, not only for those of a strategy for our game.

## Not ported

Every declaration of the matrix bridge is redeclared here under its name: the one theorem
`inconsistency_eq_bipartiteConsError`, with the departure above.
-/

open MIPStarRE.LDT (uniformDistribution)

noncomputable section

namespace MIPRE.LIDT.Co.Bridge

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ}

/-- **The inconsistency of two POVM families is the port's consistency error** of two complete
submeasurement families, when questions and outcomes are matched along equivalences `qe`, `e`,
the question distributions are uniform and the state is a unit vector.

Departure from the matrix statement: the unit vector `hψ` replaces the tensor-product strategy
whose pure state the matrix statement reads. -/
theorem inconsistency_eq_bipartiteConsError (hψ : ‖M.ψ‖ = 1)
    {X X' α α' : Type*} [Fintype X] [Fintype X'] [DecidableEq X'] [Nonempty X'] [Fintype α]
    [DecidableEq α] [Fintype α']
    (qe : X ≃ X') (e : α ≃ α')
    (P : X → POVMIn α 𝒜) (Q : X → POVMIn α ℬ)
    (A : IdxSubMeas X' α' 𝒜) (B : IdxSubMeas X' α' ℬ)
    (hA : ∀ x', (A x').total = 1) (hB : ∀ x', (B x').total = 1)
    (hP : ∀ x a, (P x).op a = (A (qe x)).outcome (e a))
    (hQ : ∀ x a, (Q x).op a = (B (qe x)).outcome (e a)) :
    M.inconsistency (uniform X) P Q = bipartiteConsError M (uniformDistribution X') A B := by
  classical
  have hcard : Fintype.card X = Fintype.card X' := Fintype.card_congr qe
  unfold MIPRE.BipartiteModel.inconsistency uniform
  rw [bipartiteConsError_uniform]
  conv_rhs => rw [Finset.mul_sum]
  simp only [one_div, hcard]
  refine Fintype.sum_equiv qe _ _ fun x => ?_
  congr 1
  rw [qBipartiteConsDefect_eq_offDiagonal M hψ _ _ (hA _) (hB _)]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  refine Fintype.sum_equiv e _ _ fun b => ?_
  simp only [e.injective.eq_iff, hP, hQ]

end MIPRE.LIDT.Co.Bridge

end

end
