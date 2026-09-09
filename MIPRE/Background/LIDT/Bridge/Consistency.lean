/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Bridge.Strategy
import MIPRE.Background.LIDT.Bridge.Defect

/-!
# Bridge, part 7: consistency

Our `inconsistency μ ψ M N = 𝔼_{x∼μ} ∑_{a≠b} ⟨ψ| M^x_a ⊗ N^x_b |ψ⟩` for families of
POVMs, versus MIPStarRE's `bipartiteConsError ψ 𝒟 A B`, an average of
`max 0 (⟨A_tot ⊗ B_tot⟩ − ∑ₐ ⟨A_a ⊗ B_a⟩)` over a weighted distribution. For complete
measurements, uniform distributions, and the pure state of a strategy, the two agree once
questions and outcomes are matched along equivalences (`inconsistency_eq_bipartiteConsError`).
-/

open MIPStarRE.LDT (QuantumState ev opTensor qBipartiteConsDefect bipartiteConsError
  uniformDistribution SubMeas IdxSubMeas)
open Matrix

noncomputable section

namespace MIPRE.LIDT.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- Our inconsistency of two POVM families agrees with MIPStarRE's consistency error of
two complete submeasurement families, when questions and outcomes are matched along
equivalences `qe`, `e` and the state is the pure state of a strategy. -/
theorem inconsistency_eq_bipartiteConsError (S : TensorProductStrategy (lidtGame F m d))
    {X X' α α' : Type*} [Fintype X] [Fintype X'] [DecidableEq X'] [Nonempty X'] [Fintype α]
    [DecidableEq α] [Fintype α']
    (qe : X ≃ X') (e : α ≃ α')
    (M : X → POVM α (Fin S.dA)) (N : X → POVM α (Fin S.dB))
    (A : IdxSubMeas X' α' (Fin S.dA)) (B : IdxSubMeas X' α' (Fin S.dB))
    (hA : ∀ x', (A x').total = 1) (hB : ∀ x', (B x').total = 1)
    (hM : ∀ x a, ((M x).mats a).val = (A (qe x)).outcome (e a))
    (hN : ∀ x a, ((N x).mats a).val = (B (qe x)).outcome (e a)) :
    inconsistency (uniform X) S.ψ M N =
      bipartiteConsError (toProjStrat S).state (uniformDistribution X') A B := by
  classical
  have hcard : Fintype.card X = Fintype.card X' := Fintype.card_congr qe
  unfold inconsistency uniform
  rw [bipartiteConsError_uniform]
  conv_rhs => rw [Finset.mul_sum]
  simp only [one_div, hcard]
  refine Fintype.sum_equiv qe _ _ fun x => ?_
  congr 1
  rw [qBipartiteConsDefect_eq_offDiagonal _ (toProjStrat S).isNormalized _ _ (hA _) (hB _)]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  refine Fintype.sum_equiv e _ _ fun b => ?_
  simp only [e.injective.eq_iff, hM, hN, ev_toProjStrat]
  rfl

end MIPRE.LIDT.Bridge

end
