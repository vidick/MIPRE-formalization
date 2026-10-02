/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.StrategyBiProj.Measurements

@[expose] public section

/-!
# Bridge, part 5, over models: consistency defects of complete measurements

The model counterpart of the repository's matrix bridge `MIPRE/Background/LIDT/Bridge/Defect.lean`
(not a vendored file; it serves the tensor instance and stays), in the port of
`planning/c6b-plan.md` (milestone M14, unit M14-1).

Generic facts about the port's two-space bipartite consistency defect
`qBipartiteConsDefect M A B = max 0 (bornProb (A_tot, B_tot) − ∑ₐ bornProb (A_a, B_a))`
(`Co/Test/StrategyBiProj/Measurements.lean`), over a bipartite model
`M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with star-ordered algebras, when the measurements `A`, `B` are
complete (`total = 1`) and the state is a unit vector (`‖M.ψ‖ = 1`):

* the defect is `1 − ∑ₐ bornProb (A_a, B_a)` (`qBipartiteConsDefect_of_complete`), and equals the
  off-diagonal mass `∑_{a ≠ b} bornProb (A_a, B_b)` (`qBipartiteConsDefect_eq_offDiagonal`);
* for coarse-grainings `postprocess A f`, `postprocess B g`, the matching mass is
  `∑_{a, b : f a = g b} bornProb (A_a, B_b)` (`qBipartiteMatchMass_postprocess`), so the defect is
  bounded by `1 − acc` whenever `acc` is a sum of some of the terms `bornProb (A_a, B_b)` with
  `f a = g b` (`qBipartiteConsDefect_postprocess_le`).

The translation is the matrix bridge's with `ev ψ (opTensor X Y)` read as `M.bornProb X Y` and
the normalization `ψ.IsNormalized` as `‖M.ψ‖ = 1`; the sums of Born probabilities go through
`M.bornProb_sum_left` and `M.bornProb_sum_right`. These are the facts through which the value of
a strategy (`Co/Bridge/Value.lean`) is compared with the port's failure surrogate.

## Not ported

Every declaration of the matrix bridge is redeclared here under its name, for a bipartite model:
`ev_opTensor_outcome_nonneg` and `sum_ev_opTensor_outcome` (stated with `M.bornProb`),
`qBipartiteMatchMass_postprocess`, `qBipartiteMatchMass_le_one`,
`qBipartiteConsDefect_of_complete`, `qBipartiteConsDefect_eq_offDiagonal`,
`qBipartiteConsDefect_postprocess_le` and `bipartiteConsError_uniform`. Nothing is left out.
-/

open MIPStarRE.LDT (Distribution avgOver uniformDistribution)

namespace MIPRE.LIDT.Co.Bridge

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ)
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Born probabilities of pairs of measurement operators are nonnegative. -/
theorem ev_opTensor_outcome_nonneg (A : SubMeas α 𝒜) (B : SubMeas β ℬ) (a : α) (b : β) :
    0 ≤ M.bornProb (A.outcome a) (B.outcome b) :=
  M.bornProb_nonneg (A.outcome_pos a) (B.outcome_pos b)

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The Born probabilities of two complete measurements on a unit vector sum to one. -/
theorem sum_ev_opTensor_outcome (hψ : ‖M.ψ‖ = 1) (A : SubMeas α 𝒜) (B : SubMeas β ℬ)
    (hA : A.total = 1) (hB : B.total = 1) :
    ∑ a, ∑ b, M.bornProb (A.outcome a) (B.outcome b) = 1 := by
  simp_rw [← M.bornProb_sum_right, ← M.bornProb_sum_left, A.sum_eq_total, B.sum_eq_total, hA, hB]
  show M.qform (M.πA 1 * M.πB 1) = 1
  rw [map_one, map_one, one_mul, M.qform_one hψ]

/-- The matching mass of two coarse-grained measurements. -/
theorem qBipartiteMatchMass_postprocess [DecidableEq γ] (A : SubMeas α 𝒜) (B : SubMeas β ℬ)
    (f : α → γ) (g : β → γ) :
    qBipartiteMatchMass M (postprocess A f) (postprocess B g) =
      ∑ a, ∑ b, if f a = g b then M.bornProb (A.outcome a) (B.outcome b) else 0 := by
  unfold qBipartiteMatchMass
  simp only [SubMeas.postprocess_outcome, MIPRE.BipartiteModel.bornProb_sum_left,
    MIPRE.BipartiteModel.bornProb_sum_right]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_comm

/-- The matching mass of two complete measurements on a unit vector is at most one. -/
theorem qBipartiteMatchMass_le_one (hψ : ‖M.ψ‖ = 1) (A : SubMeas α 𝒜) (B : SubMeas α ℬ)
    (hA : A.total = 1) (hB : B.total = 1) :
    qBipartiteMatchMass M A B ≤ 1 := by
  rw [← sum_ev_opTensor_outcome M hψ A B hA hB]
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum fun a _ => ?_
  exact Finset.single_le_sum (fun b _ => ev_opTensor_outcome_nonneg M A B a b) (Finset.mem_univ a)

/-- For complete measurements on a unit vector the defect is `1 − matching mass`. -/
theorem qBipartiteConsDefect_of_complete (hψ : ‖M.ψ‖ = 1) (A : SubMeas α 𝒜) (B : SubMeas α ℬ)
    (hA : A.total = 1) (hB : B.total = 1) :
    qBipartiteConsDefect M A B = 1 - qBipartiteMatchMass M A B := by
  have h1 : M.bornProb A.total B.total = 1 := by
    rw [hA, hB]
    show M.qform (M.πA 1 * M.πB 1) = 1
    rw [map_one, map_one, one_mul, M.qform_one hψ]
  simp only [qBipartiteConsDefect, h1]
  exact max_eq_right (sub_nonneg.mpr (qBipartiteMatchMass_le_one M hψ A B hA hB))

/-- For complete measurements on a unit vector the defect is the off-diagonal mass. -/
theorem qBipartiteConsDefect_eq_offDiagonal [DecidableEq α] (hψ : ‖M.ψ‖ = 1) (A : SubMeas α 𝒜)
    (B : SubMeas α ℬ) (hA : A.total = 1) (hB : B.total = 1) :
    qBipartiteConsDefect M A B =
      ∑ a, ∑ b, if a = b then 0 else M.bornProb (A.outcome a) (B.outcome b) := by
  rw [qBipartiteConsDefect_of_complete M hψ A B hA hB, ← sum_ev_opTensor_outcome M hψ A B hA hB]
  unfold qBipartiteMatchMass
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ b, (if a = b then (0 : ℝ) else M.bornProb (A.outcome a) (B.outcome b)) =
      M.bornProb (A.outcome a) (B.outcome b) -
        if a = b then M.bornProb (A.outcome a) (B.outcome b) else 0 := by
    intro b; split_ifs <;> simp
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The defect of two coarse-grainings of complete measurements on a unit vector is at most
`1 − acc` for any acceptance mass `acc` made of terms that force equal coarse-grained
outcomes. -/
theorem qBipartiteConsDefect_postprocess_le [DecidableEq γ] (hψ : ‖M.ψ‖ = 1) (A : SubMeas α 𝒜)
    (B : SubMeas β ℬ) (hA : A.total = 1) (hB : B.total = 1) (f : α → γ) (g : β → γ)
    (D : α → β → Prop) [DecidableRel D] (hD : ∀ a b, D a b → f a = g b) :
    qBipartiteConsDefect M (postprocess A f) (postprocess B g) ≤
      1 - ∑ a, ∑ b, if D a b then M.bornProb (A.outcome a) (B.outcome b) else 0 := by
  rw [qBipartiteConsDefect_of_complete M hψ (postprocess A f) (postprocess B g) hA hB,
    qBipartiteMatchMass_postprocess]
  refine sub_le_sub_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) 1
  by_cases h : D a b
  · rw [ite_eq_left h, ite_eq_left (hD a b h)]
  · rw [ite_eq_right h]
    split_ifs
    · exact ev_opTensor_outcome_nonneg M A B a b
    · exact le_rfl

/-! ## Averages over uniform distributions -/

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The consistency error under the uniform distribution is the average of the defects. -/
theorem bipartiteConsError_uniform {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (A : IdxSubMeas X α 𝒜) (B : IdxSubMeas X α ℬ) :
    bipartiteConsError M (uniformDistribution X) A B =
      (1 / (Fintype.card X : ℝ)) * ∑ x, qBipartiteConsDefect M (A x) (B x) := by
  classical
  unfold bipartiteConsError avgOver uniformDistribution
  simp only [Distribution.uniformOnFinset_support, Distribution.uniformOnFinset_weight,
    Finset.mem_univ, ite_true, Finset.card_univ, Finset.mul_sum]

end MIPRE.LIDT.Co.Bridge

end
