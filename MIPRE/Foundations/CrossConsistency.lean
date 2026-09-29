/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.StateDistance
public import MIPRE.Foundations.POVMValue
public import MIPRE.Foundations.Sign

@[expose] public section

/-!
# Cross-party consistency, and what winning a subtest buys

The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`: one player's operator against the
*other* player's. `MIPRE.stateDist` of `def:state-distance` compares two families on the same
side, which is what the orthonormalization step needs; this file is the cross-party form, and
the one lemma that produces it.

## The engine

`xSqNorm ψ A B = ‖(A ⊗ Id - Id ⊗ B)|ψ⟩‖²`, and `xPovmDist` averages its sum over outcomes
against a question distribution. `xSqNorm_sum_le_two_mul` is the only analytic content:

```
∑_c ‖(A_c ⊗ Id - Id ⊗ B_c)|ψ⟩‖² ≤ 2 (1 - ∑_c ⟨ψ| A_c ⊗ B_c |ψ⟩)
```

for any two POVMs indexed by the same outcome set. Expand each square; the two diagonal sums are
at most one because a POVM element `A` has `A† A = A² ≤ A` and the elements sum to the identity,
and the cross term is exactly the agreement probability. **No projectivity is used** --- which
matters, because the strategies this is applied to are arbitrary POVM strategies and the
projectivity only arrives later, through `cor:ortho-from-consistency`.

Paired with `condFail_agree`, which says the right-hand side *is* twice the conditional failure
of a subtest whose decider accepts iff two post-processings of the answers agree, this turns
each item of `lem:qld-win` into an instance: name the two post-processings, check the decider,
and the bound is `2 ε / μ`.

## The weights

`sum_mul_condFail_le` is the other half: the conditional failures of *any* set of question
pairs, weighted by their probabilities, add up to at most `ε`. `condFail_le_div` in
`MIPRE/Foundations/POVMValue.lean` is its one-pair case. The useful corollary is
`sum_condFail_le_of_le`: an auxiliary distribution `ν` on an index set that injects into the
question pairs, with `c · ν i ≤ μ` at each, gives `∑_i ν i · condFail ≤ ε / c`. That is the
blueprint's "each item is the value of the corresponding subtest, divided by the probability
that the subtest is selected", with `c` the selection probability and `ν` the conditional
question distribution.

## In a bipartite model

Everything above is proved once, for a bipartite model (`MIPRE/Foundations/BipartiteModel.lean`)
with the players' POVMs in their ordered algebras (`BipartiteModel.xSqNorm_sum_le_two_mul`,
`BipartiteModel.xSqNorm_sum_le_condFail`, `BipartiteModel.xNorm_mul_le`, ...), and the matrix
statements are its instances in the tensor-product model. The one positivity fact, `t² ≤ t` for
`0 ≤ t ≤ 1`, is used on the represented operator (`Op.mul_self_le_self`), where the functional
calculus of `B(H)` is: a player's algebra need not have one.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## In a bipartite model

The cross-party calculus is stated for any bipartite model (`MIPRE/Foundations/BipartiteModel.lean`):
the first player's operators in `𝒜`, the second player's in `ℬ`, and the deviation
`‖(πA a - πB b) ψ‖` a state norm of the model's algebra. The matrix statements below are its
instances in the tensor-product model (`xNorm_eq_tensor`, `xSqNorm_eq_tensor`,
`xPovmDist_eq_tensor`). The second player's state norm is the first player's in the swapped
model, `M.swap.stateNorm b = ‖πB b ψ‖`, so nothing is stated twice. -/

namespace BipartiteModel

open scoped InnerProductSpace

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- `‖(πA a - πB b) ψ‖`, the unsquared cross-party deviation. -/
def xNorm (a : 𝒜) (b : ℬ) : ℝ := M.snorm (M.πA a - M.πB b)

/-- `‖(πA a - πB b) ψ‖²`, the appendix's `A ⊗ Id ≃ Id ⊗ B` at a single pair of operators. -/
def xSqNorm (a : 𝒜) (b : ℬ) : ℝ := M.xNorm a b ^ 2

theorem xNorm_nonneg (a : 𝒜) (b : ℬ) : 0 ≤ M.xNorm a b := M.snorm_nonneg _

theorem xSqNorm_nonneg (a : 𝒜) (b : ℬ) : 0 ≤ M.xSqNorm a b := sq_nonneg _

theorem xSqNorm_eq_sq (a : 𝒜) (b : ℬ) : M.xSqNorm a b = M.xNorm a b ^ 2 := rfl

/-- **The swap exchanges the two sides of a deviation.** -/
theorem xNorm_swap (a : 𝒜) (b : ℬ) : M.swap.xNorm b a = M.xNorm a b :=
  M.snorm_sub_comm _ _

theorem xSqNorm_swap (a : 𝒜) (b : ℬ) : M.swap.xSqNorm b a = M.xSqNorm a b := by
  rw [xSqNorm, xSqNorm, M.xNorm_swap]

theorem stateNorm_sub_comm (a a' : 𝒜) : M.stateNorm (a - a') = M.stateNorm (a' - a) := by
  rw [stateNorm, stateNorm, map_sub, map_sub, M.snorm_sub_comm]

theorem stateSqNorm_sub_comm (a a' : 𝒜) : M.stateSqNorm (a - a') = M.stateSqNorm (a' - a) := by
  rw [stateSqNorm, stateSqNorm, M.stateNorm_sub_comm]

/-- Pushing a sum inside a deviation costs the number of terms. -/
theorem stateSqNorm_sum_le {κ : Type*} [Fintype κ] (f : κ → 𝒜) :
    M.stateSqNorm (∑ k, f k) ≤ (Fintype.card κ : ℝ) * ∑ k, M.stateSqNorm (f k) := by
  calc M.stateSqNorm (∑ k, f k) = M.stateNorm (∑ k, f k) ^ 2 := rfl
    _ ≤ (∑ k, M.stateNorm (f k)) ^ 2 :=
        pow_le_pow_left₀ (M.stateNorm_nonneg _) (M.stateNorm_sum_le _ _) 2
    _ ≤ (Fintype.card κ : ℝ) * ∑ k, M.stateNorm (f k) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ fun k => M.stateNorm_nonneg _
    _ = (Fintype.card κ : ℝ) * ∑ k, M.stateSqNorm (f k) := rfl

variable {X : Type*} [Fintype X]

/-- **The cross-party distance** of two families of operators, one on each side. -/
def xStateDist (μ : X → ℝ) (A : X → 𝒜) (B : X → ℬ) : ℝ :=
  ∑ x, μ x * M.xSqNorm (A x) (B x)

section POVMs

variable [PartialOrder 𝒜] [PartialOrder ℬ] {C : Type*} [Fintype C]

/-- **The cross-party distance** of two families of POVMs, one on each side, relative to a
question distribution: the appendix's `M^x_a ⊗ Id ≃_δ Id ⊗ N^x_a`. -/
def xPovmDist (μ : X → ℝ) (MA : X → POVMIn C 𝒜) (MB : X → POVMIn C ℬ) : ℝ :=
  ∑ x, μ x * ∑ c, M.xSqNorm ((MA x).op c) ((MB x).op c)

/-- `M^x_a ⊗ Id ≃_δ Id ⊗ N^x_a` on the state, relative to `μ`. -/
def IsXPOVMClose (μ : X → ℝ) (δ : ℝ) (MA : X → POVMIn C 𝒜) (MB : X → POVMIn C ℬ) : Prop :=
  M.xPovmDist μ MA MB ≤ δ

theorem xPovmDist_nonneg {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (MA : X → POVMIn C 𝒜)
    (MB : X → POVMIn C ℬ) : 0 ≤ M.xPovmDist μ MA MB :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => M.xSqNorm_nonneg _ _)

/-- **From POVM elements to generalized observables, across the two parties**: the triangle
inequality, then Cauchy--Schwarz over the outcome set, at the factor `|𝒜|`. -/
theorem xStateDist_obsOf_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (MA : X → POVMIn C 𝒜)
    (MB : X → POVMIn C ℬ) (α : C → ℂ) (hα : ∀ a, ‖α a‖ ≤ 1) :
    M.xStateDist μ (fun x => pvmObs (MA x).op α) (fun x => pvmObs (MB x).op α)
      ≤ (Fintype.card C : ℝ) * M.xPovmDist μ MA MB := by
  rw [xPovmDist, Finset.mul_sum, xStateDist]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_assoc, mul_comm ((Fintype.card C : ℝ)) (μ x), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hμ0 x)
  have hsub : M.πA (pvmObs (MA x).op α) - M.πB (pvmObs (MB x).op α)
      = ∑ c, α c • (M.πA ((MA x).op c) - M.πB ((MB x).op c)) := by
    rw [pvmObs, pvmObs, map_sum, map_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [map_smul, map_smul, smul_sub]
  have htri : M.xNorm (pvmObs (MA x).op α) (pvmObs (MB x).op α)
      ≤ ∑ c, M.xNorm ((MA x).op c) ((MB x).op c) := by
    rw [xNorm, hsub]
    refine (M.snorm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [M.snorm_smul]
    exact mul_le_of_le_one_left (M.snorm_nonneg _) (hα c)
  calc M.xSqNorm (pvmObs (MA x).op α) (pvmObs (MB x).op α)
      ≤ (∑ c, M.xNorm ((MA x).op c) ((MB x).op c)) ^ 2 :=
        pow_le_pow_left₀ (M.xNorm_nonneg _ _) htri 2
    _ ≤ (Fintype.card C : ℝ) * ∑ c, M.xNorm ((MA x).op c) ((MB x).op c) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ fun c => M.xNorm_nonneg _ _
    _ = (Fintype.card C : ℝ) * ∑ c, M.xSqNorm ((MA x).op c) ((MB x).op c) := rfl

end POVMs

/-! ### Products, and the order reversal -/

/-- **The order-reversal rule.** If `πA a` is `K`-bounded and `πB b'` is `L`-bounded, then
`a b` is close to `b' a'` across the parties: the second player's factors appear in the opposite
order, and each deviation is paid for by the operator norm of the factor in front of it. -/
theorem xNorm_mul_le {K L : ℝ} (a b : 𝒜) (a' b' : ℬ) (hA : M.Bnd (M.πA a) K)
    (hB' : M.Bnd (M.πB b') L) :
    M.xNorm (a * b) (b' * a') ≤ K * M.xNorm b b' + L * M.xNorm a a' := by
  have hsplit : M.πA (a * b) - M.πB (b' * a')
      = M.πA a * (M.πA b - M.πB b') + M.πB b' * (M.πA a - M.πB a') := by
    rw [map_mul, map_mul, mul_sub, mul_sub, (M.commute a b').eq]
    abel
  rw [xNorm, hsplit]
  exact (M.snorm_add_le _ _).trans (add_le_add (M.snorm_mul_le hA _) (M.snorm_mul_le hB' _))

/-- The order reversal for contractions. -/
theorem xNorm_mul_le_one (a b : 𝒜) (a' b' : ℬ) (hA : M.Bnd (M.πA a) 1)
    (hB' : M.Bnd (M.πB b') 1) :
    M.xNorm (a * b) (b' * a') ≤ M.xNorm b b' + M.xNorm a a' := by
  have h := M.xNorm_mul_le a b a' b' hA hB'
  rwa [one_mul, one_mul] at h

/-- The squared form of the order reversal, at the usual cost of a factor two. -/
theorem xSqNorm_mul_le_one (a b : 𝒜) (a' b' : ℬ) (hA : M.Bnd (M.πA a) 1)
    (hB' : M.Bnd (M.πB b') 1) :
    M.xSqNorm (a * b) (b' * a') ≤ 2 * M.xSqNorm b b' + 2 * M.xSqNorm a a' := by
  have h := M.xNorm_mul_le_one a b a' b' hA hB'
  have h0 : 0 ≤ M.xNorm b b' + M.xNorm a a' := add_nonneg (M.xNorm_nonneg _ _) (M.xNorm_nonneg _ _)
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq, xSqNorm_eq_sq]
  nlinarith [sq_nonneg (M.xNorm b b' - M.xNorm a a'), M.xNorm_nonneg (a * b) (b' * a')]

/-- **An anticommutation on the second player's side transfers to the first player's**, at the
cost of the two cross-party deviations counted twice each. The split

`ab + ba = [ab - b'a'] + [a'b' + b'a'] + [ba - a'b']`

is an identity across the two sides, and its summands are an order reversal, the second
player's anticommutator, and the other order reversal. -/
theorem stateNorm_anticomm_le (a b : 𝒜) (a' b' : ℬ) (hA : M.Bnd (M.πA a) 1)
    (hB : M.Bnd (M.πA b) 1) (hA' : M.Bnd (M.πB a') 1) (hB' : M.Bnd (M.πB b') 1) :
    M.stateNorm (a * b + b * a)
      ≤ 2 * M.xNorm a a' + 2 * M.xNorm b b' + M.swap.stateNorm (a' * b' + b' * a') := by
  have hsplit : M.πA (a * b + b * a)
      = (M.πA (a * b) - M.πB (b' * a')) + M.πB (a' * b' + b' * a')
        + (M.πA (b * a) - M.πB (a' * b')) := by
    rw [map_add, map_add]
    abel
  have h1 := M.xNorm_mul_le_one a b a' b' hA hB'
  have h2 := M.xNorm_mul_le_one b a b' a' hB hA'
  have e0 : M.stateNorm (a * b + b * a) = M.snorm (M.πA (a * b) - M.πB (b' * a')
      + M.πB (a' * b' + b' * a') + (M.πA (b * a) - M.πB (a' * b'))) := congrArg M.snorm hsplit
  have e : M.snorm (M.πA (a * b) - M.πB (b' * a') + M.πB (a' * b' + b' * a')
        + (M.πA (b * a) - M.πB (a' * b')))
      ≤ M.xNorm (a * b) (b' * a') + M.swap.stateNorm (a' * b' + b' * a')
        + M.xNorm (b * a) (a' * b') :=
    (M.snorm_add_le _ _).trans (add_le_add (M.snorm_add_le _ _) le_rfl)
  linarith

/-- **The commutator form of the transfer**: the same split, with the middle term a
commutator. -/
theorem stateNorm_comm_le (a b : 𝒜) (a' b' : ℬ) (hA : M.Bnd (M.πA a) 1)
    (hB : M.Bnd (M.πA b) 1) (hA' : M.Bnd (M.πB a') 1) (hB' : M.Bnd (M.πB b') 1) :
    M.stateNorm (a * b - b * a)
      ≤ 2 * M.xNorm a a' + 2 * M.xNorm b b' + M.swap.stateNorm (b' * a' - a' * b') := by
  have hsplit : M.πA (a * b - b * a)
      = (M.πA (a * b) - M.πB (b' * a')) + M.πB (b' * a' - a' * b')
        + (M.πB (a' * b') - M.πA (b * a)) := by
    rw [map_sub, map_sub]
    abel
  have h1 := M.xNorm_mul_le_one a b a' b' hA hB'
  have h2 := M.xNorm_mul_le_one b a b' a' hB hA'
  have e4 : M.snorm (M.πB (a' * b') - M.πA (b * a)) = M.xNorm (b * a) (a' * b') :=
    M.snorm_sub_comm _ _
  have e0 : M.stateNorm (a * b - b * a) = M.snorm (M.πA (a * b) - M.πB (b' * a')
      + M.πB (b' * a' - a' * b') + (M.πB (a' * b') - M.πA (b * a))) := congrArg M.snorm hsplit
  have e : M.snorm (M.πA (a * b) - M.πB (b' * a') + M.πB (b' * a' - a' * b')
        + (M.πB (a' * b') - M.πA (b * a)))
      ≤ M.xNorm (a * b) (b' * a') + M.swap.stateNorm (b' * a' - a' * b')
        + M.snorm (M.πB (a' * b') - M.πA (b * a)) :=
    (M.snorm_add_le _ _).trans (add_le_add (M.snorm_add_le _ _) le_rfl)
  linarith

/-- **The expansion of a cross-party deviation**, for a self-adjoint first operator: the two
players' squared norms, less twice the Born term. -/
theorem xSqNorm_eq {a : 𝒜} (ha : star a = a) (b : ℬ) :
    M.xSqNorm a b = M.stateSqNorm a + M.swap.stateSqNorm b - 2 * M.bornProb a b := by
  have h := M.inner_πA_πB ha b
  show ‖M.π (M.πA a - M.πB b) M.ψ‖ ^ 2
      = ‖M.π (M.πA a) M.ψ‖ ^ 2 + ‖M.π (M.πB b) M.ψ‖ ^ 2
        - 2 * (⟪M.ψ, M.π (M.πA a * M.πB b) M.ψ⟫_ℂ).re
  rw [map_sub]
  show ‖M.π (M.πA a) M.ψ - M.π (M.πB b) M.ψ‖ ^ 2 = _
  rw [@norm_sub_sq ℂ, h, RCLike.re_to_complex]
  ring

/-! ### Measurements are contractions on the state -/

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- An element with `a* a ≤ 1` is represented by a contraction. -/
theorem bnd_πA_of_star_mul_self_le {a : 𝒜} (h : star a * a ≤ 1) : M.Bnd (M.πA a) 1 := by
  refine Op.bnd_one_of_star_mul_self_le ?_
  have h' := OrderHomClass.mono (M.π.comp M.πA) h
  rwa [map_mul, map_star, map_one] at h'

/-- An element between `0` and `1` is represented by a positive operator at most one. -/
theorem π_πA_le_one {t : 𝒜} (h1 : t ≤ 1) : M.π (M.πA t) ≤ 1 := by
  have h' := OrderHomClass.mono (M.π.comp M.πA) h1
  rwa [map_one] at h'

/-- A POVM element is represented by a contraction. -/
theorem bnd_πA_of_nonneg_of_le_one {t : 𝒜} (h0 : 0 ≤ t) (h1 : t ≤ 1) : M.Bnd (M.πA t) 1 :=
  Op.bnd_one_of_nonneg_of_le_one (M.π_πA_nonneg h0) (M.π_πA_le_one h1)

/-- **The difference of two POVM elements is represented by a contraction**, with no
projectivity: this is what makes a two-outcome coarse-graining a `±1`-observable in every
estimate. -/
theorem bnd_πA_sub {C : Type*} [Fintype C] (P : POVMIn C 𝒜) (p q : C) :
    M.Bnd (M.πA (P.op p - P.op q)) 1 := by
  show Op.Bnd (M.π (M.πA (P.op p - P.op q))) 1
  rw [map_sub, map_sub]
  exact Op.bnd_one_of_sub (M.π_πA_nonneg (P.op_nonneg p)) (M.π_πA_le_one (P.op_le_one p))
    (M.π_πA_nonneg (P.op_nonneg q)) (M.π_πA_le_one (P.op_le_one q))

/-- **A POVM element is a contraction on the state**: `‖πA t ψ‖² ≤ ⟨ψ, πA t ψ⟩` for
`0 ≤ t ≤ 1`, because `t² ≤ t`. -/
theorem stateSqNorm_le_qform {t : 𝒜} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    M.stateSqNorm t ≤ M.qform (M.πA t) := by
  have hP0 := M.π_πA_nonneg h0
  have hsa : star (M.π (M.πA t)) = M.π (M.πA t) := (IsSelfAdjoint.of_nonneg hP0).star_eq
  have hq : 0 ≤ M.qform (M.πA t - star (M.πA t) * M.πA t) := by
    refine M.qform_nonneg ?_
    rw [map_sub, map_mul, map_star, hsa]
    exact sub_nonneg.2 (Op.mul_self_le_self hP0 (M.π_πA_le_one h1))
  rw [M.qform_sub] at hq
  rw [M.stateSqNorm_eq, map_mul, map_star]
  linarith

/-- `∑_a ‖πA(A_a) ψ‖² ≤ 1` for a POVM on a unit vector. -/
theorem sum_stateSqNorm_le_one (hψ : ‖M.ψ‖ = 1) {C : Type*} [Fintype C] (MA : POVMIn C 𝒜) :
    ∑ c, M.stateSqNorm (MA.op c) ≤ 1 := by
  calc ∑ c, M.stateSqNorm (MA.op c) ≤ ∑ c, M.qform (M.πA (MA.op c)) :=
        Finset.sum_le_sum fun c _ => M.stateSqNorm_le_qform (MA.op_nonneg c) (MA.op_le_one c)
    _ = 1 := by rw [← M.qform_sum, ← map_sum, MA.sum_op, map_one, M.qform_one hψ]

end Order

section Order2

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  {C : Type*} [Fintype C]

/-- **From agreement to cross-party closeness.** For any two POVMs with the same outcome set,
the summed cross-party squared deviation is at most twice the disagreement probability. Expand
each square: the two diagonal sums are at most one (`sum_stateSqNorm_le_one`, on each side), and
the cross term is the agreement probability. No projectivity. -/
theorem xSqNorm_sum_le_two_mul (hψ : ‖M.ψ‖ = 1) (MA : POVMIn C 𝒜) (MB : POVMIn C ℬ) :
    ∑ c, M.xSqNorm (MA.op c) (MB.op c)
      ≤ 2 * (1 - ∑ c, M.bornProb (MA.op c) (MB.op c)) := by
  rw [Finset.sum_congr rfl fun c _ => M.xSqNorm_eq (MA.star_op c) (MB.op c),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := M.sum_stateSqNorm_le_one hψ MA
  have h2 := M.swap.sum_stateSqNorm_le_one hψ MB
  linarith

/-! ### The conditional failure of an agreement subtest -/

variable {Y A B : Type*} [Fintype Y] [Fintype A] [Fintype B]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Relabelling the second player's outcomes is data processing: a weighted sum over the
relabelled outcomes is the same weighted sum over the original ones, with the weight pulled
back. -/
theorem sum_bornProb_mapB {B' : Type*} [Fintype B'] [DecidableEq B']
    (a : 𝒜) (NB : POVMIn B ℬ) (φB : B → B') (w : B' → ℝ) :
    ∑ b', w b' * M.bornProb a ((NB.map φB).op b') = ∑ b, w (φB b) * M.bornProb a (NB.op b) := by
  classical
  have hborn : ∀ b', M.bornProb a ((NB.map φB).op b')
      = ∑ b ∈ univ.filter fun b => φB b = b', M.bornProb a (NB.op b) := fun b' => by
    rw [POVMIn.map_op, M.bornProb_sum_right]
  rw [Finset.sum_congr rfl fun b' (_ : b' ∈ univ) => by rw [hborn b', Finset.mul_sum]]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq univ (φB b) _]
  simp only [mem_univ, ite_true]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- Relabelling the first player's outcomes is data processing. -/
theorem sum_bornProb_mapA {A' : Type*} [Fintype A'] [DecidableEq A'] (NA : POVMIn A 𝒜)
    (φA : A → A') (b : ℬ) (w : A' → ℝ) :
    ∑ a', w a' * M.bornProb ((NA.map φA).op a') b = ∑ a, w (φA a) * M.bornProb (NA.op a) b := by
  classical
  have hborn : ∀ a', M.bornProb ((NA.map φA).op a') b
      = ∑ a ∈ univ.filter fun a => φA a = a', M.bornProb (NA.op a) b := fun a' => by
    rw [POVMIn.map_op, M.bornProb_sum_left]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => by rw [hborn a', Finset.mul_sum]]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq univ (φA a) _]
  simp only [mem_univ, ite_true]

/-- **Relabelling both players' outcomes is data processing on the Born distribution.** A
weighted sum over the relabelled outcome pairs is the same weighted sum over the original pairs,
with the weights pulled back. -/
theorem sum_weight_bornProb_map {A' B' : Type*} [Fintype A'] [DecidableEq A'] [Fintype B']
    [DecidableEq B'] (NA : POVMIn A 𝒜) (NB : POVMIn B ℬ) (φA : A → A') (φB : B → B')
    (w : A' → B' → ℝ) :
    ∑ a', ∑ b', w a' b' * M.bornProb ((NA.map φA).op a') ((NB.map φB).op b')
      = ∑ a, ∑ b, w (φA a) (φB b) * M.bornProb (NA.op a) (NB.op b) := by
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) =>
    M.sum_bornProb_mapB ((NA.map φA).op a') NB φB (w a')]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) =>
    M.sum_bornProb_mapA NA φA (NB.op b) fun a' => w a' (φB b)]
  exact Finset.sum_comm

/-- The agreement probability of two coarse-grained POVMs, as a sum over the original outcome
pairs. -/
theorem sum_bornProb_map [DecidableEq C] (NA : POVMIn A 𝒜) (NB : POVMIn B ℬ) (f : A → C)
    (g : B → C) :
    ∑ c, M.bornProb ((NA.map f).op c) ((NB.map g).op c)
      = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0) * M.bornProb (NA.op a) (NB.op b) := by
  have h := M.sum_weight_bornProb_map NA NB f g fun c c' => if c = c' then (1 : ℝ) else 0
  rw [← h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single c (fun c' _ hc' => by rw [ite_eq_right (Ne.symm hc'), zero_mul])
    (fun hc => absurd (Finset.mem_univ c) hc), ite_eq_left rfl, one_mul]

variable {G : Game X Y A B} {MA : X → POVMIn A 𝒜} {MB : Y → POVMIn B ℬ}

/-- **Accept implies agree bounds the disagreement of the coarse-grained POVMs by the
conditional failure.** -/
theorem one_sub_sum_bornProb_le_condFail [DecidableEq C] {x : X} {y : Y} (f : A → C)
    (g : B → C) (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    1 - ∑ c, M.bornProb (((MA x).map f).op c) (((MB y).map g).op c)
      ≤ M.condFail G MA MB x y := by
  have hle : M.condWin G MA MB x y
      ≤ ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0) * M.bornProb ((MA x).op a) ((MB y).op b) := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have h0 := M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b)
    by_cases h : G.D x y a b = true
    · rw [ite_eq_left h, ite_eq_left (hD a b h)]
    · rw [ite_eq_right h, zero_mul]
      exact mul_nonneg (by split_ifs <;> norm_num) h0
  rw [M.sum_bornProb_map, condFail]
  linarith

/-- **The master estimate.** A subtest that accepts only when two post-processings of the answers
agree bounds the cross-party deviation of the coarse-grained POVMs by twice its conditional
failure. -/
theorem xSqNorm_sum_le_condFail [DecidableEq C] (hψ : ‖M.ψ‖ = 1) {x : X} {y : Y} (f : A → C)
    (g : B → C) (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, M.xSqNorm (((MA x).map f).op c) (((MB y).map g).op c) ≤ 2 * M.condFail G MA MB x y :=
  (M.xSqNorm_sum_le_two_mul hψ _ _).trans
    (mul_le_mul_of_nonneg_left (M.one_sub_sum_bornProb_le_condFail f g hD) (by norm_num))

/-! ### The weights of the subtests -/

variable {ε : ℝ}

/-- **The conditional failures of any set of question pairs, weighted by their probabilities,
add up to at most `ε`.** -/
theorem sum_mul_condFail_le (hψ : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue G MA MB ≤ ε)
    (S : Finset (X × Y)) :
    ∑ p ∈ S, G.μ p.1 p.2 * M.condFail G MA MB p.1 p.2 ≤ ε := by
  have heq : ∑ p : X × Y, G.μ p.1 p.2 * M.condFail G MA MB p.1 p.2
      = 1 - M.povmValue G MA MB := by
    rw [Fintype.sum_prod_type, M.one_sub_povmValue_eq]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun p _ _ => mul_nonneg (G.μ_nonneg _ _) (M.condFail_nonneg hψ _ _)) ?_
  rw [heq]
  exact hfail

/-- **The conditional error of a subtest, at the cost of its selection probability**: an
auxiliary weighting `ν` and a map `q` to question pairs whose pushforward stays below `μ / c`
gives `∑_i ν i · condFail (q i) ≤ ε / c`. -/
theorem sum_condFail_le_of_pushforward {ι : Type*} [Fintype ι] [DecidableEq X] [DecidableEq Y]
    (hψ : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue G MA MB ≤ ε) (ν : ι → ℝ) (q : ι → X × Y)
    {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ i ∈ univ.filter fun i => q i = p, ν i ≤ G.μ p.1 p.2) :
    ∑ i, ν i * M.condFail G MA MB (q i).1 (q i).2 ≤ ε / c := by
  have hgroup : ∑ i, ν i * M.condFail G MA MB (q i).1 (q i).2
      = ∑ p : X × Y, (∑ i ∈ univ.filter fun i => q i = p, ν i)
          * M.condFail G MA MB p.1 p.2 := by
    rw [← Finset.sum_fiberwise (g := q)
      (f := fun i => ν i * M.condFail G MA MB (q i).1 (q i).2)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [hgroup, le_div_iff₀ hc, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum
    (g := fun p : X × Y => G.μ p.1 p.2 * M.condFail G MA MB p.1 p.2) fun p _ => ?_) ?_
  · have h0 := M.condFail_nonneg (G := G) (MA := MA) (MB := MB) hψ p.1 p.2
    calc (∑ i ∈ univ.filter fun i => q i = p, ν i) * M.condFail G MA MB p.1 p.2 * c
        = c * (∑ i ∈ univ.filter fun i => q i = p, ν i) * M.condFail G MA MB p.1 p.2 := by
          ring
      _ ≤ G.μ p.1 p.2 * M.condFail G MA MB p.1 p.2 := mul_le_mul_of_nonneg_right (hpush p) h0
  · exact M.sum_mul_condFail_le hψ hfail _

/-- The injective form: an auxiliary distribution on an index set that injects into the question
pairs, with `c · ν i` below the question probability at each. -/
theorem sum_condFail_le_of_le {ι : Type*} [Fintype ι] (hψ : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue G MA MB ≤ ε) (ν : ι → ℝ) (q : ι → X × Y)
    (hq : Function.Injective q) {c : ℝ} (hc : 0 < c)
    (hνμ : ∀ i, c * ν i ≤ G.μ (q i).1 (q i).2) :
    ∑ i, ν i * M.condFail G MA MB (q i).1 (q i).2 ≤ ε / c := by
  classical
  have himg : ∑ i, G.μ (q i).1 (q i).2 * M.condFail G MA MB (q i).1 (q i).2
      = ∑ p ∈ univ.image q, G.μ p.1 p.2 * M.condFail G MA MB p.1 p.2 :=
    (Finset.sum_image (f := fun p : X × Y => G.μ p.1 p.2 * M.condFail G MA MB p.1 p.2)
      (s := (univ : Finset ι)) (g := q) fun i _ j _ h => hq h).symm
  rw [le_div_iff₀ hc, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum
    (g := fun i => G.μ (q i).1 (q i).2 * M.condFail G MA MB (q i).1 (q i).2) fun i _ => ?_) ?_
  · have h0 := M.condFail_nonneg (G := G) (MA := MA) (MB := MB) hψ (q i).1 (q i).2
    calc ν i * M.condFail G MA MB (q i).1 (q i).2 * c
        = c * ν i * M.condFail G MA MB (q i).1 (q i).2 := by ring
      _ ≤ G.μ (q i).1 (q i).2 * M.condFail G MA MB (q i).1 (q i).2 :=
          mul_le_mul_of_nonneg_right (hνμ i) h0
  · rw [himg]
    exact M.sum_mul_condFail_le hψ hfail _

end Order2

end BipartiteModel

variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The cross-party squared deviation -/

/-- `‖(A ⊗ Id - Id ⊗ B)|ψ⟩‖²`, the appendix's `A ⊗ Id ≃ Id ⊗ B` at a single pair of
operators. -/
def xSqNorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) : ℝ :=
  ‖stateVec ψ A - stateVecB ψ B‖ ^ 2

/-- `‖(A ⊗ Id - Id ⊗ B)|ψ⟩‖`, the unsquared cross-party deviation. -/
def xNorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) : ℝ :=
  ‖stateVec ψ A - stateVecB ψ B‖

theorem xSqNorm_eq_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = xNorm ψ A B ^ 2 := rfl

/-- The deviation is the state-norm of the single operator `A ⊗ Id - Id ⊗ B` on the product
space, which is what the operator-norm calculus of `MIPRE/Foundations/OpBound.lean` consumes. -/
theorem xNorm_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) _ ℂ) - bOp B) := by
  rw [xNorm, snorm, Matrix.sub_mulVec, evec_sub]
  rfl

/-- **The matrix deviation is that of the tensor-product model.** -/
theorem xNorm_eq_tensor (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = (BipartiteModel.tensor ψ).xNorm A B :=
  xNorm_eq_snorm ψ A B

theorem xSqNorm_eq_tensor (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = (BipartiteModel.tensor ψ).xSqNorm A B := by
  rw [xSqNorm_eq_sq, xNorm_eq_tensor, BipartiteModel.xSqNorm_eq_sq]

theorem xNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xNorm ψ A B := norm_nonneg _

theorem xSqNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xSqNorm ψ A B := sq_nonneg _

/-- **The cross-party distance** of two families of POVMs, one on each side, relative to a
question distribution: the appendix's `M^x_a ⊗ Id ≃_δ Id ⊗ N^x_a`. -/
def xPovmDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM C dA) (N : X → POVM C dB) : ℝ :=
  ∑ x, μ x * ∑ c, xSqNorm ψ (((M x).mats c).val) (((N x).mats c).val)

/-- `M^x_a ⊗ Id ≃_δ Id ⊗ N^x_a` on `ψ`, relative to `μ`. -/
def IsXPOVMClose (μ : X → ℝ) (ψ : dA × dB → ℂ) (δ : ℝ) (M : X → POVM C dA)
    (N : X → POVM C dB) : Prop :=
  xPovmDist μ ψ M N ≤ δ

omit [DecidableEq C] in
theorem xPovmDist_eq_tensor (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM C dA)
    (N : X → POVM C dB) :
    xPovmDist μ ψ M N =
      (BipartiteModel.tensor ψ).xPovmDist μ (fun x => (M x).toIn) (fun x => (N x).toIn) := by
  simp only [xPovmDist, BipartiteModel.xPovmDist, xSqNorm_eq_tensor, POVM.toIn_op]

omit [DecidableEq C] in
theorem xPovmDist_nonneg {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (M : X → POVM C dA) (N : X → POVM C dB) : 0 ≤ xPovmDist μ ψ M N := by
  rw [xPovmDist_eq_tensor]
  exact (BipartiteModel.tensor ψ).xPovmDist_nonneg hμ _ _

/-! ## The cross-party distance of generalized observables

`stateDist_obsOf_le` is the same-side statement (blueprint `lem:qld-povm-to-obs`); the appendix
needs it across the two parties as well, to pass from a two-outcome coarse-graining of a point
measurement to the `±1`-observable it defines. -/

/-- **The cross-party distance** of two families of operators, one on each side. -/
def xStateDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (A : X → Matrix dA dA ℂ)
    (B : X → Matrix dB dB ℂ) : ℝ :=
  ∑ x, μ x * xSqNorm ψ (A x) (B x)

theorem xStateDist_eq_tensor (μ : X → ℝ) (ψ : dA × dB → ℂ) (A : X → Matrix dA dA ℂ)
    (B : X → Matrix dB dB ℂ) :
    xStateDist μ ψ A B = (BipartiteModel.tensor ψ).xStateDist μ A B := by
  simp only [xStateDist, BipartiteModel.xStateDist, xSqNorm_eq_tensor]

omit [DecidableEq C] in
/-- **From POVM elements to generalized observables, across the two parties**: the cross-party
analogue of `stateDist_obsOf_le`, at the same factor `|𝒜|`. -/
theorem xStateDist_obsOf_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (M : X → POVM C dA) (N : X → POVM C dB) (α : C → ℂ) (hα : ∀ a, ‖α a‖ ≤ 1) :
    xStateDist μ ψ (obsOf α M) (obsOf α N)
      ≤ (Fintype.card C : ℝ) * xPovmDist μ ψ M N := by
  rw [xStateDist_eq_tensor, xPovmDist_eq_tensor]
  exact (BipartiteModel.tensor ψ).xStateDist_obsOf_le hμ0 (fun x => (M x).toIn)
    (fun x => (N x).toIn) α hα

/-! ## A POVM element is a contraction on the state

`A† A = A² ≤ A` for `0 ≤ A ≤ 1`, so the diagonal terms of the expansion below sum to at most
one. This is the only place positivity of the POVM is used. -/

/-- `A² ≤ A` for a POVM element: `A^{1/2}(1 - A)A^{1/2} ≥ 0`, here through the commuting
product `A * (1 - A)`. -/
theorem POVM.mul_self_le_self (M : POVM A dA) (a : A) :
    ((M.mats a).val) * ((M.mats a).val) ≤ ((M.mats a).val) := by
  set P := ((M.mats a).val) with hP
  have h0 : (0 : Matrix dA dA ℂ) ≤ P := Subtype.coe_le_coe.mpr (M.nonneg a)
  have h1 : (0 : Matrix dA dA ℂ) ≤ 1 - P := sub_nonneg.mpr (M.le_one a)
  have hc : Commute P (1 - P) := by show P * (1 - P) = (1 - P) * P; noncomm_ring
  have hprod : (0 : Matrix dA dA ℂ) ≤ P * (1 - P) := hc.mul_nonneg h0 h1
  have heq : P * ((1 : Matrix dA dA ℂ) - P) = P - P * P := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod

omit [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB] in
/-- A difference in the left factor of a Kronecker product splits off. -/
theorem sub_kronecker_right (N P : Matrix dA dA ℂ) (R : Matrix dB dB ℂ) :
    (N - P) ⊗ₖ R = N ⊗ₖ R - P ⊗ₖ R := by
  ext p q
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
  ring

/-- `∑_a ‖(A_a ⊗ Id)|ψ⟩‖² ≤ 1` for a POVM on a unit vector. -/
theorem sum_stateSqNorm_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM A dA) :
    ∑ a, stateSqNorm ψ (((M.mats a).val)) ≤ 1 :=
  (BipartiteModel.tensor ψ).sum_stateSqNorm_le_one (norm_evec_eq_one hψ) M.toIn

/-- Bob's version: the first player's in the swapped model. -/
theorem sum_stateSqNormB_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (N : POVM B dB) :
    ∑ b, ‖stateVecB ψ (((N.mats b).val))‖ ^ 2 ≤ 1 :=
  (BipartiteModel.tensor ψ).swap.sum_stateSqNorm_le_one (norm_evec_eq_one hψ) N.toIn

/-! ## The engine -/

omit [DecidableEq C] in
/-- **From agreement to cross-party closeness.** For any two POVMs with the same outcome set,
the summed cross-party squared deviation is at most twice the disagreement probability
(`BipartiteModel.xSqNorm_sum_le_two_mul` in the tensor-product model). No projectivity, and no
hypothesis beyond `ψ` being a unit vector. -/
theorem xSqNorm_sum_le_two_mul {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : POVM C dA) (N : POVM C dB) :
    ∑ c, xSqNorm ψ (((M.mats c).val)) (((N.mats c).val))
      ≤ 2 * (1 - ∑ c, bornProb ψ (((M.mats c).val)) (((N.mats c).val))) := by
  simp only [xSqNorm_eq_tensor, bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).xSqNorm_sum_le_two_mul (norm_evec_eq_one hψ) M.toIn N.toIn

/-! ## The conditional failure of an agreement subtest

The decider of a real test does not *equal* an agreement predicate: it first checks the answer
formats and rejects if they fail, so an ill-formatted pair with agreeing post-processings is
still rejected. What holds, and all that is needed, is the implication **accept implies agree**.
The coarse-grainings are then free to send ill-formatted answers anywhere --- `0` is the usual
choice --- since the test rejects them either way. -/

variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

omit [Fintype X] [Fintype Y] in
/-- The agreement probability of the coarse-grained POVMs, as a sum over the original outcome
pairs. -/
theorem sum_bornProb_map {x : X} {y : Y} (f : A → C) (g : B → C) :
    ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_bornProb_map (MA x).toIn (MB y).toIn f g

omit [Fintype X] [Fintype Y] [DecidableEq C] [DecidableEq dA] in
/-- Relabelling Bob's outcomes is data processing: a weighted sum over the relabelled outcomes is
the same weighted sum over the original ones, with the weight pulled back. -/
theorem sum_bornProb_mapB {B' : Type*} [Fintype B'] [DecidableEq B'] (EA : Matrix dA dA ℂ)
    (NB : POVM B dB) (φB : B → B') (w : B' → ℝ) :
    ∑ b', w b' * bornProb ψ EA (((NB.map φB).mats b').val)
      = ∑ b, w (φB b) * bornProb ψ EA ((NB.mats b).val) := by
  classical
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_bornProb_mapB EA NB.toIn φB w

omit [Fintype X] [Fintype Y] [DecidableEq C] [DecidableEq dB] in
/-- Relabelling Alice's outcomes is data processing. -/
theorem sum_bornProb_mapA {A' : Type*} [Fintype A'] [DecidableEq A'] (NA : POVM A dA)
    (φA : A → A') (EB : Matrix dB dB ℂ) (w : A' → ℝ) :
    ∑ a', w a' * bornProb ψ (((NA.map φA).mats a').val) EB
      = ∑ a, w (φA a) * bornProb ψ ((NA.mats a).val) EB := by
  classical
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_bornProb_mapA NA.toIn φA EB w

omit [Fintype X] [Fintype Y] [DecidableEq C] in
/-- **Relabelling both players' outcomes is data processing on the Born distribution.** A
weighted sum over the relabelled outcome pairs is the same weighted sum over the original pairs,
with the weights pulled back. This is what says the *value* of a relabelled strategy is at least
the value of the original one whenever the relabelled decider is more permissive. -/
theorem sum_weight_bornProb_map {A' B' : Type*} [Fintype A'] [DecidableEq A'] [Fintype B']
    [DecidableEq B'] (NA : POVM A dA) (NB : POVM B dB) (φA : A → A') (φB : B → B')
    (w : A' → B' → ℝ) :
    ∑ a', ∑ b', w a' b' * bornProb ψ (((NA.map φA).mats a').val) (((NB.map φB).mats b').val)
      = ∑ a, ∑ b, w (φA a) (φB b) * bornProb ψ ((NA.mats a).val) ((NB.mats b).val) := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_weight_bornProb_map NA.toIn NB.toIn φA φB w

/-- **Accept implies agree bounds the disagreement of the coarse-grained POVMs by the
conditional failure.** -/
theorem one_sub_sum_bornProb_le_condFail {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ condFail G ψ MA MB x y := by
  simp only [bornProb_eq_tensor, condFail_eq_tensor]
  exact (BipartiteModel.tensor ψ).one_sub_sum_bornProb_le_condFail
    (MA := fun x => (MA x).toIn) (MB := fun y => (MB y).toIn) f g hD

/-- **The master estimate.** A subtest that accepts only when two post-processings of the answers
agree bounds the cross-party deviation of the coarse-grained POVMs by twice its conditional
failure. Every item of `lem:qld-win` is an instance: name `f` and `g`, check the decider, and
read off the bound. -/
theorem xSqNorm_sum_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, xSqNorm ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ 2 * condFail G ψ MA MB x y := by
  simp only [xSqNorm_eq_tensor, condFail_eq_tensor]
  exact (BipartiteModel.tensor ψ).xSqNorm_sum_le_condFail (MA := fun x => (MA x).toIn)
    (MB := fun y => (MB y).toIn) (norm_evec_eq_one hψ) f g hD

/-! ## The weights of the subtests -/

variable {ε : ℝ}

/-- **The conditional failures of any set of question pairs, weighted by their probabilities,
add up to at most `ε`.** `condFail_le_div` is the one-pair case. -/
theorem sum_mul_condFail_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue G ψ MA MB ≤ ε) (S : Finset (X × Y)) :
    ∑ p ∈ S, G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2 ≤ ε := by
  simp only [condFail_eq_tensor]
  rw [povmValue_eq_tensor] at hfail
  exact (BipartiteModel.tensor ψ).sum_mul_condFail_le (norm_evec_eq_one hψ) hfail S

/-- **The blueprint's "divided by the probability that the subtest is selected", in the form the
Pauli basis test needs.** An auxiliary weighting `ν` on an index set and a map `q` to question
pairs whose *pushforward* stays below `μ / c` gives `∑_i ν i · condFail (q i) ≤ ε / c`. Unlike
`sum_condFail_le_of_le` this asks nothing of `q`: the subtests of the Pauli basis test are
indexed by the verifier's content, and several contents give the same question pair whenever the
types involved do not read all of it --- a `(Pauli, W)` question reads none of it at all. -/
theorem sum_condFail_le_of_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq X] [DecidableEq Y]
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue G ψ MA MB ≤ ε) (ν : ι → ℝ)
    (q : ι → X × Y) {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ i ∈ univ.filter fun i => q i = p, ν i ≤ G.μ p.1 p.2) :
    ∑ i, ν i * condFail G ψ MA MB (q i).1 (q i).2 ≤ ε / c := by
  simp only [condFail_eq_tensor]
  rw [povmValue_eq_tensor] at hfail
  exact (BipartiteModel.tensor ψ).sum_condFail_le_of_pushforward (norm_evec_eq_one hψ) hfail ν
    q hc hpush

/-- **The blueprint's "divided by the probability that the subtest is selected".** An auxiliary
distribution `ν` on an index set that injects into the question pairs, with `c · ν i` below the
question probability at each, has `∑_i ν i · condFail ≤ ε / c`: the conditional error of the
subtest, at the cost of its selection probability `c`. -/
theorem sum_condFail_le_of_le {ι : Type*} [Fintype ι]
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue G ψ MA MB ≤ ε) (ν : ι → ℝ)
    (q : ι → X × Y) (hq : Function.Injective q) {c : ℝ} (hc : 0 < c)
    (hνμ : ∀ i, c * ν i ≤ G.μ (q i).1 (q i).2) :
    ∑ i, ν i * condFail G ψ MA MB (q i).1 (q i).2 ≤ ε / c := by
  simp only [condFail_eq_tensor]
  rw [povmValue_eq_tensor] at hfail
  exact (BipartiteModel.tensor ψ).sum_condFail_le_of_le (norm_evec_eq_one hψ) hfail ν q hq hc
    hνμ

/-! ## Products, and the order reversal

`lem:qld-obs-commutation` needs one algebraic rule on top of the estimate above: if each of two of
Alice's operators is cross-close to one of Bob's, then their *product* is cross-close to the
product of Bob's **in the reverse order**. The reversal is not an accident of bookkeeping; it is
where it comes from. Split

```
AB ⊗ Id - Id ⊗ B'A' = (A ⊗ Id)(B ⊗ Id - Id ⊗ B') + (Id ⊗ B')(A ⊗ Id - Id ⊗ A')
```

--- the second step is legitimate because `A ⊗ Id` and `Id ⊗ B'` commute, and it is that commuting
step that puts `B'` on the *left* of `A'`. Each summand then loses its front factor to a bound on
its operator norm (`BipartiteModel.xNorm_mul_le`, here in the tensor-product model).

This is stated on the unsquared deviation, because the triangle inequality is what the argument
uses; `xSqNorm_mul_le` squares it at the cost of the usual factor two.
-/

section Reversal

variable {ψ : dA × dB → ℂ}

/-- The squared cross-party deviation as a `snorm` on the joint space, which is the form the
chains of the appendix are run in. -/
theorem xSqNorm_eq_snorm_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) (dA × dB) ℂ) - bOp B) ^ 2 := by
  rw [xSqNorm_eq_sq, xNorm_eq_snorm]

/-- The weighted, doubly indexed form of `xSqNorm_eq_snorm_sq`: the shape every item of
`lem:qld-win` is stated in, rewritten for the triangle inequalities on the joint space. -/
theorem sum_weighted_xSqNorm_eq {ι κ : Type*} [Fintype κ] (ψ : dA × dB → ℂ) (w : ι → ℝ)
    (S : Finset ι) (Q : ι → κ → Matrix dA dA ℂ) (R : ι → κ → Matrix dB dB ℂ) :
    ∑ i ∈ S, w i * ∑ o, xSqNorm ψ (Q i o) (R i o)
      = ∑ i ∈ S, w i * ∑ o,
          snorm ψ ((aOp (Q i o) : Matrix (dA × dB) (dA × dB) ℂ) - bOp (R i o)) ^ 2 :=
  Finset.sum_congr rfl fun i _ => by
    rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => xSqNorm_eq_snorm_sq ψ (Q i o) (R i o)]

/-- The same with the two sides exchanged, for a link the chain traverses backwards. -/
theorem sum_weighted_xSqNorm_eq' {ι κ : Type*} [Fintype κ] (ψ : dA × dB → ℂ) (w : ι → ℝ)
    (S : Finset ι) (Q : ι → κ → Matrix dA dA ℂ) (R : ι → κ → Matrix dB dB ℂ) :
    ∑ i ∈ S, w i * ∑ o, xSqNorm ψ (Q i o) (R i o)
      = ∑ i ∈ S, w i * ∑ o,
          snorm ψ ((bOp (R i o) : Matrix (dA × dB) (dA × dB) ℂ) - aOp (Q i o)) ^ 2 :=
  Finset.sum_congr rfl fun i _ => by
    refine congrArg _ (Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => ?_)
    rw [xSqNorm_eq_snorm_sq ψ (Q i o) (R i o), snorm_sub_comm]

omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl

omit [DecidableEq dB] in
theorem norm_stateVecB_eq_snorm (ψ : dA × dB → ℂ) (B : Matrix dB dB ℂ) :
    ‖stateVecB ψ B‖ = snorm ψ (bOp B : Matrix (dA × dB) _ ℂ) := rfl

/-- **The order-reversal rule.** If `A ⊗ Id` is `K`-boundedly close to `Id ⊗ A'` and `B ⊗ Id` to
`Id ⊗ B'`, then `AB ⊗ Id` is close to `Id ⊗ B'A'`: Bob's factors appear in the opposite order,
and each deviation is paid for by the operator norm of the factor in front of it. -/
theorem xNorm_mul_le {K L : ℝ} (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Bnd (aOp A : Matrix (dA × dB) _ ℂ) K) (hB' : Bnd (bOp B' : Matrix (dA × dB) _ ℂ) L) :
    xNorm ψ (A * B) (B' * A') ≤ K * xNorm ψ B B' + L * xNorm ψ A A' := by
  simp only [xNorm_eq_tensor]
  exact (BipartiteModel.tensor ψ).xNorm_mul_le A B A' B' ((BipartiteModel.bnd_tensor ψ).2 hA)
    ((BipartiteModel.bnd_tensor ψ).2 hB')

/-- The order reversal for contractions, which is how every consumer uses it: POVM elements and
generalized observables are bounded by one on either factor. -/
theorem xNorm_mul_le_one (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
    xNorm ψ (A * B) (B' * A') ≤ xNorm ψ B B' + xNorm ψ A A' := by
  have h := xNorm_mul_le (ψ := ψ) A B A' B' (bnd_aOp hA) (bnd_bOp hB')
  rwa [one_mul, one_mul] at h

/-- The squared form of the order reversal, at the usual cost of a factor two. -/
theorem xSqNorm_mul_le_one (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
    xSqNorm ψ (A * B) (B' * A') ≤ 2 * xSqNorm ψ B B' + 2 * xSqNorm ψ A A' := by
  simp only [xSqNorm_eq_tensor]
  exact (BipartiteModel.tensor ψ).xSqNorm_mul_le_one A B A' B'
    ((BipartiteModel.bnd_tensor ψ).2 (bnd_aOp hA)) ((BipartiteModel.bnd_tensor ψ).2 (bnd_bOp hB'))

/-! ### A sum inside a deviation

Pushing a sum inside a deviation costs the number of terms; the appendix's chains need it when a
marginal of a joint measurement replaces the measurement itself. -/

theorem stateSqNorm_sub_comm (ψ : dA × dB → ℂ) (M N : Matrix dA dA ℂ) :
    stateSqNorm ψ (M - N) = stateSqNorm ψ (N - M) :=
  (BipartiteModel.tensor ψ).stateSqNorm_sub_comm M N

theorem norm_stateVecB_sub_comm (ψ : dA × dB → ℂ) (M N : Matrix dB dB ℂ) :
    ‖stateVecB ψ (M - N)‖ = ‖stateVecB ψ (N - M)‖ :=
  (BipartiteModel.tensor ψ).swap.stateNorm_sub_comm M N

omit [DecidableEq dA] in
/-- Pushing a sum inside a deviation costs the number of terms. -/
theorem stateSqNorm_sum_le {κ : Type*} [Fintype κ] (ψ : dA × dB → ℂ) (f : κ → Matrix dA dA ℂ) :
    stateSqNorm ψ (∑ k, f k) ≤ (Fintype.card κ : ℝ) * ∑ k, stateSqNorm ψ (f k) := by
  classical
  exact (BipartiteModel.tensor ψ).stateSqNorm_sum_le f

/-! ### Transferring an anticommutation across the two factors

This is the shape the anticommuting case of `lem:qld-obs-commutation` needs, and it is where the
sign comes from. Suppose `A ⊗ Id ~ Id ⊗ A'` and `B ⊗ Id ~ Id ⊗ B'`. Then

```
AB + BA ⊗ Id = [AB ⊗ Id - Id ⊗ B'A'] + [Id ⊗ (A'B' + B'A')] + [BA ⊗ Id - Id ⊗ A'B']
```

is an identity --- Bob's two products cancel --- and its three summands are, in order: an order
reversal, Bob's own anticommutator, and the other order reversal. So if Bob's two operators
anticommute on the state then Alice's two *anti*commute on it as well: the product picked up a
reversal on the way across and a second one on the way back, and the two reversals do not cancel
because the anticommutator in the middle is a sum, not a difference. -/

/-- **An anticommutation on Bob's side transfers to Alice's**, at the cost of the two cross-party
deviations counted twice each (`BipartiteModel.stateNorm_anticomm_le`). Every operator in sight
is assumed to be a contraction, which is what a `±1`-observable coming from a two-outcome POVM
is. -/
theorem norm_stateVec_anticomm_le (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB : Bᴴ * B ≤ (1 : Matrix dA dA ℂ))
    (hA' : A'ᴴ * A' ≤ (1 : Matrix dB dB ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
    ‖stateVec ψ (A * B + B * A)‖
      ≤ 2 * xNorm ψ A A' + 2 * xNorm ψ B B' + ‖stateVecB ψ (A' * B' + B' * A')‖ := by
  simp only [xNorm_eq_tensor]
  exact (BipartiteModel.tensor ψ).stateNorm_anticomm_le A B A' B'
    ((BipartiteModel.tensor ψ).bnd_πA_of_star_mul_self_le hA)
    ((BipartiteModel.tensor ψ).bnd_πA_of_star_mul_self_le hB)
    ((BipartiteModel.tensor ψ).swap.bnd_πA_of_star_mul_self_le hA')
    ((BipartiteModel.tensor ψ).swap.bnd_πA_of_star_mul_self_le hB')

/-! ### Two-outcome observables

A two-outcome POVM's `±1`-observable is the difference of its two elements, which is what
`obsOf sgn` computes; stating it as a difference is what makes the contraction bound of
`POVM.sub_mul_self_le_one` available, and every consumer of the order reversal needs that. -/

/-- The `±1`-observable of a POVM with outcomes in `F_2`. -/
def obs2 {d : Type*} [Fintype d] [DecidableEq d] (P : POVM (ZMod 2) d) : Matrix d d ℂ :=
  ((P.mats 0).val) - ((P.mats 1).val)

omit [Fintype X] in
theorem obsOf_sgn_eq_obs2 (M : X → POVM (ZMod 2) dA) (x : X) :
    obsOf sgn M x = obs2 (M x) := by
  rw [obsOf, obs2, show (univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, sgn_zero, sgn_one]
  module

/-- **The observable of a coarse-grained POVM**, in terms of the original one. -/
theorem obs2_map (P : POVM A dA) (f : A → ZMod 2) :
    obs2 (P.map f) = ∑ x : A, sgn (f x) • ((P.mats x).val) := by
  classical
  have hsplit : ∀ b : ZMod 2, (((P.map f).mats b).val)
      = ∑ x ∈ univ.filter fun x => f x = b, ((P.mats x).val) := fun b =>
    AddSubmonoidClass.coe_finsetSum _ _
  rw [obs2, hsplit, hsplit,
    ← Finset.sum_fiberwise (univ : Finset A) f fun x => sgn (f x) • ((P.mats x).val)]
  rw [show (univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h0 : (∑ x ∈ univ.filter fun x => f x = 0, sgn (f x) • ((P.mats x).val))
      = ∑ x ∈ univ.filter fun x => f x = 0, ((P.mats x).val) :=
    Finset.sum_congr rfl fun x hx => by
      rw [(Finset.mem_filter.mp hx).2, sgn_zero, one_smul]
  have h1 : (∑ x ∈ univ.filter fun x => f x = 1, sgn (f x) • ((P.mats x).val))
      = -∑ x ∈ univ.filter fun x => f x = 1, ((P.mats x).val) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x hx => by
      rw [(Finset.mem_filter.mp hx).2, sgn_one, neg_one_smul]
  rw [h0, h1, sub_eq_add_neg]

theorem obs2_conjTranspose {d : Type*} [Fintype d] [DecidableEq d] (P : POVM (ZMod 2) d) :
    (obs2 P)ᴴ = obs2 P := POVM.sub_conjTranspose P 0 1

theorem obs2_mul_self_le_one {d : Type*} [Fintype d] [DecidableEq d] (P : POVM (ZMod 2) d) :
    (obs2 P)ᴴ * obs2 P ≤ (1 : Matrix d d ℂ) := by
  rw [obs2_conjTranspose]
  exact POVM.sub_mul_self_le_one P 0 1

/-! ### The swap, for mixed operators

`norm_stateVecB` says Bob's norm is Alice's norm of the swapped state, but only for an operator
sitting on one factor. The chain below needs it for a *difference* of one operator on each factor,
and the clean statement is at the level of vectors: a Kronecker product applied to the swapped
state is the swap of the exchanged product applied to the state. Everything else follows by
linearity. -/

omit [DecidableEq dA] [DecidableEq dB] in
theorem mulVec_kronecker_swapVec (X : Matrix dB dB ℂ) (Y : Matrix dA dA ℂ)
    (ψ : dA × dB → ℂ) :
    (X ⊗ₖ Y) *ᵥ swapVec ψ = swapVec ((Y ⊗ₖ X) *ᵥ ψ) := by
  classical
  funext p
  obtain ⟨j, i⟩ := p
  show ∑ q : dB × dA, (X ⊗ₖ Y) (j, i) q * swapVec ψ q
      = ∑ q : dA × dB, (Y ⊗ₖ X) (i, j) q * ψ q
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  show X j j' * Y i i' * ψ (i', j') = Y i i' * X j j' * ψ (i', j')
  ring

omit [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
theorem swapVec_sub (u v : dA × dB → ℂ) :
    swapVec (u - v) = swapVec u - swapVec v := rfl

omit [DecidableEq dA] [DecidableEq dB] in
theorem norm_swapVec (v : dA × dB → ℂ) : ‖evec (swapVec v)‖ = ‖evec v‖ := by
  classical
  rw [evec, evec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun _ => rfl

/-- **The swap exchanges the two sides of a cross-party deviation.** -/
theorem snorm_swapVec_aOp_sub_bOp (ψ : dA × dB → ℂ) (X : Matrix dB dB ℂ)
    (Y : Matrix dA dA ℂ) :
    snorm (swapVec ψ) ((aOp X : Matrix (dB × dA) (dB × dA) ℂ) - bOp Y) = xNorm ψ Y X := by
  rw [snorm, Matrix.sub_mulVec, aOp, bOp, mulVec_kronecker_swapVec, mulVec_kronecker_swapVec,
    ← swapVec_sub, norm_swapVec, xNorm_eq_snorm, snorm, Matrix.sub_mulVec, aOp, bOp,
    evec_sub, evec_sub, norm_sub_rev]

omit [DecidableEq dB] in
/-- The same for a single operator on Bob's factor. -/
theorem snorm_swapVec_aOp (ψ : dA × dB → ℂ) (X : Matrix dB dB ℂ) :
    snorm (swapVec ψ) (aOp X : Matrix (dB × dA) (dB × dA) ℂ) = ‖stateVecB ψ X‖ := by
  rw [snorm, aOp, mulVec_kronecker_swapVec, norm_swapVec, norm_stateVecB_eq_snorm, snorm, bOp]

/-! ### The commutator form of the transfer

The same split as `norm_stateVec_anticomm_le`, with the middle term a commutator rather than an
anticommutator: Bob's two products cancel either way. -/

theorem norm_stateVec_comm_le (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB : Bᴴ * B ≤ (1 : Matrix dA dA ℂ))
    (hA' : A'ᴴ * A' ≤ (1 : Matrix dB dB ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
    ‖stateVec ψ (A * B - B * A)‖
      ≤ 2 * xNorm ψ A A' + 2 * xNorm ψ B B' + ‖stateVecB ψ (B' * A' - A' * B')‖ := by
  simp only [xNorm_eq_tensor]
  exact (BipartiteModel.tensor ψ).stateNorm_comm_le A B A' B'
    ((BipartiteModel.tensor ψ).bnd_πA_of_star_mul_self_le hA)
    ((BipartiteModel.tensor ψ).bnd_πA_of_star_mul_self_le hB)
    ((BipartiteModel.tensor ψ).swap.bnd_πA_of_star_mul_self_le hA')
    ((BipartiteModel.tensor ψ).swap.bnd_πA_of_star_mul_self_le hB')

end Reversal

end MIPRE

end

end
