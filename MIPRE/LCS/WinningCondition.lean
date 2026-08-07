/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic
import MIPRE.LCS.Observable
import MIPRE.LCS.Common
import MIPRE.LCS.Strategy.ProjectorStrategy
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Winning Condition and Loss Operators

This module defines the operator-valued winning and loss expressions attached to an LCS game
and a projector strategy.

Its main result is a sum-of-squares decomposition of the local loss operator, following the
paper's algebraic winning-condition identities.
-/

namespace MIPRE.LCS



variable {G : Layout} (game : Game G)
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable (strat : ProjectorStrategy R G)

local notation "A[" i ", " j "]" => ProjectorStrategy.aliceObs strat i j
local notation "B[" j "]" => ProjectorStrategy.bobObs strat j
local notation "E[" i ", " x "]" => strat.E i x
local notation "F[" j ", " y "]" => strat.F j y
local notation "b[" i "]" => game.b i

/-- Paper-style notation for `ProjectorStrategy.aliceRowProd strat i`. -/
local notation "∏ₐ[" i "]" => ProjectorStrategy.aliceRowProd strat i

section LocalOperators
/-! ## Local Operators
This section defines the winning assignments for a constraint and the associated local winning
and loss operators.
-/

/-- The assignments satisfying equation `i` in the game `game`. -/
def winningAssignments (i : Fin G.r) : Finset (Layout.Assignment G i) :=
  Finset.univ.filter (fun α ↦ (∑ j : G.V i, (α j : ZMod 2)) = b[i])

/-- The local winning operator for a single edge `(i, j)`. -/
noncomputable def localWinningOperator (i : Fin G.r) (j : G.V i) : R :=
  ∑ x ∈ winningAssignments game i, E[i, x] * F[j, x j]

/-- The local loss operator for a single edge (i, j). -/
noncomputable def localLossOperator (i : Fin G.r) (j : G.V i) : R :=
  1 - localWinningOperator game strat i j

end LocalOperators

local notation "S[" i "]" => winningAssignments game i

section WinningProjectorIdentities
/-!
## Winning Projector Identities
Two local projector identities used in the sum-of-squares derivation.
-/

omit [StarModule ℂ R] in
/-- Lemma 4.7.1: the sum of winning projectors equals the signed row-product expression. -/
lemma sum_winning_projectors_eq_row_observable (i : Fin G.r) :
  (∑ x ∈ S[i], E[i, x]) =
  (1/2 : ℂ) • (1 + (-1 : ℂ)^(b[i]).val • ∏ₐ[i]) := by
  classical
  have hsum_one := (strat.alice_ms i).sum_one
  let prodA : R := ∏ₐ[i]
  let rhs : R := (1/2 : ℂ) • (1 + (-1 : ℂ)^(b[i]).val • prodA)
  -- The key step: show per-projector equality, then sum
  suffices h : ∀ x : Layout.Assignment G i,
      (∑ y ∈ S[i], E[i, y]) * E[i, x] = rhs * E[i, x] by
    calc ∑ x ∈ S[i], E[i, x]
        = (∑ x ∈ S[i], E[i, x]) * 1 := by exact (mul_one _).symm
      _ = (∑ x ∈ S[i], E[i, x]) * ∑ x, E[i, x] := by rw [hsum_one]
      _ = ∑ x, (∑ y ∈ S[i], E[i, y]) * E[i, x] :=
            by rw [Finset.mul_sum]
      _ = ∑ x, rhs * E[i, x] := by
            apply Finset.sum_congr rfl
            intro x _
            exact h x
      _ = rhs * ∑ x, E[i, x] := by rw [← Finset.mul_sum]
      _ = rhs := by rw [hsum_one, mul_one]
  intro x
  -- LHS
  rw [IsMeasurementSystem.sum_mul_single (strat.alice_ms i) S[i] x]
  -- RHS: expand
  have hprod : prodA * E[i, x] =
      ((G.V i).attach.prod fun j ↦ (-1 : ℂ) ^ (x j).val) • E[i, x] :=
    ProjectorStrategy.aliceObs_noncommProd_mul_E strat i _ x
      (fun j _ j' _ _ ↦ ProjectorStrategy.aliceObs_commute strat i j j')
  have hsign : ((G.V i).attach.prod fun j ↦ (-1 : ℂ) ^ (x j).val) =
      (-1 : ℂ) ^ ((∑ j : G.V i, (x j : ZMod 2)).val) :=
    prod_sign_eq_sum_sign i x
  -- Expand rhs * E i x
  -- Directly compute both sides and match via sign_indicator
  conv_rhs =>
    unfold rhs
    rw [smul_mul_assoc, add_mul, one_mul, smul_mul_assoc, hprod, hsign, smul_add,
        smul_smul, smul_smul, ← add_smul]
  rw [sign_indicator (b[i]) (∑ j : G.V i, (x j : ZMod 2))]
  simp [winningAssignments, Finset.mem_filter]

omit [StarModule ℂ R] in
/-- Lemma 4.7.2: the marginal projector sum equals the signed local observable expression. -/
lemma sum_marginal_projectors_eq_half_one_add_aliceObs (i : Fin G.r) (j : G.V i) (y : ZMod 2) :
  (∑ x ∈ Finset.univ.filter (fun x : Layout.Assignment G i ↦ x j = y), E[i, x]) =
    (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • A[i, j]) := by
  classical
  let A : R := ∑ x ∈ Finset.univ.filter (fun x : Layout.Assignment G i ↦ x j = 0), E[i, x]
  let B : R := ∑ x ∈ Finset.univ.filter (fun x : Layout.Assignment G i ↦ x j = 1), E[i, x]
  -- inducedMeasurementSystem.sum_one gives A + B = 1 directly,
  -- replacing the manual partition argument (hnot + hpart)
  have hind := IsMeasurementSystem.induced
    (strat.E i) (strat.alice_ms i) (fun x ↦ x j)
  have hpart : A + B = 1 := by
    have h := hind.sum_one
    rw [sum_univ_zmod_two] at h
    simp only [inducedMeasurementSystem] at h
    exact h
  unfold ProjectorStrategy.aliceObs observableOfMeasurementSystem inducedMeasurementSystem
  rcases zmod_two_eq_zero_or_one y with rfl | rfl
  · change A = _
    simp only [ZMod.val_zero, pow_zero, one_smul]
    rw [← hpart]; module
  · change B = _
    simp only [zmod_two_val_one, pow_one]
    rw [← hpart]; module



end WinningProjectorIdentities

-- Helper: Alice row product is involutive (RP² = 1)
omit [StarModule ℂ R] in
private lemma aliceRowProd_mul_self (i : Fin G.r) :
    ∏ₐ[i] * ∏ₐ[i] = 1 := by
  have hsum := (strat.alice_ms i).sum_one
  have hcomm :
      (((G.V i).attach : Set (G.V i)).Pairwise
        (fun j j' ↦
          Commute (ProjectorStrategy.aliceObs strat i j)
            (ProjectorStrategy.aliceObs strat i j'))) :=
    fun j _ j' _ _ ↦
      ProjectorStrategy.aliceObs_commute strat i j j'
  suffices h : ∀ x : Layout.Assignment G i,
      ∏ₐ[i] *
        ∏ₐ[i] *
          strat.E i x = strat.E i x by
    calc ∏ₐ[i] *
          ∏ₐ[i]
        = _ * 1 := (mul_one _).symm
      _ = _ * ∑ x, strat.E i x := by rw [hsum]
      _ = ∑ x, _ * strat.E i x :=
          Finset.mul_sum _ _ _
      _ = ∑ x, strat.E i x := by
          apply Finset.sum_congr rfl
          intro x _; exact h x
      _ = 1 := hsum
  intro x
  unfold ProjectorStrategy.aliceRowProd
  rw [mul_assoc,
      ProjectorStrategy.aliceObs_noncommProd_mul_E strat i _ x hcomm,
      Algebra.mul_smul_comm,
      ProjectorStrategy.aliceObs_noncommProd_mul_E strat i _ x hcomm,
      smul_smul]
  simp only [← Finset.prod_mul_distrib, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, Finset.prod_const_one, one_smul]

section LocalLossSOS
/-!
## Local Loss SOS
This section derives the sum-of-squares decomposition of the local loss operator by a sequence
of private rewriting lemmas.
-/

omit [Algebra ℂ R] [StarModule ℂ R] in
private lemma local_loss_sos_step1 (i : Fin G.r) (j : G.V i) :
  localLossOperator game strat i j =
    1 - ∑ y : ZMod 2, F[j, y] * (∑ x ∈ S[i].filter (fun x ↦ x j = y), E[i, x]) := by
  unfold localLossOperator localWinningOperator
  congr 1
  rw [show (∑ y : ZMod 2, F[j, y] * (∑ x ∈ S[i].filter (fun x ↦ x j = y), E[i, x]))
      = ∑ y : ZMod 2, ∑ x ∈ S[i].filter (fun x ↦ x j = y), E[i, x] * F[j, y] by
    congr 1; ext y
    rw [Finset.mul_sum]
    congr 1; ext x
    exact (strat.alice_bob_commute i ↑j x y).symm]
  rw [← Finset.sum_fiberwise S[i] (fun x ↦ x j) (fun x ↦ E[i, x] * F[j, x j])]
  congr 1; ext y
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_filter] at hx
  rw [hx.2]

omit [StarModule ℂ R] in
private lemma local_loss_sos_step2 (i : Fin G.r) (j : G.V i) :
    1 - ∑ y : ZMod 2, F[j, y] * (∑ x ∈ S[i].filter (fun x ↦ x j = y), E[i, x]) =
    1 - (1 / 4 : ℂ) • ∑ y : ZMod 2,
      F[j, y] * ((1 + (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i]) *
                 (1 + (-1 : ℂ) ^ y.val • A[i, j])) := by
  classical
  congr 1
  -- Pull (1/4) scalar inside the RHS sum
  rw [Finset.smul_sum]
  -- Now both sides are ∑ y, ...; prove pointwise
  apply Finset.sum_congr rfl
  intro y _
  -- Rewrite the filtered sum as intersection via IsMeasurementSystem.sum_mul_sum
  rw [finset_filter_eq_inter_univ_filter, ← IsMeasurementSystem.sum_mul_sum (strat.alice_ms i)]
  -- Apply the winning-projector and marginal-projector identities.
  rw [sum_marginal_projectors_eq_half_one_add_aliceObs strat i j y] -- 4.7.2
  have h471 := sum_winning_projectors_eq_row_observable game strat i
  rw [show ∑ x ∈ S[i], E[i, x] = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i])
      from h471] -- 4.7.1
  -- Simplify: F * ((1/2 • P) * (1/2 • Q)) = (1/4) • (F * (P * Q))
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_assoc]
  norm_num [mul_assoc]

omit [StarModule ℂ R] in
private lemma local_loss_sos_step3 (i : Fin G.r) (j : G.V i) :
    1 - (1 / 4 : ℂ) • ∑ y : ZMod 2,
      F[j, y] * ((1 + (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i]) *
                 (1 + (-1 : ℂ) ^ y.val • A[i, j])) =
    1 - (1 / 4 : ℂ) • ∑ y : ZMod 2,
      F[j, y] * (1 + (-1 : ℂ) ^ y.val • A[i, j] +
                 (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i] +
                 ((-1 : ℂ) ^ y.val * (-1 : ℂ) ^ (b[i]).val) •
                   (∏ₐ[i] * A[i, j])) := by
  congr 1
  -- Strip (1/4) • scalar from both sides
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  -- Expand (1 + c_b • P) * (1 + c_y • A) by bilinearity,
  -- then reorder the four additive summands with abel.
  simp only [add_mul, mul_add, one_mul, mul_one,
             smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
  abel

omit [StarModule ℂ R] in
private lemma local_loss_sos_step4 (i : Fin G.r) (j : G.V i) :
    1 - (1 / 4 : ℂ) • ∑ y : ZMod 2,
      F[j, y] * (1 + (-1 : ℂ) ^ y.val • A[i, j] +
                 (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i] +
                 ((-1 : ℂ) ^ y.val * (-1 : ℂ) ^ (b[i]).val) •
                   (∏ₐ[i] * A[i, j])) =
    1 - (1 / 4 : ℂ) • (1 + B[j] * A[i, j] +
                         (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i] +
                         B[j] * ((-1 : ℂ) ^ (b[i]).val • (∏ₐ[i] * A[i, j]))) := by
  congr 1; congr 1
  -- Split ∑ y : ZMod 2 into y = 0 and y = 1
  rw [sum_univ_zmod_two]
  -- (-1)^0 = 1, (-1)^1 = -1
  simp only [ZMod.val_zero, pow_zero, one_smul, one_mul,
             zmod_two_val_one, pow_one, neg_smul, neg_mul]
  -- B[j] = F[j, 0] - F[j, 1]  and F[j, 0] + F[j, 1] = 1
  have ⟨hbob_inv, hone⟩ := ProjectorStrategy.bob_measurement_recover strat ↑j
  have hbob : B[j] = strat.F j 0 - strat.F j 1 := hbob_inv.symm
  -- Abbreviate for readability
  set F0 := F[j, 0]
  set F1 := F[j, 1]
  set Aj := A[i, j]
  set RP := ∏ₐ[i]
  set c := (-1 : ℂ) ^ (b[i]).val
  -- Distribute F * (four-term sum) and normalize negations
  simp only [mul_add, mul_neg, mul_smul_comm]
  -- Collect the 4 pairs using auxiliary identities
  have h1 : F0 * (1 : R) + F1 * 1 = 1 := by simp [hone]
  have h2 : F0 * Aj + -(F1 * Aj) = B[j] * Aj := by
    rw [← sub_eq_add_neg, ← sub_mul, ← hbob]
  have h3 : c • (F0 * RP) + c • (F1 * RP) = c • RP := by
    rw [← smul_add, ← add_mul, hone, one_mul]
  have h4 : c • (F0 * (RP * Aj)) + -(c • (F1 * (RP * Aj))) =
      c • (B[j] * (RP * Aj)) := by
    rw [← sub_eq_add_neg, ← smul_sub, ← sub_mul, ← hbob]
  -- Rearrange the 8 terms into the 4 pairs and apply the identities
  calc F0 * 1 + F0 * Aj + c • (F0 * RP) + c • (F0 * (RP * Aj)) +
       (F1 * 1 + -(F1 * Aj) + c • (F1 * RP) + -(c • (F1 * (RP * Aj))))
      = (F0 * 1 + F1 * 1) + (F0 * Aj + -(F1 * Aj)) +
        (c • (F0 * RP) + c • (F1 * RP)) +
        (c • (F0 * (RP * Aj)) + -(c • (F1 * (RP * Aj)))) := by abel
    _ = 1 + B[j] * Aj + c • RP + c • (B[j] * (RP * Aj)) := by
        rw [h1, h2, h3, h4]

omit [StarModule ℂ R] in
private lemma local_loss_sos_step5 (i : Fin G.r) (j : G.V i) :
    1 - (1 / 4 : ℂ) • (1 + B[j] * A[i, j] + (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i] +
      B[j] * ((-1 : ℂ) ^ (b[i]).val • (∏ₐ[i] * A[i, j]))) =
    (1 / 8 : ℂ) • (
      (1 - B[j] * A[i, j])^2 +
      (1 - (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i])^2 +
      (1 - (-1 : ℂ) ^ (b[i]).val • (∏ₐ[i] * A[i, j] * B[j]))^2) := by
  -- Define O1, O2, O3 to make the expression more readable
  let O1 := B[j] * A[i, j]
  let O2 := (-1 : ℂ) ^ (b[i]).val • ∏ₐ[i]
  let O3 := (-1 : ℂ) ^ (b[i]).val • (∏ₐ[i] * A[i, j] * B[j])
  -- Rearange to be able to rewrite in terms of O1, O2, O3
  rw [mul_smul_comm, ← mul_assoc,
    (ProjectorStrategy.bobObs_commute_aliceRowProd strat i j).eq, mul_assoc]
  nth_rw 2 [(ProjectorStrategy.aliceObs_commute_bobObs strat i j j).symm.eq]
  rw [← mul_assoc]
  -- Perform the rewriting in terms of O1, O2, O3
  change 1 - (1 / 4 : ℂ) • (1 + O1 + O2 + O3) = (1/8 : ℂ) • ((1 - O1)^2 + (1 - O2)^2 + (1 - O3)^2)
  -- Lemmas about O1, O2, O3
  have hO1 : O1 * O1 = 1 := by
    unfold O1
    nth_rw 1 [(ProjectorStrategy.aliceObs_commute_bobObs strat i j j).symm.eq] -- B A = A B
    simp only [mul_assoc, ← mul_assoc B[↑j] B[↑j], one_mul,
      (ProjectorStrategy.isObservable_bobObs strat j).involutive,
      (ProjectorStrategy.isObservable_aliceObs strat i j).involutive]
  have hO2 : O2 * O2 = 1 := by
    unfold O2
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, aliceRowProd_mul_self strat i, sign_sq (b[i])]
    norm_num
  have hO3 : O3 * O3 = 1 := by
    unfold O3
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [sign_sq (b[i])]
    norm_num
    -- Goal: RP * A * B * (RP * A * B) = 1
    simp only [← mul_assoc]
    rw [← ProjectorStrategy.aliceObs_commute_aliceRowProd strat i j]
    rw [mul_assoc (A[i,j] * ∏ₐ[i]) B[j] ∏ₐ[i]]
    rw [(ProjectorStrategy.bobObs_commute_aliceRowProd strat i j).eq]
    rw [← mul_assoc ]
    rw [mul_assoc (A[i,j] * ∏ₐ[i] * ∏ₐ[i] * B[j]) A[i,j] B[j]]
    rw [ProjectorStrategy.aliceObs_commute_bobObs strat i j j]
    rw [← mul_assoc]
    simp only [aliceRowProd_mul_self, mul_one, mul_assoc,
      (ProjectorStrategy.isObservable_aliceObs strat i j).involutive,
      (ProjectorStrategy.isObservable_bobObs strat j).involutive]
  -- expand the square on RHS
  simp only [sq, sub_mul, mul_sub, one_mul, mul_one]
  rw [hO1, hO2, hO3]
  module




omit [StarModule ℂ R] in
/-- The Sum of Squares decomposition of the local loss operator. -/
theorem localLossOperator_sos (i : Fin G.r) (j : G.V i) :
  localLossOperator game strat i j =
    (1/8 : ℂ) • (
      (1 - B[j] * A[i, j])^2 +
      (1 - (-1 : ℂ)^(b[i]).val • ∏ₐ[i])^2 +
      (1 - (-1 : ℂ)^(b[i]).val • (∏ₐ[i] * A[i, j] * B[j]))^2
    ) := by
  rw [local_loss_sos_step1 game strat i j,
      local_loss_sos_step2 game strat i j,
      local_loss_sos_step3 game strat i j,
      local_loss_sos_step4 game strat i j,
      local_loss_sos_step5 game strat i j]

end LocalLossSOS

section GlobalOperators
/-! ## Global Operators
The overall winning and loss operators are obtained by averaging the local quantities over the
question graph of the game.
-/

/-- The total winning operator `v` is the average of the local winning operators. -/
noncomputable def winningOperator : R :=
  ∑ i : Fin G.r, ∑ j : G.V i,
  let normalization : ℂ := (G.r * (G.V i).card : ℕ)
  (1 / normalization) • localWinningOperator game strat i j

/-- The total Loss Operator `1 - v`. -/
noncomputable def lossOperator : R :=
  1 - winningOperator game strat

end GlobalOperators

end MIPRE.LCS
