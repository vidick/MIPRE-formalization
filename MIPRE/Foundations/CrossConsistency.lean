/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.StateDistance
import MIPRE.Foundations.POVMValue

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
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The cross-party squared deviation -/

/-- `‖(A ⊗ Id - Id ⊗ B)|ψ⟩‖²`, the appendix's `A ⊗ Id ≃ Id ⊗ B` at a single pair of
operators. -/
def xSqNorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) : ℝ :=
  ‖stateVec ψ A - stateVecB ψ B‖ ^ 2

theorem xSqNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xSqNorm ψ A B := by rw [xSqNorm]; positivity

/-- **The cross-party distance** of two families of POVMs, one on each side, relative to a
question distribution: the appendix's `M^x_a ⊗ Id ≃_δ Id ⊗ N^x_a`. -/
def xPovmDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM C dA) (N : X → POVM C dB) : ℝ :=
  ∑ x, μ x * ∑ c, xSqNorm ψ (((M x).mats c).val) (((N x).mats c).val)

/-- `M^x_a ⊗ Id ≃_δ Id ⊗ N^x_a` on `ψ`, relative to `μ`. -/
def IsXPOVMClose (μ : X → ℝ) (ψ : dA × dB → ℂ) (δ : ℝ) (M : X → POVM C dA)
    (N : X → POVM C dB) : Prop :=
  xPovmDist μ ψ M N ≤ δ

omit [DecidableEq C] in
theorem xPovmDist_nonneg {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (M : X → POVM C dA) (N : X → POVM C dB) : 0 ≤ xPovmDist μ ψ M N :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _)

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
    ∑ a, stateSqNorm ψ (((M.mats a).val)) ≤ 1 := by
  classical
  have hterm : ∀ a, (stateSqNorm ψ (((M.mats a).val)) : ℝ)
      ≤ (star ψ ⬝ᵥ ((((M.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ)).re := by
    intro a
    have hsa : (((M.mats a).val))ᴴ = ((M.mats a).val) := by
      rw [← Matrix.star_eq_conjTranspose, (M.mats a).2]
    have hdiff : (0 : Matrix dA dA ℂ)
        ≤ ((M.mats a).val) - (((M.mats a).val))ᴴ * ((M.mats a).val) := by
      rw [hsa]; exact sub_nonneg.mpr (POVM.mul_self_le_self M a)
    have hker : (0 : Matrix (dA × dB) (dA × dB) ℂ)
        ≤ (((M.mats a).val) - (((M.mats a).val))ᴴ * ((M.mats a).val))
            ⊗ₖ (1 : Matrix dB dB ℂ) :=
      Matrix.nonneg_iff_posSemidef.mpr
        ((Matrix.nonneg_iff_posSemidef.mp hdiff).kronecker
          (Matrix.PosSemidef.one : (1 : Matrix dB dB ℂ).PosSemidef))
    have hq := (Matrix.nonneg_iff_posSemidef.mp hker).dotProduct_mulVec_nonneg ψ
    rw [sub_kronecker_right, Matrix.sub_mulVec, dotProduct_sub, quadForm_eq] at hq
    have := (Complex.nonneg_iff.mp hq).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  have hsum : ∑ a, (star ψ ⬝ᵥ ((((M.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ)).re
      = (star ψ ⬝ᵥ ((∑ a, (((M.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ)).re := by
    rw [sum_quadForm ψ (univ : Finset A) fun a => (((M.mats a).val) ⊗ₖ
      (1 : Matrix dB dB ℂ)), Complex.re_sum]
  rw [hsum, ← sum_kronecker_left, POVM.sum_val, Matrix.one_kronecker_one, Matrix.one_mulVec,
    hψ, Complex.one_re]

/-- Bob's version, by the swap. -/
theorem sum_stateSqNormB_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (N : POVM B dB) :
    ∑ b, ‖stateVecB ψ (((N.mats b).val))‖ ^ 2 ≤ 1 := by
  have hψ' : star (swapVec ψ) ⬝ᵥ swapVec ψ = 1 := by rw [swapVec_dotProduct]; exact hψ
  have h := sum_stateSqNorm_le_one (dA := dB) (dB := dA) (A := B) hψ' N
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) h
  rw [norm_stateVecB, stateSqNorm]

/-! ## The engine -/

omit [DecidableEq C] in
/-- **From agreement to cross-party closeness.** For any two POVMs with the same outcome set,
the summed cross-party squared deviation is at most twice the disagreement probability. Expand
each square: the two diagonal sums are at most one (`sum_stateSqNorm_le_one`), and the cross
term is the agreement probability.

No projectivity, and no hypothesis beyond `ψ` being a unit vector. -/
theorem xSqNorm_sum_le_two_mul {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : POVM C dA) (N : POVM C dB) :
    ∑ c, xSqNorm ψ (((M.mats c).val)) (((N.mats c).val))
      ≤ 2 * (1 - ∑ c, bornProb ψ (((M.mats c).val)) (((N.mats c).val))) := by
  classical
  have hexp : ∀ c, xSqNorm ψ (((M.mats c).val)) (((N.mats c).val))
      = stateSqNorm ψ (((M.mats c).val)) + ‖stateVecB ψ (((N.mats c).val))‖ ^ 2
        - 2 * bornProb ψ (((M.mats c).val)) (((N.mats c).val)) := by
    intro c
    have hsa : (((M.mats c).val))ᴴ = ((M.mats c).val) := by
      rw [← Matrix.star_eq_conjTranspose, (M.mats c).2]
    rw [xSqNorm, norm_sub_sq (𝕜 := ℂ), inner_stateVec_stateVecB ψ hsa, stateSqNorm,
      stateNorm, bornProb]
    simp only [RCLike.re_to_complex]
    ring
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hexp c]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_stateSqNorm_le_one (dB := dB) hψ M
  have h2 := sum_stateSqNormB_le_one (dA := dA) hψ N
  linarith

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
  classical
  have hvalA : ∀ c, ((((MA x).map f).mats c).val)
      = ∑ a ∈ univ.filter fun a => f a = c, (((MA x).mats a).val) := fun c => by
    rw [show (((MA x).map f).mats c) = ∑ a ∈ univ.filter fun a => f a = c, (MA x).mats a from
      rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  have hvalB : ∀ c, ((((MB y).map g).mats c).val)
      = ∑ b ∈ univ.filter fun b => g b = c, (((MB y).mats b).val) := fun c => by
    rw [show (((MB y).map g).mats c) = ∑ b ∈ univ.filter fun b => g b = c, (MB y).mats b from
      rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  -- the Born probability of a coarse-grained outcome is the sum over its fibre
  have hborn : ∀ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      = ∑ a ∈ univ.filter fun a => f a = c, ∑ b ∈ univ.filter fun b => g b = c,
          bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    intro c
    simp only [bornProb]
    rw [hvalA c, hvalB c, sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]
  -- and the fibres of the two post-processings regroup into the agreement indicator
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hborn c]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq univ (f a) _]
  simp only [mem_univ, if_true]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : f a = g b
  · rw [if_pos h.symm, if_pos h, one_mul]
  · rw [if_neg fun hh : g b = f a => h hh.symm, if_neg h, zero_mul]

omit [Fintype X] [Fintype Y] [DecidableEq C] [DecidableEq dA] in
/-- Relabelling Bob's outcomes is data processing: a weighted sum over the relabelled outcomes is
the same weighted sum over the original ones, with the weight pulled back. -/
theorem sum_bornProb_mapB {B' : Type*} [Fintype B'] [DecidableEq B'] (EA : Matrix dA dA ℂ)
    (NB : POVM B dB) (φB : B → B') (w : B' → ℝ) :
    ∑ b', w b' * bornProb ψ EA (((NB.map φB).mats b').val)
      = ∑ b, w (φB b) * bornProb ψ EA ((NB.mats b).val) := by
  classical
  have hval : ∀ b', (((NB.map φB).mats b').val)
      = ∑ b ∈ univ.filter fun b => φB b = b', ((NB.mats b).val) := fun b' => by
    rw [show ((NB.map φB).mats b') = ∑ b ∈ univ.filter fun b => φB b = b', NB.mats b from rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  have hborn : ∀ b', bornProb ψ EA (((NB.map φB).mats b').val)
      = ∑ b ∈ univ.filter fun b => φB b = b', bornProb ψ EA ((NB.mats b).val) := by
    intro b'
    simp only [bornProb]
    rw [hval b', kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]
  rw [Finset.sum_congr rfl fun b' (_ : b' ∈ univ) => by rw [hborn b', Finset.mul_sum]]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq univ (φB b) _]
  simp only [mem_univ, if_true]

omit [Fintype X] [Fintype Y] [DecidableEq C] [DecidableEq dB] in
/-- Relabelling Alice's outcomes is data processing. -/
theorem sum_bornProb_mapA {A' : Type*} [Fintype A'] [DecidableEq A'] (NA : POVM A dA)
    (φA : A → A') (EB : Matrix dB dB ℂ) (w : A' → ℝ) :
    ∑ a', w a' * bornProb ψ (((NA.map φA).mats a').val) EB
      = ∑ a, w (φA a) * bornProb ψ ((NA.mats a).val) EB := by
  classical
  have hval : ∀ a', (((NA.map φA).mats a').val)
      = ∑ a ∈ univ.filter fun a => φA a = a', ((NA.mats a).val) := fun a' => by
    rw [show ((NA.map φA).mats a') = ∑ a ∈ univ.filter fun a => φA a = a', NA.mats a from rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  have hborn : ∀ a', bornProb ψ (((NA.map φA).mats a').val) EB
      = ∑ a ∈ univ.filter fun a => φA a = a', bornProb ψ ((NA.mats a).val) EB := by
    intro a'
    simp only [bornProb]
    rw [hval a', sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => by rw [hborn a', Finset.mul_sum]]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq univ (φA a) _]
  simp only [mem_univ, if_true]

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
  classical
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) =>
    sum_bornProb_mapB (ψ := ψ) (((NA.map φA).mats a').val) NB φB (w a')]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) =>
    sum_bornProb_mapA (ψ := ψ) NA φA ((NB.mats b).val) fun a' => w a' (φB b)]
  exact Finset.sum_comm

/-- **Accept implies agree bounds the disagreement of the coarse-grained POVMs by the
conditional failure.** -/
theorem one_sub_sum_bornProb_le_condFail {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ condFail G ψ MA MB x y := by
  classical
  have hle : condWin G ψ MA MB x y
      ≤ ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have h0 : 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) :=
      bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
    by_cases h : G.D x y a b = true
    · rw [if_pos h, if_pos (hD a b h)]
    · rw [if_neg h, zero_mul]
      exact mul_nonneg (by split_ifs <;> norm_num) h0
  rw [sum_bornProb_map, condFail]
  linarith

/-- **The master estimate.** A subtest that accepts only when two post-processings of the answers
agree bounds the cross-party deviation of the coarse-grained POVMs by twice its conditional
failure. Every item of `lem:qld-win` is an instance: name `f` and `g`, check the decider, and
read off the bound. -/
theorem xSqNorm_sum_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, xSqNorm ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ 2 * condFail G ψ MA MB x y := by
  refine le_trans (xSqNorm_sum_le_two_mul hψ _ _) ?_
  exact mul_le_mul_of_nonneg_left (one_sub_sum_bornProb_le_condFail f g hD) (by norm_num)

/-! ## The weights of the subtests -/

variable {ε : ℝ}

/-- **The conditional failures of any set of question pairs, weighted by their probabilities,
add up to at most `ε`.** `condFail_le_div` is the one-pair case. -/
theorem sum_mul_condFail_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue G ψ MA MB ≤ ε) (S : Finset (X × Y)) :
    ∑ p ∈ S, G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2 ≤ ε := by
  classical
  have heq : ∑ p : X × Y, G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2
      = 1 - povmValue G ψ MA MB := by
    rw [Fintype.sum_prod_type, one_sub_povmValue_eq]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun p _ _ => mul_nonneg (G.μ_nonneg _ _) (condFail_nonneg hψ _ _)) ?_
  rw [heq]
  exact hfail

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
  classical
  -- group the index set by its image
  have hgroup : ∑ i, ν i * condFail G ψ MA MB (q i).1 (q i).2
      = ∑ p : X × Y, (∑ i ∈ univ.filter fun i => q i = p, ν i)
          * condFail G ψ MA MB p.1 p.2 := by
    rw [← Finset.sum_fiberwise (g := q) (f := fun i => ν i * condFail G ψ MA MB (q i).1 (q i).2)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [hgroup, le_div_iff₀ hc, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum
    (g := fun p : X × Y => G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2) fun p _ => ?_) ?_
  · have h0 : 0 ≤ condFail G ψ MA MB p.1 p.2 :=
      condFail_nonneg (G := G) (ψ := ψ) (MA := MA) (MB := MB) hψ p.1 p.2
    calc (∑ i ∈ univ.filter fun i => q i = p, ν i) * condFail G ψ MA MB p.1 p.2 * c
        = c * (∑ i ∈ univ.filter fun i => q i = p, ν i) * condFail G ψ MA MB p.1 p.2 := by ring
      _ ≤ G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2 :=
          mul_le_mul_of_nonneg_right (hpush p) h0
  · exact sum_mul_condFail_le hψ hfail _

/-- **The blueprint's "divided by the probability that the subtest is selected".** An auxiliary
distribution `ν` on an index set that injects into the question pairs, with `c · ν i` below the
question probability at each, has `∑_i ν i · condFail ≤ ε / c`: the conditional error of the
subtest, at the cost of its selection probability `c`. -/
theorem sum_condFail_le_of_le {ι : Type*} [Fintype ι]
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue G ψ MA MB ≤ ε) (ν : ι → ℝ)
    (q : ι → X × Y) (hq : Function.Injective q) {c : ℝ} (hc : 0 < c)
    (hνμ : ∀ i, c * ν i ≤ G.μ (q i).1 (q i).2) :
    ∑ i, ν i * condFail G ψ MA MB (q i).1 (q i).2 ≤ ε / c := by
  classical
  have himg : ∑ i, G.μ (q i).1 (q i).2 * condFail G ψ MA MB (q i).1 (q i).2
      = ∑ p ∈ univ.image q, G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2 :=
    (Finset.sum_image (f := fun p : X × Y => G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2)
      (s := (univ : Finset ι)) (g := q) fun i _ j _ h => hq h).symm
  rw [le_div_iff₀ hc, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum
    (g := fun i => G.μ (q i).1 (q i).2 * condFail G ψ MA MB (q i).1 (q i).2)
    fun i _ => ?_) ?_
  · have h0 : 0 ≤ condFail G ψ MA MB (q i).1 (q i).2 :=
      condFail_nonneg (G := G) (ψ := ψ) (MA := MA) (MB := MB) hψ (q i).1 (q i).2
    calc ν i * condFail G ψ MA MB (q i).1 (q i).2 * c
        = c * ν i * condFail G ψ MA MB (q i).1 (q i).2 := by ring
      _ ≤ G.μ (q i).1 (q i).2 * condFail G ψ MA MB (q i).1 (q i).2 :=
          mul_le_mul_of_nonneg_right (hνμ i) h0
  · rw [himg]
    exact sum_mul_condFail_le hψ hfail _

end MIPRE

end
