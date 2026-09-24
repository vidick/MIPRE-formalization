/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.StarOrder
import MIPRE.Foundations.CommutingOperator
import MIPRE.Foundations.GameTransport
import MIPRE.Foundations.ValueApprox.Norms

/-!
# Bipartite correlation sets `C_q`, `C_qa`, `C_qc`

The three sets of bipartite correlations `p : X → Y → A → B → ℝ` of Tsirelson's problem
(blueprint `cor:tsirelson`):

* `Cq X Y A B`, the Born probabilities of finite-dimensional tensor-product strategies, with the
  projective measurements of `MIPRE.TensorProductStrategy`;
* `Cqa X Y A B := closure (Cq X Y A B)`, in the product topology;
* `Cqc X Y A B`, the correlations of commuting-operator strategies
  (`MIPRE.CommutingOperatorStrategy`, POVMs on a Hilbert space in universe `0`).

A game pays off linearly in a correlation (`Game.payoff`), and the values of both strategy
classes are that payoff (`TensorProductStrategy.value_eq_payoff`,
`CommutingOperatorStrategy.value_eq_payoff`). Every tensor-product strategy is a
commuting-operator strategy on `ℂ^dA ⊗ ℂ^dB` (`TensorProductStrategy.toCommuting`), so
`Cq ⊆ Cqc` and `quantumValue ≤ commutingOperatorValue`; payoffs on `Cqa` are bounded by the
quantum value, since the payoff is continuous. `Cqa ⊆ Cqc` holds as soon as `Cqc` is closed.

The commuting-operator correlations are nonnegative and sum to one for each question pair
(`CommutingOperatorStrategy.correlation_nonneg`, `correlation_sum`), by Mathlib's
`Commute.mul_nonneg`: the product of two commuting positive operators is positive. So the
commuting-operator value lies in `[0, 1]`.
-/

namespace MIPRE

open scoped BigOperators InnerProductSpace Kronecker
open Matrix

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## The payoff of a correlation -/

/-- The payoff of a correlation `p` in the game `G`: the probability of winning when the
answers `(a, b)` to the questions `(x, y)` are drawn with probability `p x y a b`. -/
noncomputable def Game.payoff (G : Game X Y A B) (p : X → Y → A → B → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * p x y a b

/-- The payoff is continuous in the correlation. -/
theorem Game.continuous_payoff (G : Game X Y A B) : Continuous G.payoff := by
  unfold Game.payoff
  fun_prop

/-! ## Tensor-product correlations -/

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-- The correlation of a tensor-product strategy: its Born-rule probabilities
`⟨ψ| A^x_a ⊗ B^y_b |ψ⟩`. -/
noncomputable def correlation (S : TensorProductStrategy G) : X → Y → A → B → ℝ :=
  fun x y a b => (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

/-- The value of a tensor-product strategy is the payoff of its correlation. -/
theorem value_eq_payoff (S : TensorProductStrategy G) : S.value = G.payoff S.correlation := rfl

/-- The correlation does not depend on the game the strategy is attached to. -/
@[simp] theorem correlation_copy (S : TensorProductStrategy G) (G' : Game X Y A B) :
    (S.copy G').correlation = S.correlation := rfl

end TensorProductStrategy

variable (X Y A B) in
/-- **`C_q`**: the correlations of finite-dimensional tensor-product strategies. The game is
immaterial (`TensorProductStrategy` only carries it as an index), so the definition quantifies
over the strategy data directly; `mem_Cq_iff` restates it for any game. -/
def Cq : Set (X → Y → A → B → ℝ) :=
  {p | ∃ (dA dB : ℕ) (ψ : Fin dA × Fin dB → ℂ) (_ : star ψ ⬝ᵥ ψ = 1)
      (PA : ProjectiveMeasurement X A (Matrix (Fin dA) (Fin dA) ℂ))
      (PB : ProjectiveMeasurement Y B (Matrix (Fin dB) (Fin dB) ℂ)),
      p = fun x y a b => (star ψ ⬝ᵥ ((PA.M x a ⊗ₖ PB.M y b) *ᵥ ψ)).re}

variable (X Y A B) in
/-- **`C_qa`**: the closure of `C_q`. -/
def Cqa : Set (X → Y → A → B → ℝ) := closure (Cq X Y A B)

/-- The correlation of a tensor-product strategy lies in `C_q`. -/
theorem TensorProductStrategy.correlation_mem_Cq {G : Game X Y A B}
    (S : TensorProductStrategy G) : S.correlation ∈ Cq X Y A B :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA, S.PB, rfl⟩

/-- Membership in `C_q`, through the strategies of any game on the same alphabets. -/
theorem mem_Cq_iff (G : Game X Y A B) {p : X → Y → A → B → ℝ} :
    p ∈ Cq X Y A B ↔ ∃ S : TensorProductStrategy G, S.correlation = p := by
  constructor
  · rintro ⟨dA, dB, ψ, hψ, PA, PB, rfl⟩
    exact ⟨⟨dA, dB, ψ, hψ, PA, PB⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact S.correlation_mem_Cq

omit [Fintype X] [Fintype Y] in
/-- `C_q ⊆ C_qa`. -/
theorem Cq_subset_Cqa : Cq X Y A B ⊆ Cqa X Y A B := subset_closure

/-- The payoff of a quantum correlation is at most the quantum value. -/
theorem payoff_le_quantumValue_of_mem_Cq (G : Game X Y A B) {p : X → Y → A → B → ℝ}
    (hp : p ∈ Cq X Y A B) : G.payoff p ≤ quantumValue G := by
  obtain ⟨S, rfl⟩ := (mem_Cq_iff G).1 hp
  exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) S

/-- The payoff of a correlation in `C_qa` is at most the quantum value: the payoff is
continuous, so the bound passes to the closure. -/
theorem payoff_le_quantumValue_of_mem_Cqa (G : Game X Y A B) {p : X → Y → A → B → ℝ}
    (hp : p ∈ Cqa X Y A B) : G.payoff p ≤ quantumValue G := by
  have hclosed : IsClosed {p : X → Y → A → B → ℝ | G.payoff p ≤ quantumValue G} :=
    isClosed_le G.continuous_payoff continuous_const
  exact closure_minimal (fun q hq => payoff_le_quantumValue_of_mem_Cq G hq) hclosed hp

/-! ## Commuting-operator correlations -/

namespace CommutingOperatorStrategy

variable (S : CommutingOperatorStrategy X Y A B)

/-- The value of a commuting-operator strategy is the payoff of its correlation. -/
theorem value_eq_payoff (G : Game X Y A B) : S.value G = G.payoff S.correlation := rfl

/-- The joint effect `E^x_a F^y_b` is a positive operator: the product of two commuting
positive operators. -/
theorem isPositive_mul (x : X) (y : Y) (a : A) (b : B) : (S.E x a * S.F y b).IsPositive := by
  rw [← ContinuousLinearMap.nonneg_iff_isPositive]
  exact Commute.mul_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive _).2 (S.E_pos x a))
    ((ContinuousLinearMap.nonneg_iff_isPositive _).2 (S.F_pos y b)) (S.commutes x y a b)

/-- Commuting-operator correlations are nonnegative. -/
theorem correlation_nonneg (x : X) (y : Y) (a : A) (b : B) : 0 ≤ S.correlation x y a b := by
  exact (S.isPositive_mul x y a b).re_inner_nonneg_right S.ψ

/-- For each question pair, commuting-operator correlations sum to one. -/
theorem correlation_sum (x : X) (y : Y) : ∑ a, ∑ b, S.correlation x y a b = 1 := by
  have h : ∑ a, ∑ b, ⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ = 1 := by
    have hF : ∑ b, S.F y b S.ψ = S.ψ := by
      rw [← _root_.sum_apply, S.F_sum y]; rfl
    have hE : ∑ a, S.E x a S.ψ = S.ψ := by
      rw [← _root_.sum_apply, S.E_sum x]; rfl
    have hsum : ∑ a, ∑ b, S.E x a (S.F y b S.ψ) = S.ψ := by
      simp_rw [← map_sum, hF, hE]
    calc ∑ a, ∑ b, ⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ
        = ⟪S.ψ, ∑ a, ∑ b, S.E x a (S.F y b S.ψ)⟫_ℂ := by simp only [inner_sum]
      _ = 1 := by
        rw [hsum, inner_self_eq_norm_sq_to_K, S.ψ_norm]
        simp
  have := congrArg Complex.re h
  simpa [correlation, Complex.re_sum] using this

/-- Commuting-operator correlations are at most one. -/
theorem correlation_le_one (x : X) (y : Y) (a : A) (b : B) : S.correlation x y a b ≤ 1 := by
  calc S.correlation x y a b ≤ ∑ b', S.correlation x y a b' :=
        Finset.single_le_sum (fun b' _ => S.correlation_nonneg x y a b') (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', S.correlation x y a' b' :=
        Finset.single_le_sum (f := fun a' => ∑ b', S.correlation x y a' b')
          (fun a' _ => Finset.sum_nonneg fun b' _ => S.correlation_nonneg x y a' b')
          (Finset.mem_univ a)
    _ = 1 := S.correlation_sum x y

/-- The value of a commuting-operator strategy is nonnegative. -/
theorem value_nonneg (G : Game X Y A B) : 0 ≤ S.value G := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  have hind : (0 : ℝ) ≤ if G.D x y a b then 1 else 0 := by split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg (G.μ_nonneg x y) hind) (S.correlation_nonneg x y a b)

/-- The value of a commuting-operator strategy is at most one. -/
theorem value_le_one (G : Game X Y A B) : S.value G ≤ 1 := by
  calc S.value G ≤ ∑ x, ∑ y, G.μ x y * ∑ a, ∑ b, S.correlation x y a b := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        cases hD : G.D x y a b with
        | false =>
          simpa [hD] using mul_nonneg (G.μ_nonneg x y) (S.correlation_nonneg x y a b)
        | true => simp
    _ = ∑ x, ∑ y, G.μ x y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [S.correlation_sum, mul_one]
    _ = 1 := G.μ_sum_one

end CommutingOperatorStrategy

/-- The values of commuting-operator strategies are bounded above (by one). -/
theorem CommutingOperatorStrategy.bddAbove_range_value (G : Game X Y A B) :
    BddAbove (Set.range fun S : CommutingOperatorStrategy X Y A B => S.value G) :=
  ⟨1, by rintro r ⟨S, rfl⟩; exact S.value_le_one G⟩

/-- A strategy's value is at most the commuting-operator value. -/
theorem CommutingOperatorStrategy.value_le_commutingOperatorValue (G : Game X Y A B)
    (S : CommutingOperatorStrategy X Y A B) : S.value G ≤ commutingOperatorValue G :=
  le_ciSup (CommutingOperatorStrategy.bddAbove_range_value G) S

/-- The commuting-operator value is nonnegative. -/
theorem commutingOperatorValue_nonneg (G : Game X Y A B) : 0 ≤ commutingOperatorValue G :=
  Real.iSup_nonneg fun S => S.value_nonneg G

/-- The commuting-operator value is at most one. -/
theorem commutingOperatorValue_le_one (G : Game X Y A B) : commutingOperatorValue G ≤ 1 :=
  Real.iSup_le (fun S => S.value_le_one G) zero_le_one

variable (X Y A B) in
/-- **`C_qc`**: the correlations of commuting-operator strategies. -/
def Cqc : Set (X → Y → A → B → ℝ) :=
  Set.range fun S : CommutingOperatorStrategy X Y A B => S.correlation

/-- The payoff of a commuting-operator correlation is at most the commuting-operator value. -/
theorem payoff_le_commutingOperatorValue_of_mem_Cqc (G : Game X Y A B)
    {p : X → Y → A → B → ℝ} (hp : p ∈ Cqc X Y A B) : G.payoff p ≤ commutingOperatorValue G := by
  obtain ⟨S, rfl⟩ := hp
  exact S.value_le_commutingOperatorValue G

/-! ## Tensor-product strategies are commuting-operator strategies -/

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-- A projection on Euclidean space, as the image of a self-adjoint idempotent matrix, is a
positive operator. -/
private theorem isPositive_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hs : star P = P) (hp : P * P = P) :
    (toEuclideanCLM (𝕜 := ℂ) P).IsPositive := by
  rw [← ContinuousLinearMap.nonneg_iff_isPositive]
  have h : toEuclideanCLM (𝕜 := ℂ) P
      = star (toEuclideanCLM (𝕜 := ℂ) P) * toEuclideanCLM (𝕜 := ℂ) P := by
    rw [← map_star, ← map_mul, hs, hp]
  rw [h]
  exact star_mul_self_nonneg _

private theorem kronecker_sum_left {m n : Type*} {ι : Type*} (s : Finset ι)
    (P : ι → Matrix m m ℂ) (Q : Matrix n n ℂ) :
    (∑ i ∈ s, P i) ⊗ₖ Q = ∑ i ∈ s, P i ⊗ₖ Q := by
  ext p q
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

private theorem kronecker_sum_right {m n : Type*} {ι : Type*} (s : Finset ι)
    (P : Matrix m m ℂ) (Q : ι → Matrix n n ℂ) :
    P ⊗ₖ (∑ i ∈ s, Q i) = ∑ i ∈ s, P ⊗ₖ Q i := by
  ext p q
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]

/-- **Finite-dimensional tensor-product data as a commuting-operator strategy**, on the
Euclidean space `ℂ^(dA × dB)`: the first player measures `A^x_a ⊗ 1`, the second `1 ⊗ B^y_b`. -/
noncomputable def ofTensor {dA dB : ℕ} (ψ : Fin dA × Fin dB → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (PA : ProjectiveMeasurement X A (Matrix (Fin dA) (Fin dA) ℂ))
    (PB : ProjectiveMeasurement Y B (Matrix (Fin dB) (Fin dB) ℂ)) :
    CommutingOperatorStrategy X Y A B where
  H := EuclideanSpace ℂ (Fin dA × Fin dB)
  ψ := WithLp.toLp 2 ψ
  ψ_norm := by
    have h := MIPRE.ValueApprox.norm_sq_toLp ψ
    rw [hψ, Complex.one_re] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin dA × Fin dB))]
  E x a := toEuclideanCLM (𝕜 := ℂ) (PA.M x a ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))
  F y b := toEuclideanCLM (𝕜 := ℂ) ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ PB.M y b)
  E_pos x a := by
    refine isPositive_toEuclideanCLM ?_ ?_
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
        ← Matrix.star_eq_conjTranspose, PA.selfAdjoint, Matrix.conjTranspose_one]
    · rw [← Matrix.mul_kronecker_mul, PA.projective, Matrix.mul_one]
  F_pos y b := by
    refine isPositive_toEuclideanCLM ?_ ?_
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.star_eq_conjTranspose, PB.selfAdjoint]
    · rw [← Matrix.mul_kronecker_mul, PB.projective, Matrix.mul_one]
  E_sum x := by
    rw [← map_sum, ← kronecker_sum_left, PA.normalized, Matrix.one_kronecker_one, map_one]
  F_sum y := by
    rw [← map_sum, ← kronecker_sum_right, PB.normalized, Matrix.one_kronecker_one, map_one]
  commutes x y a b := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

/-- The embedding preserves the Born probabilities. -/
theorem correlation_ofTensor {dA dB : ℕ} (ψ : Fin dA × Fin dB → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (PA : ProjectiveMeasurement X A (Matrix (Fin dA) (Fin dA) ℂ))
    (PB : ProjectiveMeasurement Y B (Matrix (Fin dB) (Fin dB) ℂ)) :
    (ofTensor ψ hψ PA PB).correlation =
      fun x y a b => (star ψ ⬝ᵥ ((PA.M x a ⊗ₖ PB.M y b) *ᵥ ψ)).re := by
  funext x y a b
  change (⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin dA × Fin dB)),
    toEuclideanCLM (𝕜 := ℂ) (PA.M x a ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))
      (toEuclideanCLM (𝕜 := ℂ) ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ PB.M y b)
        (WithLp.toLp 2 ψ))⟫_ℂ).re = _
  rw [toEuclideanCLM_toLp, toEuclideanCLM_toLp, MIPRE.ValueApprox.inner_toLp_toLp,
    Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- **A tensor-product strategy is a commuting-operator strategy.** -/
noncomputable def toCommuting (S : TensorProductStrategy G) : CommutingOperatorStrategy X Y A B :=
  ofTensor S.ψ S.ψ_unit S.PA S.PB

/-- The embedding preserves the correlation. -/
theorem correlation_toCommuting (S : TensorProductStrategy G) :
    S.toCommuting.correlation = S.correlation :=
  correlation_ofTensor _ _ _ _

/-- The embedding preserves the value. -/
theorem value_toCommuting (S : TensorProductStrategy G) : S.toCommuting.value G = S.value := by
  rw [CommutingOperatorStrategy.value_eq_payoff, correlation_toCommuting, value_eq_payoff]

end TensorProductStrategy

/-- `C_q ⊆ C_qc`. -/
theorem Cq_subset_Cqc : Cq X Y A B ⊆ Cqc X Y A B := by
  rintro p ⟨dA, dB, ψ, hψ, PA, PB, rfl⟩
  exact ⟨TensorProductStrategy.ofTensor ψ hψ PA PB,
    TensorProductStrategy.correlation_ofTensor _ _ _ _⟩

/-- The quantum value is at most the commuting-operator value. -/
theorem quantumValue_le_commutingOperatorValue (G : Game X Y A B) :
    quantumValue G ≤ commutingOperatorValue G :=
  Real.iSup_le (fun S => S.value_toCommuting ▸ S.toCommuting.value_le_commutingOperatorValue G)
    (commutingOperatorValue_nonneg G)

/-- `C_qa ⊆ C_qc` once `C_qc` is closed. -/
theorem Cqa_subset_Cqc_of_isClosed (h : IsClosed (Cqc X Y A B)) : Cqa X Y A B ⊆ Cqc X Y A B :=
  closure_minimal Cq_subset_Cqc h

end MIPRE
