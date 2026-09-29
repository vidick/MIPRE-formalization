/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import MIPRE.Foundations.Correlations
public import MIPRE.Foundations.HalmosDilation
public import MIPRE.Foundations.OperatorMatrix
public import MIPRE.Tactics

@[expose] public section

/-!
# Projective commuting-operator strategies, by a commutation-preserving dilation

The first item of Phase 1 of `planning/mipco-track.md`: the commuting-operator value `ω_co` is
attained on **projective** commuting-operator strategies (`CommutingOperatorStrategy.IsProjective`),
those whose measurement operators are all orthogonal projections. This is the model the stage
analyses are to be generalized over (`reports/co-generalization-audit.md` §4, mechanism 2): they
use projectivity, while `ω_co` is defined with positive operator valued measures.

**The dilation.** For a strategy `S` and a question `x` of the first player, put `s a := √E^x_a`
(the continuous functional calculus square root, which commutes with everything commuting with
`E^x_a`, in particular with every `F^y_b`). The Naimark matrix of `s` at a fixed answer `a₀` is a
partial isometry, and its Halmos unitary `U` on `S.H ⊗ ℂ^(A ⊕ A)` turns the diagonal
projections onto the coordinates into a projection-valued measure `P_a = U* Q_a U`
(`MIPRE/Foundations/HalmosDilation.lean`). The dilated strategy `S.dilateLeft x a₀` lives on
`S.H ⊗ ℂ^(A ⊕ A)` with the state `ψ ⊗ e_{inl a₀}`; the first player measures `P_a` at `x`
and `E^{x'}_a ⊗ 1` at the other questions, the second measures `F^y_b ⊗ 1`. Then:

* `P_a` compresses to `E^x_a` at `ψ ⊗ e_{inl a₀}`, as an operator identity, and the embedding
  intertwines each `c ⊗ 1` with `c`, so the correlation is unchanged
  (`correlation_dilateLeft`);
* `P_a` commutes with every `F^y_b ⊗ 1`, since every entry of `U` does, so the dilation is again a
  commuting-operator strategy;
* the amplification `c ↦ c ⊗ 1` is a `⋆`-homomorphism, so every question that was projective
  stays projective, and `x` becomes projective.

The second player's questions are dilated the same way with the players exchanged
(`CommutingOperatorStrategy.swap`, `dilateRight`). One question at a time, first all of the first
player's and then all of the second's, gives a projective strategy with the same correlation
(`exists_isProjective_correlation_eq`), hence `ω_co` is the supremum over projective strategies
(`commutingOperatorValue_eq_iSup_isProjective`), in the form a soundness proof consumes
(`exists_isProjective_lt_value`). The tensor-product strategies are projective commuting-operator
strategies (`TensorProductStrategy.isProjective_toCommuting`), so the projective model contains both
the tensor-product and the commuting-operator values.

No von Neumann algebra theory is used, and no comparison of projections: the defect projections of
the Naimark partial isometry are never compared, which is what the finite-dimensional dilation of
`MIPRE/Foundations/Dilation.lean` does by counting dimensions.
-/

namespace MIPRE

open scoped InnerProductSpace Kronecker
open Matrix

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

namespace CommutingOperatorStrategy

/-- A commuting-operator strategy is **projective** when every measurement operator is
idempotent; being positive, the operators are then orthogonal projections. -/
def IsProjective (S : CommutingOperatorStrategy X Y A B) : Prop :=
  (∀ x a, IsIdempotentElem (S.E x a)) ∧ ∀ y b, IsIdempotentElem (S.F y b)

/-- The strategy with the two players exchanged. -/
def swap (S : CommutingOperatorStrategy X Y A B) : CommutingOperatorStrategy Y X B A where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  E := S.F
  F := S.E
  E_pos := S.F_pos
  F_pos := S.E_pos
  E_sum := S.F_sum
  F_sum := S.E_sum
  commutes y x b a := (S.commutes x y a b).symm

@[simp]
theorem swap_E (S : CommutingOperatorStrategy X Y A B) : S.swap.E = S.F := rfl

@[simp]
theorem swap_F (S : CommutingOperatorStrategy X Y A B) : S.swap.F = S.E := rfl

/-- Exchanging the players transposes the correlation, since the two players' operators
commute. -/
theorem correlation_swap (S : CommutingOperatorStrategy X Y A B) (y : Y) (x : X) (b : B) (a : A) :
    S.swap.correlation y x b a = S.correlation x y a b := by
  show (⟪S.ψ, (S.F y b * S.E x a) S.ψ⟫_ℂ).re = (⟪S.ψ, (S.E x a * S.F y b) S.ψ⟫_ℂ).re
  rw [(S.commutes x y a b).eq]

/-- A question of the first player has an answer: its measurement sums to one on a nonzero
space. -/
theorem nonempty_left (S : CommutingOperatorStrategy X Y A B) (x : X) : Nonempty A := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 : (1 : S.H →L[ℂ] S.H) = 0 := by
    rw [← S.E_sum x, Finset.univ_eq_empty, Finset.sum_empty]
  have hψ : S.ψ = 0 := by
    simpa using congrArg (fun T : S.H →L[ℂ] S.H => T S.ψ) h1
  have hn := S.ψ_norm
  rw [hψ, norm_zero] at hn
  exact zero_ne_one hn

/-- A question of the second player has an answer. -/
theorem nonempty_right (S : CommutingOperatorStrategy X Y A B) (y : Y) : Nonempty B :=
  S.swap.nonempty_left y

/-! ## The square roots of the first player's effects -/

/-- The square root of the first player's effect `E^x_a`. -/
noncomputable def sqrtE (S : CommutingOperatorStrategy X Y A B) (x : X) (a : A) :
    S.H →L[ℂ] S.H :=
  CFC.sqrt (S.E x a)

theorem star_sqrtE (S : CommutingOperatorStrategy X Y A B) (x : X) (a : A) :
    star (S.sqrtE x a) = S.sqrtE x a :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq

theorem sqrtE_mul_self (S : CommutingOperatorStrategy X Y A B) (x : X) (a : A) :
    S.sqrtE x a * S.sqrtE x a = S.E x a :=
  CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.2 (S.E_pos x a))

theorem sum_sqrtE_mul_self (S : CommutingOperatorStrategy X Y A B) (x : X) :
    ∑ a, S.sqrtE x a * S.sqrtE x a = 1 := by
  simp_rw [sqrtE_mul_self]
  exact S.E_sum x

/-- The square roots commute with the second player's operators. -/
theorem commute_F_sqrtE (S : CommutingOperatorStrategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    Commute (S.F y b) (S.sqrtE x a) :=
  (Commute.cfcₙ_nnreal (S.commutes x y a b) _).symm

/-! ## The dilation of one question of the first player -/

section Dilation

variable [DecidableEq X] [DecidableEq A]

/-- The dilated projection-valued measure of the question `x`, as a matrix of operators on
`S.H ⊗ ℂ^(A ⊕ A)`: the Halmos dilation of the Naimark matrix of `a ↦ √E^x_a` at `a₀`. -/
noncomputable def dilProj (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ a : A) :
    Matrix (A ⊕ A) (A ⊕ A) (S.H →L[ℂ] S.H) :=
  Halmos.proj (Halmos.naimark (S.sqrtE x) a₀) a

omit [DecidableEq X] in
theorem isStarProjection_dilProj (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ a : A) :
    IsStarProjection (S.dilProj x a₀ a) :=
  Halmos.isStarProjection_proj
    (Halmos.naimark_mul_conjTranspose_mul (S.star_sqrtE x) (S.sum_sqrtE_mul_self x) a₀) a

omit [DecidableEq X] in
theorem sum_dilProj (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ : A) :
    ∑ a, S.dilProj x a₀ a = 1 :=
  Halmos.sum_proj
    (Halmos.naimark_mul_conjTranspose_mul (S.star_sqrtE x) (S.sum_sqrtE_mul_self x) a₀)

omit [DecidableEq X] in
theorem dilProj_inl_inl (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ a : A) :
    S.dilProj x a₀ a (Sum.inl a₀) (Sum.inl a₀) = S.E x a := by
  rw [dilProj, Halmos.proj_naimark_inl_inl (S.star_sqrtE x) (S.sum_sqrtE_mul_self x),
    sqrtE_mul_self]

omit [DecidableEq X] in
theorem commute_diagonal_F_dilProj (S : CommutingOperatorStrategy X Y A B) (x : X) (y : Y)
    (a₀ a : A) (b : B) :
    Commute (diagonal fun _ : A ⊕ A => S.F y b) (S.dilProj x a₀ a) :=
  Halmos.commute_diagonal_proj_naimark (S.star_sqrtE x) (fun a' => S.commute_F_sqrtE x y a' b)
    a₀ a

/-- **The commutation-preserving dilation of the first player's question `x`**, on
`S.H ⊗ ℂ^(A ⊕ A)` with the state `ψ ⊗ e_{inl a₀}`: the first player measures the dilated
projection-valued measure at `x` and `E^{x'}_a ⊗ 1` elsewhere, the second measures
`F^y_b ⊗ 1`. -/
noncomputable def dilateLeft (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ : A) :
    CommutingOperatorStrategy X Y A B where
  H := OperatorMatrix.Ampl (A ⊕ A) S.H
  ψ := OperatorMatrix.emb (Sum.inl a₀) S.ψ
  ψ_norm := by rw [OperatorMatrix.norm_emb, S.ψ_norm]
  E x' a := if x' = x then OperatorMatrix.toCLM (S.dilProj x a₀ a)
    else OperatorMatrix.amplify (ι := A ⊕ A) (H := S.H) (S.E x' a)
  F y b := OperatorMatrix.amplify (ι := A ⊕ A) (H := S.H) (S.F y b)
  E_pos x' a := by
    by_cases h : x' = x
    · rw [ite_eq_left h]
      exact OperatorMatrix.isPositive_toCLM_of_isStarProjection
        (S.isStarProjection_dilProj x a₀ a)
    · rw [ite_eq_right h]
      exact OperatorMatrix.isPositive_toCLM_diagonal (S.E_pos x' a)
  F_pos y b := OperatorMatrix.isPositive_toCLM_diagonal (S.F_pos y b)
  E_sum x' := by
    by_cases h : x' = x
    · simp only [ite_eq_left h]
      rw [← OperatorMatrix.toCLM_sum, S.sum_dilProj x a₀, OperatorMatrix.toCLM_one]
    · simp only [ite_eq_right h]
      rw [← map_sum, S.E_sum x', map_one]
  F_sum y := by rw [← map_sum, S.F_sum y, map_one]
  commutes x' y a b := by
    by_cases h : x' = x
    · rw [ite_eq_left h]
      exact ((S.commute_diagonal_F_dilProj x y a₀ a b).symm).map
        (OperatorMatrix.toCLMStarAlgHom (ι := A ⊕ A) (H := S.H))
    · rw [ite_eq_right h]
      exact (S.commutes x' y a b).map (OperatorMatrix.amplify (ι := A ⊕ A) (H := S.H))

theorem dilateLeft_E_self (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ a : A) :
    (S.dilateLeft x a₀).E x a = OperatorMatrix.toCLM (S.dilProj x a₀ a) :=
  ite_eq_left rfl

theorem dilateLeft_E_of_ne (S : CommutingOperatorStrategy X Y A B) {x x' : X} (h : x' ≠ x)
    (a₀ a : A) :
    (S.dilateLeft x a₀).E x' a = OperatorMatrix.amplify (ι := A ⊕ A) (H := S.H) (S.E x' a) :=
  ite_eq_right h

theorem dilateLeft_F (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ : A) (y : Y) (b : B) :
    (S.dilateLeft x a₀).F y b = OperatorMatrix.amplify (ι := A ⊕ A) (H := S.H) (S.F y b) :=
  rfl

/-- **The dilation preserves the correlation.** -/
theorem correlation_dilateLeft (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ : A) :
    (S.dilateLeft x a₀).correlation = S.correlation := by
  funext x' y a b
  show (⟪OperatorMatrix.emb (ι := A ⊕ A) (Sum.inl a₀) S.ψ,
    (if x' = x then OperatorMatrix.toCLM (S.dilProj x a₀ a)
      else OperatorMatrix.amplify (ι := A ⊕ A) (H := S.H) (S.E x' a))
      (OperatorMatrix.amplify (ι := A ⊕ A) (H := S.H) (S.F y b)
        (OperatorMatrix.emb (Sum.inl a₀) S.ψ))⟫_ℂ).re =
      (⟪S.ψ, S.E x' a (S.F y b S.ψ)⟫_ℂ).re
  simp only [OperatorMatrix.amplify_apply]
  rw [OperatorMatrix.toCLM_diagonal_emb (S.F y b)]
  by_cases h : x' = x
  · subst h
    rw [ite_eq_left rfl, OperatorMatrix.inner_emb_toCLM_emb, dilProj_inl_inl]
  · rw [ite_eq_right h, OperatorMatrix.toCLM_diagonal_emb, OperatorMatrix.inner_emb_emb]

theorem isIdempotentElem_dilateLeft_E_self (S : CommutingOperatorStrategy X Y A B) (x : X)
    (a₀ a : A) : IsIdempotentElem ((S.dilateLeft x a₀).E x a) := by
  rw [dilateLeft_E_self]
  exact (OperatorMatrix.isStarProjection_toCLM
    (S.isStarProjection_dilProj x a₀ a)).isIdempotentElem

theorem isIdempotentElem_dilateLeft_E_of_ne (S : CommutingOperatorStrategy X Y A B) {x x' : X}
    (h : x' ≠ x) (a₀ : A) {a : A} (hE : IsIdempotentElem (S.E x' a)) :
    IsIdempotentElem ((S.dilateLeft x a₀).E x' a) := by
  rw [dilateLeft_E_of_ne _ h]
  exact hE.map _

theorem isIdempotentElem_dilateLeft_F (S : CommutingOperatorStrategy X Y A B) (x : X) (a₀ : A)
    {y : Y} {b : B} (hF : IsIdempotentElem (S.F y b)) :
    IsIdempotentElem ((S.dilateLeft x a₀).F y b) := by
  rw [dilateLeft_F]
  exact hF.map _

end Dilation

/-! ## The dilation of one question of the second player -/

section DilationRight

variable [DecidableEq Y] [DecidableEq B]

/-- The commutation-preserving dilation of the second player's question `y`: the first
player's dilation, with the players exchanged. -/
noncomputable def dilateRight (S : CommutingOperatorStrategy X Y A B) (y : Y) (b₀ : B) :
    CommutingOperatorStrategy X Y A B :=
  (S.swap.dilateLeft y b₀).swap

theorem correlation_dilateRight (S : CommutingOperatorStrategy X Y A B) (y : Y) (b₀ : B) :
    (S.dilateRight y b₀).correlation = S.correlation := by
  funext x y' a b
  rw [dilateRight, correlation_swap, correlation_dilateLeft, correlation_swap]

theorem isIdempotentElem_dilateRight_F_self (S : CommutingOperatorStrategy X Y A B) (y : Y)
    (b₀ b : B) : IsIdempotentElem ((S.dilateRight y b₀).F y b) :=
  S.swap.isIdempotentElem_dilateLeft_E_self y b₀ b

theorem isIdempotentElem_dilateRight_F_of_ne (S : CommutingOperatorStrategy X Y A B) {y y' : Y}
    (h : y' ≠ y) (b₀ : B) {b : B} (hF : IsIdempotentElem (S.F y' b)) :
    IsIdempotentElem ((S.dilateRight y b₀).F y' b) :=
  S.swap.isIdempotentElem_dilateLeft_E_of_ne h b₀ hF

theorem isIdempotentElem_dilateRight_E (S : CommutingOperatorStrategy X Y A B) (y : Y) (b₀ : B)
    {x : X} {a : A} (hE : IsIdempotentElem (S.E x a)) :
    IsIdempotentElem ((S.dilateRight y b₀).E x a) :=
  S.swap.isIdempotentElem_dilateLeft_F y b₀ hE

end DilationRight

/-! ## Every strategy has a projective one with the same correlation -/

/-- **Every commuting-operator strategy has a projective one with the same correlation**:
the first player's questions are dilated one at a time, then the second player's. -/
theorem exists_isProjective_correlation_eq (S : CommutingOperatorStrategy X Y A B) :
    ∃ T : CommutingOperatorStrategy X Y A B,
      T.IsProjective ∧ T.correlation = S.correlation := by
  classical
  have hA : ∀ s : Finset X, ∃ T : CommutingOperatorStrategy X Y A B,
      T.correlation = S.correlation ∧ ∀ x ∈ s, ∀ a, IsIdempotentElem (T.E x a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨S, rfl, by simp⟩
    | insert x s _ ih =>
      obtain ⟨T, hT, hTs⟩ := ih
      have := T.nonempty_left x
      refine ⟨T.dilateLeft x (Classical.arbitrary A), (T.correlation_dilateLeft _ _).trans hT,
        fun x' hx' a => ?_⟩
      by_cases h : x' = x
      · subst h
        exact T.isIdempotentElem_dilateLeft_E_self _ _ _
      · exact T.isIdempotentElem_dilateLeft_E_of_ne h _
          (hTs x' ((Finset.mem_insert.1 hx').resolve_left h) a)
  obtain ⟨T, hT, hTE⟩ := hA Finset.univ
  have hB : ∀ t : Finset Y, ∃ T' : CommutingOperatorStrategy X Y A B,
      T'.correlation = S.correlation ∧ (∀ x a, IsIdempotentElem (T'.E x a)) ∧
        ∀ y ∈ t, ∀ b, IsIdempotentElem (T'.F y b) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨T, hT, fun x a => hTE x (Finset.mem_univ x) a, by simp⟩
    | insert y t _ ih =>
      obtain ⟨T', hT', hT'E, hT'F⟩ := ih
      have := T'.nonempty_right y
      refine ⟨T'.dilateRight y (Classical.arbitrary B),
        (T'.correlation_dilateRight _ _).trans hT',
        fun x a => T'.isIdempotentElem_dilateRight_E _ _ (hT'E x a), fun y' hy' b => ?_⟩
      by_cases h : y' = y
      · subst h
        exact T'.isIdempotentElem_dilateRight_F_self _ _ _
      · exact T'.isIdempotentElem_dilateRight_F_of_ne h _
          (hT'F y' ((Finset.mem_insert.1 hy').resolve_left h) b)
  obtain ⟨T', hT', hT'E, hT'F⟩ := hB Finset.univ
  exact ⟨T', ⟨hT'E, fun y b => hT'F y (Finset.mem_univ y) b⟩, hT'⟩

/-- Every commuting-operator strategy has a projective one with the same value. -/
theorem exists_isProjective_value_eq (S : CommutingOperatorStrategy X Y A B) (G : Game X Y A B) :
    ∃ T : CommutingOperatorStrategy X Y A B, T.IsProjective ∧ T.value G = S.value G := by
  obtain ⟨T, hT, hc⟩ := S.exists_isProjective_correlation_eq
  exact ⟨T, hT, by rw [value_eq_payoff, value_eq_payoff, hc]⟩

end CommutingOperatorStrategy

/-- **The commuting-operator value is attained on projective strategies**: it is the supremum of
the values of the projective commuting-operator strategies. -/
theorem commutingOperatorValue_eq_iSup_isProjective (G : Game X Y A B) :
    commutingOperatorValue G =
      ⨆ T : {T : CommutingOperatorStrategy X Y A B // T.IsProjective}, T.1.value G := by
  have hbdd : BddAbove (Set.range fun T : {T : CommutingOperatorStrategy X Y A B //
      T.IsProjective} => T.1.value G) :=
    ⟨1, by rintro _ ⟨T, rfl⟩; exact T.1.value_le_one G⟩
  refine le_antisymm (Real.iSup_le (fun S => ?_) (Real.iSup_nonneg fun T => T.1.value_nonneg G))
    (Real.iSup_le (fun T => T.1.value_le_commutingOperatorValue G)
      (commutingOperatorValue_nonneg G))
  obtain ⟨T, hT, hv⟩ := S.exists_isProjective_value_eq G
  rw [← hv]
  exact le_ciSup hbdd ⟨T, hT⟩

/-- **A strategy witnessing a lower bound on `ω_co` can be taken projective**: the form in which a
soundness proof consumes the dilation. -/
theorem exists_isProjective_lt_value {G : Game X Y A B} {t : ℝ} (ht : 0 ≤ t)
    (h : t < commutingOperatorValue G) :
    ∃ T : CommutingOperatorStrategy X Y A B, T.IsProjective ∧ t < T.value G := by
  rcases isEmpty_or_nonempty (CommutingOperatorStrategy X Y A B) with hE | hne
  · rw [commutingOperatorValue, Real.iSup_of_isEmpty] at h
    exact absurd h (not_lt.2 ht)
  · obtain ⟨S, hS⟩ := exists_lt_of_lt_ciSup h
    obtain ⟨T, hT, hv⟩ := S.exists_isProjective_value_eq G
    exact ⟨T, hT, hv ▸ hS⟩

/-- **Tensor-product strategies are projective commuting-operator strategies**, so the
projective model contains the tensor-product model. -/
theorem TensorProductStrategy.isProjective_toCommuting {G : Game X Y A B}
    (S : TensorProductStrategy G) : S.toCommuting.IsProjective := by
  refine ⟨fun x a => ?_, fun y b => ?_⟩
  · show IsIdempotentElem (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (S.PA.M x a ⊗ₖ (1 : Matrix (Fin S.dB) (Fin S.dB) ℂ)))
    rw [IsIdempotentElem, ← map_mul, ← Matrix.mul_kronecker_mul, S.PA.projective,
      Matrix.mul_one]
  · show IsIdempotentElem (Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((1 : Matrix (Fin S.dA) (Fin S.dA) ℂ) ⊗ₖ S.PB.M y b))
    rw [IsIdempotentElem, ← map_mul, ← Matrix.mul_kronecker_mul, S.PB.projective,
      Matrix.mul_one]

end MIPRE

end
