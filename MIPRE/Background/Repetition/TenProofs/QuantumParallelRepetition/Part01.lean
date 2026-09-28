/-
Copyright (c) 2026 the openai/ten-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/openai/ten-proofs (commit 94bc0feb, 2026-08-01) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: QuantumParallelRepetition.lean
-/
module
public import Mathlib

@[expose] public section

-- Part 1 of 8 of upstream's single module `QuantumParallelRepetition.lean`: its lines
-- 14-8995, cut between top-level `noncomputable section` blocks by
-- scripts/vendor-repetition.py (the Palomar registry caps a Lean file at 10,000 lines).
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace QuantumParallelRepetition


noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*}

structure Game (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : (∑ x : X, ∑ y : Y, questionWeight x y) = 1
  predicate : X → Y → A → B → Bool

namespace Game

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def marginalX (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

def marginalY (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

theorem marginalX_nonneg (G : Game X Y A B) (x : X) :
    0 ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.sum_nonneg fun y _ => G.weight_nonneg x y

theorem marginalY_nonneg (G : Game X Y A B) (y : Y) :
    0 ≤ G.marginalY y := by
  unfold marginalY
  exact Finset.sum_nonneg fun x _ => G.weight_nonneg x y

theorem marginalX_normalized (G : Game X Y A B) :
    (∑ x : X, G.marginalX x) = 1 := by
  simpa [marginalX] using G.weight_normalized

theorem marginalY_normalized (G : Game X Y A B) :
    (∑ y : Y, G.marginalY y) = 1 := by
  unfold marginalY
  rw [Finset.sum_comm]
  exact G.weight_normalized

def «repeat» (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questionWeight xs ys := ∏ i : Fin n, G.questionWeight (xs i) (ys i)
  weight_nonneg xs ys :=
    Finset.prod_nonneg fun i _ => G.weight_nonneg (xs i) (ys i)
  weight_normalized := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        ∏ i : Fin n, G.questionWeight (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y,
            G.questionWeight (xs i) y := by
              apply Finset.sum_congr rfl
              intro xs _
              exact (Fintype.prod_sum
                (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y,
            G.questionWeight x y := by
              exact (Fintype.prod_sum
                (fun _i : Fin n => fun x : X => ∑ y : Y,
                  G.questionWeight x y)).symm
      _ = 1 := by simp [G.weight_normalized]
  predicate xs ys as bs :=
    decide (∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true)

@[simp] theorem repeat_questionWeight (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y) :
    (G.repeat n).questionWeight xs ys =
      ∏ i : Fin n, G.questionWeight (xs i) (ys i) := rfl

@[simp] theorem repeat_predicate_eq_true (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    (G.repeat n).predicate xs ys as bs = true ↔
      ∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true := by
  simp [«repeat»]

end Game

structure DensityMatrix (d : Type*) [Fintype d] where
  matrix : Matrix d d ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

structure POVM (ι d : Type*) [Fintype ι] [Fintype d] [DecidableEq d] where
  effect : ι → Matrix d d ℂ
  positive : ∀ i, (effect i).PosSemidef
  complete : (∑ i : ι, effect i) = 1

structure Strategy [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (_G : Game X Y A B) where
  Alice : Type
  Bob : Type
  [alice_fintype : Fintype Alice]
  [bob_fintype : Fintype Bob]
  [alice_decidableEq : DecidableEq Alice]
  [bob_decidableEq : DecidableEq Bob]
  state : DensityMatrix (Alice × Bob)
  aliceMeasurement : X → POVM A Alice
  bobMeasurement : Y → POVM B Bob

attribute [instance] Strategy.alice_fintype Strategy.bob_fintype
  Strategy.alice_decidableEq Strategy.bob_decidableEq

theorem trace_mul_posSemidef_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    {R E : Matrix d d ℂ} (hR : R.PosSemidef) (hE : E.PosSemidef) :
    0 ≤ (Matrix.trace (R * E)).re := by
  obtain ⟨K, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hpositive : (K * E * star K).PosSemidef := by
    simpa [star_eq_conjTranspose] using hE.mul_mul_conjTranspose_same K
  have htrace : 0 ≤ (Matrix.trace (K * E * star K)).re :=
    (Complex.nonneg_iff.mp hpositive.trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at htrace
  exact htrace

namespace Strategy

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

def jointEffect (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  (S.aliceMeasurement x).effect a ⊗ₖ (S.bobMeasurement y).effect b

theorem jointEffect_positive (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (S.jointEffect x y a b).PosSemidef := by
  exact ((S.aliceMeasurement x).positive a).kronecker
    ((S.bobMeasurement y).positive b)

def outcomeProbability (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (Matrix.trace (S.state.matrix * S.jointEffect x y a b)).re

theorem outcomeProbability_nonneg (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.outcomeProbability x y a b := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    (S.jointEffect_positive x y a b)

theorem jointEffect_complete (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) =
        (∑ a : A, (S.aliceMeasurement x).effect a) ⊗ₖ
          (∑ b : B, (S.bobMeasurement y).effect b) := by
            ext ⟨i, j⟩ ⟨k, l⟩
            simp only [jointEffect, Matrix.sum_apply, Matrix.kroneckerMap_apply]
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = 1 := by
      rw [(S.aliceMeasurement x).complete, (S.bobMeasurement y).complete]
      exact Matrix.one_kronecker_one

theorem outcomeProbability_normalized (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) =
        (Matrix.trace
          (S.state.matrix * (∑ a : A, ∑ b : B, S.jointEffect x y a b))).re := by
            simp [outcomeProbability, Matrix.mul_sum, Matrix.trace_sum]
    _ = (Matrix.trace S.state.matrix).re := by
      rw [S.jointEffect_complete x y]
      simp
    _ = 1 := by rw [S.state.trace_one]; rfl

def winProbability (S : Strategy G) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then S.outcomeProbability x y a b else 0

theorem winProbability_nonneg (S : Strategy G) : 0 ≤ S.winProbability := by
  unfold winProbability
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  apply mul_nonneg (G.weight_nonneg x y)
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split <;> simp [S.outcomeProbability_nonneg]

theorem winProbability_le_one (S : Strategy G) : S.winProbability ≤ 1 := by
  classical
  have hxy (x : X) (y : Y) :
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then S.outcomeProbability x y a b else 0) ≤ 1 := by
    calc
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then S.outcomeProbability x y a b else 0) ≤
          ∑ a : A, ∑ b : B, S.outcomeProbability x y a b := by
            apply Finset.sum_le_sum
            intro a _
            apply Finset.sum_le_sum
            intro b _
            split
            · exact le_rfl
            · exact S.outcomeProbability_nonneg x y a b
      _ = 1 := S.outcomeProbability_normalized x y
  calc
    S.winProbability =
        ∑ x : X, ∑ y : Y, G.questionWeight x y *
          (∑ a : A, ∑ b : B,
            if G.predicate x y a b = true then S.outcomeProbability x y a b else 0) := rfl
    _ ≤ ∑ x : X, ∑ y : Y, G.questionWeight x y * 1 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hxy x y) (G.weight_nonneg x y)
    _ = 1 := by simpa using G.weight_normalized

end Strategy

def entangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) : ℝ :=
  sSup (Set.range (Strategy.winProbability (G := G)))

theorem winProbabilities_bddAbove [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : Game X Y A B) :
    BddAbove (Set.range (Strategy.winProbability (G := G))) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨S, rfl⟩
  exact S.winProbability_le_one

theorem entangledValue_le_one [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : Game X Y A B) :
    entangledValue G ≤ 1 := by
  unfold entangledValue
  by_cases h : (Set.range (Strategy.winProbability (G := G))).Nonempty
  · apply csSup_le h
    rintro _ ⟨S, rfl⟩
    exact S.winProbability_le_one
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]
    exact zero_le_one

theorem entangledValue_nonneg [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : Game X Y A B) :
    0 ≤ entangledValue G := by
  unfold entangledValue
  by_cases h : (Set.range (Strategy.winProbability (G := G))).Nonempty
  · rcases h with ⟨_, S, rfl⟩
    exact le_trans S.winProbability_nonneg
      (le_csSup (winProbabilities_bddAbove G) ⟨S, rfl⟩)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]

def repeatedEntangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) : ℝ :=
  entangledValue (G.repeat n)

end

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def quadraticExpectation (W : H →L[ℂ] H) (z : H) : ℝ :=
  (⟪z, W z⟫_ℂ).re

theorem positive_quadraticExpectation_nonneg
    (W : H →L[ℂ] H) (hW : W.IsPositive) (z : H) :
    0 ≤ quadraticExpectation W z := by
  exact hW.re_inner_nonneg_right z

theorem positive_complement_quadraticExpectation_le
    (W : H →L[ℂ] H)
    (h_complement : (1 - W).IsPositive) (z : H) :
    quadraticExpectation W z ≤ ‖z‖ ^ 2 := by
  have h := h_complement.re_inner_nonneg_right z
  have hnorm : (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [pow_two, Complex.mul_re]
  change 0 ≤ (⟪z, z - W z⟫_ℂ).re at h
  rw [inner_sub_right, Complex.sub_re, hnorm] at h
  unfold quadraticExpectation
  exact sub_nonneg.mp h

theorem norm_le_of_operator_contraction
    (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1) (z : H) :
    ‖W z‖ ≤ ‖z‖ := by
  calc
    ‖W z‖ ≤ ‖W‖ * ‖z‖ := W.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg z)
    _ = ‖z‖ := one_mul _

theorem quadraticExpectation_sub_le
    (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1) (z w : H) :
    |quadraticExpectation W z - quadraticExpectation W w| ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have h_expand :
      ⟪z, W z⟫_ℂ - ⟪w, W w⟫_ℂ =
        ⟪z - w, W z⟫_ℂ + ⟪w, W (z - w)⟫_ℂ := by
    simp [map_sub]
  have hz := norm_le_of_operator_contraction W hW z
  have hdiff := norm_le_of_operator_contraction W hW (z - w)
  unfold quadraticExpectation
  calc
    |(⟪z, W z⟫_ℂ).re - (⟪w, W w⟫_ℂ).re| =
        |(⟪z, W z⟫_ℂ - ⟪w, W w⟫_ℂ).re| := by
          rw [Complex.sub_re]
    _ ≤ ‖⟪z, W z⟫_ℂ - ⟪w, W w⟫_ℂ‖ :=
      Complex.abs_re_le_norm _
    _ = ‖⟪z - w, W z⟫_ℂ + ⟪w, W (z - w)⟫_ℂ‖ := by
      rw [h_expand]
    _ ≤ ‖⟪z - w, W z⟫_ℂ‖ + ‖⟪w, W (z - w)⟫_ℂ‖ :=
      norm_add_le _ _
    _ ≤ ‖z - w‖ * ‖W z‖ + ‖w‖ * ‖W (z - w)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖z - w‖ * ‖z‖ + ‖w‖ * ‖z - w‖ := by
      gcongr
    _ = (‖z‖ + ‖w‖) * ‖z - w‖ := by ring

theorem weighted_real_cauchy
    {ι : Type*} [Fintype ι]
    (weight f g : ι → ℝ)
    (h_weight : ∀ i, 0 ≤ weight i) :
    (∑ i : ι, weight i * f i * g i) ≤
      Real.sqrt (∑ i : ι, weight i * f i ^ 2) *
        Real.sqrt (∑ i : ι, weight i * g i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i : ι => Real.sqrt (weight i) * f i)
    (fun i : ι => Real.sqrt (weight i) * g i)
  have hsq (i : ι) : Real.sqrt (weight i) ^ 2 = weight i :=
    Real.sq_sqrt (h_weight i)
  have h_left :
      (∑ i : ι,
        (Real.sqrt (weight i) * f i) *
          (Real.sqrt (weight i) * g i)) =
        ∑ i : ι, weight i * f i * g i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      (Real.sqrt (weight i) * f i) *
          (Real.sqrt (weight i) * g i) =
        Real.sqrt (weight i) ^ 2 * f i * g i := by ring
      _ = weight i * f i * g i := by rw [hsq i]
  have h_f :
      (∑ i : ι, (Real.sqrt (weight i) * f i) ^ 2) =
        ∑ i : ι, weight i * f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, hsq i]
  have h_g :
      (∑ i : ι, (Real.sqrt (weight i) * g i) ^ 2) =
        ∑ i : ι, weight i * g i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, hsq i]
  simpa [h_left, h_f, h_g] using h

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem matrixEffectCLM_isPositive
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : E.PosSemidef) :
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E).IsPositive := by
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hE

theorem matrixEffectCLM_complement_isPositive
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : (1 - E).PosSemidef) :
    (1 - Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E).IsPositive := by
  simpa using matrixEffectCLM_isPositive (1 - E) hE

theorem matrixEffectCLM_norm_le_one
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : E.PosSemidef)
    (h_complement : (1 - E).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E‖ ≤ 1 := by
  have h_positive := matrixEffectCLM_isPositive E hE
  have h_nonneg :
      0 ≤ Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E :=
    -- Vendoring compile fix (Mathlib v4.35): `nonneg_iff_isPositive` and `le_def` take
    -- their operators implicitly. See README.md.
    ContinuousLinearMap.nonneg_iff_isPositive.mpr h_positive
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ h_nonneg).mpr
  exact ContinuousLinearMap.le_def.mpr
    (matrixEffectCLM_complement_isPositive E h_complement)

namespace Strategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

def winningEffect (S : Strategy G) (x : X) (y : Y) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then S.jointEffect x y a b else 0

theorem winningEffect_born
    (S : Strategy G) (x : X) (y : Y) :
    (Matrix.trace (S.state.matrix * S.winningEffect x y)).re =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          S.outcomeProbability x y a b else 0 := by
  classical
  simp [winningEffect, outcomeProbability, Matrix.mul_sum,
    Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp

theorem winProbability_eq_winningEffect_born
    (S : Strategy G) :
    S.winProbability =
      ∑ x : X, ∑ y : Y,
        G.questionWeight x y *
          (Matrix.trace (S.state.matrix * S.winningEffect x y)).re := by
  simp_rw [S.winningEffect_born]
  rfl

end Strategy

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}

theorem posSemidef_blockDiagonal'
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → Type*} [∀ j, Fintype (d j)]
    (M : ∀ j, Matrix (d j) (d j) ℂ)
    (hM : ∀ j, (M j).PosSemidef) :
    (Matrix.blockDiagonal' M).PosSemidef := by
  classical
  choose K hK using fun j =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM j).nonneg
  apply Matrix.LE.le.posSemidef
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
  refine ⟨Matrix.blockDiagonal' K, ?_⟩
  calc
    Matrix.blockDiagonal' M =
        Matrix.blockDiagonal' (fun j => star (K j) * K j) := by
          congr 1
          funext j
          exact hK j
    _ = star (Matrix.blockDiagonal' K) * Matrix.blockDiagonal' K := by
          simp [star_eq_conjTranspose, ← Matrix.blockDiagonal'_mul]

abbrev mixtureAlice (S : J → Strategy G) := Σ j : J, (S j).Alice

abbrev mixtureBob (S : J → Strategy G) := Σ j : J, (S j).Bob

abbrev mixtureMatched (S : J → Strategy G) :=
  Σ j : J, (S j).Alice × (S j).Bob

def mixtureMatchedIndex (S : J → Strategy G) :
    mixtureMatched S → mixtureAlice S × mixtureBob S
  | ⟨j, (a, b)⟩ => (⟨j, a⟩, ⟨j, b⟩)

omit [Fintype J] [DecidableEq J] in

theorem mixtureMatchedIndex_injective (S : J → Strategy G) :
    Function.Injective (mixtureMatchedIndex S) := by
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
  have hflag : i = j := congrArg (fun q => q.1.1) h
  subst j
  have ha : a = c :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.fst h)).2
  have hb : b = d :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.snd h)).2
  subst c
  subst d
  rfl

def mixtureEmbedding (S : J → Strategy G) :
    Matrix (mixtureAlice S × mixtureBob S) (mixtureMatched S) ℂ := by
  classical
  exact fun q r => if q = mixtureMatchedIndex S r then 1 else 0

theorem mixtureEmbedding_isometry (S : J → Strategy G) :
    (mixtureEmbedding S)ᴴ * mixtureEmbedding S = 1 := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    simp [mixtureEmbedding, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  · have hindex : mixtureMatchedIndex S i ≠ mixtureMatchedIndex S j :=
      fun hij => h (mixtureMatchedIndex_injective S hij)
    simp [mixtureEmbedding, Matrix.mul_apply,
      Matrix.conjTranspose_apply, h, hindex.symm]

theorem mixtureEmbedding_compress (S : J → Strategy G)
    (E : Matrix (mixtureAlice S × mixtureBob S)
      (mixtureAlice S × mixtureBob S) ℂ) :
    (mixtureEmbedding S)ᴴ * E * mixtureEmbedding S =
      E.submatrix (mixtureMatchedIndex S) (mixtureMatchedIndex S) := by
  classical
  ext i j
  simp [mixtureEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply]

def mixtureBlockMatrix (p : J → ℝ) (S : J → Strategy G) :
    Matrix (mixtureMatched S) (mixtureMatched S) ℂ :=
  Matrix.blockDiagonal' fun j => p j • (S j).state.matrix

theorem mixtureBlockMatrix_posSemidef
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (S : J → Strategy G) :
    (mixtureBlockMatrix p S).PosSemidef := by
  unfold mixtureBlockMatrix
  apply posSemidef_blockDiagonal'
  intro j
  exact (S j).state.positive.smul (hp j)

theorem mixtureBlockMatrix_trace
    (p : J → ℝ) (S : J → Strategy G) :
    Matrix.trace (mixtureBlockMatrix p S) =
      (↑(∑ j : J, p j) : ℂ) := by
  unfold mixtureBlockMatrix
  rw [Matrix.trace_blockDiagonal']
  simp [Matrix.trace_smul, DensityMatrix.trace_one]

def mixtureDensityMatrix (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) :
    DensityMatrix (mixtureAlice S × mixtureBob S) where
  matrix := mixtureEmbedding S * mixtureBlockMatrix p S *
    (mixtureEmbedding S)ᴴ
  positive :=
    (mixtureBlockMatrix_posSemidef p hp S).mul_mul_conjTranspose_same
      (mixtureEmbedding S)
  trace_one := by
    rw [Matrix.trace_mul_cycle, mixtureEmbedding_isometry,
      Matrix.one_mul, mixtureBlockMatrix_trace, h_normalized]
    norm_num

def mixtureAlicePOVM (S : J → Strategy G) (x : X) :
    POVM A (mixtureAlice S) where
  effect a := Matrix.blockDiagonal' fun j =>
    ((S j).aliceMeasurement x).effect a
  positive a := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).aliceMeasurement x).positive a
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Alice (S i).Alice ℂ => M u v)
        ((S i).aliceMeasurement x).complete
      simpa [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        Matrix.one_apply] using h_complete
    · simp [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        h]

def mixtureBobPOVM (S : J → Strategy G) (y : Y) :
    POVM B (mixtureBob S) where
  effect b := Matrix.blockDiagonal' fun j =>
    ((S j).bobMeasurement y).effect b
  positive b := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).bobMeasurement y).positive b
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Bob (S i).Bob ℂ => M u v)
        ((S i).bobMeasurement y).complete
      simpa [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        Matrix.one_apply] using h_complete
    · simp [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        h]

def convexMixtureStrategy (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) : Strategy G where
  Alice := mixtureAlice S
  Bob := mixtureBob S
  alice_fintype := inferInstance
  bob_fintype := inferInstance
  alice_decidableEq := inferInstance
  bob_decidableEq := inferInstance
  state := mixtureDensityMatrix p hp h_normalized S
  aliceMeasurement := mixtureAlicePOVM S
  bobMeasurement := mixtureBobPOVM S

theorem mixtureJointEffect_compress (S : J → Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    (((mixtureAlicePOVM S x).effect a ⊗ₖ
      (mixtureBobPOVM S y).effect b).submatrix
        (mixtureMatchedIndex S) (mixtureMatchedIndex S)) =
      Matrix.blockDiagonal' fun j =>
        (S j).jointEffect x y a b := by
  classical
  ext ⟨i, u, v⟩ ⟨j, u', v'⟩
  by_cases h : i = j
  · subst j
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      mixtureMatchedIndex, mixtureAlicePOVM, mixtureBobPOVM,
      Matrix.blockDiagonal'_apply, Strategy.jointEffect]
  · simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      mixtureMatchedIndex, mixtureAlicePOVM, mixtureBobPOVM,
      Matrix.blockDiagonal'_apply, Strategy.jointEffect, h]

theorem mixtureEmbedding_trace_mul (S : J → Strategy G)
    (R : Matrix (mixtureMatched S) (mixtureMatched S) ℂ)
    (E : Matrix (mixtureAlice S × mixtureBob S)
      (mixtureAlice S × mixtureBob S) ℂ) :
    Matrix.trace
      ((mixtureEmbedding S * R * (mixtureEmbedding S)ᴴ) * E) =
      Matrix.trace
        (R * E.submatrix (mixtureMatchedIndex S)
          (mixtureMatchedIndex S)) := by
  calc
    Matrix.trace
        ((mixtureEmbedding S * R * (mixtureEmbedding S)ᴴ) * E) =
        Matrix.trace
          ((mixtureEmbedding S * R) * ((mixtureEmbedding S)ᴴ * E)) := by
            congr 1
            simp [Matrix.mul_assoc]
    _ = Matrix.trace
          (((mixtureEmbedding S)ᴴ * E) * (mixtureEmbedding S * R)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (((mixtureEmbedding S)ᴴ * E * mixtureEmbedding S) * R) := by
            congr 1
            simp [Matrix.mul_assoc]
    _ = Matrix.trace
          (R * ((mixtureEmbedding S)ᴴ * E * mixtureEmbedding S)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (R * E.submatrix (mixtureMatchedIndex S)
            (mixtureMatchedIndex S)) := by
          rw [mixtureEmbedding_compress]

theorem mixtureBlockMatrix_trace_mul
    (p : J → ℝ) (S : J → Strategy G)
    (E : ∀ j : J,
      Matrix ((S j).Alice × (S j).Bob)
        ((S j).Alice × (S j).Bob) ℂ) :
    Matrix.trace (mixtureBlockMatrix p S * Matrix.blockDiagonal' E) =
      ∑ j : J, p j • Matrix.trace ((S j).state.matrix * E j) := by
  unfold mixtureBlockMatrix
  rw [← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
  simp [Matrix.trace_smul]

theorem convexMixtureStrategy_outcomeProbability
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (convexMixtureStrategy p hp h_normalized S).outcomeProbability
        x y a b =
      ∑ j : J, p j * (S j).outcomeProbability x y a b := by
  change
    (Matrix.trace
      ((mixtureEmbedding S * mixtureBlockMatrix p S *
          (mixtureEmbedding S)ᴴ) *
        ((mixtureAlicePOVM S x).effect a ⊗ₖ
          (mixtureBobPOVM S y).effect b))).re = _
  rw [mixtureEmbedding_trace_mul, mixtureJointEffect_compress,
    mixtureBlockMatrix_trace_mul]
  simp [Strategy.outcomeProbability]

theorem convexMixtureStrategy_winProbability
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) :
    (convexMixtureStrategy p hp h_normalized S).winProbability =
      ∑ j : J, p j * (S j).winProbability := by
  classical
  have h_branch (x : X) (y : Y) (a : A) (b : B) :
      (if G.predicate x y a b = true then
        ∑ j : J, p j * (S j).outcomeProbability x y a b
       else 0) =
        ∑ j : J, p j *
          (if G.predicate x y a b = true then
            (S j).outcomeProbability x y a b else 0) := by
    split <;> simp
  have h_swap (f : X → Y → A → B → J → ℝ) :
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, ∑ j : J,
        f x y a b j) =
        ∑ j : J, ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          f x y a b j := by
    calc
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, ∑ j : J,
        f x y a b j) =
          ∑ x : X, ∑ y : Y, ∑ a : A, ∑ j : J, ∑ b : B,
            f x y a b j := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              apply Finset.sum_congr rfl
              intro a _
              exact Finset.sum_comm
      _ = ∑ x : X, ∑ y : Y, ∑ j : J, ∑ a : A, ∑ b : B,
            f x y a b j := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              exact Finset.sum_comm
      _ = ∑ x : X, ∑ j : J, ∑ y : Y, ∑ a : A, ∑ b : B,
            f x y a b j := by
              apply Finset.sum_congr rfl
              intro x _
              exact Finset.sum_comm
      _ = ∑ j : J, ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
            f x y a b j := Finset.sum_comm
  unfold Strategy.winProbability
  simp_rw [convexMixtureStrategy_outcomeProbability p hp h_normalized S]
  simp_rw [h_branch]
  simp_rw [Finset.mul_sum]
  rw [h_swap (fun x y a b j =>
    G.questionWeight x y *
      (p j * (if G.predicate x y a b = true then
        (S j).outcomeProbability x y a b else 0)))]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def pureDensityMatrix
    {d : Type*} [Fintype d] [DecidableEq d]
    (z : EuclideanSpace ℂ d) (hz : ‖z‖ = 1) : DensityMatrix d where
  matrix := Matrix.vecMulVec (ofLp z) (star (ofLp z))
  positive := Matrix.posSemidef_vecMulVec_self_star (ofLp z)
  trace_one := by
    rw [Matrix.trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct z z,
      inner_self_eq_norm_sq_to_K, hz]
    norm_num

theorem pureDensityMatrix_trace_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (z : EuclideanSpace ℂ d) (hz : ‖z‖ = 1)
    (E : Matrix d d ℂ) :
    (Matrix.trace ((pureDensityMatrix z hz).matrix * E)).re =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E) z := by
  unfold pureDensityMatrix quadraticExpectation
  congr 1
  calc
    Matrix.trace
        (Matrix.vecMulVec (ofLp z) (star (ofLp z)) * E) =
      Matrix.trace
        (E * Matrix.vecMulVec (ofLp z) (star (ofLp z))) :=
          Matrix.trace_mul_comm _ _
    _ = E.mulVec (ofLp z) ⬝ᵥ star (ofLp z) := by
      rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    _ = ⟪z, Matrix.toEuclideanCLM
          (n := d) (𝕜 := ℂ) E z⟫_ℂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rfl

def pureVectorStrategy
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) : Strategy G where
  Alice := dA
  Bob := dB
  alice_fintype := inferInstance
  bob_fintype := inferInstance
  alice_decidableEq := inferInstance
  bob_decidableEq := inferInstance
  state := pureDensityMatrix z hz
  aliceMeasurement := PA
  bobMeasurement := PB

theorem pureVectorStrategy_outcomeProbability
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) (a : A) (b : B) :
    (pureVectorStrategy G z hz PA PB).outcomeProbability x y a b =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
          ((PA x).effect a ⊗ₖ (PB y).effect b)) z := by
  change
    (Matrix.trace
      ((pureDensityMatrix z hz).matrix *
        ((PA x).effect a ⊗ₖ (PB y).effect b))).re = _
  exact pureDensityMatrix_trace_mul z hz
    ((PA x).effect a ⊗ₖ (PB y).effect b)

def pureFlaggedStrategy
    {X Y A B : Type*} {dA dB J : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    [Fintype J] [DecidableEq J]
    (G : Game X Y A B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (z : J → EuclideanSpace ℂ (dA × dB))
    (hz : ∀ j, ‖z j‖ = 1)
    (PA : J → X → POVM A dA)
    (PB : J → Y → POVM B dB) : Strategy G :=
  convexMixtureStrategy p hp h_normalized
    (fun j => pureVectorStrategy G (z j) (hz j) (PA j) (PB j))

theorem pureFlaggedStrategy_winProbability
    {X Y A B : Type*} {dA dB J : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    [Fintype J] [DecidableEq J]
    (G : Game X Y A B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (z : J → EuclideanSpace ℂ (dA × dB))
    (hz : ∀ j, ‖z j‖ = 1)
    (PA : J → X → POVM A dA)
    (PB : J → Y → POVM B dB) :
    (pureFlaggedStrategy G p hp h_normalized z hz PA PB).winProbability =
      ∑ j : J, p j *
        (pureVectorStrategy G (z j) (hz j) (PA j) (PB j)).winProbability := by
  exact convexMixtureStrategy_winProbability p hp h_normalized
    (fun j => pureVectorStrategy G (z j) (hz j) (PA j) (PB j))

end

noncomputable section

open scoped BigOperators

structure FiniteEventLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : (∑ ω, weight ω) = 1

namespace FiniteEventLaw

variable {Ω ι : Type*} [Fintype Ω]

def eventMass (law : FiniteEventLaw Ω) (event : Finset Ω) : ℝ :=
  ∑ ω ∈ event, law.weight ω

theorem eventMass_univ (law : FiniteEventLaw Ω) :
    law.eventMass Finset.univ = 1 := by
  simpa [eventMass] using law.weight_sum

theorem eventMass_mono
    (law : FiniteEventLaw Ω) {s t : Finset Ω} (h : s ⊆ t) :
    law.eventMass s ≤ law.eventMass t := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun ω _ _ => law.weight_nonneg ω)

def winEvent [Fintype ι]
    (wins : ι → Ω → Bool) (D : Finset ι) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ i ∈ D, wins i ω = true)

theorem winEvent_empty [Fintype ι] (wins : ι → Ω → Bool) :
    winEvent wins ∅ = Finset.univ := by
  classical
  simp [winEvent]

theorem winEvent_antitone [Fintype ι]
    (wins : ι → Ω → Bool) {D E : Finset ι} (h : D ⊆ E) :
    winEvent wins E ⊆ winEvent wins D := by
  classical
  intro ω hω
  have h_all : ∀ i ∈ E, wins i ω = true := by
    simpa [winEvent] using hω
  simp only [winEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i hi => h_all i (h hi)

theorem allWinMass_le_partial [Fintype ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) :
    law.eventMass (winEvent wins Finset.univ) ≤
      law.eventMass (winEvent wins D) := by
  apply law.eventMass_mono
  exact winEvent_antitone wins (Finset.subset_univ D)

def failureMass [Fintype ι] [DecidableEq ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) (i : ι) : ℝ :=
  law.eventMass (winEvent wins D) -
    law.eventMass (winEvent wins (insert i D))

theorem exists_greedy_stopping [Fintype ι] [DecidableEq ι]
    (mass : Finset ι → ℝ) {θ η : ℝ} {T : ℕ}
    (_hθ : 0 < θ)
    (_hη : 0 < η)
    (hη_one : η ≤ 1)
    (hT : T ≤ Fintype.card ι)
    (hempty : mass ∅ = 1)
    (hfloor : ∀ D : Finset ι, θ ≤ mass D)
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset ι,
      D.card < T ∧
      θ ≤ mass D ∧
      (∑ i ∈ Finset.univ \ D,
        (mass D - mass (insert i D)))
        < ((Finset.univ \ D).card : ℝ) * (η * mass D) := by
  classical
  let candidates : Finset (Finset ι) :=
    Finset.univ.powerset.filter
      (fun D => D.card ≤ T ∧ mass D ≤ (1 - η) ^ D.card)
  have h_candidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, hempty]
  obtain ⟨D, hD, hmax⟩ :=
    Finset.exists_max_image candidates (fun E : Finset ι => E.card)
      h_candidates
  have hD_data : D.card ≤ T ∧ mass D ≤ (1 - η) ^ D.card :=
    (Finset.mem_filter.mp hD).2
  have hD_lt : D.card < T := by
    have hne : D.card ≠ T := by
      intro heq
      have hupper : mass D ≤ (1 - η) ^ T := by
        simpa [heq] using hD_data.2
      linarith [hfloor D]
    exact lt_of_le_of_ne hD_data.1 hne
  refine ⟨D, hD_lt, hfloor D, ?_⟩
  by_contra h_not_stopped
  have h_sum :
      ((Finset.univ \ D).card : ℝ) * (η * mass D)
        ≤ ∑ i ∈ Finset.univ \ D,
          (mass D - mass (insert i D)) :=
    le_of_not_gt h_not_stopped
  have h_card : D.card < (Finset.univ : Finset ι).card := by
    simpa using hD_lt.trans_le hT
  have h_remaining : (Finset.univ \ D).Nonempty :=
    Finset.sdiff_nonempty_of_card_lt_card h_card
  have h_sum_constant :
      (∑ _i ∈ Finset.univ \ D, η * mass D)
        ≤ ∑ i ∈ Finset.univ \ D,
          (mass D - mass (insert i D)) := by
    simpa using h_sum
  obtain ⟨i, hi, hfailure⟩ :=
    Finset.exists_le_of_sum_le h_remaining h_sum_constant
  have hi_not : i ∉ D := (Finset.mem_sdiff.mp hi).2
  have hnext_card : (insert i D).card ≤ T := by
    rw [Finset.card_insert_of_notMem hi_not]
    omega
  have hshrink :
      mass (insert i D) ≤ (1 - η) * mass D := by
    linarith
  have hnext_bound :
      mass (insert i D) ≤
        (1 - η) ^ (insert i D).card := by
    calc
      mass (insert i D) ≤ (1 - η) * mass D := hshrink
      _ ≤ (1 - η) * (1 - η) ^ D.card :=
        mul_le_mul_of_nonneg_left hD_data.2
          (sub_nonneg.mpr hη_one)
      _ = (1 - η) ^ (insert i D).card := by
        rw [Finset.card_insert_of_notMem hi_not, pow_succ]
        ring
  have hnext_mem : insert i D ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hnext_card, hnext_bound⟩
  have h_impossible := hmax (insert i D) hnext_mem
  rw [Finset.card_insert_of_notMem hi_not] at h_impossible
  omega

theorem exists_conditioned_win_set [Fintype ι] [DecidableEq ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    {θ η : ℝ} {T : ℕ}
    (hθ : 0 < θ)
    (hη : 0 < η)
    (hη_one : η ≤ 1)
    (hT : T ≤ Fintype.card ι)
    (hwin : θ ≤ law.eventMass (winEvent wins Finset.univ))
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset ι,
      D.card < T ∧
      θ ≤ law.eventMass (winEvent wins D) ∧
      (∑ i ∈ Finset.univ \ D, failureMass law wins D i)
        < ((Finset.univ \ D).card : ℝ) *
          (η * law.eventMass (winEvent wins D)) := by
  let mass : Finset ι → ℝ :=
    fun D => law.eventMass (winEvent wins D)
  have hempty : mass ∅ = 1 := by
    dsimp [mass]
    rw [winEvent_empty]
    exact law.eventMass_univ
  have hfloor : ∀ D : Finset ι, θ ≤ mass D := by
    intro D
    exact hwin.trans (law.allWinMass_le_partial wins D)
  obtain ⟨D, hD, hp, hstop⟩ :=
    exists_greedy_stopping mass hθ hη hη_one hT hempty hfloor
      h_terminal
  refine ⟨D, hD, hp, ?_⟩
  simpa [failureMass, mass] using hstop

end FiniteEventLaw

section StrategyEventLaw

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev StrategyOutcome (X Y A B : Type*) :=
  X × Y × A × B

def strategyEventLaw (G : Game X Y A B) (S : Strategy G) :
    FiniteEventLaw (StrategyOutcome X Y A B) where
  weight ω :=
    G.questionWeight ω.1 ω.2.1 *
      S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  weight_nonneg ω :=
    mul_nonneg (G.weight_nonneg ω.1 ω.2.1)
      (S.outcomeProbability_nonneg
        ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
  weight_sum := by
    classical
    change
      (∑ ω : X × Y × A × B,
        G.questionWeight ω.1 ω.2.1 *
          S.outcomeProbability
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = 1
    simp_rw [Fintype.sum_prod_type]
    calc
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
        G.questionWeight x y *
          S.outcomeProbability x y a b) =
        ∑ x : X, ∑ y : Y,
          G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              S.outcomeProbability x y a b) := by
                apply Finset.sum_congr rfl
                intro x _
                apply Finset.sum_congr rfl
                intro y _
                simp only [Finset.mul_sum]
      _ = ∑ x : X, ∑ y : Y,
          G.questionWeight x y * 1 := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            rw [S.outcomeProbability_normalized x y]
      _ = 1 := by
            simpa using G.weight_normalized

def strategyWinEvent (G : Game X Y A B) :
    Finset (StrategyOutcome X Y A B) :=
  Finset.univ.filter
    (fun ω =>
      G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true)

theorem strategyEventLaw_winEvent
    (G : Game X Y A B) (S : Strategy G) :
    (strategyEventLaw G S).eventMass (strategyWinEvent G) =
      S.winProbability := by
  classical
  unfold FiniteEventLaw.eventMass strategyWinEvent
  simp only [Finset.sum_filter]
  change
    (∑ ω : X × Y × A × B,
      if G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true
      then G.questionWeight ω.1 ω.2.1 *
        S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
      else 0) =
      S.winProbability
  simp_rw [Fintype.sum_prod_type]
  unfold Strategy.winProbability
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp

def repeatedCoordinateWin (G : Game X Y A B) (n : ℕ)
    (i : Fin n)
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B)) : Bool :=
  G.predicate (ω.1 i) (ω.2.1 i)
    (ω.2.2.1 i) (ω.2.2.2 i)

theorem repeated_allWinEvent_eq
    (G : Game X Y A B) (n : ℕ) :
    FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
      (Finset.univ : Finset (Fin n)) =
      strategyWinEvent (G.repeat n) := by
  classical
  ext ω
  simp [FiniteEventLaw.winEvent, strategyWinEvent,
    repeatedCoordinateWin, Game.repeat_predicate_eq_true]

theorem repeated_allWinMass_eq
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) :
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
        (Finset.univ : Finset (Fin n))) =
      S.winProbability := by
  rw [repeated_allWinEvent_eq]
  exact strategyEventLaw_winEvent (G.repeat n) S

theorem repeatedStrategy_exists_greedy_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {θ η : ℝ} {T : ℕ}
    (hθ : 0 < θ)
    (hη : 0 < η)
    (hη_one : η ≤ 1)
    (hT : T ≤ n)
    (hwin : θ ≤ S.winProbability)
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset (Fin n),
      D.card < T ∧
      θ ≤ (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) ∧
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i)
        <
      ((Finset.univ \ D).card : ℝ) *
        (η * (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D)) := by
  have h_card : T ≤ Fintype.card (Fin n) := by
    simpa using hT
  have h_full :
      θ ≤ (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n)
          (Finset.univ : Finset (Fin n))) := by
    rw [repeated_allWinMass_eq]
    exact hwin
  exact FiniteEventLaw.exists_conditioned_win_set
    (strategyEventLaw (G.repeat n) S)
    (repeatedCoordinateWin G n)
    hθ hη hη_one h_card h_full h_terminal

end StrategyEventLaw

end

noncomputable section

open scoped BigOperators

variable {ι : Type*}

theorem negMulLog_rescale
    {W p : ℝ} (hW : 0 < W) (hp : 0 < p) :
    W * Real.negMulLog (p / W) = p * Real.log (W / p) := by
  unfold Real.negMulLog
  rw [Real.log_div hp.ne' hW.ne', Real.log_div hW.ne' hp.ne']
  field_simp
  ring

theorem finite_weighted_entropy_le
    (s : Finset ι) (w h : ι → ℝ) {W p : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hW : 0 < W)
    (hp : 0 < p)
    (hw_sum : (∑ i ∈ s, w i) = W)
    (hp_sum : (∑ i ∈ s, w i * h i) = p) :
    (∑ i ∈ s, w i * Real.negMulLog (h i))
      ≤ p * Real.log (W / p) := by
  classical
  have h_normalized :
      (∑ i ∈ s, w i / W) = 1 := by
    calc
      (∑ i ∈ s, w i / W) = (∑ i ∈ s, w i) / W := by
        rw [Finset.sum_div]
      _ = W / W := by rw [hw_sum]
      _ = 1 := div_self hW.ne'
  have h_mean :
      (∑ i ∈ s, (w i / W) * h i) = p / W := by
    calc
      (∑ i ∈ s, (w i / W) * h i) =
          ∑ i ∈ s, (w i * h i) / W := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ s, w i * h i) / W := by
            rw [Finset.sum_div]
      _ = p / W := by rw [hp_sum]
  have h_jensen :
      (∑ i ∈ s, (w i / W) * Real.negMulLog (h i))
        ≤ Real.negMulLog (∑ i ∈ s, (w i / W) * h i) := by
    simpa only [smul_eq_mul] using
      (Real.concaveOn_negMulLog.le_map_sum
        (t := s) (w := fun i => w i / W) (p := h)
        (fun i hi => div_nonneg (hw i hi) hW.le)
        h_normalized
        (fun i hi => show h i ∈ Set.Ici (0 : ℝ) from hh i hi))
  calc
    (∑ i ∈ s, w i * Real.negMulLog (h i)) =
        W * (∑ i ∈ s, (w i / W) * Real.negMulLog (h i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          field_simp
    _ ≤ W * Real.negMulLog (∑ i ∈ s, (w i / W) * h i) :=
          mul_le_mul_of_nonneg_left h_jensen hW.le
    _ = W * Real.negMulLog (p / W) := by rw [h_mean]
    _ = p * Real.log (W / p) := negMulLog_rescale hW hp

theorem finite_weighted_entropy_le_of_weight_bound
    (s : Finset ι) (w h : ι → ℝ) {W N p : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hW : 0 < W)
    (hp : 0 < p)
    (hw_sum : (∑ i ∈ s, w i) = W)
    (hp_sum : (∑ i ∈ s, w i * h i) = p)
    (hWN : W ≤ N) :
    (∑ i ∈ s, w i * Real.negMulLog (h i))
      ≤ p * Real.log (N / p) := by
  have hquot : W / p ≤ N / p := by
    exact (div_le_div_iff_of_pos_right hp).mpr hWN
  have hlog : Real.log (W / p) ≤ Real.log (N / p) :=
    Real.log_le_log (div_pos hW hp) hquot
  exact
    (finite_weighted_entropy_le s w h hw hh hW hp hw_sum hp_sum).trans
      (mul_le_mul_of_nonneg_left hlog hp.le)

end

noncomputable section

open scoped BigOperators

theorem noncommutative_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF : RF * (F + S) = 1)
    (hM : (M + S) * RM = 1) :
    RF - RM = RF * (M - F) * RM := by
  calc
    RF - RM = RF * ((M + S) * RM) - (RF * (F + S)) * RM := by
      rw [hM, hF]
      simp
    _ = RF * (M - F) * RM := by
      noncomm_ring

theorem noncommutative_filtered_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1) :
    F * RF - M * RM = S * (RF * (F - M) * RM) := by
  have hFR : F * RF = 1 - S * RF := by
    have h : F * RF + S * RF = 1 := by
      simpa [add_mul] using hF_left
    exact eq_sub_of_add_eq h
  have hMR : M * RM = 1 - S * RM := by
    have h : M * RM + S * RM = 1 := by
      simpa [add_mul] using hM_left
    exact eq_sub_of_add_eq h
  have hdiff : RM - RF = RF * (F - M) * RM := by
    calc
      RM - RF = -(RF - RM) := by noncomm_ring
      _ = -(RF * (M - F) * RM) := by
        rw [noncommutative_resolvent_identity F M S RF RM hF_right hM_left]
      _ = RF * (F - M) * RM := by noncomm_ring
  rw [hFR, hMR]
  calc
    (1 - S * RF) - (1 - S * RM) = S * (RM - RF) := by
      noncomm_ring
    _ = S * (RF * (F - M) * RM) := by rw [hdiff]

theorem noncommutative_resolvent_second_order
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    RF = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by
  have hleft : RM - RF = RM * (F - M) * RF :=
    noncommutative_resolvent_identity M F S RM RF hM_right hF_left
  have hright : RF - RM = RF * (M - F) * RM :=
    noncommutative_resolvent_identity F M S RF RM hF_right hM_left
  have hfirst : RF = RM - RM * (F - M) * RF := by
    calc
      RF = RM - (RM - RF) := by noncomm_ring
      _ = RM - RM * (F - M) * RF := by rw [hleft]
  have hsecond : RF = RM - RF * (F - M) * RM := by
    calc
      RF = RM + (RF - RM) := by noncomm_ring
      _ = RM + RF * (M - F) * RM := by rw [hright]
      _ = RM - RF * (F - M) * RM := by noncomm_ring
  calc
    RF = RM - RM * (F - M) * RF := hfirst
    _ = RM - RM * (F - M) *
      (RM - RF * (F - M) * RM) := by rw [← hsecond]
    _ = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by noncomm_ring

theorem noncommutative_weighted_resolvent_second_order
    {ι R : Type*} [Fintype ι] [Ring R]
    (weight : ι → R) (F : ι → R) (M S : R)
    (RF : ι → R) (RM : R)
    (normalized : (∑ i : ι, weight i) = 1)
    (centered : (∑ i : ι, weight i * (F i - M)) = 0)
    (commute_mean : ∀ i, weight i * RM = RM * weight i)
    (hF_left : ∀ i, (F i + S) * RF i = 1)
    (hF_right : ∀ i, RF i * (F i + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    (∑ i : ι, weight i * RF i) - RM =
      RM * (∑ i : ι,
        weight i * ((F i - M) * RF i * (F i - M))) * RM := by
  have hterm (i : ι) :
      weight i * RF i =
        weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
    nth_rewrite 1 [noncommutative_resolvent_second_order
      (F i) M S (RF i) RM (hF_left i) (hF_right i) hM_left hM_right]
    have hw := commute_mean i
    calc
      weight i *
        (RM - RM * (F i - M) * RM +
          RM * (F i - M) * RF i * (F i - M) * RM) =
        weight i * RM -
          (weight i * RM) * (F i - M) * RM +
          (weight i * RM) * ((F i - M) * RF i * (F i - M)) * RM := by
            noncomm_ring
      _ = weight i * RM -
          (RM * weight i) * (F i - M) * RM +
          (RM * weight i) * ((F i - M) * RF i * (F i - M)) * RM := by
            rw [hw]
      _ = weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            noncomm_ring
  calc
    (∑ i : ι, weight i * RF i) - RM =
        (∑ i : ι,
          (weight i * RM - RM * (weight i * (F i - M)) * RM +
            RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM)) - RM := by
              congr 1
              exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i : ι, weight i) * RM -
          RM * (∑ i : ι, weight i * (F i - M)) * RM +
          RM * (∑ i : ι,
            weight i * ((F i - M) * RF i * (F i - M))) * RM - RM := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.sum_mul, ← Finset.mul_sum]
    _ = RM * (∑ i : ι,
          weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            rw [normalized, centered]
            noncomm_ring

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

theorem posSemidef_hermitian_sandwich
    {d : Type*} [Fintype d] [DecidableEq d]
    {A D : Matrix d d ℂ}
    (hA : A.PosSemidef) (hD : D.IsHermitian) :
    (D * A * D).PosSemidef := by
  simpa [hD.eq] using hA.mul_mul_conjTranspose_same D

theorem shifted_posSemidef_matrix_posDef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F : Matrix d d ℂ} (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (F + s • (1 : Matrix d d ℂ)).PosDef := by
  have hshift : (s • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.one.smul hs
  exact Matrix.PosDef.posSemidef_add hF hshift

theorem shifted_posSemidef_matrix_inverse_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F : Matrix d d ℂ} (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    ((F + s • (1 : Matrix d d ℂ))⁻¹).PosSemidef :=
  (shifted_posSemidef_matrix_posDef hF hs).posSemidef.inv

theorem matrix_weighted_centered
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M) :
    (∑ i : ι, weight i • (F i - M)) = 0 := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, mean, ← Finset.sum_smul, normalized]
  simp

theorem weighted_positive_matrix_mean
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (positive : ∀ i, (F i).PosSemidef) :
    (∑ i : ι, weight i • F i).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ
    (fun i _ => (positive i).smul (nonnegative i))

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

theorem scalar_resolvent_purification_integrable_of_pos
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun s : ℝ => (z / (z + s)) ^ 2) (Ioi 0) := by
  have hpower :
      IntegrableOn (fun s : ℝ => (s + z) ^ (-2 : ℝ)) (Ioi 0) := by
    exact integrableOn_add_rpow_Ioi_of_lt
      (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := z)
      (by norm_num) (by linarith)
  have hscaled :
      IntegrableOn (fun s : ℝ => z ^ 2 * (s + z) ^ (-2 : ℝ))
        (Ioi 0) :=
    hpower.const_mul (z ^ 2)
  refine hscaled.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hspos : 0 < s + z := by
    have : 0 < s := hs
    linarith
  change z ^ 2 * (s + z) ^ (-2 : ℝ) = (z / (z + s)) ^ 2
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg hspos.le, Real.rpow_two]
  rw [div_pow]
  simp [div_eq_mul_inv, add_comm]

theorem scalar_resolvent_purification_integrable
    {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun s : ℝ => (z / (z + s)) ^ 2) (Ioi 0) := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp
  · exact scalar_resolvent_purification_integrable_of_pos hzpos

theorem scalar_resolvent_purification_integral
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ s in Ioi (0 : ℝ), (z / (z + s)) ^ 2) = z := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp
  · have hderiv :
        ∀ x ∈ Ici (0 : ℝ),
          HasDerivAt (fun t : ℝ => -(z ^ 2) / (z + t))
            ((z / (z + x)) ^ 2) x := by
      intro x hx
      have hden : z + x ≠ 0 := by
        have hx_nonneg : 0 ≤ x := hx
        exact ne_of_gt (by linarith)
      have hd := ((hasDerivAt_const x (-(z ^ 2))).div
        ((hasDerivAt_const x z).add (hasDerivAt_id x)) hden)
      have hfun :
          (fun t : ℝ => -(z ^ 2) / (z + t)) =
            (fun _t : ℝ => -(z ^ 2)) /
              ((fun _t : ℝ => z) + id) := by
        funext t
        rfl
      rw [hfun]
      simpa [div_pow] using hd
    have hlimit :
        Tendsto (fun t : ℝ => -(z ^ 2) / (z + t))
          atTop (𝓝 (0 : ℝ)) := by
      have hden : Tendsto (fun t : ℝ => t + z) atTop atTop :=
        tendsto_atTop_add_const_right atTop z tendsto_id
      have hzero : Tendsto (fun t : ℝ => -(z ^ 2) / (t + z))
          atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds.div_atTop hden
      simpa [add_comm] using hzero
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv (scalar_resolvent_purification_integrable_of_pos hzpos) hlimit
    calc
      (∫ s in Ioi (0 : ℝ), (z / (z + s)) ^ 2) =
          (0 : ℝ) - (-(z ^ 2) / (z + 0)) := hftc
      _ = z := by
        field_simp
        ; ring

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def diagonalPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)

theorem diagonalPurificationGram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalue i) :
    IntegrableOn (diagonalPurificationGram eigenvalue) (Ioi 0) := by
  apply MeasureTheory.Integrable.of_eval
  intro i
  apply MeasureTheory.Integrable.of_eval
  intro j
  classical
  by_cases h : i = j
  · subst j
    have hcomplex :
        Integrable
          (fun s : ℝ =>
            (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ))
          (volume.restrict (Ioi 0)) :=
      MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
        (scalar_resolvent_purification_integrable (h_nonneg i))
    simpa only [diagonalPurificationGram, Matrix.diagonal_apply_eq] using
      hcomplex
  · simp [diagonalPurificationGram, h]

theorem integral_diagonalPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalue i) :
    (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) =
      Matrix.diagonal (fun i => (eigenvalue i : ℂ)) := by
  classical
  have hmatrix := diagonalPurificationGram_integrable eigenvalue h_nonneg
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ => diagonalPurificationGram eigenvalue s i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  have hentry (i : d) :
      ∀ j : d,
        Integrable
          (fun s : ℝ => diagonalPurificationGram eigenvalue s i j)
          (volume.restrict (Ioi 0)) :=
    fun j => (hrows i).eval j
  ext i j
  rw [MeasureTheory.eval_integral hrows i,
    MeasureTheory.eval_integral (hentry i) j]
  by_cases h : i = j
  · subst j
    simp only [diagonalPurificationGram, Matrix.diagonal_apply_eq]
    calc
      (∫ s in Ioi (0 : ℝ),
        (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) =
          ((∫ s in Ioi (0 : ℝ),
            (eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ) :=
        integral_ofReal
      _ = (eigenvalue i : ℂ) := by
        rw [scalar_resolvent_purification_integral (h_nonneg i)]
  · simp [diagonalPurificationGram, h]

def spectralConjugationCLM
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    (Unitary.conjStarAlgAut ℝ (Matrix d d ℂ) U).toAlgEquiv.toLinearEquiv.toLinearMap

@[simp] theorem spectralConjugationCLM_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    spectralConjugationCLM U A =
      (U : Matrix d d ℂ) * A * star (U : Matrix d d ℂ) := by
  rfl

def spectralPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (diagonalPurificationGram hF.isHermitian.eigenvalues s)

theorem spectralPurificationGram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn (spectralPurificationGram F hF) (Ioi 0) := by
  have hdiag := diagonalPurificationGram_integrable
    hF.isHermitian.eigenvalues (fun i => hF.eigenvalues_nonneg i)
  exact (spectralConjugationCLM hF.isHermitian.eigenvectorUnitary).integrable_comp
    hdiag

theorem integral_spectralPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ), spectralPurificationGram F hF s) = F := by
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag := diagonalPurificationGram_integrable
    eigenvalue (fun i => hF.eigenvalues_nonneg i)
  calc
    (∫ s in Ioi (0 : ℝ), spectralPurificationGram F hF s) =
        spectralConjugationCLM U
          (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) := by
            exact ContinuousLinearMap.integral_comp_comm
              (spectralConjugationCLM U) hdiag
    _ = spectralConjugationCLM U
          (Matrix.diagonal (fun i => (eigenvalue i : ℂ))) := by
            rw [integral_diagonalPurificationGram eigenvalue
              (fun i => hF.eigenvalues_nonneg i)]
    _ = F := by
          simpa [U, eigenvalue, Function.comp_def,
            Unitary.conjStarAlgAut_apply] using
            hF.isHermitian.spectral_theorem.symm

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Kronecker Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def spectralPurificationFilter
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i /
        (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

theorem spectralPurificationFilter_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s =
      spectralPurificationGram F hF s := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let D : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U
  have hDhermitian : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) = _
    simp
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hDhermitian.eq
  have hDsquare : D * D = diagonalPurificationGram eigenvalue s := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp [diagonalPurificationGram, pow_two]
    · simp [diagonalPurificationGram, h]
  change star (e D) * e D = e (diagonalPurificationGram eigenvalue s)
  calc
    star (e D) * e D = e (star D) * e D := by rw [map_star]
    _ = e (star D * D) := (map_mul e (star D) D).symm
    _ = e (diagonalPurificationGram eigenvalue s) := by
      rw [hDstar, hDsquare]

theorem integral_spectralPurificationFilter_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ),
      star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s) = F := by
  simp_rw [spectralPurificationFilter_gram]
  exact integral_spectralPurificationGram F hF

theorem spectralPurificationFilter_gram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn
      (fun s : ℝ => star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s) (Ioi 0) := by
  simpa only [spectralPurificationFilter_gram] using
    spectralPurificationGram_integrable F hF

def bornTracePairing
    {dA dB : Type*} [Fintype dA] [Fintype dB]
    (ρ : Matrix (dA × dB) (dA × dB) ℂ) :
    Matrix dA dA ℂ →ₗ[ℝ] Matrix dB dB ℂ →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := fun G => (Matrix.trace (ρ * (F ⊗ₖ G))).re
      map_add' := by
        intro G H
        simp [Matrix.kronecker_add, Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro r G
        simp [Matrix.kronecker_smul, mul_smul_comm, Matrix.trace_smul] }
  map_add' := by
    intro F H
    ext G
    simp [Matrix.add_kronecker, Matrix.mul_add, Matrix.trace_add]
  map_smul' := by
    intro r F
    ext G
    simp [Matrix.smul_kronecker, mul_smul_comm, Matrix.trace_smul]

end

noncomputable section

open scoped BigOperators Kronecker

namespace Game

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem questionWeight_le_marginalX
    (G : Game X Y A B) (x : X) (y : Y) :
    G.questionWeight x y ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.single_le_sum
    (fun y _ => G.weight_nonneg x y)
    (Finset.mem_univ y)

theorem questionWeight_le_marginalY
    (G : Game X Y A B) (x : X) (y : Y) :
    G.questionWeight x y ≤ G.marginalY y := by
  unfold marginalY
  exact Finset.single_le_sum
    (fun x _ => G.weight_nonneg x y)
    (Finset.mem_univ x)

def conditionalYGivenX (G : Game X Y A B) (x : X) (y : Y) : ℝ :=
  G.questionWeight x y / G.marginalX x

def conditionalXGivenY (G : Game X Y A B) (y : Y) (x : X) : ℝ :=
  G.questionWeight x y / G.marginalY y

theorem conditionalYGivenX_nonneg
    (G : Game X Y A B) (x : X) (y : Y) :
    0 ≤ G.conditionalYGivenX x y := by
  exact div_nonneg (G.weight_nonneg x y)
    (G.marginalX_nonneg x)

theorem conditionalXGivenY_nonneg
    (G : Game X Y A B) (y : Y) (x : X) :
    0 ≤ G.conditionalXGivenY y x := by
  exact div_nonneg (G.weight_nonneg x y)
    (G.marginalY_nonneg y)

theorem marginalX_mul_conditionalYGivenX
    (G : Game X Y A B) (x : X) (y : Y) :
    G.marginalX x * G.conditionalYGivenX x y =
      G.questionWeight x y := by
  unfold conditionalYGivenX
  by_cases hx : G.marginalX x = 0
  · have hzero : G.questionWeight x y = 0 := by
      have hle := G.questionWeight_le_marginalX x y
      have hnonneg := G.weight_nonneg x y
      rw [hx] at hle
      linarith
    simp [hx, hzero]
  · field_simp

theorem marginalY_mul_conditionalXGivenY
    (G : Game X Y A B) (x : X) (y : Y) :
    G.marginalY y * G.conditionalXGivenY y x =
      G.questionWeight x y := by
  unfold conditionalXGivenY
  by_cases hy : G.marginalY y = 0
  · have hzero : G.questionWeight x y = 0 := by
      have hle := G.questionWeight_le_marginalY x y
      have hnonneg := G.weight_nonneg x y
      rw [hy] at hle
      linarith
    simp [hy, hzero]
  · field_simp

theorem conditionalYGivenX_sum
    (G : Game X Y A B) (x : X)
    (hx : 0 < G.marginalX x) :
    (∑ y : Y, G.conditionalYGivenX x y) = 1 := by
  unfold conditionalYGivenX
  rw [← Finset.sum_div]
  change G.marginalX x / G.marginalX x = 1
  exact div_self hx.ne'

theorem conditionalXGivenY_sum
    (G : Game X Y A B) (y : Y)
    (hy : 0 < G.marginalY y) :
    (∑ x : X, G.conditionalXGivenY y x) = 1 := by
  unfold conditionalXGivenY
  rw [← Finset.sum_div]
  change G.marginalY y / G.marginalY y = 1
  exact div_self hy.ne'

end Game

section MixedHistories

variable {X Y A B U V : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup V] [Module ℝ V]

def conditionalBobAverage
    (G : Game X Y A B) (K : Y → V) (x : X) : V :=
  ∑ y : Y, G.conditionalYGivenX x y • K y

def conditionalAliceAverage
    (G : Game X Y A B) (H : X → U) (y : Y) : U :=
  ∑ x : X, G.conditionalXGivenY y x • H x

theorem alice_mixed_history_pairing
    (G : Game X Y A B)
    (pair : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H : X → U) (K : Y → V) :
    (∑ x : X,
      G.marginalX x *
        pair (H x) (conditionalBobAverage G K x))
      =
    ∑ x : X, ∑ y : Y,
      G.questionWeight x y * pair (H x) (K y) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  unfold conditionalBobAverage
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [map_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, G.marginalX_mul_conditionalYGivenX x y]

theorem bob_mixed_history_pairing
    (G : Game X Y A B)
    (pair : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H : X → U) (K : Y → V) :
    (∑ y : Y,
      G.marginalY y *
        pair (conditionalAliceAverage G H y) (K y))
      =
    ∑ x : X, ∑ y : Y,
      G.questionWeight x y * pair (H x) (K y) := by
  classical
  calc
    (∑ y : Y,
      G.marginalY y *
        pair (conditionalAliceAverage G H y) (K y))
      =
      ∑ y : Y, ∑ x : X,
        G.questionWeight x y * pair (H x) (K y) := by
        apply Finset.sum_congr rfl
        intro y _
        unfold conditionalAliceAverage
        rw [map_sum]
        simp only [LinearMap.sum_apply, map_smul,
          LinearMap.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [← mul_assoc, G.marginalY_mul_conditionalXGivenY x y]
    _ =
      ∑ x : X, ∑ y : Y,
        G.questionWeight x y * pair (H x) (K y) := by
          rw [Finset.sum_comm]

theorem alice_reveal_increment
    (G : Game X Y A B)
    (pair : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H : X → U) (M : Y → U) (K : Y → V)
    (f : U → U) :
    (∑ x : X,
      G.marginalX x *
        pair (f (H x)) (conditionalBobAverage G K x))
      -
    (∑ y : Y,
      G.marginalY y *
        pair (f (M y)) (K y))
      =
    ∑ y : Y,
      G.marginalY y *
        pair
          (conditionalAliceAverage G (fun x => f (H x)) y -
            f (M y))
          (K y) := by
  classical
  rw [alice_mixed_history_pairing G pair (fun x => f (H x)) K]
  rw [← bob_mixed_history_pairing G pair (fun x => f (H x)) K]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [map_sub]
  simp only [LinearMap.sub_apply]
  ring

end MixedHistories

section RepeatedQuantumFilters

open scoped ComplexOrder MatrixOrder

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def conditionedAliceEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact
    ∑ answers : Fin n → A,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = α ⟨i, hi⟩
      then (S.aliceMeasurement xs).effect answers
      else 0

def conditionedBobEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact
    ∑ answers : Fin n → B,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = β ⟨i, hi⟩
      then (S.bobMeasurement ys).effect answers
      else 0

theorem conditionedAliceEffect_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    (conditionedAliceEffect G n S D α xs).PosSemidef := by
  classical
  unfold conditionedAliceEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.aliceMeasurement xs).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedBobEffect_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    (conditionedBobEffect G n S D β ys).PosSemidef := by
  classical
  unfold conditionedBobEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.bobMeasurement ys).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedAliceEffect_complement_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    (1 - conditionedAliceEffect G n S D α xs).PosSemidef := by
  classical
  have hsplit :
      1 - conditionedAliceEffect G n S D α xs =
        ∑ answers : Fin n → A,
          if ∀ (i : Fin n) (hi : i ∈ D),
            answers i = α ⟨i, hi⟩
          then 0
          else (S.aliceMeasurement xs).effect answers := by
    unfold conditionedAliceEffect
    rw [← (S.aliceMeasurement xs).complete,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro answers _
    split_ifs <;> simp
  rw [hsplit]
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact (S.aliceMeasurement xs).positive answers

theorem conditionedBobEffect_complement_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    (1 - conditionedBobEffect G n S D β ys).PosSemidef := by
  classical
  have hsplit :
      1 - conditionedBobEffect G n S D β ys =
        ∑ answers : Fin n → B,
          if ∀ (i : Fin n) (hi : i ∈ D),
            answers i = β ⟨i, hi⟩
          then 0
          else (S.bobMeasurement ys).effect answers := by
    unfold conditionedBobEffect
    rw [← (S.bobMeasurement ys).complete,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro answers _
    split_ifs <;> simp
  rw [hsplit]
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact (S.bobMeasurement ys).positive answers

end RepeatedQuantumFilters

theorem history_forward_telescope (E : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, (E (k + 1) - E k))
      = E m - E 0 := by
  simpa [Nat.succ_eq_add_one] using Finset.sum_range_sub E m

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

def spectralSupportFunctional
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) : Matrix d d ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary)
      (Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ))

theorem spectralSupportFunctional_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f g : ℝ → ℝ) :
    spectralSupportFunctional F hF f *
        spectralSupportFunctional F hF g =
      spectralSupportFunctional F hF (fun x => f x * g x) := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  change e _ * e _ = e _
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  rfl

theorem spectralSupportFunctional_id
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportFunctional F hF (fun x => x) = F := by
  simpa [spectralSupportFunctional, Function.comp_def] using
    hF.isHermitian.spectral_theorem.symm

theorem spectralSupportFunctional_congr
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {f g : ℝ → ℝ}
    (h : ∀ i : d,
      f (hF.isHermitian.eigenvalues i) =
        g (hF.isHermitian.eigenvalues i)) :
    spectralSupportFunctional F hF f =
      spectralSupportFunctional F hF g := by
  unfold spectralSupportFunctional
  congr 2
  funext i
  exact_mod_cast h i

theorem spectralSupportFunctional_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) :
    (spectralSupportFunctional F hF f).IsHermitian := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ)
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (f (hF.isHermitian.eigenvalues i) : ℂ) = _
    simp
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hD.eq
  change Matrix.conjTranspose (e D) = e D
  simpa only [Matrix.star_eq_conjTranspose] using
    (show star (e D) = e D by rw [← map_star, hDstar])

def spectralSupportInverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => x⁻¹)

def spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)

def spectralSupportSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF Real.sqrt

theorem spectralSupportInverse_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportInverse F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _

theorem spectralSupportProjection_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportProjection F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _

theorem spectralSupportInverse_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportInverse F hF * F =
      spectralSupportProjection F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F =
        spectralSupportFunctional F hF (fun x => x⁻¹) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x⁻¹ * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])

theorem mul_spectralSupportInverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    F * spectralSupportInverse F hF =
      spectralSupportProjection F hF := by
  change F * spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    F * spectralSupportFunctional F hF (fun x => x⁻¹) =
        spectralSupportFunctional F hF (fun x => x) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x * x⁻¹) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])

theorem spectralSupportProjection_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportProjection F hF * F = F := by
  change spectralSupportFunctional F hF
      (fun x => if x = 0 then 0 else 1) * F = F
  calc
    spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) * F =
      spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (if x = 0 then 0 else 1) * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = spectralSupportFunctional F hF (fun x => x) :=
      spectralSupportFunctional_congr F hF (by
        intro i
        by_cases hi : hF.isHermitian.eigenvalues i = 0 <;> simp [hi])
    _ = F := spectralSupportFunctional_id F hF

theorem spectralSupportInverse_penrose
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportInverse F hF * F *
        spectralSupportInverse F hF =
      spectralSupportInverse F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F *
      spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => x⁻¹)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F *
        spectralSupportFunctional F hF (fun x => x⁻¹) =
      (spectralSupportFunctional F hF (fun x => x⁻¹) *
        spectralSupportFunctional F hF (fun x => x)) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (x⁻¹ * x) * x⁻¹) := by
      rw [spectralSupportFunctional_mul,
        spectralSupportFunctional_mul]
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])

theorem spectralSupportSqrt_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportSqrt F hF * spectralSupportSqrt F hF = F := by
  change spectralSupportFunctional F hF Real.sqrt *
    spectralSupportFunctional F hF Real.sqrt = F
  calc
    spectralSupportFunctional F hF Real.sqrt *
        spectralSupportFunctional F hF Real.sqrt =
      spectralSupportFunctional F hF
        (fun x => Real.sqrt x * Real.sqrt x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = spectralSupportFunctional F hF (fun x => x) :=
      spectralSupportFunctional_congr F hF (by
        intro i
        exact Real.mul_self_sqrt (hF.eigenvalues_nonneg i))
    _ = F := spectralSupportFunctional_id F hF

end

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

theorem mul_spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    F * spectralSupportProjection F hF = F := by
  have h := congrArg Matrix.conjTranspose
    (spectralSupportProjection_mul F hF)
  simpa [Matrix.conjTranspose_mul,
    (spectralSupportProjection_isHermitian F hF).eq,
    hF.isHermitian.eq] using h

theorem posSemidef_kernel_of_sub_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hA : A.PosSemidef) (hsub : (F - A).PosSemidef)
    {x : d → ℂ} (hx : F *ᵥ x = 0) :
    A *ᵥ x = 0 := by
  -- Vendoring compile fix (Mathlib v4.35): `dotProduct_mulVec_zero_iff` takes the vector
  -- implicitly. See README.md.
  apply hA.dotProduct_mulVec_zero_iff.mp
  have hA_nonneg : 0 ≤ star x ⬝ᵥ (A *ᵥ x) :=
    hA.dotProduct_mulVec_nonneg x
  have hsub_nonneg : 0 ≤ star x ⬝ᵥ ((F - A) *ᵥ x) :=
    hsub.dotProduct_mulVec_nonneg x
  have hzero :
      star x ⬝ᵥ (A *ᵥ x) +
        star x ⬝ᵥ ((F - A) *ᵥ x) = 0 := by
    calc
      star x ⬝ᵥ (A *ᵥ x) +
          star x ⬝ᵥ ((F - A) *ᵥ x) =
        star x ⬝ᵥ ((A + (F - A)) *ᵥ x) := by
          rw [Matrix.add_mulVec, dotProduct_add]
      _ = star x ⬝ᵥ (F *ᵥ x) := by
        have hsum : A + (F - A) = F := by abel
        rw [hsum]
      _ = 0 := by rw [hx]; simp
  exact (add_eq_zero_iff_of_nonneg hA_nonneg hsub_nonneg).mp hzero |>.1

theorem posSemidef_mul_spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    A * spectralSupportProjection F hF = A := by
  let P := spectralSupportProjection F hF
  have hFP : F * P = F := mul_spectralSupportProjection F hF
  have hkernel : F * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hFP, sub_self]
  have hAzero : A * (1 - P) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    have hxi : F *ᵥ ((1 - P) *ᵥ Pi.single i 1) = 0 := by
      have h := congrArg
        (fun M : Matrix d d ℂ => M *ᵥ Pi.single i 1) hkernel
      simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using h
    have hAi := posSemidef_kernel_of_sub_posSemidef hA hsub hxi
    simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hAi
  have hdiff : A - A * P = 0 := by
    simpa [mul_sub] using hAzero
  exact (sub_eq_zero.mp hdiff).symm

theorem spectralSupportProjection_mul_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    spectralSupportProjection F hF * A = A := by
  have h := congrArg Matrix.conjTranspose
    (posSemidef_mul_spectralSupportProjection hF hA hsub)
  simpa [Matrix.conjTranspose_mul,
    (spectralSupportProjection_isHermitian F hF).eq,
    hA.isHermitian.eq] using h

theorem refinement_complement_posSemidef
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    ((∑ b : ι, effect b) - effect a).PosSemidef := by
  have herase : (∑ b ∈ Finset.univ.erase a, effect b).PosSemidef := by
    apply Matrix.posSemidef_sum (Finset.univ.erase a)
    intro c _
    exact hpositive c
  have hsum : effect a +
      (∑ b ∈ Finset.univ.erase a, effect b) =
      ∑ b : ι, effect b := by
    simp
  rw [← hsum, add_sub_cancel_left]
  exact herase

end

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option maxHeartbeats 400000

def purificationRangeProjection
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ

theorem purificationRangeProjection_isHermitian
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) :
    (purificationRangeProjection F hF Γ).IsHermitian := by
  unfold purificationRangeProjection
  change Matrix.conjTranspose
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) = _
  simp [Matrix.conjTranspose_mul,
    (spectralSupportInverse_isHermitian F hF).eq, Matrix.mul_assoc]

theorem purificationRangeProjection_idempotent
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    purificationRangeProjection F hF Γ *
        purificationRangeProjection F hF Γ =
      purificationRangeProjection F hF Γ := by
  unfold purificationRangeProjection
  calc
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * (spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            rw [hΓ]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

theorem purificationRangeProjection_complement_posSemidef
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    (1 - purificationRangeProjection F hF Γ).PosSemidef := by
  let P := purificationRangeProjection F hF Γ
  have hPstar : Matrix.conjTranspose P = P :=
    (purificationRangeProjection_isHermitian F hF Γ).eq
  have hPsq : P * P = P :=
    purificationRangeProjection_idempotent F hF Γ hΓ
  have hsquare :
      Matrix.conjTranspose (1 - P) * (1 - P) = 1 - P := by
    calc
      Matrix.conjTranspose (1 - P) * (1 - P) =
          (1 - P) * (1 - P) := by
            simp [Matrix.conjTranspose_sub, hPstar]
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPsq]; noncomm_ring
  have hpositive := Matrix.posSemidef_conjTranspose_mul_self
    (1 - P)
  rw [hsquare] at hpositive
  exact hpositive

def purifiedRefinementCore
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ) (a : ι) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * effect a *
    spectralSupportInverse F hF * Matrix.conjTranspose Γ

theorem purifiedRefinementCore_posSemidef
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    (purifiedRefinementCore F hF Γ effect a).PosSemidef := by
  have h := (hpositive a).mul_mul_conjTranspose_same
    (Γ * spectralSupportInverse F hF)
  simpa [purifiedRefinementCore, Matrix.conjTranspose_mul,
    (spectralSupportInverse_isHermitian F hF).eq,
    Matrix.mul_assoc] using h

theorem purifiedRefinementCore_sum
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F) :
    (∑ a : ι, purifiedRefinementCore F hF Γ effect a) =
      purificationRangeProjection F hF Γ := by
  unfold purifiedRefinementCore purificationRangeProjection
  calc
    (∑ a : ι,
      Γ * spectralSupportInverse F hF * effect a *
        spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * spectralSupportInverse F hF *
        (∑ a : ι, effect a) * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_sum, Matrix.sum_mul]
    _ = Γ * spectralSupportInverse F hF * F *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ := by
            rw [hsum]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

def purifiedRefinedEffect
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (a₀ a : ι) : Matrix e e ℂ :=
  purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0

theorem purifiedRefinedEffect_posSemidef
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a₀ a : ι) :
    (purifiedRefinedEffect F hF Γ effect a₀ a).PosSemidef := by
  change (purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0).PosSemidef
  refine (purifiedRefinementCore_posSemidef F hF Γ effect
    hpositive a).add ?_
  split
  · exact purificationRangeProjection_complement_posSemidef F hF Γ hΓ
  · exact Matrix.PosSemidef.zero

theorem purifiedRefinedEffect_complete
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) :
    (∑ a : ι, purifiedRefinedEffect F hF Γ effect a₀ a) = 1 := by
  classical
  unfold purifiedRefinedEffect
  rw [Finset.sum_add_distrib]
  rw [purifiedRefinementCore_sum F hF Γ effect hsum]
  simp

theorem purificationRangeProjection_compression
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ = F := by
  unfold purificationRangeProjection
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) := by
          simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * F := by rw [hΓ]
    _ = spectralSupportProjection F hF * F := by
      rw [mul_spectralSupportInverse]
    _ = F := spectralSupportProjection_mul F hF

theorem purificationRangeProjection_complement_compression
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ = 0 := by
  calc
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ =
      Matrix.conjTranspose Γ * Γ -
        Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp
    _ = F - F := by
      rw [hΓ, purificationRangeProjection_compression F hF Γ hΓ]
    _ = 0 := sub_self F

theorem purifiedRefinementCore_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinementCore F hF Γ effect a * Γ = effect a := by
  have hsub : (F - effect a).PosSemidef := by
    rw [← hsum]
    exact refinement_complement_posSemidef effect hpositive a
  unfold purifiedRefinementCore
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        effect a * spectralSupportInverse F hF *
          (Matrix.conjTranspose Γ * Γ) := by
            simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * F := by
            rw [hΓ]
    _ = (F * spectralSupportInverse F hF) * effect a *
          (spectralSupportInverse F hF * F) := by
            simp only [Matrix.mul_assoc]
    _ = spectralSupportProjection F hF * effect a *
          spectralSupportProjection F hF := by
            rw [mul_spectralSupportInverse, spectralSupportInverse_mul]
    _ = effect a := by
      rw [spectralSupportProjection_mul_posSemidef hF
        (hpositive a) hsub]
      exact posSemidef_mul_spectralSupportProjection hF
        (hpositive a) hsub

theorem purifiedRefinedEffect_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinedEffect F hF Γ effect a₀ a * Γ = effect a := by
  have hdefect : Matrix.conjTranspose Γ *
      (if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = 0 := by
    split
    · exact purificationRangeProjection_complement_compression F hF Γ hΓ
    · simp
  change Matrix.conjTranspose Γ *
      (purifiedRefinementCore F hF Γ effect a +
        if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = effect a
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [purifiedRefinementCore_compression F hF Γ hΓ
    effect hpositive hsum a, hdefect, add_zero]

def purifiedRefinedPOVM
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) : POVM ι e where
  effect := purifiedRefinedEffect F hF Γ effect a₀
  positive a := purifiedRefinedEffect_posSemidef F hF Γ hΓ
    effect hpositive a₀ a
  complete := purifiedRefinedEffect_complete F hF Γ effect hsum a₀

theorem purifiedRefinedPOVM_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
      (purifiedRefinedPOVM F hF Γ hΓ effect hpositive hsum a₀).effect a *
        Γ = effect a :=
  purifiedRefinedEffect_compression F hF Γ hΓ effect
    hpositive hsum a₀ a

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def fullHistoryRemaining (n : ℕ)
    (D L : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ D) \ L

@[ext (iff := false)] structure FullSubsetHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    (n : ℕ) (D L : Finset (Fin n)) where
  aliceConditioned : {i : Fin n // i ∈ D} → X
  bobConditioned : {i : Fin n // i ∈ D} → Y
  aliceRevealed : {i : Fin n // i ∈ L} → X
  bobRemaining : {i : Fin n // i ∈ fullHistoryRemaining n D L} → Y
  deriving Fintype

def fullHistoryAliceQuestion
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) :
    Fin n → X := fun i =>
  if hiD : i ∈ D then h.aliceConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then h.aliceRevealed ⟨i, hiL⟩
  else hidden ⟨i, by
    simp [fullHistoryRemaining, hiD, hiL]⟩

def fullHistoryBobQuestion
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) :
    Fin n → Y := fun i =>
  if hiD : i ∈ D then h.bobConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then hidden ⟨i, hiL⟩
  else h.bobRemaining ⟨i, by
    simp [fullHistoryRemaining, hiD, hiL]⟩

def fullHistoryQuestionEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (FullSubsetHistory X Y n D L ×
      ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) ×
      ({i : Fin n // i ∈ L} → Y)) ≃
      ((Fin n → X) × (Fin n → Y)) where
  toFun t :=
    (fullHistoryAliceQuestion t.1 t.2.1,
      fullHistoryBobQuestion t.1 t.2.2)
  invFun q :=
    (⟨fun i => q.1 i,
      fun i => q.2 i,
      fun i => q.1 i,
      fun i => q.2 i⟩,
      (fun i => q.1 i),
      (fun i => q.2 i))
  left_inv := by
    rintro ⟨h, hx, hy⟩
    apply Prod.ext
    · apply FullSubsetHistory.ext
      · funext i
        simp [fullHistoryAliceQuestion, i.property]
      · funext i
        simp [fullHistoryBobQuestion, i.property]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp [fullHistoryAliceQuestion, hiD, i.property]
      · funext i
        have hiD : (i : Fin n) ∉ D := by
          have := i.property
          simpa [fullHistoryRemaining] using
            (Finset.mem_sdiff.mp
              (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp [fullHistoryBobQuestion, hiD, hiL]
    · apply Prod.ext
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp
            (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp [fullHistoryAliceQuestion, hiD, hiL]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp [fullHistoryBobQuestion, hiD, i.property]
  right_inv := by
    rintro ⟨xs, ys⟩
    apply Prod.ext
    · funext i
      by_cases hiD : i ∈ D
      · simp [fullHistoryAliceQuestion, hiD]
      · by_cases hiL : i ∈ L <;>
          simp [fullHistoryAliceQuestion, hiD, hiL]
    · funext i
      by_cases hiD : i ∈ D
      · simp [fullHistoryBobQuestion, hiD]
      · by_cases hiL : i ∈ L <;>
          simp [fullHistoryBobQuestion, hiD, hiL]

section ActualHistoryWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullHistoryWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) : ℝ :=
  (∏ i : {i : Fin n // i ∈ D},
    G.questionWeight (h.aliceConditioned i) (h.bobConditioned i)) *
  (∏ i : {i : Fin n // i ∈ L},
    G.marginalX (h.aliceRevealed i)) *
  (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.marginalY (h.bobRemaining i))

def fullHistoryHiddenAliceWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) : ℝ :=
  ∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.conditionalXGivenY (h.bobRemaining i) (hidden i)

def fullHistoryHiddenBobWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) : ℝ :=
  ∏ i : {i : Fin n // i ∈ L},
    G.conditionalYGivenX (h.aliceRevealed i) (hidden i)

theorem fullHistoryWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) :
    0 ≤ fullHistoryWeight G h := by
  unfold fullHistoryWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun i _ =>
        G.weight_nonneg (h.aliceConditioned i) (h.bobConditioned i)
    · exact Finset.prod_nonneg fun i _ =>
        G.marginalX_nonneg (h.aliceRevealed i)
  · exact Finset.prod_nonneg fun i _ =>
      G.marginalY_nonneg (h.bobRemaining i)

theorem fullHistoryHiddenAliceWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) :
    0 ≤ fullHistoryHiddenAliceWeight G h hidden := by
  unfold fullHistoryHiddenAliceWeight
  exact Finset.prod_nonneg fun i _ =>
    G.conditionalXGivenY_nonneg (h.bobRemaining i) (hidden i)

theorem fullHistoryHiddenBobWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) :
    0 ≤ fullHistoryHiddenBobWeight G h hidden := by
  unfold fullHistoryHiddenBobWeight
  exact Finset.prod_nonneg fun i _ =>
    G.conditionalYGivenX_nonneg (h.aliceRevealed i) (hidden i)

theorem fullHistoryWeight_mul_hidden
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (h : FullSubsetHistory X Y n D L)
    (hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X)
    (hy : {i : Fin n // i ∈ L} → Y) :
    fullHistoryWeight G h *
        fullHistoryHiddenAliceWeight G h hx *
        fullHistoryHiddenBobWeight G h hy =
      (G.repeat n).questionWeight
        (fullHistoryAliceQuestion h hx)
        (fullHistoryBobQuestion h hy) := by
  classical
  let q : Fin n → ℝ := fun i =>
    G.questionWeight
      (fullHistoryAliceQuestion h hx i)
      (fullHistoryBobQuestion h hy i)
  have hDprod :
      (∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) =
        ∏ i ∈ D, q i := by
    calc
      (∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) =
        ∏ i : {i : Fin n // i ∈ D}, q i := by
          apply Finset.prod_congr rfl
          intro i _
          simp [q, fullHistoryAliceQuestion,
            fullHistoryBobQuestion, i.property]
      _ = ∏ i ∈ D, q i := Finset.prod_coe_sort D q
  have hLprod :
      (∏ i : {i : Fin n // i ∈ L},
        G.marginalX (h.aliceRevealed i)) *
      (∏ i : {i : Fin n // i ∈ L},
        G.conditionalYGivenX
          (h.aliceRevealed i) (hy i)) =
        ∏ i ∈ L, q i := by
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i : {i : Fin n // i ∈ L},
        G.marginalX (h.aliceRevealed i) *
          G.conditionalYGivenX (h.aliceRevealed i) (hy i)) =
        ∏ i : {i : Fin n // i ∈ L}, q i := by
          apply Finset.prod_congr rfl
          intro i _
          have hiD : (i : Fin n) ∉ D :=
            (Finset.mem_sdiff.mp (hL i.property)).2
          simpa [q, fullHistoryAliceQuestion,
            fullHistoryBobQuestion, hiD, i.property] using
              G.marginalX_mul_conditionalYGivenX
                (h.aliceRevealed i) (hy i)
      _ = ∏ i ∈ L, q i := Finset.prod_coe_sort L q
  have hRprod :
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.marginalY (h.bobRemaining i)) *
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.conditionalXGivenY
          (h.bobRemaining i) (hx i)) =
        ∏ i ∈ fullHistoryRemaining n D L, q i := by
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.marginalY (h.bobRemaining i) *
          G.conditionalXGivenY (h.bobRemaining i) (hx i)) =
        ∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L}, q i := by
          apply Finset.prod_congr rfl
          intro i _
          have hiD : (i : Fin n) ∉ D :=
            (Finset.mem_sdiff.mp
              (Finset.mem_sdiff.mp i.property).1).2
          have hiL : (i : Fin n) ∉ L :=
            (Finset.mem_sdiff.mp i.property).2
          simpa [q, fullHistoryAliceQuestion,
            fullHistoryBobQuestion, hiD, hiL] using
              G.marginalY_mul_conditionalXGivenY
                (hx i) (h.bobRemaining i)
      _ = ∏ i ∈ fullHistoryRemaining n D L, q i :=
        Finset.prod_coe_sort (fullHistoryRemaining n D L) q
  have hDL : Disjoint D L := by
    apply Finset.disjoint_left.mpr
    intro i hiD hiL
    exact (Finset.mem_sdiff.mp (hL hiL)).2 hiD
  have hDR : Disjoint (D ∪ L) (fullHistoryRemaining n D L) := by
    apply Finset.disjoint_left.mpr
    intro i hiUnion hiR
    have hiD : i ∉ D :=
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hiR).1).2
    have hiL : i ∉ L := (Finset.mem_sdiff.mp hiR).2
    rcases Finset.mem_union.mp hiUnion with hi | hi
    · exact hiD hi
    · exact hiL hi
  have hcover : D ∪ L ∪ fullHistoryRemaining n D L =
      (Finset.univ : Finset (Fin n)) := by
    ext i
    simp [fullHistoryRemaining]
    tauto
  rw [Game.repeat_questionWeight]
  change fullHistoryWeight G h *
      fullHistoryHiddenAliceWeight G h hx *
      fullHistoryHiddenBobWeight G h hy =
    ∏ i : Fin n, q i
  unfold fullHistoryWeight fullHistoryHiddenAliceWeight
    fullHistoryHiddenBobWeight
  calc
    ((∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) *
      (∏ i : {i : Fin n // i ∈ L},
        G.marginalX (h.aliceRevealed i)) *
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.marginalY (h.bobRemaining i))) *
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.conditionalXGivenY
          (h.bobRemaining i) (hx i)) *
      (∏ i : {i : Fin n // i ∈ L},
        G.conditionalYGivenX
          (h.aliceRevealed i) (hy i)) =
      (∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) *
        ((∏ i : {i : Fin n // i ∈ L},
          G.marginalX (h.aliceRevealed i)) *
          (∏ i : {i : Fin n // i ∈ L},
            G.conditionalYGivenX
              (h.aliceRevealed i) (hy i))) *
        ((∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
          G.marginalY (h.bobRemaining i)) *
          (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
            G.conditionalXGivenY
              (h.bobRemaining i) (hx i))) := by ring
    _ = (∏ i ∈ D, q i) *
          (∏ i ∈ L, q i) *
          (∏ i ∈ fullHistoryRemaining n D L, q i) := by
            rw [hDprod, hLprod, hRprod]
    _ = ∏ i : Fin n, q i := by
      rw [← Finset.prod_union hDL,
        ← Finset.prod_union hDR, hcover]

def fullHistoryAliceFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceEffect G n S D α
        (fullHistoryAliceQuestion h hidden)

def fullHistoryBobFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {i : Fin n // i ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobEffect G n S D β
        (fullHistoryBobQuestion h hidden)

theorem fullHistoryAliceFilter_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    (fullHistoryAliceFilter G n S D L h α).PosSemidef := by
  unfold fullHistoryAliceFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro hidden _
  exact (conditionedAliceEffect_positive G n S D α
    (fullHistoryAliceQuestion h hidden)).smul
      (fullHistoryHiddenAliceWeight_nonneg G h hidden)

theorem fullHistoryBobFilter_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    (fullHistoryBobFilter G n S D L h β).PosSemidef := by
  unfold fullHistoryBobFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro hidden _
  exact (conditionedBobEffect_positive G n S D β
    (fullHistoryBobQuestion h hidden)).smul
      (fullHistoryHiddenBobWeight_nonneg G h hidden)

def fullHistoryWinIndicator
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (h.aliceConditioned i) (h.bobConditioned i)
      (α i) (β i) = true then 1 else 0

theorem fullHistoryWinIndicator_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    0 ≤ fullHistoryWinIndicator G h α β := by
  classical
  unfold fullHistoryWinIndicator
  split <;> norm_num

theorem conditionedAnswerMatches_iff
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n))
    (answer : Fin n → T)
    (α : {i : Fin n // i ∈ D} → T) :
    (∀ (i : Fin n) (hi : i ∈ D), answer i = α ⟨i, hi⟩) ↔
      α = fun i : {i : Fin n // i ∈ D} => answer (i : Fin n) := by
  constructor
  · intro h
    funext i
    exact (h i i.property).symm
  · intro h i hi
    subst α
    rfl

theorem conditionedEffects_born_expansion
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y) :
    bornTracePairing S.state.matrix
        (conditionedAliceEffect G n S D α xs)
        (conditionedBobEffect G n S D β ys) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
          if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
            S.outcomeProbability xs ys aa bb
          else 0
        else 0 := by
  classical
  simp only [conditionedAliceEffect, conditionedBobEffect,
    map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  split_ifs with ha
  · apply Finset.sum_congr rfl
    intro bb _
    split_ifs with hb
    · rfl
    · exact map_zero _
  · simp

theorem finite_sum_four_swap
    {I J K T : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype T]
    (f : I → J → K → T → ℝ) :
    (∑ i : I, ∑ j : J, ∑ k : K, ∑ t : T, f i j k t) =
      ∑ k : K, ∑ t : T, ∑ i : I, ∑ j : J, f i j k t := by
  classical
  calc
    (∑ i : I, ∑ j : J, ∑ k : K, ∑ t : T, f i j k t) =
      ∑ i : I, ∑ k : K, ∑ j : J, ∑ t : T, f i j k t := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ k : K, ∑ i : I, ∑ j : J, ∑ t : T, f i j k t := by
      rw [Finset.sum_comm]
    _ = ∑ k : K, ∑ i : I, ∑ t : T, ∑ j : J, f i j k t := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : K, ∑ t : T, ∑ i : I, ∑ j : J, f i j k t := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

def fullQuestionWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D : Finset (Fin n))
    (xs : Fin n → X) (ys : Fin n → Y)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (xs i) (ys i) (α i) (β i) = true
    then 1 else 0

theorem fullHistoryWinIndicator_eq_question
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X)
    (hy : {i : Fin n // i ∈ L} → Y)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    fullHistoryWinIndicator G h α β =
      fullQuestionWinIndicator G D
        (fullHistoryAliceQuestion h hx)
        (fullHistoryBobQuestion h hy) α β := by
  classical
  unfold fullHistoryWinIndicator fullQuestionWinIndicator
  congr 1
  apply propext
  constructor
  · intro hw i
    simpa [fullHistoryAliceQuestion,
      fullHistoryBobQuestion, i.property] using hw i
  · intro hw i
    simpa [fullHistoryAliceQuestion,
      fullHistoryBobQuestion, i.property] using hw i

theorem conditionedEffects_postselection_sum
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (xs : Fin n → X) (ys : Fin n → Y) :
    (∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys)) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if ∀ i : {i : Fin n // i ∈ D},
          G.predicate (xs i) (ys i) (aa i) (bb i) = true
        then S.outcomeProbability xs ys aa bb else 0 := by
  classical
  simp_rw [conditionedEffects_born_expansion G n S D]
  calc
    (∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullQuestionWinIndicator G D xs ys α β *
          (∑ aa : Fin n → A, ∑ bb : Fin n → B,
            if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
              if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
                S.outcomeProbability xs ys aa bb else 0
            else 0)) =
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        fullQuestionWinIndicator G D xs ys α β *
          (if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
            if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
              S.outcomeProbability xs ys aa bb else 0
          else 0) := by
            simp only [Finset.mul_sum]
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullQuestionWinIndicator G D xs ys α β *
          (if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
            if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
              S.outcomeProbability xs ys aa bb else 0
          else 0) := finite_sum_four_swap _
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if ∀ i : {i : Fin n // i ∈ D},
          G.predicate (xs i) (ys i) (aa i) (bb i) = true
        then S.outcomeProbability xs ys aa bb else 0 := by
      apply Finset.sum_congr rfl
      intro aa _
      apply Finset.sum_congr rfl
      intro bb _
      simp [conditionedAnswerMatches_iff,
        fullQuestionWinIndicator, mul_ite]

theorem repeated_partialWinMass_expansion
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        (G.repeat n).questionWeight xs ys *
          (if ∀ i : {i : Fin n // i ∈ D},
            G.predicate (xs i) (ys i) (aa i) (bb i) = true
          then S.outcomeProbability xs ys aa bb else 0) := by
  classical
  unfold FiniteEventLaw.eventMass FiniteEventLaw.winEvent
  simp only [Finset.sum_filter]
  simp only [repeatedCoordinateWin, strategyEventLaw]
  change
    (∑ ω : (Fin n → X) × (Fin n → Y) ×
      (Fin n → A) × (Fin n → B),
      if ∀ i ∈ D,
        G.predicate (ω.1 i) (ω.2.1 i)
          (ω.2.2.1 i) (ω.2.2.2 i) = true
      then (G.repeat n).questionWeight ω.1 ω.2.1 *
        S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
      else 0) = _
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  apply Finset.sum_congr rfl
  intro aa _
  apply Finset.sum_congr rfl
  intro bb _
  have hiff :
      (∀ i ∈ D, G.predicate (xs i) (ys i) (aa i) (bb i) = true) ↔
        (∀ i : {i : Fin n // i ∈ D},
          G.predicate (xs i) (ys i) (aa i) (bb i) = true) := by
    constructor
    · intro h i
      exact h i i.property
    · intro h i hi
      exact h ⟨i, hi⟩
  by_cases hw : ∀ i : {i : Fin n // i ∈ D},
    G.predicate (xs i) (ys i) (aa i) (bb i) = true
  · rw [if_pos (hiff.mpr hw), if_pos hw]
  · rw [if_neg (mt hiff.mp hw), if_neg hw, mul_zero]

theorem fullQuestionConditionedBornMass_eq
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight xs ys *
          fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys)) =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) := by
  classical
  calc
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight xs ys *
          fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys)) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        (G.repeat n).questionWeight xs ys *
          (∑ α : {i : Fin n // i ∈ D} → A,
            ∑ β : {i : Fin n // i ∈ D} → B,
              fullQuestionWinIndicator G D xs ys α β *
                bornTracePairing S.state.matrix
                  (conditionedAliceEffect G n S D α xs)
                  (conditionedBobEffect G n S D β ys)) := by
        apply Finset.sum_congr rfl
        intro xs _
        apply Finset.sum_congr rfl
        intro ys _
        simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        (G.repeat n).questionWeight xs ys *
          (if ∀ i : {i : Fin n // i ∈ D},
            G.predicate (xs i) (ys i) (aa i) (bb i) = true
          then S.outcomeProbability xs ys aa bb else 0) := by
        apply Finset.sum_congr rfl
        intro xs _
        apply Finset.sum_congr rfl
        intro ys _
        rw [conditionedEffects_postselection_sum G n S D xs ys]
        simp only [Finset.mul_sum]
    _ = _ := (repeated_partialWinMass_expansion G n S D).symm

theorem fullHistoryFilters_born_expansion
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    bornTracePairing S.state.matrix
        (fullHistoryAliceFilter G n S D L h α)
        (fullHistoryBobFilter G n S D L h β) =
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
        fullHistoryHiddenAliceWeight G h hx *
          fullHistoryHiddenBobWeight G h hy *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α
              (fullHistoryAliceQuestion h hx))
            (conditionedBobEffect G n S D β
              (fullHistoryBobQuestion h hy)) := by
  classical
  unfold fullHistoryAliceFilter fullHistoryBobFilter
  simp only [map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro hx _
  apply Finset.sum_congr rfl
  intro hy _
  ring

theorem fullSubsetHistory_mass_eq_postselection
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          bornTracePairing S.state.matrix
            (fullHistoryAliceFilter G n S D L h α)
            (fullHistoryBobFilter G n S D L h β)) =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          bornTracePairing S.state.matrix
            (fullHistoryAliceFilter G n S D L h α)
            (fullHistoryBobFilter G n S D L h β)) =
      ∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          fullHistoryHiddenAliceWeight G h hx *
          fullHistoryHiddenBobWeight G h hy *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α
              (fullHistoryAliceQuestion h hx))
            (conditionedBobEffect G n S D β
              (fullHistoryBobQuestion h hy)) := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        rw [fullHistoryFilters_born_expansion G n S D L h α β]
        simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ h : FullSubsetHistory X Y n D L,
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          fullHistoryHiddenAliceWeight G h hx *
          fullHistoryHiddenBobWeight G h hy *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α
              (fullHistoryAliceQuestion h hx))
            (conditionedBobEffect G n S D β
              (fullHistoryBobQuestion h hy)) := by
        apply Finset.sum_congr rfl
        intro h _
        exact finite_sum_four_swap _
    _ = ∑ h : FullSubsetHistory X Y n D L,
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight
          (fullHistoryAliceQuestion h hx)
          (fullHistoryBobQuestion h hy) *
        fullQuestionWinIndicator G D
          (fullHistoryAliceQuestion h hx)
          (fullHistoryBobQuestion h hy) α β *
        bornTracePairing S.state.matrix
          (conditionedAliceEffect G n S D α
            (fullHistoryAliceQuestion h hx))
          (conditionedBobEffect G n S D β
            (fullHistoryBobQuestion h hy)) := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro hx _
        apply Finset.sum_congr rfl
        intro hy _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        rw [fullHistoryWinIndicator_eq_question G D L h hx hy α β]
        rw [← fullHistoryWeight_mul_hidden G D L hL h hx hy]
        ring
    _ = ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight xs ys *
          fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys) := by
      let f : ((Fin n → X) × (Fin n → Y)) → ℝ := fun q =>
        ∑ α : {i : Fin n // i ∈ D} → A,
        ∑ β : {i : Fin n // i ∈ D} → B,
          (G.repeat n).questionWeight q.1 q.2 *
            fullQuestionWinIndicator G D q.1 q.2 α β *
            bornTracePairing S.state.matrix
              (conditionedAliceEffect G n S D α q.1)
              (conditionedBobEffect G n S D β q.2)
      simpa only [f, fullHistoryQuestionEquiv, Equiv.coe_fn_mk,
        Fintype.sum_prod_type] using
        (fullHistoryQuestionEquiv
          (X := X) (Y := Y) D L hL).sum_comp f
    _ = _ := fullQuestionConditionedBornMass_eq G n S D

end ActualHistoryWeights

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_mul_shift
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s *
        (F + s • (1 : Matrix d d ℂ)) = F := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (eigenvalue i : ℂ)
  let T : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U
  have heigenvalue (i : d) : 0 ≤ eigenvalue i :=
    hF.eigenvalues_nonneg i
  have hden (i : d) : eigenvalue i + s ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (heigenvalue i) hs)
  have hFspec : F = e D := by
    simpa [D, eigenvalue, e, Function.comp_def] using
      hF.isHermitian.spectral_theorem
  have hshift_inner :
      D + s • (1 : Matrix d d ℂ) =
        Matrix.diagonal fun i => ((eigenvalue i + s : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]
  have hproduct : T * (D + s • (1 : Matrix d d ℂ)) = D := by
    rw [hshift_inner]
    change
      Matrix.diagonal (fun i =>
        ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)) *
          Matrix.diagonal (fun i => ((eigenvalue i + s : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => (eigenvalue i : ℂ))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    push_cast
    have hden_complex :
        (eigenvalue i : ℂ) + (s : ℂ) ≠ 0 := by
      exact_mod_cast hden i
    rw [div_mul_cancel₀ _ hden_complex]
  have hscalar : e (s • (1 : Matrix d d ℂ)) =
      s • (1 : Matrix d d ℂ) := by
    change
      (U : Matrix d d ℂ) * (s • (1 : Matrix d d ℂ)) *
          star (U : Matrix d d ℂ) = s • (1 : Matrix d d ℂ)
    rw [mul_smul_comm, mul_one, smul_mul_assoc]
    simp
  change e T * (F + s • (1 : Matrix d d ℂ)) = F
  rw [hFspec, ← hscalar, ← map_add, ← map_mul, hproduct]

theorem spectralPurificationFilter_eq_resolvent
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s =
      F * (F + s • (1 : Matrix d d ℂ))⁻¹ := by
  have hdet : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  calc
    spectralPurificationFilter F hF s =
        spectralPurificationFilter F hF s *
          ((F + s • (1 : Matrix d d ℂ)) *
            (F + s • (1 : Matrix d d ℂ))⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, mul_one]
    _ = (spectralPurificationFilter F hF s *
          (F + s • (1 : Matrix d d ℂ))) *
          (F + s • (1 : Matrix d d ℂ))⁻¹ := by
          rw [mul_assoc]
    _ = F * (F + s • (1 : Matrix d d ℂ))⁻¹ := by
          rw [spectralPurificationFilter_mul_shift F hF hs]

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_square_contraction
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (spectralPurificationFilter F hF s -
      star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s).PosSemidef := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let D : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U
  have hDhermitian : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) = _
    simp
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hDhermitian.eq
  have hdiag : (D - D * D).PosSemidef := by
    rw [show D * D = Matrix.diagonal (fun i =>
      (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) by
        dsimp [D]
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        simp [pow_two]]
    have hsub : D - Matrix.diagonal (fun i =>
        (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) =
        Matrix.diagonal (fun i =>
          ((eigenvalue i / (eigenvalue i + s) -
            (eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D]
      · simp [D, hij]
    rw [hsub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ ((eigenvalue i / (eigenvalue i + s) -
      (eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)
    apply Complex.nonneg_iff.mpr
    constructor
    · have hnonneg : 0 ≤ eigenvalue i / (eigenvalue i + s) :=
        div_nonneg (hF.eigenvalues_nonneg i)
          (le_of_lt (add_pos_of_nonneg_of_pos
            (hF.eigenvalues_nonneg i) hs))
      have hle : eigenvalue i / (eigenvalue i + s) ≤ 1 :=
        (div_le_one (add_pos_of_nonneg_of_pos
          (hF.eigenvalues_nonneg i) hs)).mpr (by linarith)
      change 0 ≤ eigenvalue i / (eigenvalue i + s) -
        (eigenvalue i / (eigenvalue i + s)) ^ 2
      nlinarith
    · simp only [Complex.ofReal_im]
  change (e D - star (e D) * e D).PosSemidef
  rw [← map_star, hDstar, ← map_mul, ← map_sub]
  change ((U : Matrix d d ℂ) * (D - D * D) *
    star (U : Matrix d d ℂ)).PosSemidef
  simpa [Matrix.star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same (U : Matrix d d ℂ)

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def matrixQuadraticCLM
    {d : Type*} [Fintype d]
    (x : d → ℂ) : Matrix d d ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star x ⬝ᵥ A.mulVec x
      map_add' := by
        intro A B
        simp [Matrix.mulVec, dotProduct, add_mul, mul_add,
          Finset.sum_add_distrib]
      map_smul' := by
        intro r A
        change
          (∑ i, star (x i) *
            ∑ j, ((r : ℂ) * A i j) * x j) =
          (r : ℂ) *
            (∑ i, star (x i) * ∑ j, A i j * x j)
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring }

def matrixAdjointCLM
    {d : Type*} [Fintype d] :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star A
      map_add' := by
        intro A B
        exact star_add A B
      map_smul' := by
        intro r A
        simp }

theorem bochner_integral_posSemidef
    {α d : Type*} [MeasurableSpace α]
    [Fintype d] [DecidableEq d]
    {μ : Measure α} {f : α → Matrix d d ℂ}
    (hf : Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  have hadjoint :
      star (∫ t, f t ∂μ) = ∫ t, star (f t) ∂μ := by
    exact (ContinuousLinearMap.integral_comp_comm
      matrixAdjointCLM hf).symm
  have hadjoint_ae : (fun t => star (f t)) =ᵐ[μ] f := by
    filter_upwards [hpos] with t ht
    simpa only [Matrix.star_eq_conjTranspose] using ht.isHermitian.eq
  have hhermitian : (∫ t, f t ∂μ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have hstar : star (∫ t, f t ∂μ) = ∫ t, f t ∂μ :=
      hadjoint.trans (integral_congr_ae hadjoint_ae)
    have hentry := congr_fun (congr_fun hstar i) j
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose] using hentry
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hhermitian
  intro x
  have hcomm :
      (∫ t, matrixQuadraticCLM x (f t) ∂μ) =
        matrixQuadraticCLM x (∫ t, f t ∂μ) :=
    ContinuousLinearMap.integral_comp_comm
      (matrixQuadraticCLM x) hf
  change 0 ≤ matrixQuadraticCLM x (∫ t, f t ∂μ)
  rw [← hcomm]
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with t ht
  exact ht.dotProduct_mulVec_nonneg x

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_eq_one_sub_shifted_inverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s =
      1 - s • (F + s • (1 : Matrix d d ℂ))⁻¹ := by
  have hdet : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  rw [spectralPurificationFilter_eq_resolvent F hF hs]
  apply eq_sub_of_add_eq
  simpa [add_mul, smul_mul_assoc] using
    Matrix.mul_nonsing_inv
      (F + s • (1 : Matrix d d ℂ)) hdet

theorem shifted_inverse_square_contraction
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (s • (F + s • (1 : Matrix d d ℂ))⁻¹ -
      s ^ 2 •
        ((F + s • (1 : Matrix d d ℂ))⁻¹ *
          (F + s • (1 : Matrix d d ℂ))⁻¹)).PosSemidef := by
  let R : Matrix d d ℂ := (F + s • (1 : Matrix d d ℂ))⁻¹
  have hstar : star R = R := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hF hs).isHermitian.eq
  have h := spectralPurificationFilter_square_contraction F hF hs
  rw [spectralPurificationFilter_eq_one_sub_shifted_inverse F hF hs] at h
  change (s • R - s ^ 2 • (R * R)).PosSemidef
  change ((1 - s • R) - star (1 - s • R) *
    (1 - s • R)).PosSemidef at h
  convert h using 1
  simp only [star_sub, star_one, star_smul, star_trivial, hstar,
    sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, pow_two]
  module

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_sub_resolvent
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s =
      s • ((F + s • (1 : Matrix d d ℂ))⁻¹ *
        (F - M) * (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  have hdetF : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  have hdetM : IsUnit (M + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hM hs).isUnit
  rw [spectralPurificationFilter_eq_resolvent F hF hs,
    spectralPurificationFilter_eq_resolvent M hM hs]
  simpa [smul_mul_assoc] using
    noncommutative_filtered_resolvent_identity
      F M (s • (1 : Matrix d d ℂ))
      (F + s • (1 : Matrix d d ℂ))⁻¹
      (M + s • (1 : Matrix d d ℂ))⁻¹
      (Matrix.mul_nonsing_inv _ hdetF)
      (Matrix.nonsing_inv_mul _ hdetF)
      (Matrix.mul_nonsing_inv _ hdetM)

theorem spectralPurificationFilter_sub_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    star (spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s) *
      (spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s) =
      s ^ 2 •
        ((M + s • (1 : Matrix d d ℂ))⁻¹ * (F - M) *
          ((F + s • (1 : Matrix d d ℂ))⁻¹ *
            (F + s • (1 : Matrix d d ℂ))⁻¹) *
          (F - M) * (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  let RF : Matrix d d ℂ := (F + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ := (M + s • (1 : Matrix d d ℂ))⁻¹
  let D : Matrix d d ℂ := F - M
  have hRF : star RF = RF := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hF hs).isHermitian.eq
  have hRM : star RM = RM := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hM hs).isHermitian.eq
  have hD : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (hF.isHermitian.sub hM.isHermitian).eq
  rw [spectralPurificationFilter_sub_resolvent F M hF hM hs]
  change star (s • (RF * D * RM)) * (s • (RF * D * RM)) =
    s ^ 2 • (RM * D * (RF * RF) * D * RM)
  simp only [star_smul, star_trivial, star_mul, hRF, hRM, hD,
    smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
  congr 1
  noncomm_ring

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem weighted_shifted_inverse_second_order
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (∑ i : ι, weight i •
      (F i + s • (1 : Matrix d d ℂ))⁻¹) -
        (M + s • (1 : Matrix d d ℂ))⁻¹ =
      (M + s • (1 : Matrix d d ℂ))⁻¹ *
        (∑ i : ι, weight i •
          ((F i - M) * (F i + s • (1 : Matrix d d ℂ))⁻¹ *
            (F i - M))) *
        (M + s • (1 : Matrix d d ℂ))⁻¹ := by
  let W : ι → Matrix d d ℂ := fun i =>
    weight i • (1 : Matrix d d ℂ)
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  have hW_normalized : (∑ i : ι, W i) = 1 := by
    dsimp [W]
    rw [← Finset.sum_smul, normalized]
    simp
  have hW_centered : (∑ i : ι, W i * (F i - M)) = 0 := by
    dsimp [W]
    simp_rw [smul_mul_assoc, one_mul]
    exact matrix_weighted_centered weight F M normalized mean
  have hW_commutes (i : ι) : W i * RM = RM * W i := by
    dsimp [W]
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hdetF (i : ι) :
      IsUnit (F i + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef (positive i) hs).isUnit
  have hdetM : IsUnit (M + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hM hs).isUnit
  have hidentity := noncommutative_weighted_resolvent_second_order
    W F M (s • (1 : Matrix d d ℂ)) RF RM
    hW_normalized hW_centered hW_commutes
    (fun i => Matrix.mul_nonsing_inv _ (hdetF i))
    (fun i => Matrix.nonsing_inv_mul _ (hdetF i))
    (Matrix.mul_nonsing_inv _ hdetM)
    (Matrix.nonsing_inv_mul _ hdetM)
  simpa [W, RF, RM, smul_mul_assoc] using hidentity

theorem weighted_spectralPurificationFilter_variance_le_inverse_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    (s •
      ((∑ i : ι, weight i •
        (F i + s • (1 : Matrix d d ℂ))⁻¹) -
        (M + s • (1 : Matrix d d ℂ))⁻¹) -
      ∑ i : ι, weight i •
        (star (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s))).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  let D : ι → Matrix d d ℂ := fun i => F i - M
  let K : ι → Matrix d d ℂ := fun i =>
    s • RF i - s ^ 2 • (RF i * RF i)
  have hK (i : ι) : (K i).PosSemidef :=
    shifted_inverse_square_contraction (F i) (positive i) hs
  have hD (i : ι) : (D i).IsHermitian :=
    (positive i).isHermitian.sub hM.isHermitian
  have hinner :
      (∑ i : ι, weight i • (D i * K i * D i)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact (posSemidef_hermitian_sandwich (hK i) (hD i)).smul
      (nonnegative i)
  have hRM : RM.IsHermitian :=
    (shifted_posSemidef_matrix_inverse_posSemidef hM hs).isHermitian
  have houter :
      (RM * (∑ i : ι, weight i • (D i * K i * D i)) * RM).PosSemidef :=
    posSemidef_hermitian_sandwich hinner hRM
  have hsecond :
      (∑ i : ι, weight i • RF i) - RM =
        RM * (∑ i : ι, weight i • (D i * RF i * D i)) * RM :=
    weighted_shifted_inverse_second_order
      weight F M normalized mean positive hM hs
  have hgram (i : ι) :
      star (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) =
        s ^ 2 • (RM * D i * (RF i * RF i) * D i * RM) :=
    spectralPurificationFilter_sub_gram
      (F i) M (positive i) hM hs
  change
    (s • ((∑ i : ι, weight i • RF i) - RM) -
      ∑ i : ι, weight i •
        (star (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s))).PosSemidef
  rw [hsecond]
  simp_rw [hgram]
  convert houter using 1
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_sub, sub_mul, K]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_sub, smul_smul, smul_smul, mul_comm s (weight i)]
  simp only [mul_assoc]

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalarResolventFilter_memLp_two
    {z : ℝ} (hz : 0 ≤ z) :
    MemLp (fun s : ℝ => z / (z + s)) 2
      (volume.restrict (Ioi 0)) := by
  have hmeas :
      AEStronglyMeasurable (fun s : ℝ => z / (z + s))
        (volume.restrict (Ioi 0)) := by
    exact (measurable_const.div
      (measurable_const.add measurable_id)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hmeas).mpr
    (scalar_resolvent_purification_integrable hz)

theorem spectralPurificationFilter_memLp_two
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    MemLp (spectralPurificationFilter F hF) 2
      (volume.restrict (Ioi 0)) := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  have hform :
      (fun s : ℝ => spectralPurificationFilter F hF s i j) =
        (fun s : ℝ => ∑ k : d,
          (U : Matrix d d ℂ) i k *
            ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ) *
            star (U : Matrix d d ℂ) k j) := by
    funext s
    change
      ((U : Matrix d d ℂ) *
        Matrix.diagonal (fun k =>
          ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ)) *
        star (U : Matrix d d ℂ)) i j = _
    simp [Matrix.mul_apply, Matrix.diagonal, mul_ite]
  rw [hform]
  apply memLp_finsetSum Finset.univ
  intro k _
  exact ((scalarResolventFilter_memLp_two
    (hF.eigenvalues_nonneg k)).ofReal.const_mul
      ((U : Matrix d d ℂ) i k)).mul_const
        (star (U : Matrix d d ℂ) k j)

theorem matrix_memLp_two_mul_integrable
    {α d : Type*} [MeasurableSpace α]
    [Fintype d] {μ : Measure α}
    {f g : α → Matrix d d ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => f t * g t) μ := by
  classical
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  change Integrable (fun t => ∑ k : d, f t i k * g t k j) μ
  apply integrable_finsetSum Finset.univ
  intro k _
  exact ((hf.eval i).eval k).integrable_mul ((hg.eval k).eval j)

theorem spectralPurificationFilter_difference_gram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef) :
    IntegrableOn
      (fun s : ℝ =>
        star (spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s))
      (Ioi 0) := by
  have hdelta :
      MemLp (fun s : ℝ =>
        spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s) 2
        (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_memLp_two F hF).sub
      (spectralPurificationFilter_memLp_two M hM)
  exact matrix_memLp_two_mul_integrable hdelta.star hdelta

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalar_entropy_resolvent_integrable
    {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn
      (fun s : ℝ => z / (1 + s) - z / (z + s))
      (Ioi 0) := by
  have hone :
      MemLp (fun s : ℝ => 1 / (1 + s)) 2
        (volume.restrict (Ioi 0)) :=
    scalarResolventFilter_memLp_two (z := 1) (by norm_num)
  have hzfilter := scalarResolventFilter_memLp_two hz
  have hproduct :
      Integrable
        (fun s : ℝ =>
          (1 / (1 + s)) * (z / (z + s)))
        (volume.restrict (Ioi 0)) :=
    hone.integrable_mul hzfilter
  have hscaled :
      IntegrableOn
        (fun s : ℝ =>
          (z - 1) * ((1 / (1 + s)) * (z / (z + s))))
        (Ioi 0) := hproduct.const_mul (z - 1)
  refine hscaled.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hspos : 0 < s := hs
  have hzone : 1 + s ≠ 0 := ne_of_gt (by linarith)
  have hzden : z + s ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ; ring

def spectralEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i / (1 + s) -
        hF.isHermitian.eigenvalues i /
          (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

theorem spectralEntropyKernel_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn (spectralEntropyKernel F hF) (Ioi 0) := by
  classical
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag :
      IntegrableOn
        (fun s : ℝ => Matrix.diagonal fun i : d =>
          ((eigenvalue i / (1 + s) -
            eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
        (Ioi 0) := by
    apply Integrable.of_eval
    intro i
    apply Integrable.of_eval
    intro j
    by_cases hij : i = j
    · subst j
      have heigenvalue : 0 ≤ eigenvalue i :=
        hF.eigenvalues_nonneg i
      have hcomplex :
          Integrable
            (fun s : ℝ =>
              ((eigenvalue i / (1 + s) -
                eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
            (volume.restrict (Ioi 0)) :=
        MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
          (scalar_entropy_resolvent_integrable heigenvalue)
      simpa only [Matrix.diagonal_apply_eq] using hcomplex
    · simp [hij]
  exact
    (spectralConjugationCLM hF.isHermitian.eigenvectorUnitary).integrable_comp
      hdiag

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralEntropyKernel_eq_scalar_sub_filter
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    spectralEntropyKernel F hF s =
      (1 / (1 + s) : ℝ) • F -
        spectralPurificationFilter F hF s := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let L := spectralConjugationCLM U
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (eigenvalue i : ℂ)
  let G : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let K : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (1 + s) -
      eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  have hFspec : F = L D := by
    simpa [L, U, D, eigenvalue, Function.comp_def,
      Unitary.conjStarAlgAut_apply] using
      hF.isHermitian.spectral_theorem
  have hdiag : K = (1 / (1 + s) : ℝ) • D - G := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [K, D, G, div_eq_mul_inv, mul_comm]
    · simp [K, D, G, hij]
  change L K = (1 / (1 + s) : ℝ) • F - L G
  rw [hFspec, ← L.map_smul, ← L.map_sub, hdiag]

def weightedSpectralFilterVariance
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  ∑ i : ι, weight i •
    (star (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s) *
      (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s))

def weightedSpectralEntropyJensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  (∑ i : ι, weight i • spectralEntropyKernel (F i) (positive i) s) -
    spectralEntropyKernel M hM s

theorem weightedSpectralFilterVariance_integrable
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    IntegrableOn
      (weightedSpectralFilterVariance weight F M positive hM)
      (Ioi 0) := by
  unfold weightedSpectralFilterVariance
  apply integrable_finsetSum Finset.univ
  intro i _
  exact (spectralPurificationFilter_difference_gram_integrable
    (F i) M (positive i) hM).smul (weight i)

theorem weightedSpectralEntropyJensen_integrable
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    IntegrableOn
      (weightedSpectralEntropyJensen weight F M positive hM)
      (Ioi 0) := by
  unfold weightedSpectralEntropyJensen
  apply Integrable.sub
  · apply integrable_finsetSum Finset.univ
    intro i _
    exact (spectralEntropyKernel_integrable
      (F i) (positive i)).smul (weight i)
  · exact spectralEntropyKernel_integrable M hM

theorem weightedSpectralEntropyJensen_eq_shifted_inverse
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    {s : ℝ} (hs : 0 < s) :
    weightedSpectralEntropyJensen weight F M positive hM s =
      s •
        ((∑ i : ι, weight i •
          (F i + s • (1 : Matrix d d ℂ))⁻¹) -
          (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  classical
  let c : ℝ := 1 / (1 + s)
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  have hscalar :
      (∑ i : ι, weight i • (c • F i)) = c • M := by
    calc
      (∑ i : ι, weight i • (c • F i)) =
          ∑ i : ι, c • (weight i • F i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [smul_smul, mul_comm]
      _ = c • (∑ i : ι, weight i • F i) := by
            rw [Finset.smul_sum]
      _ = c • M := by rw [mean]
  have hscale :
      (∑ i : ι, weight i • (s • RF i)) =
        s • (∑ i : ι, weight i • RF i) := by
    calc
      (∑ i : ι, weight i • (s • RF i)) =
          ∑ i : ι, s • (weight i • RF i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [smul_smul, mul_comm]
      _ = s • (∑ i : ι, weight i • RF i) := by
            rw [Finset.smul_sum]
  have hfilter_sum :
      (∑ i : ι, weight i •
        spectralPurificationFilter (F i) (positive i) s) =
      1 - s • (∑ i : ι, weight i • RF i) := by
    calc
      (∑ i : ι, weight i •
          spectralPurificationFilter (F i) (positive i) s) =
          ∑ i : ι, weight i • (1 - s • RF i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [spectralPurificationFilter_eq_one_sub_shifted_inverse
              (F i) (positive i) hs]
      _ = 1 - s • (∑ i : ι, weight i • RF i) := by
            simp_rw [smul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_smul,
              normalized, hscale]
            simp
  unfold weightedSpectralEntropyJensen
  simp_rw [spectralEntropyKernel_eq_scalar_sub_filter]
  change
    (∑ i : ι, weight i •
      (c • F i - spectralPurificationFilter (F i) (positive i) s)) -
      (c • M - spectralPurificationFilter M hM s) =
    s • ((∑ i : ι, weight i • RF i) - RM)
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, hscalar, hfilter_sum,
    spectralPurificationFilter_eq_one_sub_shifted_inverse M hM hs]
  module

theorem integrated_weighted_spectralPurificationFilter_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∫ s in Ioi (0 : ℝ),
        weightedSpectralEntropyJensen weight F M positive hM s) -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have hentropy := weightedSpectralEntropyJensen_integrable
    weight F M positive hM
  have hvariance := weightedSpectralFilterVariance_integrable
    weight F M positive hM
  have hremainder :
      Integrable
        (fun s : ℝ =>
          weightedSpectralEntropyJensen weight F M positive hM s -
            weightedSpectralFilterVariance weight F M positive hM s)
        (volume.restrict (Ioi 0)) :=
    hentropy.sub hvariance
  have hpointwise :
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        (weightedSpectralEntropyJensen weight F M positive hM s -
          weightedSpectralFilterVariance weight F M positive hM s).PosSemidef := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := hs
    rw [weightedSpectralEntropyJensen_eq_shifted_inverse
      weight F M positive hM normalized mean hspos]
    unfold weightedSpectralFilterVariance
    exact weighted_spectralPurificationFilter_variance_le_inverse_jensen
      weight F M nonnegative normalized mean positive hspos
  have hintegral := bochner_integral_posSemidef hremainder hpointwise
  rw [integral_sub hentropy hvariance] at hintegral
  exact hintegral

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalar_entropy_resolvent_integral
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ s in Ioi (0 : ℝ),
      (z / (1 + s) - z / (z + s))) = z * Real.log z := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp
  · have hderiv :
        ∀ x ∈ Ici (0 : ℝ),
          HasDerivAt
            (fun t : ℝ => z * Real.log ((1 + t) / (z + t)))
            (z / (1 + x) - z / (z + x)) x := by
      intro x hx
      have hxnonneg : 0 ≤ x := hx
      have hnum : 1 + x ≠ 0 := ne_of_gt (by linarith)
      have hden : z + x ≠ 0 := ne_of_gt (by linarith)
      have hratio : (1 + x) / (z + x) ≠ 0 :=
        div_ne_zero hnum hden
      have hdnum :=
        (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
      have hdden :=
        (hasDerivAt_const x z).add (hasDerivAt_id x)
      have hd :
          HasDerivAt
            (fun t : ℝ => z * Real.log ((1 + t) / (z + t)))
            (z * (((z + x) - (1 + x)) / (z + x) ^ 2 /
              ((1 + x) / (z + x)))) x := by
        simpa [Function.comp_def] using
          ((hdnum.div hdden hden).log hratio).const_mul z
      apply hd.congr_deriv
      field_simp [hnum, hden]
    have hden_top : Tendsto (fun t : ℝ => z + t) atTop atTop := by
      simpa [add_comm] using
        tendsto_atTop_add_const_right atTop z tendsto_id
    have hzero :
        Tendsto (fun t : ℝ => (1 - z) / (z + t))
          atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop hden_top
    have hratio_limit :
        Tendsto (fun t : ℝ => (1 + t) / (z + t))
          atTop (𝓝 (1 : ℝ)) := by
      have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
          atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
      have h' :
          Tendsto (fun t : ℝ => 1 + (1 - z) / (z + t))
            atTop (𝓝 (1 : ℝ)) := by
        simpa using hone.add hzero
      apply h'.congr'
      filter_upwards [eventually_gt_atTop (-z)] with t ht
      have hden : z + t ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ; ring
    have hlog_limit :
        Tendsto (fun t : ℝ =>
          Real.log ((1 + t) / (z + t)))
          atTop (𝓝 (0 : ℝ)) := by
      have hlog :
          Tendsto
            (Real.log ∘ (fun t : ℝ => (1 + t) / (z + t)))
            atTop (𝓝 (Real.log (1 : ℝ))) :=
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
          hratio_limit
      change
        Tendsto (fun t : ℝ => Real.log ((1 + t) / (z + t)))
          atTop (𝓝 (Real.log (1 : ℝ))) at hlog
      simpa only [Real.log_one] using hlog
    have hlimit :
        Tendsto (fun t : ℝ =>
          z * Real.log ((1 + t) / (z + t)))
          atTop (𝓝 (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hlog_limit
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv (scalar_entropy_resolvent_integrable hzpos.le) hlimit
    calc
      (∫ s in Ioi (0 : ℝ),
        (z / (1 + s) - z / (z + s))) =
          0 - z * Real.log ((1 + 0) / (z + 0)) := hftc
      _ = z * Real.log z := by
        simp [Real.log_inv]

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def diagonalEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    ((eigenvalue i / (1 + s) -
      eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)

theorem diagonalEntropyKernel_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (nonnegative : ∀ i, 0 ≤ eigenvalue i) :
    IntegrableOn (diagonalEntropyKernel eigenvalue) (Ioi 0) := by
  classical
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  by_cases hij : i = j
  · subst j
    have hcomplex :
        Integrable
          (fun s : ℝ =>
            ((eigenvalue i / (1 + s) -
              eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
          (volume.restrict (Ioi 0)) :=
      MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
        (scalar_entropy_resolvent_integrable (nonnegative i))
    simpa only [diagonalEntropyKernel,
      Matrix.diagonal_apply_eq] using hcomplex
  · simp [diagonalEntropyKernel, hij]

theorem integral_diagonalEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (nonnegative : ∀ i, 0 ≤ eigenvalue i) :
    (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s) =
      Matrix.diagonal fun i =>
        ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ) := by
  classical
  have hmatrix := diagonalEntropyKernel_integrable
    eigenvalue nonnegative
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ => diagonalEntropyKernel eigenvalue s i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  have hentry (i : d) :
      ∀ j : d,
        Integrable
          (fun s : ℝ => diagonalEntropyKernel eigenvalue s i j)
          (volume.restrict (Ioi 0)) :=
    fun j => (hrows i).eval j
  ext i j
  rw [MeasureTheory.eval_integral hrows i,
    MeasureTheory.eval_integral (hentry i) j]
  by_cases hij : i = j
  · subst j
    simp only [diagonalEntropyKernel, Matrix.diagonal_apply_eq]
    calc
      (∫ s in Ioi (0 : ℝ),
        ((eigenvalue i / (1 + s) -
          eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)) =
          ((∫ s in Ioi (0 : ℝ),
            eigenvalue i / (1 + s) -
              eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) :=
            integral_ofReal
      _ = ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ) := by
            rw [scalar_entropy_resolvent_integral (nonnegative i)]
  · simp [diagonalEntropyKernel, hij]

theorem integral_spectralEntropyKernel_eq_cfc
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ), spectralEntropyKernel F hF s) =
      cfc (fun z : ℝ => z * Real.log z) F := by
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag := diagonalEntropyKernel_integrable
    eigenvalue (fun i => hF.eigenvalues_nonneg i)
  calc
    (∫ s in Ioi (0 : ℝ), spectralEntropyKernel F hF s) =
        spectralConjugationCLM U
          (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s) := by
            exact ContinuousLinearMap.integral_comp_comm
              (spectralConjugationCLM U) hdiag
    _ = spectralConjugationCLM U
          (Matrix.diagonal fun i =>
            ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ)) := by
            rw [integral_diagonalEntropyKernel eigenvalue
              (fun i => hF.eigenvalues_nonneg i)]
    _ = cfc (fun z : ℝ => z * Real.log z) F := by
          rw [hF.isHermitian.cfc_eq]
          rfl

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_weightedSpectralEntropyJensen_eq_cfc
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    (∫ s in Ioi (0 : ℝ),
      weightedSpectralEntropyJensen weight F M positive hM s) =
      (∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
        cfc (fun z : ℝ => z * Real.log z) M := by
  have hterm (i : ι) :
      Integrable
        (fun s : ℝ => weight i •
          spectralEntropyKernel (F i) (positive i) s)
        (volume.restrict (Ioi 0)) :=
    (spectralEntropyKernel_integrable (F i) (positive i)).smul
      (weight i)
  have hsum :
      Integrable
        (fun s : ℝ => ∑ i : ι, weight i •
          spectralEntropyKernel (F i) (positive i) s)
        (volume.restrict (Ioi 0)) :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  have hmean := spectralEntropyKernel_integrable M hM
  unfold weightedSpectralEntropyJensen
  rw [integral_sub hsum hmean]
  rw [integral_finsetSum Finset.univ (fun i _ => hterm i)]
  simp_rw [integral_smul, integral_spectralEntropyKernel_eq_cfc]

theorem exact_matrix_log_entropy_filter_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have h := integrated_weighted_spectralPurificationFilter_jensen
    weight F M nonnegative normalized mean positive
  change
    ((∫ s in Ioi (0 : ℝ),
        weightedSpectralEntropyJensen weight F M positive hM s) -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef at h
  rw [integral_weightedSpectralEntropyJensen_eq_cfc
    weight F M positive hM] at h
  exact h

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section HistoryContractions

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem Game.conditionalYGivenX_sum_le_one
    (G : Game X Y A B) (x : X) :
    (∑ y : Y, G.conditionalYGivenX x y) ≤ 1 := by
  by_cases hx : G.marginalX x = 0
  · simp [Game.conditionalYGivenX, hx]
  · have hpos : 0 < G.marginalX x :=
      lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx)
    rw [G.conditionalYGivenX_sum x hpos]

theorem Game.conditionalXGivenY_sum_le_one
    (G : Game X Y A B) (y : Y) :
    (∑ x : X, G.conditionalXGivenY y x) ≤ 1 := by
  by_cases hy : G.marginalY y = 0
  · simp [Game.conditionalXGivenY, hy]
  · have hpos : 0 < G.marginalY y :=
      lt_of_le_of_ne (G.marginalY_nonneg y) (Ne.symm hy)
    rw [G.conditionalXGivenY_sum y hpos]

theorem fullHistoryHiddenAliceWeight_sum_le_one
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) :
    (∑ hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      fullHistoryHiddenAliceWeight G h hidden) ≤ 1 := by
  unfold fullHistoryHiddenAliceWeight
  rw [← Fintype.prod_sum]
  -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one₀` is the version with the
  -- nonnegativity hypothesis. See README.md.
  apply Finset.prod_le_one₀
  · intro i _
    exact Finset.sum_nonneg fun x _ =>
      G.conditionalXGivenY_nonneg (h.bobRemaining i) x
  · intro i _
    exact G.conditionalXGivenY_sum_le_one (h.bobRemaining i)

theorem fullHistoryHiddenBobWeight_sum_le_one
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) :
    (∑ hidden : {i : Fin n // i ∈ L} → Y,
      fullHistoryHiddenBobWeight G h hidden) ≤ 1 := by
  unfold fullHistoryHiddenBobWeight
  rw [← Fintype.prod_sum]
  -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one₀` is the version with the
  -- nonnegativity hypothesis. See README.md.
  apply Finset.prod_le_one₀
  · intro i _
    exact Finset.sum_nonneg fun y _ =>
      G.conditionalYGivenX_nonneg (h.aliceRevealed i) y
  · intro i _
    exact G.conditionalYGivenX_sum_le_one (h.aliceRevealed i)

theorem fullHistoryAliceFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    (1 - fullHistoryAliceFilter G n S D L h α).PosSemidef := by
  classical
  let w : ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) → ℝ :=
    fullHistoryHiddenAliceWeight G h
  let E : ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) →
      Matrix S.Alice S.Alice ℂ := fun x =>
    conditionedAliceEffect G n S D α (fullHistoryAliceQuestion h x)
  have hsum : (∑ x, w x) ≤ 1 :=
    fullHistoryHiddenAliceWeight_sum_le_one G h
  have hsplit :
      1 - (∑ x, w x • E x) =
        (1 - (∑ x, w x)) • (1 : Matrix S.Alice S.Alice ℂ) +
          ∑ x, w x • (1 - E x) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  change (1 - ∑ x, w x • E x).PosSemidef
  rw [hsplit]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hsum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro x _
    exact (conditionedAliceEffect_complement_positive G n S D α
      (fullHistoryAliceQuestion h x)).smul
        (fullHistoryHiddenAliceWeight_nonneg G h x)

theorem fullHistoryBobFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    (1 - fullHistoryBobFilter G n S D L h β).PosSemidef := by
  classical
  let w : ({i : Fin n // i ∈ L} → Y) → ℝ :=
    fullHistoryHiddenBobWeight G h
  let E : ({i : Fin n // i ∈ L} → Y) → Matrix S.Bob S.Bob ℂ :=
    fun y => conditionedBobEffect G n S D β (fullHistoryBobQuestion h y)
  have hsum : (∑ y, w y) ≤ 1 :=
    fullHistoryHiddenBobWeight_sum_le_one G h
  have hsplit :
      1 - (∑ y, w y • E y) =
        (1 - (∑ y, w y)) • (1 : Matrix S.Bob S.Bob ℂ) +
          ∑ y, w y • (1 - E y) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  change (1 - ∑ y, w y • E y).PosSemidef
  rw [hsplit]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hsum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro y _
    exact (conditionedBobEffect_complement_positive G n S D β
      (fullHistoryBobQuestion h y)).smul
        (fullHistoryHiddenBobWeight_nonneg G h y)

theorem matrixLogEntropy_nonpos_of_contraction
    {d : Type*} [Fintype d] [DecidableEq d]
    {F : Matrix d d ℂ}
    (hF : F.PosSemidef)
    (hcomplement : (1 - F).PosSemidef) :
    (-(cfc (fun z : ℝ => z * Real.log z) F)).PosSemidef := by
  have hFle : F ≤ (1 : Matrix d d ℂ) :=
    Matrix.le_iff.mpr hcomplement
  have hupper : ∀ z ∈ spectrum ℝ F, z ≤ 1 :=
    (CFC.le_one_iff (R := ℝ) F hF.isHermitian).mp hFle
  have hlower : ∀ z ∈ spectrum ℝ F, 0 ≤ z := by
    intro z hz
    rw [hF.isHermitian.spectrum_real_eq_range_eigenvalues] at hz
    obtain ⟨i, rfl⟩ := hz
    exact hF.eigenvalues_nonneg i
  have hnonpos : cfc (fun z : ℝ => z * Real.log z) F ≤
      (0 : Matrix d d ℂ) := by
    apply cfc_nonpos
    intro z hz
    exact Real.mul_log_nonpos (hlower z hz) (hupper z hz)
  simpa using Matrix.le_iff.mp hnonpos

theorem matrixLogEntropy_born_nonpos_left
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ)
    (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (hG : G.PosSemidef) :
    bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G ≤ 0 := by
  have hneg := matrixLogEntropy_nonpos_of_contraction hF hFcomplement
  have hpair : 0 ≤ bornTracePairing ρ.matrix
      (-(cfc (fun z : ℝ => z * Real.log z) F)) G := by
    exact trace_mul_posSemidef_nonneg ρ.positive (hneg.kronecker hG)
  have hrewrite : bornTracePairing ρ.matrix
      (-(cfc (fun z : ℝ => z * Real.log z) F)) G =
      -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G := by
    simp
  rw [hrewrite] at hpair
  exact neg_nonneg.mp hpair

theorem matrixLogEntropy_born_nonpos_right
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ)
    (hF : F.PosSemidef)
    (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) ≤ 0 := by
  have hneg := matrixLogEntropy_nonpos_of_contraction hG hGcomplement
  have hpair : 0 ≤ bornTracePairing ρ.matrix F
      (-(cfc (fun z : ℝ => z * Real.log z) G)) := by
    exact trace_mul_posSemidef_nonneg ρ.positive (hF.kronecker hneg)
  have hrewrite : bornTracePairing ρ.matrix F
      (-(cfc (fun z : ℝ => z * Real.log z) G)) =
      -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) :=
    (bornTracePairing ρ.matrix F).map_neg _
  rw [hrewrite] at hpair
  exact neg_nonneg.mp hpair

def fullHistoryAliceEntropyPotential
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) : ℝ :=
  ∑ h : FullSubsetHistory X Y n D L,
    ∑ α : {i : Fin n // i ∈ D} → A,
    ∑ β : {i : Fin n // i ∈ D} → B,
      fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (fullHistoryAliceFilter G n S D L h α))
          (fullHistoryBobFilter G n S D L h β)

theorem fullHistoryAliceEntropyPotential_nonpos
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) :
    fullHistoryAliceEntropyPotential G n S D L ≤ 0 := by
  unfold fullHistoryAliceEntropyPotential
  apply Finset.sum_nonpos
  intro h _
  apply Finset.sum_nonpos
  intro α _
  apply Finset.sum_nonpos
  intro β _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (fullHistoryWeight_nonneg G h)
      (fullHistoryWinIndicator_nonneg G h α β)
  · exact matrixLogEntropy_born_nonpos_left S.state
      (fullHistoryAliceFilter G n S D L h α)
      (fullHistoryBobFilter G n S D L h β)
      (fullHistoryAliceFilter_posSemidef G n S D L h α)
      (fullHistoryAliceFilter_complement_posSemidef G n S D L h α)
      (fullHistoryBobFilter_posSemidef G n S D L h β)

end HistoryContractions

def positiveMatrixSpectralAtom
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℂ)))

theorem positiveMatrixSpectralAtom_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    (positiveMatrixSpectralAtom F hF i).PosSemidef := by
  classical
  have hdiag :
      (Matrix.diagonal (Pi.single i (1 : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  unfold positiveMatrixSpectralAtom
  rw [spectralConjugationCLM_apply]
  simpa [Matrix.star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same
      (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)

theorem positiveMatrixSpectralAtom_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∑ i : d, positiveMatrixSpectralAtom F hF i) = 1 := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  have hdiag :
      (∑ i : d, Matrix.diagonal (Pi.single i (1 : ℂ))) =
        (1 : Matrix d d ℂ) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [Matrix.sum_apply, Pi.single_apply]
    · simp [Matrix.sum_apply,         hjk]
  change
    (∑ i : d,
      spectralConjugationCLM U
        (Matrix.diagonal (Pi.single i (1 : ℂ)))) = 1
  rw [← map_sum, hdiag]
  simp [spectralConjugationCLM_apply]

theorem positiveMatrix_cfc_spectral_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) :
    cfc f F =
      ∑ i : d,
        f (hF.isHermitian.eigenvalues i) •
          positiveMatrixSpectralAtom F hF i := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag :
      (∑ i : d,
        f (eigenvalue i) •
          Matrix.diagonal (Pi.single i (1 : ℂ))) =
        Matrix.diagonal fun i => (f (eigenvalue i) : ℂ) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [Matrix.sum_apply, Pi.single_apply]
    · simp [Matrix.sum_apply,         hjk]
  calc
    cfc f F =
        spectralConjugationCLM U
          (Matrix.diagonal fun i => (f (eigenvalue i) : ℂ)) := by
      rw [hF.isHermitian.cfc_eq]
      rfl
    _ = spectralConjugationCLM U
          (∑ i : d,
            f (eigenvalue i) •
              Matrix.diagonal (Pi.single i (1 : ℂ))) := by
      rw [hdiag]
    _ = ∑ i : d,
        f (eigenvalue i) •
          positiveMatrixSpectralAtom F hF i := by
      simp [positiveMatrixSpectralAtom, U, eigenvalue]

def leftSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ)
    (i : dA) : ℝ :=
  bornTracePairing ρ.matrix
    (positiveMatrixSpectralAtom F hF i) G

theorem leftSpectralBornWeight_nonneg
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dA) :
    0 ≤ leftSpectralBornWeight ρ F hF G i := by
  exact trace_mul_posSemidef_nonneg ρ.positive
    ((positiveMatrixSpectralAtom_posSemidef F hF i).kronecker hG)

theorem leftSpectralBornWeight_sum
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    (∑ i : dA, leftSpectralBornWeight ρ F hF G i) =
      bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G := by
  unfold leftSpectralBornWeight
  calc
    (∑ i : dA,
      bornTracePairing ρ.matrix
        (positiveMatrixSpectralAtom F hF i) G) =
      bornTracePairing ρ.matrix
        (∑ i : dA, positiveMatrixSpectralAtom F hF i) G := by
          simp [map_sum, LinearMap.sum_apply]
    _ = bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G := by
      rw [positiveMatrixSpectralAtom_sum]

theorem leftSpectralBornWeight_moment
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    (∑ i : dA,
      leftSpectralBornWeight ρ F hF G i *
        hF.isHermitian.eigenvalues i) =
      bornTracePairing ρ.matrix F G := by
  have hspectral : F =
      ∑ i : dA,
        hF.isHermitian.eigenvalues i •
          positiveMatrixSpectralAtom F hF i := by
    calc
      F = cfc (fun z : ℝ => z) F :=
        (cfc_id' ℝ F hF.isHermitian).symm
      _ = _ := positiveMatrix_cfc_spectral_sum F hF (fun z : ℝ => z)
  have h := congrArg
    (fun H : Matrix dA dA ℂ => bornTracePairing ρ.matrix H G)
      hspectral
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at h
  calc
    (∑ i : dA,
      leftSpectralBornWeight ρ F hF G i *
        hF.isHermitian.eigenvalues i) =
      ∑ i : dA,
        hF.isHermitian.eigenvalues i *
          bornTracePairing ρ.matrix
            (positiveMatrixSpectralAtom F hF i) G := by
        apply Finset.sum_congr rfl
        intro i _
        unfold leftSpectralBornWeight
        ring
    _ = bornTracePairing ρ.matrix F G := h.symm

theorem leftSpectralBornWeight_entropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G =
      ∑ i : dA,
        leftSpectralBornWeight ρ F hF G i *
          (hF.isHermitian.eigenvalues i *
            Real.log (hF.isHermitian.eigenvalues i)) := by
  have hspectral := positiveMatrix_cfc_spectral_sum F hF
    (fun z : ℝ => z * Real.log z)
  have h := congrArg
    (fun H : Matrix dA dA ℂ => bornTracePairing ρ.matrix H G)
      hspectral
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at h
  calc
    bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G =
      ∑ i : dA,
        (hF.isHermitian.eigenvalues i *
          Real.log (hF.isHermitian.eigenvalues i)) *
          bornTracePairing ρ.matrix
            (positiveMatrixSpectralAtom F hF i) G := h
    _ = ∑ i : dA,
      leftSpectralBornWeight ρ F hF G i *
        (hF.isHermitian.eigenvalues i *
          Real.log (hF.isHermitian.eigenvalues i)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold leftSpectralBornWeight
      ring

theorem bornTracePairing_one_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB)) :
    bornTracePairing ρ.matrix
      (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) = 1 := by
  simp [bornTracePairing, ρ.trace_one]

theorem bornTracePairing_one_le_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (G : Matrix dB dB ℂ)
    (hGcomplement : (1 - G).PosSemidef) :
    bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G ≤ 1 := by
  have hpositive : 0 ≤ bornTracePairing ρ.matrix
      (1 : Matrix dA dA ℂ) (1 - G) :=
    trace_mul_posSemidef_nonneg ρ.positive
      (Matrix.PosSemidef.one.kronecker hGcomplement)
  have hdiff : bornTracePairing ρ.matrix
      (1 : Matrix dA dA ℂ) (1 - G) =
      bornTracePairing ρ.matrix
        (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) -
      bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G :=
    (bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ)).map_sub 1 G
  rw [hdiff, bornTracePairing_one_one] at hpositive
  linarith

theorem positiveContraction_eigenvalue_le_one
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (hcomplement : (1 - F).PosSemidef)
    (i : d) :
    hF.isHermitian.eigenvalues i ≤ 1 := by
  have hFle : F ≤ (1 : Matrix d d ℂ) :=
    Matrix.le_iff.mpr hcomplement
  have hspectrum : ∀ z ∈ spectrum ℝ F, z ≤ 1 :=
    (CFC.le_one_iff (R := ℝ) F hF.isHermitian).mp hFle
  exact hspectrum _ (hF.isHermitian.eigenvalues_mem_spectrum_real i)

theorem leftSpectralBornWeight_negEntropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G =
      ∑ i : dA,
        leftSpectralBornWeight ρ F hF G i *
          Real.negMulLog (hF.isHermitian.eigenvalues i) := by
  rw [leftSpectralBornWeight_entropy ρ F hF G,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Real.negMulLog]

theorem matrixLogEntropy_born_lower_bound_left
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) := by
  classical
  have hp_nonneg : 0 ≤ bornTracePairing ρ.matrix F G :=
    trace_mul_posSemidef_nonneg ρ.positive (hF.kronecker hG)
  have hmass_le :
      bornTracePairing ρ.matrix F G ≤
        bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G := by
    calc
      bornTracePairing ρ.matrix F G =
        ∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            hF.isHermitian.eigenvalues i :=
          (leftSpectralBornWeight_moment ρ F hF G).symm
      _ ≤ ∑ i : dA, leftSpectralBornWeight ρ F hF G i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right
          (leftSpectralBornWeight_nonneg ρ F hF G hG i)
          (positiveContraction_eigenvalue_le_one F hF hFcomplement i)
      _ = bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G :=
        leftSpectralBornWeight_sum ρ F hF G
  by_cases hp : bornTracePairing ρ.matrix F G = 0
  · have hzero :
        (∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            hF.isHermitian.eigenvalues i) = 0 := by
        rw [leftSpectralBornWeight_moment, hp]
    have hterm (i : dA) :
        leftSpectralBornWeight ρ F hF G i *
          hF.isHermitian.eigenvalues i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg
          (leftSpectralBornWeight_nonneg ρ F hF G hG j)
          (hF.eigenvalues_nonneg j))).mp hzero i (Finset.mem_univ i)
    have hentropy :
        (∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            Real.negMulLog (hF.isHermitian.eigenvalues i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases mul_eq_zero.mp (hterm i) with hw | he
      · simp [hw]
      · simp [he]
    calc
      -bornTracePairing ρ.matrix
          (cfc (fun z : ℝ => z * Real.log z) F) G =
        ∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            Real.negMulLog (hF.isHermitian.eigenvalues i) :=
          leftSpectralBornWeight_negEntropy ρ F hF G
      _ = 0 := hentropy
      _ ≤ Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [hp]
        simp
  · have hp_pos : 0 < bornTracePairing ρ.matrix F G :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hp)
    have hW_pos : 0 <
        bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G :=
      lt_of_lt_of_le hp_pos hmass_le
    have hscalar := finite_weighted_entropy_le_of_weight_bound
      (Finset.univ : Finset dA)
      (leftSpectralBornWeight ρ F hF G)
      hF.isHermitian.eigenvalues
      (W := bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G)
      (N := (1 : ℝ))
      (p := bornTracePairing ρ.matrix F G)
      (fun i _ => leftSpectralBornWeight_nonneg ρ F hF G hG i)
      (fun i _ => hF.eigenvalues_nonneg i)
      hW_pos hp_pos
      (leftSpectralBornWeight_sum ρ F hF G)
      (leftSpectralBornWeight_moment ρ F hF G)
      (bornTracePairing_one_le_one ρ G hGcomplement)
    calc
      -bornTracePairing ρ.matrix
          (cfc (fun z : ℝ => z * Real.log z) F) G =
        ∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            Real.negMulLog (hF.isHermitian.eigenvalues i) :=
        leftSpectralBornWeight_negEntropy ρ F hF G
      _ ≤ bornTracePairing ρ.matrix F G *
          Real.log (1 / bornTracePairing ρ.matrix F G) := hscalar
      _ = Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [one_div, Real.log_inv]
        simp [Real.negMulLog]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def rawEmbezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2 fun q : Fin n × Fin n =>
    if q.1 = q.2 then
      (↑((Real.sqrt ((q.1.val : ℝ) + 1))⁻¹) : ℂ)
    else
      0

theorem rawEmbezzlementState_ne_zero
    (n : ℕ) (hn : 0 < n) :
    rawEmbezzlementState n ≠ 0 := by
  intro h
  let j : Fin n := ⟨0, hn⟩
  have hj := congrArg
    (fun z : EuclideanSpace ℂ (Fin n × Fin n) => z (j, j)) h
  simp [rawEmbezzlementState, j] at hj

def harmonicNumber (n : ℕ) : ℝ :=
  ∑ j : Fin n, ((j.val : ℝ) + 1)⁻¹

theorem rawEmbezzlementState_norm_sq (n : ℕ) :
    ‖rawEmbezzlementState n‖ ^ 2 =
      harmonicNumber n := by
  classical
  have hamp (j : Fin n) :
      ‖(↑((Real.sqrt ((j.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2 =
        ((j.val : ℝ) + 1)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt (by positivity)]
  have hterm (i j : Fin n) :
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2 =
      if i = j then
        ‖(↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2
      else
        0 := by
    split_ifs <;> simp
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  unfold harmonicNumber
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : Fin n,
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2) = ((i.val : ℝ) + 1)⁻¹
  calc
    (∑ j : Fin n,
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2) =
        ‖(↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2 := by
          simp_rw [hterm]
          simp
    _ = ((i.val : ℝ) + 1)⁻¹ := hamp i

def embezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
    rawEmbezzlementState n

theorem embezzlementState_norm
    (n : ℕ) (hn : 0 < n) :
    ‖embezzlementState n‖ = 1 := by
  have hraw : ‖rawEmbezzlementState n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (rawEmbezzlementState_ne_zero n hn)
  rw [embezzlementState, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hraw]

theorem embezzlementState_apply
    (n : ℕ) (i j : Fin n) :
    embezzlementState n (i, j) =
      (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
        (if i = j then
          (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
        else
          0) := by
  rfl

abbrev BipartiteUnitVector (d : ℕ) :=
  {ξ : EuclideanSpace ℂ (Fin d × Fin d) // ‖ξ‖ = 1}

def spectralAtomOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) : ℝ :=
  (Matrix.trace
    (positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j)).re

theorem spectralAtomOverlap_nonneg
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) :
    0 ≤ spectralAtomOverlap F G hF hG i j := by
  exact trace_mul_posSemidef_nonneg
    (positiveMatrixSpectralAtom_posSemidef F hF i)
    (positiveMatrixSpectralAtom_posSemidef G hG j)

theorem spectralAtom_trace
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (i : d) :
    Matrix.trace (positiveMatrixSpectralAtom F hF i) = 1 := by
  classical
  unfold positiveMatrixSpectralAtom
  rw [spectralConjugationCLM_apply, Matrix.trace_mul_cycle,
    Matrix.UnitaryGroup.star_mul_self, one_mul,
    Matrix.trace_diagonal]
  simp [Pi.single_apply]

theorem spectralAtom_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (i j : d) :
    positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom F hF j =
        if i = j then positiveMatrixSpectralAtom F hF i else 0 := by
  classical
  let e := Unitary.conjStarAlgAut ℝ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  change
    e (Matrix.diagonal (Pi.single i (1 : ℂ))) *
      e (Matrix.diagonal (Pi.single j (1 : ℂ))) =
        if i = j then
          e (Matrix.diagonal (Pi.single i (1 : ℂ)))
        else
          0
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    ext k l
    simp only [Matrix.diagonal_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · simp only [hij, ite_false]
    rw [← map_mul, Matrix.diagonal_mul_diagonal, ← map_zero e]
    congr 1
    ext k l
    by_cases hik : k = i
    · subst k
      simp [Matrix.diagonal_apply, Pi.single_apply, hij]
    · simp [Matrix.diagonal_apply, Pi.single_apply, hik]

theorem spectralAtomSum_mul_self
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (s : Finset d) :
    (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) *
      (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) =
        ∑ i ∈ s, positiveMatrixSpectralAtom F hF i := by
  classical
  calc
    (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) *
        (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) =
      ∑ i ∈ s, ∑ j ∈ s,
        positiveMatrixSpectralAtom F hF i *
          positiveMatrixSpectralAtom F hF j := by
            simp only [Matrix.sum_mul, Matrix.mul_sum]
            rw [Finset.sum_comm]
    _ = ∑ i ∈ s, positiveMatrixSpectralAtom F hF i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [spectralAtom_mul, hi]

theorem rectangularMatrix_norm_sq
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d]
    (K : Matrix e d ℂ) (z : EuclideanSpace ℂ d) :
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * K)) z := by
  calc
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
        (inner ℂ (toLp 2 (K.mulVec (ofLp z)))
          (toLp 2 (K.mulVec (ofLp z)))).re :=
            norm_sq_eq_re_inner (𝕜 := ℂ)
              (toLp 2 (K.mulVec (ofLp z)))
    _ = (star (K.mulVec (ofLp z)) ⬝ᵥ
          K.mulVec (ofLp z)).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (K.mulVec (ofLp z) ⬝ᵥ
          star (K.mulVec (ofLp z))).re = _
      rw [dotProduct_comm]
    _ = (star (ofLp z) ⬝ᵥ
        (K.conjTranspose * K).mulVec (ofLp z)).re := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
            Matrix.mulVec_mulVec]
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * K)) z := by
      unfold quadraticExpectation
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (star (ofLp z) ⬝ᵥ
          (K.conjTranspose * K).mulVec (ofLp z)).re =
        ((K.conjTranspose * K).mulVec (ofLp z) ⬝ᵥ
          star (ofLp z)).re
      rw [dotProduct_comm]

def coherentBinaryJointOutcome
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM Bool d) (Q : POVM Bool e)
    (z : EuclideanSpace ℂ (d × e))
    (a b : Bool) : EuclideanSpace ℂ (d × e) :=
  toLp 2
    (((P.effect a ⊗ₖ Q.effect b)).mulVec (ofLp z))

theorem coherentBinaryJointOutcome_norm_sq
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM Bool d) (Q : POVM Bool e)
    (hP : ∀ c : Bool, P.effect c * P.effect c = P.effect c)
    (hQ : ∀ c : Bool, Q.effect c * Q.effect c = Q.effect c)
    (z : EuclideanSpace ℂ (d × e)) (hz : ‖z‖ = 1)
    (a b : Bool) :
    ‖coherentBinaryJointOutcome P Q z a b‖ ^ 2 =
      (Matrix.trace
        ((pureDensityMatrix z hz).matrix *
          (P.effect a ⊗ₖ Q.effect b))).re := by
  let K : Matrix (d × e) (d × e) ℂ :=
    P.effect a ⊗ₖ Q.effect b
  have hgram : K.conjTranspose * K = K := by
    dsimp [K]
    rw [Matrix.conjTranspose_kronecker,
      (P.positive a).isHermitian.eq,
      (Q.positive b).isHermitian.eq,
      ← Matrix.mul_kronecker_mul,
      hP a, hQ b]
  calc
    ‖coherentBinaryJointOutcome P Q z a b‖ ^ 2 =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d × e) (𝕜 := ℂ)
          (K.conjTranspose * K)) z :=
        rectangularMatrix_norm_sq K z
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM (n := d × e) (𝕜 := ℂ) K) z := by
      rw [hgram]
    _ = (Matrix.trace ((pureDensityMatrix z hz).matrix * K)).re :=
      (pureDensityMatrix_trace_mul z hz K).symm

def finiteTensorVector
    {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → EuclideanSpace ℂ d) :
    EuclideanSpace ℂ (ι → d) :=
  toLp 2 fun q : ι → d => ∏ i : ι, v i (q i)

theorem finiteTensorVector_norm_sq
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]
    (v : ι → EuclideanSpace ℂ d) :
    ‖finiteTensorVector v‖ ^ 2 =
      ∏ i : ι, ‖v i‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  change
    (∑ q : ι → d, ‖∏ i : ι, v i (q i)‖ ^ 2) =
      ∏ i : ι, ‖v i‖ ^ 2
  calc
    (∑ q : ι → d, ‖∏ i : ι, v i (q i)‖ ^ 2) =
        ∑ q : ι → d, ∏ i : ι, ‖v i (q i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_prod, ← Finset.prod_pow]
    _ = ∏ i : ι, ∑ a : d, ‖v i a‖ ^ 2 :=
      (Fintype.prod_sum
        (fun i : ι => fun a : d => ‖v i a‖ ^ 2)).symm
    _ = ∏ i : ι, ‖v i‖ ^ 2 := by
      apply Finset.prod_congr rfl
      intro i _
      exact (EuclideanSpace.norm_sq_eq (v i)).symm

theorem finiteTensorVector_norm
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]
    (v : ι → EuclideanSpace ℂ d)
    (hv : ∀ i, ‖v i‖ = 1) :
    ‖finiteTensorVector v‖ = 1 := by
  have hsquare := finiteTensorVector_norm_sq v
  simp_rw [hv, one_pow, Finset.prod_const_one] at hsquare
  nlinarith [norm_nonneg (finiteTensorVector v)]

theorem spectralAtomOverlap_sum_right
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i : d) :
    (∑ j : d, spectralAtomOverlap F G hF hG i j) = 1 := by
  classical
  calc
    (∑ j : d, spectralAtomOverlap F G hF hG i j) =
        (Matrix.trace
          (positiveMatrixSpectralAtom F hF i *
            (∑ j : d, positiveMatrixSpectralAtom G hG j))).re := by
              simp only [spectralAtomOverlap,
                Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    _ = (Matrix.trace (positiveMatrixSpectralAtom F hF i)).re := by
      rw [positiveMatrixSpectralAtom_sum]
      simp
    _ = 1 := by
      rw [spectralAtom_trace]
      rfl

theorem spectralAtomOverlap_sum_left
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (j : d) :
    (∑ i : d, spectralAtomOverlap F G hF hG i j) = 1 := by
  classical
  calc
    (∑ i : d, spectralAtomOverlap F G hF hG i j) =
        (Matrix.trace
          ((∑ i : d, positiveMatrixSpectralAtom F hF i) *
            positiveMatrixSpectralAtom G hG j)).re := by
              simp only [spectralAtomOverlap,
                Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    _ = (Matrix.trace (positiveMatrixSpectralAtom G hG j)).re := by
      rw [positiveMatrixSpectralAtom_sum]
      simp
    _ = 1 := by
      rw [spectralAtom_trace]
      rfl

theorem positiveDensity_eigenvalues_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (htrace : Matrix.trace F = 1) :
    (∑ i : d, hF.isHermitian.eigenvalues i) = 1 := by
  have hspectral := congrArg Complex.re
    hF.isHermitian.trace_eq_sum_eigenvalues
  simpa [htrace, Complex.re_sum] using hspectral.symm

theorem spectralAtomOverlap_schmidtMass_le_one
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (hFtrace : Matrix.trace F = 1)
    (hGtrace : Matrix.trace G = 1) :
    (∑ i : d, ∑ j : d,
      Real.sqrt (hF.isHermitian.eigenvalues i) *
        Real.sqrt (hG.isHermitian.eigenvalues j) *
          spectralAtomOverlap F G hF hG i j) ≤ 1 := by
  classical
  let w : d × d → ℝ := fun q =>
    spectralAtomOverlap F G hF hG q.1 q.2
  let f : d × d → ℝ := fun q =>
    Real.sqrt (hF.isHermitian.eigenvalues q.1)
  let g : d × d → ℝ := fun q =>
    Real.sqrt (hG.isHermitian.eigenvalues q.2)
  have hf : (∑ q : d × d, w q * f q ^ 2) = 1 := by
    dsimp [w, f]
    rw [Fintype.sum_prod_type]
    simp_rw [Real.sq_sqrt (hF.eigenvalues_nonneg _)]
    calc
      (∑ i : d, ∑ j : d,
        spectralAtomOverlap F G hF hG i j *
          hF.isHermitian.eigenvalues i) =
        ∑ i : d,
          hF.isHermitian.eigenvalues i *
            (∑ j : d,
              spectralAtomOverlap F G hF hG i j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ i : d, hF.isHermitian.eigenvalues i := by
        simp_rw [spectralAtomOverlap_sum_right,
          mul_one]
      _ = 1 := positiveDensity_eigenvalues_sum F hF hFtrace
  have hg : (∑ q : d × d, w q * g q ^ 2) = 1 := by
    dsimp [w, g]
    rw [Fintype.sum_prod_type]
    simp_rw [Real.sq_sqrt (hG.eigenvalues_nonneg _)]
    calc
      (∑ i : d, ∑ j : d,
        spectralAtomOverlap F G hF hG i j *
          hG.isHermitian.eigenvalues j) =
        ∑ j : d,
          hG.isHermitian.eigenvalues j *
            (∑ i : d,
              spectralAtomOverlap F G hF hG i j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = ∑ j : d, hG.isHermitian.eigenvalues j := by
        simp_rw [spectralAtomOverlap_sum_left,
          mul_one]
      _ = 1 := positiveDensity_eigenvalues_sum G hG hGtrace
  calc
    (∑ i : d, ∑ j : d,
      Real.sqrt (hF.isHermitian.eigenvalues i) *
        Real.sqrt (hG.isHermitian.eigenvalues j) *
          spectralAtomOverlap F G hF hG i j) =
      ∑ q : d × d, w q * f q * g q := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [w, f, g]
        ring
    _ ≤ Real.sqrt (∑ q : d × d, w q * f q ^ 2) *
        Real.sqrt (∑ q : d × d, w q * g q ^ 2) := by
          apply weighted_real_cauchy
          intro q
          exact spectralAtomOverlap_nonneg
            F G hF hG q.1 q.2
    _ = 1 := by rw [hf, hg]; norm_num

def binaryBornProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e)
    (a b : Bool) : ℝ :=
  (Matrix.trace
    (ρ.matrix * (P.effect a ⊗ₖ Q.effect b))).re

theorem binaryBornProbability_normalized
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) :
    (∑ a : Bool, ∑ b : Bool,
      binaryBornProbability ρ P Q a b) = 1 := by
  classical
  have hjoint :
      (∑ a : Bool, ∑ b : Bool, P.effect a ⊗ₖ Q.effect b) =
        (1 : Matrix (d × e) (d × e) ℂ) := by
    calc
      (∑ a : Bool, ∑ b : Bool, P.effect a ⊗ₖ Q.effect b) =
          (∑ a : Bool, P.effect a) ⊗ₖ
            (∑ b : Bool, Q.effect b) := by
              ext ⟨i, j⟩ ⟨k, l⟩
              simp only [Matrix.sum_apply,
                Matrix.kroneckerMap_apply]
              rw [Finset.sum_mul]
              simp_rw [Finset.mul_sum]
      _ = 1 := by
        rw [P.complete, Q.complete]
        exact Matrix.one_kronecker_one
  calc
    (∑ a : Bool, ∑ b : Bool,
      binaryBornProbability ρ P Q a b) =
        (Matrix.trace
          (ρ.matrix *
            (∑ a : Bool, ∑ b : Bool,
              P.effect a ⊗ₖ Q.effect b))).re := by
          simp only [Fintype.sum_bool,
            binaryBornProbability, Matrix.mul_add,
            Matrix.trace_add, Complex.add_re]
    _ = (Matrix.trace ρ.matrix).re := by
      rw [hjoint]
      simp
    _ = 1 := by
      rw [ρ.trace_one]
      rfl

def binaryContinueProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q false false

def binaryJointSuccessProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true true

def binaryMismatchProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true false +
    binaryBornProbability ρ P Q false true

theorem binaryStoppingPartition
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) :
    binaryContinueProbability ρ P Q +
      binaryJointSuccessProbability ρ P Q +
        binaryMismatchProbability ρ P Q = 1 := by
  have hnormalized := binaryBornProbability_normalized ρ P Q
  simp only [Fintype.sum_bool] at hnormalized
  unfold binaryContinueProbability
    binaryJointSuccessProbability
    binaryMismatchProbability
  linarith

theorem unitVector_distance_of_real_overlap
    {ι : Type*} [Fintype ι]
    (z w : EuclideanSpace ℂ ι)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hoverlap : 1 - ε ≤ (inner ℂ z w).re) :
    ‖z - w‖ ≤ Real.sqrt (2 * ε) := by
  have hoverlap' : 1 - ε ≤ RCLike.re (inner ℂ z w) := by
    exact hoverlap
  have hsq : ‖z - w‖ ^ 2 ≤ 2 * ε := by
    rw [@norm_sub_sq ℂ, hz, hw]
    nlinarith [hoverlap']
  have hsqrt : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε :=
    Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg (z - w), Real.sqrt_nonneg (2 * ε)]

def sharedThresholdResourceRaw
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  toLp 2 fun q : (Σ _ : κ, d) × (Σ _ : κ, d) =>
    if q.1.1 = q.2.1 ∧ q.1.2 = q.2.2 then
      (τ q.1.1 : ℂ)
    else
      0

theorem sharedThresholdResourceRaw_norm_sq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    ‖sharedThresholdResourceRaw (d := d) τ‖ ^ 2 =
      (Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2 := by
  classical
  have hterm (k l : κ) (i j : d) :
      ‖if k = l ∧ i = j then (τ k : ℂ) else 0‖ ^ 2 =
        if k = l then if i = j then τ k ^ 2 else 0 else 0 := by
    split_ifs <;>
      simp_all [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sigma]
  change
    (∑ k : κ, ∑ i : d, ∑ l : κ, ∑ j : d,
      ‖if k = l ∧ i = j then (τ k : ℂ) else 0‖ ^ 2) =
        (Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2
  simp_rw [hterm]
  simp [Finset.mul_sum]

theorem sharedThresholdResourceRaw_ne_zero
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    sharedThresholdResourceRaw (d := d) τ ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun z : EuclideanSpace ℂ
        ((Σ _ : κ, d) × (Σ _ : κ, d)) =>
      z (⟨k, i⟩, ⟨k, i⟩)) hzero
  have hcast : (τ k : ℂ) = 0 := by
    simpa [sharedThresholdResourceRaw] using hentry
  exact hk (by exact_mod_cast hcast)

def sharedThresholdResource
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  (‖sharedThresholdResourceRaw (d := d) τ‖⁻¹ : ℝ) •
    sharedThresholdResourceRaw (d := d) τ

theorem sharedThresholdResource_norm
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    ‖sharedThresholdResource (d := d) τ‖ = 1 := by
  have hnorm : ‖sharedThresholdResourceRaw (d := d) τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (sharedThresholdResourceRaw_ne_zero τ k i hk)
  rw [sharedThresholdResource, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hnorm]

def transposePOVM
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (P : POVM ι d) : POVM ι d where
  effect b := (P.effect b).transpose
  positive b := (P.positive b).transpose
  complete := by
    classical
    ext i j
    have hc := congrArg
      (fun M : Matrix d d ℂ => M j i) P.complete
    simpa [Matrix.sum_apply, Matrix.transpose_apply,
      Matrix.one_apply, eq_comm] using hc

theorem transposePOVM_projective
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (P : POVM ι d)
    (hP : ∀ b : ι, P.effect b * P.effect b = P.effect b)
    (b : ι) :
    (transposePOVM P).effect b *
      (transposePOVM P).effect b =
        (transposePOVM P).effect b := by
  change
    (P.effect b).transpose * (P.effect b).transpose =
      (P.effect b).transpose
  rw [← Matrix.transpose_mul, hP b]

theorem sharedThresholdResourceRaw_eq_vec
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    sharedThresholdResourceRaw (d := d) τ =
      toLp 2 (Matrix.vec
        (Matrix.diagonal (fun q : Σ _ : κ, d => (τ q.1 : ℂ)))) := by
  ext ⟨⟨k, i⟩, ⟨l, j⟩⟩
  by_cases h : k = l
  · subst l
    by_cases hij : i = j
    · subst j
      simp [sharedThresholdResourceRaw, Matrix.vec]
    · simp [sharedThresholdResourceRaw,
        Matrix.vec, hij, Ne.symm hij]
  · simp [sharedThresholdResourceRaw,
      Matrix.vec, h, Ne.symm h]

theorem sharedThresholdResourceRaw_local_action
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ)
    (A B : Matrix (Σ _ : κ, d) (Σ _ : κ, d) ℂ) :
    toLp 2
      ((A ⊗ₖ B.transpose).mulVec
        (ofLp (sharedThresholdResourceRaw (d := d) τ))) =
      toLp 2
        (Matrix.vec
          (B.transpose *
            Matrix.diagonal
              (fun q : Σ _ : κ, d => (τ q.1 : ℂ)) * A.transpose)) := by
  rw [sharedThresholdResourceRaw_eq_vec]
  apply WithLp.ofLp_injective
  change
    (A ⊗ₖ B.transpose).mulVec
      (Matrix.vec
        (Matrix.diagonal
          (fun q : Σ _ : κ, d => (τ q.1 : ℂ)))) =
      Matrix.vec
        (B.transpose *
          Matrix.diagonal
            (fun q : Σ _ : κ, d => (τ q.1 : ℂ)) * A.transpose)
  exact Matrix.kronecker_mulVec_vec
    B.transpose
    (Matrix.diagonal
      (fun q : Σ _ : κ, d => (τ q.1 : ℂ)))
    A

theorem matrixVectorization_norm_sq
    {d e : Type*} [Fintype d] [Fintype e]
    (K : Matrix d e ℂ) :
    ‖toLp 2 (Matrix.vec K)‖ ^ 2 =
      (Matrix.trace (K.conjTranspose * K)).re := by
  calc
    ‖toLp 2 (Matrix.vec K)‖ ^ 2 =
        (inner ℂ (toLp 2 (Matrix.vec K))
          (toLp 2 (Matrix.vec K))).re :=
            norm_sq_eq_re_inner (𝕜 := ℂ)
              (toLp 2 (Matrix.vec K))
    _ = (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (Matrix.vec K ⬝ᵥ star (Matrix.vec K)).re =
          (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re
      rw [dotProduct_comm]
    _ = (Matrix.trace (K.conjTranspose * K)).re := by
      rw [Matrix.star_vec_dotProduct_vec]

theorem sharedThresholdDiagonal_eq_block
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    Matrix.diagonal
        (fun q : Σ _ : κ, d => (τ q.1 : ℂ)) =
      Matrix.blockDiagonal' fun k : κ =>
        (τ k : ℂ) • (1 : Matrix d d ℂ) := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  by_cases h : k = l
  · subst l
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal'_apply]
    · simp [Matrix.blockDiagonal'_apply, hij]
  · simp [Matrix.blockDiagonal'_apply, h]

theorem sharedThresholdResourceRaw_block_action
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (A B : κ → Matrix d d ℂ) :
    toLp 2
      ((Matrix.blockDiagonal' A ⊗ₖ
          (Matrix.blockDiagonal' B).transpose).mulVec
        (ofLp (sharedThresholdResourceRaw (d := d) τ))) =
      toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : κ =>
              (τ k : ℂ) • (A k * B k)).transpose)) := by
  rw [sharedThresholdResourceRaw_local_action]
  congr 2
  rw [sharedThresholdDiagonal_eq_block]
  simp only [Matrix.blockDiagonal'_transpose]
  rw [← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  simp [Matrix.transpose_mul]

theorem projectorProduct_hilbertSchmidt_trace
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAA : A * A = A) (hBB : B * B = B) :
    Matrix.trace ((A * B).conjTranspose * (A * B)) =
      Matrix.trace (A * B) := by
  rw [Matrix.conjTranspose_mul,
    hA.isHermitian.eq, hB.isHermitian.eq]
  calc
    Matrix.trace ((B * A) * (A * B)) =
        Matrix.trace (B * (A * A) * B) := by
          congr 1
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (B * A * B) := by rw [hAA]
    _ = Matrix.trace (B * B * A) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (B * A) := by rw [hBB]
    _ = Matrix.trace (A * B) := Matrix.trace_mul_comm B A

theorem weightedProjectorProduct_hilbertSchmidt_trace
    {d : Type*} [Fintype d] [DecidableEq d]
    (t : ℝ) (A B : Matrix d d ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAA : A * A = A) (hBB : B * B = B) :
    (Matrix.trace
      (((t : ℂ) • (A * B)).conjTranspose *
        ((t : ℂ) • (A * B)))).re =
      t ^ 2 * (Matrix.trace (A * B)).re := by
  have hgram := projectorProduct_hilbertSchmidt_trace
    A B hA hB hAA hBB
  rw [Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, hgram]
  simp [Complex.mul_re, pow_two, mul_assoc]

theorem sharedThresholdResourceRaw_block_action_norm_sq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ)
    (A B : κ → Matrix d d ℂ)
    (hA : ∀ k, (A k).PosSemidef)
    (hB : ∀ k, (B k).PosSemidef)
    (hAA : ∀ k, A k * A k = A k)
    (hBB : ∀ k, B k * B k = B k) :
    ‖toLp 2
      ((Matrix.blockDiagonal' A ⊗ₖ
          (Matrix.blockDiagonal' B).transpose).mulVec
        (ofLp (sharedThresholdResourceRaw (d := d) τ)))‖ ^ 2 =
      ∑ k : κ, τ k ^ 2 *
        (Matrix.trace (A k * B k)).re := by
  rw [sharedThresholdResourceRaw_block_action,
    matrixVectorization_norm_sq]
  let K : Matrix (Σ _ : κ, d) (Σ _ : κ, d) ℂ :=
    Matrix.blockDiagonal' fun k : κ =>
      (τ k : ℂ) • (A k * B k)
  change
    (Matrix.trace (K.transpose.conjTranspose * K.transpose)).re =
      ∑ k : κ, τ k ^ 2 *
        (Matrix.trace (A k * B k)).re
  rw [Matrix.transpose_conjTranspose,
    ← Matrix.conjTranspose_transpose,
    Matrix.trace_transpose_mul]
  change
    (Matrix.trace
      ((Matrix.blockDiagonal' fun k : κ =>
        (τ k : ℂ) • (A k * B k)).conjTranspose *
        (Matrix.blockDiagonal' fun k : κ =>
          (τ k : ℂ) • (A k * B k)))).re = _
  rw [Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul,
    Matrix.trace_blockDiagonal', Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact weightedProjectorProduct_hilbertSchmidt_trace
    (τ k) (A k) (B k) (hA k) (hB k) (hAA k) (hBB k)

theorem sharedThresholdResource_block_action_norm_sq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ)
    (A B : κ → Matrix d d ℂ)
    (hA : ∀ k, (A k).PosSemidef)
    (hB : ∀ k, (B k).PosSemidef)
    (hAA : ∀ k, A k * A k = A k)
    (hBB : ∀ k, B k * B k = B k) :
    ‖toLp 2
      ((Matrix.blockDiagonal' A ⊗ₖ
          (Matrix.blockDiagonal' B).transpose).mulVec
        (ofLp (sharedThresholdResource (d := d) τ)))‖ ^ 2 =
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace (A k * B k)).re) /
        ((Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2) := by
  let M : Matrix
      ((Σ _ : κ, d) × (Σ _ : κ, d))
      ((Σ _ : κ, d) × (Σ _ : κ, d)) ℂ :=
    Matrix.blockDiagonal' A ⊗ₖ
      (Matrix.blockDiagonal' B).transpose
  change
    ‖Matrix.toEuclideanLin M
      (sharedThresholdResource (d := d) τ)‖ ^ 2 = _
  rw [sharedThresholdResource,
    (Matrix.toEuclideanLin M).map_smul_of_tower,
    norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    mul_pow, inv_pow]
  change
    (‖sharedThresholdResourceRaw (d := d) τ‖ ^ 2)⁻¹ *
      ‖toLp 2
        ((Matrix.blockDiagonal' A ⊗ₖ
            (Matrix.blockDiagonal' B).transpose).mulVec
          (ofLp (sharedThresholdResourceRaw (d := d) τ)))‖ ^ 2 = _
  rw [sharedThresholdResourceRaw_norm_sq,
    sharedThresholdResourceRaw_block_action_norm_sq
      τ A B hA hB hAA hBB]
  simp [div_eq_mul_inv, mul_comm]

theorem doublyStochasticSchmidtMass_le_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ) (w : ι → κ → ℝ)
    (hσunit : (∑ i : ι, σ i ^ 2) = 1)
    (hμunit : (∑ j : κ, μ j ^ 2) = 1)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, (∑ j : κ, w i j) = 1)
    (hcol : ∀ j, (∑ i : ι, w i j) = 1) :
    (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) ≤ 1 := by
  classical
  let W : ι × κ → ℝ := fun q => w q.1 q.2
  let f : ι × κ → ℝ := fun q => σ q.1
  let g : ι × κ → ℝ := fun q => μ q.2
  have hf : (∑ q : ι × κ, W q * f q ^ 2) = 1 := by
    dsimp [W, f]
    rw [Fintype.sum_prod_type]
    calc
      (∑ i : ι, ∑ j : κ, w i j * σ i ^ 2) =
          ∑ i : ι, σ i ^ 2 * (∑ j : κ, w i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring_nf
      _ = ∑ i : ι, σ i ^ 2 := by simp_rw [hrow, mul_one]
      _ = 1 := hσunit
  have hg : (∑ q : ι × κ, W q * g q ^ 2) = 1 := by
    dsimp [W, g]
    rw [Fintype.sum_prod_type]
    calc
      (∑ i : ι, ∑ j : κ, w i j * μ j ^ 2) =
          ∑ j : κ, μ j ^ 2 * (∑ i : ι, w i j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ j : κ, μ j ^ 2 := by simp_rw [hcol, mul_one]
      _ = 1 := hμunit
  calc
    (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) =
        ∑ q : ι × κ, W q * f q * g q := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          dsimp [W, f, g]
          ring
    _ ≤ Real.sqrt (∑ q : ι × κ, W q * f q ^ 2) *
        Real.sqrt (∑ q : ι × κ, W q * g q ^ 2) := by
          apply weighted_real_cauchy
          intro q
          exact hw q.1 q.2
    _ = 1 := by rw [hf, hg]; norm_num

theorem doublyStochasticSchmidtEnergy_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ) (w : ι → κ → ℝ)
    (hσunit : (∑ i : ι, σ i ^ 2) = 1)
    (hμunit : (∑ j : κ, μ j ^ 2) = 1)
    (hrow : ∀ i, (∑ j : κ, w i j) = 1)
    (hcol : ∀ j, (∑ i : ι, w i j) = 1) :
    (∑ i : ι, ∑ j : κ, (σ i - μ j) ^ 2 * w i j) =
      2 - 2 * (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) := by
  classical
  have hfirst :
      (∑ i : ι, ∑ j : κ, σ i ^ 2 * w i j) = 1 := by
    calc
      (∑ i : ι, ∑ j : κ, σ i ^ 2 * w i j) =
          ∑ i : ι, σ i ^ 2 * (∑ j : κ, w i j) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ i : ι, σ i ^ 2 := by simp_rw [hrow, mul_one]
      _ = 1 := hσunit
  have hsecond :
      (∑ i : ι, ∑ j : κ, μ j ^ 2 * w i j) = 1 := by
    calc
      (∑ i : ι, ∑ j : κ, μ j ^ 2 * w i j) =
          ∑ j : κ, μ j ^ 2 * (∑ i : ι, w i j) := by
            rw [Finset.sum_comm]
            simp_rw [Finset.mul_sum]
      _ = ∑ j : κ, μ j ^ 2 := by simp_rw [hcol, mul_one]
      _ = 1 := hμunit
  calc
    (∑ i : ι, ∑ j : κ, (σ i - μ j) ^ 2 * w i j) =
      (∑ i : ι, ∑ j : κ, σ i ^ 2 * w i j) -
        2 * (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) +
          (∑ i : ι, ∑ j : κ, μ j ^ 2 * w i j) := by
            simp_rw [sub_sq]
            simp only [sub_mul, add_mul,
              Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum]
            ring_nf
    _ = 2 - 2 * (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) := by
      rw [hfirst, hsecond]
      ring

def weightedComplexOverlapVector
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ)
    (L : ι → κ → ℂ) : EuclideanSpace ℂ (ι × κ) :=
  toLp 2 fun q : ι × κ =>
    (Real.sqrt (σ q.1 * μ q.2) : ℂ) * L q.1 q.2

theorem weightedComplexOverlapVector_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (L : ι → κ → ℂ) :
    ‖weightedComplexOverlapVector σ μ L‖ ^ 2 =
      ∑ i : ι, ∑ j : κ,
        σ i * μ j * ‖L i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change
    ‖(Real.sqrt (σ i * μ j) : ℂ) * L i j‖ ^ 2 =
      σ i * μ j * ‖L i j‖ ^ 2
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_nonneg (hσ i) (hμ j))]

theorem complexInner_norm_sq_le
    {ι : Type*} [Fintype ι]
    (z w : EuclideanSpace ℂ ι) :
    ‖inner ℂ z w‖ ^ 2 ≤ ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
  have hcauchy := @norm_inner_le_norm ℂ _ _ _ _ z w
  nlinarith [norm_nonneg (inner ℂ z w), norm_nonneg z,
    norm_nonneg w, mul_nonneg (norm_nonneg z) (norm_nonneg w)]

theorem twoSidedSchmidtSpectralEnergy_le
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (ψ φ : EuclideanSpace ℂ ν)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (σ : ι → ℝ) (μ : κ → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (hσunit : (∑ i : ι, σ i ^ 2) = 1)
    (hμunit : (∑ j : κ, μ j ^ 2) = 1)
    (L R : ι → κ → ℂ)
    (hLrow : ∀ i, (∑ j : κ, ‖L i j‖ ^ 2) = 1)
    (hLcol : ∀ j, (∑ i : ι, ‖L i j‖ ^ 2) = 1)
    (hRrow : ∀ i, (∑ j : κ, ‖R i j‖ ^ 2) = 1)
    (hRcol : ∀ j, (∑ i : ι, ‖R i j‖ ^ 2) = 1)
    (hinner :
      inner ℂ ψ φ =
        inner ℂ
          (weightedComplexOverlapVector σ μ L)
          (weightedComplexOverlapVector σ μ R)) :
    (∑ i : ι, ∑ j : κ,
      (σ i - μ j) ^ 2 * ‖L i j‖ ^ 2) ≤
        2 * ‖ψ - φ‖ ^ 2 := by
  classical
  let a : ℝ :=
    ∑ i : ι, ∑ j : κ, σ i * μ j * ‖L i j‖ ^ 2
  let b : ℝ :=
    ∑ i : ι, ∑ j : κ, σ i * μ j * ‖R i j‖ ^ 2
  have ha : 0 ≤ a := by
    dsimp [a]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg
      (mul_nonneg (hσ i) (hμ j)) (sq_nonneg _)
  have hb : b ≤ 1 := by
    exact doublyStochasticSchmidtMass_le_one
      σ μ (fun i j => ‖R i j‖ ^ 2)
      hσunit hμunit
      (fun i j => sq_nonneg _)
      hRrow hRcol
  have hinnerbound : ‖inner ℂ ψ φ‖ ^ 2 ≤ a := by
    calc
      ‖inner ℂ ψ φ‖ ^ 2 =
          ‖inner ℂ
            (weightedComplexOverlapVector σ μ L)
            (weightedComplexOverlapVector σ μ R)‖ ^ 2 := by
              rw [hinner]
      _ ≤ ‖weightedComplexOverlapVector σ μ L‖ ^ 2 *
          ‖weightedComplexOverlapVector σ μ R‖ ^ 2 :=
            complexInner_norm_sq_le
              (weightedComplexOverlapVector σ μ L)
              (weightedComplexOverlapVector σ μ R)
      _ = a * b := by
            rw [weightedComplexOverlapVector_norm_sq
              σ μ hσ hμ L,
              weightedComplexOverlapVector_norm_sq
                σ μ hσ hμ R]
      _ ≤ a := by nlinarith
  have hre : (inner ℂ ψ φ).re ^ 2 ≤ a := by
    calc
      (inner ℂ ψ φ).re ^ 2 =
          (inner ℂ ψ φ).re * (inner ℂ ψ φ).re := by ring
      _ ≤ Complex.normSq (inner ℂ ψ φ) :=
        Complex.re_sq_le_normSq (inner ℂ ψ φ)
      _ = ‖inner ℂ ψ φ‖ ^ 2 :=
        Complex.normSq_eq_norm_sq (inner ℂ ψ φ)
      _ ≤ a := hinnerbound
  have hdistance :
      ‖ψ - φ‖ ^ 2 = 2 - 2 * (inner ℂ ψ φ).re := by
    rw [@norm_sub_sq ℂ, hψ, hφ]
    change
      1 ^ 2 - 2 * (inner ℂ ψ φ).re + 1 ^ 2 =
        2 - 2 * (inner ℂ ψ φ).re
    ring
  rw [doublyStochasticSchmidtEnergy_eq
    σ μ (fun i j => ‖L i j‖ ^ 2)
    hσunit hμunit hLrow hLcol, hdistance]
  change 2 - 2 * a ≤ 2 *
    (2 - 2 * (inner ℂ ψ φ).re)
  nlinarith [sq_nonneg ((inner ℂ ψ φ).re - 1)]

def tensorEmbezzlementTarget
    {d n : ℕ} (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin (d * n) × Fin (d * n)) :=
  toLp 2 fun q : Fin (d * n) × Fin (d * n) =>
    let a : Fin d × Fin n := finProdFinEquiv.symm q.1
    let b : Fin d × Fin n := finProdFinEquiv.symm q.2
    ξ.val (a.1, b.1) * embezzlementState n (a.2, b.2)

theorem tensorEmbezzlementTarget_norm
    {d n : ℕ} (hn : 0 < n)
    (ξ : BipartiteUnitVector d) :
    ‖tensorEmbezzlementTarget (n := n) ξ‖ = 1 := by
  classical
  let e : ((Fin d × Fin d) × (Fin n × Fin n)) ≃
      (Fin (d * n) × Fin (d * n)) :=
    (Equiv.prodProdProdComm (Fin d) (Fin d) (Fin n) (Fin n)).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  have hpoint (p : (Fin d × Fin d) × (Fin n × Fin n)) :
      tensorEmbezzlementTarget (n := n) ξ (e p) =
        ξ.val p.1 * embezzlementState n p.2 := by
    rcases p with ⟨⟨a, b⟩, ⟨c, f⟩⟩
    change
      ξ.val
        ((finProdFinEquiv.symm (finProdFinEquiv (a, c))).1,
          (finProdFinEquiv.symm (finProdFinEquiv (b, f))).1) *
        embezzlementState n
          ((finProdFinEquiv.symm (finProdFinEquiv (a, c))).2,
            (finProdFinEquiv.symm (finProdFinEquiv (b, f))).2) =
        ξ.val (a, b) * embezzlementState n (c, f)
    simp only [Equiv.symm_apply_apply]
  have hsum :
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖tensorEmbezzlementTarget (n := n) ξ q‖ ^ 2) =
      ∑ p : (Fin d × Fin d) × (Fin n × Fin n),
        ‖ξ.val p.1 * embezzlementState n p.2‖ ^ 2 := by
    calc
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖tensorEmbezzlementTarget (n := n) ξ q‖ ^ 2) =
        ∑ p : (Fin d × Fin d) × (Fin n × Fin n),
          ‖tensorEmbezzlementTarget (n := n) ξ (e p)‖ ^ 2 :=
            (Equiv.sum_comp e
              (fun q : Fin (d * n) × Fin (d * n) =>
                ‖tensorEmbezzlementTarget (n := n) ξ q‖ ^ 2)).symm
      _ = ∑ p : (Fin d × Fin d) × (Fin n × Fin n),
          ‖ξ.val p.1 * embezzlementState n p.2‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hpoint p]
  have hfactor :
      (∑ p : (Fin d × Fin d) × (Fin n × Fin n),
        ‖ξ.val p.1 * embezzlementState n p.2‖ ^ 2) =
      (∑ a : Fin d × Fin d, ‖ξ.val a‖ ^ 2) *
        (∑ b : Fin n × Fin n,
          ‖embezzlementState n b‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [norm_mul, mul_pow]
    exact (Fintype.sum_mul_sum
      (fun a : Fin d × Fin d => ‖ξ.val a‖ ^ 2)
      (fun b : Fin n × Fin n =>
        ‖embezzlementState n b‖ ^ 2)).symm
  have hsquare :
      ‖tensorEmbezzlementTarget (n := n) ξ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, hsum, hfactor,
      ← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq,
      ξ.property, embezzlementState_norm n hn]
    norm_num
  nlinarith [norm_nonneg (tensorEmbezzlementTarget (n := n) ξ)]

def localUnitaryAction {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2
    (((U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)).mulVec (ofLp ψ))

theorem localUnitaryAction_matrix_mem_unitary {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    ((U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)) ∈
        Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  exact Matrix.kronecker_mem_unitary U.property V.property

theorem localUnitaryAction_norm {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖localUnitaryAction U V ψ‖ = ‖ψ‖ := by
  let M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    (U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)
  have hM : M ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ :=
    localUnitaryAction_matrix_mem_unitary U V
  have hclm : Matrix.toEuclideanCLM
      (n := Fin n × Fin n) (𝕜 := ℂ) M ∈
      unitary
        (EuclideanSpace ℂ (Fin n × Fin n) →L[ℂ]
          EuclideanSpace ℂ (Fin n × Fin n)) :=
    Unitary.map_mem
      (Matrix.toEuclideanCLM (n := Fin n × Fin n) (𝕜 := ℂ)) hM
  exact ContinuousLinearMap.norm_map_of_mem_unitary hclm ψ

theorem unitary_row_norm_sq_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (i : d) :
    (∑ j : d, ‖U i j‖ ^ 2) = 1 := by
  have hnorm (z : ℂ) :
      z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h := congrArg
    (fun M : Matrix d d ℂ => (M i i).re) U.property.2
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, hnorm, Matrix.one_apply] using h

theorem unitary_col_norm_sq_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (j : d) :
    (∑ i : d, ‖U i j‖ ^ 2) = 1 := by
  have hnorm (z : ℂ) :
      z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h := congrArg
    (fun M : Matrix d d ℂ => (M j j).re) U.property.1
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, hnorm, Matrix.one_apply] using h

def unitaryBasisOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup d ℂ := U⁻¹ * V

def diagonalSchmidtState
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) : EuclideanSpace ℂ (d × d) :=
  toLp 2 fun q : d × d =>
    if q.1 = q.2 then (σ q.1 : ℂ) else 0

theorem diagonalSchmidtState_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) :
    ‖diagonalSchmidtState σ‖ ^ 2 =
      ∑ i : d, σ i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : d, ‖if i = j then (σ i : ℂ) else 0‖ ^ 2) =
      σ i ^ 2
  have hterm (j : d) :
      ‖if i = j then (σ i : ℂ) else 0‖ ^ 2 =
        if i = j then σ i ^ 2 else 0 := by
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hterm]
  simp

def schmidtVector
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  localUnitaryAction U V
    (diagonalSchmidtState σ)

theorem schmidtVector_norm_sq
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖schmidtVector σ U V‖ ^ 2 =
      ∑ i : Fin d, σ i ^ 2 := by
  rw [schmidtVector,
    localUnitaryAction_norm,
    diagonalSchmidtState_norm_sq]

theorem schmidtVector_apply
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) :
    schmidtVector σ U V (a, b) =
      ∑ i : Fin d, (σ i : ℂ) * U a i * V b i := by
  classical
  simp [schmidtVector, localUnitaryAction,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    diagonalSchmidtState, Fintype.sum_prod_type,
    mul_assoc, mul_comm]

theorem weightedComplexOverlapVector_inner
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (L R : ι → κ → ℂ) :
    inner ℂ
      (weightedComplexOverlapVector σ μ
        (fun i j => star (L i j)))
      (weightedComplexOverlapVector σ μ R) =
        ∑ i : ι, ∑ j : κ,
          (σ i : ℂ) * (μ j : ℂ) * L i j * R i j := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    (∑ q : ι × κ,
      ((Real.sqrt (σ q.1 * μ q.2) : ℂ) * R q.1 q.2) *
        star ((Real.sqrt (σ q.1 * μ q.2) : ℂ) *
          star (L q.1 q.2))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsqrt :
      (Real.sqrt (σ i * μ j) : ℂ) *
        (Real.sqrt (σ i * μ j) : ℂ) =
          (σ i : ℂ) * (μ j : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (mul_nonneg (hσ i) (hμ j))
  calc
    ((Real.sqrt (σ i * μ j) : ℂ) * R i j) *
        star ((Real.sqrt (σ i * μ j) : ℂ) * star (L i j)) =
      ((Real.sqrt (σ i * μ j) : ℂ) * R i j) *
        ((Real.sqrt (σ i * μ j) : ℂ) * L i j) := by simp
    _ =
      ((Real.sqrt (σ i * μ j) : ℂ) *
        (Real.sqrt (σ i * μ j) : ℂ)) *
          L i j * R i j := by ring
    _ = (σ i : ℂ) * (μ j : ℂ) * L i j * R i j := by
      rw [hsqrt]

theorem matrixVectorization_inner
    {d e : Type*} [Fintype d] [Fintype e]
    (X Y : Matrix d e ℂ) :
    inner ℂ (toLp 2 (Matrix.vec X))
      (toLp 2 (Matrix.vec Y)) =
        Matrix.trace (X.conjTranspose * Y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    Matrix.vec Y ⬝ᵥ star (Matrix.vec X) =
      Matrix.trace (X.conjTranspose * Y)
  rw [dotProduct_comm, Matrix.star_vec_dotProduct_vec]

theorem diagonalSchmidtState_eq_vec
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) :
    diagonalSchmidtState σ =
      toLp 2 (Matrix.vec (Matrix.diagonal fun i => (σ i : ℂ))) := by
  ext ⟨i, j⟩
  by_cases h : i = j
  · subst j
    simp [diagonalSchmidtState, Matrix.vec]
  · simp [diagonalSchmidtState, Matrix.vec, h, Ne.symm h]

theorem schmidtVector_eq_vec
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    schmidtVector σ U V =
      toLp 2
        (Matrix.vec
          ((V : Matrix (Fin d) (Fin d) ℂ) *
            Matrix.diagonal (fun i => (σ i : ℂ)) *
            (U : Matrix (Fin d) (Fin d) ℂ).transpose)) := by
  rw [schmidtVector, localUnitaryAction,
    diagonalSchmidtState_eq_vec]
  apply WithLp.ofLp_injective
  exact Matrix.kronecker_mulVec_vec
    (V : Matrix (Fin d) (Fin d) ℂ)
    (Matrix.diagonal (fun i => (σ i : ℂ)))
    (U : Matrix (Fin d) (Fin d) ℂ)

theorem weightedSchmidtMatrixTrace
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ μ : d → ℝ) (L R : Matrix d d ℂ) :
    Matrix.trace
      (L.transpose *
        Matrix.diagonal (fun i => (σ i : ℂ)) *
        R * Matrix.diagonal (fun j => (μ j : ℂ))) =
      ∑ i : d, ∑ j : d,
        (σ i : ℂ) * (μ j : ℂ) * L i j * R i j := by
  classical
  simp [Matrix.trace, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply,
    mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

theorem schmidtVector_inner
    {d : ℕ}
    (σ μ : Fin d → ℝ)
    (U V X Y : Matrix.unitaryGroup (Fin d) ℂ) :
    inner ℂ
      (schmidtVector σ U V)
      (schmidtVector μ X Y) =
        ∑ i : Fin d, ∑ j : Fin d,
          (σ i : ℂ) * (μ j : ℂ) *
            (((U : Matrix (Fin d) (Fin d) ℂ).conjTranspose *
              (X : Matrix (Fin d) (Fin d) ℂ)) i j) *
            (((V : Matrix (Fin d) (Fin d) ℂ).conjTranspose *
              (Y : Matrix (Fin d) (Fin d) ℂ)) i j) := by
  classical
  rw [schmidtVector_eq_vec σ U V,
    schmidtVector_eq_vec μ X Y,
    matrixVectorization_inner]
  let S : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal fun i => (σ i : ℂ)
  let T : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal fun i => (μ i : ℂ)
  let A : Matrix (Fin d) (Fin d) ℂ := U
  let B : Matrix (Fin d) (Fin d) ℂ := V
  let C : Matrix (Fin d) (Fin d) ℂ := X
  let D : Matrix (Fin d) (Fin d) ℂ := Y
  change
    Matrix.trace ((B * S * A.transpose).conjTranspose *
      (D * T * C.transpose)) = _
  calc
    Matrix.trace ((B * S * A.transpose).conjTranspose *
        (D * T * C.transpose)) =
      Matrix.trace
        (((B * S * A.transpose).conjTranspose *
          (D * T)) * C.transpose) := by
            congr 1
            simp [Matrix.mul_assoc]
    _ = Matrix.trace
        (C.transpose *
          ((B * S * A.transpose).conjTranspose * (D * T))) :=
            Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        ((A.conjTranspose * C).transpose * S *
          (B.conjTranspose * D) * T) := by
            congr 1
            simp [Matrix.conjTranspose_mul,
              Matrix.transpose_mul,
              Matrix.transpose_conjTranspose,
              Matrix.conjTranspose_transpose,
              Matrix.diagonal_conjTranspose,
              S, Pi.star_def, Matrix.mul_assoc]
    _ = _ := weightedSchmidtMatrixTrace
      σ μ (A.conjTranspose * C) (B.conjTranspose * D)

@[simp] theorem unitaryBasisOverlap_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) (i j : d) :
    unitaryBasisOverlap U V i j =
      (((U : Matrix d d ℂ).conjTranspose *
        (V : Matrix d d ℂ)) i j) := by
  rfl

theorem schmidtVector_spectralEnergy_le
    {d : ℕ}
    (σ μ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (hσunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (hμunit : (∑ j : Fin d, μ j ^ 2) = 1)
    (U V X Y : Matrix.unitaryGroup (Fin d) ℂ) :
    (∑ i : Fin d, ∑ j : Fin d,
      (σ i - μ j) ^ 2 *
        ‖unitaryBasisOverlap U X i j‖ ^ 2) ≤
      2 * ‖schmidtVector σ U V -
        schmidtVector μ X Y‖ ^ 2 := by
  have hψ : ‖schmidtVector σ U V‖ = 1 := by
    have h := schmidtVector_norm_sq σ U V
    rw [hσunit] at h
    nlinarith [norm_nonneg (schmidtVector σ U V)]
  have hφ : ‖schmidtVector μ X Y‖ = 1 := by
    have h := schmidtVector_norm_sq μ X Y
    rw [hμunit] at h
    nlinarith [norm_nonneg (schmidtVector μ X Y)]
  let L : Fin d → Fin d → ℂ :=
    fun i j => star (unitaryBasisOverlap U X i j)
  let R : Fin d → Fin d → ℂ :=
    fun i j => unitaryBasisOverlap V Y i j
  have hLrow : ∀ i, (∑ j : Fin d, ‖L i j‖ ^ 2) = 1 := by
    intro i
    simpa [L] using
      unitary_row_norm_sq_sum
        (unitaryBasisOverlap U X) i
  have hLcol : ∀ j, (∑ i : Fin d, ‖L i j‖ ^ 2) = 1 := by
    intro j
    simpa [L] using
      unitary_col_norm_sq_sum
        (unitaryBasisOverlap U X) j
  have hRrow : ∀ i, (∑ j : Fin d, ‖R i j‖ ^ 2) = 1 := by
    intro i
    exact unitary_row_norm_sq_sum
      (unitaryBasisOverlap V Y) i
  have hRcol : ∀ j, (∑ i : Fin d, ‖R i j‖ ^ 2) = 1 := by
    intro j
    exact unitary_col_norm_sq_sum
      (unitaryBasisOverlap V Y) j
  have hinner :
      inner ℂ (schmidtVector σ U V)
          (schmidtVector μ X Y) =
        inner ℂ
          (weightedComplexOverlapVector σ μ L)
          (weightedComplexOverlapVector σ μ R) := by
    rw [weightedComplexOverlapVector_inner
      σ μ hσ hμ
      (fun i j => unitaryBasisOverlap U X i j)
      (fun i j => unitaryBasisOverlap V Y i j)]
    simpa [unitaryBasisOverlap_apply] using
      schmidtVector_inner σ μ U V X Y
  simpa [L] using
    twoSidedSchmidtSpectralEnergy_le
      (schmidtVector σ U V)
      (schmidtVector μ X Y)
      hψ hφ σ μ hσ hμ hσunit hμunit L R
      hLrow hLcol hRrow hRcol hinner

end

noncomputable section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

theorem linearMap_exists_singularBases
    {d : ℕ}
    (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d)) :
    ∃ (σ : Fin d → ℝ)
      (u v : OrthonormalBasis (Fin d) ℂ
        (EuclideanSpace ℂ (Fin d))),
      (∀ i, 0 ≤ σ i) ∧
        (∀ i, T (v i) = (σ i : ℂ) • u i) := by
  classical
  let hT := T.isPositive_adjoint_comp_self
  let v : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)) :=
    hT.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let σ : Fin d → ℝ := fun i =>
    Real.sqrt
      (hT.isSymmetric.eigenvalues finrank_euclideanSpace_fin i)
  have hσ (i : Fin d) : 0 ≤ σ i := Real.sqrt_nonneg _
  have hσsq (i : Fin d) :
      σ i ^ 2 =
        hT.isSymmetric.eigenvalues finrank_euclideanSpace_fin i := by
    exact Real.sq_sqrt
      (hT.nonneg_eigenvalues finrank_euclideanSpace_fin i)
  have heigen (i : Fin d) :
      (T.adjoint ∘ₗ T) (v i) = ((σ i ^ 2 : ℝ) : ℂ) • v i := by
    rw [hσsq]
    exact hT.isSymmetric.apply_eigenvectorBasis
      finrank_euclideanSpace_fin i
  let s : Set (Fin d) := {i | σ i ≠ 0}
  let f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun i => ((σ i : ℂ)⁻¹) • T (v i)
  have hGram (i j : Fin d) :
      inner ℂ (T (v i)) (T (v j)) =
        ((σ j ^ 2 : ℝ) : ℂ) *
          inner ℂ (v i) (v j) := by
    calc
      inner ℂ (T (v i)) (T (v j)) =
          inner ℂ (v i) (T.adjoint (T (v j))) :=
        (T.adjoint_inner_right (v i) (T (v j))).symm
      _ = inner ℂ (v i)
          (((σ j ^ 2 : ℝ) : ℂ) • v j) := by
        rw [← heigen j]
        rfl
      _ = ((σ j ^ 2 : ℝ) : ℂ) *
          inner ℂ (v i) (v j) := by
        rw [inner_smul_right]
  have hf : Orthonormal ℂ (s.restrict f) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (σ (i : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast i.property
    have hj : (σ (j : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast j.property
    change inner ℂ
      (((σ (i : Fin d) : ℂ)⁻¹) • T (v i))
      (((σ (j : Fin d) : ℂ)⁻¹) • T (v j)) = _
    rw [inner_smul_left, inner_smul_right, hGram,
      v.inner_eq_ite]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, mul_one]
      have hs :
          starRingEnd ℂ ((σ (i : Fin d) : ℂ)⁻¹) =
            ((σ (i : Fin d) : ℂ)⁻¹) := by
        simp
      rw [hs]
      push_cast
      field_simp
    · have hval : (i : Fin d) ≠ (j : Fin d) := by
        intro h
        exact hij (Subtype.ext h)
      simp [hij, hval]
  obtain ⟨u, hu⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by
        rw [Fintype.card_fin]
        exact finrank_euclideanSpace_fin) hf
  refine ⟨σ, u, v, hσ, ?_⟩
  intro i
  by_cases hi : σ i = 0
  · have hker : (T.adjoint ∘ₗ T) (v i) = 0 := by
      rw [heigen i, hi]
      simp
    have hTv : T (v i) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← T.ker_adjoint_comp_self]
      exact LinearMap.mem_ker.mpr hker
    simp [hi, hTv]
  · have hui : u i = f i := hu i hi
    rw [hui]
    change T (v i) =
      (σ i : ℂ) • (((σ i : ℂ)⁻¹) • T (v i))
    rw [smul_smul, mul_inv_cancel₀]
    · simp
    · exact_mod_cast hi

end

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

def orthonormalBasisUnitary
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d))) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp] theorem orthonormalBasisUnitary_apply
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)))
    (i j : Fin d) :
    orthonormalBasisUnitary b i j = b j i := by
  rfl

def conjugateUnitary
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d) ℂ := by
  refine ⟨(U.val.conjTranspose).transpose, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change
    ((U.val.conjTranspose).transpose).conjTranspose *
      (U.val.conjTranspose).transpose = 1
  have htranspose :
      ((U.val.conjTranspose).transpose).conjTranspose =
        U.val.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [htranspose]
  have h := congrArg Matrix.transpose U.property.1
  simpa [Matrix.star_eq_conjTranspose, Matrix.transpose_mul] using h

@[simp] theorem conjugateUnitary_apply
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    conjugateUnitary U i j = star (U i j) := by
  rfl

-- Vendoring compile fix (Lean v4.33): this proof needs the pre-v4.33 transparency
-- behaviour (its closing `simpa` no longer sees through `Matrix.toEuclideanLin`);
-- see README.md.
set_option backward.isDefEq.respectTransparency false in
theorem exists_proofSchmidtDecomposition
    {d : ℕ}
    (ξ : EuclideanSpace ℂ (Fin d × Fin d)) :
    ∃ (σ : Fin d → ℝ)
      (U V : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, 0 ≤ σ i) ∧
        ξ = schmidtVector σ U V := by
  classical
  let C : Matrix (Fin d) (Fin d) ℂ := fun b a => ξ (a, b)
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d) := Matrix.toEuclideanLin C
  obtain ⟨σ, u, v, hσ, hsing⟩ :=
    linearMap_exists_singularBases T
  refine ⟨σ,
    conjugateUnitary (orthonormalBasisUnitary v),
    orthonormalBasisUnitary u, hσ, ?_⟩
  ext ⟨a, b⟩
  rw [schmidtVector_apply]
  have hrepr :
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
        ∑ i : Fin d,
          inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
            T (v i) := by
    calc
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
          T (∑ i : Fin d,
            inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
              v i) := by
        rw [v.sum_repr']
      _ = _ := by
        simp
  have hcoord := congrArg
    (fun z : EuclideanSpace ℂ (Fin d) => z b) hrepr
  simpa [T, C, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, EuclideanSpace.inner_single_right,
    conjugateUnitary_apply,
    orthonormalBasisUnitary_apply, hsing,
    mul_assoc, mul_left_comm, mul_comm] using hcoord

theorem exists_proofUnitSchmidtDecomposition
    {d : ℕ}
    (ξ : BipartiteUnitVector d) :
    ∃ (σ : Fin d → ℝ)
      (U V : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, 0 ≤ σ i) ∧
        (∑ i : Fin d, σ i ^ 2) = 1 ∧
        ξ.val = schmidtVector σ U V := by
  obtain ⟨σ, U, V, hσ, hξ⟩ :=
    exists_proofSchmidtDecomposition ξ.val
  refine ⟨σ, U, V, hσ, ?_, hξ⟩
  have hnorm : ‖schmidtVector σ U V‖ ^ 2 = 1 := by
    rw [← hξ, ξ.property]
    norm_num
  exact (schmidtVector_norm_sq σ U V).symm.trans hnorm

end

noncomputable section

open scoped BigOperators

theorem harmonicNumber_eq_harmonic (n : ℕ) :
    harmonicNumber n = (harmonic n : ℝ) := by
  unfold harmonicNumber harmonic
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem harmonicNumber_log_lower (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ harmonicNumber n := by
  rw [harmonicNumber_eq_harmonic]
  simpa [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n

theorem harmonicNumber_log_upper (n : ℕ) :
    harmonicNumber n ≤ 1 + Real.log (n : ℝ) := by
  rw [harmonicNumber_eq_harmonic]
  exact harmonic_le_one_add_log n

theorem harmonicNumber_pos {n : ℕ} (hn : 0 < n) :
    0 < harmonicNumber n := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (Real.log_pos (by linarith : (1 : ℝ) < (n : ℝ) + 1)).trans_le
    (harmonicNumber_log_lower n)

theorem harmonicNumber_mul_le_add
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    harmonicNumber (d * n) ≤
      harmonicNumber n + (1 + Real.log (d : ℝ)) := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log (n : ℝ) ≤ harmonicNumber n := by
    exact (Real.log_le_log hnreal (by linarith :
      (n : ℝ) ≤ (n : ℝ) + 1)).trans
      (harmonicNumber_log_lower n)
  calc
    harmonicNumber (d * n) ≤
        1 + Real.log ((d * n : ℕ) : ℝ) :=
          harmonicNumber_log_upper (d * n)
    _ = 1 + (Real.log (d : ℝ) + Real.log (n : ℝ)) := by
      rw [Nat.cast_mul, Real.log_mul hdreal.ne' hnreal.ne']
    _ ≤ harmonicNumber n + (1 + Real.log (d : ℝ)) := by
      linarith

theorem exists_proofHarmonicNumber_gt (bound : ℝ) :
    ∃ n : ℕ, bound < harmonicNumber n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp bound)
  have hpositive : 0 < (n : ℝ) + 1 := by positivity
  have hlog : bound < Real.log ((n : ℝ) + 1) := by
    apply (Real.lt_log_iff_exp_lt hpositive).mpr
    exact lt_trans hn (by linarith)
  exact ⟨n, hlog.trans_le (harmonicNumber_log_lower n)⟩

theorem exists_proofHarmonicNumber_ratio_ge
    (d : ℕ) (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ n : ℕ, 0 < n ∧
      1 - ε ≤ harmonicNumber n /
        harmonicNumber (d * n) := by
  let C : ℝ := 1 + Real.log (d : ℝ)
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hd
  have hC : 0 < C := by
    dsimp [C]
    linarith
  obtain ⟨n, hnlarge⟩ :=
    exists_proofHarmonicNumber_gt (C / ε)
  have hn : 0 < n := by
    have hzero : harmonicNumber 0 = 0 := by
      rw [harmonicNumber_eq_harmonic]
      simp
    by_contra hnot
    have hnzero : n = 0 := by omega
    rw [hnzero, hzero] at hnlarge
    have hpositive : 0 < C / ε := div_pos hC hε
    linarith
  have hden : 0 < harmonicNumber (d * n) :=
    harmonicNumber_pos (Nat.mul_pos hd hn)
  have hupper := harmonicNumber_mul_le_add hd hn
  have hbudget : C < ε * harmonicNumber n := by
    have h := (div_lt_iff₀ hε).mp hnlarge
    nlinarith
  refine ⟨n, hn, (le_div_iff₀ hden).mpr ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left
    hupper (sub_nonneg.mpr hεone)
  have hproduct : 0 ≤ ε * C := mul_nonneg hε.le hC.le
  change (1 - ε) * harmonicNumber (d * n) ≤
    harmonicNumber n
  change harmonicNumber (d * n) ≤
    harmonicNumber n + C at hupper
  change (1 - ε) * harmonicNumber (d * n) ≤
    (1 - ε) * (harmonicNumber n + C) at hscaled
  nlinarith

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker

def ePRState (m : ℕ) :
    EuclideanSpace ℂ (Fin m × Fin m) :=
  toLp 2 fun q : Fin m × Fin m =>
    if q.1 = q.2 then
      (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
    else
      0

theorem ePRState_norm (m : ℕ) (hm : 0 < m) :
    ‖ePRState m‖ = 1 := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hamp :
      ‖(↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)‖ ^ 2 =
        (m : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      inv_pow, Real.sq_sqrt hmreal.le]
  have hsquare : ‖ePRState m‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    have hterm (i j : Fin m) :
        ‖if i = j then
          (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
        else
          0‖ ^ 2 =
          if i = j then (m : ℝ)⁻¹ else 0 := by
      split_ifs with h
      · exact hamp
      · simp
    change
      (∑ i : Fin m, ∑ j : Fin m,
        ‖if i = j then
          (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
        else
          0‖ ^ 2) = 1
    simp_rw [hterm]
    simp [hmreal.ne']
  nlinarith [norm_nonneg (ePRState m)]

theorem permutationMatrix_mem_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

def permutationUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨σ.permMatrix ℂ, permutationMatrix_mem_unitary σ⟩

@[simp] theorem permutationUnitary_val
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    (permutationUnitary σ : Matrix ι ι ℂ) =
      σ.permMatrix ℂ := rfl

theorem localPermutationUnitaryAction_apply
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n × Fin n))
    (i j : Fin n) :
    localUnitaryAction
      (permutationUnitary σ)
      (permutationUnitary σ) ψ (i, j) =
        ψ (σ i, σ j) := by
  let X : Matrix (Fin n) (Fin n) ℂ :=
    fun a b => ψ (b, a)
  have hx : ofLp ψ = Matrix.vec X := by
    funext q
    rcases q with ⟨a, b⟩
    rfl
  change
    (((σ.permMatrix ℂ) ⊗ₖ (σ.permMatrix ℂ)).mulVec
      (ofLp ψ)) (i, j) = ψ (σ i, σ j)
  rw [hx, Matrix.kronecker_mulVec_vec]
  change
    ((σ.permMatrix ℂ) * X *
      (σ.permMatrix ℂ).transpose) j i = ψ (σ i, σ j)
  rw [Matrix.transpose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem diagonalInner_real_eq_sum
    {N : ℕ}
    (z w : EuclideanSpace ℂ (Fin N × Fin N))
    (hz : ∀ i j : Fin N, i ≠ j → z (i, j) = 0) :
    (inner ℂ z w).re =
      ∑ i : Fin N, (inner ℂ (z (i, i)) (w (i, i))).re := by
  rw [PiLp.inner_apply, Complex.re_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hz i j (Ne.symm hji)]
    simp
  · simp

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem harmonicSchmidtFiber_count_sq_le
    {n : ℕ} (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    (((Finset.univ.filter fun j : Fin n =>
      x ≤ a * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) * x ^ 2 ≤
      a ^ 2 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j : Fin n =>
    x ≤ a * (Real.sqrt ((j.val : ℝ) + 1))⁻¹
  change (S.card : ℝ) * x ^ 2 ≤ a ^ 2
  by_cases hs : S.Nonempty
  · let j : Fin n := S.max' hs
    have hjmem : j ∈ S := S.max'_mem hs
    have hjthreshold :
        x ≤ a * (Real.sqrt ((j.val : ℝ) + 1))⁻¹ :=
      (Finset.mem_filter.mp hjmem).2
    have hcard : S.card ≤ j.val + 1 := by
      calc
        S.card ≤ (Finset.Iic j).card := by
          apply Finset.card_le_card
          intro k hk
          exact Finset.mem_Iic.mpr (S.le_max' k hk)
        _ = j.val + 1 := by simp
    have hjpositive : 0 < (j.val : ℝ) + 1 := by positivity
    have hsqrtpositive : 0 < Real.sqrt ((j.val : ℝ) + 1) :=
      Real.sqrt_pos.2 hjpositive
    have hscaled :
        x * Real.sqrt ((j.val : ℝ) + 1) ≤ a := by
      apply (le_div_iff₀ hsqrtpositive).mp
      simpa [div_eq_mul_inv] using hjthreshold
    have hsquares :
        ((j.val : ℝ) + 1) * x ^ 2 ≤ a ^ 2 := by
      have hnonneg : 0 ≤ x * Real.sqrt ((j.val : ℝ) + 1) :=
        mul_nonneg hx (Real.sqrt_nonneg _)
      have hs :
          (x * Real.sqrt ((j.val : ℝ) + 1)) ^ 2 ≤ a ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hscaled)
          (add_nonneg ha hnonneg)]
      rw [mul_pow, Real.sq_sqrt hjpositive.le] at hs
      nlinarith
    have hcardreal : (S.card : ℝ) ≤ (j.val : ℝ) + 1 := by
      exact_mod_cast hcard
    exact (mul_le_mul_of_nonneg_right hcardreal (sq_nonneg x)).trans
      hsquares
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    simp [sq_nonneg a]

def harmonicTensorSchmidtAmplitude
    {d n : ℕ} (σ : Fin d → ℝ) (q : Fin (d * n)) : ℝ :=
  let p : Fin d × Fin n := finProdFinEquiv.symm q
  σ p.1 * (Real.sqrt ((p.2.val : ℝ) + 1))⁻¹

def descendingHarmonicSchmidtPermutation
    {d n : ℕ} (σ : Fin d → ℝ) : Equiv.Perm (Fin (d * n)) :=
  Tuple.sort (fun q : Fin (d * n) =>
    -harmonicTensorSchmidtAmplitude (n := n) σ q)

theorem descendingHarmonicSchmidtPermutation_antitone
    {d n : ℕ} (σ : Fin d → ℝ) :
    Antitone (fun q : Fin (d * n) =>
      harmonicTensorSchmidtAmplitude (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ q)) := by
  intro i j hij
  have h := Tuple.monotone_sort
    (fun q : Fin (d * n) =>
      -harmonicTensorSchmidtAmplitude (n := n) σ q)
    hij
  exact neg_le_neg_iff.mp h

theorem harmonicSchmidtThreshold_card_eq
    {d n : ℕ} (σ : Fin d → ℝ) (x : ℝ) :
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) =
      ∑ i : Fin d,
        (((Finset.univ.filter fun j : Fin n =>
          x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) := by
  classical
  calc
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) =
      ∑ q : Fin (d * n),
        if x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q
          then (1 : ℝ) else 0 := by
            simp
    _ = ∑ p : Fin d × Fin n,
      if x ≤ harmonicTensorSchmidtAmplitude (n := n) σ
          (finProdFinEquiv p)
        then (1 : ℝ) else 0 := by
          exact (Equiv.sum_comp finProdFinEquiv
            (fun q : Fin (d * n) =>
              if x ≤ harmonicTensorSchmidtAmplitude
                (n := n) σ q then (1 : ℝ) else 0)).symm
    _ = ∑ i : Fin d,
        (((Finset.univ.filter fun j : Fin n =>
          x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          simp [harmonicTensorSchmidtAmplitude]

theorem harmonicSchmidtThreshold_count_sq_le_one
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (x : ℝ) (hx : 0 ≤ x) :
    (((Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q).card : ℕ) : ℝ) *
        x ^ 2 ≤ 1 := by
  rw [harmonicSchmidtThreshold_card_eq]
  calc
    (∑ i : Fin d,
      (((Finset.univ.filter fun j : Fin n =>
        x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ)) *
          x ^ 2 =
        ∑ i : Fin d,
          (((Finset.univ.filter fun j : Fin n =>
            x ≤ σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹).card : ℕ) : ℝ) *
              x ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin d, σ i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact harmonicSchmidtFiber_count_sq_le
        (σ i) x (hσ i) hx
    _ = 1 := hunit

theorem descendingHarmonicSchmidtAmplitude_rank_sq_le_one
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    (((k.val : ℝ) + 1) *
      harmonicTensorSchmidtAmplitude (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k) ^ 2) ≤ 1 := by
  classical
  let π := descendingHarmonicSchmidtPermutation
    (n := n) σ
  let x := harmonicTensorSchmidtAmplitude
    (n := n) σ (π k)
  let S : Finset (Fin (d * n)) :=
    Finset.univ.filter fun q : Fin (d * n) =>
      x ≤ harmonicTensorSchmidtAmplitude (n := n) σ q
  have hx : 0 ≤ x := by
    dsimp [x, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hanti :=
    descendingHarmonicSchmidtPermutation_antitone
      (n := n) σ
  have hcard : k.val + 1 ≤ S.card := by
    calc
      k.val + 1 = (Finset.Iic k).card := by simp
      _ = ((Finset.Iic k).map π.toEmbedding).card := by simp
      _ ≤ S.card := by
        apply Finset.card_le_card
        intro q hq
        obtain ⟨l, hl, hleq⟩ := Finset.mem_map.mp hq
        subst q
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact hanti (Finset.mem_Iic.mp hl)
  have hcardreal : (k.val : ℝ) + 1 ≤ (S.card : ℝ) := by
    exact_mod_cast hcard
  have htotal := harmonicSchmidtThreshold_count_sq_le_one
    (n := n) σ hσ hunit x hx
  change ((k.val : ℝ) + 1) * x ^ 2 ≤ 1
  change (S.card : ℝ) * x ^ 2 ≤ 1 at htotal
  exact (mul_le_mul_of_nonneg_right hcardreal
    (sq_nonneg x)).trans htotal

theorem descendingHarmonicSchmidtAmplitude_le_harmonic
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    harmonicTensorSchmidtAmplitude (n := n) σ
      (descendingHarmonicSchmidtPermutation
        (n := n) σ k) ≤
      (Real.sqrt ((k.val : ℝ) + 1))⁻¹ := by
  let x := harmonicTensorSchmidtAmplitude (n := n) σ
    (descendingHarmonicSchmidtPermutation
      (n := n) σ k)
  have hx : 0 ≤ x := by
    dsimp [x, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hrank : 0 < (k.val : ℝ) + 1 := by positivity
  have hsqrt : 0 < Real.sqrt ((k.val : ℝ) + 1) :=
    Real.sqrt_pos.mpr hrank
  have hrankbound :=
    descendingHarmonicSchmidtAmplitude_rank_sq_le_one
      (n := n) σ hσ hunit k
  change x ≤ (Real.sqrt ((k.val : ℝ) + 1))⁻¹
  rw [← one_div]
  apply (le_div_iff₀ hsqrt).2
  have hsquare :
      (x * Real.sqrt ((k.val : ℝ) + 1)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hrank.le]
    nlinarith
  have hnonneg :
      0 ≤ x * Real.sqrt ((k.val : ℝ) + 1) :=
    mul_nonneg hx hsqrt.le
  nlinarith [sq_nonneg
    (x * Real.sqrt ((k.val : ℝ) + 1) + 1)]

def diagonalSchmidtUnitVector
    {d : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    BipartiteUnitVector d := by
  refine ⟨diagonalSchmidtState σ, ?_⟩
  have hsquare := diagonalSchmidtState_norm_sq σ
  rw [hunit] at hsquare
  nlinarith [norm_nonneg (diagonalSchmidtState σ)]

theorem diagonalSchmidtTensorTarget_diagonal
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (q : Fin (d * n)) :
    tensorEmbezzlementTarget (n := n)
      (diagonalSchmidtUnitVector σ hunit) (q, q) =
        (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
          (harmonicTensorSchmidtAmplitude
            (n := n) σ q : ℂ) := by
  simp [tensorEmbezzlementTarget,
    diagonalSchmidtUnitVector,
    diagonalSchmidtState,
    embezzlementState_apply,
    harmonicTensorSchmidtAmplitude,
    mul_assoc, mul_comm]

def harmonicSchmidtPermutationUnitary
    {d n : ℕ} (σ : Fin d → ℝ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ :=
  permutationUnitary
    (descendingHarmonicSchmidtPermutation
      (n := n) σ).symm

theorem harmonicSchmidtPermutationAction_off_diagonal
    {d n : ℕ} (σ : Fin d → ℝ)
    (i j : Fin (d * n)) (hij : i ≠ j) :
    localUnitaryAction
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (embezzlementState (d * n)) (i, j) = 0 := by
  rw [harmonicSchmidtPermutationUnitary,
    localPermutationUnitaryAction_apply,
    embezzlementState_apply]
  have hperm :
      (descendingHarmonicSchmidtPermutation
        (n := n) σ).symm i ≠
      (descendingHarmonicSchmidtPermutation
        (n := n) σ).symm j :=
    (descendingHarmonicSchmidtPermutation
      (n := n) σ).symm.injective.ne hij
  simp [hperm]

theorem harmonicSchmidtPermutationAction_diagonal
    {d n : ℕ} (σ : Fin d → ℝ)
    (k : Fin (d * n)) :
    localUnitaryAction
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (harmonicSchmidtPermutationUnitary (n := n) σ)
      (embezzlementState (d * n))
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k,
          descendingHarmonicSchmidtPermutation
            (n := n) σ k) =
      (‖rawEmbezzlementState (d * n)‖⁻¹ : ℝ) •
        (↑((Real.sqrt ((k.val : ℝ) + 1))⁻¹) : ℂ) := by
  rw [harmonicSchmidtPermutationUnitary,
    localPermutationUnitaryAction_apply,
    embezzlementState_apply]
  simp

theorem harmonicTensorSchmidtAmplitude_sq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (∑ q : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ q ^ 2) =
      harmonicNumber n := by
  have hterm (i : Fin d) (j : Fin n) :
      (σ i * (Real.sqrt ((j.val : ℝ) + 1))⁻¹) ^ 2 =
        σ i ^ 2 * ((j.val : ℝ) + 1)⁻¹ := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  calc
    (∑ q : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ q ^ 2) =
      ∑ p : Fin d × Fin n,
        harmonicTensorSchmidtAmplitude
          (n := n) σ (finProdFinEquiv p) ^ 2 := by
            exact (Equiv.sum_comp finProdFinEquiv
              (fun q : Fin (d * n) =>
                harmonicTensorSchmidtAmplitude
                  (n := n) σ q ^ 2)).symm
    _ = ∑ i : Fin d,
      σ i ^ 2 * harmonicNumber n := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [harmonicTensorSchmidtAmplitude,
          Equiv.symm_apply_apply]
        simp_rw [hterm]
        rw [← Finset.mul_sum]
        rfl
    _ = (∑ i : Fin d, σ i ^ 2) *
      harmonicNumber n := by
        rw [Finset.sum_mul]
    _ = harmonicNumber n := by rw [hunit, one_mul]

theorem descendingHarmonicSchmidtAmplitude_sq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (∑ k : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ
          (descendingHarmonicSchmidtPermutation
            (n := n) σ k) ^ 2) =
      harmonicNumber n := by
  calc
    (∑ k : Fin (d * n),
      harmonicTensorSchmidtAmplitude
        (n := n) σ
          (descendingHarmonicSchmidtPermutation
            (n := n) σ k) ^ 2) =
        ∑ q : Fin (d * n),
          harmonicTensorSchmidtAmplitude
            (n := n) σ q ^ 2 :=
          Equiv.sum_comp
            (descendingHarmonicSchmidtPermutation
              (n := n) σ)
            (fun q : Fin (d * n) =>
              harmonicTensorSchmidtAmplitude
                (n := n) σ q ^ 2)
    _ = harmonicNumber n :=
      harmonicTensorSchmidtAmplitude_sq_sum
        (n := n) σ hunit

def universalCatalystOverlapTerm
    {d n : ℕ} (σ : Fin d → ℝ)
    (k : Fin (d * n)) : ℝ :=
  ‖rawEmbezzlementState (d * n)‖⁻¹ *
    (Real.sqrt ((k.val : ℝ) + 1))⁻¹ *
    ‖rawEmbezzlementState n‖⁻¹ *
    harmonicTensorSchmidtAmplitude
      (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k)

theorem universalCatalystOverlap_eq_sum
    {d n : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    (inner ℂ
      (localUnitaryAction
        (harmonicSchmidtPermutationUnitary (n := n) σ)
        (harmonicSchmidtPermutationUnitary (n := n) σ)
        (embezzlementState (d * n)))
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit))).re =
      ∑ k : Fin (d * n),
        universalCatalystOverlapTerm
          (n := n) σ k := by
  rw [diagonalInner_real_eq_sum _ _
    (harmonicSchmidtPermutationAction_off_diagonal
      (n := n) σ)]
  calc
    (∑ q : Fin (d * n),
      (inner ℂ
        (localUnitaryAction
          (harmonicSchmidtPermutationUnitary (n := n) σ)
          (harmonicSchmidtPermutationUnitary (n := n) σ)
          (embezzlementState (d * n)) (q, q))
        (tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)
          (q, q))).re) =
      ∑ k : Fin (d * n),
        (inner ℂ
          (localUnitaryAction
            (harmonicSchmidtPermutationUnitary (n := n) σ)
            (harmonicSchmidtPermutationUnitary (n := n) σ)
            (embezzlementState (d * n))
            (descendingHarmonicSchmidtPermutation
              (n := n) σ k,
              descendingHarmonicSchmidtPermutation
                (n := n) σ k))
          (tensorEmbezzlementTarget (n := n)
            (diagonalSchmidtUnitVector σ hunit)
            (descendingHarmonicSchmidtPermutation
              (n := n) σ k,
              descendingHarmonicSchmidtPermutation
                (n := n) σ k))).re := by
          exact (Equiv.sum_comp
            (descendingHarmonicSchmidtPermutation
              (n := n) σ)
            (fun q : Fin (d * n) =>
              (inner ℂ
                (localUnitaryAction
                  (harmonicSchmidtPermutationUnitary
                    (n := n) σ)
                  (harmonicSchmidtPermutationUnitary
                    (n := n) σ)
                  (embezzlementState (d * n)) (q, q))
                (tensorEmbezzlementTarget (n := n)
                  (diagonalSchmidtUnitVector σ hunit)
                  (q, q))).re)).symm
    _ = ∑ k : Fin (d * n),
        universalCatalystOverlapTerm
          (n := n) σ k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [harmonicSchmidtPermutationAction_diagonal,
            diagonalSchmidtTensorTarget_diagonal]
          simp [universalCatalystOverlapTerm,
            mul_assoc, mul_comm, mul_left_comm]

theorem universalCatalystOverlapTerm_lower
    {d n : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (k : Fin (d * n)) :
    ‖rawEmbezzlementState (d * n)‖⁻¹ *
      ‖rawEmbezzlementState n‖⁻¹ *
        harmonicTensorSchmidtAmplitude
          (n := n) σ
            (descendingHarmonicSchmidtPermutation
              (n := n) σ k) ^ 2 ≤
      universalCatalystOverlapTerm
        (n := n) σ k := by
  let a := harmonicTensorSchmidtAmplitude
    (n := n) σ
      (descendingHarmonicSchmidtPermutation
        (n := n) σ k)
  let h := (Real.sqrt ((k.val : ℝ) + 1))⁻¹
  let c := ‖rawEmbezzlementState (d * n)‖⁻¹ *
    ‖rawEmbezzlementState n‖⁻¹
  have ha : 0 ≤ a := by
    dsimp [a, harmonicTensorSchmidtAmplitude]
    exact mul_nonneg (hσ _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hah : a ≤ h :=
    descendingHarmonicSchmidtAmplitude_le_harmonic
      (n := n) σ hσ hunit k
  change c * a ^ 2 ≤ _
  calc
    c * a ^ 2 = (c * a) * a := by ring
    _ ≤ (c * a) * h :=
      mul_le_mul_of_nonneg_left hah (mul_nonneg hc ha)
    _ = universalCatalystOverlapTerm
      (n := n) σ k := by
        dsimp [c, a, h, universalCatalystOverlapTerm]
        ring

theorem universalDiagonalCatalystOverlap_lower
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖ ≤
        (inner ℂ
          (localUnitaryAction
            (harmonicSchmidtPermutationUnitary
              (n := n) σ)
            (harmonicSchmidtPermutationUnitary
              (n := n) σ)
            (embezzlementState (d * n)))
          (tensorEmbezzlementTarget (n := n)
            (diagonalSchmidtUnitVector σ hunit))).re := by
  have hnraw : ‖rawEmbezzlementState n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (rawEmbezzlementState_ne_zero n hn)
  have hdnraw :
      ‖rawEmbezzlementState (d * n)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (rawEmbezzlementState_ne_zero
        (d * n) (Nat.mul_pos hd hn))
  calc
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖ =
        ‖rawEmbezzlementState (d * n)‖⁻¹ *
          ‖rawEmbezzlementState n‖⁻¹ *
            harmonicNumber n := by
              rw [← rawEmbezzlementState_norm_sq n]
              field_simp
    _ = ∑ k : Fin (d * n),
      ‖rawEmbezzlementState (d * n)‖⁻¹ *
        ‖rawEmbezzlementState n‖⁻¹ *
          harmonicTensorSchmidtAmplitude
            (n := n) σ
              (descendingHarmonicSchmidtPermutation
                (n := n) σ k) ^ 2 := by
          rw [← descendingHarmonicSchmidtAmplitude_sq_sum
            (n := n) σ hunit, Finset.mul_sum]
    _ ≤ ∑ k : Fin (d * n),
      universalCatalystOverlapTerm
        (n := n) σ k := by
          apply Finset.sum_le_sum
          intro k _
          exact universalCatalystOverlapTerm_lower
            (n := n) σ hσ hunit k
    _ = (inner ℂ
      (localUnitaryAction
        (harmonicSchmidtPermutationUnitary
          (n := n) σ)
        (harmonicSchmidtPermutationUnitary
          (n := n) σ)
        (embezzlementState (d * n)))
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit))).re :=
      (universalCatalystOverlap_eq_sum
        (n := n) σ hunit).symm

def harmonicTargetLiftUnitary
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ := by
  let e : (Fin d × Fin n) ≃ Fin (d * n) :=
    finProdFinEquiv
  let M : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ :=
    (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
  have hM : M ∈ Matrix.unitaryGroup (Fin d × Fin n) ℂ := by
    exact Matrix.kronecker_mem_unitary U.property
      (show (1 : Matrix (Fin n) (Fin n) ℂ) ∈
        Matrix.unitaryGroup (Fin n) ℂ from
          (Matrix.unitaryGroup (Fin n) ℂ).one_mem)
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose,
      Matrix.reindex_apply, Matrix.conjTranspose_apply]
  rw [hstar]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp hM]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

@[simp] theorem harmonicTargetLiftUnitary_apply
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) (i j : Fin n) :
    harmonicTargetLiftUnitary (n := n) U
      (finProdFinEquiv (a, i))
      (finProdFinEquiv (b, j)) =
        if i = j then U a b else 0 := by
  change
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
        (finProdFinEquiv (a, i))
        (finProdFinEquiv (b, j)) = _
  simp [Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem localUnitaryAction_comp
    {m : ℕ}
    (U₁ V₁ U₂ V₂ : Matrix.unitaryGroup (Fin m) ℂ)
    (ψ : EuclideanSpace ℂ (Fin m × Fin m)) :
    localUnitaryAction U₁ V₁
      (localUnitaryAction U₂ V₂ ψ) =
        localUnitaryAction (U₁ * U₂) (V₁ * V₂) ψ := by
  apply WithLp.ofLp_injective
  change
    ((U₁.val ⊗ₖ V₁.val).mulVec
      ((U₂.val ⊗ₖ V₂.val).mulVec (ofLp ψ))) =
      ((U₁ * U₂).val ⊗ₖ (V₁ * V₂).val).mulVec (ofLp ψ)
  rw [Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul]
  rfl

theorem targetCatalystDoubleSum_reindex
    {d n : ℕ}
    (F : Fin (d * n) → Fin (d * n) → ℂ) :
    (∑ i : Fin (d * n), ∑ j : Fin (d * n), F i j) =
      ∑ p : Fin d × Fin n,
        ∑ q : Fin d × Fin n,
          F (finProdFinEquiv p) (finProdFinEquiv q) := by
  calc
    (∑ i : Fin (d * n), ∑ j : Fin (d * n), F i j) =
        ∑ p : Fin d × Fin n,
          ∑ j : Fin (d * n), F (finProdFinEquiv p) j := by
            exact (Equiv.sum_comp finProdFinEquiv
              (fun i : Fin (d * n) =>
                ∑ j : Fin (d * n), F i j)).symm
    _ = ∑ p : Fin d × Fin n,
        ∑ q : Fin d × Fin n,
          F (finProdFinEquiv p) (finProdFinEquiv q) := by
            apply Finset.sum_congr rfl
            intro p _
            exact (Equiv.sum_comp finProdFinEquiv
              (fun j : Fin (d * n) =>
                F (finProdFinEquiv p) j)).symm

theorem harmonicTargetLift_diagonal_action_apply
    {d n : ℕ}
    (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) (i j : Fin n) :
    localUnitaryAction
      (harmonicTargetLiftUnitary (n := n) U)
      (harmonicTargetLiftUnitary (n := n) V)
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit))
        (finProdFinEquiv (a, i),
          finProdFinEquiv (b, j)) =
      schmidtVector σ U V (a, b) *
        embezzlementState n (i, j) := by
  classical
  let LU := harmonicTargetLiftUnitary (n := n) U
  let LV := harmonicTargetLiftUnitary (n := n) V
  let T := tensorEmbezzlementTarget (n := n)
    (diagonalSchmidtUnitVector σ hunit)
  have hT (p q : Fin d × Fin n) :
      T (finProdFinEquiv p, finProdFinEquiv q) =
        (if p.1 = q.1 then (σ p.1 : ℂ) else 0) *
          embezzlementState n (p.2, q.2) := by
    change
      (if (finProdFinEquiv.symm (finProdFinEquiv p)).1 =
          (finProdFinEquiv.symm (finProdFinEquiv q)).1 then
        (σ (finProdFinEquiv.symm (finProdFinEquiv p)).1 : ℂ)
      else 0) *
        embezzlementState n
          ((finProdFinEquiv.symm (finProdFinEquiv p)).2,
            (finProdFinEquiv.symm (finProdFinEquiv q)).2) = _
    simp only [Equiv.symm_apply_apply]
  change
    ((LU.val ⊗ₖ LV.val).mulVec
      (ofLp T))
      (finProdFinEquiv (a, i), finProdFinEquiv (b, j)) = _
  calc
    ((LU.val ⊗ₖ LV.val).mulVec
      (ofLp T))
      (finProdFinEquiv (a, i), finProdFinEquiv (b, j)) =
      ∑ r : Fin (d * n), ∑ s : Fin (d * n),
        LU (finProdFinEquiv (a, i)) r *
          LV (finProdFinEquiv (b, j)) s * T (r, s) := by
            simp [Matrix.mulVec, dotProduct,
              Matrix.kroneckerMap_apply,
              Fintype.sum_prod_type, mul_assoc]
    _ = ∑ p : Fin d × Fin n,
        ∑ q : Fin d × Fin n,
          LU (finProdFinEquiv (a, i)) (finProdFinEquiv p) *
            LV (finProdFinEquiv (b, j)) (finProdFinEquiv q) *
            T (finProdFinEquiv p, finProdFinEquiv q) :=
          targetCatalystDoubleSum_reindex
            (fun r s =>
              LU (finProdFinEquiv (a, i)) r *
                LV (finProdFinEquiv (b, j)) s * T (r, s))
    _ = schmidtVector σ U V (a, b) *
      embezzlementState n (i, j) := by
        simp_rw [hT]
        simp [LU, LV,
          harmonicTargetLiftUnitary_apply,
          schmidtVector_apply,
          Fintype.sum_prod_type,
          mul_assoc, mul_comm, mul_left_comm]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring

theorem harmonicTargetLift_diagonal_action
    {d n : ℕ}
    (ξ : BipartiteUnitVector d)
    (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (hξ : ξ.val = schmidtVector σ U V) :
    localUnitaryAction
      (harmonicTargetLiftUnitary (n := n) U)
      (harmonicTargetLiftUnitary (n := n) V)
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit)) =
      tensorEmbezzlementTarget (n := n) ξ := by
  ext ⟨r, s⟩
  let p : Fin d × Fin n := finProdFinEquiv.symm r
  let q : Fin d × Fin n := finProdFinEquiv.symm s
  have hr : finProdFinEquiv p = r :=
    Equiv.apply_symm_apply finProdFinEquiv r
  have hs : finProdFinEquiv q = s :=
    Equiv.apply_symm_apply finProdFinEquiv s
  calc
    localUnitaryAction
      (harmonicTargetLiftUnitary (n := n) U)
      (harmonicTargetLiftUnitary (n := n) V)
      (tensorEmbezzlementTarget (n := n)
        (diagonalSchmidtUnitVector σ hunit)) (r, s) =
      localUnitaryAction
        (harmonicTargetLiftUnitary (n := n) U)
        (harmonicTargetLiftUnitary (n := n) V)
        (tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit))
          (finProdFinEquiv (p.1, p.2),
            finProdFinEquiv (q.1, q.2)) := by
          simp [hr, hs]
    _ = schmidtVector σ U V (p.1, q.1) *
      embezzlementState n (p.2, q.2) :=
        harmonicTargetLift_diagonal_action_apply
          σ hunit U V p.1 q.1 p.2 q.2
    _ = ξ.val (p.1, q.1) *
      embezzlementState n (p.2, q.2) := by rw [hξ]
    _ = tensorEmbezzlementTarget (n := n) ξ
      (finProdFinEquiv (p.1, p.2),
        finProdFinEquiv (q.1, q.2)) := by
          change _ =
            ξ.val
              ((finProdFinEquiv.symm
                (finProdFinEquiv (p.1, p.2))).1,
                (finProdFinEquiv.symm
                  (finProdFinEquiv (q.1, q.2))).1) *
              embezzlementState n
                ((finProdFinEquiv.symm
                  (finProdFinEquiv (p.1, p.2))).2,
                  (finProdFinEquiv.symm
                    (finProdFinEquiv (q.1, q.2))).2)
          simp only [Equiv.symm_apply_apply]
    _ = tensorEmbezzlementTarget (n := n) ξ (r, s) := by
      simp [hr, hs]

theorem localUnitaryAction_sub
    {m : ℕ}
    (U V : Matrix.unitaryGroup (Fin m) ℂ)
    (z w : EuclideanSpace ℂ (Fin m × Fin m)) :
    localUnitaryAction U V (z - w) =
      localUnitaryAction U V z -
        localUnitaryAction U V w := by
  apply WithLp.ofLp_injective
  change
    ((U.val ⊗ₖ V.val).mulVec
      ((ofLp z) - (ofLp w))) =
        ((U.val ⊗ₖ V.val).mulVec (ofLp z)) -
          ((U.val ⊗ₖ V.val).mulVec (ofLp w))
  exact Matrix.mulVec_sub _ _ _

theorem universalDiagonalCatalystOverlap_of_harmonic_ratio
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hratio : 1 - δ ≤
      harmonicNumber n /
        harmonicNumber (d * n)) :
    1 - δ ≤
      (inner ℂ
        (localUnitaryAction
          (harmonicSchmidtPermutationUnitary
            (n := n) σ)
          (harmonicSchmidtPermutationUnitary
            (n := n) σ)
          (embezzlementState (d * n)))
        (tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit))).re := by
  let q : ℝ :=
    ‖rawEmbezzlementState n‖ /
      ‖rawEmbezzlementState (d * n)‖
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hqsquare :
      q ^ 2 = harmonicNumber n /
        harmonicNumber (d * n) := by
    dsimp [q]
    rw [div_pow,
      rawEmbezzlementState_norm_sq,
      rawEmbezzlementState_norm_sq]
  have hgoalnonneg : 0 ≤ 1 - δ := sub_nonneg.mpr hδone
  have hgoalsquare : (1 - δ) ^ 2 ≤ 1 - δ := by
    nlinarith [mul_nonneg hδ hgoalnonneg]
  have hqbound : 1 - δ ≤ q := by
    rw [← hqsquare] at hratio
    nlinarith [sq_nonneg (q + (1 - δ))]
  exact hqbound.trans
    (universalDiagonalCatalystOverlap_lower
      hd hn σ hσ hunit)

theorem universalDiagonalCatalyst_distance
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hratio : 1 - δ ≤
      harmonicNumber n /
        harmonicNumber (d * n)) :
    ‖localUnitaryAction
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)‖ ≤
      Real.sqrt (2 * δ) := by
  apply unitVector_distance_of_real_overlap
    (localUnitaryAction
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (harmonicSchmidtPermutationUnitary
        (n := n) σ)
      (embezzlementState (d * n)))
    (tensorEmbezzlementTarget (n := n)
      (diagonalSchmidtUnitVector σ hunit))
    (by rw [localUnitaryAction_norm,
      embezzlementState_norm (d * n)
        (Nat.mul_pos hd hn)])
    (tensorEmbezzlementTarget_norm hn
      (diagonalSchmidtUnitVector σ hunit))
    δ hδ
  exact universalDiagonalCatalystOverlap_of_harmonic_ratio
    hd hn σ hσ hunit δ hδ hδone hratio

theorem exists_proofUniversalHarmonicCatalyst
    (d : ℕ) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∀ ξ : BipartiteUnitVector d,
        ∃ U V : Matrix.unitaryGroup (Fin (d * n)) ℂ,
          ‖localUnitaryAction U V
            (embezzlementState (d * n)) -
              tensorEmbezzlementTarget (n := n) ξ‖ ≤ ε := by
  let δ : ℝ := min (ε ^ 2 / 2) 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  obtain ⟨n, hn, hratio⟩ :=
    exists_proofHarmonicNumber_ratio_ge d hd hδ hδone
  refine ⟨n, hn, ?_⟩
  intro ξ
  obtain ⟨σ, U, V, hσ, hunit, hξ⟩ :=
    exists_proofUnitSchmidtDecomposition ξ
  let LU := harmonicTargetLiftUnitary (n := n) U
  let LV := harmonicTargetLiftUnitary (n := n) V
  let P := harmonicSchmidtPermutationUnitary
    (n := n) σ
  refine ⟨LU * P, LV * P, ?_⟩
  have hdiagonal := universalDiagonalCatalyst_distance
    hd hn σ hσ hunit δ hδ.le hδone hratio
  have htarget := harmonicTargetLift_diagonal_action
    (n := n) ξ σ hunit U V hξ
  have hdeltaeps : 2 * δ ≤ ε ^ 2 := by
    have hmin : δ ≤ ε ^ 2 / 2 := min_le_left _ _
    linarith
  have hsqrt : Real.sqrt (2 * δ) ≤ ε := by
    have hsq : (Real.sqrt (2 * δ)) ^ 2 = 2 * δ :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (2 * δ)]
  calc
    ‖localUnitaryAction (LU * P) (LV * P)
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n) ξ‖ =
      ‖localUnitaryAction LU LV
        (localUnitaryAction P P
          (embezzlementState (d * n)) -
            tensorEmbezzlementTarget (n := n)
              (diagonalSchmidtUnitVector σ hunit))‖ := by
        rw [localUnitaryAction_sub,
          localUnitaryAction_comp]
        rw [htarget]
    _ = ‖localUnitaryAction P P
      (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n)
          (diagonalSchmidtUnitVector σ hunit)‖ :=
        localUnitaryAction_norm LU LV _
    _ ≤ Real.sqrt (2 * δ) := hdiagonal
    _ ≤ ε := hsqrt

def coherentSharedRandomControlledUnitary
    {Ω d : Type*}
    [Fintype Ω] [Fintype d]
    [DecidableEq Ω] [DecidableEq d]
    (U : Ω → Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, d) ℂ := by
  refine ⟨Matrix.blockDiagonal' fun ω : Ω =>
    (U ω : Matrix d d ℂ), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  have hblock (ω : Ω) :
      (U ω : Matrix d d ℂ).conjTranspose *
        (U ω : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff').mp (U ω).property
  simp_rw [hblock]
  ext ⟨ω, i⟩ ⟨ν, j⟩
  by_cases hων : ω = ν <;>
    by_cases hij : i = j <;>
      simp [Matrix.blockDiagonal'_apply,
        Matrix.one_apply, hων, hij]

def spectralPartitionPOVM
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) : POVM κ d where
  effect k :=
    ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
      positiveMatrixSpectralAtom F hF i
  positive k := by
    apply Matrix.posSemidef_sum
    intro i _
    exact positiveMatrixSpectralAtom_posSemidef F hF i
  complete := by
    classical
    calc
      (∑ k : κ,
        ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
          positiveMatrixSpectralAtom F hF i) =
        ∑ i : d, positiveMatrixSpectralAtom F hF i := by
          simp [Finset.sum_filter, Finset.sum_comm]
      _ = 1 := positiveMatrixSpectralAtom_sum F hF

theorem spectralPartitionPOVM_projective
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) (k : κ) :
    (spectralPartitionPOVM F hF bin).effect k *
      (spectralPartitionPOVM F hF bin).effect k =
        (spectralPartitionPOVM F hF bin).effect k := by
  exact spectralAtomSum_mul_self F hF
    (Finset.univ.filter (fun i : d => bin i = k))

def bilateralWorkPairEquiv
    {ι d e : Type*} :
    ((ι → d) × (ι → e)) ≃ (ι → d × e) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv x := by
    rcases x with ⟨a, b⟩
    rfl
  right_inv x := by
    funext i
    exact Prod.eta (x i)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

theorem spectralPartitionPOVM_trace_eq_atom_count
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) (k : κ) :
    (Matrix.trace
      ((spectralPartitionPOVM F hF bin).effect k)).re =
      ∑ i : d, if bin i = k then (1 : ℝ) else 0 := by
  classical
  simp [spectralPartitionPOVM,
    Matrix.trace_sum, spectralAtom_trace]

theorem spectralPartitionPOVM_trace_mul_eq_atom_overlap
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (binF binG : d → κ) (k : κ) :
    (Matrix.trace
      ((spectralPartitionPOVM F hF binF).effect k *
        (spectralPartitionPOVM G hG binG).effect k)).re =
      ∑ i ∈ (Finset.univ.filter fun i : d => binF i = k),
        ∑ j ∈ (Finset.univ.filter fun j : d => binG j = k),
          spectralAtomOverlap F G hF hG i j := by
  classical
  simp [spectralPartitionPOVM,
    spectralAtomOverlap,
    Matrix.sum_mul, Matrix.mul_sum,
    Matrix.trace_sum]
  rw [Finset.sum_comm]

theorem spectralPartitionPOVM_weighted_trace_deficit_eq_mismatch
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (binF binG : d → κ)
    (τ : κ → ℝ) :
    (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM G hG binG).effect k)).re) -
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM F hF binF).effect k *
            (spectralPartitionPOVM G hG binG).effect k)).re) =
      ∑ i : d, ∑ j : d,
        if binF i = binG j then 0
        else τ (binG j) ^ 2 *
          spectralAtomOverlap F G hF hG i j := by
  classical
  let w : d → d → ℝ :=
    spectralAtomOverlap F G hF hG
  have hQ :
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM G hG binG).effect k)).re) =
        ∑ j : d, τ (binG j) ^ 2 := by
    simp_rw [spectralPartitionPOVM_trace_eq_atom_count]
    calc
      (∑ k : κ, τ k ^ 2 *
        (∑ j : d, if binG j = k then (1 : ℝ) else 0)) =
          ∑ k : κ, ∑ j : d,
            if binG j = k then τ k ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              split_ifs <;> simp
      _ = ∑ j : d, ∑ k : κ,
          if binG j = k then τ k ^ 2 else 0 :=
            Finset.sum_comm
      _ = ∑ j : d, τ (binG j) ^ 2 := by
            simp
  have hPQ :
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace
          ((spectralPartitionPOVM F hF binF).effect k *
            (spectralPartitionPOVM G hG binG).effect k)).re) =
        ∑ i : d, ∑ j : d,
          if binF i = binG j then
            τ (binG j) ^ 2 * w i j
          else 0 := by
    have hsingle (k : κ) :
        τ k ^ 2 *
          (Matrix.trace
            ((spectralPartitionPOVM F hF binF).effect k *
              (spectralPartitionPOVM G hG binG).effect k)).re =
          ∑ i : d, ∑ j : d,
            if binF i = k ∧ binG j = k then
              τ k ^ 2 * w i j
            else 0 := by
      rw [spectralPartitionPOVM_trace_mul_eq_atom_overlap]
      dsimp [w]
      simp only [Finset.sum_filter, Finset.mul_sum,
        mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : binF i = k
      · simp [hi]
      · simp [hi]
    simp_rw [hsingle]
    calc
      (∑ k : κ, ∑ i : d, ∑ j : d,
        if binF i = k ∧ binG j = k then
          τ k ^ 2 * w i j
        else 0) =
          ∑ i : d, ∑ j : d, ∑ k : κ,
            if binF i = k ∧ binG j = k then
              τ k ^ 2 * w i j
            else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
      _ = ∑ i : d, ∑ j : d,
          if binF i = binG j then
            τ (binG j) ^ 2 * w i j
          else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            have reindex (k : κ) :
                (if binF i = k ∧ binG j = k then
                  τ k ^ 2 * w i j
                else 0) =
                  if binG j = k then
                    if binF i = binG j then
                      τ (binG j) ^ 2 * w i j
                    else 0
                  else 0 := by
              by_cases hk : binG j = k
              · subst k
                simp
              · simp [hk]
            simp_rw [reindex]
            simp
  rw [hQ, hPQ]
  have hcolumn : ∀ j : d, (∑ i : d, w i j) = 1 :=
    spectralAtomOverlap_sum_left F G hF hG
  have hfirst :
      (∑ j : d, τ (binG j) ^ 2) =
        ∑ i : d, ∑ j : d,
          τ (binG j) ^ 2 * w i j := by
    calc
      (∑ j : d, τ (binG j) ^ 2) =
          ∑ j : d,
            τ (binG j) ^ 2 * (∑ i : d, w i j) := by
              simp_rw [hcolumn]
              simp
      _ = ∑ i : d, ∑ j : d,
          τ (binG j) ^ 2 * w i j := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
  rw [hfirst, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [w]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

def finiteUniformThresholdGrid
    (lower upper : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  lower + (k.val : ℝ) * ((upper - lower) / (N : ℝ))

def finiteUniformThresholdCrossing
    (lower upper a b : ℝ) (N : ℕ) : ℝ :=
  ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
    (N : ℝ)

theorem finiteUniformGrid_interval_card_le
    (N : ℕ) (offset step lo hi : ℝ)
    (positive : 0 < step)
    (ordered : lo ≤ hi) :
    (((Finset.univ.filter fun k : Fin N =>
      lo ≤ offset + (k.val : ℝ) * step ∧
        offset + (k.val : ℝ) * step ≤ hi).card : ℕ) : ℝ) ≤
      (hi - lo) / step + 1 := by
  classical
  let selected : Finset (Fin N) :=
    Finset.univ.filter fun k : Fin N =>
      lo ≤ offset + (k.val : ℝ) * step ∧
        offset + (k.val : ℝ) * step ≤ hi
  change (selected.card : ℝ) ≤ (hi - lo) / step + 1
  by_cases present : selected.Nonempty
  · let first : Fin N := selected.min' present
    let last : Fin N := selected.max' present
    have first_mem : first ∈ selected :=
      Finset.min'_mem selected present
    have last_mem : last ∈ selected :=
      Finset.max'_mem selected present
    have interval : selected ⊆ Finset.Icc first last := by
      intro k hk
      apply Finset.mem_Icc.mpr
      constructor
      · exact Finset.min'_le selected k hk
      · exact Finset.le_max' selected k hk
    have cardinal : selected.card ≤
        last.val + 1 - first.val := by
      have h := Finset.card_le_card interval
      simpa using h
    have ordered_indices : first.val ≤ last.val := by
      change (selected.min' present).val ≤ (selected.max' present).val
      exact Finset.min'_le_max' selected present
    have nat_bound : first.val ≤ last.val + 1 := by omega
    have real_cardinal :
        (selected.card : ℝ) ≤
          (last.val : ℝ) + 1 - (first.val : ℝ) := by
      exact_mod_cast cardinal
    have first_lower : lo ≤ offset + (first.val : ℝ) * step :=
      (Finset.mem_filter.mp first_mem).2.1
    have last_upper : offset + (last.val : ℝ) * step ≤ hi :=
      (Finset.mem_filter.mp last_mem).2.2
    have spread :
        ((last.val : ℝ) - (first.val : ℝ)) * step ≤ hi - lo := by
      nlinarith
    have scaled :
        (last.val : ℝ) - (first.val : ℝ) ≤
          (hi - lo) / step :=
      (le_div_iff₀ positive).2 spread
    linarith
  · have empty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp present
    rw [empty, Finset.card_empty, Nat.cast_zero]
    have difference : 0 ≤ hi - lo := sub_nonneg.mpr ordered
    exact add_nonneg (div_nonneg difference positive.le)
      (by norm_num)

theorem finiteUniformThresholdCrossing_le
    {lower upper : ℝ}
    (window : lower < upper)
    (a b : ℝ)
    (N : ℕ) (nonempty : 0 < N) :
    finiteUniformThresholdCrossing lower upper a b N ≤
      |a - b| / (upper - lower) + 1 / (N : ℝ) := by
  have realN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast nonempty
  have width : 0 < upper - lower := sub_pos.mpr window
  have step : 0 < (upper - lower) / (N : ℝ) :=
    div_pos width realN
  have count := finiteUniformGrid_interval_card_le
    N lower ((upper - lower) / (N : ℝ))
    (min a b) (max a b) step min_le_max
  change
    ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
      (N : ℝ) ≤ _
  have same_count :
      ((Finset.univ.filter fun k : Fin N =>
        min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
          finiteUniformThresholdGrid lower upper N k ≤
            max a b).card : ℝ) ≤
        (max a b - min a b) /
          ((upper - lower) / (N : ℝ)) + 1 := by
    simpa [finiteUniformThresholdGrid] using count
  calc
    ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
      (N : ℝ) ≤
        ((max a b - min a b) /
          ((upper - lower) / (N : ℝ)) + 1) / (N : ℝ) :=
      div_le_div_of_nonneg_right same_count realN.le
    _ = |a - b| / (upper - lower) + 1 / (N : ℝ) := by
      rw [max_sub_min_eq_abs]
      have habs : |b - a| = |a - b| := abs_sub_comm b a
      rw [habs]
      field_simp [realN.ne', width.ne']

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem localUnitaryPureResidual_targetLocalInverse_reset
    {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n × Fin n)) :
    localUnitaryAction U⁻¹ V⁻¹
        (localUnitaryAction U V x) = x := by
  rw [localUnitaryAction_comp,
    inv_mul_cancel, inv_mul_cancel]
  simp [localUnitaryAction]

def targetCoefficientMatrix
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun b a => ξ.val (a, b)

theorem targetCoefficientMatrix_vec
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    toLp 2 (Matrix.vec (targetCoefficientMatrix ξ)) = ξ.val := by
  ext ⟨a, b⟩
  rfl

def targetReducedDensity
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (targetCoefficientMatrix ξ).conjTranspose *
    targetCoefficientMatrix ξ

theorem targetReducedDensity_posSemidef
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    (targetReducedDensity ξ).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self
    (targetCoefficientMatrix ξ)

theorem targetReducedDensity_trace
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.trace (targetReducedDensity ξ) = 1 := by
  have vectorized := matrixVectorization_inner
    (targetCoefficientMatrix ξ)
    (targetCoefficientMatrix ξ)
  rw [targetCoefficientMatrix_vec,
    inner_self_eq_one_of_norm_eq_one ξ.property] at vectorized
  exact vectorized.symm

theorem targetSpectralAtom_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (i a b : d) :
    positiveMatrixSpectralAtom F hF i a b =
      (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) a i *
        star ((hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) b i) := by
  classical
  simp [positiveMatrixSpectralAtom, spectralConjugationCLM_apply,
    Matrix.mul_apply, Matrix.diagonal_apply,
    Pi.single_apply]

theorem targetSpectralAtomOverlap_eq_basis_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) :
    spectralAtomOverlap F G hF hG i j =
      ‖unitaryBasisOverlap
        hF.isHermitian.eigenvectorUnitary
        hG.isHermitian.eigenvectorUnitary i j‖ ^ 2 := by
  classical
  let U : Matrix d d ℂ := hF.isHermitian.eigenvectorUnitary
  let V : Matrix d d ℂ := hG.isHermitian.eigenvectorUnitary
  let z : ℂ := ∑ a : d, star (U a i) * V a j
  have cross :
      Matrix.trace
        (positiveMatrixSpectralAtom F hF i *
          positiveMatrixSpectralAtom G hG j) = star z * z := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      targetSpectralAtom_apply]
    change
      (∑ a : d, ∑ b : d,
        (U a i * star (U b i)) *
          (V b j * star (V a j))) = star z * z
    dsimp [z]
    rw [map_sum, Finset.sum_mul]
    simp only [map_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [starRingEnd_apply, star_star]
    ring
  unfold spectralAtomOverlap
  rw [cross]
  have coeff :
      unitaryBasisOverlap
        hF.isHermitian.eigenvectorUnitary
        hG.isHermitian.eigenvectorUnitary i j = z := by
    simp [unitaryBasisOverlap_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, U, V, z]
  rw [coeff, ← Complex.normSq_eq_norm_sq]
  change (star z * z).re = Complex.normSq z
  simpa [Complex.star_def] using
    (congrArg Complex.re
      (@Complex.normSq_eq_conj_mul_self z)).symm

end

noncomputable section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072

def targetCanonicalSchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((targetReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

theorem targetCanonicalSchmidtCoefficient_nonneg
    {d : ℕ} (ξ : BipartiteUnitVector d) (i : Fin d) :
    0 ≤ targetCanonicalSchmidtCoefficient ξ i :=
  Real.sqrt_nonneg _

theorem targetCanonicalSchmidtCoefficient_sq_sum
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    (∑ i : Fin d, targetCanonicalSchmidtCoefficient ξ i ^ 2) = 1 := by
  unfold targetCanonicalSchmidtCoefficient
  simp_rw [Real.sq_sqrt
    ((targetReducedDensity_posSemidef ξ).eigenvalues_nonneg _)]
  exact positiveDensity_eigenvalues_sum
    (targetReducedDensity ξ)
    (targetReducedDensity_posSemidef ξ)
    (targetReducedDensity_trace ξ)

theorem exists_proofTargetCanonicalSpectralSchmidtDecomposition
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ∃ (V : Matrix.unitaryGroup (Fin d) ℂ),
      ξ.val = schmidtVector
        (targetCanonicalSchmidtCoefficient ξ)
        (conjugateUnitary
          (targetReducedDensity_posSemidef ξ).isHermitian.eigenvectorUnitary)
        V := by
  classical
  let C : Matrix (Fin d) (Fin d) ℂ := targetCoefficientMatrix ξ
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d) := Matrix.toEuclideanLin C
  let hF := targetReducedDensity_posSemidef ξ
  let v : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)) := hF.isHermitian.eigenvectorBasis
  let σ : Fin d → ℝ := targetCanonicalSchmidtCoefficient ξ
  have hσ (i : Fin d) : 0 ≤ σ i :=
    targetCanonicalSchmidtCoefficient_nonneg ξ i
  have hσsq (i : Fin d) :
      σ i ^ 2 = hF.isHermitian.eigenvalues i := by
    exact Real.sq_sqrt (hF.eigenvalues_nonneg i)
  have heigen (i : Fin d) :
      (T.adjoint ∘ₗ T) (v i) = ((σ i ^ 2 : ℝ) : ℂ) • v i := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change
      toLp 2
        (C.conjTranspose.mulVec
          (C.mulVec (ofLp (v i)))) =
        ((σ i ^ 2 : ℝ) : ℂ) • v i
    rw [Matrix.mulVec_mulVec]
    have spectral := hF.isHermitian.mulVec_eigenvectorBasis i
    change
      (C.conjTranspose * C).mulVec
        (ofLp (v i)) =
        (hF.isHermitian.eigenvalues i) • (ofLp (v i)) at spectral
    rw [spectral, ← hσsq]
    rfl
  let s : Set (Fin d) := {i | σ i ≠ 0}
  let f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun i => ((σ i : ℂ)⁻¹) • T (v i)
  have hGram (i j : Fin d) :
      inner ℂ (T (v i)) (T (v j)) =
        ((σ j ^ 2 : ℝ) : ℂ) * inner ℂ (v i) (v j) := by
    calc
      inner ℂ (T (v i)) (T (v j)) =
          inner ℂ (v i) (T.adjoint (T (v j))) :=
        (T.adjoint_inner_right (v i) (T (v j))).symm
      _ = inner ℂ (v i) (((σ j ^ 2 : ℝ) : ℂ) • v j) := by
        rw [← heigen j]
        rfl
      _ = _ := by rw [inner_smul_right]
  have hf : Orthonormal ℂ (s.restrict f) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (σ (i : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast i.property
    have hj : (σ (j : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast j.property
    change inner ℂ
      (((σ (i : Fin d) : ℂ)⁻¹) • T (v i))
      (((σ (j : Fin d) : ℂ)⁻¹) • T (v j)) = _
    rw [inner_smul_left, inner_smul_right, hGram,
      v.inner_eq_ite]
    by_cases same : i = j
    · subst j
      simp only [ite_true, mul_one]
      have real_star :
          starRingEnd ℂ ((σ (i : Fin d) : ℂ)⁻¹) =
            ((σ (i : Fin d) : ℂ)⁻¹) := by simp
      rw [real_star]
      push_cast
      field_simp
    · have unequal : (i : Fin d) ≠ (j : Fin d) := by
        intro equal
        exact same (Subtype.ext equal)
      simp [same, unequal]
  obtain ⟨u, hu⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by
        rw [Fintype.card_fin]
        exact finrank_euclideanSpace_fin) hf
  have singular (i : Fin d) :
      T (v i) = (σ i : ℂ) • u i := by
    by_cases zero : σ i = 0
    · have kernel : (T.adjoint ∘ₗ T) (v i) = 0 := by
        rw [heigen i, zero]
        simp
      have image : T (v i) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [← T.ker_adjoint_comp_self]
        exact LinearMap.mem_ker.mpr kernel
      simp [zero, image]
    · have chosen : u i = f i := hu i zero
      rw [chosen]
      change T (v i) =
        (σ i : ℂ) • (((σ i : ℂ)⁻¹) • T (v i))
      rw [smul_smul, mul_inv_cancel₀]
      · simp
      · exact_mod_cast zero
  refine ⟨orthonormalBasisUnitary u, ?_⟩
  have eigen_unitary :
      orthonormalBasisUnitary v =
        hF.isHermitian.eigenvectorUnitary := rfl
  ext ⟨a, b⟩
  rw [schmidtVector_apply]
  have repr :
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
        ∑ i : Fin d,
          inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
            T (v i) := by
    calc
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
          T (∑ i : Fin d,
            inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
              v i) := by rw [v.sum_repr']
      _ = _ := by simp
  have coordinate := congrArg
    (fun z : EuclideanSpace ℂ (Fin d) => z b) repr
  have replace :
      conjugateUnitary
          hF.isHermitian.eigenvectorUnitary =
        conjugateUnitary
          (orthonormalBasisUnitary v) := by
    rw [eigen_unitary]
  rw [replace]
  simpa [T, C, σ, targetCoefficientMatrix, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, EuclideanSpace.inner_single_right,
    conjugateUnitary_apply,
    orthonormalBasisUnitary_apply, singular,
    mul_assoc, mul_left_comm, mul_comm] using coordinate

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem conjugateUnitaryBasisOverlap_norm_sq
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    ‖unitaryBasisOverlap
      (conjugateUnitary U)
      (conjugateUnitary V) i j‖ ^ 2 =
      ‖unitaryBasisOverlap U V i j‖ ^ 2 := by
  have hconj :
      unitaryBasisOverlap
        (conjugateUnitary U)
        (conjugateUnitary V) i j =
        star (unitaryBasisOverlap U V i j) := by
    simp [unitaryBasisOverlap_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      conjugateUnitary_apply]
  rw [hconj, norm_star]

def targetCanonicalSpectralEnergy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF := targetReducedDensity_posSemidef ξ
  let hG := targetReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    (Real.sqrt (hF.isHermitian.eigenvalues i) -
      Real.sqrt (hG.isHermitian.eigenvalues j)) ^ 2 *
      spectralAtomOverlap F G hF hG i j

theorem targetCanonicalSpectralEnergy_le_of_canonicalSchmidt
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (V W : Matrix.unitaryGroup (Fin d) ℂ)
    (hξ :
      ξ.val = schmidtVector
        (fun i => Real.sqrt
          ((targetReducedDensity_posSemidef ξ).isHermitian.eigenvalues i))
        (conjugateUnitary
          (targetReducedDensity_posSemidef ξ).isHermitian.eigenvectorUnitary)
        V)
    (hζ :
      ζ.val = schmidtVector
        (fun j => Real.sqrt
          ((targetReducedDensity_posSemidef ζ).isHermitian.eigenvalues j))
        (conjugateUnitary
          (targetReducedDensity_posSemidef ζ).isHermitian.eigenvectorUnitary)
        W) :
    targetCanonicalSpectralEnergy ξ ζ ≤
      2 * ‖ξ.val - ζ.val‖ ^ 2 := by
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF : F.PosSemidef := targetReducedDensity_posSemidef ξ
  let hG : G.PosSemidef := targetReducedDensity_posSemidef ζ
  have hFtrace : Matrix.trace F = 1 :=
    targetReducedDensity_trace ξ
  have hGtrace : Matrix.trace G = 1 :=
    targetReducedDensity_trace ζ
  have hσunit :
      (∑ i : Fin d, (Real.sqrt (hF.isHermitian.eigenvalues i)) ^ 2) = 1 := by
    simp_rw [Real.sq_sqrt (hF.eigenvalues_nonneg _)]
    exact positiveDensity_eigenvalues_sum F hF hFtrace
  have hμunit :
      (∑ j : Fin d, (Real.sqrt (hG.isHermitian.eigenvalues j)) ^ 2) = 1 := by
    simp_rw [Real.sq_sqrt (hG.eigenvalues_nonneg _)]
    exact positiveDensity_eigenvalues_sum G hG hGtrace
  have henergy := schmidtVector_spectralEnergy_le
    (fun i => Real.sqrt (hF.isHermitian.eigenvalues i))
    (fun j => Real.sqrt (hG.isHermitian.eigenvalues j))
    (fun i => Real.sqrt_nonneg _)
    (fun j => Real.sqrt_nonneg _)
    hσunit hμunit
    (conjugateUnitary hF.isHermitian.eigenvectorUnitary) V
    (conjugateUnitary hG.isHermitian.eigenvectorUnitary) W
  simp_rw [conjugateUnitaryBasisOverlap_norm_sq,
    ← targetSpectralAtomOverlap_eq_basis_norm_sq F G hF hG] at henergy
  change targetCanonicalSpectralEnergy ξ ζ ≤
    2 * ‖ξ.val - ζ.val‖ ^ 2
  simpa [targetCanonicalSpectralEnergy, F, G, hF, hG, hξ, hζ]
    using henergy

theorem targetCanonicalSpectralEnergy_le
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    targetCanonicalSpectralEnergy ξ ζ ≤
      2 * ‖ξ.val - ζ.val‖ ^ 2 := by
  obtain ⟨V, hξ⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition ξ
  obtain ⟨W, hζ⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition ζ
  apply targetCanonicalSpectralEnergy_le_of_canonicalSchmidt
    ξ ζ V W
  · exact hξ
  · exact hζ

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

theorem harmonicCoherentSharedResource_inverseAbsorption_distance
    {d n : ℕ}
    (U V : Matrix.unitaryGroup (Fin (d * n)) ℂ)
    (resource : BipartiteUnitVector d) :
    ‖localUnitaryAction U⁻¹ V⁻¹
        (tensorEmbezzlementTarget (n := n) resource) -
      embezzlementState (d * n)‖ =
      ‖localUnitaryAction U V
          (embezzlementState (d * n)) -
        tensorEmbezzlementTarget (n := n) resource‖ := by
  have reset :
      localUnitaryAction U V
        (localUnitaryAction U⁻¹ V⁻¹
          (tensorEmbezzlementTarget (n := n) resource)) =
        tensorEmbezzlementTarget (n := n) resource := by
    simpa using
      (localUnitaryPureResidual_targetLocalInverse_reset
        U⁻¹ V⁻¹
        (tensorEmbezzlementTarget (n := n) resource))
  calc
    _ = ‖localUnitaryAction U V
        (localUnitaryAction U⁻¹ V⁻¹
          (tensorEmbezzlementTarget (n := n) resource) -
          embezzlementState (d * n))‖ :=
      (localUnitaryAction_norm U V _).symm
    _ = ‖tensorEmbezzlementTarget (n := n) resource -
          localUnitaryAction U V
            (embezzlementState (d * n))‖ := by
      rw [localUnitaryAction_sub, reset]
    _ = _ := norm_sub_rev _ _

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

theorem dSVProjectorSquaredDifference_trace
    {d : Type*} [Fintype d] [DecidableEq d]
    (P Q : Matrix d d ℂ)
    (hP : P * P = P) (hQ : Q * Q = Q) :
    (Matrix.trace ((P - Q) * (P - Q))).re =
      (Matrix.trace P).re + (Matrix.trace Q).re -
        2 * (Matrix.trace (P * Q)).re := by
  have complex :
      Matrix.trace ((P - Q) * (P - Q)) =
        Matrix.trace P + Matrix.trace Q -
          2 * Matrix.trace (P * Q) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
      hP, hQ, Matrix.trace_mul_comm Q P]
    ring
  rw [complex]
  simp

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

theorem dSVCanonicalFailurePrefix_card
    {d : ℕ} (r : Fin (d + 1)) :
    (Finset.univ.filter
      (fun i : Fin d => i.val < r.val)).card = r.val := by
  classical
  calc
    (Finset.univ.filter
      (fun i : Fin d => i.val < r.val)).card =
        (Finset.range r.val).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i member
        exact Finset.mem_range.mpr (Finset.mem_filter.mp member).2
      · intro i _ j _ equal
        exact Fin.ext equal
      · intro j member
        have before : j < r.val := Finset.mem_range.mp member
        have bounded : j < d := by
          have endpoint : r.val ≤ d := by omega
          omega
        refine ⟨⟨j, bounded⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, before⟩
    _ = r.val := Finset.card_range _

def dSVCanonicalFailurePrefix
    {d : ℕ} (r : Fin (d + 1)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    if q.1 = q.2 ∧ q.1.val < r.val then 1 else 0

theorem dSVCanonicalFailurePrefix_norm_sq
    {d : ℕ} (r : Fin (d + 1)) :
    ‖dSVCanonicalFailurePrefix r‖ ^ 2 = (r.val : ℝ) := by
  classical
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  change
    (∑ i : Fin d, ∑ j : Fin d,
      ‖if i = j ∧ i.val < r.val then (1 : ℂ) else 0‖ ^ 2) =
      (r.val : ℝ)
  have atom (i j : Fin d) :
      ‖if i = j ∧ i.val < r.val then (1 : ℂ) else 0‖ ^ 2 =
        if i = j then if i.val < r.val then (1 : ℝ) else 0
        else 0 := by
    by_cases same : i = j
    · subst j
      by_cases before : i.val < r.val <;> simp [before]
    · simp [same]
  simp_rw [atom]
  have count := dSVCanonicalFailurePrefix_card r
  simpa [Finset.sum_boole] using congrArg
    (fun n : ℕ => (n : ℝ)) count

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

theorem dSVProjectorComplement_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Matrix d d ℂ) (positive : P.PosSemidef)
    (projective : P * P = P) :
    (1 - P).PosSemidef := by
  have gram :
      (1 - P).conjTranspose * (1 - P) = (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      positive.isHermitian.eq]
    simp [Matrix.sub_mul, Matrix.mul_sub, projective]
  rw [← gram]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

theorem dSVCanonicalFailurePrefix_inner
    {d : ℕ} (r s : Fin (d + 1)) :
    inner ℂ (dSVCanonicalFailurePrefix r)
        (dSVCanonicalFailurePrefix s) =
      (min r.val s.val : ℕ) := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    (∑ q : Fin d × Fin d,
      (if q.1 = q.2 ∧ q.1.val < s.val then (1 : ℂ) else 0) *
        star (if q.1 = q.2 ∧ q.1.val < r.val
          then (1 : ℂ) else 0)) =
      (min r.val s.val : ℕ)
  rw [Fintype.sum_prod_type]
  change
    (∑ i : Fin d, ∑ j : Fin d,
      (if i = j ∧ i.val < s.val then (1 : ℂ) else 0) *
        star (if i = j ∧ i.val < r.val then (1 : ℂ) else 0)) =
      (min r.val s.val : ℕ)
  have atom (i j : Fin d) :
      (if i = j ∧ i.val < s.val then (1 : ℂ) else 0) *
        star (if i = j ∧ i.val < r.val then (1 : ℂ) else 0) =
        if i = j then
          if i.val < min r.val s.val then (1 : ℂ) else 0
        else 0 := by
    by_cases same : i = j
    · subst j
      by_cases belowr : i.val < r.val
      · by_cases belows : i.val < s.val
        · simp [belowr, belows]
        · simp [belowr, belows]
      · by_cases belows : i.val < s.val
        · simp [belowr, belows]
        · simp [belowr, belows]
    · simp [same]
  simp_rw [atom]
  let t : Fin (d + 1) := ⟨min r.val s.val, by
    have hr : r.val ≤ d := by omega
    have hs : s.val ≤ d := by omega
    omega⟩
  have counted := dSVCanonicalFailurePrefix_card t
  have cast_counted := congrArg (fun n : ℕ => (n : ℂ)) counted
  simpa [t, Finset.sum_boole] using cast_counted

theorem dSVCanonicalFailurePrefix_sub_norm_sq
    {d : ℕ} (r s : Fin (d + 1)) :
    ‖dSVCanonicalFailurePrefix r -
        dSVCanonicalFailurePrefix s‖ ^ 2 =
      |(r.val : ℝ) - (s.val : ℝ)| := by
  rw [@norm_sub_sq ℂ,
    dSVCanonicalFailurePrefix_norm_sq,
    dSVCanonicalFailurePrefix_norm_sq,
    dSVCanonicalFailurePrefix_inner]
  change
    (r.val : ℝ) - 2 * (min r.val s.val : ℕ) + (s.val : ℝ) =
      |(r.val : ℝ) - (s.val : ℝ)|
  by_cases order : r.val ≤ s.val
  · rw [min_eq_left order, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast order)
  · have opposite : s.val ≤ r.val := Nat.le_of_not_ge order
    rw [min_eq_right opposite, abs_of_nonneg]
    · ring
    · exact sub_nonneg.mpr (by exact_mod_cast opposite)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVRankControlledTargetCatalystIndexEquiv
    {ι : Type*} [Fintype ι]
    (d n : ℕ) :
    ((Fin d × ι) × Fin n) ≃
      Fin (d * (Fintype.card ι * n)) :=
  (Equiv.prodAssoc (Fin d) ι (Fin n)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin d))
      ((Equiv.prodCongr (Fintype.equivFin ι)
        (Equiv.refl (Fin n))).trans finProdFinEquiv)).trans
      finProdFinEquiv)

end

end QuantumParallelRepetition

end
