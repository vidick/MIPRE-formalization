import Mathlib

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

namespace QuantumParallelRepetition

variable {X Y A B : Type*}

structure Game (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : (∑ x : X, ∑ y : Y, questionWeight x y) = 1
  predicate : X → Y → A → B → Bool

namespace Game

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

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

namespace Strategy

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

def jointEffect (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  (S.aliceMeasurement x).effect a ⊗ₖ (S.bobMeasurement y).effect b

def outcomeProbability (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (Matrix.trace (S.state.matrix * S.jointEffect x y a b)).re

def winProbability (S : Strategy G) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then S.outcomeProbability x y a b else 0

end Strategy

def entangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) : ℝ :=
  sSup (Set.range (Strategy.winProbability (G := G)))

def repeatedEntangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) : ℝ :=
  entangledValue (G.repeat n)

def HasExponentialBound (v : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, v n ≤ C * Real.exp (-c * (n : ℝ))

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def StandardQuantumParallelRepetition (G : Game X Y A B) : Prop :=
  entangledValue G < 1 →
    HasExponentialBound (repeatedEntangledValue G)

theorem distributionUniformExponential :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) := by
  sorry

theorem standardQuantumParallelRepetition
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    StandardQuantumParallelRepetition G := by
  sorry

end QuantumParallelRepetition

end
