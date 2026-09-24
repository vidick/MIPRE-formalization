/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games
import MIPRE.Foundations.RegisterReindex
import MIPRE.LCS.EPR

/-!
# The nonlocal game of a linear constraint system

This file interprets an LCS instance (`MIPRE.LCS.Game`) as a two-player one-round
nonlocal game in the sense of `MIPRE.Game`, connecting the operator-algebraic
perfect-play formalism of `MIPRE.LCS` with the game-value framework of
`MIPRE.Foundations.Games`.

## The game is symmetric in the players

Both players receive questions from the same alphabet `Fin G.r ⊕ Fin G.s` --- an equation
or a variable --- and answer in the same alphabet `(Fin G.s → ZMod 2) ⊕ ZMod 2` --- an
assignment or a bit. The referee samples an incidence `(i, j)` with `j ∈ G.V i` and then a
uniform *orientation*: one player is asked the equation and the other the variable. So there
are `2 r |V i|`-many equiprobable oriented pairs, and both players have measurements at both
kinds of question.

That is deliberate, and it is what the literature's `game^MS` means. An earlier version of
this file sent the equation to Alice and the variable to Bob always. Nothing in the repository
depended on that choice, and it made statements about *both* players' variable observables ---
which is what the Pauli basis test consumes from the Magic Square, blueprint
`lem:ms-direct-anticomm` --- inexpressible: Alice never received a variable question, so
`A^{Variable_j}` did not exist. The orientation also fixes the constant of that lemma: the sum
of the conditional failures over the oriented incidences is `2 r |V i|` times the failure
probability rather than `r |V i|` times it.

## The decider checks the shape

`Game.accepts` rejects an answer whose shape does not match its question, and rejects an
off-support pair `(i, j)` with `j ∉ G.V i`. Neither check is redundant with the question
distribution vanishing there. `reports/clgame-format-check-missing.md` records what a missing
format check cost the seeded CL game: the test became vacuous and a soundness theorem about it
false. The `accepts_*` simp lemmas below and the
`decide`-checked witnesses in `MIPRE/LCS/MagicSquare/Game.lean` --- an accepted pair in each
orientation, and one rejected for each of the three reasons --- are the guard against a
repeat.

## Main definitions

- `MIPRE.LCS.Layout.Question`, `MIPRE.LCS.Layout.Answer`: the shared question and answer
  alphabets;
- `MIPRE.LCS.Layout.questionDist`: the oriented-incidence distribution;
- `MIPRE.LCS.Game.accepts`: the decider;
- `MIPRE.LCS.Game.toNonlocalGame`: the nonlocal game of an LCS instance.

## Main statements

- `MIPRE.LCS.exists_tensorStrategy_value_eq_one_of_localLoss_annihilates_epr`:
  a bipartite observable strategy whose local loss operators annihilate the
  (unnormalized) EPR vector yields a perfect tensor-product strategy for the
  associated nonlocal game.
-/

namespace MIPRE.LCS

open Matrix
open scoped Kronecker

variable {G : Layout}

/-! ## The alphabets -/

/-- A question of the LCS game: an equation (`inl`) or a variable (`inr`). Both players
receive questions from this alphabet. -/
abbrev Layout.Question (G : Layout) : Type := Fin G.r ⊕ Fin G.s

/-- An answer: an assignment to all the variables (`inl`), which is what an equation question
is answered with, or a single bit (`inr`), which is what a variable question is answered with.
The decider rejects the shape that does not match the question, so the two are not
interchangeable --- a player who answers a variable question with an assignment loses. -/
abbrev Layout.Answer (G : Layout) : Type := (Fin G.s → ZMod 2) ⊕ ZMod 2

/-! ## The question distribution -/

/-- The oriented-incidence distribution: an incidence `(i, j)` with `j ∈ G.V i`, then a
uniform orientation. Each of the `2 ∑_i |V i|` oriented pairs has probability
`1 / (2 r |V i|)`. -/
noncomputable def Layout.questionDist (G : Layout) : G.Question → G.Question → ℝ
  | .inl i, .inr j => if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0
  | .inr j, .inl i => if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0
  | _, _ => 0

theorem Layout.questionDist_nonneg (G : Layout) (x y : G.Question) :
    0 ≤ G.questionDist x y := by
  cases x <;> cases y <;> simp only [questionDist] <;>
    first
      | exact le_refl 0
      | (split_ifs <;> positivity)

/-- One player's row sums to `1 / (2 r)` at an equation question: the variable is uniform in
the equation's support and the orientation costs the factor two. -/
theorem Layout.sum_questionDist_inl (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty)
    (i : Fin G.r) : ∑ y : G.Question, G.questionDist (.inl i) y = 1 / (2 * (G.r : ℝ)) := by
  classical
  have hr' : ((G.r : ℝ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hcard : (((G.V i).card : ℝ)) ≠ 0 := by exact_mod_cast (hV i).card_pos.ne'
  rw [Fintype.sum_sum_type]
  have hleft : ∑ _i' : Fin G.r, G.questionDist (.inl i) (.inl _i') = 0 := by
    simp [Layout.questionDist]
  rw [hleft, zero_add]
  have hright : ∑ j : Fin G.s, G.questionDist (.inl i) (.inr j)
      = ∑ j : Fin G.s, (if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0) :=
    rfl
  rw [hright, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem Layout.sum_questionDist (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty) :
    ∑ x : G.Question, ∑ y : G.Question, G.questionDist x y = 1 := by
  classical
  have hr' : ((G.r : ℝ)) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Fintype.sum_sum_type]
  -- the equation rows
  have hL : ∑ i : Fin G.r, ∑ y : G.Question, G.questionDist (.inl i) y = 1 / 2 := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Layout.sum_questionDist_inl hr hV i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the variable rows: the same mass, summed in the other order
  have hR : ∑ j : Fin G.s, ∑ y : G.Question, G.questionDist (.inr j) y = 1 / 2 := by
    have hrow : ∀ j : Fin G.s, ∑ y : G.Question, G.questionDist (.inr j) y
        = ∑ i : Fin G.r,
            (if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0) := by
      intro j
      rw [Fintype.sum_sum_type]
      have hz : ∑ _j' : Fin G.s, G.questionDist (.inr j) (.inr _j') = 0 := by
        simp [Layout.questionDist]
      rw [hz, add_zero]
      rfl
    have hcol : ∀ i : Fin G.r,
        ∑ j : Fin G.s, (if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0)
          = 1 / (2 * (G.r : ℝ)) := by
      intro i
      have hcard : (((G.V i).card : ℝ)) ≠ 0 := by exact_mod_cast (hV i).card_pos.ne'
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hrow j, Finset.sum_comm,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hcol i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hL, hR]
  norm_num

/-! ## The decider -/

/-- The decider: the answer shapes must match the questions, the incidence must be on
support, the assignment must satisfy its equation, and it must agree with the other player's
bit at his variable. Every other combination is rejected. -/
def Game.accepts (game : Game G) : G.Question → G.Question → G.Answer → G.Answer → Bool
  | .inl i, .inr j, .inl a, .inr v =>
      decide (j ∈ G.V i) && decide ((∑ k ∈ G.V i, a k) = game.b i) && decide (a j = v)
  | .inr j, .inl i, .inr v, .inl a =>
      decide (j ∈ G.V i) && decide ((∑ k ∈ G.V i, a k) = game.b i) && decide (a j = v)
  | _, _, _, _ => false

/-- **The decider rejects a mismatched shape.** Answering an equation question with a bit, or
a variable question with an assignment, loses --- whatever the other player does. -/
@[simp] theorem Game.accepts_inl_inr_of_inr (game : Game G) (i : Fin G.r) (j : Fin G.s)
    (v : ZMod 2) (c : G.Answer) : game.accepts (.inl i) (.inr j) (.inr v) c = false := by
  cases c <;> rfl

@[simp] theorem Game.accepts_inl_inr_of_inl (game : Game G) (i : Fin G.r) (j : Fin G.s)
    (a b : Fin G.s → ZMod 2) : game.accepts (.inl i) (.inr j) (.inl a) (.inl b) = false := rfl

@[simp] theorem Game.accepts_same_kind_left (game : Game G) (i i' : Fin G.r)
    (c d : G.Answer) : game.accepts (.inl i) (.inl i') c d = false := by
  cases c <;> cases d <;> rfl

@[simp] theorem Game.accepts_same_kind_right (game : Game G) (j j' : Fin G.s)
    (c d : G.Answer) : game.accepts (.inr j) (.inr j') c d = false := by
  cases c <;> cases d <;> rfl

/-- The decider rejects an off-support incidence, independently of the question
distribution vanishing there. -/
theorem Game.accepts_eq_false_of_not_mem (game : Game G) {i : Fin G.r} {j : Fin G.s}
    (h : j ∉ G.V i) (a : Fin G.s → ZMod 2) (v : ZMod 2) :
    game.accepts (.inl i) (.inr j) (.inl a) (.inr v) = false := by
  simp [Game.accepts, h]

/-! ## The symmetry between the players

The orientation is sampled uniformly and the decider reads the two sides symmetrically, so
exchanging the players is an automorphism of the game. This is what lets a one-sided soundness
statement be applied twice --- as blueprint `lem:ms-direct-anticomm` does, whose Alice half is
its Bob half for the swapped strategy. -/

theorem Layout.questionDist_symm (G : Layout) (x y : G.Question) :
    G.questionDist x y = G.questionDist y x := by
  cases x <;> cases y <;> rfl

theorem Game.accepts_symm (game : Game G) (x y : G.Question) (c d : G.Answer) :
    game.accepts x y c d = game.accepts y x d c := by
  cases x <;> cases y <;> cases c <;> cases d <;> rfl

/-! ## The game -/

/-- **The nonlocal game of an LCS instance.** The referee samples an incidence `(i, j)` with
`j ∈ G.V i` and a uniform orientation; the player who receives the equation answers an
assignment (only its restriction to `G.V i` is read), the player who receives the variable
answers a bit, and they win if the assignment satisfies the equation and agrees with the bit.
The hypotheses `hr` and `hV` are what make `questionDist` a probability distribution.

Blueprint `def:lcs-game`. -/
noncomputable def Game.toNonlocalGame (game : Game G)
    (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty) :
    MIPRE.Game G.Question G.Question G.Answer G.Answer where
  μ := G.questionDist
  μ_nonneg := G.questionDist_nonneg
  μ_sum_one := Layout.sum_questionDist hr hV
  D := game.accepts

@[simp] theorem Game.toNonlocalGame_μ (game : Game G) (hr : 0 < G.r)
    (hV : ∀ i, (G.V i).Nonempty) (x y : G.Question) :
    (game.toNonlocalGame hr hV).μ x y = G.questionDist x y := rfl

@[simp] theorem Game.toNonlocalGame_D (game : Game G) (hr : 0 < G.r)
    (hV : ∀ i, (G.V i).Nonempty) (x y : G.Question) (c d : G.Answer) :
    (game.toNonlocalGame hr hV).D x y c d = game.accepts x y c d := rfl

/-! ## Perfect strategies from operator solutions -/

section Perfect

variable {G : Layout} {n : Type*} [Fintype n] [DecidableEq n]

namespace BipartiteObservableStrategy

/-- The local strategy on `ℂ^n`: Alice's observables are the grid, Bob's are trivial. Only
its Alice measurement is used. -/
noncomputable def localStrategy (strat : BipartiteObservableStrategy n G) :
    ObservableStrategy (Matrix n n ℂ) G where
  aliceObs := strat.obs
  bobObs := fun _ => 1
  alice_isObservable := strat.isObservable
  bob_isObservable := fun _ => ⟨by simp, by simp⟩
  sameEquation_comm := strat.sameEquation_comm
  alice_bob_commute := fun _ _ => Commute.one_right _

/-- Alice's lift as a monoid homomorphism. -/
noncomputable def aliceLiftHom : Matrix n n ℂ →* Matrix (n × n) (n × n) ℂ where
  toFun := bipartiteAliceLift
  map_one' := by simp [bipartiteAliceLift]
  map_mul' A B := (bipartiteAliceLift_mul n A B).symm

theorem bipartiteAliceLift_observableToProjector (O : Matrix n n ℂ) (a : ZMod 2) :
    bipartiteAliceLift (observableToProjector O a)
      = observableToProjector (bipartiteAliceLift O) a := by
  simp [bipartiteAliceLift, observableToProjector, Matrix.add_kronecker, Matrix.smul_kronecker]

theorem bipartiteBobLift_observableToProjector (O : Matrix n n ℂ) (a : ZMod 2) :
    bipartiteBobLift (observableToProjector O a)
      = observableToProjector (bipartiteBobLift O) a := by
  simp [bipartiteBobLift, observableToProjector, Matrix.kronecker_add, Matrix.kronecker_smul]

theorem toProjectorStrategy_E (strat : BipartiteObservableStrategy n G) (i : Fin G.r)
    (α : Layout.Assignment G i) :
    strat.toProjectorStrategy.E i α
      = bipartiteAliceLift (strat.localStrategy.aliceMeasurement i α) := by
  change _ = aliceLiftHom _
  unfold ObservableStrategy.aliceMeasurement
  refine Eq.trans ?_ (Finset.map_noncommProd _ _ _ (aliceLiftHom (n := n))).symm
  change ObservableStrategy.aliceMeasurement _ i α = _
  unfold ObservableStrategy.aliceMeasurement
  refine Finset.noncommProd_congr rfl (fun k _ => ?_) _
  exact (bipartiteAliceLift_observableToProjector _ _).symm

theorem toProjectorStrategy_F (strat : BipartiteObservableStrategy n G) (j : Fin G.s)
    (v : ZMod 2) :
    strat.toProjectorStrategy.F j v = bipartiteBobLift (observableToProjector (strat.obs j) v) :=
  (bipartiteBobLift_observableToProjector _ _).symm

end BipartiteObservableStrategy

/-! ## Kronecker products of sums -/

theorem finset_sum_kronecker {ι m : Type*} [Fintype m] (s : Finset ι) (A : ι → Matrix m m ℂ)
    (B : Matrix m m ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext a b
  simp [Matrix.sum_apply, Finset.sum_mul]

theorem kronecker_finset_sum {ι m : Type*} [Fintype m] (s : Finset ι) (A : Matrix m m ℂ)
    (B : ι → Matrix m m ℂ) : A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ B i := by
  ext a b
  simp [Matrix.sum_apply, Finset.mul_sum]

/-- **Pushing both measurements forward.** The accepted operator of two induced measurements
is the accepted operator of the original ones, read through the two maps. -/
theorem sum_induced_kron {I J I' J' m : Type*} [Fintype I] [Fintype J] [Fintype I']
    [Fintype J'] [DecidableEq J] [DecidableEq J'] [Fintype m] [DecidableEq m]
    (E : I → Matrix m m ℂ) (F : I' → Matrix m m ℂ) (f : I → J) (g : I' → J')
    (c : J → J' → ℂ) :
    ∑ a, ∑ b, c a b • (inducedMeasurementSystem E f a ⊗ₖ inducedMeasurementSystem F g b)
      = ∑ α, ∑ β, c (f α) (g β) • (E α ⊗ₖ F β) := by
  unfold inducedMeasurementSystem
  simp_rw [finset_sum_kronecker, kronecker_finset_sum, Finset.smul_sum]
  have h1 : ∀ a, ∑ b, ∑ α ∈ Finset.univ.filter (fun α => f α = a),
      ∑ β ∈ Finset.univ.filter (fun β => g β = b), c a b • (E α ⊗ₖ F β)
      = ∑ α ∈ Finset.univ.filter (fun α => f α = a), ∑ β, c (f α) (g β) • (E α ⊗ₖ F β) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    obtain rfl := (Finset.mem_filter.mp hα).2
    rw [← Finset.sum_fiberwise Finset.univ g (fun β => c (f α) (g β) • (E α ⊗ₖ F β))]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun β hβ => ?_
    rw [(Finset.mem_filter.mp hβ).2]
  simp_rw [h1]
  exact Finset.sum_fiberwise Finset.univ f (fun α => ∑ β, c (f α) (g β) • (E α ⊗ₖ F β))

/-! ## The normalized EPR state -/

section EPRState

variable (n)

/-- The normalized EPR state `Ω / √|n|`. -/
noncomputable def eprState : n × n → ℂ :=
  ((Real.sqrt (Fintype.card n) : ℂ)⁻¹) • eprVec n

theorem star_eprVec_dotProduct (v : n × n → ℂ) :
    star (eprVec n) ⬝ᵥ v = ∑ a, v (a, a) := by
  rw [dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [eprVec]

theorem eprVec_form_kron (A B : Matrix n n ℂ) :
    star (eprVec n) ⬝ᵥ ((A ⊗ₖ B) *ᵥ eprVec n) = ∑ a, ∑ k, A a k * B a k := by
  rw [star_eprVec_dotProduct, kronecker_mulVec_epr]

theorem eprVec_form_kron_comm (A B : Matrix n n ℂ) :
    star (eprVec n) ⬝ᵥ ((A ⊗ₖ B) *ᵥ eprVec n) = star (eprVec n) ⬝ᵥ ((B ⊗ₖ A) *ᵥ eprVec n) := by
  simp only [eprVec_form_kron, mul_comm]

theorem eprState_form (M : Matrix (n × n) (n × n) ℂ) :
    star (eprState n) ⬝ᵥ (M *ᵥ eprState n)
      = ((Fintype.card n : ℂ))⁻¹ * (star (eprVec n) ⬝ᵥ (M *ᵥ eprVec n)) := by
  have hc : star ((Real.sqrt (Fintype.card n) : ℂ)⁻¹) = (Real.sqrt (Fintype.card n) : ℂ)⁻¹ := by
    simp [Complex.conj_ofReal]
  have hsq : (Real.sqrt (Fintype.card n) : ℂ)⁻¹ * (Real.sqrt (Fintype.card n) : ℂ)⁻¹
      = ((Fintype.card n : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  unfold eprState
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hc, smul_smul,
    hsq, smul_eq_mul]

theorem eprState_unit [Nonempty n] : star (eprState n) ⬝ᵥ eprState n = 1 := by
  have h := eprState_form n 1
  rw [Matrix.one_mulVec, Matrix.one_mulVec, star_eprVec_dotProduct] at h
  rw [h]
  simp [eprVec]

theorem bornProb_eprState_comm (A B : Matrix n n ℂ) :
    bornProb (eprState n) A B = bornProb (eprState n) B A := by
  unfold bornProb
  rw [eprState_form, eprState_form, eprVec_form_kron_comm]

end EPRState

/-! ## The measurements of the perfect strategy -/

namespace BipartiteObservableStrategy

/-- An assignment to the variables of equation `i`, extended by zero to all variables. -/
def extendAssignment (i : Fin G.r) (α : Layout.Assignment G i) : Fin G.s → ZMod 2 :=
  fun k => if h : k ∈ G.V i then α ⟨k, h⟩ else 0

/-- The measurements both players use: at an equation, the joint measurement of its
observables, answered as an assignment extended by zero; at a variable, the binary
measurement of its observable. -/
noncomputable def lcsMeasurement (strat : BipartiteObservableStrategy n G) :
    G.Question → G.Answer → Matrix n n ℂ
  | .inl i => inducedMeasurementSystem (strat.localStrategy.aliceMeasurement i)
      (fun α => Sum.inl (extendAssignment i α))
  | .inr j => inducedMeasurementSystem (observableToProjector (strat.obs j)) Sum.inr

theorem isMeasurementSystem_lcsMeasurement (strat : BipartiteObservableStrategy n G)
    (x : G.Question) : IsMeasurementSystem (strat.lcsMeasurement x) := by
  rcases x with i | j
  · exact IsMeasurementSystem.induced (J := G.Answer) _
      (strat.localStrategy.isMeasurementSystem_aliceMeasurement i) _
  · exact IsMeasurementSystem.induced (J := G.Answer) _
      (isMeasurementSystem_observableToProjector _ (strat.isObservable j)) _

/-- The measurements as a `ProjectiveMeasurement`. -/
noncomputable def lcsPM (strat : BipartiteObservableStrategy n G) :
    ProjectiveMeasurement G.Question G.Answer (Matrix n n ℂ) where
  M := strat.lcsMeasurement
  selfAdjoint x a := (strat.isMeasurementSystem_lcsMeasurement x).self_adjoint a
  projective x a := (strat.isMeasurementSystem_lcsMeasurement x).idempotent a
  normalized x := (strat.isMeasurementSystem_lcsMeasurement x).sum_one

end BipartiteObservableStrategy

/-! ## The accepted probability as one quadratic form -/

theorem condWin_eq_re {X A m : Type*} [Fintype X] [Fintype A] [Fintype m] [DecidableEq m]
    (Γ : MIPRE.Game X X A A) (ψ : m × m → ℂ) (P : ProjectiveMeasurement X A (Matrix m m ℂ))
    (x y : X) :
    condWin Γ ψ (fun x => P.toPOVM x) (fun y => P.toPOVM y) x y
      = (star ψ ⬝ᵥ ((∑ a, ∑ b, (if Γ.D x y a b then (1 : ℂ) else 0) • (P.M x a ⊗ₖ P.M y b))
          *ᵥ ψ)).re := by
  unfold condWin bornProb
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [ProjectiveMeasurement.toPOVM]

/-- Exchanging the players, for a symmetric game, a symmetric Born rule and one measurement
family used by both. -/
theorem condWin_swap {X A m : Type*} [Fintype X] [Fintype A] [Fintype m] [DecidableEq m]
    (Γ : MIPRE.Game X X A A) (ψ : m × m → ℂ) (P : ProjectiveMeasurement X A (Matrix m m ℂ))
    (hD : ∀ x y a b, Γ.D x y a b = Γ.D y x b a)
    (hψ : ∀ E F : Matrix m m ℂ, bornProb ψ E F = bornProb ψ F E) (x y : X) :
    condWin Γ ψ (fun x => P.toPOVM x) (fun y => P.toPOVM y) x y
      = condWin Γ ψ (fun x => P.toPOVM x) (fun y => P.toPOVM y) y x := by
  unfold condWin
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [hD, hψ]

namespace BipartiteObservableStrategy

theorem sum_extendAssignment (i : Fin G.r) (α : Layout.Assignment G i) :
    ∑ k ∈ G.V i, extendAssignment i α k = ∑ k : G.V i, α k := by
  rw [← Finset.sum_coe_sort (G.V i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [extendAssignment, k.2]

theorem extendAssignment_of_mem (i : Fin G.r) (α : Layout.Assignment G i) {j : Fin G.s}
    (hj : j ∈ G.V i) : extendAssignment i α j = α ⟨j, hj⟩ := by
  simp [extendAssignment, hj]

/-- **The accepted operator at an incidence is the local winning operator**, lifted: at the
question pair (equation `i`, variable `j`), the Kronecker products of the players' accepted
outcomes sum to the winning operator of the edge `(i, j)` of the projector strategy. -/
theorem acceptedOp_eq (game : Game G) (strat : BipartiteObservableStrategy n G) (i : Fin G.r)
    {j : Fin G.s} (hj : j ∈ G.V i) :
    ∑ a, ∑ b, (if game.accepts (.inl i) (.inr j) a b then (1 : ℂ) else 0) •
        (strat.lcsMeasurement (.inl i) a ⊗ₖ strat.lcsMeasurement (.inr j) b)
      = localWinningOperator game strat.toProjectorStrategy i ⟨j, hj⟩ := by
  change ∑ a, ∑ b, (if game.accepts (.inl i) (.inr j) a b then (1 : ℂ) else 0) •
      (inducedMeasurementSystem (strat.localStrategy.aliceMeasurement i)
          (fun α => (Sum.inl (extendAssignment i α) : G.Answer)) a ⊗ₖ
        inducedMeasurementSystem (observableToProjector (strat.obs j))
          (fun v => (Sum.inr v : G.Answer)) b) = _
  rw [sum_induced_kron]
  unfold localWinningOperator winningAssignments
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Game.accepts, hj, decide_true, Bool.true_and, sum_extendAssignment,
    extendAssignment_of_mem i α hj, Bool.and_eq_true, decide_eq_true_eq]
  rw [toProjectorStrategy_E, toProjectorStrategy_F, bipartiteAliceLift_mul_bipartiteBobLift]
  rw [Finset.univ_eq_attach]
  split_ifs with hw
  · rw [Finset.sum_eq_single (α ⟨j, hj⟩)]
    · simp [hw]
    · intro v _ hv
      simp [Ne.symm hv]
    · simp
  · simp [hw]

end BipartiteObservableStrategy

end Perfect

/-- A bipartite observable strategy whose local loss operators all annihilate the
(unnormalized) EPR vector yields a perfect tensor-product strategy for the associated
nonlocal game.

Both players use one measurement family (`lcsMeasurement`) on `ℂ^n`, sharing the
normalized EPR state `eprState n`. At an equation `i` a player measures the joint
measurement of the grid observables of `i`, answering the assignment extended by zero; at
a variable `j`, the binary measurement of `obs j`. At an oriented incidence the Kronecker
products of the accepted outcomes sum to the lifted local winning operator
(`acceptedOp_eq`), which fixes the EPR vector because the local loss operator annihilates
it; the other orientation is the same by the symmetry of the EPR state
(`bornProb_eprState_comm`) and of the decider. The `[Nonempty n]` hypothesis is
necessary: for empty `n` the hypothesis `hLoss` is vacuous while no unit vector exists.
Blueprint `thm:lcs-perfect`. -/
theorem exists_tensorStrategy_value_eq_one_of_localLoss_annihilates_epr
    (game : Game G) (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty)
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (strat : BipartiteObservableStrategy n G)
    (hLoss : ∀ (i : Fin G.r) (j : G.V i),
      localLossOperator game strat.toProjectorStrategy i j *ᵥ eprVec n = 0) :
    ∃ S : MIPRE.TensorProductStrategy (game.toNonlocalGame hr hV), S.value = 1 := by
  set Γ := game.toNonlocalGame hr hV
  refine ⟨TensorProductStrategy.ofProjective Γ (eprState n) (eprState_unit n) strat.lcsPM
    strat.lcsPM, ?_⟩
  rw [TensorProductStrategy.value_ofProjective]
  unfold povmValue
  have hwin : ∀ (i : Fin G.r) (j : Fin G.s) (hj : j ∈ G.V i),
      condWin Γ (eprState n) (fun x => strat.lcsPM.toPOVM x) (fun y => strat.lcsPM.toPOVM y)
        (.inl i) (.inr j) = 1 := by
    intro i j hj
    rw [condWin_eq_re]
    change (star (eprState n) ⬝ᵥ ((∑ a, ∑ b,
      (if game.accepts (.inl i) (.inr j) a b then (1 : ℂ) else 0) •
        (strat.lcsMeasurement (.inl i) a ⊗ₖ strat.lcsMeasurement (.inr j) b)) *ᵥ
          eprState n)).re = 1
    rw [BipartiteObservableStrategy.acceptedOp_eq game strat i hj]
    have hW : localWinningOperator game strat.toProjectorStrategy i ⟨j, hj⟩ *ᵥ eprVec n
        = eprVec n := by
      have h := hLoss i ⟨j, hj⟩
      unfold localLossOperator at h
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      exact h.symm
    have hW' : localWinningOperator game strat.toProjectorStrategy i ⟨j, hj⟩ *ᵥ eprState n
        = eprState n := by
      unfold eprState
      rw [Matrix.mulVec_smul, hW]
    rw [hW', eprState_unit, Complex.one_re]
  have key : ∀ x y : G.Question, Γ.μ x y *
      condWin Γ (eprState n) (fun x => strat.lcsPM.toPOVM x) (fun y => strat.lcsPM.toPOVM y)
        x y = Γ.μ x y := by
    rintro (i | j) (i' | j')
    · simp [Γ, Layout.questionDist]
    · by_cases hj : j' ∈ G.V i
      · rw [hwin i j' hj, mul_one]
      · simp [Γ, Layout.questionDist, hj]
    · by_cases hj : j ∈ G.V i'
      · rw [condWin_swap Γ (eprState n) strat.lcsPM (fun x y a b => game.accepts_symm x y a b)
          (bornProb_eprState_comm n), hwin i' j hj, mul_one]
      · simp [Γ, Layout.questionDist, hj]
    · simp [Γ, Layout.questionDist]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => key x y]
  exact Γ.μ_sum_one

end MIPRE.LCS
