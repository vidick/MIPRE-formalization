/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Reduction.lean
-/
/-
# The strict tracial reduction (Section 3)

Statement skeleton for audit nodes 1.1, 1.1.2, 1.1.3, 1.1.4.
Anchors: 03_tracial_reduction.tex, prop strict-tracial-reduction and its
proof (eqs strict-threshold, strict-margin-p, tagged-alphabets,
strict-margin-q, left-right-actions).

The common-alphabet objects use the sum types `X ⊕ Y`, `A ⊕ B` for the
manuscript's tagged disjoint unions ({A-tag}×X) ⊔ ({B-tag}×Y): `Sum.inl`
is the Alice tag, `Sum.inr` the Bob tag.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Basic
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Strategy
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.Main
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Scalar
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.CommutantPullback

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

namespace Game

/-- The tagged common-alphabet game of the strict tracial reduction
(03_tracial_reduction.tex, eq tagged-alphabets and following): question
law supported on (Alice-tag, Bob-tag) pairs where it equals `μ`, payoff
the zero-extended tagged payoff — equal to `V` on correctly tagged
question/answer pairs, zero otherwise. Its `win` is the manuscript's
"continuous linear functional of the common-alphabet correlation table". -/
def tagged (H : Game X Y A B) : Game (X ⊕ Y) (X ⊕ Y) (A ⊕ B) (A ⊕ B) where
  questionWeight q₁ q₂ :=
    match q₁, q₂ with
    | Sum.inl x, Sum.inr y => H.questionWeight x y
    | _, _ => 0
  weight_nonneg q₁ q₂ := by
    rcases q₁ with x | y <;> rcases q₂ with x' | y' <;>
      first
        | exact le_refl 0
        | exact H.weight_nonneg _ _
  weight_normalized := by
    classical
    simp only [Fintype.sum_sum_type]
    simpa using H.weight_normalized
  payoff q₁ q₂ a₁ b₁ :=
    match q₁, q₂, a₁, b₁ with
    | Sum.inl x, Sum.inr y, Sum.inl a, Sum.inr b => H.payoff x y a b
    | _, _, _, _ => 0
  payoff_nonneg q₁ q₂ a₁ b₁ := by
    rcases q₁ with x | y <;> rcases q₂ with x' | y' <;>
      rcases a₁ with a | b <;> rcases b₁ with a' | b' <;>
        first
          | exact le_refl 0
          | exact H.payoff_nonneg _ _ _ _
  payoff_le_one q₁ q₂ a₁ b₁ := by
    rcases q₁ with x | y <;> rcases q₂ with x' | y' <;>
      rcases a₁ with a | b <;> rcases b₁ with a' | b' <;>
        first
          | exact zero_le_one
          | exact H.payoff_le_one _ _ _ _

end Game

/-- The winning functional is `1`-Lipschitz for the unhalved ℓ¹ distance on
correlation tables (03_tracial_reduction.tex: "Apply Theorem 3.1 closely
enough that its value changes by less than ρ/2"; coefficients `μ·V ∈ [0,1]`
entrywise). -/
theorem Game.abs_win_sub_win_le_l1Dist (G : Game X Y A B)
    (p q : Correlation X Y A B) :
    |G.win p - G.win q| ≤ l1Dist p q := by
  have hterm : ∀ x y a b,
      |G.questionWeight x y * G.payoff x y a b * p x y a b -
        G.questionWeight x y * G.payoff x y a b * q x y a b|
      ≤ |p x y a b - q x y a b| := by
    intro x y a b
    rw [← mul_sub, abs_mul]
    have hco : |G.questionWeight x y * G.payoff x y a b| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg (G.weight_nonneg x y)
        (G.payoff_nonneg x y a b))]
      calc G.questionWeight x y * G.payoff x y a b
          ≤ 1 * 1 := mul_le_mul (G.questionWeight_le_one x y)
            (G.payoff_le_one x y a b) (G.payoff_nonneg x y a b) zero_le_one
        _ = 1 := one_mul 1
    nlinarith [abs_nonneg (p x y a b - q x y a b)]
  calc |G.win p - G.win q|
      = |∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          (G.questionWeight x y * G.payoff x y a b * p x y a b -
           G.questionWeight x y * G.payoff x y a b * q x y a b)| := by
        simp only [Game.win, Finset.sum_sub_distrib]
    _ ≤ ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          |G.questionWeight x y * G.payoff x y a b * p x y a b -
           G.questionWeight x y * G.payoff x y a b * q x y a b| :=
        abs_sum4_le _
    _ ≤ ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, |p x y a b - q x y a b| :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            hterm x y a b
    _ = l1Dist p q := rfl

/-- Unfolding computation for the tagged winning functional: only the
(Alice-tag question, Bob-tag question, Alice-tag answer, Bob-tag answer)
entries of a common-alphabet correlation carry weight
(03_tracial_reduction.tex, eq tagged-alphabets: the tagged question law
and payoff vanish off the correctly tagged block). Auxiliary lemma. -/
theorem Game.tagged_win_eq (H : Game X Y A B)
    (q : Correlation (X ⊕ Y) (X ⊕ Y) (A ⊕ B) (A ⊕ B)) :
    H.tagged.win q
      = ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          H.questionWeight x y * H.payoff x y a b *
            q (Sum.inl x) (Sum.inr y) (Sum.inl a) (Sum.inr b) := by
  classical
  unfold Game.win Game.tagged
  simp [Fintype.sum_sum_type]

/-- **Tagged symmetrization** (node 1.1.2; 03_tracial_reduction.tex, eq
tagged-alphabets and following): every commuting correlation for the
asymmetric game `H` induces a commuting correlation on the tagged common
alphabets with the same tagged payoff — original measurements on own-tag
questions, fixed outputs on wrong-tag questions, zero wrong-tag answer
effects. -/
theorem Game.tagged_symmetrization [Nonempty A] [Nonempty B]
    (H : Game X Y A B) {p : Correlation X Y A B}
    (hp : IsCommutingCorrelation p) :
    ∃ pt : Correlation (X ⊕ Y) (X ⊕ Y) (A ⊕ B) (A ⊕ B),
      IsCommutingCorrelation pt ∧ H.tagged.win pt = H.win p := by
  classical
  obtain ⟨S, hS⟩ := hp
  let St : CommutingStrategy.{0} (X ⊕ Y) (X ⊕ Y) (A ⊕ B) (A ⊕ B) :=
    { H := S.H
      ψ := S.ψ
      ψ_norm := S.ψ_norm
      E := fun q c =>
        match q, c with
        | Sum.inl x, Sum.inl a => S.E x a
        | Sum.inl _, Sum.inr _ => 0
        | Sum.inr _, Sum.inl a =>
            if a = Classical.arbitrary A then 1 else 0
        | Sum.inr _, Sum.inr _ => 0
      F := fun q c =>
        match q, c with
        | Sum.inr y, Sum.inr b => S.F y b
        | Sum.inr _, Sum.inl _ => 0
        | Sum.inl _, Sum.inr b =>
            if b = Classical.arbitrary B then 1 else 0
        | Sum.inl _, Sum.inl _ => 0
      E_pos := by
        rintro (x | y) (a | b)
        · exact S.E_pos x a
        · exact ContinuousLinearMap.isPositive_zero
        · by_cases h : a = Classical.arbitrary A
          · simpa [h] using
              ContinuousLinearMap.isPositive_one (E := S.H) (𝕜 := ℂ)
          · simpa [h] using
              ContinuousLinearMap.isPositive_zero (E := S.H) (𝕜 := ℂ)
        · exact ContinuousLinearMap.isPositive_zero
      F_pos := by
        rintro (x | y) (a | b)
        · exact ContinuousLinearMap.isPositive_zero
        · by_cases h : b = Classical.arbitrary B
          · simpa [h] using
              ContinuousLinearMap.isPositive_one (E := S.H) (𝕜 := ℂ)
          · simpa [h] using
              ContinuousLinearMap.isPositive_zero (E := S.H) (𝕜 := ℂ)
        · exact ContinuousLinearMap.isPositive_zero
        · exact S.F_pos y b
      E_sum := by
        rintro (x | y)
        · simp [Fintype.sum_sum_type, S.E_sum x]
        · simp [Fintype.sum_sum_type, Finset.sum_ite_eq']
      F_sum := by
        rintro (x | y)
        · simp [Fintype.sum_sum_type, Finset.sum_ite_eq']
        · simp [Fintype.sum_sum_type, S.F_sum y]
      commutes := by
        rintro (x | y) (x' | y') (a | b) (a' | b') <;>
          first
            | exact Commute.zero_left _
            | exact Commute.zero_right _
            | exact S.commutes _ _ _ _
            | (dsimp only; split_ifs <;>
                first
                  | exact Commute.one_left _
                  | exact Commute.one_right _
                  | exact Commute.zero_left _
                  | exact Commute.zero_right _) }
  refine ⟨St.correlation, ⟨St, rfl⟩, ?_⟩
  rw [Game.tagged_win_eq]
  unfold Game.win
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [← hS]
  rfl

/-- **Commutant pullback, consumed form** (node 1.1.4;
03_tracial_reduction.tex, eqs left-right-actions,
tracial-correlation-formula): every tracially embeddable correlation (Bob
in the commutant of the left action) is realized by a `TracialStrategy` —
Bob's effects pulled back through the canonical anti-isomorphism `R` to a
POVM in the algebra, after passing to the generated von Neumann algebra in
its standard form. This is the Stage-B tracial-Tomita obligation `L(M)′ =
R(M)`; it is proved, never assumed. -/
theorem TraciallyEmbeddableCorrelation.exists_tracialStrategy
    {Xc Ac : Type} [Fintype Xc] [Fintype Ac]
    (q : TraciallyEmbeddableCorrelation Xc Ac) :
    ∃ T : TracialStrategy.{0} Xc Xc Ac Ac,
      T.correlation = q.toCorrelation :=
  ⟨q.pullback, q.pullback_correlation⟩

/-- **Detagging** (node 1.1.3; 03_tracial_reduction.tex, proof of prop
strict-tracial-reduction): local deterministic postprocessing — wrong-tag
outputs to a fixed valid answer, tags stripped — of a tracially embeddable
common-alphabet correlation yields a tracial strategy for the original
asymmetric game whose winning probability is at least the zero-extended
tagged payoff (postprocessing is an ℓ¹ contraction that cannot decrease
the nonnegative tagged payoff, and coarse-graining POVM effects preserves
tracial embeddability). The output type deliberately folds the node-1.1.4
pullback into this statement — the 1.1.3/1.1.4 proof-obligation boundary
differs from the audit tree's, with the composition unchanged. -/
theorem Game.detag [Nonempty A] [Nonempty B] (H : Game X Y A B)
    (qt : TraciallyEmbeddableCorrelation (X ⊕ Y) (A ⊕ B)) :
    ∃ T : TracialStrategy.{0} X Y A B,
      H.tagged.win qt.toCorrelation ≤ H.win T.correlation := by
  classical
  obtain ⟨T0, hT0⟩ := qt.exists_tracialStrategy
  refine ⟨{ M := T0.M
            σ := T0.σ
            σ_pos := T0.σ_pos
            σ_normalized := T0.σ_normalized
            E := fun x a => T0.E (Sum.inl x) (Sum.inl a) +
              (if a = Classical.arbitrary A then
                ∑ b' : B, T0.E (Sum.inl x) (Sum.inr b') else 0)
            F := fun y b => T0.F (Sum.inr y) (Sum.inr b) +
              (if b = Classical.arbitrary B then
                ∑ a' : A, T0.F (Sum.inr y) (Sum.inl a') else 0)
            E_pos := ?_
            F_pos := ?_
            E_sum := ?_
            F_sum := ?_ }, ?_⟩
  · intro x a
    refine (T0.E_pos _ _).add ?_
    split_ifs
    · exact isPosElem_sum _ _ fun b' _ => T0.E_pos _ _
    · exact isPosElem_zero
  · intro y b
    refine (T0.F_pos _ _).add ?_
    split_ifs
    · exact isPosElem_sum _ _ fun a' _ => T0.F_pos _ _
    · exact isPosElem_zero
  · intro x
    have h := T0.E_sum (Sum.inl x)
    simp only [Fintype.sum_sum_type] at h
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ
      (Classical.arbitrary A)
      (fun _ => ∑ b' : B, T0.E (Sum.inl x) (Sum.inr b')),
      if_pos (Finset.mem_univ _)]
    exact h
  · intro y
    have h := T0.F_sum (Sum.inr y)
    simp only [Fintype.sum_sum_type] at h
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ
      (Classical.arbitrary B)
      (fun _ => ∑ a' : A, T0.F (Sum.inr y) (Sum.inl a')),
      if_pos (Finset.mem_univ _)]
    rw [add_comm (∑ a' : A, T0.F (Sum.inr y) (Sum.inl a'))] at h
    exact h
  · rw [Game.tagged_win_eq]
    unfold Game.win
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (H.weight_nonneg x y) (H.payoff_nonneg x y a b))
    rw [← hT0]
    -- abbreviations for the four bilinear pieces
    set P := T0.E (Sum.inl x) (Sum.inl a) with hP
    set Q := (if a = Classical.arbitrary A then
      ∑ b' : B, T0.E (Sum.inl x) (Sum.inr b') else 0) with hQ
    set R := T0.F (Sum.inr y) (Sum.inr b) with hR
    set S := (if b = Classical.arbitrary B then
      ∑ a' : A, T0.F (Sum.inr y) (Sum.inl a') else 0) with hS
    have hQpos : IsPosElem Q := by
      rw [hQ]
      split_ifs
      · exact isPosElem_sum _ _ fun a' _ => T0.E_pos _ _
      · exact isPosElem_zero
    have hSpos : IsPosElem S := by
      rw [hS]
      split_ifs
      · exact isPosElem_sum _ _ fun a' _ => T0.F_pos _ _
      · exact isPosElem_zero
    have hexp : star T0.σ * ((P + Q) * T0.σ * (R + S))
        = star T0.σ * (P * T0.σ * R) + (star T0.σ * (P * T0.σ * S) +
          (star T0.σ * (Q * T0.σ * R) + star T0.σ * (Q * T0.σ * S))) := by
      noncomm_ring
    have h1 : 0 ≤ (T0.M.τ (star T0.σ * (P * T0.σ * S))).re :=
      T0.M.pairing_nonneg T0.σ (T0.E_pos _ _) hSpos
    have h2 : 0 ≤ (T0.M.τ (star T0.σ * (Q * T0.σ * R))).re :=
      T0.M.pairing_nonneg T0.σ hQpos (T0.F_pos _ _)
    have h3 : 0 ≤ (T0.M.τ (star T0.σ * (Q * T0.σ * S))).re :=
      T0.M.pairing_nonneg T0.σ hQpos hSpos
    show T0.correlation (Sum.inl x) (Sum.inr y) (Sum.inl a) (Sum.inr b)
      ≤ (T0.M.τ (star T0.σ * ((P + Q) * T0.σ * (R + S)))).re
    rw [hexp, map_add, map_add, map_add, Complex.add_re, Complex.add_re,
      Complex.add_re]
    unfold TracialStrategy.correlation
    linarith

/-- **Strict tracial reduction** (node 1.1; 03_tracial_reduction.tex, prop
strict-tracial-reduction): for every finite game `H` (possibly asymmetric
alphabets) and every
`λ < ω^co(H)`, `H` has an exact tracially embeddable commuting strategy
with winning probability strictly greater than `λ`. Applied downstream
with `H = G^{⊗n}` and `λ = e^{−γn}` (node 1.5.2). No attainment of the
supremum is assumed. -/
theorem strict_tracial_reduction
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (H : Game X Y A B) {lam : ℝ} (hlam : lam < H.omegaCO) :
    ∃ T : TracialStrategy.{0} X Y A B, lam < H.win T.correlation := by
  classical
  -- a commuting strategy beating `lam` (no attainment of the supremum)
  have hne : (Set.range fun S : CommutingStrategy.{0} X Y A B =>
      H.win S.correlation).Nonempty := ⟨_, CommutingStrategy.trivial, rfl⟩
  obtain ⟨_, ⟨S, rfl⟩, hS⟩ := exists_lt_of_lt_csSup hne hlam
  -- symmetrize onto the tagged common alphabets
  obtain ⟨pt, hpt, hwin⟩ := H.tagged_symmetrization ⟨S, rfl⟩
  -- tracial density at accuracy `win − λ` (eq strict-margin-p)
  haveI : Nonempty (X ⊕ Y) := ⟨Sum.inl (Classical.arbitrary X)⟩
  haveI : Nonempty (A ⊕ B) := ⟨Sum.inl (Classical.arbitrary A)⟩
  obtain ⟨qt, hl1⟩ := Density.tracialDensity (X ⊕ Y) (A ⊕ B) pt hpt
    (H.win S.correlation - lam) (by linarith)
  -- detag back to the asymmetric game (eq strict-margin-q)
  obtain ⟨T, hT⟩ := H.detag qt
  refine ⟨T, ?_⟩
  have habs := H.tagged.abs_win_sub_win_le_l1Dist pt qt.toCorrelation
  have hle : H.tagged.win pt - H.tagged.win qt.toCorrelation
      ≤ |H.tagged.win pt - H.tagged.win qt.toCorrelation| := le_abs_self _
  linarith

end CommutingRepetition
