/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestMagicSquare
import MIPRE.Foundations.Introspection.RegisterTransport
import MIPRE.Foundations.GameDouble
import MIPRE.Foundations.Pasting
import MIPRE.Foundations.PerfectStrategy

/-! # Perfect PCC play of the actual Magic Square game

The arbitrary anticommuting pair is extended by one qubit. Constraint triples
are encoded as assignments with zeroes outside the queried constraint. This
file uses the existing game's exact distribution and decision predicate.
-/

noncomputable section

namespace MIPRE.Introspection.HonestMagicSquare

open Matrix Finset LCS LCS.MagicSquare Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Extend the three reported bits by zero outside the queried constraint. -/
def assignment (c : Fin layout.r) (a : Fin 3 → ZMod 2) : Fin layout.s → ZMod 2 :=
  fun j => if j ∈ layout.V c then a (cellIdx c j) else 0

@[simp] theorem assignment_cell (c : Fin layout.r) (a : Fin 3 → ZMod 2) (j : Fin 3) :
    assignment c a (cell c j) = a j := by
  simp [assignment, cell_mem]

theorem assignment_parity (c : Fin layout.r) (a : Fin 3 → ZMod 2) :
    (∑ j ∈ layout.V c, assignment c a j) = a 0 + a 1 + a 2 := by
  rw [sum_cells]
  simp

def constraintAnswer (c : Fin layout.r) (a : Fin 3 → ZMod 2) : layout.Answer :=
  .inl (assignment c a)

theorem constraintAnswer_injective (c : Fin layout.r) : Function.Injective (constraintAnswer c) := by
  intro a b h
  have hfun := Sum.inl.inj h
  funext j
  simpa only [assignment_cell] using congrFun hfun (cell c j)

/-- The actual shared answer alphabet, including zero effects for wrong shapes. -/
def questionOp (A B : Matrix I I ℂ) : layout.Question → layout.Answer →
    Matrix (I × Fin 2) (I × Fin 2) ℂ
  | .inl c => fibSum (constraintOp A B c) (constraintAnswer c)
  | .inr j => fibSum (variableOp A B j) Sum.inr

theorem questionOp_isPVM {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (q : layout.Question) : IsPVM (questionOp A B q) := by
  cases q with
  | inl c => exact isPVM_fibSum (constraintOp_isPVM hA hB hAB c) _
  | inr j => exact isPVM_fibSum (variableOp_isPVM hA hB hAB j) _

omit [DecidableEq I] in
private theorem coarse_commute {X Y : Type*} [Fintype X] [Fintype Y]
    {U V : Type*} [DecidableEq U] [DecidableEq V]
    (M : X → Matrix I I ℂ) (N : Y → Matrix I I ℂ)
    (f : X → U) (g : Y → V) (hc : ∀ x y, Commute (M x) (N y)) (u : U) (v : V) :
    Commute (fibSum M f u) (fibSum N g v) := by
  unfold fibSum
  exact Commute.sum_left _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => hc x y))

theorem questionOp_incidence_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) (j : Fin layout.s)
    (hj : j ∈ layout.V c) (a b : layout.Answer) :
    Commute (questionOp A B (.inl c) a) (questionOp A B (.inr j) b) := by
  apply coarse_commute
  intro x y
  have h := (variable_constraint_commute hAB c (cellIdx c j) x y).symm
  simpa only [cellIndex, cell_cellIdx hj] using h

private theorem constraint_incidence_reject {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (j : Fin layout.s) (hj : j ∈ layout.V c)
    (a : Fin 3 → ZMod 2) (b : ZMod 2)
    (hr : game.accepts (.inl c) (.inr j) (constraintAnswer c a) (.inr b) = false) :
    constraintOp A B c a * variableOp A B j b = 0 := by
  have hbad : ¬ (a 0 + a 1 + a 2 = game.b c ∧ a (cellIdx c j) = b) := by
    intro h
    have ht : game.accepts (.inl c) (.inr j) (constraintAnswer c a) (.inr b) = true := by
      simp only [LCS.Game.accepts, constraintAnswer, assignment_parity, h.1, decide_true]
      simp [hj, assignment, h.2]
    rw [ht] at hr
    contradiction
  simpa only [cellIndex, cell_cellIdx hj] using
    constraint_reject_zero hA hB hAB c a (cellIdx c j) b hbad

theorem questionOp_incidence_reject {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (j : Fin layout.s) (hj : j ∈ layout.V c)
    (a b : layout.Answer) (hr : game.accepts (.inl c) (.inr j) a b = false) :
    questionOp A B (.inl c) a * questionOp A B (.inr j) b = 0 := by
  simp only [questionOp, fibSum]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  have hx' : constraintAnswer c x = a := (Finset.mem_filter.mp hx).2
  have hy' : Sum.inr y = b := (Finset.mem_filter.mp hy).2
  apply constraint_incidence_reject hA hB hAB c j hj x y
  simpa only [hx', hy'] using hr

private theorem positive_incidence (p q : layout.Question)
    (h : 0 < nonlocalGame.μ p q) :
    (∃ c j, p = .inl c ∧ q = .inr j ∧ j ∈ layout.V c) ∨
      (∃ c j, p = .inr j ∧ q = .inl c ∧ j ∈ layout.V c) := by
  change 0 < layout.questionDist p q at h
  cases p with
  | inl c =>
    cases q with
    | inl d => exact (lt_irrefl 0 h).elim
    | inr j =>
      have hj : j ∈ layout.V c := by
        by_contra hn
        simp [Layout.questionDist, hn] at h
      exact Or.inl ⟨c, j, rfl, rfl, hj⟩
  | inr j =>
    cases q with
    | inl c =>
      have hj : j ∈ layout.V c := by
        by_contra hn
        simp [Layout.questionDist, hn] at h
      exact Or.inr ⟨c, j, rfl, rfl, hj⟩
    | inr k => exact (lt_irrefl 0 h).elim

theorem questionOp_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (p q : layout.Question)
    (h : 0 < nonlocalGame.μ p q) (a b : layout.Answer) :
    Commute (questionOp A B p a) (questionOp A B q b) := by
  rcases positive_incidence p q h with ⟨c, j, rfl, rfl, hj⟩ | ⟨c, j, rfl, rfl, hj⟩
  · exact questionOp_incidence_commute hAB c j hj a b
  · exact (questionOp_incidence_commute hAB c j hj b a).symm

theorem questionOp_reject {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (p q : layout.Question) (h : 0 < nonlocalGame.μ p q) (a b : layout.Answer)
    (hr : nonlocalGame.D p q a b = false) : questionOp A B p a * questionOp A B q b = 0 := by
  rcases positive_incidence p q h with ⟨c, j, rfl, rfl, hj⟩ | ⟨c, j, rfl, rfl, hj⟩
  · exact questionOp_incidence_reject hA hB hAB c j hj a b hr
  · rw [(questionOp_incidence_commute hAB c j hj b a).eq.symm]
    apply questionOp_incidence_reject hA hB hAB c j hj b a
    simpa only [nonlocalGame, LCS.Game.toNonlocalGame_D, LCS.Game.accepts_symm] using hr

variable [Nonempty I]

/-- An actual PCC strategy for the existing Magic Square game, on twice the input dimension. -/
def strategy {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) :
    SyncStrategy nonlocalGame.doubled where
  d := Fintype.card (I × Fin 2)
  d_pos := Fintype.card_pos
  P :=
    { M := fun q a => registerOp (Fintype.equivFin (I × Fin 2)).symm (questionOp A B q.2 a)
      selfAdjoint := fun q a => by
        rw [Matrix.star_eq_conjTranspose]
        exact (registerOp_isPVM _ (questionOp_isPVM hA hB hAB q.2)).isSelfAdjoint a
      projective := fun q a => (registerOp_isPVM _ (questionOp_isPVM hA hB hAB q.2)).idem a
      normalized := fun q => (registerOp_isPVM _ (questionOp_isPVM hA hB hAB q.2)).sum_eq_one }

private theorem doubled_positive (p q : Bool × layout.Question)
    (h : 0 < nonlocalGame.doubled.μ p q) :
    (p.1 = false ∧ q.1 = true) ∧ 0 < nonlocalGame.μ p.2 q.2 := by
  have ht : p.1 = false ∧ q.1 = true := by
    by_contra hn
    simp only [MIPRE.Game.doubled_μ, if_neg hn] at h
    exact (lt_irrefl 0 h).elim
  exact ⟨ht, by simpa only [MIPRE.Game.doubled_μ, if_pos ht] using h⟩

set_option backward.isDefEq.respectTransparency false in
theorem strategy_isPCC {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) :
    (strategy hA hB hAB).IsPCC := by
  intro p q h a b
  have hc := (questionOp_commute hAB p.2 q.2 (doubled_positive p q h).2 a b).eq
  have hh := congrArg (registerOp (Fintype.equivFin (I × Fin 2)).symm) hc
  simpa only [strategy, registerOp_mul] using hh

set_option backward.isDefEq.respectTransparency false in
theorem strategy_value {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) :
    (strategy hA hB hAB).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro p q h a b hr
  obtain ⟨ht, hm⟩ := doubled_positive p q h
  have hd : nonlocalGame.D p.2 q.2 a b = false := by
    change (if p.1 = false ∧ q.1 = true then nonlocalGame.D p.2 q.2 a b else false) = false at hr
    simpa only [if_pos ht] using hr
  have hh := congrArg (registerOp (Fintype.equivFin (I × Fin 2)).symm)
    (questionOp_reject hA hB hAB p.2 q.2 hm a b hd)
  rw [show registerOp (Fintype.equivFin (I × Fin 2)).symm
    (0 : Matrix (I × Fin 2) (I × Fin 2) ℂ) = 0 from rfl] at hh
  have hz : (strategy hA hB hAB).P.M p a * (strategy hA hB hAB).P.M q b = 0 := by
    simpa only [strategy, registerOp_mul] using hh
  rw [hz, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

/-- The arbitrary anticommuting pair produces a perfect PCC strategy of local dimension `2|I|`. -/
theorem exists_perfectPCC {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) :
    ∃ S : SyncStrategy nonlocalGame.doubled,
      S.IsPCC ∧ S.value = 1 ∧ S.d = 2 * Fintype.card I := by
  refine ⟨strategy hA hB hAB, strategy_isPCC hA hB hAB, strategy_value hA hB hAB, ?_⟩
  simp [strategy, Fintype.card_prod, Nat.mul_comm]

end MIPRE.Introspection.HonestMagicSquare
