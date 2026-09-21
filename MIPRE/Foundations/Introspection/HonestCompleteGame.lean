/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestCompleteAux

/-! # Perfect PCC completeness of the full auxiliary introspection game

The game uses every auxiliary type and the exact induced type graph and parsed
predicate of introspection. Its honest strategy is explicitly constructed on
the seed register tensored with the original strategy. Pauli vertices are not
part of this induced game, and no Pauli-completeness assumption is made.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {F ι A PA P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq P] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (E : P → P → Bool) (X Z : P) (projectPauli : PA → ι → F)
  (DP : P → P → PA → PA → Bool)

/-- The ordered auxiliary edges of the actual introspection graph. -/
abbrev AuxEdge := {p : AuxQuestion ℓ × AuxQuestion ℓ // TypeGraph.Adj E X Z (.inr p.1) (.inr p.2)}

instance auxEdge_nonempty : Nonempty (AuxEdge (ℓ := ℓ) E X Z) :=
  ⟨⟨((.introspect, false), (.introspect, false)), TypeGraph.adj_self E X Z _⟩⟩

/-- The full induced auxiliary game, retaining all parsed answer constructors. -/
def auxGame : Game (AuxQuestion ℓ) (AuxQuestion ℓ)
    (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA) :=
  SampledGame.game (fun e : AuxEdge E X Z => e.val.1) (fun e => e.val.2)
    (fun t u => TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr u))

theorem auxGame_mu_nonadj (t u : AuxQuestion ℓ)
    (hn : ¬ TypeGraph.Adj E X Z (.inr t) (.inr u)) :
    (auxGame L D E X Z projectPauli DP).μ t u = 0 := by
  have he (e : AuxEdge (ℓ := ℓ) E X Z) : (e.val.1, e.val.2) ≠ (t, u) := by
    intro hh
    apply hn
    have h1 : e.val.1 = t := congrArg Prod.fst hh
    have h2 : e.val.2 = u := congrArg Prod.snd hh
    simpa only [h1, h2] using e.property
  simp [auxGame, SampledGame.game, SampledGame.dist, he]

theorem auxGame_mu_pos_adj (t u : AuxQuestion ℓ)
    (h : 0 < (auxGame L D E X Z projectPauli DP).μ t u) :
    TypeGraph.Adj E X Z (.inr t) (.inr u) := by
  by_contra hn
  rw [auxGame_mu_nonadj L D E X Z projectPauli DP t u hn] at h
  exact (lt_irrefl 0) h

variable (R : SyncStrategy (sourceGame L D).doubled)
  (hL : ∀ w, (L w).SupportedOn Finset.univ)

/-- A single actual synchronous strategy covering all auxiliary types at once. -/
def auxStrategy : SyncStrategy (auxGame L D E X Z projectPauli DP).doubled where
  d := Fintype.card ((ι → F) × Fin R.d)
  d_pos := by
    let : Nonempty (Fin R.d) := Fin.pos_iff_nonempty.mp R.d_pos
    exact Fintype.card_pos
  P :=
    { M := fun q a => registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm
        (auxOp L D R hL q.2 a)
      selfAdjoint := fun q a => by
        rw [Matrix.star_eq_conjTranspose]
        exact (registerOp_isPVM _ (auxOp_isPVM L D R hL q.2)).isSelfAdjoint a
      projective := fun q a => (registerOp_isPVM _ (auxOp_isPVM L D R hL q.2)).idem a
      normalized := fun q => (registerOp_isPVM _ (auxOp_isPVM L D R hL q.2)).sum_eq_one }

theorem auxStrategy_dimension :
    (auxStrategy L D E X Z projectPauli DP R hL).d = Fintype.card (ι → F) * R.d := by
  simp [auxStrategy, Fintype.card_prod]

private theorem doubled_adj (p q : Bool × AuxQuestion ℓ)
    (hμ : 0 < (auxGame L D E X Z projectPauli DP).doubled.μ p q) :
    (p.1 = false ∧ q.1 = true) ∧ TypeGraph.Adj E X Z (.inr p.2) (.inr q.2) := by
  have ht : p.1 = false ∧ q.1 = true := by
    by_contra hn
    simp only [Game.doubled_μ, if_neg hn] at hμ
    exact (lt_irrefl 0) hμ
  refine ⟨ht, auxGame_mu_pos_adj L D E X Z projectPauli DP p.2 q.2 ?_⟩
  simpa only [Game.doubled_μ, if_pos ht] using hμ

set_option backward.isDefEq.respectTransparency false in
theorem auxStrategy_isPCC (hR : R.IsPCC) :
    (auxStrategy L D E X Z projectPauli DP R hL).IsPCC := by
  intro p q hμ a b
  have ha := (doubled_adj L D E X Z projectPauli DP p q hμ).2
  have hh := congrArg (registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm)
    (auxOp_commute L D R hL hR E X Z p.2 q.2 ha a b).eq
  simpa only [auxStrategy, registerOp_mul] using hh

set_option backward.isDefEq.respectTransparency false in
theorem auxStrategy_value (hR : R.IsPCC) (hval : R.value = 1) :
    (auxStrategy L D E X Z projectPauli DP R hL).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro p q hμ a b hrej
  obtain ⟨htags, hadj⟩ := doubled_adj L D E X Z projectPauli DP p q hμ
  have hd : TypedPredicate.check L X Z projectPauli D DP (.inr p.2) (.inr q.2) a b = false := by
    change (if p.1 = false ∧ q.1 = true then
      TypedPredicate.check L X Z projectPauli D DP (.inr p.2) (.inr q.2) a b else false) = false at hrej
    simpa only [if_pos htags] using hrej
  have hz : (auxStrategy L D E X Z projectPauli DP R hL).P.M p a *
      (auxStrategy L D E X Z projectPauli DP R hL).P.M q b = 0 := by
    have hh := congrArg (registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm)
      (auxOp_reject_zero L D R hL hR hval E X Z projectPauli DP p.2 q.2 hadj a b hd)
    rw [show registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm
      (0 : Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ) = 0 from rfl] at hh
    simpa only [auxStrategy, registerOp_mul] using hh
  rw [hz, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

include hL in
/-- Perfect original PCC strategies extend to the full auxiliary introspection game,
with exactly the seed-register dimension increase. -/
theorem exists_auxPerfectPCC (hR : R.IsPCC) (hval : R.value = 1) :
    ∃ Q : SyncStrategy (auxGame L D E X Z projectPauli DP).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = Fintype.card (ι → F) * R.d :=
  ⟨auxStrategy L D E X Z projectPauli DP R hL,
    auxStrategy_isPCC L D E X Z projectPauli DP R hL hR,
    auxStrategy_value L D E X Z projectPauli DP R hL hR hval,
    auxStrategy_dimension L D E X Z projectPauli DP R hL⟩

end MIPRE.Introspection.Honest
