/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Complete

/-!
# Soundness of answer reduction: the setup

Piece AR-5a of `planning/answer-reduction.md` (`lem:ar-soundness-setup`): a strategy for the
answer-reduced verifier's game at the answer cut, of value at least `1 - ε`, gives a strategy for
the typed answer-reduced game (`typedGame`, with the predicate `typedPred`) of value at least
`1 - 16^{54} ε`, on the same state (`typedStrategy_value_ge`). This is the detyping compiler's
soundness (`CL.Detyping.DeciderProgram.restrictAmbient_value_ge`), read through the typed
decider's acceptance law (`typedPredicate_eq`).

The strategy stays a `TensorProductStrategy`: two families of projective measurements, one per
player. The paper symmetrizes it first (`lem:symmetric-strat`); the Lean does not, and derives
every relation for each ordered pair of players from the ordered pair of types that carries it.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL SAT Pcp Cost

variable (PD : PcpDecider) (lam mu sigma : ℕ) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ)

local notation "F" => family PD lam mu sigma

/-- The typed answer-reduced game of `V` at index `n`, at the answer cut. -/
abbrev arTypedGame :=
  typedGame V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n) (chk PD V lam mu sigma n)
    (cutVal ((F).par n))

set_option maxRecDepth 10000 in
/-- **The typed strategy** of a strategy for the answer-reduced verifier's game at the answer
cut: detyping's restriction, read in the typed game with the predicate `typedPred`. -/
def typedStrategy (R : TensorProductStrategy
    ((arVerifier PD lam mu sigma V).game n (cutVal (arPar PD lam mu sigma n)))) :
    TensorProductStrategy (arTypedGame PD lam mu sigma V n) :=
  (CL.Detyping.DeciderProgram.restrictAmbient graph (typedSampler V.sampler PD lam mu sigma)
    (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) graph_nonempty
    (by unfold level; omega) (total PD V lam mu sigma) n R).relabel _
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem typedStrategy_ψ (R : TensorProductStrategy
    ((arVerifier PD lam mu sigma V).game n (cutVal (arPar PD lam mu sigma n)))) :
    (typedStrategy PD lam mu sigma V n R).ψ = R.ψ := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- **Detyping soundness for answer reduction**: the typed strategy loses at most a factor
`16^{54}` in failure probability. -/
theorem typedStrategy_value_ge (R : TensorProductStrategy
    ((arVerifier PD lam mu sigma V).game n (cutVal (arPar PD lam mu sigma n))))
    {ε : ℝ} (hR : 1 - ε ≤ R.value) :
    1 - (16 : ℝ) ^ Fintype.card ArTy * ε ≤ (typedStrategy PD lam mu sigma V n R).value := by
  have h := CL.Detyping.DeciderProgram.restrictAmbient_value_ge graph
    (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
    (arCut PD lam mu sigma) (fun _ _ _ => trivial) graph_nonempty (by unfold level; omega)
    (total PD V lam mu sigma) n R hR
  have hv : (typedStrategy PD lam mu sigma V n R).value =
      (CL.Detyping.DeciderProgram.restrictAmbient graph (typedSampler V.sampler PD lam mu sigma)
        (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) graph_nonempty
        (by unfold level; omega) (total PD V lam mu sigma) n R).value :=
    TensorProductStrategy.value_relabel
      (CL.Detyping.DeciderProgram.restrictAmbient graph (typedSampler V.sampler PD lam mu sigma)
        (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) graph_nonempty
        (by unfold level; omega) (total PD V lam mu sigma) n R)
      (arTypedGame PD lam mu sigma V n) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (fun _ _ => rfl)
      (fun p q a b => (typedPredicate_eq PD lam mu sigma V n p q a b).symm)
  rw [hv]
  exact h

end MIPRE.AnswerReduction

end
