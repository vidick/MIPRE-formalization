/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.AnswerReduction.Complete
public import MIPRE.Foundations.CL.DetypingModel
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

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

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

set_option synthInstance.maxSize 1024 in
/-- The finite detyped game the answer-reduced verifier's game at the answer cut numbers. The
derived decidable equality of the types is large, and its question set's `Fintype` instance
needs a larger instance search. -/
abbrev arFiniteGame :=
  CL.Detyping.game graph
    (CL.Detyping.DeciderProgram.sourceFamily (typedSampler V.sampler PD lam mu sigma) n)
    (CL.Detyping.DeciderProgram.typedPredicate (typedSampler V.sampler PD lam mu sigma)
      (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) n)

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 10000 in
/-- **The typed strategy** of a projective strategy, in a bipartite model, for the answer-reduced
verifier's game at the answer cut: the strategy read in the finite detyped game its questions
number (`CL.Detyping.DeciderProgram.vectorEquiv`), then detyping's restriction to the fixed graph
views, read in the typed game with the predicate `typedPred`. The same measurements, asked at
other questions: projective, on the same state. -/
def typedStrategy (R : M.ProjStrat
    ((arVerifier PD lam mu sigma V).game n (cutVal (arPar PD lam mu sigma n)))) :
    M.ProjStrat (arTypedGame PD lam mu sigma V n) :=
  (R.relabel (arFiniteGame PD lam mu sigma V n)
    (CL.Detyping.DeciderProgram.vectorEquiv _) (CL.Detyping.DeciderProgram.vectorEquiv _)
    (Equiv.refl _) (Equiv.refl _)).restrict _ (CL.Detyping.question graph false)
    (CL.Detyping.question graph true)

set_option synthInstance.maxSize 1024 in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- **Detyping soundness for answer reduction**, in a bipartite model: the typed strategy loses at
most a factor `16^{54}` in failure probability. -/
theorem typedStrategy_value_ge (R : M.ProjStrat
    ((arVerifier PD lam mu sigma V).game n (cutVal (arPar PD lam mu sigma n))))
    {ε : ℝ} (hR : 1 - ε ≤ R.value) :
    1 - (16 : ℝ) ^ Fintype.card ArTy * ε ≤ (typedStrategy PD lam mu sigma V n R).value := by
  set R' := R.relabel (arFiniteGame PD lam mu sigma V n)
    (CL.Detyping.DeciderProgram.vectorEquiv _) (CL.Detyping.DeciderProgram.vectorEquiv _)
    (Equiv.refl _) (Equiv.refl _) with hR'
  have hv : R'.value = R.value :=
    R.value_relabel _ _ _ _ _
      (fun x y => (CL.Detyping.DeciderProgram.verifier_game_mu graph
        (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
        (arCut PD lam mu sigma) (by unfold level; omega) (total PD V lam mu sigma) n x y).symm)
      (fun x y a b => (CL.Detyping.DeciderProgram.verifier_game_D graph
        (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
        (arCut PD lam mu sigma) (by unfold level; omega) (total PD V lam mu sigma) n x y a b).symm)
  have h := CL.Detyping.restrict_povmValue_ge M R.ψ_unit graph (fun _ _ _ => trivial)
    graph_nonempty
    (CL.Detyping.DeciderProgram.sourceFamily (typedSampler V.sampler PD lam mu sigma) n)
    (fun w t => (typedSampler V.sampler PD lam mu sigma).cl_exactlyOn n (Player.ofBool w) t)
    (by unfold level; omega)
    (CL.Detyping.DeciderProgram.typedPredicate (typedSampler V.sampler PD lam mu sigma)
      (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) n) R'.PA R'.PB
    (show 1 - ε ≤ R'.value by rw [hv]; exact hR)
  refine h.trans (le_of_eq (M.povmValue_congr_game ?_ ?_ _ _))
  · exact fun _ _ => rfl
  · exact fun p q a b => typedPredicate_eq PD lam mu sigma V n p q a b

end MIPRE.AnswerReduction

end

end
