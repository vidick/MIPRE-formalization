/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.ModelSoundness
public import MIPRE.Foundations.FinitePairExpand

@[expose] public section

/-!
# The low-individual-degree test in finite pairs, and values approached in sound models

Phase 6 of `planning/mipco-track.md` takes as its target, in place of `LIDT.Simul.SoundCo`, the
soundness of the seeded CL test in every **finite pair** (`SoundFin`, `def:lidt-sound-fin`): the
models whose two algebras are each other's commutants and both carry a faithful tracial state
(`MIPRE.BipartiteModel.IsFinitePair`), with an arbitrary vector state
(`reports/lidt-co-audit.md`, §3.4). `SoundFin` and `SoundCo` are incomparable as statements; what
`SoundFin` buys is a trace on both algebras. Like `SoundCo` (`SoundCo.expand`), it holds in every
ancilla extension by a unit vector of a model in its class (`SoundFin.expand`), the class being
closed under them.

The answer-reduction analysis applies the hypothesis inside the model of one near-optimal
projective strategy, so what it needs of a value model `ω` is that `ω` be approached by projective
strategies of models in which the test is sound and which `ω` dominates (`ApproxSoundIn ω`).
`val*` has it through the tensor-product models of tensor-product strategies
(`approxSoundIn_tensor`). Both hypotheses give it for `ω_co`: `SoundCo` through the
commuting-operator models (`approxSoundIn_commuting`), and `SoundFin` through finite pairs, given
that `ω_co` is approached in finite pairs (`approxSoundIn_commuting_of_fin`; the approximation is
`MIPRE.Repetition.commutingFinitePairApprox`, from Lin's tracial density).
-/

namespace MIPRE.LIDT.Simul

/-- **The seeded CL test is sound in every finite pair** (`def:lidt-sound-fin`): `SoundIn M` for
every bipartite model `M` on a Hilbert space of `Type` whose two algebras are each other's
commutants and carry faithful tracial states (`BipartiteModel.IsFinitePair`). The target of Phase
6 of `planning/mipco-track.md`. -/
def SoundFin : Prop :=
  ∀ {𝒞 𝒜 ℬ : Type} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (M : BipartiteModel.{0} 𝒞 𝒜 ℬ), M.IsFinitePair → SoundIn M

/-- **The seeded CL test is sound in every extension of a finite pair by a unit vector**, when it
is sound in every finite pair: the registers of a unit vector are nonempty
(`nonempty_of_norm_evec_eq_one`), and the extension is again a finite pair
(`BipartiteModel.IsFinitePair.expand`). The Pauli basis analysis applies the test there
(`QLD.soundIn_of_lidt`). -/
theorem SoundFin.expand (h : SoundFin) {𝒞 𝒜 ℬ : Type} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
    [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜]
    [StarModule ℂ ℬ] [StarProper ℬ] {M : BipartiteModel.{0} 𝒞 𝒜 ℬ} (hM : M.IsFinitePair)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α × β → ℂ)
    (he : ‖evec e‖ = 1) : SoundIn (M.expand e) := by
  obtain ⟨_, _⟩ := nonempty_of_norm_evec_eq_one he
  exact h _ (hM.expand e)

/-- **The value model is approached by projective strategies of models in which the seeded test
is sound and which it dominates**: below the value of a game, and above `0`, lies the value of
such a strategy, on a Hilbert space of `Type`. Answer reduction applies the test inside the model
of such a strategy (`AnswerReduction.arVerifier_soundness_of_approx`). -/
def ApproxSoundIn (ω : ValueModel) : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G : Game X Y A B) {t : ℝ},
    0 ≤ t → t < ω.val G →
      ∃ (𝒞 𝒜 ℬ : Type) (_ : Ring 𝒞) (_ : StarRing 𝒞) (_ : Algebra ℂ 𝒞) (_ : Ring 𝒜)
        (_ : StarRing 𝒜) (_ : Algebra ℂ 𝒜) (_ : Ring ℬ) (_ : StarRing ℬ) (_ : Algebra ℂ ℬ)
        (_ : PartialOrder 𝒜) (_ : StarOrderedRing 𝒜) (_ : PartialOrder ℬ)
        (_ : StarOrderedRing ℬ) (M : BipartiteModel.{0} 𝒞 𝒜 ℬ),
        SoundIn M ∧ ω.Dominates M ∧ ∃ S : M.ProjStrat G, t < S.value

/-- **`val*` is approached in tensor-product models**, where the test is sound
(`soundIn_tensor`) and which `val*` dominates (`ValueModel.tensor_dominates`): a tensor-product
strategy near the supremum is a projective strategy of its model, of the same value. -/
theorem approxSoundIn_tensor : ApproxSoundIn .tensor := fun G t ht h => by
  rw [ValueModel.tensor_val, quantumValue] at h
  rcases isEmpty_or_nonempty (TensorProductStrategy G) with hG | hG
  · rw [Real.iSup_of_isEmpty] at h
    exact absurd ht (not_le.mpr h)
  obtain ⟨T, hT⟩ := exists_lt_of_lt_ciSup h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, BipartiteModel.tensor T.ψ,
    soundIn_tensor T.ψ, ValueModel.tensor_dominates T.ψ, T.toModel, by rwa [T.value_toModel]⟩

/-- **`ω_co` is approached in the models of commuting-operator strategies**
(`exists_projStrat_lt_commutingOperatorValue`), where the test is sound if `SoundCo` holds. -/
theorem approxSoundIn_commuting (h : SoundCo) : ApproxSoundIn .commuting := fun G t ht hv => by
  obtain ⟨S, R, hR⟩ := exists_projStrat_lt_commutingOperatorValue ht hv
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, S.toModel, h S,
    ValueModel.commuting_dominates _, R, hR⟩

/-- **`ω_co` is approached in finite pairs**, where the test is sound if `SoundFin` holds, as soon
as `ω_co` is approached by projective strategies in finite pairs (`CommutingFinitePairApprox`,
proved as `MIPRE.Repetition.commutingFinitePairApprox`). -/
theorem approxSoundIn_commuting_of_fin (hV : CommutingFinitePairApprox) (h : SoundFin) :
    ApproxSoundIn .commuting := fun G t ht hv => by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, M, hM, S, hS⟩ := hV G ht hv
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, M, h M hM,
    ValueModel.commuting_dominates M, S, hS⟩

end MIPRE.LIDT.Simul

end
