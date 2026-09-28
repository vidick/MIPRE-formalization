/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CommutingTransport
import MIPRE.Foundations.SyncTransport
import MIPRE.Foundations.VerifierValue

/-!
# The commuting-operator value of a verifier's game

`Verifier.valCo n T`, the bipartite commuting-operator value `ω_co` of `Verifier.game n T`
(`MIPRE.commutingOperatorValue`), and the bookkeeping the `MIP^co = coRE` track needs of it
(`planning/mipco-track.md`, Phase 0), each the `ω_co` reading of a lemma of
`VerifierValue.lean` through the transport lemmas of `CommutingTransport.lean`:

* **Same sampler, comparable deciders.** `valCo_le_of_accepts_imp`, `valCo_congr`.
* **Answer padding.** `valCo_le_of_le`; when the decider rejects every answer longer than `T`,
  raising the bound does not move the value (`valCo_eq_of_rejects`), which is what carries the
  soundness hypothesis of a compressor's obligation across the two answer bounds, as
  `valStar_eq_of_rejects` does for `val*`.
* **The two values.** `valStar_le_valCo`: a tensor-product strategy is a commuting-operator
  strategy (`quantumValue_le_commutingOperatorValue`). This is the inequality that puts the
  class of perfect PCC strategies inside the class of commuting-operator value `1`.
* **Tabulations.** `commutingOperatorValue_toGame_eq_valCo_doubled`: a game description
  matching the doubled game of `𝒱_n` along relabelings of the alphabets has its
  commuting-operator value, the counterpart of `quantumValue_toGame_eq_valStar_doubled`.

The file ends with `GapCompression.CoSound`, the commuting-operator soundness of gap
compression stated in this value: the one hypothesis of the conditional `MIP^co = coRE`.
-/

namespace MIPRE

open Cost

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- `ω_co(𝒱_n)`, the commuting-operator value of the `n`-th game with answers of length at
most `T`. -/
noncomputable def valCo (n T : ℕ) : ℝ := commutingOperatorValue (V.game n T)

/-- A tensor-product strategy is a commuting-operator strategy: `val* ≤ ω_co`. -/
theorem valStar_le_valCo (n T : ℕ) : V.valStar n T ≤ V.valCo n T :=
  quantumValue_le_commutingOperatorValue _

theorem valCo_nonneg (n T : ℕ) : 0 ≤ V.valCo n T := commutingOperatorValue_nonneg _

theorem valCo_le_one (n T : ℕ) : V.valCo n T ≤ 1 := commutingOperatorValue_le_one _

/-! ## Same sampler, comparable deciders -/

/-- With the same sampler, a decider accepting more at index `n` gives a larger `ω_co`. -/
theorem valCo_le_of_accepts_imp {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b → W.decider.Accepts n x y a b) :
    V.valCo n T ≤ W.valCo n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV⟩ := V
  simp only at hS
  subst hS
  refine commutingOperatorValue_mono _ _ (fun _ _ => rfl) fun x y a b hd => ?_
  rw [game_D] at hd ⊢
  exact h _ _ _ _ hd

/-- With the same sampler, deciders accepting the same tuples at index `n` give the same
`ω_co`. -/
theorem valCo_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valCo n T = W.valCo n T :=
  le_antisymm (valCo_le_of_accepts_imp hS fun x y a b => (h x y a b).1)
    (valCo_le_of_accepts_imp hS.symm fun x y a b => (h x y a b).2)

/-! ## Answer padding -/

/-- Enlarging the answer-length bound can only raise `ω_co`. -/
theorem valCo_le_of_le {n T T' : ℕ} (hT : T ≤ T') : V.valCo n T ≤ V.valCo n T' := by
  refine Real.iSup_le (fun S => ?_) (commutingOperatorValue_nonneg _)
  rw [← S.value_extendAnswers (Answers.castLE hT) (Answers.castLE hT) (V.game n T) (V.game n T')
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  exact (S.extendAnswers _ _).value_le_commutingOperatorValue _

/-- When the decider rejects every answer longer than `T` at index `n`, enlarging the
answer-length bound does not change `ω_co`. -/
theorem valCo_eq_of_rejects {n T T' : ℕ} (hT : T ≤ T') (hrej : V.RejectsLong n T) :
    V.valCo n T' = V.valCo n T := by
  refine commutingOperatorValue_extendAnswers (V.game n T) (V.game n T') (Answers.castLE hT)
    (Answers.castLE hT) (fun _ _ => rfl) (fun _ _ _ _ => rfl) ?_
  intro x y a' b' h
  rw [game_D] at h
  by_cases hlen : T < a'.1.length ∨ T < b'.1.length
  · exact absurd h (hrej _ _ _ _ hlen)
  · rw [not_or, not_lt, not_lt] at hlen
    exact ⟨⟨⟨a'.1, hlen.1⟩, Subtype.ext rfl⟩, ⟨⟨b'.1, hlen.2⟩, Subtype.ext rfl⟩⟩

/-- A decider that accepts nothing at index `n` gives `ω_co = 0`. -/
theorem valCo_eq_zero_of_rejects_all {n T : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.valCo n T = 0 := by
  classical
  refine commutingOperatorValue_eq_zero_of_reject _ fun x y a b => ?_
  exact decide_eq_false (hrej _ _ _ _)

/-! ## The doubled game and its tabulations -/

/-- The doubled game has the commuting-operator value of the game it doubles. -/
theorem commutingOperatorValue_doubledGame (n T : ℕ) :
    commutingOperatorValue (V.doubledGame n T).toGame = V.valCo n T :=
  commutingOperatorValue_doubled (V.game n T)

open HaltingGameValue (GameData) in
/-- **The value bridge, doubled, in the commuting-operator value.** A game description matching
`𝒱_n`'s doubled game along relabelings of the two alphabets has `ω_co(𝒱_n)`; the counterpart
of `quantumValue_toGame_eq_valStar_doubled`, with the same matching data. -/
theorem commutingOperatorValue_toGame_eq_valCo_doubled (n T : ℕ) (g : GameData)
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l)) :
    commutingOperatorValue g.game = V.valCo n T := by
  rw [← V.commutingOperatorValue_doubledGame n T]
  exact commutingOperatorValue_eq_of_equiv (V.doubledGame n T).toGame g.game eX eX eA eA hμ hD

end Verifier

/-- **Commuting-operator soundness of gap compression**, the soundness clause of
`GapCompression` read in the commuting-operator value `ω_co` (blueprint
`def:compression-co-sound`): for a `λ`-bounded input and `n ≥ C₀`, `ω_co(𝒱_{2^n}) ≤ 1/2` implies
`ω_co(𝒱^compr_n) ≤ 1/2`, at the same answer bounds as `GapCompression.soundness`. This is the
model-`co` case of the soundness clause of Lin's gap compression theorem (`Lin25`,
`thm:gappedcompression`), and the one hypothesis of the conditional `MIP^co = coRE`
(`planning/mipco-track.md`); the value-form pipeline of chapter 6 proves the tensor case
only. -/
def GapCompression.CoSound (G : GapCompression) : Prop :=
  ∀ (V : Verifier 7) (lam n : ℕ), V.IsBounded lam → G.C₀ ≤ n →
    V.valCo (2 ^ n) ((2 ^ n) ^ lam) ≤ 1 / 2 →
    (G.output (V.sampler.prog, V.decider.prog) lam).valCo n (G.bound.eval (n + lam)) ≤ 1 / 2

end MIPRE
