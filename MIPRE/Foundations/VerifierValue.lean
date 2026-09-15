/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GapCompression
import MIPRE.Foundations.GameTransport

/-!
# The games of a verifier: congruence, answer padding, perfect PCC strategies

Bookkeeping for `Verifier.game n T` needed by the instantiation of the compressibility
criterion (blueprint `rem:compression-abstract`), all consequences of the transport lemmas of
`GameTransport`:

* **Same sampler, comparable deciders.** Two verifiers with the same sampler whose deciders
  accept the same tuples at index `n` have the same `val*` and the same perfect PCC strategies
  there (`valStar_congr`, `hasPerfectPCC_congr`); accepting more raises `val*`
  (`valStar_le_of_accepts_imp`).
* **Answer padding.** Enlarging the answer-length bound `T` can only raise `val*`
  (`valStar_le_of_le`) and preserves perfect PCC strategies (`hasPerfectPCC_of_le`); when the
  decider rejects every answer longer than `T`, it does not change `val*` at all
  (`valStar_eq_of_rejects`). This is what lets the game of a verifier be compared across the
  answer bounds `N ^ λ` and `poly(n, λ)` of `GapCompression` and the bound a class of
  descriptions is defined with.
* A perfect PCC strategy gives `val* = 1` (`valStar_eq_one_of_hasPerfectPCC`), through
  `syncValue_le_quantumValue`.
-/

namespace MIPRE

open Cost

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The embedding of the answers of length at most `T` into those of length at most `T'`. -/
def Answers.castLE {T T' : ℕ} (h : T ≤ T') : Answers T ↪ Answers T' :=
  ⟨fun a => ⟨a.1, a.2.trans h⟩, fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)⟩

@[simp] theorem Answers.castLE_val {T T' : ℕ} (h : T ≤ T') (a : Answers T) :
    (Answers.castLE h a).1 = a.1 := rfl

instance (T : ℕ) : Nonempty (Answers T) := ⟨⟨[], Nat.zero_le T⟩⟩

theorem game_μ (n T : ℕ) (x y : V.Questions n) : (V.game n T).μ x y = V.sampler.dist n x y := rfl

theorem game_D (n T : ℕ) (x y : V.Questions n) (a b : Answers T) :
    ((V.game n T).D x y a b = true) ↔
      V.decider.Accepts n (CL.toBits x) (CL.toBits y) a.1 b.1 := by
  classical
  exact decide_eq_true_iff

/-! ## Same sampler, comparable deciders -/

/-- With the same sampler, a decider accepting more at index `n` gives a larger `val*`. -/
theorem valStar_le_of_accepts_imp {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b → W.decider.Accepts n x y a b) :
    V.valStar n T ≤ W.valStar n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV⟩ := V
  simp only at hS
  subst hS
  refine quantumValue_mono _ _ (fun _ _ => rfl) fun x y a b hd => ?_
  rw [game_D] at hd ⊢
  exact h _ _ _ _ hd

/-- With the same sampler, deciders accepting the same tuples at index `n` give the same
`val*`. -/
theorem valStar_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valStar n T = W.valStar n T :=
  le_antisymm (valStar_le_of_accepts_imp hS fun x y a b => (h x y a b).1)
    (valStar_le_of_accepts_imp hS.symm fun x y a b => (h x y a b).2)

/-- With the same sampler, deciders accepting the same tuples at index `n` have the same
perfect PCC strategies. -/
theorem hasPerfectPCC_of_accepts_iff {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV'⟩ := V
  simp only at hS
  subst hS
  obtain ⟨hsync, S, hpcc, hval⟩ := hV
  have hsync' : IsSynchronousAt ⟨SW, DW, hW⟩ n := fun x a b hab hacc =>
    hsync x a b hab ((h _ _ _ _).2 hacc)
  have hD : ∀ x y a b, ((⟨SW, DW, hW⟩ : Verifier ℓ).syncGame n T hsync').D x y a b =
      ((⟨SW, DV, hV'⟩ : Verifier ℓ).syncGame n T hsync).D x y a b := by
    intro x y a b
    classical
    exact decide_eq_decide.2 (h _ _ _ _).symm
  refine ⟨hsync', S.copy _, S.isPCC_copy hpcc _ (fun _ _ => rfl), ?_⟩
  rw [S.value_copy (Verifier.syncGame ⟨SW, DW, hW⟩ n T hsync') (fun _ _ => rfl) hD, hval]

theorem hasPerfectPCC_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.HasPerfectPCC n T ↔ W.HasPerfectPCC n T :=
  ⟨hasPerfectPCC_of_accepts_iff hS h,
    hasPerfectPCC_of_accepts_iff hS.symm fun x y a b => (h x y a b).symm⟩

/-! ## Answer padding -/

/-- Enlarging the answer-length bound can only raise `val*`. -/
theorem valStar_le_of_le {n T T' : ℕ} (hT : T ≤ T') : V.valStar n T ≤ V.valStar n T' := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  rw [← S.value_extendAnswers (V.game n T') (Answers.castLE hT) (Answers.castLE hT)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  exact le_ciSup (TensorProductStrategy.bddAbove_range_value _) _

/-- When the decider rejects every answer longer than `T` at index `n`, enlarging the
answer-length bound does not change `val*`. -/
theorem valStar_eq_of_rejects {n T T' : ℕ} (hT : T ≤ T')
    (hrej : ∀ x y a b, T < a.length ∨ T < b.length → ¬ V.decider.Accepts n x y a b) :
    V.valStar n T' = V.valStar n T := by
  refine quantumValue_extendAnswers (V.game n T) (V.game n T') (Answers.castLE hT)
    (Answers.castLE hT) (fun _ _ => rfl) (fun _ _ _ _ => rfl) ?_
  intro x y a' b' h
  rw [game_D] at h
  by_cases hlen : T < a'.1.length ∨ T < b'.1.length
  · exact absurd h (hrej _ _ _ _ hlen)
  · rw [not_or, not_lt, not_lt] at hlen
    exact ⟨⟨⟨a'.1, hlen.1⟩, Subtype.ext rfl⟩, ⟨⟨b'.1, hlen.2⟩, Subtype.ext rfl⟩⟩

/-- Enlarging the answer-length bound preserves perfect PCC strategies. -/
theorem hasPerfectPCC_of_le {n T T' : ℕ} (hT : T ≤ T') (h : V.HasPerfectPCC n T) :
    V.HasPerfectPCC n T' := by
  obtain ⟨hs, S, hpcc, hval⟩ := h
  refine ⟨hs, S.extend (V.syncGame n T' hs) (Answers.castLE hT),
    S.isPCC_extend hpcc _ _ (fun _ _ => rfl), ?_⟩
  rw [S.value_extend (V.syncGame n T' hs) (Answers.castLE hT) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl), hval]

/-! ## Perfect PCC strategies and the quantum value -/

/-- A perfect PCC strategy gives quantum value `1`. -/
theorem valStar_eq_one_of_hasPerfectPCC {n T : ℕ} (h : V.HasPerfectPCC n T) :
    V.valStar n T = 1 := by
  obtain ⟨hs, S, -, hval⟩ := h
  refine le_antisymm (quantumValue_le_one _) ?_
  have h1 := le_ciSup (TensorProductStrategy.bddAbove_range_value
    (V.syncGame n T hs).toGame) S.toTensorProductStrategy
  rw [SyncStrategy.value_toTensorProductStrategy, hval] at h1
  exact h1

end Verifier

end MIPRE
