/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GapCompression
import MIPRE.Foundations.GameTransport
import MIPRE.Foundations.ValueModel

/-!
# The games of a verifier: congruence, answer padding, perfect PCC strategies

Bookkeeping for `Verifier.game n T` needed by the instantiation of the compressibility
criterion (blueprint `rem:compression-abstract`), in any value model `ω` (`ValueModel`) — the
tensor-product value `val*` and the commuting-operator value `ω_co` are its two instances — all
consequences of the transport properties a model carries:

* **Same sampler, comparable deciders.** Two verifiers with the same sampler whose deciders
  accept the same tuples at index `n` have the same value and the same perfect PCC strategies
  there (`val_congr`, `hasPerfectPCC_congr`); accepting more raises the value
  (`val_le_of_accepts_imp`).
* **Answer padding.** Enlarging the answer-length bound `T` can only raise the value
  (`val_le_of_le`) and preserves perfect PCC strategies (`hasPerfectPCC_of_le`); when the
  decider rejects every answer longer than `T`, it does not change the value at all
  (`val_eq_of_rejects`). This is what lets the game of a verifier be compared across the
  answer bounds `N ^ λ` and `poly(n, λ)` of `GapCompression` and the bound a class of
  descriptions is defined with.
* A perfect PCC strategy gives `val* = 1` (`valStar_eq_one_of_hasPerfectPCC`), through
  `syncValue_le_quantumValue` on the doubled game and `quantumValue_doubledGame`, hence value
  `1` in every model (`val_eq_one_of_hasPerfectPCC`), the model dominating `val*`.

`Verifier.val ω n T` is the value of `𝒱_n` in the model; `Verifier.valStar` is its
tensor-product instance, definitionally, and the `valStar_*` lemmas below are the generic ones
at `ValueModel.tensor`. `Verifier.HasPerfectPCC` is a PCC strategy of value `1` on the *doubled*
game (`Verifier.doubledGame`, `Foundations/GapCompression.lean`), so none of the lemmas here asks
the decider to be synchronous at `n`. The file ends with `GapCompression.Sound ω`, the soundness
clause of gap compression read in the model: `soundness` is `Sound ValueModel.tensor`, and the
commuting-operator case is the hypothesis of the conditional `MIP^co = coRE`.
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

/-! ## The value of `𝒱_n` in a model -/

/-- The value of `𝒱_n` in the model `ω`, with answers of length at most `T`. -/
noncomputable def val (ω : ValueModel) (n T : ℕ) : ℝ := ω.val (V.game n T)

@[simp] theorem val_tensor (n T : ℕ) : V.val .tensor n T = V.valStar n T := rfl

@[simp] theorem val_commuting (n T : ℕ) :
    V.val .commuting n T = commutingOperatorValue (V.game n T) := rfl

/-- Every model dominates `val*`. -/
theorem valStar_le_val (ω : ValueModel) (n T : ℕ) : V.valStar n T ≤ V.val ω n T :=
  ω.quantumValue_le _

theorem val_nonneg (ω : ValueModel) (n T : ℕ) : 0 ≤ V.val ω n T := ω.nonneg _

theorem val_le_one (ω : ValueModel) (n T : ℕ) : V.val ω n T ≤ 1 := ω.le_one _

/-! ## Same sampler, comparable deciders -/

/-- With the same sampler, a decider accepting more at index `n` gives a larger value. -/
theorem val_le_of_accepts_imp (ω : ValueModel) {V W : Verifier ℓ} {n T : ℕ}
    (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b → W.decider.Accepts n x y a b) :
    V.val ω n T ≤ W.val ω n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV⟩ := V
  simp only at hS
  subst hS
  refine ω.mono _ _ (fun _ _ => rfl) fun x y a b hd => ?_
  rw [game_D] at hd ⊢
  exact h _ _ _ _ hd

/-- With the same sampler, deciders accepting the same tuples at index `n` give the same
value. -/
theorem val_congr (ω : ValueModel) {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.val ω n T = W.val ω n T :=
  le_antisymm (val_le_of_accepts_imp ω hS fun x y a b => (h x y a b).1)
    (val_le_of_accepts_imp ω hS.symm fun x y a b => (h x y a b).2)

theorem valStar_le_of_accepts_imp {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b → W.decider.Accepts n x y a b) :
    V.valStar n T ≤ W.valStar n T :=
  val_le_of_accepts_imp .tensor hS h

theorem valStar_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valStar n T = W.valStar n T :=
  val_congr .tensor hS h

/-- With the same sampler, deciders accepting the same tuples at index `n` have the same
perfect PCC strategies. -/
theorem hasPerfectPCC_of_accepts_iff {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV'⟩ := V
  simp only at hS
  subst hS
  obtain ⟨S, hpcc, hval⟩ := hV
  have hD : ∀ p q a b, ((⟨SW, DW, hW⟩ : Verifier ℓ).doubledGame n T).D p q a b =
      ((⟨SW, DV, hV'⟩ : Verifier ℓ).doubledGame n T).D p q a b := by
    intro p q a b
    classical
    simp only [doubledGame, Game.doubled_D]
    split_ifs
    · exact decide_eq_decide.2 (h _ _ _ _).symm
    · rfl
  refine ⟨S.copy _, S.isPCC_copy hpcc _ (fun _ _ => rfl), ?_⟩
  rw [S.value_copy (Verifier.doubledGame ⟨SW, DW, hW⟩ n T) (fun _ _ => rfl) hD, hval]

theorem hasPerfectPCC_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.HasPerfectPCC n T ↔ W.HasPerfectPCC n T :=
  ⟨hasPerfectPCC_of_accepts_iff hS h,
    hasPerfectPCC_of_accepts_iff hS.symm fun x y a b => (h x y a b).symm⟩

/-! ## Answer padding -/

/-- Enlarging the answer-length bound can only raise the value. -/
theorem val_le_of_le (ω : ValueModel) {n T T' : ℕ} (hT : T ≤ T') :
    V.val ω n T ≤ V.val ω n T' :=
  ω.le_extendAnswers (V.game n T) (V.game n T') (Answers.castLE hT) (Answers.castLE hT)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

theorem valStar_le_of_le {n T T' : ℕ} (hT : T ≤ T') : V.valStar n T ≤ V.valStar n T' :=
  V.val_le_of_le .tensor hT

/-- **The decider rejects every answer longer than `T` at index `n`.** The property a compressed
decider has beyond its time bound (`GapCompression.output_rejects_long`), and the third clause
of membership in the classes of the halting reduction (`Verifier.InClassA`, `InClassB`): it is
what lets the answer bound a class is read with be raised without moving the value
(`val_eq_of_rejects`), which the soundness direction of the compressor's obligation needs.
The paper's `V^halt` has it by construction, Step 6 of its decider `F` being an explicit length
check; the classes here range over arbitrary strings and have to ask for it. -/
def RejectsLong (n T : ℕ) : Prop :=
  ∀ x y a b, T < a.length ∨ T < b.length → ¬ V.decider.Accepts n x y a b

/-- When the decider rejects every answer longer than `T` at index `n`, enlarging the
answer-length bound does not change the value. -/
theorem val_eq_of_rejects (ω : ValueModel) {n T T' : ℕ} (hT : T ≤ T') (hrej : V.RejectsLong n T) :
    V.val ω n T' = V.val ω n T := by
  refine ω.extendAnswers (V.game n T) (V.game n T') (Answers.castLE hT) (Answers.castLE hT)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) ?_
  intro x y a' b' h
  rw [game_D] at h
  by_cases hlen : T < a'.1.length ∨ T < b'.1.length
  · exact absurd h (hrej _ _ _ _ hlen)
  · rw [not_or, not_lt, not_lt] at hlen
    exact ⟨⟨⟨a'.1, hlen.1⟩, Subtype.ext rfl⟩, ⟨⟨b'.1, hlen.2⟩, Subtype.ext rfl⟩⟩

theorem valStar_eq_of_rejects {n T T' : ℕ} (hT : T ≤ T') (hrej : V.RejectsLong n T) :
    V.valStar n T' = V.valStar n T :=
  V.val_eq_of_rejects .tensor hT hrej

/-- A decider that accepts nothing at index `n` gives value `0`. -/
theorem val_eq_zero_of_rejects_all (ω : ValueModel) {n T : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.val ω n T = 0 := by
  classical
  refine ω.eq_zero_of_reject _ fun x y a b => ?_
  exact decide_eq_false (hrej _ _ _ _)

/-- Enlarging the answer-length bound preserves perfect PCC strategies. -/
theorem hasPerfectPCC_of_le {n T T' : ℕ} (hT : T ≤ T') (h : V.HasPerfectPCC n T) :
    V.HasPerfectPCC n T' := by
  obtain ⟨S, hpcc, hval⟩ := h
  refine ⟨S.extend (V.doubledGame n T') (Answers.castLE hT),
    S.isPCC_extend hpcc _ _ (fun _ _ => rfl), ?_⟩
  rw [S.value_extend (V.doubledGame n T') (Answers.castLE hT) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl), hval]

/-! ## Perfect PCC strategies and the value -/

/-- A perfect PCC strategy gives quantum value `1`. -/
theorem valStar_eq_one_of_hasPerfectPCC {n T : ℕ} (h : V.HasPerfectPCC n T) :
    V.valStar n T = 1 := by
  obtain ⟨S, -, hval⟩ := h
  refine le_antisymm (quantumValue_le_one _) ?_
  have h1 := le_ciSup (TensorProductStrategy.bddAbove_range_value
    (V.doubledGame n T).toGame) S.toTensorProductStrategy
  rw [SyncStrategy.value_toTensorProductStrategy, hval] at h1
  rw [← V.quantumValue_doubledGame n T]
  exact h1

/-- A perfect PCC strategy gives value `1` in every model: the model dominates `val*`. -/
theorem val_eq_one_of_hasPerfectPCC (ω : ValueModel) {n T : ℕ} (h : V.HasPerfectPCC n T) :
    V.val ω n T = 1 :=
  le_antisymm (V.val_le_one ω n T)
    ((V.valStar_eq_one_of_hasPerfectPCC h).symm.le.trans (V.valStar_le_val ω n T))

/-! ## The doubled game -/

/-- The doubled game has the value it doubles, in every model. -/
theorem val_doubledGame (ω : ValueModel) (n T : ℕ) :
    ω.val (V.doubledGame n T).toGame = V.val ω n T :=
  ω.doubled (V.game n T)

end Verifier

/-- **Soundness of gap compression in a value model** (blueprint `def:compression-co-sound`):
for a `λ`-bounded input and `n ≥ C₀`, a value at most `1/2` of `𝒱_{2^n}` in the model gives a
value at most `1/2` of `𝒱^compr_n`, at the answer bounds of `GapCompression.soundness`. That
field is `Sound ValueModel.tensor` (`GapCompression.sound_tensor`); `Sound ValueModel.commuting`
is the model-`co` case of the soundness clause of Lin's gap compression theorem (`Lin25`,
`thm:gappedcompression`) and the one hypothesis of the conditional `MIP^co = coRE`
(`planning/mipco-track.md`). -/
def GapCompression.Sound (G : GapCompression) (ω : ValueModel) : Prop :=
  ∀ (V : Verifier 7) (lam n : ℕ), V.IsBounded lam → G.C₀ ≤ n →
    V.val ω (2 ^ n) ((2 ^ n) ^ lam) ≤ 1 / 2 →
    (G.output (V.sampler.prog, V.decider.prog) lam).val ω n (G.bound.eval (n + lam)) ≤ 1 / 2

/-- The soundness clause of gap compression is soundness in the tensor-product model. -/
theorem GapCompression.sound_tensor (G : GapCompression) : G.Sound .tensor :=
  fun V lam n hb hn h => G.soundness V lam n hb hn h

end MIPRE
