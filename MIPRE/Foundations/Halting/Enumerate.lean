/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Wrapper
import MIPRE.Foundations.GameDescription
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Algebra.BigOperators.Fin

/-!
# Enumerating the questions and the answers of `𝒱_n`

The tabulation of `𝒱_n` as a game description (blueprint `def:game-description`,
`rem:compression-abstract`) indexes the questions and the answers by `Fin (nX + 1)` and
`Fin (nA + 1)`. This file provides the two indexings, explicitly and computably, together with
the agreement of the tabulated value with `val*`.

* `Data.bitStrsOfLen k` and `Data.bitStrsLE T`: the bit strings of length exactly `k`, and of
  length at most `T`, without repetition (`nodup_bitStrsLE`, `mem_bitStrsLE`); the second has
  `2 ^ (T + 1) - 1` entries.
* `Verifier.answerList T` and `Verifier.answerEquiv T : Fin (answerList T).length ≃ Answers T`:
  the answer alphabet, enumerated.
* `Verifier.questionEquiv s : Fin (2 ^ s) ≃ (Fin s → CL.𝔽₂)`: the question alphabet, from
  Mathlib's `finFunctionFinEquiv` (`𝔽₂ = ZMod 2` is `Fin 2`).
* `Verifier.quantumValue_toGame_eq_valStar`: a game description whose distribution and decision
  predicate match `𝒱_n` along these indexings has `val*(G) = val*(𝒱_n)`. This is the bridge
  `rem:compression-abstract` needs between the criterion's semidecision procedure, which runs on
  game descriptions (`lem:value-lower-approx`), and the verifiers of the pipeline.

What is still owed is the *computation* of such a description from an `n`-bounded verifier —
running the sampler on every point of `𝔽₂^{s(n)}` to count the question weights, and the decider
under its budget to fill in the acceptance table (`planning/formalization-plan.md`, H4).
-/

namespace MIPRE

open Cost

namespace Cost.Data

/-- The bit strings of length exactly `k`. -/
def bitStrsOfLen : ℕ → List BitStr
  | 0 => [[]]
  | k + 1 => (bitStrsOfLen k).flatMap fun l => [false :: l, true :: l]

@[simp] theorem mem_bitStrsOfLen (k : ℕ) (l : BitStr) : l ∈ bitStrsOfLen k ↔ l.length = k := by
  induction k generalizing l with
  | zero => simp [bitStrsOfLen, List.length_eq_zero_iff]
  | succ k ih =>
    simp only [bitStrsOfLen, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨l', hl', rfl | rfl⟩ <;> simp [(ih l').1 hl']
    · intro hl
      cases l with
      | nil => simp at hl
      | cons c l =>
        refine ⟨l, (ih l).2 (by simpa using hl), ?_⟩
        cases c <;> simp

theorem nodup_bitStrsOfLen (k : ℕ) : (bitStrsOfLen k).Nodup := by
  induction k with
  | zero => simp [bitStrsOfLen]
  | succ k ih =>
    refine List.nodup_flatMap.2 ⟨?_, ?_⟩
    · intro l _
      simp
    · refine ih.pairwise_of_forall_ne fun l hl l' hl' hne => ?_
      simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl | rfl) <;> rintro (h | h) <;> exact hne (by simp_all)

@[simp] theorem length_bitStrsOfLen (k : ℕ) : (bitStrsOfLen k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bitStrsOfLen, List.length_flatMap, List.map_const', List.sum_replicate,
      smul_eq_mul, ih, List.length_cons, List.length_nil]
    ring

/-- The bit strings of length at most `T`. -/
def bitStrsLE (T : ℕ) : List BitStr := (List.range (T + 1)).flatMap bitStrsOfLen

@[simp] theorem mem_bitStrsLE (T : ℕ) (l : BitStr) : l ∈ bitStrsLE T ↔ l.length ≤ T := by
  simp only [bitStrsLE, List.mem_flatMap, List.mem_range, mem_bitStrsOfLen]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨l.length, by omega, rfl⟩

theorem nodup_bitStrsLE (T : ℕ) : (bitStrsLE T).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun k _ => nodup_bitStrsOfLen k, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun k _ k' _ hne => ?_
  simp only [List.disjoint_left, mem_bitStrsOfLen]
  rintro z rfl h
  exact hne h

/-! The two enumerations are primitive recursive: the tabulation of `MIPRE.Halting` walks both
of them, so both are on the critical path of `MIPRE.Halting.tab_computable`. -/

theorem primrec_bitStrsOfLen : Primrec Data.bitStrsOfLen := by
  have hstep : Primrec₂ fun (_ : Unit) (p : ℕ × List BitStr) =>
      p.2.flatMap fun l => [false :: l, true :: l] := by
    refine (Primrec.list_flatMap
      (f := fun q : Unit × ℕ × List BitStr => q.2.2)
      (g := fun _ (l : BitStr) => [false :: l, true :: l])
      (Primrec.snd.comp Primrec.snd) ?_).to₂
    have h1 : Primrec fun q : (Unit × ℕ × List BitStr) × BitStr => false :: q.2 :=
      Primrec.list_cons.comp (Primrec.const false) Primrec.snd
    have h2 : Primrec fun q : (Unit × ℕ × List BitStr) × BitStr => true :: q.2 :=
      Primrec.list_cons.comp (Primrec.const true) Primrec.snd
    exact (Primrec.list_cons.comp h1
      (Primrec.list_cons.comp h2 (Primrec.const ([] : List BitStr)))).to₂
  have h := Primrec.nat_rec' (f := fun n : ℕ => n) (g := fun _ : ℕ => [([] : BitStr)])
    Primrec.id (Primrec.const _) (hstep.comp (Primrec.const ()) Primrec.snd).to₂
  refine h.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih => rw [Data.bitStrsOfLen, ← ih]

theorem primrec_bitStrsLE : Primrec Data.bitStrsLE :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ))
    (primrec_bitStrsOfLen.comp Primrec.snd).to₂

theorem length_bitStrsLE_pos (T : ℕ) : 0 < (bitStrsLE T).length :=
  List.length_pos_iff.2 fun h => by
    have := (mem_bitStrsLE T []).2 (Nat.zero_le T)
    rw [h] at this
    simp at this

end Cost.Data

namespace Verifier

open Cost Cost.Data

/-! ## The answer alphabet -/

/-- A bit string as an answer of length at most `T`, by truncation (the identity on the
strings that already fit). -/
def toAnswer (T : ℕ) (l : BitStr) : Answers T :=
  ⟨l.take T, by rw [List.length_take]; exact Nat.min_le_left _ _⟩

@[simp] theorem toAnswer_val (T : ℕ) (a : Answers T) : toAnswer T a.1 = a :=
  Subtype.ext (List.take_of_length_le a.2)

/-- The answers of length at most `T`, enumerated. -/
def answerList (T : ℕ) : List (Answers T) := (bitStrsLE T).map (toAnswer T)

@[simp] theorem mem_answerList (T : ℕ) (a : Answers T) : a ∈ answerList T := by
  rw [answerList, List.mem_map]
  exact ⟨a.1, (mem_bitStrsLE T a.1).2 a.2, toAnswer_val T a⟩

theorem nodup_answerList (T : ℕ) : (answerList T).Nodup := by
  refine (nodup_bitStrsLE T).map_on fun l hl l' hl' h => ?_
  have e : l.take T = l'.take T := congrArg Subtype.val h
  rwa [List.take_of_length_le ((mem_bitStrsLE T l).1 hl),
    List.take_of_length_le ((mem_bitStrsLE T l').1 hl')] at e

theorem length_answerList_pos (T : ℕ) : 0 < (answerList T).length := by
  rw [answerList, List.length_map]
  exact length_bitStrsLE_pos T

/-- The answer alphabet, indexed. -/
noncomputable def answerEquiv (T : ℕ) : Fin (answerList T).length ≃ Answers T :=
  List.Nodup.getEquivOfForallMemList _ (nodup_answerList T) (mem_answerList T)

/-! ## The question alphabet -/

/-- The question alphabet `𝔽₂^s`, indexed: `𝔽₂` is `ZMod 2`, which is `Fin 2`. -/
def questionEquiv (s : ℕ) : Fin (2 ^ s) ≃ (Fin s → CL.𝔽₂) :=
  (finFunctionFinEquiv (m := 2) (n := s)).symm

/-! ## The agreement of the tabulated value with `val*` -/

open HaltingGameValue (GameData)

/-- **The bridge to game descriptions.** A game description whose question distribution and
decision predicate match those of `𝒱_n` along the two indexings has the same quantum value.
The semidecision procedure of `lem:value-lower-approx` runs on game descriptions, and this is
what carries its verdict back to the verifier. -/
theorem quantumValue_toGame_eq_valStar {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)
    (eX : Fin (g.nX + 1) ≃ V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = V.sampler.dist n (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.game n T).D (eX i) (eX j) (eA k) (eA l)) :
    quantumValue g.game = V.valStar n T :=
  quantumValue_eq_of_equiv (V.game n T) g.game eX eX eA eA hμ hD

/-! ## The shape of the semidecision procedure -/

/-- **The complement of the class `B`**, as the criterion's semidecider has to see it: either
the verifier is not `n`-bounded — witnessed by a single input whose run exceeds the budget, so
a search — or its value at index `n` exceeds `1/2`, which is the `val*` half of
`lem:value-lower-approx` on the tabulation. Neither disjunct decides `n`-boundedness, which is
`Π₁`; the point of the disjunction is that it does not have to. -/
theorem not_inClassB_iff {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) :
    ¬ V.InClassB n T ↔ (¬ V.IsBounded n ∨ 1 / 2 < V.valStar n T) := by
  rw [InClassB, not_and_or, not_le]

/-- A verifier that *is* `n`-bounded lies outside `B` exactly when its value exceeds `1/2`. -/
theorem not_inClassB_iff_of_isBounded {ℓ : ℕ} (V : Verifier ℓ) {n T : ℕ}
    (hb : V.IsBounded n) : ¬ V.InClassB n T ↔ 1 / 2 < V.valStar n T := by
  rw [not_inClassB_iff]
  simp [hb]

end Verifier

end MIPRE
