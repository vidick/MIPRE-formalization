/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.ClassesCo
public import MIPRE.Foundations.Halting.Strings

@[expose] public section

/-!
# The classes of the co reduction, on strings

The three classes the nested compressibility criterion is instantiated with for the `coRE`
direction of `MIP^co = coRE` (`planning/mipco-track.md`, §3), on the strings-as-verifiers
reading `Vof` of `Halting/Instantiation.lean`:

* `classBCo n`: the strings whose verifier is in `Verifier.InClassBCo` at level `n`, with the
  same answer bound `ansBound` as `classA` and `classB`. The class the compressor has to
  preserve by commuting-operator soundness, and the class of the halting machines.
* `classA n`, unchanged: the class the compressor preserves by the tensor completeness of the
  main theorem, and the smaller of the two nested classes.
* `classOne n`: the strings whose *tabulated* game at level `n` does not have `ω_co < 1`. The
  larger nested class; its complement is what the upper semidecider recognizes
  (`Halting/ReductionCo.lean`), and it contains `classA n` (`classA_subset_classOne`) because
  a perfect PCC strategy gives `val* = 1 ≤ ω_co`. It is read on the tabulation directly so that
  the non-halting conclusion of the criterion needs no boundedness.

`tab_valCo` is obligation O2 in the commuting-operator value — the tabulated game has
`ω_co(𝒱_n)` at every `n`-bounded string — and `yNo_memCo` is the rejecting half of O1: the
string `yNo` of `Halting/Strings.lean` lies in `classBCo` at every level from some `n₀` on.
-/

namespace MIPRE.Halting

open Cost
open HaltingGameValue (GameData)

variable (G : GapCompression) (U : UniversalMachine)

/-- **The class `B^co` at level `n`**: the strings whose verifier is `n`-bounded, rejects long
answers, and has commuting-operator value at most `1/2` at the answer bound `ansBound`. -/
def classBCo (n : ℕ) : Set BitStr := {x | (Vof G U x).InClassBCo n (ansBound G x n)}

theorem mem_classBCo_iff {n : ℕ} {x : BitStr} :
    x ∈ classBCo G U n ↔ (Vof G U x).InClassBCo n (ansBound G x n) := Iff.rfl

theorem classBCo_subset_classB (n : ℕ) : classBCo G U n ⊆ classB G U n :=
  fun _ h => Verifier.InClassBCo.inClassB _ h

/-- **The class of commuting-operator value `1` at level `n`**, read on the tabulation: the
strings whose tabulated game at level `n` does not have `ω_co < 1`. -/
def classOne (n : ℕ) : Set BitStr := {x | ¬ commutingOperatorValue (tab G U x n).game < 1}

theorem mem_classOne_iff {n : ℕ} {x : BitStr} :
    x ∈ classOne G U n ↔ ¬ commutingOperatorValue (tab G U x n).game < 1 := Iff.rfl

/-- In `classOne` the tabulated game has commuting-operator value exactly `1`. -/
theorem commutingOperatorValue_tab_eq_one_of_mem_classOne {n : ℕ} {x : BitStr}
    (h : x ∈ classOne G U n) : commutingOperatorValue (tab G U x n).game = 1 :=
  le_antisymm (commutingOperatorValue_le_one _) (not_lt.1 h)

/-- **O2, in the commuting-operator value**: the tabulated game has `ω_co(𝒱_n)` at every
`n`-bounded string, from the doubled match `tab_match`. -/
theorem tab_valCo (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    commutingOperatorValue (tab G U x n).game = (Vof G U x).valCo n (ansBound G x n) := by
  obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U x n hb
  exact Verifier.commutingOperatorValue_toGame_eq_valCo_doubled _ _ _ _ eX eA hμ hD

/-- **The perfect-PCC class lies in the class of commuting-operator value `1`**: a perfect PCC
strategy gives `val* = 1`, and `val* ≤ ω_co`. This is the nesting `B₀ ⊆ B₁` of the
criterion. -/
theorem classA_subset_classOne (n : ℕ) : classA G U n ⊆ classOne G U n := by
  intro x hx
  rw [mem_classOne_iff, not_lt]
  have h1 : quantumValue (tab G U x n).game = 1 := by
    rw [tab_value G U x n hx.1]
    exact (Vof G U x).valStar_eq_one_of_hasPerfectPCC hx.2.2
  rw [← h1]
  exact quantumValue_le_commutingOperatorValue _

/-- **O1 for the co reduction, the rejecting side.** `yNo` lies in the class `B^co` at every
level from some `n₀` on: its verifier accepts nothing, so `ω_co = 0`. -/
theorem yNo_memCo : ∃ n₀, ∀ n, n₀ ≤ n → yNo ∈ classBCo G U n := by
  obtain ⟨n₀, hn₀⟩ := Verifier.ofSamplerDecider_isBounded U (G.sampler 0) decNo
    (sampler_hasPolyCost G 0) (sampler_polyBounded_dim G 0) decNo_hasPolyCost
  refine ⟨n₀, fun n hn => ?_⟩
  show (Vof G U yNo).InClassBCo n (ansBound G yNo n)
  rw [Vof_yNo]
  refine Verifier.inClassBCo_of_rejects_all _ (hn₀ n hn) fun x y a b hacc => ?_
  rw [Verifier.ofSamplerDecider_accepts] at hacc
  obtain ⟨-, -, t, ht⟩ := hacc
  exact decNo_not_runs_true _ _ ht

end MIPRE.Halting

end
