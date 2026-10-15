/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/VerifierValue.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression

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
  `syncValue_le_quantumValue` on the doubled game and `quantumValue_doubledGame`.

`Verifier.HasPerfectPCC` is a PCC strategy of value `1` on the *doubled* game
(`Verifier.doubledGame`, `Foundations/GapCompression.lean`), so none of the lemmas here asks
the decider to be synchronous at `n`.
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

theorem game_D (n T : ℕ) (x y : V.Questions n) (a b : Answers T) :
    ((V.game n T).D x y a b = true) ↔
      V.decider.Accepts n (CL.toBits x) (CL.toBits y) a.1 b.1 := by
  classical
  exact decide_eq_true_iff

/-! ## Same sampler, comparable deciders -/

/-! ## Answer padding -/

/-- **The decider rejects every answer longer than `T` at index `n`.** The property a compressed
decider has beyond its time bound (`GapCompression.output_rejects_long`), and the third clause
of membership in the classes of the halting reduction (`Verifier.InClassA`, `InClassB`): it is
what lets the answer bound a class is read with be raised without moving the value
(`valStar_eq_of_rejects`), which the soundness direction of the compressor's obligation needs.
The paper's `V^halt` has it by construction, Step 6 of its decider `F` being an explicit length
check; the classes here range over arbitrary strings and have to ask for it. -/
def RejectsLong (n T : ℕ) : Prop :=
  ∀ x y a b, T < a.length ∨ T < b.length → ¬ V.decider.Accepts n x y a b

/-- When the decider rejects every answer longer than `T` at index `n`, enlarging the
answer-length bound does not change `val*`. -/
theorem valStar_eq_of_rejects {n T T' : ℕ} (hT : T ≤ T') (hrej : V.RejectsLong n T) :
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
  obtain ⟨S, hpcc, hval⟩ := h
  refine ⟨S.extend (V.doubledGame n T') (Answers.castLE hT),
    S.isPCC_extend hpcc _ _ (fun _ _ => rfl), ?_⟩
  rw [S.value_extend (V.doubledGame n T') (Answers.castLE hT) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl), hval]

/-! ## Perfect PCC strategies and the quantum value -/

end Verifier

end MIPRE
