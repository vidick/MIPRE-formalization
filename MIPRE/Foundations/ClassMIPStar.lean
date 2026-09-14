/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ValueApprox.RE
import MIPRE.Foundations.Cost.Semidecide

/-!
# The classes `RE` and `MIP*`, and the inclusion `MIP* ⊆ RE`

Blueprint `def:re`, `def:mipstar` and the easy half of `thm:mipstar-eq-re`.

* `IsRE L`: the language `L ⊆ {0,1}*` is recursively enumerable — membership is an `REPred`,
  the domain of a partial computable function; equivalently (`isRE_iff`) the halting set of a
  well-scoped program of the ambient model on encoded strings.
* `MIPStar L`: there is a computable map from strings to game descriptions (`GameData`,
  `def:game-description`) with `val*(G_x) = 1` for `x ∈ L` and `val*(G_x) ≤ 1/2` for `x ∉ L`.
  This is the *computable* version of the class, with games given as explicit descriptions.
  The paper's definition asks for a polynomial-time verifier (a sampler and a decider running
  in time polynomial in `|x|`); the class it defines is contained in this one, since a
  polynomial-time verifier is in particular a computable map to the finite game it describes.
  The computable version is the one the Lean main statement uses
  (`HaltingGameValue.halting_reduces_to_gameValue`), and the inclusion in `RE` proved here for
  the larger class implies it for the smaller.
* `MIPStar.isRE`: `MIP* ⊆ RE`, from `lem:value-lower-approx`
  (`ValueApprox.rePred_lt_quantumValue`) at the threshold `1/2`: under the promise,
  `x ∈ L ↔ val*(G_x) > 1/2`.
* `exists_semidecider_lt_quantumValue`: the `Prog` form — for a computable family of game
  descriptions, a well-scoped program of the ambient model halting exactly on the `x` with
  `p/q < val*(G_x)`; the hypothesis `hS` of `Cost.compressibility_criterion` for `B` the strings
  whose game has value at most `p/q`.
-/

namespace MIPRE

open HaltingGameValue (GameData)
open MIPRE.Cost

/-- **`def:re`.** A language is recursively enumerable if membership is the domain of a partial
computable function (Mathlib's `REPred`). -/
def IsRE (L : Set BitStr) : Prop := REPred (· ∈ L)

/-- **`def:mipstar`**, computable version. A language `L` is in `MIP*` if there is a computable
map from strings to game descriptions such that the game of `x` has quantum value `1` when
`x ∈ L` and at most `1/2` when `x ∉ L`. -/
def MIPStar (L : Set BitStr) : Prop :=
  ∃ g : BitStr → GameData, Computable g ∧
    ∀ x, (x ∈ L → quantumValue (g x).game = 1) ∧ (x ∉ L → quantumValue (g x).game ≤ 1 / 2)

/-- Precomposition of an r.e. predicate with a computable function. -/
theorem REPred.comp' {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop} (hp : REPred p)
    {g : α → β} (hg : Computable g) : REPred fun a => p (g a) :=
  Partrec.comp hp hg

/-- `lem:value-lower-approx` along a computable family of game descriptions: the `x` with
`p / q < val*(G_{g x})` form an r.e. set. -/
theorem rePred_lt_quantumValue_comp {α : Type*} [Primcodable α] {g : α → GameData}
    (hg : Computable g) (p q : ℕ) :
    REPred fun x => (p : ℝ) / q < quantumValue (g x).game :=
  REPred.comp' ValueApprox.rePred_lt_quantumValue (hg.pair (Computable.const (p, q)))

/-- **`MIP* ⊆ RE`** (the easy half of `thm:mipstar-eq-re`): enumerate strategies of the game of
`x` and accept upon finding one of value greater than `1/2`. -/
theorem MIPStar.isRE {L : Set BitStr} (h : MIPStar L) : IsRE L := by
  obtain ⟨g, hg, hgap⟩ := h
  refine (rePred_lt_quantumValue_comp hg 1 2).of_eq fun x => ?_
  simp only [Nat.cast_one, Nat.cast_ofNat]
  constructor
  · intro hlt
    by_contra hx
    exact absurd ((hgap x).2 hx) (not_le.2 hlt)
  · intro hx
    rw [(hgap x).1 hx]
    norm_num

/-- Recursive enumerability in the ambient model: a language is r.e. iff it is the halting set
of a well-scoped program on encoded strings. -/
theorem isRE_iff (L : Set BitStr) :
    IsRE L ↔ ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∈ L :=
  ⟨fun h => Cost.exists_semidecider h, fun ⟨S, _, hS⟩ => (Cost.rePred_halts S).of_eq hS⟩

/-- A language in `MIP*` is the halting set of a program of the ambient model. -/
theorem MIPStar.exists_semidecider {L : Set BitStr} (h : MIPStar L) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∈ L :=
  Cost.exists_semidecider h.isRE

/-- **The semidecider of the compressibility criterion.** For a computable family of game
descriptions and a threshold `p / q`, a well-scoped program halting on `encode x` exactly when
`p / q < val*(G_{g x})`: the hypothesis `hS` of `Cost.compressibility_criterion`, with `B` the
strings whose game has value at most `p / q`. -/
theorem exists_semidecider_lt_quantumValue {g : BitStr → GameData} (hg : Computable g)
    (p q : ℕ) :
    ∃ S : Prog, S.WellScoped 1 ∧
      ∀ x : BitStr, Halts S (encode x) ↔ (p : ℝ) / q < quantumValue (g x).game :=
  Cost.exists_semidecider (rePred_lt_quantumValue_comp hg p q)

end MIPRE
