/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ValueApprox.RE
import MIPRE.Foundations.Cost.Semidecide
import MIPRE.Foundations.ValueModel

/-!
# The classes `RE`, `coRE` and `MIPClass ω`, and the inclusions `MIP* ⊆ RE`, `MIP^co ⊆ coRE`

Blueprint `def:re`, `def:core`, `def:mipstar-computable`, `def:mipco`, and the easy halves of
`thm:mipstar-eq-re` and `thm:mipco-eq-core`, written once in a value model `ω` (`ValueModel`):

* `IsRE L`: the language `L ⊆ {0,1}*` is recursively enumerable — membership is an `REPred`,
  the domain of a partial computable function; equivalently (`isRE_iff`) the halting set of a
  well-scoped program of the ambient model on encoded strings. `IsCoRE L`: its complement is.
* `MIPClass ω L`: there is a computable map from strings to game descriptions (`GameData`,
  `def:game-description`) with value `1` in the model for `x ∈ L` and at most `1/2` for `x ∉ L`.
  `MIPStar` is `MIPClass ValueModel.tensor` and `MIPCo` is `MIPClass ValueModel.commuting`.
  These are the *computable* versions of the classes, with games given as explicit
  descriptions. The paper's definition asks for a polynomial-time verifier (a sampler and a
  decider running in time polynomial in `|x|`); the class it defines is contained in this one,
  since a polynomial-time verifier is in particular a computable map to the finite game it
  describes (`MIPStarPoly.toMIPStar`). The computable version is the one the Lean main
  statement uses (`HaltingGameValue.halting_reduces_to_gameValue`), and the inclusion in `RE`
  proved here for the larger class implies it for the smaller.
* `MIPClass.isRE`: `MIPClass ω ⊆ RE` when the value is r.e. from below (`ValueModel.LowerRE`),
  at the threshold `1/2`: under the promise, `x ∈ L ↔ val(G_x) > 1/2`. At `tensor`
  (`ValueModel.tensor_lowerRE`, from `lem:value-lower-approx`) this is `MIP* ⊆ RE`.
* `MIPClass.isCoRE`: `MIPClass ω ⊆ coRE` when the value is r.e. from above
  (`ValueModel.UpperRE`), at the threshold `1`: under the promise, `x ∉ L ↔ val(G_x) < 1`. At
  `commuting` (`ValueModel.commuting_upperRE`, `Tsirelson/UpperRE.lean`) this is
  `MIP^co ⊆ coRE`, the role Lin's proof gives to the NPA hierarchy (`Lin25`).
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

/-- **`def:core`.** A language is co-recursively enumerable if its complement is. -/
def IsCoRE (L : Set BitStr) : Prop := IsRE Lᶜ

theorem isCoRE_iff (L : Set BitStr) : IsCoRE L ↔ REPred (· ∉ L) := Iff.rfl

/-- **The class of a value model**, computable version (`def:mipstar-computable` at
`ValueModel.tensor`, `def:mipco` at `ValueModel.commuting`). A language `L` is in `MIPClass ω`
if there is a computable map from strings to game descriptions such that the game of `x` has
value `1` in the model when `x ∈ L` and at most `1/2` when `x ∉ L`. -/
def MIPClass (ω : ValueModel) (L : Set BitStr) : Prop :=
  ∃ g : BitStr → GameData, Computable g ∧
    ∀ x, (x ∈ L → ω.val (g x).game = 1) ∧ (x ∉ L → ω.val (g x).game ≤ 1 / 2)

/-- **`def:mipstar`**, computable version: `MIPClass` at the tensor-product value. -/
abbrev MIPStar : Set BitStr → Prop := MIPClass .tensor

/-- **`def:mipco`**, computable version: `MIPClass` at the commuting-operator value. -/
abbrev MIPCo : Set BitStr → Prop := MIPClass .commuting

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

/-- **The tensor-product value is r.e. from below** (blueprint `lem:value-lower-approx`). -/
theorem ValueModel.tensor_lowerRE : ValueModel.tensor.LowerRE :=
  ValueApprox.rePred_lt_quantumValue

/-- A lower semidecider for the value along a computable family of game descriptions: the `x`
with `p / q < val(G_{g x})` form an r.e. set. -/
theorem ValueModel.LowerRE.comp {ω : ValueModel} (hlow : ω.LowerRE) {α : Type*} [Primcodable α]
    {g : α → GameData} (hg : Computable g) (p q : ℕ) :
    REPred fun x => (p : ℝ) / q < ω.val (g x).game :=
  REPred.comp' hlow (hg.pair (Computable.const (p, q)))

/-- An upper semidecider for the value along a computable family of game descriptions: the `x`
with `val(G_{g x}) < p / q` form an r.e. set. -/
theorem ValueModel.UpperRE.comp {ω : ValueModel} (hup : ω.UpperRE) {α : Type*} [Primcodable α]
    {g : α → GameData} (hg : Computable g) (p q : ℕ) :
    REPred fun x => ω.val (g x).game < (p : ℝ) / q :=
  REPred.comp' hup (hg.pair (Computable.const (p, q)))

/-- **`MIPClass ω ⊆ RE`** when the value is r.e. from below (the easy half of
`thm:mipstar-eq-re`): enumerate the witnesses of `val(G_x) > 1/2`. -/
theorem MIPClass.isRE {ω : ValueModel} (hlow : ω.LowerRE) {L : Set BitStr} (h : MIPClass ω L) :
    IsRE L := by
  obtain ⟨g, hg, hgap⟩ := h
  refine (hlow.comp hg 1 2).of_eq fun x => ?_
  simp only [Nat.cast_one, Nat.cast_ofNat]
  constructor
  · intro hlt
    by_contra hx
    exact absurd ((hgap x).2 hx) (not_le.2 hlt)
  · intro hx
    rw [(hgap x).1 hx]
    norm_num

/-- **`MIPClass ω ⊆ coRE`** when the value is r.e. from above (the easy half of
`thm:mipco-eq-core`): the complement of `L` is the preimage of the r.e. set of descriptions with
`val < 1` under the computable map. -/
theorem MIPClass.isCoRE {ω : ValueModel} (hup : ω.UpperRE) {L : Set BitStr}
    (h : MIPClass ω L) : IsCoRE L := by
  obtain ⟨g, hg, hgap⟩ := h
  refine (hup.comp hg 1 1).of_eq fun x => ?_
  simp only [Nat.cast_one, div_one]
  show _ ↔ x ∉ L
  constructor
  · intro hlt hx
    rw [(hgap x).1 hx] at hlt
    exact lt_irrefl _ hlt
  · intro hx
    have := (hgap x).2 hx
    linarith

/-- **`MIP* ⊆ RE`** (the easy half of `thm:mipstar-eq-re`): enumerate strategies of the game of
`x` and accept upon finding one of value greater than `1/2`. -/
theorem MIPStar.isRE {L : Set BitStr} (h : MIPStar L) : IsRE L :=
  MIPClass.isRE ValueModel.tensor_lowerRE h

/-- Recursive enumerability in the ambient model: a language is r.e. iff it is the halting set
of a well-scoped program on encoded strings. -/
theorem isRE_iff (L : Set BitStr) :
    IsRE L ↔ ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∈ L :=
  ⟨fun h => Cost.exists_semidecider h, fun ⟨S, _, hS⟩ => (Cost.rePred_halts S).of_eq hS⟩

/-- A language in `MIPClass ω`, for a value r.e. from below, is the halting set of a program of
the ambient model. -/
theorem MIPClass.exists_semidecider {ω : ValueModel} (hlow : ω.LowerRE) {L : Set BitStr}
    (h : MIPClass ω L) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∈ L :=
  Cost.exists_semidecider (h.isRE hlow)

/-- The complement of a language in `MIPClass ω`, for a value r.e. from above, is the halting
set of a program of the ambient model. -/
theorem MIPClass.exists_cosemidecider {ω : ValueModel} (hup : ω.UpperRE) {L : Set BitStr}
    (h : MIPClass ω L) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∉ L :=
  Cost.exists_semidecider (h.isCoRE hup)

/-- A language in `MIP*` is the halting set of a program of the ambient model. -/
theorem MIPStar.exists_semidecider {L : Set BitStr} (h : MIPStar L) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∈ L :=
  MIPClass.exists_semidecider ValueModel.tensor_lowerRE h

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
