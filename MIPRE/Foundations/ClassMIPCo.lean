/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ClassMIPStar
public import MIPRE.Foundations.Tsirelson.UpperRE

@[expose] public section

/-!
# The classes `coRE` and `MIP^co`, and the inclusion `MIP^co ⊆ coRE`

Blueprint `def:core`, `def:mipco` and `lem:mipco-sub-core` (`planning/mipco-track.md`).

* `IsCoRE L`: the complement of `L` is recursively enumerable.
* `MIPCo L`: there is a computable map from strings to game descriptions with
  `ω_co(G_x) = 1` for `x ∈ L` and `ω_co(G_x) ≤ 1/2` for `x ∉ L`, in the bipartite
  commuting-operator value `MIPRE.commutingOperatorValue`. As `MIPRE.MIPStar`, this is the
  *computable* version of the class; the paper's polynomial-time class is contained in it.
* `MIPCo.isCoRE`: `MIP^co ⊆ coRE`, from the upper semidecider for the commuting-operator
  value (`MIPRE.commutingUpperRE`, blueprint `lem:valco-upper-re`) at the threshold `1`: under
  the promise, `x ∉ L ↔ ω_co(G_x) < 1`. This is the role Lin's proof gives to the NPA
  hierarchy (`Lin25`, `lem:MIPcoincoRE`), and it holds with no hypothesis.
* `HaltingReductionCommuting`: the halting reduction to the commuting-operator value as a
  proposition — `ω_co ≤ 1/2` on halting machines and `ω_co = 1` on the others — which
  `Halting/ReductionCo.lean` proves from the commuting-operator soundness of compression and
  `Halting/CorollariesCo.lean` turns into `coRE ⊆ MIP^co`.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData HaltsOnEmptyInput)
open Nat.Partrec (Code)

/-- **`def:core`.** A language is co-recursively enumerable if its complement is. -/
def IsCoRE (L : Set BitStr) : Prop := IsRE Lᶜ

theorem isCoRE_iff (L : Set BitStr) : IsCoRE L ↔ REPred (· ∉ L) := Iff.rfl

/-- **`def:mipco`**, computable version. A language `L` is in `MIP^co` if there is a computable
map from strings to game descriptions such that the game of `x` has commuting-operator value
`1` when `x ∈ L` and at most `1/2` when `x ∉ L`. -/
def MIPCo (L : Set BitStr) : Prop :=
  ∃ g : BitStr → GameData, Computable g ∧
    ∀ x, (x ∈ L → commutingOperatorValue (g x).game = 1) ∧
      (x ∉ L → commutingOperatorValue (g x).game ≤ 1 / 2)

/-- The halting reduction to the commuting-operator value, as a proposition: a computable map
from codes to game descriptions whose commuting-operator value is at most `1/2` on codes that
halt on the empty input and `1` on the others. `MIPRE.Halting.halting_reduction_commuting_of`
proves it from the commuting-operator soundness of compression. -/
def HaltingReductionCommuting : Prop :=
  ∃ g : Code → GameData, Computable g ∧
    ∀ pc : Code,
      (HaltsOnEmptyInput pc → commutingOperatorValue (g pc).game ≤ 1 / 2) ∧
      (¬ HaltsOnEmptyInput pc → commutingOperatorValue (g pc).game = 1)

/-- **`MIP^co ⊆ coRE`** (blueprint `lem:mipco-sub-core`): the complement of a language in
`MIP^co` is the preimage, under its computable map, of the set of descriptions with
`ω_co < 1`, which the upper semidecider enumerates. -/
theorem MIPCo.isCoRE {L : Set BitStr} (h : MIPCo L) : IsCoRE L := by
  obtain ⟨g, hg, hgap⟩ := h
  have hP : REPred fun x : BitStr =>
      commutingOperatorValue (g x).game < ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) :=
    Partrec.comp commutingUpperRE (hg.pair (Computable.const ((1, 1) : ℕ × ℕ)))
  refine hP.of_eq fun x => ?_
  simp only [Nat.cast_one, div_one]
  show _ ↔ x ∉ L
  constructor
  · intro hlt hx
    rw [(hgap x).1 hx] at hlt
    exact lt_irrefl _ hlt
  · intro hx
    have := (hgap x).2 hx
    linarith

/-- The complement of a language in `MIP^co` is the halting set of a program of the ambient
model. -/
theorem MIPCo.exists_cosemidecider {L : Set BitStr} (h : MIPCo L) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ x ∉ L :=
  Cost.exists_semidecider h.isCoRE

end MIPRE

end
