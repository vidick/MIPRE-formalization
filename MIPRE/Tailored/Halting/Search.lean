/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Halting.Tabulate
public import MIPRE.Tailored.Halting.Main
public import MIPRE.Foundations.ClassMIPStarComputable

@[expose] public section

/-!
# The search program, and the tailored halting theorem without hypothesis

The search program of the tailored halting verifier (`SearchSpec`,
`Tailored/Halting/Induction.lean`) from the tabulation of a tailored verifier, as
`MIPRE.Halting.exists_semL` gets the existing halting layer's: on a description string `x`, run the semidecider of `1/2 < val*` on the game
description `toGameData (tabT x C)`.

* `quantumValue_tabT`: on the description of a `λ`-bounded tailored verifier `(S^λ, L^λ, P)`,
  that game description has the verifier's value at every level `n ≥ 2`. The tabulation
  presents the doubled game (`presents_tabT`), which has no weight on its loops, so it has the
  doubled game's quantum value (`Presents.quantumValue_eq`), which is the value of the game
  (`TailoredGame.quantumValue_doubled_eq_valStar`); and the conversion to a game description
  keeps the quantum value (`TailoredGameData.quantumValue_toGameData`).
* `exists_searchProg`, `search`, `search_spec`: a program meeting the specification at the
  level `C`, from the lower semicomputability of the quantum value
  (`exists_semidecider_lt_quantumValue`).
* `halting_tailored_search`: `halting_tailored` with that program, so with no hypothesis beyond
  the compression.
-/

namespace MIPRE.Tailored.Halting

open Cost TailoredGameValue

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ) (U : UniversalMachine)
  (UT : ClockedUniversalMachine)

/-- **The tabulated value of a bounded description**: on the description of a `λ`-bounded tailored
verifier `(S^λ, L^λ, P)`, at every level `n ≥ 2`, the game description of its tabulation has the
verifier's value. -/
theorem quantumValue_tabT (lam : ℕ) (P : Decider) (hb : (vof TG lam P).IsBounded lam) {n : ℕ}
    (hn : 2 ≤ n) :
    quantumValue (tabT TG (MIPRE.Halting.descOf lam P.prog) n).toGameData.game =
      (vof TG lam P).valStar n := by
  obtain ⟨e, hP⟩ := presents_tabT TG lam P hb hn
  rw [TailoredGameData.quantumValue_toGameData,
    hP.quantumValue_eq (TailoredGame.doubled_μ_self _),
    TailoredGame.quantumValue_doubled_eq_valStar]
  rfl

/-- **A program meeting the search specification** at the level `C`: the semidecider of
`1/2 < val*` on the tabulation at `C` of the string it is given. -/
theorem exists_searchProg : ∃ S' : Prog, S'.WellScoped 1 ∧ SearchSpec TG S' (C TG) := by
  obtain ⟨S, hS, hSx⟩ := exists_semidecider_lt_quantumValue
    (g := fun x => (tabT TG x (C TG)).toGameData)
    ((TailoredGameData.primrec_toGameData.to_comp.comp
      ((computable_tabT TG).comp (Computable.id.pair (Computable.const (C TG))))).of_eq
      fun _ => rfl) 1 2
  refine ⟨S, hS, fun lam P hb => (hSx _).trans ?_⟩
  rw [quantumValue_tabT TG lam P hb (two_le_C TG)]
  simp only [Nat.cast_one, Nat.cast_ofNat]

/-- **The search program.** -/
noncomputable def search : Prog := (exists_searchProg TG).choose

theorem search_wellScoped : (search TG).WellScoped 1 := (exists_searchProg TG).choose_spec.1

theorem search_spec : SearchSpec TG (search TG) (C TG) := (exists_searchProg TG).choose_spec.2

/-- The threshold of `lem:lambda` for the search program. -/
noncomputable def lamThreshold : ℕ := Lam0 TG U UT (search TG)

/-- The tailored halting verifier with the search program. -/
noncomputable def VT (M : Prog) (lam : ℕ) : TailoredVerifier ℓ := Vhalt TG U UT (search TG) M lam

/-- **The tailored halting theorem at a fixed level, from compression alone**: for every
`λ ≥ Λ₀ + 4|M|`, at the level `C`, `V^{M,λ}` has a perfect ZPC strategy if `M` halts on the empty
input, and value at most `1/2` if it does not. -/
theorem halting_tailored_search (M : Prog) (lam : ℕ)
    (h : lamThreshold TG U UT + 4 * esize M ≤ lam) :
    (Halts M .nil → (VT TG U UT M lam).HasPerfectZPC (C TG)) ∧
    (¬ Halts M .nil → (VT TG U UT M lam).valStar (C TG) ≤ 1 / 2) :=
  halting_tailored TG U UT (search_wellScoped TG) (search_spec TG) M lam h

end MIPRE.Tailored.Halting

end
