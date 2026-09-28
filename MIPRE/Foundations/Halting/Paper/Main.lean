/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Paper.Induction
import MIPRE.Foundations.Halting.Paper.Cost

/-!
# The halting verifier along the paper's route: `thm:halting` at a fixed level

Blueprint `thm:halting` in the paper's form (`recursive.tex`), for the polynomial-time halting
reduction of `planning/polytime-halting.md`: for every machine `M` and every `λ ≥ Λ₀ + 4|M|`,
the verifier `𝒱^halt M λ` of `Paper/Decider.lean`, at the **fixed** level `C = max C₀ 2`, has
a value-`1` PCC strategy if `M` halts on the empty input and value at most `1/2` otherwise —
with the answer alphabet cut at the compressor's bound `poly(C, λ)`, a polynomial in `λ`.

This is the criterion route's `thm:halting` (`Halting/Reduction.lean`, `Criterion.lean`) with the
level fixed and the parameter explicit, which is what makes the reduction polynomial-time: the
game is `𝒱^halt M λ` at index `C`, its sampler is the compressed sampler at `λ = Λ₀ + 4|M|`
(polynomial-time in `|M|` through `samplerProg`), and its decider runs within the polynomial
bound of `Paper/Cost.lean`. The class verifier of the paper's `MIP*` (PR 3 of the plan) is this
game read off a uniform program.

The search program `S'` of the decider's second branch is `semL`, the semidecider of
"`val*` at level `C` of the verifier this string describes exceeds `1/2`" (`exists_semL`),
fixed once and for all; `Λ₀` is the threshold `Lam0` of `lem:lambda` (`Paper/Cost.lean`).
-/

namespace MIPRE.Halting

open Cost Cost.Prog

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-- **The search program**: the semidecider of `1/2 < val*` at level `C` of the described
verifier, from `exists_semL`. -/
noncomputable def semL : Prog := (exists_semL G U (C G)).choose

theorem semL_wellScoped : (semL G U).WellScoped 1 := (exists_semL G U (C G)).choose_spec.1

theorem semL_spec (x : BitStr) :
    Halts (semL G U) (encode x) ↔ (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game :=
  (exists_semL G U (C G)).choose_spec.2 x

/-- The verifier `𝒱^halt M λ` with the search program `semL`. -/
noncomputable def Vpaper (M : Prog) (lam : ℕ) : Verifier 7 := Vhalt G U UT (semL G U) M lam

/-- The threshold of `lem:lambda` for the search program `semL`. -/
noncomputable def lamThreshold : ℕ := Lam0 G U UT (semL G U)

/-- `𝒱^halt M λ` is `λ`-bounded for `λ ≥ Λ₀ + 4|M|`. -/
theorem Vpaper_isBounded (M : Prog) (lam : ℕ) (h : lamThreshold G U UT + 4 * esize M ≤ lam) :
    (Vpaper G U UT M lam).IsBounded lam :=
  (Lam0_spec G U UT (semL G U) M lam h).1

/-- **`thm:halting`, the paper's form**: for `λ ≥ Λ₀ + 4|M|`, at the fixed level `C`, the game
of `𝒱^halt M λ` with answers of length at most `poly(C, λ)` has a value-`1` PCC strategy if `M`
halts on the empty input, and value at most `1/2` if it does not. -/
theorem halting_paper (M : Prog) (lam : ℕ) (h : lamThreshold G U UT + 4 * esize M ≤ lam) :
    (Halts M .nil →
      (Vpaper G U UT M lam).HasPerfectPCC (C G) (G.bound.eval (C G + lam))) ∧
    (¬ Halts M .nil →
      (Vpaper G U UT M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2) := by
  obtain ⟨hb, hpoly⟩ := Lam0_spec G U UT (semL G U) M lam h
  exact ⟨fun hM => hasPerfectPCC_of_halts G U UT (semL_wellScoped G U) (semL_spec G U) M lam
      hb hpoly hM,
    fun hM => valStar_le_of_not_halts G U UT (semL_wellScoped G U) (semL_spec G U) M lam
      hb hpoly hM⟩

/-- The values of the game, in the form of the criterion route's `thm:halting`: value `1` if
`M` halts, at most `1/2` if not. -/
theorem halting_paper_valStar (M : Prog) (lam : ℕ)
    (h : lamThreshold G U UT + 4 * esize M ≤ lam) :
    (Halts M .nil → (Vpaper G U UT M lam).valStar (C G) (G.bound.eval (C G + lam)) = 1) ∧
    (¬ Halts M .nil →
      (Vpaper G U UT M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2) := by
  obtain ⟨h1, h2⟩ := halting_paper G U UT M lam h
  exact ⟨fun hM => Verifier.valStar_eq_one_of_hasPerfectPCC _ (h1 hM), h2⟩

end MIPRE.Halting
