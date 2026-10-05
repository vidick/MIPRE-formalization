/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Halting.Cost
public import MIPRE.Tailored.ZPC

@[expose] public section

/-!
# The tailored halting verifier: the halting theorem at a fixed level

Paper II, II:2021–2066: the proof of the main theorem from compression, in the form the
halting reduction consumes, along the route of `MIPRE/Foundations/Halting/Paper/Main.lean`. For
a tailored gap compression `TG`, a search program `S'` meeting its specification, every machine
`M` and every `λ ≥ Λ₀ + 4|M|`, the tailored verifier `V^{M,λ}` at the **fixed** level
`C = max C₀ 2` has a perfect ZPC strategy (on the doubled game) if `M` halts on the empty input,
and value at most `1/2` if it does not.

The level is fixed and the parameter explicit, which is what makes a reduction out of it
polynomial-time: the game is `V^{M,λ}` at the index `C`, its sampler and answer-length
calculator are the compressed ones at `λ = Λ₀ + 4|M|`, and its processor runs within the bound
of `Tailored/Halting/Cost.lean`.

The search program is a hypothesis (`SearchSpec`), where the existing halting layer has one at
hand (`MIPRE.Halting.semL`, from its tabulation): a program meeting it comes from tabulating a
tailored verifier at a fixed level, the next part of the plan.
-/

namespace MIPRE.Tailored.Halting

open Cost Cost.Prog

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ) (U : UniversalMachine)
  (UT : ClockedUniversalMachine)

/-- **The tailored halting theorem at a fixed level**: for a search program meeting its
specification and every `λ ≥ Λ₀ + 4|M|`, at the level `C`, `V^{M,λ}` has a perfect ZPC strategy
if `M` halts on the empty input, and value at most `1/2` if it does not. -/
theorem halting_tailored {S' : Prog} (hS' : S'.WellScoped 1) (hsem : SearchSpec TG S' (C TG))
    (M : Prog) (lam : ℕ) (h : Lam0 TG U UT S' + 4 * esize M ≤ lam) :
    (Halts M .nil → (Vhalt TG U UT S' M lam).HasPerfectZPC (C TG)) ∧
    (¬ Halts M .nil → (Vhalt TG U UT S' M lam).valStar (C TG) ≤ 1 / 2) := by
  have hb := Lam0_spec TG U UT S' M lam h
  exact ⟨hasPerfectZPC_of_halts TG U UT hb hS' hsem,
    valStar_le_of_not_halts TG U UT hb hS' hsem⟩

/-- The values, in the form of the halting reduction: value `1` if `M` halts, at most `1/2` if
not. -/
theorem halting_tailored_valStar {S' : Prog} (hS' : S'.WellScoped 1)
    (hsem : SearchSpec TG S' (C TG)) (M : Prog) (lam : ℕ)
    (h : Lam0 TG U UT S' + 4 * esize M ≤ lam) :
    (Halts M .nil → (Vhalt TG U UT S' M lam).valStar (C TG) = 1) ∧
    (¬ Halts M .nil → (Vhalt TG U UT S' M lam).valStar (C TG) ≤ 1 / 2) := by
  obtain ⟨h1, h2⟩ := halting_tailored TG U UT hS' hsem M lam h
  refine ⟨fun hM => ?_, h2⟩
  have hZ := h1 hM
  unfold TailoredVerifier.HasPerfectZPC at hZ
  unfold TailoredVerifier.valStar
  exact TailoredGame.HasPerfectZPC.valStar_eq_one hZ

end MIPRE.Tailored.Halting

end
