/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.PolyBounded
import MIPRE.Foundations.Halting.Wrapper

/-!
# From polynomially bounded cost to `λ`-boundedness

`Verifier.IsBounded` (blueprint `def:lambda-bounded`) is the hypothesis every class membership
of the halting reduction carries, and until this file nothing in the repository inhabited it:
every proof of it was conditional on another time bound. This file closes that gap in the
abstract, leaving exactly one thing to supply — that the two programs of the verifier have
polynomially bounded cost (`Prog.HasPolyCost`).

* `Verifier.IsBounded.mono`: `λ`-boundedness is monotone in `λ`. The classes `classA n`,
  `classB n` ask for `IsBounded n` at the level `n` itself, so a verifier bounded at *some* `λ`
  is in them from `λ` on; this is what the thresholds `n₀` of `MIPRE.Halting.Obligations`
  absorb.
* `Decider.timeBoundAt_of_hasPolyCost` and `CL.Sampler.timeBoundAt_of_hasPolyCost`: a cost
  `C n · (|d| + 1) ^ k` with `C` polynomially bounded fits under `n ^ λ · (|d| + 1) ^ λ` for a
  single `λ` and every `n ≥ 2` (`PolyBounded.exists_le_pow`). This is the step that the two
  repairs of `TimeBoundAt` (#57, #61) were about: the bound has to grow with the input, and its
  degree has to be free, or nothing that calls the universal machine can meet it.
* `Verifier.exists_isBounded`: the threshold form, `∃ n₀, ∀ n ≥ n₀, V.IsBounded n`, which is
  what the classes consume.

Nothing here knows about wrappers or descriptions; `Halting/WrapperCost.lean` discharges the
`HasPolyCost` hypotheses for the verifier a string denotes.
-/

namespace MIPRE

open Cost

/-! ## Monotonicity in `λ` -/

namespace Verifier

/-- `λ`-boundedness is monotone in `λ`: every clause of `def:lambda-bounded` weakens as `λ`
grows. Raising `λ` is free, which is what lets a verifier bounded at some fixed `λ` belong to
the classes at every level above it. -/
theorem IsBounded.mono {ℓ : ℕ} {V : Verifier ℓ} {lam lam' : ℕ} (h : V.IsBounded lam)
    (hle : lam ≤ lam') : V.IsBounded lam' := by
  obtain ⟨hmain, hsize⟩ := h
  refine ⟨fun n hn => ?_, hsize.trans hle⟩
  obtain ⟨hdim, hS, hD⟩ := hmain n hn
  have hpow : n ^ lam ≤ n ^ lam' := Nat.pow_le_pow_right (by omega) hle
  exact ⟨hdim.trans hpow, hS.mono hpow hle, hD.mono hpow hle⟩

end Verifier

/-! ## Polynomially bounded cost gives a time bound -/

namespace Cost

/-- A program of polynomially bounded cost meets a single `n ^ λ` time bound at degree `λ`,
for every `n ≥ 2`. The degree and the coefficient are chosen together: `PolyBounded.exists_le_pow`
supplies a `λ` above which the coefficient fits under `n ^ λ`, and the degree of the cost is
absorbed by raising `λ` further. -/
theorem Prog.HasPolyCost.exists_bound {p : Prog} (h : p.HasPolyCost) :
    ∃ lam, ∀ n, 2 ≤ n → ∀ d : Data,
      HaltsWithin p (.cons (encode n) d) (n ^ lam * (d.size + 1) ^ lam) := by
  obtain ⟨C, k, hC, hrun⟩ := h
  obtain ⟨lam₀, hlam₀⟩ := hC.exists_le_pow
  refine ⟨max lam₀ k, fun n hn d => ?_⟩
  obtain ⟨r, t, ht, hrun⟩ := hrun n d
  refine ⟨r, t, ht.trans (Nat.mul_le_mul ?_ ?_), hrun⟩
  · exact (hlam₀ n hn).trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  · exact Nat.pow_le_pow_right (by omega) (le_max_right _ _)

end Cost

/-- The decider form of `Prog.HasPolyCost.exists_bound`. -/
theorem Decider.timeBoundAt_of_hasPolyCost {D : Decider} (h : D.prog.HasPolyCost) :
    ∃ lam, ∀ n, 2 ≤ n → D.TimeBoundAt n (n ^ lam) lam := by
  obtain ⟨lam, hlam⟩ := h.exists_bound
  exact ⟨lam, fun n hn d => hlam n hn d⟩

/-- The sampler form of `Prog.HasPolyCost.exists_bound`. -/
theorem CL.Sampler.timeBoundAt_of_hasPolyCost {ℓ : ℕ} {S : CL.Sampler ℓ}
    (h : S.prog.HasPolyCost) : ∃ lam, ∀ n, 2 ≤ n → S.TimeBoundAt n (n ^ lam) lam := by
  obtain ⟨lam, hlam⟩ := h.exists_bound
  exact ⟨lam, fun n hn d => hlam n hn d⟩

/-! ## The converse: a time bound with a polynomially bounded coefficient -/

/-- A uniform time bound whose coefficient is polynomially bounded *is* polynomially bounded
cost. This is the direction `MIPRE.GapCompression` supplies: its `sampler_time` and
`decider_time` fields bound the running times of the compressed verifier by
`bound.eval (n + λ)` at a fixed degree, and `bound.eval (n + λ)` is polynomially bounded in
`n`. -/
theorem Cost.Prog.hasPolyCost_of_bound {p : Prog} {T : ℕ → ℕ} {k : ℕ} (hT : PolyBounded T)
    (h : ∀ (n : ℕ) (d : Data), HaltsWithin p (.cons (encode n) d) (T n * (d.size + 1) ^ k)) :
    p.HasPolyCost :=
  ⟨T, k, hT, fun n d => h n d⟩

/-- The sampler form. -/
theorem CL.Sampler.hasPolyCost_of_timeBound {ℓ : ℕ} {S : CL.Sampler ℓ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolyBounded T) (h : ∀ n, S.TimeBoundAt n (T n) k) : S.prog.HasPolyCost :=
  Cost.Prog.hasPolyCost_of_bound hT fun n d => h n d

/-- The decider form. -/
theorem Decider.hasPolyCost_of_timeBound {D : Decider} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolyBounded T) (h : ∀ n, D.TimeBoundAt n (T n) k) : D.prog.HasPolyCost :=
  Cost.Prog.hasPolyCost_of_bound hT fun n d => h n d

/-! ## `λ`-boundedness of a verifier -/

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- **A verifier whose programs have polynomially bounded cost and whose sampler has
polynomially bounded dimension is `λ`-bounded**, for some `λ`. The three hypotheses are the
three clauses of `def:lambda-bounded`; the fourth, `|𝒱| ≤ λ`, is free, the size of a verifier
being a constant. -/
theorem exists_isBounded_lam (hdim : PolyBounded V.sampler.dim)
    (hS : V.sampler.prog.HasPolyCost) (hD : V.decider.prog.HasPolyCost) :
    ∃ lam, V.IsBounded lam := by
  obtain ⟨lamS, hlamS⟩ := CL.Sampler.timeBoundAt_of_hasPolyCost hS
  obtain ⟨lamD, hlamD⟩ := Decider.timeBoundAt_of_hasPolyCost hD
  obtain ⟨lamdim, hlamdim⟩ := hdim.exists_le_pow
  refine ⟨max (max lamS lamD) (max lamdim V.size), fun n hn => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hlamdim n hn).trans (Nat.pow_le_pow_right (by omega)
      ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (hlamS n hn).mono
      (Nat.pow_le_pow_right (by omega) ((le_max_left _ _).trans (le_max_left _ _)))
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hlamD n hn).mono
      (Nat.pow_le_pow_right (by omega) ((le_max_right _ _).trans (le_max_left _ _)))
      ((le_max_right _ _).trans (le_max_left _ _))
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- **The threshold form**: such a verifier is `n`-bounded at every level `n` from some `n₀` on.
This is the shape the classes `MIPRE.Halting.classA`, `classB` consume, `IsBounded n` being
asked at the level itself. -/
theorem exists_isBounded (hdim : PolyBounded V.sampler.dim)
    (hS : V.sampler.prog.HasPolyCost) (hD : V.decider.prog.HasPolyCost) :
    ∃ n₀, ∀ n, n₀ ≤ n → V.IsBounded n := by
  obtain ⟨lam, hlam⟩ := V.exists_isBounded_lam hdim hS hD
  exact ⟨lam, fun _ hn => hlam.mono hn⟩

end Verifier

end MIPRE
