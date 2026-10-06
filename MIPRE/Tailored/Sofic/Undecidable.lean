/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.AssocPrimrec
public import MIPRE.Foundations.Halting.Corollaries

@[expose] public section

/-!
# The sofic value is not approximable, from a halting reduction to tailored games

The argument of Corollary I:2144 without the measure side. Suppose a computable `f` approximates
the sofic value of every test to within `1/(k+1)`, and let `g` be a computable reduction from the
halting problem to tailored games (`TailoredGameValue.TailoredHaltingReduction`). Main
Theorem II separates the associated tests of the two kinds of games:

* a halting machine gives a game with a perfect ZPC strategy, whose test has sofic value `1`;
* a non-halting machine gives a game of value at most `1/2`, whose test has sofic value at most
  `1 − 1/(2K)`, with `K = K(Λ)` a computable function of the answer length.

Approximating to within `1/(4K + 1)` tells the two apart, which decides the halting problem.
`not_sofValueApproximable_of` takes the two clauses of Main Theorem II as hypotheses, in the form
`MainTheoremII K`.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue HaltingGameValue

/-- **The two clauses of Main Theorem II** (Theorem I:2126) in the form the corollary uses, for a
gap function `K` of the answer length: perfect ZPC games have tests of sofic value `1`, and games
of synchronous value at most `1/2` have tests of sofic value at most `1 − 1/(2K(Λ))`. -/
structure MainTheoremII (K : ℕ → ℕ) : Prop where
  one_le : ∀ Λ, 1 ≤ K Λ
  complete : ∀ g : TailoredGameData, g.HasPerfectZPC → (assocTest g).valSof = 1
  sound : ∀ g : TailoredGameData, gameValue g.toGame ≤ 1 / 2 →
    (assocTest g).valSof ≤ 1 - 1 / (2 * (K g.ansLen : ℝ))

/-- The decision: approximating at `k = 4K` lands at or above `k/(k+1)` exactly for the tests of
sofic value `1`. -/
theorem le_iff_of_gap {v : ℝ} {K F : ℕ} (hK : 1 ≤ K) (happ : |v - F / ((4 * K : ℕ) + 1 : ℝ)| ≤
    1 / ((4 * K : ℕ) + 1 : ℝ)) :
    (v = 1 → 4 * K ≤ F) ∧ (v ≤ 1 - 1 / (2 * (K : ℝ)) → F < 4 * K) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set k : ℝ := ((4 * K : ℕ) : ℝ) with hk
  have hk4 : k = 4 * (K : ℝ) := by rw [hk]; push_cast; ring
  have hkpos : 0 < k + 1 := by rw [hk4]; linarith
  rw [abs_le] at happ
  obtain ⟨h1, h2⟩ := happ
  constructor
  · intro hv
    subst hv
    have : (k : ℝ) ≤ F := by
      have h3 : 1 - 1 / (k + 1) ≤ F / (k + 1) := by linarith
      rw [show 1 - 1 / (k + 1) = k / (k + 1) by field_simp; ring] at h3
      exact (div_le_div_iff_of_pos_right hkpos).1 h3
    rw [hk] at this
    exact_mod_cast this
  · intro hv
    have h3 : (F : ℝ) / (k + 1) ≤ 1 - 1 / (2 * K) + 1 / (k + 1) := by linarith
    have h4 : 1 - 1 / (2 * (K : ℝ)) + 1 / (k + 1) < k / (k + 1) := by
      have e : k / (k + 1) = 1 - 1 / (k + 1) := by field_simp; ring
      have e2 : 2 / (k + 1) = 1 / (k + 1) + 1 / (k + 1) := by ring
      have h5 : 2 / (k + 1) < 1 / (2 * (K : ℝ)) := by
        rw [div_lt_div_iff₀ hkpos (by positivity), hk4]
        nlinarith
      rw [e]
      linarith
    have : (F : ℝ) < k := (div_lt_div_iff_of_pos_right hkpos).1 (h3.trans_lt h4)
    rw [hk] at this
    exact_mod_cast this

/-- **The sofic value is not approximable** (the measure-free part of Corollary I:2144): from a
halting reduction to tailored games and Main Theorem II with a primitive recursive gap function,
no computable function approximates the sofic value of every subgroup test. -/
theorem not_sofValueApproximable_of {K : ℕ → ℕ} (hK : Primrec K) (hMT : MainTheoremII K)
    (hred : TailoredHaltingReduction) : ¬ SofValueApproximable := by
  rintro ⟨f, hf, happ⟩
  obtain ⟨g, hg, hgap⟩ := hred
  have hT : Computable fun c => assocTest (g c) := primrec_assocTest.to_comp.comp hg
  have hk : Computable fun c => 4 * K (g c).ansLen :=
    (Primrec.nat_mul.comp (Primrec.const 4) (hK.comp primrec_ansLen)).to_comp.comp hg
  have hF : Computable fun c => f (assocTest (g c)) (4 * K (g c).ansLen) := hf.comp hT hk
  have hdec : Computable fun c =>
      decide (4 * K (g c).ansLen ≤ f (assocTest (g c)) (4 * K (g c).ansLen)) :=
    (Primrec.nat_le.decide.to_comp).comp hk hF
  refine MIPRE.halting_undecidable (ComputablePred.computable_iff.2 ⟨_, hdec, ?_⟩)
  funext c
  apply propext
  have hgap' := le_iff_of_gap (hMT.one_le (g c).ansLen)
    (happ (assocTest (g c)) (4 * K (g c).ansLen))
  constructor
  · intro hc
    exact decide_eq_true (hgap'.1 (hMT.complete _ ((hgap c).1 hc)))
  · intro hb
    by_contra hc
    have := hgap'.2 (hMT.sound _ ((hgap c).2 hc))
    exact absurd (of_decide_eq_true hb) (Nat.not_le.2 this)

end MIPRE.Tailored.Sofic

end
