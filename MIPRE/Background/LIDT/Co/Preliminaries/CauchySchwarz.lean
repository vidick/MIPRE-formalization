/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.ApproxDelta

@[expose] public section

/-!
# Cauchy–Schwarz inequalities for approximate measurements

Cauchy–Schwarz-style propositions from Section 3 (Preliminaries) of the LDT paper: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean` in the port
of `planning/c6b-plan.md` (milestone M3, section "Port conventions").
- `easyApproxFromApproxDelta` — Proposition `prop:easy-approx-from-approx-delta`;
- `closenessOfIP` / `closenessOfIPAdjoint` — Proposition `prop:closeness-of-ip`
  (`eq:closeness3` / `eq:closeness4`);
- `cabApproxDelta` — Proposition `prop:cab-approx-delta`.

Every statement uses a single state and joint operators, so it takes a vector state
`V : VecState K` (a symmetric model is accepted through its coercion) and families in
`K →L[ℂ] K`, and drops the vendored normalization hypothesis `hψ : ψ.IsNormalized`, a theorem of
the vector state (`V.ev_one_of_isNormalized`). `SDDRel ψ` is `V.SDDRel`, `qSDDCore ψ` is
`V.qSDDCore`, `ᴴ` is `star`.

The proofs are those of the earlier ported files: `question_easyApproxFromApproxDelta` is
`question_overlap_gap_aux` (`SwitchSandwichPrep/ApproxDelta.lean`) after splitting the sum,
`closenessOfIP` and `closenessOfIPAdjoint` are `closenessOfInnerProduct_left` and `_right`
(`SwitchSandwichPrep/InnerProduct.lean`), and `cabApproxDelta` is `cabApproxDelta_raw`
(`Preliminaries/DistanceBounds.lean`) on the raw families.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_sub)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Cauchy–Schwarz for a sum of expectations:
`|∑_a ev (X_a Y_a)| ≤ √(∑_a ev (X_a X_a†)) · √(∑_a ev (Y_a† Y_a))`. -/
theorem sum_ev_mul_le_sqrt
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (X Y : Outcome → K →L[ℂ] K) :
    |∑ a : Outcome, V.ev (X a * Y a)| ≤
      Real.sqrt (∑ a : Outcome, V.ev (X a * star (X a))) *
        Real.sqrt (∑ a : Outcome, V.ev (star (Y a) * Y a)) :=
  (Finset.abs_sum_le_sum_abs _ _).trans <|
    (Finset.sum_le_sum fun a _ => V.ev_abs_mul_le_sqrt (X a) (Y a)).trans <|
      Real.sum_sqrt_mul_sqrt_le Finset.univ
        (fun a => by simpa only [star_star] using V.ev_adjoint_self_nonneg (star (X a)))
        (fun a => V.ev_adjoint_self_nonneg (Y a))

/-- Questionwise form of `prop:easy-approx-from-approx-delta`:
`|∑_a ev (A_a C_a) - ∑_a ev (B_a C_a)| ≤ √(qSDD A B)` for submeasurements `A`, `B`, `C`. -/
theorem question_easyApproxFromApproxDelta
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B C : SubMeas Outcome (K →L[ℂ] K)) :
    |(∑ a : Outcome, V.ev (A.outcome a * C.outcome a)) -
        ∑ a : Outcome, V.ev (B.outcome a * C.outcome a)| ≤
      Real.sqrt (V.qSDD A B) := by
  rw [← Finset.sum_sub_distrib]
  simpa only [sub_mul, V.ev_sub] using question_overlap_gap_aux V A B C

/-- `prop:easy-approx-from-approx-delta`.

If `A ≈_δ B` (sub-measurements) and `C` is a sub-measurement, then
`|𝔼_x Σ_a ⟨ψ| A_a C_a |ψ⟩ - 𝔼_x Σ_a ⟨ψ| B_a C_a |ψ⟩| ≤ √δ`. -/
theorem easyApproxFromApproxDelta
    {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B C : IdxSubMeas Question Outcome (K →L[ℂ] K))
    (δ : ℝ)
    (hAB : V.SDDRel 𝒟 A B δ) :
    |avgOver 𝒟 (fun q => ∑ a : Outcome, V.ev ((A q).outcome a * (C q).outcome a)) -
        avgOver 𝒟 (fun q => ∑ a : Outcome, V.ev ((B q).outcome a * (C q).outcome a))| ≤
      Real.sqrt δ := by
  rw [← avgOver_sub]
  exact (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
    (fun q => question_easyApproxFromApproxDelta V (A q) (B q) (C q))
    (fun q => V.qSDD_nonneg (A q) (B q)) h𝒟).trans
      (Real.sqrt_le_sqrt hAB.squaredDistanceBound)

/-- `prop:closeness-of-ip` (`eq:closeness3`).

If `A ≈_γ B` (raw operators) and `Σ_a (Σ_b C_{a,b})(Σ_b C_{a,b})† ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} A_a |ψ⟩ - 𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} B_a |ψ⟩| ≤ √γ`. -/
theorem closenessOfIP
    {Question OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (V : VecState K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → K →L[ℂ] K)
    (C : Question → OutcomeA → OutcomeB → K →L[ℂ] K)
    (γ : ℝ)
    (hAB : avgOver 𝒟 (fun q => V.qSDDCore (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b) * star (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * B q a))| ≤
      Real.sqrt γ :=
  closenessOfInnerProduct_left V 𝒟 h𝒟 A B C γ hAB hC

/-- `prop:closeness-of-ip` (`eq:closeness4`, adjoint version).

If `A† ≈_γ B†` and `Σ_a (Σ_b C_{a,b})†(Σ_b C_{a,b}) ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| A_a C_{a,b} |ψ⟩ - 𝔼_x Σ_{a,b} ⟨ψ| B_a C_{a,b} |ψ⟩| ≤ √γ`. -/
theorem closenessOfIPAdjoint
    {Question OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (V : VecState K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → K →L[ℂ] K)
    (C : Question → OutcomeA → OutcomeB → K →L[ℂ] K)
    (γ : ℝ)
    (hAB :
      avgOver 𝒟
        (fun q => V.qSDDCore (fun a => star (A q a)) (fun a => star (B q a))) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          star (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (B q a * C q a b))| ≤
      Real.sqrt γ :=
  closenessOfInnerProduct_right V 𝒟 h𝒟 A B C γ hAB hC

/-- `prop:cab-approx-delta`.

If `A ≈_δ B` and `∀ x a, Σ_b (C_{a,b})† C_{a,b} ≤ I`, then
`C_{a,b} A_a ≈_δ C_{a,b} B_a`. -/
theorem cabApproxDelta
    {Question OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (V : VecState K)
    (𝒟 : Distribution Question)
    (A B : Question → OutcomeA → K →L[ℂ] K)
    (C : Question → OutcomeA → OutcomeB → K →L[ℂ] K)
    (δ : ℝ)
    (hAB : avgOver 𝒟 (fun q => V.qSDDCore (A q) (B q)) ≤ δ)
    (hC : ∀ q, ∀ a : OutcomeA, ∑ b : OutcomeB, star (C q a b) * C q a b ≤ 1) :
    avgOver 𝒟
      (fun q =>
        V.qSDDCore
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * A q ab.1)
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * B q ab.1))
      ≤ δ :=
  (cabApproxDelta_raw V 𝒟 (fun q => ⟨A q, ∑ a, A q a⟩) (fun q => ⟨B q, ∑ a, B q a⟩) C δ
    ⟨hAB⟩ hC).squaredDistanceBound

end MIPRE.LIDT.Co.Preliminaries

end
