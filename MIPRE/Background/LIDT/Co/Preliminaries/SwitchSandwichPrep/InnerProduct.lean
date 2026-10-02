/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/InnerProduct.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.Core
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

@[expose] public section

/-!
# Switch-sandwich preparation: inner-product bounds

Cauchy–Schwarz-style inner-product bounds in the `avgOver` formulation used by
the switch-sandwich argument: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/InnerProduct.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The statements use a single state and joint operators, so they take a vector state
`V : VecState K` (a symmetric model is accepted through its coercion) and families of operators
in `K →L[ℂ] K`, and they drop the vendored normalization hypothesis `hψ : ψ.IsNormalized`, a
theorem of the vector state (`V.ev_one_of_isNormalized`). `ev_adjoint_eq` is the keystone's
`V.ev_conjTranspose` under its vendored name; the vendored proof by the normalized trace of the
density matrix is not needed.

## Not ported

- `avgOver_abs_le_sqrt_of_pointwise`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_nonneg avgOver_sub avgOver_congr)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `ev` is invariant under taking adjoints. -/
theorem ev_adjoint_eq (V : VecState K) (X : K →L[ℂ] K) : V.ev (star X) = V.ev X :=
  V.ev_conjTranspose X

/-- `prop:closeness-of-ip`, left-action clause `eq:closeness3`. -/
theorem closenessOfInnerProduct_left
    {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (V : VecState K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → K →L[ℂ] K)
    (C : Question → OutcomeA → OutcomeB → K →L[ℂ] K)
    (γ : ℝ)
    (hAB : avgOver 𝒟 (fun q => V.qSDDCore (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        (∑ a : OutcomeA, (∑ b : OutcomeB, C q a b) * star (∑ b : OutcomeB, C q a b)) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * A q a)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * B q a))|
      ≤ Real.sqrt γ := by
  have hpointwise :
      ∀ q,
        |(∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * A q a)) -
          ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * B q a)| ≤
          Real.sqrt (V.qSDDCore (A q) (B q)) := by
    intro q
    set Csum : OutcomeA → K →L[ℂ] K := fun a => ∑ b : OutcomeB, C q a b
    set D : OutcomeA → K →L[ℂ] K := fun a => A q a - B q a
    have hdiff :
        (∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * A q a)) -
            ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * B q a) =
          ∑ a : OutcomeA, V.ev (Csum a * D a) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← V.ev_sum, ← V.ev_sum, ← V.ev_sub, ← Finset.sum_mul, ← Finset.sum_mul, ← mul_sub]
    have hCsum_le_one : ∑ a : OutcomeA, V.ev (Csum a * star (Csum a)) ≤ 1 := by
      rw [← V.ev_sum]
      exact (V.ev_mono _ _ (hC q)).trans_eq V.ev_one_of_isNormalized
    have hsqrt_C : Real.sqrt (∑ a : OutcomeA, V.ev (Csum a * star (Csum a))) ≤ 1 :=
      Real.sqrt_le_one.mpr hCsum_le_one
    rw [hdiff]
    calc
      |∑ a : OutcomeA, V.ev (Csum a * D a)|
        ≤ ∑ a : OutcomeA, |V.ev (Csum a * D a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : OutcomeA,
            Real.sqrt (V.ev (Csum a * star (Csum a))) * Real.sqrt (V.ev (star (D a) * D a)) :=
          Finset.sum_le_sum fun a _ => V.ev_abs_mul_le_sqrt (Csum a) (D a)
      _ ≤ Real.sqrt (∑ a : OutcomeA, V.ev (Csum a * star (Csum a))) *
            Real.sqrt (∑ a : OutcomeA, V.ev (star (D a) * D a)) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ
            (fun a => by simpa only [star_star] using V.ev_adjoint_self_nonneg (star (Csum a)))
            (fun a => V.ev_adjoint_self_nonneg (D a))
      _ ≤ 1 * Real.sqrt (∑ a : OutcomeA, V.ev (star (D a) * D a)) :=
          mul_le_mul_of_nonneg_right hsqrt_C (Real.sqrt_nonneg _)
      _ = Real.sqrt (V.qSDDCore (A q) (B q)) := one_mul _
  have hsdd_nonneg : ∀ q, 0 ≤ V.qSDDCore (A q) (B q) := fun q =>
    Finset.sum_nonneg fun a _ => V.ev_adjoint_self_nonneg (A q a - B q a)
  rw [← avgOver_sub]
  exact (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _ hpointwise hsdd_nonneg h𝒟).trans
    (Real.sqrt_le_sqrt hAB)

/-- `prop:closeness-of-ip`, right-action clause `eq:closeness4`. -/
theorem closenessOfInnerProduct_right
    {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (V : VecState K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → K →L[ℂ] K)
    (C : Question → OutcomeA → OutcomeB → K →L[ℂ] K)
    (γ : ℝ)
    (hAB :
      avgOver 𝒟
        (fun q => V.qSDDCore (fun a : OutcomeA => star (A q a))
          (fun a : OutcomeA => star (B q a)))
        ≤ γ)
    (hC :
      ∀ q,
        (∑ a : OutcomeA, star (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (A q a * C q a b)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (B q a * C q a b))|
      ≤ Real.sqrt γ := by
  have hleft :=
    closenessOfInnerProduct_left V 𝒟 h𝒟
      (fun q a => star (A q a))
      (fun q a => star (B q a))
      (fun q a b => star (C q a b))
      γ hAB (fun q => by simpa only [← star_sum, star_star] using hC q)
  simpa only [← star_mul, V.ev_conjTranspose] using hleft

end MIPRE.LIDT.Co.Preliminaries

end
