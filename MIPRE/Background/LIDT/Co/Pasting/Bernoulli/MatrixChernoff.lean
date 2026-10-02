/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
MatrixChernoff.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.Scalar
public import MIPRE.Background.LIDT.Co.Pasting.Statements
public import MIPRE.Tactics

@[expose] public section

/-!
# Section 12 pasting: matrix Chernoff comparison

Continuous-functional-calculus form of the Bernoulli matrix Chernoff lemma: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/MatrixChernoff.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The two functional-calculus identities mention no state, so they are stated over any
C⋆-algebra: they serve the local algebra `𝔓` (the vendored `Op ι`) and
`K →L[ℂ] K` alike. The vendored entrywise `ext i j; simp` closing the first of them is
`Nat.cast_smul_eq_nsmul` here. The Chernoff comparison `chernoffBernoulliMatrix` evaluates an
operator on the space of its state, so its vendored one-space state `ψ : QuantumState ι` and
operator `X : Op ι` are a vector state `V : VecState K` and an operator `X : K →L[ℂ] K`, as in
`ChernoffBernoulliMatrixStatement` of `Co/Pasting/Statements.lean`. The hypothesis
`hnorm : ψ.IsNormalized` is dropped: a vector state is normalized (`V.ev_one_of_isNormalized`).

The scalar Bernoulli tail polynomial, its affine lower envelope and the pointwise comparison of
the two are classical and imported from the vendored `Pasting/Bernoulli/Scalar.lean` through an
explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT.Pasting (scalarBernoulliTail bernoulliTailLowerAffine
  bernoulliTailLowerAffine_le_scalarBernoulliTail)
open MIPRE.LIDT.Co (VecState SubMeas)

section CFC

variable {A : Type*} [CStarAlgebra A]

/-- The scalar Bernoulli tail polynomial lifted through continuous functional
calculus is exactly the matrix Bernoulli tail operator. -/
theorem cfc_scalarBernoulliTail_eq_bernoulliTailOperator
    (X : A) (hA : IsSelfAdjoint X) (k degree : ℕ) :
    cfc (scalarBernoulliTail k degree) X = bernoulliTailOperator k degree X := by
  have hone : ContinuousOn (fun p : ℝ => 1 - p) (spectrum ℝ X) :=
    (continuous_const.sub continuous_id).continuousOn
  have hsub : cfc (fun p : ℝ => 1 - p) X = 1 - X := by
    rw [cfc_sub (a := X) (f := fun _ => 1) (g := fun p => p) continuousOn_const continuousOn_id,
      cfc_const_one ℝ X hA, cfc_id' ℝ X hA]
  have hterm : ∀ r : ℕ,
      cfc (fun p : ℝ => (Nat.choose k r : ℝ) * (p ^ r * (1 - p) ^ (k - r))) X =
        (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r)) := fun r => by
    rw [cfc_const_mul (Nat.choose k r : ℝ) (fun p => p ^ r * (1 - p) ^ (k - r)) X
        ((continuous_pow r).continuousOn.mul (hone.pow _)),
      cfc_mul (fun p : ℝ => p ^ r) (fun p => (1 - p) ^ (k - r)) X
        (continuous_pow r).continuousOn (hone.pow _),
      cfc_pow_id X r hA, cfc_pow (fun p : ℝ => 1 - p) (k - r) X hone hA, hsub,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [show scalarBernoulliTail k degree = ∑ r ∈ Finset.Icc (degree + 1) k,
      fun p : ℝ => (Nat.choose k r : ℝ) * (p ^ r * (1 - p) ^ (k - r)) from
      (Finset.sum_fn _ _).symm,
    cfc_sum (fun r p => (Nat.choose k r : ℝ) * (p ^ r * (1 - p) ^ (k - r))) X _ fun r _ =>
      continuousOn_const.mul ((continuous_pow r).continuousOn.mul (hone.pow _))]
  exact Finset.sum_congr rfl fun r _ => hterm r

/-- Continuous functional calculus sends the affine lower envelope to the
expected affine operator expression. -/
theorem cfc_bernoulliTailLowerAffine_eq
    (X : A) (hA : IsSelfAdjoint X) (theta c : ℝ) :
    cfc (bernoulliTailLowerAffine theta c) X =
      ((1 - c : ℝ) • (1 : A)) - ((1 / (1 - theta) : ℝ) • (1 - X)) := by
  have hone : ContinuousOn (fun p : ℝ => 1 - p) (spectrum ℝ X) :=
    (continuous_const.sub continuous_id).continuousOn
  rw [show bernoulliTailLowerAffine theta c =
      fun p => (1 - c) - (1 / (1 - theta)) * (1 - p) from rfl,
    cfc_sub (a := X) (f := fun _ => 1 - c) (g := fun p => (1 / (1 - theta)) * (1 - p))
      continuousOn_const (continuousOn_const.mul hone),
    cfc_const (1 - c) X hA, Algebra.algebraMap_eq_smul_one,
    cfc_const_mul (1 / (1 - theta)) (fun p : ℝ => 1 - p) X hone,
    cfc_sub (a := X) (f := fun _ => 1) (g := fun p => p) continuousOn_const continuousOn_id,
    cfc_const_one ℝ X hA, cfc_id' ℝ X hA]

end CFC

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `lem:chernoff-bernoulli-matrix`.

Continuous functional calculus compares the Bernoulli-tail polynomial `F(X)` against an affine
lower envelope, and the scalar Hoeffding estimate is the classical
`bernoulliTailLowerAffine_le_scalarBernoulliTail`. -/
theorem chernoffBernoulliMatrix
    (V : VecState K)
    (theta : ℝ) (k degree : ℕ) (X : K →L[ℂ] K) (kappa : ℝ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : ℝ)) / theta ≤ (k : ℝ))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : V.CompletenessAtLeast
      ({ outcome := fun _ => X
         total := X
         outcome_pos := fun _ => hXpsd
         sum_eq_total := Fintype.sum_unique fun _ => X
         total_le_one := hXleOne } : SubMeas Unit (K →L[ℂ] K))
      (1 - kappa)) :
    ChernoffBernoulliMatrixStatement V theta k degree X kappa hXpsd hXleOne := by
  set expTerm : ℝ := Real.exp (-((theta ^ (2 : ℕ)) * (k : ℝ)) / 2)
  have hXsa : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hXpsd
  have hPointwise : ∀ x ∈ spectrum ℝ X,
      bernoulliTailLowerAffine theta expTerm x ≤ scalarBernoulliTail k degree x := fun x hx =>
    bernoulliTailLowerAffine_le_scalarBernoulliTail theta k degree hθ0 hθ1 hk
      (spectrum_nonneg_of_nonneg hXpsd hx)
      ((CFC.le_one_iff (R := ℝ) X (ha := hXsa)).1 hXleOne x hx)
  have hContLower : ContinuousOn (bernoulliTailLowerAffine theta expTerm) (spectrum ℝ X) :=
    (continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hContTail : ContinuousOn (scalarBernoulliTail k degree) (spectrum ℝ X) :=
    (continuous_finsetSum _ fun r _ => continuous_const.mul
      ((continuous_pow r).mul ((continuous_const.sub continuous_id).pow _))).continuousOn
  have hCfcLe : cfc (bernoulliTailLowerAffine theta expTerm) X ≤
      bernoulliTailOperator k degree X :=
    ((cfc_le_iff (f := bernoulliTailLowerAffine theta expTerm)
      (g := scalarBernoulliTail k degree) (a := X) (hf := hContLower)
      (hg := hContTail) (ha := hXsa)).2 hPointwise).trans_eq
      (cfc_scalarBernoulliTail_eq_bernoulliTailOperator X hXsa k degree)
  have hEvOneSub : 1 - V.ev X ≤ kappa := by
    have hmass : 1 - kappa ≤ V.ev X := hcomplete.lowerBound
    linarith
  have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
  have hfrac : (1 / (1 - theta)) * (1 - V.ev X) ≤ kappa / (1 - theta) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hEvOneSub hθden.le
  have hEvLower : 1 - kappa / (1 - theta) - expTerm ≤
      V.ev (cfc (bernoulliTailLowerAffine theta expTerm) X) := by
    rw [cfc_bernoulliTailLowerAffine_eq X hXsa theta expTerm, V.ev_sub, V.ev_real_smul,
      V.ev_real_smul, V.ev_sub, V.ev_one_of_isNormalized]
    linarith
  exact ⟨⟨hEvLower.trans (V.ev_mono _ _ hCfcLe)⟩⟩

end MIPRE.LIDT.Co.Pasting

end
