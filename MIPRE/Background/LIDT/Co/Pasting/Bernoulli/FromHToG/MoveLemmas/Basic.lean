/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/MoveLemmas/Basic.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.QuantumState
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.Core.FactBundles
public import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.MoveLemmas.Basic

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/Basic.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the completed slices, the half-products and
the recurrence weights are local operators in `𝔓` (the vendored `Op ι`), and `ᴴ` is `star`. The
sandwich domination `psd_contraction_comm_sandwich_le` reads no state and holds in any
C⋆-algebra with its order. The two state lemmas whose vendored state only evaluates,
`fromHToG_qSDDCore_symm` (vendored `ψ : QuantumState ι`, applied to the joint state) and
`fromHToG_closenessOfIP_avgContext` (vendored `ψ : QuantumState (ι × ι)`), take a vector state
`V : VecState K` with joint operators `K →L[ℂ] K`, to which callers pass `strategy.state`; the
placement lemma `fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left` takes the
symmetric model `S : SymModel 𝔓 K`, in the vendored argument position.
`fromHToG_closenessOfIP_avgContext` drops the unused normalization hypothesis
`_hψ : ψ.IsNormalized` (section "Port conventions"), so its vendored callers' `ψbi hnorm` becomes
`strategy.state`.

## Not ported

- `abs_sub_le_four`: classical, imported.
- `commuteGHalfSandwichError_mono_length`: classical, imported.
- `fromHToGPointTupleReverseEquiv`: classical, imported.
- `fromHToGGHatTupleOutcomeReverseEquiv`: classical, imported.
- `fromHToG_pointTupleTail_snoc`: classical, imported.
- `fromHToG_gHatTupleOutcomeTail_snoc`: classical, imported.
- `fromHToG_sum_product`: classical, imported.
- `fromHToG_avgOver_sub`: classical, imported.
- `fromHToG_type_filtered_outcome_sum`: classical, imported.
- `fromHToG_bool_type_filtered_outcome_sum`: classical, imported.
- `fromHToG_sum₂_avgOver₂`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple Distribution avgOver avgOver_congr)
open MIPStarRE.LDT.Pasting (GHatType GHatOutcome GHatTupleOutcome pointTupleTail
  gHatTupleOutcomeTail fromHToGPointTupleReverseEquiv fromHToGGHatTupleOutcomeReverseEquiv
  fromHToG_pointTupleTail_snoc fromHToG_gHatTupleOutcomeTail_snoc fromHToG_avgOver_sub)
open MIPRE.LIDT.Co (SymModel VecState IdxPolyFamily sq_le_self)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Symmetry of the raw pointwise state-dependent distance core.  This local
form is useful when orienting adjoint half-sandwich commutators for the second
paper commutation step. -/
theorem fromHToG_qSDDCore_symm {Outcome : Type*} [Fintype Outcome] (V : VecState K)
    (A B : Outcome → K →L[ℂ] K) :
    V.qSDDCore A B = V.qSDDCore B A :=
  Finset.sum_congr rfl fun a _ => by rw [← neg_sub (B a) (A a), star_neg, neg_mul_neg]

/-- If `A` is PSD and `B ≤ C`, then the corresponding bipartite scalar
expectations with left/right tensor placement are monotone in the right factor. -/
theorem fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left (S : SymModel 𝔓 K)
    {A B C : 𝔓} (hA : 0 ≤ A) (hBC : B ≤ C) :
    S.ev (S.L A * S.R B) ≤ S.ev (S.L A * S.R C) :=
  S.ev_mono _ _ (S.opTensor_mono_right hA hBC)

/-- If `S` is a PSD contraction commuting with `B`, then `S * B * S ≤ B`.  This
formalizes the paper's `eq:S-sandwich` domination step without using explicit
square roots. -/
theorem psd_contraction_comm_sandwich_le {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄]
    [StarOrderedRing 𝔄] {S B : 𝔄}
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hB0 : 0 ≤ B) (hSB : Commute S B) :
    S * B * S ≤ B := by
  have hSS_le_one : S * S ≤ 1 := (sq_le_self hS0 hS1).trans hS1
  have hnonneg : 0 ≤ B * (1 - S * S) :=
    ((Commute.one_right B).sub_right (hSB.mul_left hSB).symm).mul_nonneg hB0
      (sub_nonneg.mpr hSS_le_one)
  rw [mul_sub, mul_one, ← mul_assoc, ← hSB.eq] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Paper `eq:S-sandwich` for the complete branch average `G`. -/
theorem fromHToGRecurrenceWeight_sandwich_base_le (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * family.averagedSubMeas.total * S ≤ family.averagedSubMeas.total :=
  psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    family.averagedSubMeas.total_nonneg
    (fromHToGRecurrenceWeight_commute_base params family prefixLen τtail)

/-- Paper `eq:S-sandwich` for the incomplete branch average `I - G`. -/
theorem fromHToGRecurrenceWeight_sandwich_one_sub_base_le (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * (1 - family.averagedSubMeas.total) * S ≤ 1 - family.averagedSubMeas.total :=
  psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    (sub_nonneg.mpr family.averagedSubMeas.total_le_one)
    (fromHToGRecurrenceWeight_commute_one_sub_base params family prefixLen τtail)

/-- Completed `ĝ` measurement outcomes are self-adjoint.  This records the
positivity-to-self-adjointness conversion used when orienting the adjoint
half-sandwich commutator in the `M₂ → M₃` move. -/
theorem fromHToG_gHatIdxMeas_outcome_isHermitian (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) (g : GHatOutcome params) :
    star ((gHatIdxMeas params family x).outcome g) = (gHatIdxMeas params family x).outcome g :=
  (IsSelfAdjoint.of_nonneg ((gHatIdxMeas params family x).outcome_pos g)).star_eq

/-- The reverse half-product is the adjoint of the ordered half-product. -/
theorem fromHToG_gHatReverseHalfProductOutcomeOperator_eq_adjoint (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    ∀ (n : ℕ) (xs : PointTuple params n) (gs : GHatTupleOutcome params n),
      gHatReverseHalfProductOutcomeOperator params family n xs gs =
        star (gHatHalfProductOutcomeOperator params family n xs gs)
  | 0, _xs, _gs => star_one 𝔓 |>.symm
  | n + 1, xs, gs => by
      rw [gHatReverseHalfProductOutcomeOperator, gHatHalfProductOutcomeOperator,
        fromHToG_gHatReverseHalfProductOutcomeOperator_eq_adjoint params family n, star_mul]
      exact congrArg _ (fromHToG_gHatIdxMeas_outcome_isHermitian params family _ _).symm

/-- Ordered half-products satisfy a snoc recursion. -/
theorem fromHToG_gHatHalfProductOutcomeOperator_snoc (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ (n : ℕ) (xs : PointTuple params n) (x : Fq params)
      (gs : GHatTupleOutcome params n) (g : GHatOutcome params),
      gHatHalfProductOutcomeOperator params family (n + 1) (Fin.snoc xs x) (Fin.snoc gs g) =
        gHatHalfProductOutcomeOperator params family n xs gs *
          (gHatIdxMeas params family x).outcome g
  | 0, xs, x, gs, g => by
      have h0x : Fin.snoc (α := fun _ : Fin 1 => Fq params) xs x 0 = x :=
        Fin.snoc_last (α := fun _ : Fin 1 => Fq params) x xs
      have h0g : Fin.snoc (α := fun _ : Fin 1 => GHatOutcome params) gs g 0 = g :=
        Fin.snoc_last (α := fun _ : Fin 1 => GHatOutcome params) g gs
      simp [gHatHalfProductOutcomeOperator, h0x, h0g]
  | n + 1, xs, x, gs, g => by
      rw [gHatHalfProductOutcomeOperator, fromHToG_pointTupleTail_snoc params xs x,
        fromHToG_gHatTupleOutcomeTail_snoc params gs g,
        fromHToG_gHatHalfProductOutcomeOperator_snoc params family n
          (pointTupleTail xs) x (gHatTupleOutcomeTail gs) g]
      have hheadx : Fin.snoc (α := fun _ : Fin (n + 2) => Fq params) xs x 0 = xs 0 := by
        simp
      have hheadg :
          Fin.snoc (α := fun _ : Fin (n + 2) => GHatOutcome params) gs g 0 = gs 0 := by
        simp
      rw [hheadx, hheadg, gHatHalfProductOutcomeOperator, mul_assoc]

/-- Reversing a tuple turns the ordered half-product into its adjoint. -/
theorem fromHToG_gHatHalfProduct_reverse_eq_adjoint (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ (n : ℕ) (xs : PointTuple params n) (gs : GHatTupleOutcome params n),
      gHatHalfProductOutcomeOperator params family n
          ((fromHToGPointTupleReverseEquiv params n) xs)
          ((fromHToGGHatTupleOutcomeReverseEquiv params n) gs) =
        star (gHatHalfProductOutcomeOperator params family n xs gs)
  | 0, _xs, _gs => star_one 𝔓 |>.symm
  | n + 1, xs, gs => by
      refine Fin.snocCases ?_ xs
      intro xs x
      refine Fin.snocCases ?_ gs
      intro gs g
      have hheadx : ((fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) 0 = x := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) xs x (Fin.rev 0) = x
        rw [Fin.rev_zero]
        simp
      have hheadg :
          ((fromHToGGHatTupleOutcomeReverseEquiv params (n + 1)) (Fin.snoc gs g)) 0 = g := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params) gs g (Fin.rev 0) = g
        rw [Fin.rev_zero]
        simp
      have htailx :
          pointTupleTail ((fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) =
            (fromHToGPointTupleReverseEquiv params n) xs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) xs x (i.succ.rev) = xs i.rev
        rw [Fin.rev_succ]
        simp
      have htailg :
          gHatTupleOutcomeTail ((fromHToGGHatTupleOutcomeReverseEquiv params (n + 1))
            (Fin.snoc gs g)) = (fromHToGGHatTupleOutcomeReverseEquiv params n) gs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params) gs g (i.succ.rev) =
          gs i.rev
        rw [Fin.rev_succ]
        simp
      rw [gHatHalfProductOutcomeOperator, hheadx, hheadg, htailx, htailg,
        fromHToG_gHatHalfProduct_reverse_eq_adjoint params family n xs gs,
        fromHToG_gHatHalfProductOutcomeOperator_snoc params family n xs x gs g, star_mul,
        fromHToG_gHatIdxMeas_outcome_isHermitian]

/-- Averaged-context variant of `closenessOfIP`: the contraction side condition is
only required after averaging over the question distribution. -/
theorem fromHToG_closenessOfIP_avgContext {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] (V : VecState K) (𝒟 : Distribution Question)
    (_h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → K →L[ℂ] K)
    (C : Question → OutcomeA → OutcomeB → K →L[ℂ] K)
    (γ : ℝ)
    (hAB : avgOver 𝒟 (fun q => V.qSDDCore (A q) (B q)) ≤ γ)
    (hC : avgOver 𝒟 (fun q =>
      ∑ a : OutcomeA, V.ev ((∑ b : OutcomeB, C q a b) * star (∑ b : OutcomeB, C q a b))) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * B q a))| ≤
      Real.sqrt γ := by
  let Csum : Question → OutcomeA → K →L[ℂ] K := fun q a => ∑ b : OutcomeB, C q a b
  let D : Question → OutcomeA → K →L[ℂ] K := fun q a => A q a - B q a
  let t : Question → OutcomeA → ℝ := fun q a => V.ev (Csum q a * D q a)
  let x : Question → OutcomeA → ℝ := fun q a => V.ev (Csum q a * star (Csum q a))
  let y : Question → OutcomeA → ℝ := fun q a => V.ev (star (D q a) * D q a)
  have hx : ∀ q a, 0 ≤ x q a := fun q a => by
    simpa [x] using V.ev_adjoint_self_nonneg (star (Csum q a))
  have hweighted := MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz 𝒟 t x y
    (fun q a => V.ev_abs_mul_le_sqrt (Csum q a) (D q a)) hx
    (fun q a => V.ev_adjoint_self_nonneg (D q a))
  have hgap :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * A q a)) -
          avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, V.ev (C q a b * B q a)) := by
    rw [fromHToG_avgOver_sub]
    refine avgOver_congr _ _ _ fun q => ?_
    simp only [t, Csum, D, mul_sub, V.ev_sub, Finset.sum_mul, V.ev_sum, Finset.sum_sub_distrib]
  rw [← hgap]
  calc
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a)|
      ≤ Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, x q a)) *
          Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := hweighted
    _ ≤ 1 * Real.sqrt (avgOver 𝒟 (fun q => V.qSDDCore (A q) (B q))) :=
          mul_le_mul_of_nonneg_right ((Real.sqrt_le_sqrt hC).trans_eq Real.sqrt_one)
            (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt γ := by
          rw [one_mul]
          exact Real.sqrt_le_sqrt hAB

end MIPRE.LIDT.Co.Pasting

end
