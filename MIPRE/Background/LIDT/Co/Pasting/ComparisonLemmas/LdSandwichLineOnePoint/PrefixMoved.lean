/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LdSandwichLineOnePoint/PrefixMoved.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.Endpoint

@[expose] public section

/-!
# Section 12 pasting: line one-point transport — prefix moved lemmas

The prefix lemmas of the line one-point transport: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/PrefixMoved.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the prefix families and the half-products
are local, in `𝔓`, and the vendored conjugate transpose `ᴴ` is `star`. The endpoint consistency
of the rotated prefix family is a `ConsRel` on `strategy.state`, and the raw commutation of the
prefix an `SDDOpRel` on a symmetric model `S`; no swap or normalization hypothesis appears, the
vendored statements having none. The half-product identities (the last factor split off, the
last slice summed out, the reversed product as the adjoint) hold in `𝔓` from the projectivity of
the completed slices alone.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SandwichedLineQuestion pointTupleTail
  gHatTupleOutcomeTail commuteGHalfSandwichError pointTupleLastFrontEquiv
  gHatTupleOutcomeLastFrontEquiv pointTupleLastReverseEquiv gHatTupleOutcomeLastReverseEquiv
  gHatTupleOutcomePrefixLastEquiv)
open MIPRE.LIDT.Co (SymModel SymStrat IdxSubMeas IdxPolyFamily postprocess evaluateAt
  completeSubMeas)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The original one-point left family restricted to the prefix through coordinate `i`. -/
noncomputable def ldSandwichLineOnePointPrefixOriginalFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) 𝔓 :=
  fun q =>
    let xs : PointTuple params (i + 1) := fun j => q.2 ⟨j.1, by omega⟩
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family (i + 1) xs)
        (fun gs => (gs ⟨i, Nat.lt_succ_self i⟩).isSome = true))
      (fun gs => Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩))

/-- The prefix family after rotating the selected coordinate to the front. -/
noncomputable def ldSandwichLineOnePointPrefixMovedFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) 𝔓 :=
  fun q =>
    let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
    let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family (i + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1) (gs 0))

/-- Rotating the selected coordinate to the front reduces the prefix family to `ldGbcon`.

This is the prefix-completeness collapse and endpoint identification used after
`references/ldt-paper/ld-pasting.tex:1011--1024`: once the selected coordinate is
first, summing the remaining prefix sandwich leaves the one-point endpoint
measurement. -/
theorem ldSandwichLineOnePointPrefixMoved_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePointPrefixMovedFamily params family hi =
      (fun q : SandwichedLineQuestion params k =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some) := by
  funext q
  let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) fun j => q.2 ⟨j.1, by omega⟩
  exact congrFun (ldSandwichLineOnePointLeftFamily_zero_eq_endpoint params strategy family
    (k := i + 1) (Nat.succ_pos i)) (q.1, xs)

/-- The global one-point left family at its last prefix index is the prefix family. -/
theorem ldSandwichLineOnePointLeftFamily_self_eq_prefixOriginal
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (i : ℕ) :
    ldSandwichLineOnePointLeftFamily params strategy family (i + 1) i =
      ldSandwichLineOnePointPrefixOriginalFamily params family (Nat.lt_succ_self i) := by
  funext q
  simp [ldSandwichLineOnePointLeftFamily, ldSandwichLineOnePointPrefixOriginalFamily]

/-- Endpoint consistency for the rotated prefix family. -/
theorem ldSandwichLineOnePointPrefixMoved_consRel_endpoint_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    {k i : ℕ} (hi : i < k) :
    strategy.state.ConsRel
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixMovedFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) := by
  rw [ldSandwichLineOnePointPrefixMoved_eq_endpoint params strategy family hi]
  exact ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
    params strategy eps delta zeta haxis hself family hcons k i hi

/-- Raw commutation for the nonempty prefix before adding the remaining question tail. -/
theorem ldSandwichLineOnePointPrefixMoved_rawCommutation
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    {i : ℕ} (hi0 : i ≠ 0) :
    S.SDDOpRel
      (uniformDistribution (PointTuple params (i + 1)))
      (gHatHalfSandwichLeft S params family (i + 1))
      (gHatHalfSandwichRight S params family (i + 1))
      (commuteGHalfSandwichError params gamma zeta (i + 1)) :=
  (hcomm (i + 1) (by omega)).repeatedCommutation

/-- Expand a half-product into the prefix product times the last slice operator. -/
theorem gHatHalfProduct_prefix_mul_last
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ i (xs : PointTuple params (i + 2)) (gs : GHatTupleOutcome params (i + 2)),
      gHatHalfProductOutcomeOperator params family (i + 2) xs gs =
        gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => xs ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩) *
          (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
            (gs ⟨i + 1, by omega⟩) := by
  intro i
  induction i with
  | zero =>
      intro xs gs
      simp [gHatHalfProductOutcomeOperator, pointTupleTail, gHatTupleOutcomeTail]
  | succ i ih =>
      intro xs gs
      rw [gHatHalfProductOutcomeOperator, ih (pointTupleTail xs) (gHatTupleOutcomeTail gs)]
      simp only [gHatHalfProductOutcomeOperator, pointTupleTail, gHatTupleOutcomeTail, mul_assoc]
      rfl

/-- Split the ordered half-product into its first `n` coordinates and the last slice. -/
theorem gHatHalfProductOutcomeOperator_prefix_last
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ n (xs : PointTuple params (n + 1)) (gs : GHatTupleOutcome params (n + 1)),
      gHatHalfProductOutcomeOperator params family (n + 1) xs gs =
        gHatHalfProductOutcomeOperator params family n
            (fun j => xs ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩) *
          (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome
            (gs ⟨n, Nat.lt_succ_self n⟩)
  | 0, xs, gs => by
      simp [gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => gHatHalfProduct_prefix_mul_last params family n xs gs

/-- Summing the last completed-slice sandwich coordinate deletes that coordinate.

This formalizes the measurement-completeness step in `ld-pasting.tex`
lines 934--941 for a single trailing coordinate. -/
theorem gHatSandwich_sum_last_eq_prefix
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (n : ℕ) (xs : PointTuple params (n + 1))
    (gsPrefix : GHatTupleOutcome params n) :
    (∑ g : GHatOutcome params,
      let half := gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * star half) =
      gHatHalfProductOutcomeOperator params family n
        (fun j => xs ⟨j.1, by omega⟩) gsPrefix *
        star (gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix) := by
  let P : 𝔓 :=
    gHatHalfProductOutcomeOperator params family n
      (fun j => xs ⟨j.1, by omega⟩) gsPrefix
  let G : GHatOutcome params → 𝔓 := fun g =>
    (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome g
  have hsumG : (∑ g : GHatOutcome params, G g) = 1 := by
    refine (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).sum_eq_total.trans ?_
    simp [gHatIdxMeas, completeSubMeas]
  have hGG : ∀ g, G g * star (G g) = G g := fun g => by
    rw [(gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome_hermitian g]
    exact gHatIdxMeas_proj params family (xs ⟨n, Nat.lt_succ_self n⟩) g
  calc
    (∑ g : GHatOutcome params,
      let half := gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * star half)
        = ∑ g : GHatOutcome params, P * (G g * star (G g)) * star P := by
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [gHatHalfProductOutcomeOperator_prefix_last params family n xs]
          simp [P, G, gHatTupleOutcomePrefixLastEquiv, star_mul, mul_assoc]
    _ = P * star P := by
          simp only [hGG]
          rw [← Finset.sum_mul, ← Finset.mul_sum, hsumG, mul_one]

/-- Reversing the prefix after moving the last coordinate to the front gives the adjoint product. -/
theorem gHatHalfProduct_lastReverse_eq_conjTranspose
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ i (xs : PointTuple params (i + 1)) (gs : GHatTupleOutcome params (i + 1)),
      gHatHalfProductOutcomeOperator params family (i + 1)
          ((pointTupleLastReverseEquiv params i) xs)
          ((gHatTupleOutcomeLastReverseEquiv params i) gs) =
        star (gHatHalfProductOutcomeOperator params family (i + 1) xs gs) := by
  intro i
  induction i with
  | zero =>
      intro xs gs
      have hhead :
          star ((gHatIdxMeas params family (xs 0)).outcome (gs 0)) =
            (gHatIdxMeas params family (xs 0)).outcome (gs 0) :=
        (gHatIdxMeas params family (xs 0)).outcome_hermitian (gs 0)
      simp [pointTupleLastReverseEquiv, gHatTupleOutcomeLastReverseEquiv,
        gHatHalfProductOutcomeOperator, hhead]
  | succ i ih =>
      intro xs gs
      let xsPrefix : PointTuple params (i + 1) := fun j => xs ⟨j.1, by omega⟩
      let gsPrefix : GHatTupleOutcome params (i + 1) := fun j => gs ⟨j.1, by omega⟩
      have htail :
          pointTupleTail ((pointTupleLastReverseEquiv params (i + 1)) xs) =
            (pointTupleLastReverseEquiv params i) xsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [pointTupleTail, pointTupleLastReverseEquiv, xsPrefix]
        | succ j =>
            simpa only [pointTupleTail, pointTupleLastReverseEquiv, Equiv.coe_fn_mk,
              Fin.cons_succ, xsPrefix] using
              congrArg xs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hgtail :
          gHatTupleOutcomeTail ((gHatTupleOutcomeLastReverseEquiv params (i + 1)) gs) =
            (gHatTupleOutcomeLastReverseEquiv params i) gsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv, gsPrefix]
        | succ j =>
            simpa only [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv,
              Equiv.coe_fn_mk, Fin.cons_succ, gsPrefix] using
              congrArg gs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hlast :
          star ((gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩)) =
            (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩) :=
        (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome_hermitian
          (gs ⟨i + 1, by omega⟩)
      rw [gHatHalfProductOutcomeOperator, htail, hgtail, ih xsPrefix gsPrefix,
        gHatHalfProductOutcomeOperator_prefix_last params family (i + 1) xs gs, star_mul, hlast]
      rfl

/-- The rotated product on the last-reversed tuple is the adjoint of the last-front product. -/
theorem gHatRotatedHalfProduct_lastReverse_eq_conjTranspose_lastFront
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ i (xs : PointTuple params (i + 1)) (gs : GHatTupleOutcome params (i + 1)),
      gHatRotatedHalfProductOutcomeOperator params family (i + 1)
          ((pointTupleLastReverseEquiv params i) xs)
          ((gHatTupleOutcomeLastReverseEquiv params i) gs) =
        star (gHatHalfProductOutcomeOperator params family (i + 1)
          ((pointTupleLastFrontEquiv params i) xs)
          ((gHatTupleOutcomeLastFrontEquiv params i) gs)) := by
  intro i
  cases i with
  | zero =>
      intro xs gs
      have hhead :
          star ((gHatIdxMeas params family (xs 0)).outcome (gs 0)) =
            (gHatIdxMeas params family (xs 0)).outcome (gs 0) :=
        (gHatIdxMeas params family (xs 0)).outcome_hermitian (gs 0)
      simp [pointTupleLastReverseEquiv, gHatTupleOutcomeLastReverseEquiv,
        pointTupleLastFrontEquiv, gHatTupleOutcomeLastFrontEquiv,
        gHatRotatedHalfProductOutcomeOperator, gHatHalfProductOutcomeOperator, hhead]
  | succ i =>
      intro xs gs
      let xsPrefix : PointTuple params (i + 1) := fun j => xs ⟨j.1, by omega⟩
      let gsPrefix : GHatTupleOutcome params (i + 1) := fun j => gs ⟨j.1, by omega⟩
      have htail :
          pointTupleTail ((pointTupleLastReverseEquiv params (i + 1)) xs) =
            (pointTupleLastReverseEquiv params i) xsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [pointTupleTail, pointTupleLastReverseEquiv, xsPrefix]
        | succ j =>
            simpa only [pointTupleTail, pointTupleLastReverseEquiv, Equiv.coe_fn_mk,
              Fin.cons_succ, xsPrefix] using
              congrArg xs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hgtail :
          gHatTupleOutcomeTail ((gHatTupleOutcomeLastReverseEquiv params (i + 1)) gs) =
            (gHatTupleOutcomeLastReverseEquiv params i) gsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv, gsPrefix]
        | succ j =>
            simpa only [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv,
              Equiv.coe_fn_mk, Fin.cons_succ, gsPrefix] using
              congrArg gs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hhead :
          star ((gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩)) =
            (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩) :=
        (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome_hermitian
          (gs ⟨i + 1, by omega⟩)
      have hfront :
          gHatHalfProductOutcomeOperator params family (i + 1 + 1)
              ((pointTupleLastFrontEquiv params (i + 1)) xs)
              ((gHatTupleOutcomeLastFrontEquiv params (i + 1)) gs) =
            (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
                (gs ⟨i + 1, by omega⟩) *
              gHatHalfProductOutcomeOperator params family (i + 1) xsPrefix gsPrefix :=
        rfl
      rw [gHatRotatedHalfProductOutcomeOperator, htail, hgtail,
        gHatHalfProduct_lastReverse_eq_conjTranspose params family i xsPrefix gsPrefix,
        hfront, star_mul, hhead]
      rfl

end MIPRE.LIDT.Co.Pasting

end
