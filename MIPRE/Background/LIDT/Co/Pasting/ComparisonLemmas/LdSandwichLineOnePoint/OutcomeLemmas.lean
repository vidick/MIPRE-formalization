/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LdSandwichLineOnePoint/OutcomeLemmas.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.PrefixMoved
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.OutcomeLemmas

@[expose] public section

/-!
# Section 12 pasting: line one-point transport — outcome lemmas

The outcome lemmas of the line one-point transport: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/OutcomeLemmas.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the one-point left families and their
outcomes are local, in `𝔓`, and the vendored conjugate transpose `ᴴ` is `star`. The lemmas
expand the outcomes of the restricted sandwich families (`G_{g} G_{g}^*` summed over the tuples
whose selected slot evaluates to `a`), show that no family has mass on `none`, and delete the
trailing coordinates of the full left family, leaving the prefix family
(`ldSandwichLineOnePointLeftFamily_eq_prefixOriginal`, the exact marginalization of
`ld-pasting.tex` lines 932--953). No statement mentions the state, so no swap or normalization
hypothesis appears, the vendored statements having none.

## Not ported

- `ldSandwichLineOnePoint_endpoint_comm_error_le`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point PointTuple AxisParallelLine appendPoint
  zeroCoord lastCoord)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SandwichedLineQuestion
  gHatTupleOutcomePrefixLastEquiv)
open MIPRE.LIDT.Co (SymStrat SubMeas IdxPolyFamily postprocess postprocess_total)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The postprocessed one-point right family has zero-operator `none` outcome,
because the selected slot satisfies `i < k` and is always postprocessed to `some`. -/
theorem ldSandwichLineOnePointRightFamily_outcome_none_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome none = 0 := by
  simp [ldSandwichLineOnePointRightFamily, postprocess, hi]

/-- The one-point right family is measurement-valued when the selected coordinate
exists.  This is the source of nonnegativity for the linear consistency defect. -/
theorem ldSandwichLineOnePointRightFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).total = 1 := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params q.1 zeroCoord
      direction := lastCoord params }
  simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, hi,
    postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

/-- The rotated prefix-only one-point left family has no `none` outcome. -/
theorem ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome none = 0 := by
  simp only [ldSandwichLineOnePointPrefixMovedFamily, postprocess, restrictSubMeas,
    Finset.sum_filter]
  refine Finset.sum_eq_zero fun gs _ => ?_
  split_ifs with h₁ h₂ <;> simp_all

/-- Generic outcome expansion for evaluating a restricted completed-slice sandwich
family at a concrete field value. -/
theorem gHatSandwichFamily_restrict_eval_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {n : ℕ} (xs : PointTuple params n)
    (idx : Fin n) (u : Point params) (a : Fq params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family n xs)
        (fun gs => (gs idx).isSome = true))
      (fun gs => Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u)
        (gs idx))).outcome (some a) =
      ∑ gs : GHatTupleOutcome params n,
        if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs idx) = some a then
          let half := gHatHalfProductOutcomeOperator params family n xs gs
          half * star half
        else
          0 := by
  simp only [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_congr rfl fun gs _ => ?_
  split_ifs with h₁ h₂ <;> simp_all

/-- Outcome expansion for the original full one-point left family at a concrete field value. -/
theorem ldSandwichLineOnePointLeftFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k i) q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params k,
        if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1) (gs ⟨i, hi⟩) =
            some a then
          let half := gHatHalfProductOutcomeOperator params family k q.2 gs
          half * star half
        else
          0 := by
  simpa [ldSandwichLineOnePointLeftFamily, hi] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family q.2 ⟨i, hi⟩ q.1 a

/-- Outcome expansion for the original-order prefix family at a concrete field value. -/
theorem ldSandwichLineOnePointPrefixOriginalFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
            (gs ⟨i, Nat.lt_succ_self i⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          half * star half
        else
          0 :=
  gHatSandwichFamily_restrict_eval_outcome_some
    params family (fun j => q.2 ⟨j.1, by omega⟩) ⟨i, Nat.lt_succ_self i⟩ q.1 a

/-- Outcome expansion for the selected-first prefix family at a concrete field value. -/
theorem ldSandwichLineOnePointPrefixMovedFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1) (gs 0) = some a then
          let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
          let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
          let half := gHatHalfProductOutcomeOperator params family (i + 1) xs gs
          half * star half
        else
          0 :=
  gHatSandwichFamily_restrict_eval_outcome_some
    params family (Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩)) 0 q.1 a

/-- The full one-point left family has no `none` outcome: the selected coordinate is
restricted to genuine completed polynomials before postprocessing by evaluation. -/
theorem ldSandwichLineOnePointLeftFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k i) q).outcome none = 0 := by
  simp only [ldSandwichLineOnePointLeftFamily, postprocess, restrictSubMeas, hi,
    Finset.sum_filter, dite_true]
  refine Finset.sum_eq_zero fun gs _ => ?_
  split_ifs with h₁ h₂ <;> simp_all

/-- The prefix-only one-point left family has no `none` outcome. -/
theorem ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome none = 0 := by
  simp only [ldSandwichLineOnePointPrefixOriginalFamily, postprocess, restrictSubMeas,
    Finset.sum_filter]
  refine Finset.sum_eq_zero fun gs _ => ?_
  split_ifs with h₁ h₂ <;> simp_all

/-- Delete one trailing sandwiched-line coordinate from the full one-point left
family, for a genuine field outcome.

This is the one-coordinate version of paper `ld-pasting.tex` lines 934--941:
summing over an extraneous completed-slice outcome collapses that measurement to
`I`, leaving the shorter sandwich. -/
theorem ldSandwichLineOnePointLeftFamily_drop_last_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {n i : ℕ} (hi : i < n)
    (q : SandwichedLineQuestion params (n + 1))
    (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome
        (some a) =
      ((ldSandwichLineOnePointLeftFamily params strategy family n i)
        (q.1, fun j => q.2 ⟨j.1, by omega⟩)).outcome (some a) := by
  have hiFull : i < n + 1 := by omega
  rw [ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hiFull q a,
    ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hi _ a,
    ← (gHatTupleOutcomePrefixLastEquiv params n).symm.sum_comp, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun gsPrefix _ => ?_
  have hsel : ∀ g, (gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g) ⟨i, hiFull⟩ =
      gsPrefix ⟨i, hi⟩ := fun _ => dite_eq_left hi
  simp only [hsel]
  by_cases hm : Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
      (gsPrefix ⟨i, hi⟩) = some a
  · simp only [hm, ↓reduceIte]
    exact gHatSandwich_sum_last_eq_prefix params family n q.2 gsPrefix
  · simp only [hm, ↓reduceIte, Finset.sum_const_zero]

/-- Deleting all coordinates after `i` from the full one-point left family leaves
exactly the prefix family used in the Cauchy--Schwarz transport.

This closes the paper's exact marginalization step `ld-pasting.tex` lines
932--953; the remaining analytic residual starts after this deletion. -/
theorem ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    ∀ {k i : ℕ} (hi : i < k),
      ldSandwichLineOnePointLeftFamily params strategy family k i =
        ldSandwichLineOnePointPrefixOriginalFamily params family hi
  | 0, i, hi => by cases hi
  | n + 1, i, hi => by
      by_cases hlast : i = n
      · subst i
        exact ldSandwichLineOnePointLeftFamily_self_eq_prefixOriginal params strategy family n
      · have hiPrefix : i < n := by omega
        have ih := ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
          (params := params) (strategy := strategy) (family := family) hiPrefix
        funext q
        have hout : ∀ o : Option (Fq params),
            ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome o =
              (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome o := by
          rintro (_ | a)
          · rw [ldSandwichLineOnePointLeftFamily_outcome_none_eq_zero
              params strategy family hi q,
              ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero params family hi q]
          · rw [ldSandwichLineOnePointLeftFamily_drop_last_outcome_some
              params strategy family hiPrefix q a, ih]
            rfl
        refine SubMeas.ext hout ?_
        rw [← SubMeas.sum_eq_total, ← SubMeas.sum_eq_total]
        exact Finset.sum_congr rfl fun o _ => hout o

end MIPRE.LIDT.Co.Pasting

end
