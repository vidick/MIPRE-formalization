/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Sandwich/
GHatSandwich.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Sandwich.Switcheroo

@[expose] public section

/-!
# Section 12 — Sandwich constructions: `GHat` sandwich families

Completed-slice sandwich families and restriction helpers: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The positivity and boundedness of the Bernoulli tail operator read no state, so they hold in
any C*-algebra with its order (`𝔓` and `K →L[ℂ] K` alike), through `CStarAlgebra.pow_nonneg`
and `Commute.mul_nonneg` in place of the vendored `Matrix.PosSemidef` arguments; the
restriction of a submeasurement holds in any ordered `⋆`-ring. The sandwiched family
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}` is a local
family in `𝔓`, and the two half-sandwich families take the symmetric model `S : SymModel 𝔓 K` as
their first explicit argument, in place of the vendored named carrier `(ιB := ι)`, and place by
`OpFamily.leftPlacedOpFamily S`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome InterpolationEligible pointTupleTail
  gHatTupleOutcomeTail)
open MIPRE.LIDT.Co (SymModel SubMeas IdxSubMeas OpFamily IdxOpFamily IdxPolyFamily)

section Bernoulli

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Each binomial term in the Bernoulli tail operator is positive. -/
theorem binomialOperatorTerm_nonneg {G : A} (n r : ℕ) (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ (Nat.choose n r : ℂ) • (G ^ r * (1 - G) ^ (n - r)) := by
  have hcomm : Commute G (1 - G) := (Commute.one_right G).sub_right (Commute.refl G)
  rw [Nat.cast_smul_eq_nsmul ℂ]
  refine nsmul_nonneg (Commute.mul_nonneg (CStarAlgebra.pow_nonneg G r hG)
    (CStarAlgebra.pow_nonneg (1 - G) (n - r) (sub_nonneg.mpr hGle))
    ((hcomm.pow_left r).pow_right (n - r))) _

/-- Positivity of the Bernoulli tail operator for a positive contraction. -/
theorem bernoulliTailOperator_nonneg (k degree : ℕ) (G : A) (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ bernoulliTailOperator k degree G :=
  Finset.sum_nonneg fun r _ => binomialOperatorTerm_nonneg k r hG hGle

/-- The Bernoulli tail operator is bounded by the identity for a positive contraction. -/
theorem bernoulliTailOperator_le_one (k degree : ℕ) (G : A) (hG : 0 ≤ G) (hGle : G ≤ 1) :
    bernoulliTailOperator k degree G ≤ 1 := by
  let term : ℕ → A := fun r => (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r))
  have hsubset : Finset.Icc (degree + 1) k ⊆ Finset.range (k + 1) := fun r hr =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hr).2)
  have hcomm : Commute G (1 - G) := (Commute.one_right G).sub_right (Commute.refl G)
  have hfull : ∑ r ∈ Finset.range (k + 1), term r = 1 := by
    calc ∑ r ∈ Finset.range (k + 1), term r
        = ∑ r ∈ Finset.range (k + 1), G ^ r * (1 - G) ^ (k - r) * (Nat.choose k r : A) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [term]
          rw [Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul, Nat.cast_comm]
      _ = (G + (1 - G)) ^ k := (Commute.add_pow hcomm k).symm
      _ = 1 := by rw [add_sub_cancel, one_pow]
  calc bernoulliTailOperator k degree G
      = ∑ r ∈ Finset.Icc (degree + 1) k, term r := rfl
    _ ≤ ∑ r ∈ Finset.range (k + 1), term r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun r _ _ =>
          binomialOperatorTerm_nonneg k r hG hGle
    _ = 1 := hfull

end Bernoulli

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Concrete family for the full sandwich
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatSandwichFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) 𝔓 :=
  fun xs => by
    refine
    { outcome := fun gs =>
        let half := gHatHalfProductOutcomeOperator params family k xs gs
        half * star half
      total :=
        let half := gHatHalfProductTotalOperator params family k xs
        half * star half
      outcome_pos := fun gs => mul_star_self_nonneg _
      sum_eq_total := ?_
      total_le_one := by
        simp only [gHatHalfProductTotalOperator_eq_one, star_one, mul_one, le_refl] }
    induction k with
    | zero =>
        rw [Fintype.sum_unique]
        rfl
    | succ k ih =>
        have htail : ∀ g (gs : GHatTupleOutcome params k),
            gHatTupleOutcomeTail
              ((Fin.consEquiv fun _ : Fin (k + 1) => GHatOutcome params) (g, gs)) = gs :=
          fun _ _ => rfl
        let G := gHatIdxMeas params family (xs 0)
        have ih' := ih (pointTupleTail xs)
        simp only [gHatHalfProductTotalOperator_eq_one, star_one, mul_one] at ih'
        have hsum : ∀ g, ∑ gs : GHatTupleOutcome params k,
            G.outcome g * gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
              star (G.outcome g *
                gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs) =
            G.outcome g := by
          intro g
          calc _ = G.outcome g * (∑ gs : GHatTupleOutcome params k,
                gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                  star (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs)) *
                G.outcome g := by
                rw [Finset.mul_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun gs _ => ?_
                rw [star_mul, G.outcome_hermitian g]
                simp only [mul_assoc]
            _ = G.outcome g := by rw [ih', mul_one, gHatIdxMeas_proj params family (xs 0) g]
        rw [← (Fin.consEquiv fun _ : Fin (k + 1) => GHatOutcome params).sum_comp,
          Fintype.sum_prod_type]
        simp only [gHatHalfProductOutcomeOperator, htail, Fin.consEquiv_apply, Fin.cons_zero]
        rw [Finset.sum_congr rfl fun g _ => hsum g, G.sum_eq_total,
          gHatHalfProductTotalOperator_eq_one, star_one, mul_one]
        rfl

/-- Restrict a submeasurement to the outcomes satisfying `p`, dropping all other
mass from the total operator. -/
noncomputable def restrictSubMeas {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] {α : Type*} [Fintype α]
    (A : SubMeas α R) (p : α → Prop) [DecidablePred p] : SubMeas α R where
  outcome := fun a => if p a then A.outcome a else 0
  total := ∑ a ∈ Finset.univ.filter p, A.outcome a
  outcome_pos := fun a => by
    by_cases ha : p a
    · simp only [ha, ite_true, A.outcome_pos a]
    · simp only [ha, ite_false, le_refl]
  sum_eq_total := (Finset.sum_filter p A.outcome).symm
  total_le_one :=
    (Finset.sum_le_univ_sum_of_nonneg A.outcome_pos).trans_eq A.sum_eq_total |>.trans
      A.total_le_one

/-- Restricting a submeasurement can only decrease its total operator. -/
theorem restrictSubMeas_total_le_total {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] {α : Type*} [Fintype α]
    (A : SubMeas α R) (p : α → Prop) [DecidablePred p] :
    (restrictSubMeas A p).total ≤ A.total :=
  (Finset.sum_le_univ_sum_of_nonneg A.outcome_pos).trans_eq A.sum_eq_total

/-- Restrict the sandwiched completed-slice family to tuples with support of size at
least `d + 1`, matching the `|τ| ≥ d+1` filter in the paper before interpolation. -/
noncomputable def interpolationEligibleSandwichFamily (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) 𝔓 :=
  fun xs => restrictSubMeas (gHatSandwichFamily params family k xs) (InterpolationEligible params)

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
noncomputable def gHatHalfSandwichLeft (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (K →L[ℂ] K) :=
  fun xs => OpFamily.leftPlacedOpFamily S
    { outcome := fun gs => gHatHalfProductOutcomeOperator params family k xs gs
      total := gHatHalfProductTotalOperator params family k xs }

/-- Concrete family for the cyclically permuted half-sandwich product. -/
noncomputable def gHatHalfSandwichRight (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (K →L[ℂ] K) :=
  fun xs => OpFamily.leftPlacedOpFamily S
    { outcome := fun gs => gHatRotatedHalfProductOutcomeOperator params family k xs gs
      total := gHatRotatedHalfProductTotalOperator params family k xs }

end MIPRE.LIDT.Co.Pasting

end
