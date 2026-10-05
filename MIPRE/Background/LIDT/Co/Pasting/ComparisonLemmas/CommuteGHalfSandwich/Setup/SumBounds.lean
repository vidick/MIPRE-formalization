/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/Setup/SumBounds.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.Definitions
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.SumBounds

@[expose] public section

/-!
# Section 12 pasting: commute G half-sandwich setup — sum bounds

Sum-of-adjoint-products `≤ 1` bounds for the half-product, reverse-half-product, pair-prefix and
bipartite placed families: the counterpart of the vendored file of the same path under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M11,
section "Port conventions").

The half-product, reverse-half-product and pair-prefix bounds read no state: they are
inequalities in the local C*-algebra `𝔓` (the vendored `Op ι`). The bipartite bound
`leftTensor_rightTensor_sum_adjoint_mul_le_one` is about the placements `S.L` and `S.R`, so it
takes the symmetric model `S : SymModel 𝔓 K` as an explicit first argument, in place of the
vendored named carriers `(ι₁ := ι)`, `(ι₂ := ι)`; callers write
`leftTensor_rightTensor_sum_adjoint_mul_le_one strategy.state prefixOp tailOp hprefix htail`.
No vendored lemma here has a swap, density or normalization hypothesis.

The vendored half-product and pair-prefix proofs expand `∑_g (G_g T)^* (G_g T)` in a calc each;
here the private `sum_star_gHat_mul_mul_self` (`∑_g (Ĝ^x_g b)^* (Ĝ^x_g b) = b^* b`, the outcomes
being projections summing to `1`) serves both, and the pair-prefix bound is proved from it
directly rather than through the length-two half-product and its reindexing. The bipartite
bound is a sum of `S.opTensor (p^* p) (t^* t)` (`S.conjTranspose_opTensor`, `S.opTensor_mul`)
bounded by `S.opTensor_le_leftTensor`, without the vendored Kronecker identities.

## Not ported

- `rpow_oneSixteenth_nonneg`: classical, imported.
- `commuteGHalfSandwich_error_bound`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SlicePairQuestion pointTupleTail
  gHatTupleOutcomeConsEquiv')
open MIPRE.LIDT.Co (SymModel Measurement IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Half-product sum bounds -/

/-- The completed-slice outcomes at one point are projections summing to `1`, so
`∑_g (Ĝ^x_g b)^* (Ĝ^x_g b) = b^* b`. -/
private theorem sum_star_gHat_mul_mul_self
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) (b : 𝔓) :
    ∑ g : GHatOutcome params,
        star ((gHatIdxMeas params family x).outcome g * b) *
          ((gHatIdxMeas params family x).outcome g * b) =
      star b * b := by
  calc
    _ = ∑ g : GHatOutcome params, star b * (gHatIdxMeas params family x).outcome g * b :=
        Finset.sum_congr rfl fun g _ => by
          rw [star_mul, (gHatIdxMeas params family x).outcome_hermitian, mul_assoc,
            ← mul_assoc ((gHatIdxMeas params family x).outcome g), gHatIdxMeas_proj, ← mul_assoc]
    _ = star b * b := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, Measurement.sum_eq, mul_one]

/-- The ordered half-products of completed-slice outcomes satisfy `∑_gs T_gs^* T_gs ≤ 1`. -/
theorem gHatHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          star (gHatHalfProductOutcomeOperator params family r xs gs) *
            gHatHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let M := gHatIdxMeas params family (xs 0)
      let T := gHatHalfProductOutcomeOperator params family r (pointTupleTail xs)
      calc
        ∑ gs : GHatTupleOutcome params (r + 1),
            star (gHatHalfProductOutcomeOperator params family (r + 1) xs gs) *
              gHatHalfProductOutcomeOperator params family (r + 1) xs gs
          = ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              star (M.outcome p.1 * T p.2) * (M.outcome p.1 * T p.2) :=
            Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r) _ _ fun _ => rfl
        _ = ∑ gs : GHatTupleOutcome params r, star (T gs) * T gs := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            exact Finset.sum_congr rfl fun gs _ =>
              sum_star_gHat_mul_mul_self params family (xs 0) (T gs)
        _ ≤ 1 := ihr (pointTupleTail xs)

/-- The reverse-ordered half-products of completed-slice outcomes satisfy
`∑_gs T_gs^* T_gs ≤ 1`. -/
theorem gHatReverseHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          star (gHatReverseHalfProductOutcomeOperator params family r xs gs) *
            gHatReverseHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatReverseHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let M := gHatIdxMeas params family (xs 0)
      let T := gHatReverseHalfProductOutcomeOperator params family r (pointTupleTail xs)
      have hM : ∀ g, star (M.outcome g) * M.outcome g = M.outcome g := fun g => by
        rw [M.outcome_hermitian]
        exact gHatIdxMeas_proj params family (xs 0) g
      calc
        ∑ gs : GHatTupleOutcome params (r + 1),
            star (gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs) *
              gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs
          = ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              star (T p.2 * M.outcome p.1) * (T p.2 * M.outcome p.1) :=
            Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r) _ _ fun _ => rfl
        _ = ∑ g : GHatOutcome params,
              star (M.outcome g) * (∑ gs : GHatTupleOutcome params r, star (T gs) * T gs) *
                M.outcome g := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun gs _ => by simp only [star_mul, mul_assoc]
        _ ≤ ∑ g : GHatOutcome params, star (M.outcome g) * 1 * M.outcome g :=
            Finset.sum_le_sum fun g _ =>
              Preliminaries.conjTranspose_mul_mono (ihr (pointTupleTail xs))
        _ = 1 := by
            simp only [mul_one, hM]
            exact M.sum_eq

/-! ### Pair-prefix and bipartite tensor bounds -/

/-- The products `Ĝ^x_g Ĝ^y_h` of two completed slices satisfy
`∑_{g,h} (Ĝ^x_g Ĝ^y_h)^* (Ĝ^x_g Ĝ^y_h) ≤ 1`, with equality. -/
theorem gHatPairPrefix_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (q : SlicePairQuestion params) :
    ∑ og : GHatOutcome params × GHatOutcome params,
        star (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)) *
          (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)) ≤ 1 := by
  refine le_of_eq ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ h : GHatOutcome params,
          star ((gHatIdxMeas params family q.2).outcome h) *
            (gHatIdxMeas params family q.2).outcome h :=
        Finset.sum_congr rfl fun h _ => sum_star_gHat_mul_mul_self params family q.1 _
    _ = 1 := by
        simpa only [mul_one, star_one] using sum_star_gHat_mul_mul_self params family q.2 1

/-- Generic tensor-contraction bound: if `prefixOp : α → 𝔓` and `tailOp : β → 𝔓` each satisfy
`∑ (·)^* (·) ≤ 1`, then the joint family `S.L (prefixOp a) * S.R (tailOp b)` on `α × β` also
satisfies `∑ (·)^* (·) ≤ 1`. -/
theorem leftTensor_rightTensor_sum_adjoint_mul_le_one
    (S : SymModel 𝔓 K)
    {α β : Type*}
    [Fintype α]
    [Fintype β]
    (prefixOp : α → 𝔓)
    (tailOp : β → 𝔓)
    (hprefix : ∑ a : α, star (prefixOp a) * prefixOp a ≤ 1)
    (htail : ∑ b : β, star (tailOp b) * tailOp b ≤ 1) :
    ∑ ag : α × β,
        star (S.L (prefixOp ag.1) * S.R (tailOp ag.2)) *
          (S.L (prefixOp ag.1) * S.R (tailOp ag.2)) ≤ 1 := by
  calc
    _ = ∑ a : α, S.L (star (prefixOp a) * prefixOp a) *
          S.R (∑ b : β, star (tailOp b) * tailOp b) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← S.rightTensor_finset_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ =>
          (congrArg (· * (S.L (prefixOp a) * S.R (tailOp b)))
            (S.conjTranspose_opTensor (prefixOp a) (tailOp b))).trans (S.opTensor_mul _ _ _ _)
    _ ≤ ∑ a : α, S.L (star (prefixOp a) * prefixOp a) :=
        Finset.sum_le_sum fun a _ => S.opTensor_le_leftTensor (star_mul_self_nonneg _) htail
    _ = S.L (∑ a : α, star (prefixOp a) * prefixOp a) := S.leftTensor_finset_sum _ _
    _ ≤ 1 := S.leftTensor_le_one hprefix

end MIPRE.LIDT.Co.Pasting

end
