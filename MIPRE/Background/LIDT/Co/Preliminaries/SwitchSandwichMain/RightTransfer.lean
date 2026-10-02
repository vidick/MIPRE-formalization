/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/RightTransfer.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.InnerProduct

@[expose] public section

/-!
# Switch-sandwich main: middle-to-right transfer

The middle-to-right transfer estimate used in `prop:switch-sandwich`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/RightTransfer.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The state `ψ : QuantumState (ι × ι)` becomes a symmetric model `S : SymModel 𝔓 K`, the
placements `leftTensor`, `rightTensor` become `S.L`, `S.R`, and `ᴴ` becomes `star`. The vendored
normalization hypothesis `hψ : ψ.IsNormalized` is dropped: it is a theorem of the model
(`ev_one_of_isNormalized`).

The proof is the vendored one, shortened. For each question, the gap is `ev(LB (LT - RT))`,
where `LB`, `LT`, `RT` are the placements of `B` and of the total projector; Cauchy–Schwarz
(`ev_abs_mul_le_sqrt`) and `LB² ≤ 1` bound it by `√ev((LT - RT)²)`, and
`ev((LT - RT)²) ≤ qSDD (A ⊗ 1) (1 ⊗ A)` because both expand, for commuting projections, as
`ev L + ev R - 2 ev(L R)` and the cross terms `ev(Aₐ ⊗ A_b)` are nonnegative. The Kronecker
identities of the vendored proof become `S.leftTensor_mul_leftTensor`,
`S.rightTensor_mul_rightTensor` and `S.L_comm_R`. The question average is
`avgOver_abs_le_sqrt_of_pointwise`.

## New here

- `ev_star_L_sub_R_mul_self`: for self-adjoint `X`, `Y`, the expansion
  `ev((L X - R Y)^* (L X - R Y)) = ev L(X²) + ev R(Y²) - 2 ev(L X R Y)`, which the vendored
  proofs of `switchSandwich_rightTransfer` and `wrongSideEstimate` (`SelfConsistency/DataProcessing`)
  and of `qBipartiteSSCDefect` bounds (`BipartiteSelfConsistency/Core`) each repeat inline.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_sub)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For self-adjoint local operators `X`, `Y`,
`ev((L X - R Y)^* (L X - R Y)) = ev L(X²) + ev R(Y²) - 2 ev(L X R Y)`: the difference is
self-adjoint, and the two cross terms agree because the placements commute. -/
theorem ev_star_L_sub_R_mul_self (S : SymModel 𝔓 K) {X Y : 𝔓} (hX : IsSelfAdjoint X)
    (hY : IsSelfAdjoint Y) :
    S.ev (star (S.L X - S.R Y) * (S.L X - S.R Y)) =
      S.ev (S.L (X * X)) + S.ev (S.R (Y * Y)) - 2 * S.ev (S.L X * S.R Y) := by
  rw [star_sub, S.leftTensor_conjTranspose, S.rightTensor_conjTranspose, hX.star_eq, hY.star_eq,
    sub_mul, mul_sub, mul_sub, ← (S.L_comm_R X Y).eq, S.leftTensor_mul_leftTensor,
    S.rightTensor_mul_rightTensor, S.ev_sub, S.ev_sub, S.ev_sub]
  ring

/-- Middle-to-right transfer estimate used in the switch-sandwich theorem:
`|E_x ∑ₐ ev(B ⊗ Aₐ) - E_x ∑ₐ ev(B Aₐ ⊗ I)| ≤ √δ` when `A ⊗ I ≈_δ I ⊗ A`. -/
theorem switchSandwich_rightTransfer
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome 𝔓)
    (B : 𝔓) (hB : OpBounded01 B)
    (δ : ℝ) :
    BipartiteSDDRel S 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    |middleSandwichExpectation S 𝒟 A B -
      rightSandwichExpectation S 𝒟 A B| ≤
      Real.sqrt δ := by
  intro happrox
  have hδ :
      avgOver 𝒟
        (fun q => S.qSDD ((A q).toSubMeas.liftLeft S) ((A q).toSubMeas.liftRight S)) ≤ δ :=
    happrox.leftRightSquaredDistanceBound
  -- `ev((X ⊗ I - I ⊗ Y)²) = ev(X ⊗ I) + ev(I ⊗ Y) - 2 ev(X ⊗ Y)` for projections `X`, `Y`.
  have hexp : ∀ X Y : 𝔓, X * X = X → Y * Y = Y → 0 ≤ X → 0 ≤ Y →
      S.ev (star (S.L X - S.R Y) * (S.L X - S.R Y)) =
        S.ev (S.L X) + S.ev (S.R Y) - 2 * S.ev (S.L X * S.R Y) := fun X Y hX hY hX0 hY0 => by
    rw [ev_star_L_sub_R_mul_self S (.of_nonneg hX0) (.of_nonneg hY0), hX, hY]
  have hpointwise : ∀ q,
      |(∑ a, S.ev (S.L B * S.R ((A q).outcome a))) -
        ∑ a, S.ev (S.L (B * (A q).outcome a))| ≤
        Real.sqrt (S.qSDD ((A q).toSubMeas.liftLeft S) ((A q).toSubMeas.liftRight S)) := by
    intro q
    have hLB := leftTensor_opBounded01 S hB
    have hrewrite :
        (∑ a, S.ev (S.L (B * (A q).outcome a))) - ∑ a, S.ev (S.L B * S.R ((A q).outcome a)) =
          S.ev (S.L B * (S.L (A q).total - S.R (A q).total)) := by
      rw [mul_sub, S.ev_sub, ← (A q).sum_eq_total, ← S.leftTensor_finset_sum,
        ← S.rightTensor_finset_sum, Finset.mul_sum, Finset.mul_sum, S.ev_sum, S.ev_sum]
      simp only [S.leftTensor_mul_leftTensor]
    have hsqrt_LB : Real.sqrt (S.ev (S.L B * star (S.L B))) ≤ 1 := by
      rw [opBounded01_hermitian hLB]
      exact Real.sqrt_le_one.mpr
        ((S.ev_mono _ _ (opBounded01_sq_le_one hLB)).trans_eq S.ev_one_of_isNormalized)
    have hLT : S.ev (S.L (A q).total) = ∑ a, S.ev (S.L ((A q).outcome a)) := by
      rw [← (A q).sum_eq_total, ← S.leftTensor_finset_sum, S.ev_sum]
    have hRT : S.ev (S.R (A q).total) = ∑ a, S.ev (S.R ((A q).outcome a)) := by
      rw [← (A q).sum_eq_total, ← S.rightTensor_finset_sum, S.ev_sum]
    have hcross :
        ∑ a, S.ev (S.L ((A q).outcome a) * S.R ((A q).outcome a)) ≤
          S.ev (S.L (A q).total * S.R (A q).total) := by
      rw [← (A q).sum_eq_total, ← S.leftTensor_finset_sum, ← S.rightTensor_finset_sum,
        Finset.sum_mul_sum, S.ev_finset_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [S.ev_finset_sum]
      exact Finset.single_le_sum
        (fun b _ => ev_leftTensor_mul_rightTensor_nonneg S
          ((A q).outcome_pos a) ((A q).outcome_pos b)) (Finset.mem_univ a)
    have htotal_sq_le :
        S.ev (star (S.L (A q).total - S.R (A q).total) * (S.L (A q).total - S.R (A q).total)) ≤
          S.qSDD ((A q).toSubMeas.liftLeft S) ((A q).toSubMeas.liftRight S) := by
      have htot := projSubMeas_total_proj (A q)
      have htot0 := (A q).toSubMeas.total_nonneg
      show _ ≤ ∑ a, S.ev (star (S.L ((A q).outcome a) - S.R ((A q).outcome a)) *
        (S.L ((A q).outcome a) - S.R ((A q).outcome a)))
      rw [hexp _ _ htot htot htot0 htot0, Finset.sum_congr rfl fun a _ =>
          hexp _ _ ((A q).proj a) ((A q).proj a) ((A q).outcome_pos a) ((A q).outcome_pos a),
        Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hLT, hRT]
      linarith
    rw [abs_sub_comm, hrewrite]
    calc
      |S.ev (S.L B * (S.L (A q).total - S.R (A q).total))|
        ≤ Real.sqrt (S.ev (S.L B * star (S.L B))) *
            Real.sqrt (S.ev (star (S.L (A q).total - S.R (A q).total) *
              (S.L (A q).total - S.R (A q).total))) :=
          S.ev_abs_mul_le_sqrt _ _
      _ ≤ 1 * Real.sqrt (S.ev (star (S.L (A q).total - S.R (A q).total) *
              (S.L (A q).total - S.R (A q).total))) :=
          mul_le_mul_of_nonneg_right hsqrt_LB (Real.sqrt_nonneg _)
      _ ≤ _ := (one_mul _).trans_le (Real.sqrt_le_sqrt htotal_sq_le)
  rw [middleSandwichExpectation, rightSandwichExpectation, ← avgOver_sub]
  exact (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _ hpointwise
    (fun q => S.qSDD_nonneg _ _) h𝒟).trans (Real.sqrt_le_sqrt hδ)

end MIPRE.LIDT.Co.Preliminaries

end
