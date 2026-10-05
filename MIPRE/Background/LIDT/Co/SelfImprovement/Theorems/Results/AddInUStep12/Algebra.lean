/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUStep12/Algebra.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.CommonHelpers
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Residual
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.ScalarChain

@[expose] public section

/-!
# Add-in-u Cauchy--Schwarz algebraic alignment

Operator identities that align the differences of the add-in-`u` scalar chains with the forms
used in the Cauchy--Schwarz estimates of the paper: the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUStep12/Algebra.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `addInU_step1_pointwise_op_eq` … `addInU_step4_pointwise_op_eq`: the operator-level
  difference identities for the four scalar moves, as identities in `K →L[ℂ] K` between
  `S.opTensor`, `S.L` and `S.R` terms. They take the model `(S : SymModel 𝔓 K)` as an explicit
  first argument and local operators `𝔓`, where the vendored lemmas are generic over a finite
  carrier `κ`. The vendored proofs compute with `opTensor_mul` and `simp [Matrix.mul_assoc]`;
  here they are rewrites with the keystone's oriented placement lemmas
  (`leftTensor_mul_opTensor`, `rightTensor_mul_opTensor`, `opTensor_mul_leftTensor`,
  `opTensor_sub_left`) and `mul_assoc`.
- `addInU_cs_chain_step1_diff_eq` … `addInU_cs_chain_step4_diff_eq` and their reverse forms:
  the differences of the diagonal chain `addInUCSChainQ0`–`Q4` in commutator-times-PSD form.
- `addInU_selected_cs_chain_step1_diff_eq` … `addInU_selected_cs_chain_step4_diff_eq` and their
  reverse forms: the same identities for the selected chain `addInUSelectedCSChainQ0`–`Q4`.

Every scalar is `strategy.state.ev` of a joint operator; `leftTensor A`, `rightTensor A` and
`opTensor A B` are `strategy.state.L A`, `strategy.state.R A` and `strategy.state.opTensor A B`.
No statement carries a swap, density or normalization hypothesis, and none of the vendored ones
did.

The vendored file imports `SelfImprovement/Theorems/Thresholds/Final.lean`, wholly classical and
without a Co file; so does this one.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 255–297
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution avgOver_congr
  avgOver_sub)
open MIPStarRE.LDT.SelfImprovement (AddInUSelection addInUSelectionPairs)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Algebraic CS-alignment for the add-in-u Step 1/2 differences

Pure operator-algebra rewrites that bring the differences `addInUCSChainQ1 - addInUCSChainQ0`
and `addInUCSChainQ2 - addInUCSChainQ1` into the shapes required by the paper's
Cauchy--Schwarz steps `eq:move-one-cauchy-schwarz` and `eq:move-another-cauchy-schwarz`
(`self_improvement.tex`, lines 261--266 and 285--289). The reverse-difference companions give
the downstream orientation `Q₀ - Q₁` and `Q₁ - Q₂`.

They do **not** discharge the Cauchy--Schwarz estimate itself; they reduce the raw
`|Q₁ - Q₀| ≤ √(2δ)` and `|Q₁ - Q₂| ≤ √(2δ)` bounds to a sandwich-form Cauchy--Schwarz on the
resulting `D · (M^u_h ⊗ T_h) · D'` expression, plus the two square-root inputs
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`. -/

/-- Operator identity for the `Q₀ → Q₁` move:
`(A^v M) ⊗ (T A^v) − M ⊗ (A^v T A^v) = (A^v ⊗ I − I ⊗ A^v) · (M ⊗ T) · (I ⊗ A^v)`. -/
theorem addInU_step1_pointwise_op_eq (S : SymModel 𝔓 K) (M Av Th : 𝔓) :
    S.opTensor (Av * M) (Th * Av) - S.opTensor M (Av * Th * Av) =
      (S.L Av - S.R Av) * (S.opTensor M Th * S.R Av) := by
  have h : S.opTensor M Th * S.R Av = S.opTensor M (Th * Av) :=
    (mul_assoc _ _ _).trans (congrArg (S.L M * ·) (S.rightTensor_mul_rightTensor Th Av))
  rw [h, sub_mul, S.leftTensor_mul_opTensor, S.rightTensor_mul_opTensor, mul_assoc Av Th Av]

/-- Operator identity for the `Q₁ → Q₂` move:
`(A^v M A^v) ⊗ T − (A^v M) ⊗ (T A^v) = (A^v ⊗ I) · (M ⊗ T) · (A^v ⊗ I − I ⊗ A^v)`. -/
theorem addInU_step2_pointwise_op_eq (S : SymModel 𝔓 K) (M Av Th : 𝔓) :
    S.opTensor (Av * M * Av) Th - S.opTensor (Av * M) (Th * Av) =
      S.L Av * (S.opTensor M Th * (S.L Av - S.R Av)) := by
  have h : S.opTensor M Th * S.R Av = S.opTensor M (Th * Av) :=
    (mul_assoc _ _ _).trans (congrArg (S.L M * ·) (S.rightTensor_mul_rightTensor Th Av))
  rw [mul_sub, mul_sub, h, S.opTensor_mul_leftTensor, S.leftTensor_mul_opTensor,
    S.leftTensor_mul_opTensor, mul_assoc Av M Av]

/-- Operator algebra reduction for the `Q₂ → Q₃` add-in-`u` step.

The operator difference of the bipartite-tensor expectations of
`A^v · H^u_h · A^v` and `A^u · H^u_h · A^v` (with shared right factor `T_h`)
factors as `(A^v − A^u) · H^u_h · A^v` on the left tensor factor, leaving the
right factor `T_h` untouched. -/
theorem addInU_step3_pointwise_op_eq (S : SymModel 𝔓 K) (Au Av Mh Th : 𝔓) :
    S.opTensor (Av * Mh * Av) Th - S.opTensor (Au * Mh * Av) Th =
      S.opTensor ((Av - Au) * Mh * Av) Th := by
  rw [S.opTensor_sub_left, sub_mul, sub_mul]

/-- Operator algebra reduction for the `Q₃ → Q₄` add-in-`u` step.

The operator difference of the bipartite-tensor expectations of
`A^u · H^u_h · A^v` and `A^u · H^u_h · A^u` (with shared right factor `T_h`)
factors as `A^u · H^u_h · (A^v − A^u)` on the left tensor factor, leaving the
right factor `T_h` untouched. -/
theorem addInU_step4_pointwise_op_eq (S : SymModel 𝔓 K) (Au Av Mh Th : 𝔓) :
    S.opTensor (Au * Mh * Av) Th - S.opTensor (Au * Mh * Au) Th =
      S.opTensor (Au * Mh * (Av - Au)) Th := by
  rw [S.opTensor_sub_left, mul_sub]

/-- Algebraic CS-alignment for the `Q₀ → Q₁` step.

Rewrites the difference `addInUCSChainQ1 - addInUCSChainQ0` in the exact form
appearing on the LHS of `eq:move-one-cauchy-schwarz` (paper lines 261--266):
the inner-product of the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}` with `M^u_h ⊗ T_h · (I ⊗ A^v_{h(v)})`,
averaged over `(u, v)` and summed over `h`.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency`. -/
theorem addInU_cs_chain_step1_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUCSChainQ1 params strategy T - addInUCSChainQ0 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          strategy.state.ev
            ((strategy.state.L Av - strategy.state.R Av) *
              (strategy.state.opTensor Mh (T.outcome h) * strategy.state.R Av))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun h _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step1_pointwise_op_eq strategy.state _ _ (T.outcome h)

/-- Algebraic CS-alignment for the `Q₁ → Q₂` step.

Rewrites the difference `addInUCSChainQ2 - addInUCSChainQ1` in the exact form
appearing on the LHS of `eq:move-another-cauchy-schwarz` (paper lines 285--289):
the inner-product of `(A^v_{h(v)} · M^u_h) ⊗ T_h` with the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}`, averaged over `(u, v)` and summed over `h`.
The Lean statement keeps the equivalent factored form
`(A^v_{h(v)} ⊗ I) · (M^u_h ⊗ T_h)` before the commutator.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`. -/
theorem addInU_cs_chain_step2_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUCSChainQ2 params strategy T - addInUCSChainQ1 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          strategy.state.ev
            (strategy.state.L Av *
              (strategy.state.opTensor Mh (T.outcome h) *
                (strategy.state.L Av - strategy.state.R Av)))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun h _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step2_pointwise_op_eq strategy.state _ _ (T.outcome h)

/-- Reverse-orientation form of `addInU_cs_chain_step1_diff_eq`.

This is the same algebraic identity as the `Q₀ → Q₁` rewrite, stated in the
`Q₀ - Q₁` orientation used by the later absolute-value chain. -/
theorem addInU_cs_chain_step1_reverse_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          strategy.state.ev
            ((strategy.state.L Av - strategy.state.R Av) *
              (strategy.state.opTensor Mh (T.outcome h) * strategy.state.R Av))) := by
  rw [← addInU_cs_chain_step1_diff_eq params strategy T, neg_sub]

/-- Reverse-orientation form of `addInU_cs_chain_step2_diff_eq`.

This is the same algebraic identity as the `Q₁ → Q₂` rewrite, stated in the
`Q₁ - Q₂` orientation used by the later absolute-value chain. -/
theorem addInU_cs_chain_step2_reverse_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          strategy.state.ev
            (strategy.state.L Av *
              (strategy.state.opTensor Mh (T.outcome h) *
                (strategy.state.L Av - strategy.state.R Av)))) := by
  rw [← addInU_cs_chain_step2_diff_eq params strategy T, neg_sub]

/-- Algebraic CS-alignment for the `Q₂ → Q₃` step.

Rewrites the difference `addInUCSChainQ2 - addInUCSChainQ3` in the exact form
appearing on the LHS of `eq:change-one-cauchy-schwarz` (paper lines 306--311):
the expectation of `((A^v_{h(v)} - A^u_{h(u)}) · H^u_h · A^v_{h(v)}) ⊗ T_h`,
averaged over `(u, v)` and summed over `h`.

The paper writes the middle factor as the fiber operator `M^u_o`; in this
formalization the preceding `o`-sum has already been collapsed along
`o = h(u)`, so the same factor appears as
`H^u_h = (sandwichedPolynomialSubMeasAt params strategy T u).outcome h`.

This identity is purely algebraic; the operator Cauchy--Schwarz estimate is
proved downstream by `add_in_u_cs_chain_q2_q3_factored_cs`. -/
theorem addInU_cs_chain_step3_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          strategy.state.ev
            (strategy.state.opTensor ((Av - Au) * Mh * Av) (T.outcome h))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun h _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step3_pointwise_op_eq strategy.state _ _ _ (T.outcome h)

/-! ### Selection-parametrized Step 1/2 algebraic identities -/

/-- Algebraic CS-alignment for the selected `Q₀ → Q₁` step.

This is the selection-parametrized form of `addInU_cs_chain_step1_diff_eq`.
The identity is stated in the same orientation as the diagonal chain, namely
as `Q₁ - Q₀`.  It rewrites the scalar difference using the same commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}`, but sums only over the selected pairs
`(o,h) ∈ S_u` and leaves the arbitrary outcome operator `M^u_o` in place. -/
theorem addInU_selected_cs_chain_step1_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ0 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            ((strategy.state.L Av - strategy.state.R Av) *
              (strategy.state.opTensor Moh (T.outcome ah.2) * strategy.state.R Av))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun ah _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step1_pointwise_op_eq strategy.state _ _ (T.outcome ah.2)

/-- Algebraic CS-alignment for the selected `Q₁ → Q₂` step.

This is the selection-parametrized form of `addInU_cs_chain_step2_diff_eq`,
with the arbitrary selected outcome operator `M^u_o` in the left tensor factor. -/
theorem addInU_selected_cs_chain_step2_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            (strategy.state.L Av *
              (strategy.state.opTensor Moh (T.outcome ah.2) *
                (strategy.state.L Av - strategy.state.R Av)))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun ah _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step2_pointwise_op_eq strategy.state _ _ (T.outcome ah.2)

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step1_diff_eq`. -/
theorem addInU_selected_cs_chain_step1_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            ((strategy.state.L Av - strategy.state.R Av) *
              (strategy.state.opTensor Moh (T.outcome ah.2) * strategy.state.R Av))) := by
  rw [← addInU_selected_cs_chain_step1_diff_eq params strategy M T S, neg_sub]

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step2_diff_eq`. -/
theorem addInU_selected_cs_chain_step2_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            (strategy.state.L Av *
              (strategy.state.opTensor Moh (T.outcome ah.2) *
                (strategy.state.L Av - strategy.state.R Av)))) := by
  rw [← addInU_selected_cs_chain_step2_diff_eq params strategy M T S, neg_sub]

/-- Algebraic CS-alignment for the selected `Q₂ → Q₃` step.

This rewrites the first point-replacement move for an arbitrary selected
outcome family.  The only changed factor is the left copy of the point
projector, from `A^v_{h(v)}` to `A^u_{h(u)}`. -/
theorem addInU_selected_cs_chain_step3_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            (strategy.state.opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun ah _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step3_pointwise_op_eq strategy.state _ _ _ (T.outcome ah.2)

/-- Algebraic CS-alignment for the selected `Q₃ → Q₄` step.

This rewrites the second point-replacement move for an arbitrary selected
outcome family.  The only changed factor is the right copy of the point
projector, from `A^v_{h(v)}` to `A^u_{h(u)}`. -/
theorem addInU_selected_cs_chain_step4_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            (strategy.state.opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun ah _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step4_pointwise_op_eq strategy.state _ _ _ (T.outcome ah.2)

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step3_diff_eq`. -/
theorem addInU_selected_cs_chain_step3_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            (strategy.state.opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2))) := by
  rw [← addInU_selected_cs_chain_step3_diff_eq params strategy M T S, neg_sub]

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step4_diff_eq`. -/
theorem addInU_selected_cs_chain_step4_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ4 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          strategy.state.ev
            (strategy.state.opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2))) := by
  rw [← addInU_selected_cs_chain_step4_diff_eq params strategy M T S, neg_sub]

/-- Algebraic CS-alignment for the `Q₃ → Q₄` step.

Rewrites the difference `addInUCSChainQ3 - addInUCSChainQ4` in the exact form
appearing on the left-hand side of `eq:change-another` (paper lines 326--332):
the expectation of `(A^u_{h(u)} · H^u_h · (A^v_{h(v)} - A^u_{h(u)})) ⊗ T_h`,
averaged over `(u, v)` and summed over `h`.

This identity is purely algebraic; the actual operator Cauchy--Schwarz step
is provided by `add_in_u_cs_chain_q3_q4_factored_cs`. -/
theorem addInU_cs_chain_step4_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          strategy.state.ev
            (strategy.state.opTensor (Au * Mh * (Av - Au)) (T.outcome h))) :=
  (avgOver_sub _ _ _).symm.trans <| avgOver_congr _ _ _ fun _ =>
    (Finset.sum_sub_distrib ..).symm.trans <| Finset.sum_congr rfl fun h _ =>
      (strategy.state.ev_sub _ _).symm.trans <| congrArg strategy.state.ev <|
        addInU_step4_pointwise_op_eq strategy.state _ _ _ (T.outcome h)

end MIPRE.LIDT.Co.SelfImprovement

end
