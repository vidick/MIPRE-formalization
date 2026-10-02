/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooCompletion.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion.CompletePart
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion.Utilities
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion.FourthTermChain

@[expose] public section

/-!
# Section 12 pasting: switcheroo completion bounds

Completion and first-stage switcheroo error bounds, `lem:commutativity-switcheroo`: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean` in the port
of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position, and a strategy is a
`SymStrat params.next 𝔓 K`; the slice family is an `IdxPolyFamily params 𝔓` and the auxiliary
family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`. The vendored hypotheses
`hnorm : ψbi.IsNormalized` and `hfix : swapDensity ψbi.density = ψbi.density` are dropped, both
being theorems of the model (section "Swap symmetry is a theorem"): callers pass
`switcherooCompletePartCenter_eq_target params S family M` and
`commutativitySwitcheroo_ofCompleteSelfConsistency params S family M zeta omega chi hselfG hselfM
hcomm`. `commutativitySwitcheroo` no longer reads `strategy.permInvState`, `strategy.isNormalized`
or `strategy.densityFixed`.

The swap of the two centres is `S.ev_opTensor_swap_of_density_fixed`, which needs no hypothesis.
The assembly compares the four terms of the expansion with the one centre `G ⊗ M`: the first by
the switch sandwich on `M`, the second by the switch sandwich on the complete part followed by the
centre swap, and the third and fourth through the fourth-term chain of
`Co/Pasting/SwitcherooCompletion/FourthTermChain.lean`. The arithmetic is one `linarith` on the
unfolded absolute-value bounds, in place of the vendored `nlinarith` steps; it proves the
displayed `6√ζ + 6√ω + 4√χ` from the sharper `6√ζ + 2√ω + 4√χ`.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion commutativitySwitcherooError)
open MIPRE.LIDT.Co (SymModel SymStrat IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The complete-part `M ⊗ G` centre equals the `G ⊗ M` switcheroo target. -/
theorem switcherooCompletePartCenter_eq_target
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
      Preliminaries.middleSandwichExpectation S
        (uniformDistribution (SliceQuestion params))
        (completePartProjFamily params family) (((M y).toSubMeas).total)) =
      switcherooAggregateTarget params S family M :=
  (switcherooAggregateMGCenterComplete_eq_opTensor_avg params S family M).trans <|
    (avgOver_congr _ _ _ fun _ => S.ev_opTensor_swap_of_density_fixed _ _).trans
      (switcherooAggregateTarget_eq_opTensor_avg params S family M).symm

/-- Internal form of `lem:commutativity-switcheroo` after applying
`lem:g-complete-self-consistency`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:560-706` uses
the complete-part self-consistency conclusion internally.  The paper-facing
theorem `commutativitySwitcheroo` below derives it from the source strong
self-consistency hypothesis rather than exposing it as a public hypothesis. -/
theorem commutativitySwitcheroo_ofCompleteSelfConsistency
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta omega chi : ℝ)
    (hselfG : GCompleteSelfConsistencyStatement params S family zeta)
    (hselfM : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft S params M)
      (switcherooSelfConsistencyRight S params M)
      omega)
    (hcomm : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft S params family M)
      (switcherooPointProductRight S params family M)
      chi) :
    CommutativitySwitcherooStatement params S family M zeta omega chi := by
  /-
  Paper reference: `lem:commutativity-switcheroo` in `references/ldt-paper/ld-pasting.tex`.
  The four terms of the `qSDDOp` expansion are compared with the `G ⊗ M` centre; the second
  term's natural centre `M ⊗ G` equals it by the swap symmetry of the model.
  -/
  refine ⟨⟨?_⟩⟩
  -- The first term against the `G ⊗ M` centre, by the switch sandwich on `M`.
  have hfirst : |switcherooAggregateFirstTerm params S family M -
      switcherooAggregateTarget params S family M| ≤ 2 * Real.sqrt omega := by
    rw [switcherooAggregateFirstTerm_eq_leftSandwich, switcherooAggregateTarget_eq_middleSandwich]
    exact switcheroo_first_term_close params S family M omega hselfM
  -- The second term against the same centre, through the complete-part centre.
  have hsecond : |switcherooAggregateSecondTerm params S family M -
      switcherooAggregateTarget params S family M| ≤ 2 * Real.sqrt zeta := by
    rw [← switcherooCompletePartCenter_eq_target params S family M]
    exact switcheroo_second_aggregate_term_close params S family M zeta hselfG
  -- The fourth-term chain.
  have hstep1 := switcherooAggregateFourthTerm_close_once_commuted_scalar params S family M chi hcomm
  have hstep2 := switcherooAggregateOnceCommutedScalar_close_mixed params S family M zeta hselfG
  have hstep3 := switcherooAggregateMixedScalar_close_leftFrontScalar params S family M zeta hselfG
  have hstep4 :=
    switcherooAggregateLeftFrontScalar_close_firstSplitScalar params S family M chi hcomm
  have hstep5 : switcherooAggregateFirstSplitScalar params S family M =
      switcherooAggregateFirstTerm params S family M := by
    rw [← switcherooAggregateFirstTerm_eq_split_by_g]
    refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun go _ => ?_
    rw [mul_assoc]
  have hsqrt : ∀ x : ℝ, Real.rpow x (1 / 2) = Real.sqrt x := fun x =>
    (Real.sqrt_eq_rpow x).symm
  refine (le_of_eq (switcherooAggregate_qSDDOp_expand_avg params S family M)).trans ?_
  rw [switcherooAggregateThirdTerm_eq_fourthTerm, commutativitySwitcherooError, hsqrt, hsqrt,
    hsqrt]
  have := Real.sqrt_nonneg omega
  rw [abs_le] at hfirst hsecond hstep1 hstep2 hstep3 hstep4
  linarith [hfirst.1, hfirst.2, hsecond.1, hsecond.2, hstep1.1, hstep1.2, hstep2.1, hstep2.2,
    hstep3.1, hstep3.2, hstep4.1, hstep4.2]

/-- `lem:commutativity-switcheroo`, source-facing form. -/
theorem commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (zeta omega chi : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hselfM : strategy.state.SDDRel
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft strategy.state params M)
      (switcherooSelfConsistencyRight strategy.state params M)
      omega)
    (hcomm : strategy.state.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft strategy.state params family M)
      (switcherooPointProductRight strategy.state params family M)
      chi) :
    CommutativitySwitcherooStatement params strategy.state family M zeta omega chi :=
  commutativitySwitcheroo_ofCompleteSelfConsistency params strategy.state family M zeta omega chi
    (gCompleteSelfConsistency params strategy.state family zeta hself) hselfM hcomm

end MIPRE.LIDT.Co.Pasting

end
