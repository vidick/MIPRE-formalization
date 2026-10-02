/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LdSandwichLineOnePoint/CauchySchwarz.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.CSSetup

@[expose] public section

/-!
# Section 12 pasting: line one-point transport — Cauchy–Schwarz chain

The two off-diagonal Cauchy–Schwarz moves of the line one-point transport: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CauchySchwarz.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The fact record `LdSandwichLineOnePointCSFacts` is assembled from the adjoint raw-core bound
(`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts`): the two unit-side bounds are
the completeness of the half-products, placed by `S.L` and multiplied by a right complement
between `0` and `1` (`S.opTensor_le_leftTensor`), and the four scalar identities regroup the
outcome sums through `S.leftTensor_mul_opTensor` and `S.opTensor_mul_leftTensor`, in place of the
vendored Kronecker calculations. The ported `Preliminaries.closenessOfIPAdjoint` and
`Preliminaries.closenessOfIP` then give the two absolute-value bounds on the vector state of the
strategy, without the vendored normalization argument, and the one-sided route, the expanded
bound and the linear-defect bound follow as in the vendored file. The vendored conjugate
transpose `ᴴ` is `star`. No vendored statement here carries a swap or normalization hypothesis.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple Distribution avgOver avgOver_congr
  uniformDistribution uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (GHatTupleOutcome SandwichedLineQuestion commuteGHalfSandwichError
  pointTupleLastFrontEquiv gHatTupleOutcomeLastFrontEquiv)
open MIPRE.LIDT.Co (SymModel SymStrat SubMeas IdxSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Collapse a sum over field values of selected sandwich terms against a right family:
`Σ_a ev((Σ_b [e b = a] X_b) ⊗ Y_a) = Σ_b ev(X_b ⊗ Y_{e b})`, with `Y_none = 0`. -/
private theorem sum_ev_opTensor_ite_eq {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (S : SymModel 𝔓 K) (e : β → Option α) (X : β → 𝔓) (Y : α → 𝔓) :
    ∑ a : α, S.ev (S.opTensor (∑ b : β, if e b = some a then X b else 0) (Y a)) =
      ∑ b : β, S.ev (S.opTensor (X b) (Option.elim (e b) 0 Y)) := by
  simp_rw [S.opTensor_sum_left_univ, S.ev_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hite : ∀ (p : Prop) [Decidable p] (Z W : 𝔓),
      S.ev (S.opTensor (if p then Z else 0) W) = if p then S.ev (S.opTensor Z W) else 0 := by
    intro p _ Z W
    split
    · rfl
    · rw [SymModel.opTensor, map_zero, zero_mul, VecState.ev_zero]
  rcases e b with _ | a₀
  · simp only [reduceCtorEq, ite_false, Option.elim_none, SymModel.opTensor, map_zero, zero_mul,
      mul_zero, VecState.ev_zero, Finset.sum_const_zero]
  · simp only [Option.some.injEq, hite, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl

/-- Assemble the line-one-point CS facts from the single adjoint raw-core estimate. -/
theorem ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    LdSandwichLineOnePointCSFacts params strategy family gamma zeta hi := by
  classical
  -- The right complement is between `0` and `1`.
  have hR : ∀ (q : SandwichedLineQuestion params k) (gs : GHatTupleOutcome params (i + 1)),
      0 ≤ ldSandwichLineOnePointCS_rightComplement params strategy family q gs ∧
        ldSandwichLineOnePointCS_rightComplement params strategy family q gs ≤ 1 := by
    intro q gs
    unfold ldSandwichLineOnePointCS_rightComplement
    split
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨sub_nonneg.2 (SubMeas.outcome_le_one _ _), sub_le_self _ (SubMeas.outcome_pos _ _)⟩
  -- Its two squares are at most `1`.
  have hRsq : ∀ (q : SandwichedLineQuestion params k) (gs : GHatTupleOutcome params (i + 1)),
      star (ldSandwichLineOnePointCS_rightComplement params strategy family q gs) *
          ldSandwichLineOnePointCS_rightComplement params strategy family q gs ≤ 1 ∧
        ldSandwichLineOnePointCS_rightComplement params strategy family q gs *
          star (ldSandwichLineOnePointCS_rightComplement params strategy family q gs) ≤ 1 := by
    intro q gs
    obtain ⟨h0, h1⟩ := hR q gs
    rw [(IsSelfAdjoint.of_nonneg h0).star_eq]
    exact ⟨(sq_le_self h0 h1).trans h1, (sq_le_self h0 h1).trans h1⟩
  -- The completeness of a half-product sandwich.
  have htotal : ∀ xs : PointTuple params (i + 1),
      ∑ gs : GHatTupleOutcome params (i + 1),
        gHatHalfProductOutcomeOperator params family (i + 1) xs gs *
          star (gHatHalfProductOutcomeOperator params family (i + 1) xs gs) = 1 := fun xs => by
    refine (gHatSandwichFamily params family (i + 1) xs).sum_eq_total.trans ?_
    show gHatHalfProductTotalOperator params family (i + 1) xs *
      star (gHatHalfProductTotalOperator params family (i + 1) xs) = 1
    rw [gHatHalfProductTotalOperator_eq_one, star_one, mul_one]
  have hsumOrd : ∀ q : SandwichedLineQuestion params k,
      ∑ gs : GHatTupleOutcome params (i + 1),
        ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
          star (ldSandwichLineOnePointCS_orderedHalf params family hi q gs) = 1 :=
    fun q => htotal _
  have hsumRot : ∀ q : SandwichedLineQuestion params k,
      ∑ gs : GHatTupleOutcome params (i + 1),
        ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
          star (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs) = 1 :=
    fun q => (Equiv.sum_comp (gHatTupleOutcomeLastFrontEquiv params i) _).trans (htotal _)
  -- The right complement as an `Option.elim`.
  have hRc : ∀ (q : SandwichedLineQuestion params k) (gs : GHatTupleOutcome params (i + 1)),
      ldSandwichLineOnePointCS_rightComplement params strategy family q gs =
        Option.elim (Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
            (gs ⟨i, Nat.lt_succ_self i⟩)) 0
          (fun a => 1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a)) := by
    intro q gs
    unfold ldSandwichLineOnePointCS_rightComplement
    cases Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩) <;> rfl
  -- The intermediate outcome sum, with the right complement.
  have hafter : ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
        ∑ gs : GHatTupleOutcome params (i + 1),
          strategy.state.ev (strategy.state.opTensor
            (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
              star (ldSandwichLineOnePointCS_orderedHalf params family hi q gs))
            (ldSandwichLineOnePointCS_rightComplement params strategy family q gs))) := by
    refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun gs _ => ?_
    rw [hRc]
    cases Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩) with
    | none =>
        rw [Option.elim_none, SymModel.opTensor, map_zero, mul_zero, VecState.ev_zero]
    | some a => rfl
  refine ⟨
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
      params strategy family gamma zeta hi hi0 facts,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    calc
      ∑ gs : GHatTupleOutcome params (i + 1),
          star (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) *
            (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)
          ≤ ∑ gs : GHatTupleOutcome params (i + 1),
              strategy.state.L (ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                star (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)) :=
            Finset.sum_le_sum fun gs _ => by
              rw [Fintype.sum_unique, ldSandwichLineOnePointCS_Cfirst,
                SymModel.conjTranspose_opTensor, star_star, SymModel.opTensor_mul]
              exact strategy.state.opTensor_le_leftTensor (mul_star_self_nonneg _) (hRsq q gs).1
      _ = 1 := by rw [strategy.state.leftTensor_finset_sum, hsumOrd, SymModel.leftTensor_one]
  · intro q
    calc
      ∑ gs : GHatTupleOutcome params (i + 1),
          (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
            star (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)
          ≤ ∑ gs : GHatTupleOutcome params (i + 1),
              strategy.state.L (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                star (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)) :=
            Finset.sum_le_sum fun gs _ => by
              rw [Fintype.sum_unique, ldSandwichLineOnePointCS_Csecond,
                SymModel.conjTranspose_opTensor, SymModel.opTensor_mul]
              exact strategy.state.opTensor_le_leftTensor (mul_star_self_nonneg _) (hRsq q gs).2
      _ = 1 := by rw [strategy.state.leftTensor_finset_sum, hsumRot, SymModel.leftTensor_one]
  · refine avgOver_congr _ _ _ fun q => ?_
    simp only [ldSandwichLineOnePointPrefixOriginalFamily_outcome_some]
    rw [sum_ev_opTensor_ite_eq]
    refine Finset.sum_congr rfl fun gs _ => ?_
    rw [Fintype.sum_unique, ← hRc]
    exact congrArg strategy.state.ev (strategy.state.leftTensor_mul_opTensor _ _ _).symm
  · rw [hafter]
    refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun gs _ => ?_
    rw [Fintype.sum_unique]
    exact congrArg strategy.state.ev (strategy.state.leftTensor_mul_opTensor _ _ _).symm
  · rw [hafter]
    refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun gs _ => ?_
    rw [Fintype.sum_unique]
    refine congrArg strategy.state.ev ?_
    rw [ldSandwichLineOnePointCS_Csecond, ldSandwichLineOnePointCS_Aord,
      strategy.state.leftTensor_conjTranspose, strategy.state.opTensor_mul_leftTensor]
  · refine avgOver_congr _ _ _ fun q => ?_
    simp only [ldSandwichLineOnePointPrefixMovedFamily_outcome_some]
    rw [sum_ev_opTensor_ite_eq, ← Equiv.sum_comp (gHatTupleOutcomeLastFrontEquiv params i)]
    refine Finset.sum_congr rfl fun gs _ => ?_
    rw [Fintype.sum_unique]
    calc
      _ = strategy.state.ev (strategy.state.opTensor
            (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
              star (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs))
            (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) := by
          rw [hRc]
          rfl
      _ = _ := by
          rw [ldSandwichLineOnePointCS_Csecond, ldSandwichLineOnePointCS_Arot,
            strategy.state.leftTensor_conjTranspose, strategy.state.opTensor_mul_leftTensor]

/-- Narrow analytic endpoint for the two off-diagonal Cauchy--Schwarz moves in their
absolute-value `closenessOfIP` output shape.

The generic applications of `Preliminaries.closenessOfIPAdjoint` and
`Preliminaries.closenessOfIP` are proved here, on the vector state of the strategy.  The CS facts
record proves the measurement-completeness/unit bounds and scalar regrouping equalities; the
remaining nontrivial estimate is the adjoint raw-core orientation lemma
`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore`. -/
theorem ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    LdSandwichLineOnePointOutcomeSumCSAbsBounds params strategy family gamma zeta hi := by
  have h𝒟 := uniformDistribution_weight_sum_le_one (SandwichedLineQuestion params k)
  have csFacts :=
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts
      params strategy family gamma zeta hi hi0 facts
  refine ⟨?_, ?_⟩
  · rw [csFacts.source_eq_firstSourceRaw, csFacts.afterFirst_eq_firstTargetRaw]
    exact Preliminaries.closenessOfIPAdjoint strategy.state.toVecState _ h𝒟
      (ldSandwichLineOnePointCS_Aord strategy.state params family hi)
      (ldSandwichLineOnePointCS_Arot strategy.state params family hi)
      (ldSandwichLineOnePointCS_Cfirst params strategy family hi)
      (commuteGHalfSandwichError params gamma zeta (i + 1))
      csFacts.adjointRawCore csFacts.firstUnitBound
  · rw [csFacts.afterFirst_eq_secondSourceRaw, csFacts.moved_eq_secondTargetRaw]
    exact Preliminaries.closenessOfIP strategy.state.toVecState _ h𝒟
      (fun q gs => star (ldSandwichLineOnePointCS_Aord strategy.state params family hi q gs))
      (fun q gs => star (ldSandwichLineOnePointCS_Arot strategy.state params family hi q gs))
      (ldSandwichLineOnePointCS_Csecond params strategy family hi)
      (commuteGHalfSandwichError params gamma zeta (i + 1))
      csFacts.adjointRawCore csFacts.secondUnitBound

/-- One-sided route for the two off-diagonal Cauchy--Schwarz moves in
`ld-pasting.tex:964--1010`.

The substantive analytic residual is the pair of absolute-value estimates
`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds`; this lemma
only converts those two `closenessOfIP`-style bounds into the one-sided
inequalities consumed by the downstream scalar transport. -/
theorem ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    LdSandwichLineOnePointOutcomeSumCSRoute params strategy family gamma zeta hi := by
  have hbounds :=
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds
      params strategy family gamma zeta hi hi0 facts
  exact ⟨by linarith [le_abs_self (ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy
      family hi - ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi),
      hbounds.firstAbs],
    by linarith [le_abs_self (ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy
      family hi - ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi),
      hbounds.secondAbs]⟩

/-- The remaining expanded off-diagonal scalar transport in
`lem:ld-sandwich-line-one-point`.

This is the exact scalar form of `ld-pasting.tex:954--1024` after the linear
consistency defect has been expanded as
`Σ_a ev(A_a ⊗ (I − B_a))`.  The only remaining analytic content is the
paper's two averaged Cauchy--Schwarz moves plus the prefix-completeness collapse;
the surrounding `qBipartiteLinearConsDefect` bookkeeping is proved in
`ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound`. -/
theorem ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      ∑ a : Fq params,
        strategy.state.ev
          (strategy.state.opTensor
            (((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q).outcome
              (some a))
            (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
              (some a))))
      ≤
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      ∑ a : Fq params,
        strategy.state.ev
          (strategy.state.opTensor
            (((ldSandwichLineOnePointPrefixMovedFamily params family hi) q).outcome
              (some a))
            (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
              (some a)))) +
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  have hroute :=
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route
      params strategy family gamma zeta hi hi0 facts
  have htwo := add_le_add hroute.firstCauchySchwarz hroute.secondCauchySchwarz
  change ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  linarith

/-- Linear-defect reduction for the expanded off-diagonal post-deletion transport in
`lem:ld-sandwich-line-one-point`.

The paper's two Cauchy--Schwarz moves and prefix collapse from
`references/ldt-paper/ld-pasting.tex:954--1024` act on the expanded scalar
expression `Σ_a ev(A_a ⊗ (I − B_a))`.  This lemma proves the exact
bookkeeping reduction from the averaged linear consistency defects to that
expanded residual, using the measurement-valued right family and the fact that
both option-valued families have zero `none` mass.  The remaining analytic gap is
therefore the split Cauchy--Schwarz route
`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route`; the arithmetic
absorption into `ν₅` is proved separately in
`ldSandwichLineOnePoint_endpoint_comm_error_le`. -/
theorem ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      qBipartiteLinearConsDefect strategy.state
        ((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q)
        ((ldSandwichLineOnePointRightFamily params strategy family k i) q))
      ≤
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      qBipartiteLinearConsDefect strategy.state
        ((ldSandwichLineOnePointPrefixMovedFamily params family hi) q)
        ((ldSandwichLineOnePointRightFamily params strategy family k i) q)) +
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  rw [avgOver_congr _ _ _ fun q => qBipartiteLinearConsDefect_option_eq_sum_some_complement
      strategy.state _ _
      (ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi q)
      (ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero params family hi q)
      (ldSandwichLineOnePointRightFamily_outcome_none_eq_zero params strategy family hi q),
    avgOver_congr _ _ _ fun q => qBipartiteLinearConsDefect_option_eq_sum_some_complement
      strategy.state _ _
      (ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi q)
      (ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero params family hi q)
      (ldSandwichLineOnePointRightFamily_outcome_none_eq_zero params strategy family hi q)]
  exact ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_bound
    params strategy family gamma zeta hi hi0 facts

end MIPRE.LIDT.Co.Pasting

end
