/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz
public import MIPRE.Background.LIDT.Co.Preliminaries.Triangles.SimEq
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichMain.Completeness
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.Extensions

@[expose] public section

/-!
# Self-consistency: data processing

`prop:self-consistency-implies-data-processing`: self-consistency implies that postprocessing a
measurement cannot substantially decrease consistency. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

Both statements take a symmetric model `S : SymModel 𝔓 K` in place of the state
`ψ : QuantumState (ι × ι)`, as an explicit first argument, with the local families `A` and `P`
in `𝔓` lifted by `IdxSubMeas.liftLeft S` and `IdxSubMeas.liftRight S`. The vendored hypotheses
`hperm : PermInvState ψ` and `hψ : ψ.IsNormalized` are dropped: swap symmetry is the model's
`S.ev_L_eq_ev_R` (which replaces the vendored `hperm.swap_ev`) and enters also through
`twoNotionsOfSelfConsistencyAfterEvaluation`; normalization is not used. The subprobability
hypothesis `h𝒟` stays.

The proof of `wrongSideEstimate` is the vendored one, organised question by question: the
squared distance between `P_[f_q] ⊗ I` and `I ⊗ A_[f_q]` expands, outcome by outcome, as
`ev(L p²) + ev(R a²) - 2 ev(L p R a)` (`ev_star_L_sub_R_mul_self`, in
`SwitchSandwichMain/RightTransfer.lean`), the diagonal
terms are at most the masses (`subMeas_diagMass_le_mass`) and the cross term at least that of
the unprocessed families (`qMatchMass_leftRight_postprocess_ge`). The average is then bounded
through `avgOver_sub`, `avgOver_add` and `avgOver_const_mul`, in place of the vendored unfolding
of `avgOver` into finite sums.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_mono avgOver_add avgOver_sub avgOver_const_mul)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `prop:self-consistency-implies-data-processing`, the wrong-side estimate
`P_[f_q] ⊗ I ≈_{2δ + 4√ε} I ⊗ A_[f_q]`.

Proof:
1. expand the `qSDD` square, outcome by outcome, and bound the diagonal terms by the masses;
2. bound the mass of `P` by `completenessTransferProjectiveP`;
3. bound the postprocessed cross term below by the unprocessed one
   (`qMatchMass_leftRight_postprocess_ge`), and compare that with the diagonal overlap of `A`
   (`easyApproxFromApproxDelta`);
4. bound the gap between the mass of `A` and its diagonal overlap by bipartite SSC.

The vendored lemma asks for a permutation-invariant, normalized state. -/
theorem wrongSideEstimate
    {Question α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α 𝔓)
    (P : IdxProjSubMeas Question α 𝔓)
    (δ ε : ℝ) (f : Question → α → β) :
    S.BipartiteSSCRel 𝒟 A δ →
    S.SDDRel 𝒟
      (IdxSubMeas.liftLeft S (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft S A) ε →
      S.SDDRel 𝒟
        (IdxSubMeas.liftLeft S (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftRight S (fun q => postprocess (A q) (f q)))
        (2 * δ + 4 * Real.sqrt ε) := by
  intro ⟨hssc⟩ hsdd
  -- The squared distance of a left and a right lift, bounded by masses and the cross term.
  have hgen : ∀ X Y : SubMeas β 𝔓,
      S.qSDD (X.liftLeft S) (Y.liftRight S) ≤
        S.ev (S.L X.total) + S.ev (S.R Y.total) -
          2 * ∑ b, S.ev (S.L (X.outcome b) * S.R (Y.outcome b)) := by
    intro X Y
    have hx : ∑ b, S.ev (S.L (X.outcome b) * S.L (X.outcome b)) ≤ S.ev (S.L X.total) :=
      subMeas_diagMass_le_mass S.toVecState (X.liftLeft S)
    have hy : ∑ b, S.ev (S.R (Y.outcome b) * S.R (Y.outcome b)) ≤ S.ev (S.R Y.total) :=
      subMeas_diagMass_le_mass S.toVecState (Y.liftRight S)
    simp only [S.leftTensor_mul_leftTensor, S.rightTensor_mul_rightTensor] at hx hy
    show ∑ b, S.ev (star (S.L (X.outcome b) - S.R (Y.outcome b)) *
      (S.L (X.outcome b) - S.R (Y.outcome b))) ≤ _
    rw [Finset.sum_congr rfl fun b _ => ev_star_L_sub_R_mul_self S (.of_nonneg (X.outcome_pos b))
      (.of_nonneg (Y.outcome_pos b)), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    linarith
  have hpt : ∀ q, S.qSDD
      ((postprocess ((P q).toSubMeas) (f q)).liftLeft S)
      ((postprocess (A q) (f q)).liftRight S) ≤
        S.ev (S.L (P q).total) + S.ev (S.L (A q).total) -
          2 * ∑ a, S.ev (S.L ((P q).outcome a) * S.R ((A q).outcome a)) := by
    intro q
    have h := hgen (postprocess ((P q).toSubMeas) (f q)) (postprocess (A q) (f q))
    have hz : ∑ a, S.ev (S.L ((P q).outcome a) * S.R ((A q).outcome a)) ≤
        ∑ b, S.ev (S.L ((postprocess ((P q).toSubMeas) (f q)).outcome b) *
          S.R ((postprocess (A q) (f q)).outcome b)) :=
      qMatchMass_leftRight_postprocess_ge S (P q).toSubMeas (A q) (f q)
    have hLR : S.ev (S.R (postprocess (A q) (f q)).total) = S.ev (S.L (A q).total) :=
      (S.ev_L_eq_ev_R (A q).total).symm
    have hP : S.ev (S.L (postprocess ((P q).toSubMeas) (f q)).total) = S.ev (S.L (P q).total) :=
      rfl
    linarith
  -- Step 2: the mass of `P` is at most that of `A` plus `2√ε`.
  have hmassP : avgOver 𝒟 (fun q => S.ev (S.L (A q).total)) ≥
      avgOver 𝒟 (fun q => S.ev (S.L (P q).total)) - 2 * Real.sqrt ε :=
    (completenessTransferProjectiveP S.toVecState 𝒟 h𝒟 (IdxSubMeas.liftLeft S A)
      (fun q => (P q).liftLeft S) ε
      (sddRel_symm S.toVecState 𝒟
        (IdxSubMeas.liftLeft S (IdxProjSubMeas.toIdxSubMeas P))
        (IdxSubMeas.liftLeft S A) ε hsdd)).completenessTransfer
  -- Step 3: the unprocessed cross term is `√ε`-close to the diagonal overlap of `A`.
  have hcross : |avgOver 𝒟 (fun q => ∑ a, S.ev (S.L ((P q).outcome a) * S.R ((A q).outcome a))) -
      avgOver 𝒟 (fun q => ∑ a, S.ev (S.L ((A q).outcome a) * S.R ((A q).outcome a)))| ≤
        Real.sqrt ε :=
    easyApproxFromApproxDelta S.toVecState 𝒟 h𝒟
      (IdxSubMeas.liftLeft S (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft S A) (IdxSubMeas.liftRight S A) ε hsdd
  -- Step 4: bipartite SSC bounds the mass of `A` against its diagonal overlap.
  have hgap : avgOver 𝒟 (fun q => S.ev (S.L (A q).total)) -
      avgOver 𝒟 (fun q => ∑ a, S.ev (S.L ((A q).outcome a) * S.R ((A q).outcome a))) ≤ δ := by
    rw [← avgOver_sub]
    exact (avgOver_mono 𝒟 _ (fun q => S.qBipartiteSSCDefect (A q))
      fun q => le_max_right _ _).trans hssc
  constructor
  calc
    S.sddError 𝒟 _ _
      ≤ avgOver 𝒟 (fun q => S.ev (S.L (P q).total) + S.ev (S.L (A q).total) -
          2 * ∑ a, S.ev (S.L ((P q).outcome a) * S.R ((A q).outcome a))) :=
        avgOver_mono 𝒟 _ _ hpt
    _ = avgOver 𝒟 (fun q => S.ev (S.L (P q).total)) +
          avgOver 𝒟 (fun q => S.ev (S.L (A q).total)) -
          2 * avgOver 𝒟
            (fun q => ∑ a, S.ev (S.L ((P q).outcome a) * S.R ((A q).outcome a))) := by
        rw [avgOver_sub, avgOver_add, avgOver_const_mul]
    _ ≤ 2 * δ + 4 * Real.sqrt ε := by
        linarith [(abs_le.mp hcross).1]

/-- `prop:self-consistency-implies-data-processing`.

A projective approximation to a strongly self-consistent family remains close after
postprocessing on the left register. The proof combines the wrong-side estimate,
self-consistency after evaluation, and the `SDDRel` triangle inequality. The vendored lemma
asks for a permutation-invariant, normalized state. -/
theorem selfConsistencyImpliesDataProcessing
    {Question α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α 𝔓)
    (P : IdxProjSubMeas Question α 𝔓)
    (δ ε : ℝ) (f : Question → α → β) :
    S.BipartiteSSCRel 𝒟 A δ →
    S.SDDRel 𝒟
      (IdxSubMeas.liftLeft S (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft S A) ε →
      S.SDDRel 𝒟
        (IdxSubMeas.liftLeft S (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftLeft S (fun q => postprocess (A q) (f q)))
        (8 * δ + 8 * Real.sqrt ε) := fun hssc hsdd =>
  stateDependentDistanceRel_mono S.toVecState 𝒟 _ _
    (2 * ((2 * δ + 4 * Real.sqrt ε) + 2 * δ)) _ (by linarith)
    (stateDependentDistanceRel_triangle S.toVecState 𝒟
      (IdxSubMeas.liftLeft S (fun q => postprocess ((P q).toSubMeas) (f q)))
      (IdxSubMeas.liftRight S (fun q => postprocess (A q) (f q)))
      (IdxSubMeas.liftLeft S (fun q => postprocess (A q) (f q)))
      _ _
      (wrongSideEstimate S 𝒟 h𝒟 A P δ ε f hssc hsdd)
      (sddRel_symm S.toVecState 𝒟 _ _ _
        (twoNotionsOfSelfConsistencyAfterEvaluation S 𝒟 A δ f hssc)))

end MIPRE.LIDT.Co.Preliminaries

end
