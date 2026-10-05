/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/Common.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.GHatFacts
public import MIPRE.Background.LIDT.Co.Pasting.Core.CompletePart
public import MIPRE.Background.LIDT.Co.Pasting.Sandwich.PastedFamilies
public import MIPStarRE.LDT.Basic.LowDegreePolynomial
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.Common

@[expose] public section

/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution and boundedness helpers for the Section 12
comparison lemmas: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/Common.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The postprocessing lemmas read no state and hold over any ordered `⋆`-ring, as
`hRestrictionToVerticalLine` of `Co/Pasting/Sandwich/PastedFamilies.lean` does, so they serve `𝔓`
and `K →L[ℂ] K` alike. The bipartite lemmas take the symmetric model `S : SymModel 𝔓 K` as
their first explicit argument, in place of the vendored `ψ : QuantumState (ι × ι)`, and keep
this file's namespace so that their vendored names pair. The vendored normalization hypothesis
`hnorm : ψ.IsNormalized` of the four `_le_one` lemmas is dropped (section "Swap symmetry is a
theorem": `S.ev_one_of_isNormalized` takes no hypothesis), so callers pass `S` and the
submeasurements only. Their proofs are the keystone's `S.qBipartiteMatchMass_nonneg`,
`S.qBipartiteConsDefect_le_one_of_isNormalized` and `S.bipartiteConsError_uniform_le_one` of
`Co/Test/Defs.lean`.

## Not ported

- `sqrt_min_le_rpow32`: classical, imported.
- `hAConsistency_sqrt_bound_of_pos`: classical, imported.
- `hAConsistency_error_le_nu_of_pos`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point AxisParallelLine appendPoint truncatePoint
  pointHeight zeroCoord lastCoord avgOver avgOver_uniform_fst avgOver_uniform_le_const
  uniformDistribution)
open MIPStarRE.LDT.Pasting (verticalLine_pointAt_appendPoint)
open MIPRE.LIDT.Co (SymModel SubMeas IdxSubMeas postprocess evaluateAt)

section Generic

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- Postprocessing by `f` and then by `g` is postprocessing by `g ∘ f`. -/
theorem postprocess_postprocess
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α R) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (g ∘ f) :=
  SubMeas.postprocess_comp A f g

/-- Reading the restriction of `H` to the vertical line through `truncatePoint u` at the height
of `u` is evaluating `H` at `u`. -/
theorem postprocess_hRestrictionToVerticalLine_eq_evaluateAt
    (params : Parameters) [FieldModel params.q]
    (H : SubMeas (MIPStarRE.LDT.Polynomial params.next) R) (u : Point params.next) :
    postprocess
      (hRestrictionToVerticalLine params H (truncatePoint params u))
      (fun f => f (pointHeight params u)) =
    evaluateAt params.next u H := by
  refine (SubMeas.postprocess_comp _ _ _).trans
    (congrArg (postprocess H) (funext fun h => ?_))
  refine (MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply params.next h _
    (pointHeight params u)).trans (congrArg h ?_)
  exact (verticalLine_pointAt_appendPoint params (truncatePoint params u)
    (pointHeight params u)).trans
    ((MIPStarRE.LDT.CommutativityPoints.pointNextEquiv params).left_inv u)

end Generic

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A consistency relation over uniform questions `a` persists when an unused uniform
coordinate `b` is adjoined to the question. -/
theorem consRel_uniform_fst
    {α β Outcome : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A B : IdxSubMeas α Outcome 𝔓) (δ : ℝ) :
    S.ConsRel (uniformDistribution α) A B δ →
      S.ConsRel (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := fun ⟨h⟩ =>
  ⟨(avgOver_uniform_fst (β := β) fun a => S.qBipartiteConsDefect (A a) (B a)).trans_le h⟩

/-- The bipartite matching mass is nonnegative. -/
theorem qBipartiteMatchMass_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A B : SubMeas Outcome 𝔓) :
    0 ≤ S.qBipartiteMatchMass A B :=
  S.qBipartiteMatchMass_nonneg A B

/-- A bipartite consistency defect is at most `1`. -/
theorem qBipartiteConsDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A B : SubMeas Outcome 𝔓) :
    S.qBipartiteConsDefect A B ≤ 1 :=
  S.qBipartiteConsDefect_le_one_of_isNormalized A B

/-- Under the uniform question distribution, the averaged bipartite consistency error is at
most `1`. -/
theorem bipartiteConsError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A B : IdxSubMeas Question Outcome 𝔓) :
    S.bipartiteConsError (uniformDistribution Question) A B ≤ 1 :=
  S.bipartiteConsError_uniform_le_one A B

/-- A bipartite strong self-consistency defect is at most `1`. -/
theorem qBipartiteSSCDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : SubMeas Outcome 𝔓) :
    S.qBipartiteSSCDefect A ≤ 1 := by
  have hoverlap_nonneg : 0 ≤ ∑ a : Outcome, S.ev (S.opTensor (A.outcome a) (A.outcome a)) :=
    Finset.sum_nonneg fun a _ =>
      S.ev_nonneg_of_psd _ (S.opTensor_nonneg (A.outcome_pos a) (A.outcome_pos a))
  have htotal_le : S.ev (S.L A.total) ≤ 1 :=
    (S.ev_mono _ _ (S.leftTensor_le_one A.total_le_one)).trans_eq S.ev_one_of_isNormalized
  exact max_le zero_le_one (by linarith)

/-- Under the uniform question distribution, the averaged bipartite strong self-consistency
error is at most `1`. -/
theorem bipartiteSSCError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓) :
    S.bipartiteSSCError (uniformDistribution Question) A ≤ 1 :=
  avgOver_uniform_le_const _ 1 fun q => qBipartiteSSCDefect_le_one S (A q)

end MIPRE.LIDT.Co.Pasting

end
