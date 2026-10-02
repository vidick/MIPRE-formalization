/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/Triangles/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Triangles.Core

@[expose] public section

/-!
# Triangle inequalities for state-dependent distance: core

The main triangle-substitution estimates for approximate measurements: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Triangles/Core.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions").

The same-space statements (`qSDD_symm`, `sddRel_symm`, `triangleInequalityForVectorsSquared`,
`subMeas_total_ev_gap_abs_le_sqrt_card_qSDD`, `right_match_gap_abs_le_sqrt_qSDD`) take a vector
state `V : VecState K` (a symmetric model is accepted through its coercion) and joint operators
in `K →L[ℂ] K`. The substitution theorems `triangleSub*` are about the bipartite relation
`S.ConsRel`, so they take the symmetric model `S : SymModel 𝔓 K` as an ordinary explicit argument
in place of the vendored state, with local families in `𝔓`, as in `Co/Preliminaries/Defs.lean`.
Every statement drops the vendored normalization hypothesis `hψ : ψ.IsNormalized`, a theorem of
the vector state (`V.ev_one_of_isNormalized`).

`triangleSub_heterogeneous` and `triangleSub_right_heterogeneous` are the vendored statements
with both tensor factors fixed to `𝔓` (the vendored ones allow two carriers `ιA`, `ιB`); in the
symmetric model the placements `IdxSubMeas.placeLeft S`, `IdxSubMeas.placeRight S` are the lifts
`IdxSubMeas.liftLeft S`, `IdxSubMeas.liftRight S` by `rfl`
(`Co/Basic/SubMeasurementFamilies.lean`), so they are the same-space theorems. Their vendored
callers, on the two-space `ProjStrat` of `Test/MainTheorem/SourceRoleRegister`, are left to M13
and M14 (`planning/c6b-plan.md`, "Same-space and bipartite quantities").

The vendored file proves each of its four substitution theorems in full, with the same
pointwise estimate on `max 0 (total - match)` and the same averaging. Here that argument is
proved once, as `consRel_of_matchGap`, and each theorem supplies the match-mass gap (by
`question_easyApproxFromApproxDelta` of `Co/Preliminaries/CauchySchwarz.lean` on the left, by
`right_match_gap_abs_le_sqrt_qSDD` on the right) and the change of the total overlap (zero for
measurements). `triangleSub_right` is `triangleSub_right_subMeas_total_le`, the totals of
measurements being the identity.

## New here

- `consRel_of_matchGap`: the common substitution step. If `S.ConsRel 𝒟 A B δ`, the
  matching masses of `(A, B)` and `(A', B')` differ by at most `√(s q)` at each question, with
  `𝔼 s ≤ ε`, and the total overlap of `(A', B')` exceeds that of `(A, B)` by at most `e q`, with
  `𝔼 e ≤ η`, then `S.ConsRel 𝒟 A' B' (δ + √ε + η)`.

## Not ported

- `max_zero_add_le`: classical, imported.
- `avgOver_abs_le_sqrt_of_pointwise_nonneg`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_mono avgOver_add avgOver_zero)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise_nonneg)

section VecState

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Symmetry of the question-level state-dependent distance. -/
theorem qSDD_symm
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B : SubMeas Outcome (K →L[ℂ] K)) :
    V.qSDD A B = V.qSDD B A :=
  Finset.sum_congr rfl fun a _ => by
    rw [← neg_sub (B.outcome a), star_neg, neg_mul_neg]

/-- Symmetry of the state-dependent distance relation. -/
theorem sddRel_symm
    {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    V.SDDRel 𝒟 A B δ →
      V.SDDRel 𝒟 B A δ :=
  fun ⟨h⟩ => ⟨by simpa only [VecState.sddError, qSDD_symm V (B _)] using h⟩

/-- `prop:triangle-inequality-for-vectors-squared`.

For a finite family of operators `Dᵢ`, the squared norm of the summed vector
`(∑ᵢ Dᵢ) ψ` is controlled by the cardinality times the sum of the squared norms
of the individual vectors `Dᵢ ψ`. -/
theorem triangleInequalityForVectorsSquared
    {κ : Type*} [Fintype κ]
    (V : VecState K) (D : κ → K →L[ℂ] K) :
    V.ev (star (∑ i, D i) * (∑ i, D i)) ≤
      (Fintype.card κ : ℝ) * ∑ i, V.ev (star (D i) * D i) :=
  V.ev_sum_conjTranspose_mul_sum_le D

/-- The expectation of the difference of two submeasurement totals is controlled
by the state-dependent distance between the two outcome families, with the
finite-outcome Cauchy--Schwarz loss.

This is the total-operator analogue of the matching-mass estimates used in
`triangleSub`.  It is useful precisely when the right-register families are
submeasurements rather than measurements, so that their total operators need
not be the identity. -/
theorem subMeas_total_ev_gap_abs_le_sqrt_card_qSDD
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B : SubMeas Outcome (K →L[ℂ] K)) :
    |V.ev A.total - V.ev B.total| ≤
      Real.sqrt (Fintype.card Outcome : ℝ) * Real.sqrt (V.qSDD A B) := by
  set D : Outcome → K →L[ℂ] K := fun a => A.outcome a - B.outcome a
  have hev : V.ev A.total - V.ev B.total = V.ev (1 * ∑ a, D a) := by
    rw [one_mul, ← V.ev_sub, ← A.sum_eq_total, ← B.sum_eq_total, ← Finset.sum_sub_distrib]
  rw [hev, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  calc |V.ev (1 * ∑ a, D a)|
      ≤ Real.sqrt (V.ev (1 * star 1)) * Real.sqrt (V.ev (star (∑ a, D a) * ∑ a, D a)) :=
        V.ev_abs_mul_le_sqrt 1 _
    _ ≤ Real.sqrt ((Fintype.card Outcome : ℝ) * V.qSDD A B) := by
        rw [star_one, one_mul, V.ev_one_of_isNormalized, Real.sqrt_one, one_mul]
        exact Real.sqrt_le_sqrt (V.ev_sum_conjTranspose_mul_sum_le D)

/-- Right-register matching gap: `|∑_a ev (A_a B_a) - ∑_a ev (A_a D_a)| ≤ √(qSDD B D)` for
submeasurements `A`, `B`, `D`. -/
theorem right_match_gap_abs_le_sqrt_qSDD
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B D : SubMeas Outcome (K →L[ℂ] K)) :
    |(∑ a : Outcome, V.ev (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, V.ev (A.outcome a * D.outcome a)| ≤
      Real.sqrt (V.qSDD B D) := by
  simpa only [V.ev_mul_comm_of_psd _ _ (A.outcome_pos _) (B.outcome_pos _),
    V.ev_mul_comm_of_psd _ _ (A.outcome_pos _) (D.outcome_pos _)] using
    question_easyApproxFromApproxDelta V B D A

end VecState

section Model

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The common substitution step of the `triangleSub` family. If `S.ConsRel 𝒟 A B δ`, the
matching masses of `(A, B)` and `(A', B')` differ by at most `√(s q)` at each question, and the
total overlap of `(A', B')` exceeds that of `(A, B)` by at most `e q`, then
`S.ConsRel 𝒟 A' B' (δ + √ε + η)` for `𝔼 s ≤ ε` and `𝔼 e ≤ η`. -/
theorem consRel_of_matchGap
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B A' B' : IdxSubMeas Question Outcome 𝔓) (s e : Question → ℝ) (δ ε η : ℝ)
    (hAB : S.ConsRel 𝒟 A B δ)
    (hgap : ∀ q, |S.qBipartiteMatchMass (A q) (B q) - S.qBipartiteMatchMass (A' q) (B' q)| ≤
      Real.sqrt (s q))
    (hs : ∀ q, 0 ≤ s q) (hsε : avgOver 𝒟 s ≤ ε)
    (he : ∀ q, max 0 (S.ev (S.opTensor (A' q).total (B' q).total) -
      S.ev (S.opTensor (A q).total (B q).total)) ≤ e q)
    (heη : avgOver 𝒟 e ≤ η) :
    S.ConsRel 𝒟 A' B' (δ + Real.sqrt ε + η) := by
  set gap : Question → ℝ := fun q =>
    S.qBipartiteMatchMass (A q) (B q) - S.qBipartiteMatchMass (A' q) (B' q)
  have hpt : ∀ q, S.qBipartiteConsDefect (A' q) (B' q) ≤
      S.qBipartiteConsDefect (A q) (B q) + |gap q| + e q := fun q => by
    have he' := he q
    show max 0 (_ - _) ≤ max 0 (_ - _) + _ + _
    exact max_le (add_nonneg (add_nonneg (le_max_left _ _) (abs_nonneg _))
      ((le_max_left _ _).trans he'))
      (by linarith [le_max_right 0 (S.ev (S.opTensor (A q).total (B q).total) -
        S.qBipartiteMatchMass (A q) (B q)), le_abs_self (gap q), (le_max_right _ _).trans he'])
  refine ⟨(avgOver_mono 𝒟 _ _ hpt).trans ?_⟩
  rw [avgOver_add, avgOver_add]
  exact add_le_add (add_le_add hAB.offDiagonalBound
    ((avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap s hgap hs).trans
      (Real.sqrt_le_sqrt hsε))) heη

/-- `prop:triangle-sub`.

Both consistency errors are `max 0 (ev (I ⊗ C.total) - Σₐ ev (...))`; the overlap difference is
bounded by Cauchy–Schwarz (`question_easyApproxFromApproxDelta`) and averaged
(`consRel_of_matchGap`). -/
theorem triangleSub
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxMeas Question Outcome 𝔓) (C : IdxSubMeas Question Outcome 𝔓)
    (δ ε : ℝ)
    (hAC : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A) C δ)
    (hAB : S.SDDRel 𝒟
      (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas B)) ε) :
    S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas B)
      C (δ + Real.sqrt ε) :=
  (consRel_of_matchGap S 𝒟 h𝒟 _ _ _ _ _ (fun _ => 0) δ ε 0 hAC
    (fun q => question_easyApproxFromApproxDelta S.toVecState
      (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas A) q)
      (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas B) q) (IdxSubMeas.liftRight S C q))
    (fun _ => S.qSDD_nonneg _ _) hAB.squaredDistanceBound
    (fun q => by
      show max 0 (S.ev (S.opTensor (B q).total _) - S.ev (S.opTensor (A q).total _)) ≤ 0
      rw [(A q).total_eq_one, (B q).total_eq_one, sub_self, max_self])
    (avgOver_zero 𝒟).le).mono (add_zero _).le

/-- Heterogeneous left-register substitution.

The vendored statement places the two left families on `H_A` and the right family on `H_B`; in
the symmetric model these placements are the lifts, and this is `triangleSub`. -/
theorem triangleSub_heterogeneous
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxMeas Question Outcome 𝔓) (C : IdxSubMeas Question Outcome 𝔓)
    (δ ε : ℝ)
    (hAC : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A) C δ)
    (hAB : S.SDDRel 𝒟
      (IdxSubMeas.placeLeft S (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.placeLeft S (IdxMeas.toIdxSubMeas B)) ε) :
    S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas B)
      C (δ + Real.sqrt ε) :=
  triangleSub S 𝒟 h𝒟 A B C δ ε hAC hAB

/-! ### Right-register variants of `triangleSub` -/

/-- Right-register substitution for submeasurements when the right total
overlap is monotone in the replacement direction.

The general submeasurement form `triangleSub_right_subMeas_totalGap` includes
the absolute displacement of the total-overlap term.  In the special case where
the new right family has no larger total overlap with the fixed left family,
this displacement is not needed: increasing the total is the only way in which
the total term can worsen the consistency defect.  The remaining contribution
is exactly the usual matching-mass Cauchy--Schwarz term. -/
theorem triangleSub_right_subMeas_total_le
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B D : IdxSubMeas Question Outcome 𝔓) (δ ε : ℝ)
    (hAB : S.ConsRel 𝒟 A B δ)
    (hBD : S.SDDRel 𝒟
      (IdxSubMeas.liftRight S B)
      (IdxSubMeas.liftRight S D) ε)
    (hTotalLe :
      ∀ q : Question,
        S.ev (S.L ((A q).total) * S.R ((D q).total)) ≤
          S.ev (S.L ((A q).total) * S.R ((B q).total))) :
    S.ConsRel 𝒟 A D (δ + Real.sqrt ε) :=
  (consRel_of_matchGap S 𝒟 h𝒟 _ _ _ _ _ (fun _ => 0) δ ε 0 hAB
    (fun q => right_match_gap_abs_le_sqrt_qSDD S.toVecState (IdxSubMeas.liftLeft S A q)
      (IdxSubMeas.liftRight S B q) (IdxSubMeas.liftRight S D q))
    (fun _ => S.qSDD_nonneg _ _) hBD.squaredDistanceBound
    (fun q => max_le le_rfl (sub_nonpos.mpr (hTotalLe q)))
    (avgOver_zero 𝒟).le).mono (add_zero _).le

/-- Right-register substitution: `triangleSub` with the measurement replaced on the second
factor. -/
theorem triangleSub_right
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B D : IdxMeas Question Outcome 𝔓) (δ ε : ℝ)
    (hAB : S.ConsRel 𝒟
      A (IdxMeas.toIdxSubMeas B) δ)
    (hBD : S.SDDRel 𝒟
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas D)) ε) :
    S.ConsRel 𝒟
      A
      (IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) :=
  triangleSub_right_subMeas_total_le S 𝒟 h𝒟 A _ _ δ ε hAB hBD fun q => by
    show S.ev (_ * S.R (D q).total) ≤ S.ev (_ * S.R (B q).total)
    rw [(D q).total_eq_one, (B q).total_eq_one]

/-- Heterogeneous right-register substitution.

The vendored statement places the left family on `H_A` and the two right families on `H_B`; in
the symmetric model these placements are the lifts, and this is `triangleSub_right`. -/
theorem triangleSub_right_heterogeneous
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B D : IdxMeas Question Outcome 𝔓) (δ ε : ℝ)
    (hAB : S.ConsRel 𝒟
      A (IdxMeas.toIdxSubMeas B) δ)
    (hBD : S.SDDRel 𝒟
      (IdxSubMeas.placeRight S (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeRight S (IdxMeas.toIdxSubMeas D)) ε) :
    S.ConsRel 𝒟
      A
      (IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) :=
  triangleSub_right S 𝒟 h𝒟 A B D δ ε hAB hBD

/-- Right-register substitution for submeasurements, with the total-overlap
displacement stated explicitly.

For complete right-register measurements the total-overlap term
`ev ψ (A_total ⊗ B_total)` is independent of the right family.  For general
submeasurements this term may change.  The lemma therefore separates the usual
state-dependent-distance contribution from the averaged displacement of the
right total operator. -/
theorem triangleSub_right_subMeas_totalGap
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B D : IdxSubMeas Question Outcome 𝔓) (δ ε η : ℝ)
    (hAB : S.ConsRel 𝒟 A B δ)
    (hBD : S.SDDRel 𝒟
      (IdxSubMeas.liftRight S B)
      (IdxSubMeas.liftRight S D) ε)
    (hTotal :
      avgOver 𝒟 (fun q =>
        |S.ev (S.L ((A q).total) * S.R ((D q).total)) -
          S.ev (S.L ((A q).total) * S.R ((B q).total))|) ≤ η) :
    S.ConsRel 𝒟 A D (δ + Real.sqrt ε + η) :=
  consRel_of_matchGap S 𝒟 h𝒟 _ _ _ _ _ _ δ ε η hAB
    (fun q => right_match_gap_abs_le_sqrt_qSDD S.toVecState (IdxSubMeas.liftLeft S A q)
      (IdxSubMeas.liftRight S B q) (IdxSubMeas.liftRight S D q))
    (fun _ => S.qSDD_nonneg _ _) hBD.squaredDistanceBound
    (fun _ => max_le (abs_nonneg _) (le_abs_self _)) hTotal

end Model

end MIPRE.LIDT.Co.Preliminaries

end
