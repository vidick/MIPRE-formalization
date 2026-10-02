/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/Triangles/SimEq.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.Triangles.Core

@[expose] public section

/-!
# Triangle inequalities for state-dependent distance: simultaneous equivalence

The simultaneous-equivalence triangle inequalities and the approximate-delta triangle estimate:
the counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Triangles/SimEq.lean` in
the port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The consistency statements take the symmetric model `S : SymModel 𝔓 K` as an ordinary explicit
argument in place of the vendored state, with local measurements in `𝔓`, and drop the vendored
normalization hypothesis `hψ : ψ.IsNormalized`; `triangleInequalityForApproxDelta` is about a
single state and takes a vector state `V : VecState K`. In the symmetric model both tensor
factors carry `𝔓`, so `simeqTriangleInequality_heterogeneous` has the type of
`simeqTriangleInequality` up to the order of its arguments, and is that theorem.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `prop:simeq-triangle-inequality`.

Apply `simeqToApprox` to the two hypotheses through the middle
measurement `C`, use the `SDDRel` triangle inequality to compare the induced
right-side families, and finish with `triangleSub_right`. Quantitatively this gives
`ε + sqrt (4 * (δ + γ)) = ε + 2 * sqrt (δ + γ)`. -/
theorem simeqTriangleInequality
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B C D : IdxMeas Question Outcome 𝔓)
    (ε δ γ : ℝ)
    (hAB : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas B) ε)
    (hCB : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas B) δ)
    (hCD : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas D) γ) :
    S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas D)
      (ε + 2 * Real.sqrt (δ + γ)) := by
  have hδ : 0 ≤ δ := (S.bipartiteConsError_nonneg 𝒟 _ _).trans hCB.offDiagonalBound
  have hγ : 0 ≤ γ := (S.bipartiteConsError_nonneg 𝒟 _ _).trans hCD.offDiagonalBound
  have hBD : S.SDDRel 𝒟
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas D)) (4 * (δ + γ)) :=
    stateDependentDistanceRel_mono S.toVecState 𝒟 _ _ _ _ (by linarith)
      (stateDependentDistanceRel_triangle S.toVecState 𝒟 _
        (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas C)) _ (2 * δ) (2 * γ)
        (sddRel_symm S.toVecState 𝒟 _ _ _
          ⟨(simeqToApprox S 𝒟 C B δ hCB).leftRightSquaredDistanceBound⟩)
        ⟨(simeqToApprox S 𝒟 C D γ hCD).leftRightSquaredDistanceBound⟩)
  have hsqrt : Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  exact (triangleSub_right S 𝒟 h𝒟 _ B D ε _ hAB hBD).mono (by rw [hsqrt])

/-- Heterogeneous form of `prop:simeq-triangle-inequality`.

The vendored statement is the triangle step for a general bipartite strategy, the first and
third measurements acting on Alice's space and the second and fourth on Bob's. In the symmetric
model both spaces carry `𝔓`, and this is `simeqTriangleInequality`. -/
theorem simeqTriangleInequality_heterogeneous
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A C : IdxMeas Question Outcome 𝔓)
    (B D : IdxMeas Question Outcome 𝔓)
    (ε δ γ : ℝ)
    (hAB : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas B) ε)
    (hCB : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas B) δ)
    (hCD : S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas D) γ) :
    S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas D)
      (ε + 2 * Real.sqrt (δ + γ)) :=
  simeqTriangleInequality S 𝒟 h𝒟 A B C D ε δ γ hAB hCB hCD

/-- `prop:triangle-inequality-for-approx_delta`.

The paper states the iterated telescoping version for an arbitrary chain of
approximations. The current API records the binary composition step used
throughout the repository; the full iterated form follows by induction on the
length of the chain. -/
theorem triangleInequalityForApproxDelta
    {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ₁ δ₂ : ℝ) :
    V.SDDRel 𝒟 A B δ₁ →
    V.SDDRel 𝒟 B C δ₂ →
    V.SDDRel 𝒟 A C (2 * (δ₁ + δ₂)) :=
  stateDependentDistanceRel_triangle V 𝒟 A B C δ₁ δ₂

end MIPRE.LIDT.Co.Preliminaries

end
