/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Basic.lean, to the symmetric
model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Statements
public import MIPRE.Background.LIDT.Co.Preliminaries.Completion
public import MIPRE.Background.LIDT.Co.Preliminaries.CompletionTransfer
public import MIPRE.Background.LIDT.Co.Preliminaries.DistanceBounds
public import MIPRE.Background.LIDT.Co.Preliminaries.Triangles.SimEq
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Core
public import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic

@[expose] public section

/-!
# Section 5 — basic projectivization data

The right-register transport of the state-dependent distance and the residual hypotheses passed
to the self-consistency handoff of the orthonormalization projectivization chain: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Basic.lean`
in the port of `planning/c6b-plan.md` (milestone M8, section "Port conventions").

The mathematical source is the orthonormalization-and-completion argument of
`inductive_step.tex`, lines 130–149. The vendored file also records the scalar of that
argument, `ζ₂ = 2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ`, and its absorbed form
`200·ζ^{1/4} + 42·ζ^{1/8}`. Those three declarations are classical; they are imported from the
vendored file, not ported, and consumers name them through an explicit
`open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizeAndCompleteError …)` list. Inside
`MIPRE.LIDT.Co`, a dotted `MakingMeasurementsProjective.X` resolves to the namespace of the port
and does not find them.

The vendored transport lemmas ask for a permutation-invariant state, which determined the state
implicitly. Here swap symmetry is a theorem of the model (`S.ev_L_eq_ev_R`, through
`Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv`), so `hperm` is dropped and the
model `S : SymModel 𝔓 K` is explicit. The vendored lifts `A.liftLeft`, `A.liftRight` are
`A.map S.L`, `A.map S.R` on submeasurements and `IdxSubMeas.liftLeft S`,
`IdxSubMeas.liftRight S` on indexed families. `ProjectivizationSelfConsistencyHandoff` is a
`SymModel` structure, with its fields verbatim.

## Not ported

- `orthonormalizeAndCompleteError`: classical, imported.
- `sqrt_orthonormalizationError_eq`: classical, imported.
- `orthonormalizeAndCompleteError_le_absorbedZeta2`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex` lines 130–149
- `references/ldt-paper/orthonormalization.tex` lines 67–77 (`thm:orthonormalization`)
- `references/ldt-paper/preliminaries.tex` lines 1101–1170 (`prop:completing-to-measurement`)
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MakingMeasurementsProjective

open MIPStarRE.LDT (Distribution avgOver uniformDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Right-register transport -/

/-- The state-dependent distance between right placements of two local submeasurements equals
the distance between their left placements.

This is the bookkeeping for the Bob-side completion estimate of `inductive_step.tex`, lines
140–147: the orthonormalize-and-complete step returns a left-register bound, and the paper also
uses the right-register bound. It is the submeasurement case of
`Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv`. -/
theorem qSDD_liftRight_eq_liftLeft_of_permInv {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : SubMeas Outcome 𝔓) :
    S.qSDD (A.map S.R) (B.map S.R) = S.qSDD (A.map S.L) (B.map S.L) :=
  Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv S A.outcome B.outcome

/-- Transport an `SDDRel` bound from left lifts to right lifts. -/
theorem sddRel_liftRight_of_liftLeft_permInv {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome 𝔓) (δ : ℝ) :
    S.SDDRel 𝒟 (IdxSubMeas.liftLeft S A) (IdxSubMeas.liftLeft S B) δ →
      S.SDDRel 𝒟 (IdxSubMeas.liftRight S A) (IdxSubMeas.liftRight S B) δ := by
  intro h
  have heq : S.sddError 𝒟 (IdxSubMeas.liftRight S A) (IdxSubMeas.liftRight S B) =
      S.sddError 𝒟 (IdxSubMeas.liftLeft S A) (IdxSubMeas.liftLeft S B) :=
    congrArg (avgOver 𝒟) <| funext fun q =>
      qSDD_liftRight_eq_liftLeft_of_permInv S (A q) (B q)
  exact ⟨heq ▸ h.squaredDistanceBound⟩

/-! ### Projective self-consistency handoff -/

/-- Handoff data for the projective-measurement part of the orthonormalization proof.

The three fields record the paper's pre-projective consistency and the two completion-closeness
estimates of `inductive_step.tex`, lines 130–149: the hypotheses needed once the
orthonormalization and completion constructions have produced projective measurements
`Q_A`, `Q_B` close to the pre-projective measurements `G_A`, `G_B`. -/
structure ProjectivizationSelfConsistencyHandoff {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (G_A G_B : Measurement Outcome 𝔓) (Q_A Q_B : ProjMeas Outcome 𝔓)
    (ζ₁ ζ₂ : ℝ) : Prop where
  /-- Paper line 131, obtained before the projective measurements are produced. -/
  preProjectiveConsistency :
    S.ConsRel (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    S.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (G_A.toSubMeas.map S.L))
      (constSubMeasFamily (Q_A.toSubMeas.map S.L)) ζ₂
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    S.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (G_B.toSubMeas.map S.R))
      (constSubMeasFamily (Q_B.toSubMeas.map S.R)) ζ₂

end MIPRE.LIDT.Co.MakingMeasurementsProjective

end
