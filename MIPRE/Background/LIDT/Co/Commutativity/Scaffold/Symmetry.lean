/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Scaffold/Symmetry.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Core

@[expose] public section

/-!
# Section 11 commutativity: symmetry transport

The point-consistency relation of a polynomial family, written in the evaluated-point-family
notation and in both orientations used by the Section 11 commutativity argument: the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Scaffold/Symmetry.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

The relation is the bipartite `strategy.state.ConsRel` of the strategy's symmetric model. The
swapped orientation is `SymModel.consRel_symm_of_density_fixed`, a theorem of the model, so the
vendored `strategy.densityFixed` argument is gone.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The point-consistency relation written in local evaluated-point-family
notation. -/
lemma evaluatedPointFamily_pointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    strategy.state.ConsRel
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta :=
  hcons.pointConsistency

/-- The evaluated-point consistency relation with the two families swapped.
This is the orientation needed by `Preliminaries.consSubMeas`, whose
submeasurement input comes first. -/
lemma evaluatedPointFamily_pointConsistency_swapped
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    strategy.state.ConsRel
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      zeta :=
  strategy.state.consRel_symm_of_density_fixed
    (uniformDistribution (Point params.next))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (evaluatedPointFamily params family)
    zeta
    (evaluatedPointFamily_pointConsistency params strategy family zeta hcons)

end MIPRE.LIDT.Co.Commutativity

end
