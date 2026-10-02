/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/EvaluatedSliceCommutation/Consequences.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceCommutation.Averages

@[expose] public section

/-!
# Section 11 commutativity: evaluated-slice commutation consequences

Downstream consequences of the evaluated-slice commutation estimate: pulling single-point
evaluated-family self-consistency bounds up to evaluated-slice questions. This is the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/EvaluatedSliceCommutation/Consequences.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The relations are `strategy.state.SDDRel`, a vector-state relation on joint operators, and the
placed families `evaluatedPointFamilyLeft strategy.state` and
`evaluatedPointFamilyRight strategy.state` take the model explicitly in the port
(`Co/Commutativity/Defs/Core.lean`). Each proof is the marginalization of the uniform product
distribution, as a term.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point uniformDistribution avgOver_uniform_fst
  avgOver_uniform_snd)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pull a single-point evaluated-family self-consistency bound up to the first
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_fst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hssc : strategy.state.SDDRel
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft strategy.state params family)
      (evaluatedPointFamilyRight strategy.state params family)
      zeta) :
    strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.1)
      (fun q => evaluatedPointFamilyRight strategy.state params family q.1)
      zeta :=
  ⟨(avgOver_uniform_fst (β := Point params.next) fun u =>
      strategy.state.qSDD (evaluatedPointFamilyLeft strategy.state params family u)
        (evaluatedPointFamilyRight strategy.state params family u)).trans_le
    hssc.squaredDistanceBound⟩

/-- Pull a single-point evaluated-family self-consistency bound up to the second
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_snd
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hssc : strategy.state.SDDRel
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft strategy.state params family)
      (evaluatedPointFamilyRight strategy.state params family)
      zeta) :
    strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.2)
      (fun q => evaluatedPointFamilyRight strategy.state params family q.2)
      zeta :=
  ⟨(avgOver_uniform_snd (α := Point params.next) fun u =>
      strategy.state.qSDD (evaluatedPointFamilyLeft strategy.state params family u)
        (evaluatedPointFamilyRight strategy.state params family u)).trans_le
    hssc.squaredDistanceBound⟩

end MIPRE.LIDT.Co.Commutativity

end
