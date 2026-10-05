/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Scaffold/Core.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Defs.Normalization
public import MIPStarRE.LDT.Commutativity.Scaffold.Core

@[expose] public section

/-!
# Section 11 commutativity: displayed conclusions

The displayed conclusions of `lem:comm-data-processed-g`, `thm:com-main` and
`lem:normalization-condition`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Scaffold/Core.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

The two commutativity conclusions are state-dependent distances of joint operator families on
the symmetric model `strategy.state` of a `SymStrat params.next 𝔓 K`, written
`strategy.state.SDDOpRel …` (a `VecState` relation, reached through the parent structure); the
normalization statement is about local operators of any C*-algebra `𝔓` with its order.

The two error terms of the vendored file are real-valued functions of the parameters alone: this
file imports the vendored file for them and names them through an explicit
`open MIPStarRE.LDT.Commutativity (…)` list.

## Not ported

- `commDataProcessedGError`: classical, imported.
- `comMainError`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion FullSliceQuestion
  commDataProcessedGError comMainError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:16-47`
(`\label{lem:comm-data-processed-g}`).

Displayed conclusion of the commutativity-of-`G`-after-evaluation lemma. The local
measurements are placed on the first factor of the strategy's symmetric model. -/
abbrev CommDataProcessedGConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) : Prop :=
  strategy.state.SDDOpRel
    (uniformDistribution (EvaluatedSliceQuestion params))
    (evaluatedSliceProductLeft params strategy family)
    (evaluatedSliceProductRight params strategy family)
    (commDataProcessedGError params gamma zeta)

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:228-257`
(`\label{thm:com-main}`).

Displayed conclusion of the commutativity-of-`G` theorem. -/
abbrev ComMainConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) : Prop :=
  strategy.state.SDDOpRel
    (uniformDistribution (FullSliceQuestion params))
    (fullSliceProductLeft params strategy family)
    (fullSliceProductRight params strategy family)
    (comMainError params gamma zeta)

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:309-338`
(`\label{lem:normalization-condition}`); records the Hermitian-square /
identity-bound expansion used inside the proof of the commutativity theorem
`\label{thm:com-main}` (`references/ldt-paper/commutativity-G.tex:228-378`).

Conclusion statement for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓)
    (Q : ProjSubMeas OutcomeB 𝔓) : Prop where
  /-- The two square operators formed from `∑_b Q_b P_a Q_b` agree. -/
  sandwichedHermitianSquare :
    normalizationConditionAdjointSquareOperator P Q =
      normalizationConditionSquareOperator P Q
  /-- The square operator formed from the sandwiched family is bounded by the
  identity operator. -/
  sandwichedBoundedByIdentity :
    normalizationConditionSquareOperator P Q ≤ normalizationConditionIdentityBound P Q

end MIPRE.LIDT.Co.Commutativity

end
