/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.Core

@[expose] public section

/-!
# Section 12 pasting: commute G half-sandwich

The public statement of `lem:commute-g-half-sandwich`: the counterpart of the vendored file of the
same path under `MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md`
(milestone M11, section "Port conventions").

`commuteGHalfSandwich_ofGHatFacts params S family gamma zeta k hk hzeta_le hfacts` takes the
symmetric model `S : SymModel 𝔓 K` where the vendored `ψbi` was, and the source-facing
`commuteGHalfSandwich` takes a `SymStrat params.next 𝔓 K` and concludes on `strategy.state`, as the
ported `gHatFacts` does. Neither vendored lemma has a swap, density or normalization hypothesis, so
both statements are the vendored ones with the state translated.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel)
open MIPRE.LIDT.Co (SymModel SymStrat IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Internal form of `lem:commute-g-half-sandwich` after applying
`cor:G-hat-facts`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:871-910` uses
the completed-measurement self-consistency and commutation estimates from
`cor:G-hat-facts`.  The paper-facing theorem `commuteGHalfSandwich` below
derives those estimates from the source hypotheses. -/
theorem commuteGHalfSandwich_ofGHatFacts
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hfacts : GHatFactsStatement params S family gamma zeta) :
    CommuteGHalfSandwichStatement params S family gamma zeta k :=
  ⟨commuteGHalfSandwich_core params S family gamma zeta k hk hzeta_le
    hfacts.completedSelfConsistency hfacts.completedCommutation⟩

/-- `lem:commute-g-half-sandwich`, source-facing form. -/
theorem commuteGHalfSandwich
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 2 ≤ k) :
    CommuteGHalfSandwichStatement params strategy.state family gamma zeta k :=
  commuteGHalfSandwich_ofGHatFacts params strategy.state family gamma zeta k hk hzeta_le
    (gHatFacts params strategy family eps delta gamma zeta hgamma_nonneg hgamma_le
      hzeta_nonneg hzeta_le hdq_le hgood hcons hself hbound)

end MIPRE.LIDT.Co.Pasting

end
