/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.PaperMoveChain.Telescope

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G theorem

Derivation of `lem:from-H-to-G`, from the `G`-hat facts, the half-sandwich commutation theorem,
and the telescoping Bernoulli-stage comparison: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position, a strategy is a
`SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`. The vendored
`fromHToG_ofGHatFactsAndHalfSandwich` and `fromHToG_ofGHatFacts` take the normalization
hypothesis `hnorm : ψbi.IsNormalized` only to pass it to
`fromHToG_stageMassTelescope_of_paperMoveChain`, whose ported form drops it (section
"Swap symmetry is a theorem"), so it is dropped here as well, and the vendored calls that passed
`strategy.state strategy.isNormalized` pass `strategy.state`. No lemma of the file has a swap or
density hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel)
open MIPStarRE.LDT.Pasting (fromHToGPaperTotalError fromHToGPaperTotalError_le)
open MIPRE.LIDT.Co (SymModel SymStrat IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Internal form of `lem:from-H-to-G` after applying `cor:G-hat-facts` and
`lem:commute-g-half-sandwich`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:1295-1670`
uses the completed-measurement facts and the half-sandwich commutation theorem
internally.  The paper-facing theorem `fromHToG` below derives those inputs
from the source hypotheses. -/
theorem fromHToG_ofGHatFactsAndHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le_one : zeta ≤ 1)
    (hfacts : GHatFactsStatement params S family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    (k : ℕ) :
    FromHToGStatement params strategy S family gamma zeta k := by
  refine ⟨?_⟩
  have hpaper :
      |fromHToGStageMass params S family k 0 - fromHToGStageMass params S family k k| ≤
        fromHToGPaperTotalError params gamma zeta k :=
    fromHToG_stageMassTelescope_of_paperMoveChain params S family gamma zeta
      hgamma_nonneg hzeta_nonneg hfacts hhalf
      (fromHToGAdjacentStageExactFacts_of_weights params S family) k
  rw [fromHToGStageMass_zero_eq params strategy S family k,
    fromHToGStageMass_terminal_eq params S family k] at hpaper
  exact hpaper.trans <|
    fromHToGPaperTotalError_le params gamma zeta k hgamma_nonneg hzeta_nonneg hzeta_le_one

/-- Internal form of `lem:from-H-to-G` from `cor:G-hat-facts`.

The half-sandwich estimates are obtained from the same `G-hat` facts. -/
theorem fromHToG_ofGHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le_one : zeta ≤ 1)
    (hfacts : GHatFactsStatement params S family gamma zeta)
    (k : ℕ) :
    FromHToGStatement params strategy S family gamma zeta k :=
  fromHToG_ofGHatFactsAndHalfSandwich params strategy S family gamma zeta hgamma_nonneg
    hzeta_nonneg hzeta_le_one hfacts
    (fun j hj => commuteGHalfSandwich_ofGHatFacts params S family gamma zeta j hj
      hzeta_le_one hfacts) k

/-- Internal form of `lem:from-H-to-G` from the Section 11 commutativity
conclusion. -/
theorem fromHToG_ofComMain
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (k : ℕ) :
    FromHToGStatement params strategy strategy.state family gamma zeta k :=
  fromHToG_ofGHatFacts params strategy strategy.state family gamma zeta hgamma_nonneg
    hzeta_nonneg hzeta_le_one
    (gHatFacts_ofComMainAndSelfConsistency params strategy family gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le_one hdq_le hcom hself) k

/-- `lem:from-H-to-G`, source-facing form at the strategy state. -/
theorem fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hgamma_le : gamma ≤ 1) (hzeta_le_one : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    FromHToGStatement params strategy strategy.state family gamma zeta k :=
  fromHToG_ofGHatFactsAndHalfSandwich params strategy strategy.state family gamma zeta
    hgamma_nonneg hzeta_nonneg hzeta_le_one
    (gHatFacts params strategy family eps delta gamma zeta hgamma_nonneg hgamma_le
      hzeta_nonneg hzeta_le_one hdq_le hgood hcons hself hbound)
    (fun j hj => commuteGHalfSandwich params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le_one hdq_le hgood hcons hself hbound j hj) k

end MIPRE.LIDT.Co.Pasting

end
