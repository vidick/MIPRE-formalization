/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
CommutingWithG/Complete.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Main.Results
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion
public import MIPRE.Background.LIDT.Co.Preliminaries.CompletionTransfer
public import MIPStarRE.LDT.Pasting.CommutingWithG.Complete

@[expose] public section

/-!
# Section 12 pasting: commuting-with-G complete part

Complete-part commuting-with-`G` bounds, `cor:commuting-with-G-complete`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/CommutingWithG/Complete.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`; the
placed families take `strategy.state` as their first explicit argument. The vendored proofs read
`strategy.isNormalized`, `strategy.densityFixed` and `strategy.permInvState` only to pass them to
`commutativitySwitcheroo_ofCompleteSelfConsistency`, `Commutativity.comMain` and
`gCompleteSelfConsistency`, whose ported forms take no such hypothesis (section "Swap symmetry is
a theorem"), so the statements here are the vendored ones, translated, and the proofs no longer
read those fields.

The two switcheroo applications are as in the vendored proof: the first, on `M = G`, gives the
point-with-complete-part bound after swapping the two questions and the two families
(`sddOpRel_swap_questions`, `Preliminaries.sddOpRel_symm`); the second, on the complete-part
family, gives the total-product bound. The comparisons with `thm:com-main` and between the
placed families hold by definition, where the vendored proof unfolds them under `simpa`.

The scalar bound `secondSwitcherooError_le_commutingWithGCompleteError` mentions no state,
operator or measurement, so it is classical: this file imports the vendored file for it, and
dependants name it through an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.Pasting (SlicePairQuestion commutativitySwitcherooError firstSwitcherooError_le_eighth_stage
  commutingWithGCompleteError pairwiseCompletePartCommutationError
  firstSwitcherooError_le_commutingWithGCompleteError)
open MIPRE.LIDT.Co (SymStrat IdxPolyFamily)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

The paper's scalar inequality
`12·√ζ + 4·√θ₁ ≤ ν₂`, where `θ₁ = θ(ζ, ζ, comMainError)` is the first
switcheroo error. The proof uses `firstSwitcherooError_le_eighth_stage` to bound
`θ₁` by `36m · eighthSum`, then a sqrt/rpow chain to land on
`ν₂ = commutingWithGCompleteError`. -/
lemma secondSwitcherooError_le_commutingWithGCompleteError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    commutativitySwitcherooError zeta zeta
      (commutativitySwitcherooError zeta zeta
        (MIPStarRE.LDT.Commutativity.comMainError params gamma zeta))
      ≤ commutingWithGCompleteError params gamma zeta := by
  have hm_nonneg : 0 ≤ (params.m : ℝ) := by positivity
  have hm_ge_one : (1 : ℝ) ≤ (params.m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hq_pos : (0 : ℝ) < params.q := by
    exact_mod_cast params.hq
  have hratio_nonneg : 0 ≤ ((params.d : ℝ) / (params.q : ℝ)) := by
    positivity
  have hratio_le_one : ((params.d : ℝ) / (params.q : ℝ)) ≤ 1 := by
    exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
  let eighthSum : ℝ :=
    Real.rpow gamma (1 / (8 : ℝ)) +
      Real.rpow zeta (1 / (8 : ℝ)) +
      Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (8 : ℝ))
  let sixteenthSum : ℝ :=
    Real.rpow gamma (1 / (16 : ℝ)) +
      Real.rpow zeta (1 / (16 : ℝ)) +
      Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ))
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hsqrt_m_le : Real.sqrt (params.m : ℝ) ≤ (params.m : ℝ) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hgamma_sixteen_sq :
      (Real.rpow gamma (1 / (16 : ℝ))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (8 : ℝ)) := by
    calc
      (Real.rpow gamma (1 / (16 : ℝ))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (16 : ℝ))) ^ (2 : ℝ) := by norm_num
      _ = Real.rpow gamma ((1 / (16 : ℝ)) * (2 : ℝ)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (8 : ℝ)) := by norm_num
  have hzeta_sixteen_sq :
      (Real.rpow zeta (1 / (16 : ℝ))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (8 : ℝ)) := by
    calc
      (Real.rpow zeta (1 / (16 : ℝ))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (16 : ℝ))) ^ (2 : ℝ) := by norm_num
      _ = Real.rpow zeta ((1 / (16 : ℝ)) * (2 : ℝ)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (8 : ℝ)) := by norm_num
  have hratio_sixteen_sq :
      (Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ))) ^ (2 : ℕ) =
        Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (8 : ℝ)) := by
    calc
      (Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ))) ^ (2 : ℕ)
          =
            (Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ))) ^
              (2 : ℝ) := by norm_num
      _ =
          Real.rpow (((params.d : ℝ) / (params.q : ℝ)))
            ((1 / (16 : ℝ)) * (2 : ℝ)) := by
              symm
              exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (8 : ℝ)) := by
            norm_num
  have heighth_le_sixteenth_sq : eighthSum ≤ sixteenthSum ^ (2 : ℕ) := by
    let a : ℝ := Real.rpow gamma (1 / (16 : ℝ))
    let b : ℝ := Real.rpow zeta (1 / (16 : ℝ))
    let c : ℝ := Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma_sixteen_sq, hzeta_sixteen_sq, hratio_sixteen_sq] at hsq
    simpa [a, b, c, eighthSum, sixteenthSum] using hsq
  have hsqrt_eighth : Real.sqrt eighthSum ≤ sixteenthSum := by
    exact (Real.sqrt_le_iff).2 ⟨hsixteenth_nonneg, by simpa using heighth_le_sixteenth_sq⟩
  have hsqrt_theta1 :
      Real.rpow
        (commutativitySwitcherooError zeta zeta
          (MIPStarRE.LDT.Commutativity.comMainError params gamma zeta))
        (1 / (2 : ℝ)) ≤ 6 * (params.m : ℝ) * sixteenthSum := by
    have hsqrt36 : Real.sqrt (36 : ℝ) = 6 := by norm_num
    have hsqrt_theta1' :
        Real.sqrt
          (commutativitySwitcherooError zeta zeta
            (MIPStarRE.LDT.Commutativity.comMainError params gamma zeta))
          ≤ 6 * (params.m : ℝ) * sixteenthSum := by
      calc
        Real.sqrt
            (commutativitySwitcherooError zeta zeta
              (MIPStarRE.LDT.Commutativity.comMainError params gamma zeta))
          ≤ Real.sqrt (36 * (params.m : ℝ) * eighthSum) := by
              have htheta1_bound :=
                firstSwitcherooError_le_eighth_stage params gamma zeta
                  hgamma_nonneg hzeta_nonneg hzeta hd_le_q
              exact Real.sqrt_le_sqrt htheta1_bound
        _ = Real.sqrt (36 : ℝ) * Real.sqrt ((params.m : ℝ) * eighthSum) := by
              rw [show (36 * (params.m : ℝ) * eighthSum) =
                (36 : ℝ) * ((params.m : ℝ) * eighthSum) by ring]
              rw [Real.sqrt_mul (by positivity)]
        _ = 6 * (Real.sqrt (params.m : ℝ) * Real.sqrt eighthSum) := by
              rw [hsqrt36, Real.sqrt_mul hm_nonneg]
        _ ≤ 6 * ((params.m : ℝ) * Real.sqrt eighthSum) := by
              gcongr
        _ ≤ 6 * ((params.m : ℝ) * sixteenthSum) := by
              gcongr
        _ = 6 * (params.m : ℝ) * sixteenthSum := by ring
    simpa [Real.sqrt_eq_rpow] using hsqrt_theta1'
  have hhalf_zeta :
      Real.rpow zeta (1 / (2 : ℝ)) ≤ Real.rpow zeta (1 / (16 : ℝ)) := by
    have hpow : (1 / (16 : ℝ)) ≤ (1 / (2 : ℝ)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have hgamma16_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : ℝ)) := by
    exact Real.rpow_nonneg hgamma_nonneg _
  have hratio16_nonneg :
      0 ≤ Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ)) := by
    exact Real.rpow_nonneg hratio_nonneg _
  have hzeta_term :
      12 * Real.rpow zeta (1 / (2 : ℝ)) ≤ 12 * (params.m : ℝ) * sixteenthSum := by
    have hsum1 :
        Real.rpow zeta (1 / (16 : ℝ)) ≤
          Real.rpow gamma (1 / (16 : ℝ)) + Real.rpow zeta (1 / (16 : ℝ)) := by
      linarith
    have hsum2 :
        Real.rpow gamma (1 / (16 : ℝ)) + Real.rpow zeta (1 / (16 : ℝ)) ≤
          sixteenthSum := by
      have hsum2' :
          Real.rpow gamma (1 / (16 : ℝ)) + Real.rpow zeta (1 / (16 : ℝ)) ≤
            Real.rpow gamma (1 / (16 : ℝ)) + Real.rpow zeta (1 / (16 : ℝ)) +
              Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ)) := by
        linarith
      simpa [sixteenthSum] using hsum2'
    have hterm : Real.rpow zeta (1 / (2 : ℝ)) ≤ sixteenthSum := by
      exact le_trans hhalf_zeta (le_trans hsum1 hsum2)
    calc
      12 * Real.rpow zeta (1 / (2 : ℝ)) ≤ 12 * sixteenthSum := by
        gcongr
      _ ≤ 12 * ((params.m : ℝ) * sixteenthSum) := by
        nlinarith [hm_ge_one, hsixteenth_nonneg]
      _ = 12 * (params.m : ℝ) * sixteenthSum := by ring
  have hchi_term :
      4 * Real.rpow
        (commutativitySwitcherooError zeta zeta
          (MIPStarRE.LDT.Commutativity.comMainError params gamma zeta))
        (1 / (2 : ℝ)) ≤ 24 * (params.m : ℝ) * sixteenthSum := by
    nlinarith [hsqrt_theta1]
  calc
    commutativitySwitcherooError zeta zeta
      (commutativitySwitcherooError zeta zeta
        (MIPStarRE.LDT.Commutativity.comMainError params gamma zeta))
      = 12 * Real.rpow zeta (1 / (2 : ℝ)) +
          4 * Real.rpow
            (commutativitySwitcherooError zeta zeta
              (MIPStarRE.LDT.Commutativity.comMainError params gamma zeta))
            (1 / (2 : ℝ)) := by
              simp [commutativitySwitcherooError]
              ring
    _ ≤ 12 * (params.m : ℝ) * sixteenthSum +
          24 * (params.m : ℝ) * sixteenthSum := by
            nlinarith [hzeta_term, hchi_term]
    _ = commutingWithGCompleteError params gamma zeta := by
          simp [commutingWithGCompleteError, sixteenthSum]
          ring

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Internal form of `cor:commuting-with-G-complete` after applying
`thm:com-main` and `lem:g-complete-self-consistency`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:721-774`
uses `thm:com-main`, `lem:commutativity-switcheroo`, and
`lem:g-complete-self-consistency` internally.  The paper-facing theorem
`commutingWithGComplete` below derives the first and third inputs from the
source hypotheses rather than exposing them as public hypotheses. -/
theorem commutingWithGComplete_ofComMainAndSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    CommutingWithGCompleteStatement params strategy.state family gamma zeta := by
  have hswitch₁ :
      CommutativitySwitcherooStatement params strategy.state family family.meas
        zeta zeta (pairwiseCompletePartCommutationError params gamma zeta) :=
    commutativitySwitcheroo_ofCompleteSelfConsistency params strategy.state family family.meas
      zeta zeta (pairwiseCompletePartCommutationError params gamma zeta)
      hself hself.completePartSelfConsistency hcom
  have hpoint_raw :
      strategy.state.SDDOpRel
        (uniformDistribution (SlicePairQuestion params))
        (completePartPointProductLeft strategy.state params family)
        (completePartPointProductRight strategy.state params family)
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)) :=
    Preliminaries.sddOpRel_symm strategy.state.toVecState
      (uniformDistribution (SlicePairQuestion params))
      (fun q => switcherooAggregateLeft strategy.state params family family.meas (q.2, q.1))
      (fun q => switcherooAggregateRight strategy.state params family family.meas (q.2, q.1))
      _
      (sddOpRel_swap_questions params strategy.state.toVecState
        (switcherooAggregateLeft strategy.state params family family.meas)
        (switcherooAggregateRight strategy.state params family family.meas)
        _ hswitch₁.aggregateCommutation)
  have hswitch₂ :
      CommutativitySwitcherooStatement params strategy.state family
        (completePartProjFamily params family) zeta zeta
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)) :=
    commutativitySwitcheroo_ofCompleteSelfConsistency params strategy.state family
      (completePartProjFamily params family) zeta zeta _ hself
      (completePartProjFamily_selfConsistency params strategy family zeta hself)
      (pointWithCompletePart_as_switcheroo_input params strategy.state family _ hpoint_raw)
  refine ⟨hcom, ?_, ?_⟩
  · exact Preliminaries.sddOpRel_mono strategy.state.toVecState _ _ _ _ _ hpoint_raw
      (firstSwitcherooError_le_commutingWithGCompleteError params gamma zeta
        hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q)
  · exact Preliminaries.sddOpRel_mono strategy.state.toVecState _ _ _ _ _
      (completePartAggregateCommutation_as_total params strategy.state family _
        hswitch₂.aggregateCommutation)
      (secondSwitcherooError_le_commutingWithGCompleteError params gamma zeta
        hgamma_nonneg hzeta_nonneg hzeta hd_le_q)

/-- `cor:commuting-with-G-complete`, source-facing form. -/
theorem commutingWithGComplete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommutingWithGCompleteStatement params strategy.state family gamma zeta :=
  commutingWithGComplete_ofComMainAndSelfConsistency params strategy family gamma zeta
    hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q
    (Commutativity.comMain params strategy eps delta gamma zeta hgood family hcons hself hbound)
    (gCompleteSelfConsistency params strategy.state family zeta hself)

end MIPRE.LIDT.Co.Pasting

end
