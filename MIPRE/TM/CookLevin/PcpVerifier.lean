/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.ShoupCoefficients
import MIPRE.TM.CookLevin.PcpPrepare
import MIPRE.TM.CookLevin.PcpViewSize
import MIPRE.Foundations.SAT.PcpFieldTests
import MIPRE.Foundations.SAT.PcpFormat
import MIPRE.Foundations.SAT.CircuitFieldCorrect

/-!
# The raw polynomial-time classical PCP verifier

The verifier rejects invalid specifications and malformed field views, constructs
the exact circuit within the supplied view budget, evaluates its polynomial, and
checks both algebraic identities on coefficient vectors. Its correspondence to
typed low-degree proofs is established separately.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Desc LowDegree LowDegree.BinaryPolynomial

set_option maxRecDepth 4096

noncomputable def verifierParams : PolyTimeFun PcpInput ParamInput := snd.comp (fst.comp fst)

noncomputable def pointProg : PolyTimeFun PcpInput (List BitStr) := fst.comp snd
noncomputable def claimsProg : PolyTimeFun PcpInput (List BitStr) := snd.comp snd

/-- Construct the binary field modulus once from its unary degree. -/
noncomputable def verifierModulus : PolyTimeFun PcpInput BitStr :=
  shoupLowerCoeffs.comp (fieldDegreeU.comp verifierParams)

theorem verifierModulus_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierModulus (pcpInput D n T Q σ x y z ev) =
      shoupLowerCoeffs (unary (pcpParams n T Q σ).k) := by
  simp only [verifierModulus, comp_apply, fieldDegreeU_apply, verifierParams,
    fst_apply, snd_apply, pcpInput]

/-- Evaluate the concrete circuit polynomial at the supplied field point. -/
noncomputable def verifierCircuitValue : PolyTimeFun PcpInput BitStr :=
  let inputCount := inputCountU.comp verifierParams
  let x := take.comp (pointProg.pair inputCount)
  let w := drop.comp (pointProg.pair inputCount)
  let gs := snd.comp (Circuit.partsProg.comp pcpCircuitProg)
  Circuit.circuitBitsProg.comp (verifierModulus.pair (x.pair (w.pair gs)))

theorem verifierCircuitValue_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierCircuitValue (pcpInput D n T Q σ x y z ev) =
      Circuit.circuitBits (verifierModulus (pcpInput D n T Q σ x y z ev))
        (z.take (5 * (pcpParams n T Q σ).m + 5))
        (z.drop (5 * (pcpParams n T Q σ).m + 5))
        (pcpCircuitProg (pcpInput D n T Q σ x y z ev)).gates := by
  simp only [verifierCircuitValue, comp_apply, pair_apply, Circuit.circuitBitsProg_apply,
    take_apply, drop_apply, pointProg, fst_apply, snd_apply, inputCountU_length,
    verifierParams, Circuit.partsProg, ofEncodeEq_apply, pcpInput, pcpParams]

/-- Pair the five claimed answer evaluations with the five sign coordinates. -/
noncomputable def verifierLiterals : PolyTimeFun PcpInput (List (BitStr × BitStr)) :=
  let offset := (nsmulU 5).comp (innerDimParamsU.comp verifierParams)
  let signs := take.comp ((drop.comp (pointProg.pair offset)).pair (const (unary 5)))
  zip.comp ((take.comp (claimsProg.pair (const (unary 5)))).pair signs)

theorem verifierLiterals_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierLiterals (pcpInput D n T Q σ x y z ev) =
      (ev.take 5).zip ((z.drop (5 * (pcpParams n T Q σ).m)).take 5) := by
  simp only [verifierLiterals, comp_apply, pair_apply, zip_apply, take_apply, drop_apply,
    claimsProg, pointProg, fst_apply, snd_apply, const_apply, length_unary, length_nsmulU,
    innerDimParamsU_length, verifierParams, pcpInput, pcpParams]

/-- Pair the certificate evaluations after the main certificate with each coordinate. -/
noncomputable def verifierCertificates : PolyTimeFun PcpInput (List (BitStr × BitStr)) :=
  zip.comp ((drop.comp (claimsProg.pair (const (unary 6)))).pair pointProg)

theorem verifierCertificates_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierCertificates (pcpInput D n T Q σ x y z ev) = (ev.drop 6).zip z := by
  simp only [verifierCertificates, comp_apply, pair_apply, zip_apply, drop_apply,
    claimsProg, pointProg, fst_apply, snd_apply, const_apply, length_unary, pcpInput]

/-- Both field identities, including the single circuit-polynomial evaluation. -/
noncomputable def verifierTests : PolyTimeFun PcpInput Bool :=
  let β := (ArrayProg.getD []).comp ((const 5).pair claimsProg)
  PcpFieldTests.checksProg.comp (verifierModulus.pair
    (verifierCircuitValue.pair (β.pair (verifierLiterals.pair verifierCertificates))))

theorem verifierTests_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierTests (pcpInput D n T Q σ x y z ev) =
      PcpFieldTests.checksProg
        (verifierModulus (pcpInput D n T Q σ x y z ev),
          verifierCircuitValue (pcpInput D n T Q σ x y z ev), ev.getD 5 [],
          (ev.take 5).zip ((z.drop (5 * (pcpParams n T Q σ).m)).take 5), (ev.drop 6).zip z) := by
  change PcpFieldTests.checksProg
    (verifierModulus (pcpInput D n T Q σ x y z ev),
      verifierCircuitValue (pcpInput D n T Q σ x y z ev), ev.getD 5 [],
      verifierLiterals (pcpInput D n T Q σ x y z ev),
      verifierCertificates (pcpInput D n T Q σ x y z ev)) = _
  rw [verifierLiterals_apply, verifierCertificates_apply]

/-- The constructed parameter family's exact raw view check. -/
noncomputable def verifierFormat : PolyTimeFun PcpInput Bool :=
  viewFormatProg.comp
    (((fieldDegreeProg.comp verifierParams).pair (outerDimProg.comp verifierParams)).pair snd)

theorem verifierFormat_true_iff (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifierFormat (pcpInput D n T Q σ x y z ev) = true ↔
      ViewFormat (pcpParams n T Q σ) z ev := by
  simp only [verifierFormat, comp_apply, pair_apply, fieldDegreeProg_apply,
    outerDimProg_apply, verifierParams, fst_apply, snd_apply, pcpInput]
  rw [← pcpParams_outer n T Q σ]
  exact viewFormatProg_true_iff (pcpParams n T Q σ) z ev

/-- The actual globally polynomial-time verifier, with both mandatory rejection checks. -/
noncomputable def verifyPcp : PolyTimeFun PcpInput Bool :=
  ite (validProg.comp fst) (ite verifierFormat verifierTests (const false)) (const false)

theorem verifyPcp_true_iff (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr) :
    verifyPcp (pcpInput D n T Q σ x y z ev) = true ↔
      Valid D n T Q σ x y ∧ ViewFormat (pcpParams n T Q σ) z ev ∧
        verifierTests (pcpInput D n T Q σ x y z ev) = true := by
  change (if validProg ((D, n, T, Q, σ), x, y) = true then
    if verifierFormat (pcpInput D n T Q σ x y z ev) = true then
      verifierTests (pcpInput D n T Q σ x y z ev) else false else false) = true ↔ _
  by_cases hv : validProg ((D, n, T, Q, σ), x, y) = true
  · rw [if_pos hv]
    have hV := (validProg_true_iff D n T Q σ x y).mp hv
    by_cases hf : verifierFormat (pcpInput D n T Q σ x y z ev) = true
    · rw [if_pos hf]
      have hF := (verifierFormat_true_iff D n T Q σ x y z ev).mp hf
      simp only [hV, hF, true_and]
    · rw [if_neg hf]
      have hF : ¬ ViewFormat (pcpParams n T Q σ) z ev :=
        fun h => hf ((verifierFormat_true_iff D n T Q σ x y z ev).mpr h)
      simp only [Bool.false_eq_true, hF, false_and, and_false]
  · rw [if_neg hv]
    have hV : ¬ Valid D n T Q σ x y :=
      fun h => hv ((validProg_true_iff D n T Q σ x y).mpr h)
    simp only [Bool.false_eq_true, hV, false_and]

/-- Invalid specifications and malformed views are rejected unconditionally. -/
theorem verifyPcp_reject_invalid (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (z ev : List BitStr)
    (h : ¬ Valid D n T Q σ x y ∨ ¬ ViewFormat (pcpParams n T Q σ) z ev) :
    verifyPcp (pcpInput D n T Q σ x y z ev) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨hv, hf, _⟩ := (verifyPcp_true_iff D n T Q σ x y z ev).mp ht
  exact h.elim (fun hn => hn hv) (fun hn => hn hf)

/-- The raw verifier has exactly the source-parameter time bound in the PCP contract. -/
theorem verifyPcp_time_le :
    ∃ R : Polynomial ℕ, ∀ D n T Q σ x y z ev, Valid D n T Q σ x y →
      ViewFormat (pcpParams n T Q σ) z ev →
      ∃ t ≤ R.eval (Nat.size n + Nat.size T + Q + σ),
        verifyPcp.code.Runs (encode (pcpInput D n T Q σ x y z ev))
          (encode (verifyPcp (pcpInput D n T Q σ x y z ev))) t :=
  pcpProgram_time_le verifyPcp

end MIPRE.TM.CookLevin.Pad
