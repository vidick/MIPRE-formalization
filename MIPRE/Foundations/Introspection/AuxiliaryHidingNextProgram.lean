/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryHidingCoreProgram
import MIPRE.Foundations.Introspection.AuxiliaryRegisterProgram

/-! # The complete executable interior hiding edge

Only the prefixes needed by the edge are scanned. On successful scans, all
factor and matrix queries are legal and the core inputs are exact. Acceptance
is precisely prefix attainability together with the quotient hiding predicate.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryHiding
open Cost Cost.PolyTimeFun CLChecks AuxiliaryScan LowDegree.BinaryLinear
open AuxiliaryProgram (andCheck andCheck_iff)

abbrev Input := AuxiliarySource.Context × Triple × Triple

def sourceContext : PolyTimeFun Input AuxiliarySource.Context := fst
def leftAnswer : PolyTimeFun Input Triple := fst.comp snd
def rightAnswer : PolyTimeFun Input Triple := snd.comp snd
def leftInput : PolyTimeFun Input AuxiliaryScan.Input := sourceContext.pair (fst.comp leftAnswer)
def rightInput : PolyTimeFun Input AuxiliaryScan.Input := sourceContext.pair (fst.comp rightAnswer)
def leftScan (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ) : PolyTimeFun Input State :=
  (program f m k).comp leftInput
def rightScan (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ) : PolyTimeFun Input State :=
  (program f m k).comp rightInput

def prepare (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ) : PolyTimeFun Input CoreInput :=
  let lpre := fst.comp (snd.comp (leftScan f m k))
  let rpre := fst.comp (snd.comp (rightScan f m k))
  let old := (registers f m (k + 1)).comp rightInput
  let next := (registers f m (k + 2)).comp rightInput
  let fresh := (factorAt f m (k + 1)).comp rightInput
  let mat := m.comp ((nextContext (k + 1)).comp (rightInput.pair (rightScan f m (k + 1))))
  (lpre.pair rpre).pair ((leftAnswer.pair rightAnswer).pair
    (old.pair (next.pair (fresh.pair mat))))

def check (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ) : PolyTimeFun Input Bool :=
  andCheck (fst.comp (leftScan f m k)) <|
    andCheck (fst.comp (rightScan f m (k + 1))) (core.comp (prepare f m k))

theorem prepare_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (k : ℕ) (y yp x z zp t : Fin n → CL.𝔽₂)
    (hq : ∀ j ≤ k + 1, QueriesCorrectAt f m ctx P j)
    (hy : ∃ a, (P.truncate k).eval a = P.outputPrefix k y)
    (hz : ∃ a, (P.truncate (k + 1)).eval a = P.outputPrefix (k + 1) z) :
    prepare f m k (ctx, (CL.toBits y, CL.toBits yp, CL.toBits x),
        (CL.toBits z, CL.toBits zp, CL.toBits t)) =
      ((CL.toBits (P.outputPrefix k y), CL.toBits (P.outputPrefix k z)),
       ((CL.toBits y, CL.toBits yp, CL.toBits x), (CL.toBits z, CL.toBits zp, CL.toBits t)),
       (CL.indicatorBits (prefixRegister P (k + 1) z),
        CL.indicatorBits (prefixRegister P (k + 2) z),
        CL.indicatorBits (P.factorOfPrefix (k + 1) z),
        matrixBits (LinearMap.toMatrix' (P.mapOfPrefix (k + 1) z)))) := by
  have hz0 : ∃ a, (P.truncate k).eval a = P.outputPrefix k z := by
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, earlier_attained hP (by omega) z a ha⟩
  obtain ⟨a, hls, _⟩ := program_sound f m ctx hP y k
    (fun j hj => hq j (by omega))
    (program_complete f m ctx hP y k (fun j hj => hq j (by omega)) hy)
  obtain ⟨b, hrs, _⟩ := program_sound f m ctx hP z k
    (fun j hj => hq j (by omega))
    (program_complete f m ctx hP z k (fun j hj => hq j (by omega)) hz0)
  obtain ⟨c, hrn, hc⟩ := program_sound f m ctx hP z (k + 1)
    (fun j hj => hq j (by omega))
    (program_complete f m ctx hP z (k + 1) (fun j hj => hq j (by omega)) hz)
  have hro := registers_correct f m ctx hP z (k + 1)
    (fun j hj => hq j (by omega)) (by simpa using hz0)
  have hrnew := registers_correct f m ctx hP z (k + 2)
    (fun j hj => hq j (by omega)) (by simpa using hz)
  have hrf := factorAt_correct f m ctx hP z (k + 1) hq hz
  have hrm := (hq (k + 1) le_rfl _ ⟨c, hc⟩).2
  rw [AuxiliaryPrefix.mapOfPrefix_outputPrefix hP] at hrm
  simp only [prepare, leftScan, rightScan, leftInput, rightInput, sourceContext,
    leftAnswer, rightAnswer, comp_apply, pair_apply, fst_apply, snd_apply,
    hls, hrs, hrn, hro, hrnew, hrf]
  change (_, _, _, _, _, m (contextAt ctx (k + 2) (CL.toBits (P.outputPrefix (k + 1) z)))) = _
  rw [hrm]

theorem check_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (k : ℕ) (y yp x z zp t : Fin n → CL.𝔽₂)
    (hq : ∀ j ≤ k + 1, QueriesCorrectAt f m ctx P j) :
    check f m k (ctx, (CL.toBits y, CL.toBits yp, CL.toBits x),
      (CL.toBits z, CL.toBits zp, CL.toBits t)) = true ↔
      (∃ a, (P.truncate k).eval a = P.outputPrefix k y) ∧
      (∃ a, (P.truncate (k + 1)).eval a = P.outputPrefix (k + 1) z) ∧
      AuxiliaryQuotient.hidingNext P k (y, yp, x) (z, zp, t) := by
  simp only [check, andCheck_iff, comp_apply, leftScan, rightScan, leftInput, rightInput,
    sourceContext, leftAnswer, rightAnswer, pair_apply, fst_apply, snd_apply]
  constructor
  · rintro ⟨hl, hr, hc⟩
    obtain ⟨a, _, ha⟩ := program_sound f m ctx hP y k (fun j hj => hq j (by omega)) hl
    obtain ⟨b, _, hb⟩ := program_sound f m ctx hP z (k + 1) (fun j hj => hq j (by omega)) hr
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    rw [prepare_correct f m ctx hP k y yp x z zp t hq ⟨a, ha⟩ ⟨b, hb⟩,
      core_correct] at hc
    exact hc
  · rintro ⟨hy, hz, hc⟩
    refine ⟨program_complete f m ctx hP y k (fun j hj => hq j (by omega)) hy,
      program_complete f m ctx hP z (k + 1) (fun j hj => hq j (by omega)) hz, ?_⟩
    rw [prepare_correct f m ctx hP k y yp x z zp t hq hy hz, core_correct]
    exact hc

end MIPRE.Introspection.AuxiliaryHiding
end
