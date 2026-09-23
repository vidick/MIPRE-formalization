/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryQuotientProgram
import MIPRE.Foundations.Introspection.AuxiliaryQuotientChecks
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram

/-! # Executable comparisons for an interior hiding edge

The caller supplies the two extracted prefixes, the two raw triples, the
visited-register masks, and the queried next-factor matrix. This core performs
the four exact comparisons. The prefix scan separately certifies those inputs.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryHiding
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open AuxiliaryProgram (andCheck andCheck_iff equal equal_iff toBits_injective)

abbrev Triple := BitStr × BitStr × BitStr
abbrev CoreInput := (BitStr × BitStr) × (Triple × Triple) ×
  (BitStr × BitStr × BitStr × List BitStr)

def prefixes : PolyTimeFun CoreInput (BitStr × BitStr) := fst
def answers : PolyTimeFun CoreInput (Triple × Triple) := fst.comp snd
def masks : PolyTimeFun CoreInput (BitStr × BitStr × BitStr × List BitStr) := snd.comp snd
def leftDual : PolyTimeFun CoreInput BitStr := fst.comp (snd.comp (fst.comp answers))
def rightDual : PolyTimeFun CoreInput BitStr := fst.comp (snd.comp (snd.comp answers))
def leftTail : PolyTimeFun CoreInput BitStr := snd.comp (snd.comp (fst.comp answers))
def rightTail : PolyTimeFun CoreInput BitStr := snd.comp (snd.comp (snd.comp answers))
def visited : PolyTimeFun CoreInput BitStr := fst.comp masks
def remaining : PolyTimeFun CoreInput BitStr := AuxiliaryBits.complement.comp (fst.comp (snd.comp masks))
def fresh : PolyTimeFun CoreInput BitStr := fst.comp (snd.comp (snd.comp masks))
def nextMatrix : PolyTimeFun CoreInput (List BitStr) := snd.comp (snd.comp (snd.comp masks))

def core : PolyTimeFun CoreInput Bool :=
  andCheck (equal (fst.comp prefixes) (snd.comp prefixes)) <|
    andCheck (equal (AuxiliaryBits.mask.comp (visited.pair leftDual))
      (AuxiliaryBits.mask.comp (visited.pair rightDual))) <|
    andCheck (equal (AuxiliaryBits.mask.comp (remaining.pair leftTail))
      (AuxiliaryBits.mask.comp (remaining.pair rightTail))) <|
      AuxiliaryBits.quotient.comp (fresh.pair (nextMatrix.pair (rightDual.pair leftTail)))

theorem core_correct {n ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin n) ℓ) (k : ℕ)
    (y yp x z zp t : Fin n → CL.𝔽₂) :
    core ((CL.toBits (P.outputPrefix k y), CL.toBits (P.outputPrefix k z)),
      ((CL.toBits y, CL.toBits yp, CL.toBits x), (CL.toBits z, CL.toBits zp, CL.toBits t)),
      (CL.indicatorBits (CLChecks.prefixRegister P (k + 1) z),
       CL.indicatorBits (CLChecks.prefixRegister P (k + 2) z),
       CL.indicatorBits (P.factorOfPrefix (k + 1) z),
       matrixBits (LinearMap.toMatrix' (P.mapOfPrefix (k + 1) z)))) = true ↔
      AuxiliaryQuotient.hidingNext P k (y, yp, x) (z, zp, t) := by
  simp only [core, andCheck_iff, equal_iff, comp_apply, pair_apply, fst_apply, snd_apply,
    prefixes, answers, masks, visited, remaining, fresh, nextMatrix,
    leftDual, rightDual, leftTail, rightTail]
  rw [← CLChecks.stageLinear_toLinearMap P (k + 1) z, AuxiliaryBits.quotient_correct]
  simp only [AuxiliaryBits.complement_correct, AuxiliaryBits.mask_correct, toBits_injective.eq_iff]
  rfl

end MIPRE.Introspection.AuxiliaryHiding
end
