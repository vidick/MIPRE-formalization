/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliarySourceQueries
import MIPRE.Foundations.Introspection.AuxiliaryMaskProgram
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram

/-! # One executable Gaussian stage of the hiding prefix scan

The stage queries the next register and its matrix, solves for the claimed
component, checks the solution by matrix multiplication, and replaces exactly
that register in the seed witness. The returned prefix is the old prefix plus
the claimed new component. Every operation has an ambient polynomial bound.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryScan
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear LowDegree.BinaryPolynomial

abbrev StageInput := AuxiliarySource.Context × BitStr × BitStr
abbrev State := Bool × BitStr × BitStr

def context : PolyTimeFun StageInput AuxiliarySource.Context := fst
def claimed : PolyTimeFun StageInput BitStr := fst.comp snd
def seed : PolyTimeFun StageInput BitStr := snd.comp snd
def oldPrefix : PolyTimeFun StageInput BitStr := AuxiliarySource.inputPrefix.comp context
def stageMask (f : PolyTimeFun AuxiliarySource.Context BitStr) : PolyTimeFun StageInput BitStr :=
  f.comp context
def stageMatrix (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) : PolyTimeFun StageInput (List BitStr) :=
  m.comp context
def target (f : PolyTimeFun AuxiliarySource.Context BitStr) : PolyTimeFun StageInput BitStr :=
  AuxiliaryBits.mask.comp ((stageMask f).pair claimed)
def solution (f : PolyTimeFun AuxiliarySource.Context BitStr) (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) : PolyTimeFun StageInput BitStr :=
  matrixSolveProg.comp ((length.comp claimed).pair ((stageMatrix m).pair (target f)))

def stage (f : PolyTimeFun AuxiliarySource.Context BitStr) (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) : PolyTimeFun StageInput State :=
  (AuxiliaryProgram.equal (applyBitsProg.comp ((stageMatrix m).pair (solution f m))) (target f)).pair
    ((xorBitsProg.comp (oldPrefix.pair (target f))).pair
      (AuxiliaryBits.replace.comp ((stageMask f).pair (seed.pair (solution f m)))))

set_option backward.isDefEq.respectTransparency false in
theorem stage_correct (f : PolyTimeFun AuxiliarySource.Context BitStr) (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context) {n : ℕ}
    (S : Finset (Fin n)) (L : (Fin n → CL.𝔽₂) →ₗ[CL.𝔽₂] (Fin n → CL.𝔽₂))
    (u y x : Fin n → CL.𝔽₂)
    (hu : AuxiliarySource.inputPrefix ctx = CL.toBits u)
    (hS : f ctx = CL.indicatorBits S)
    (hL : m ctx = matrixBits (LinearMap.toMatrix' L)) :
    stage f m (ctx, CL.toBits y, CL.toBits x) =
      let v := CL.proj S y
      let z := AuxiliaryPrefix.solveStage L v
      (decide (L z = v), CL.toBits (u + v), CL.toBits (CL.proj Sᶜ x + CL.proj S z)) := by
  have ht : target f (ctx, CL.toBits y, CL.toBits x) = CL.toBits (CL.proj S y) := by
    change AuxiliaryBits.mask (f ctx, CL.toBits y) = _
    rw [hS, AuxiliaryBits.mask_correct]
  have hz : solution f m (ctx, CL.toBits y, CL.toBits x) =
      CL.toBits (AuxiliaryPrefix.solveStage L (CL.proj S y)) := by
    change matrixSolveProg (unary (CL.toBits y).length,
      m ctx, target f (ctx, CL.toBits y, CL.toBits x)) = _
    rw [CL.length_toBits, hL, ht, AuxiliaryBits.matrixSolve_encoding]
    rfl
  have hm : applyBits (matrixBits (LinearMap.toMatrix' L))
      (CL.toBits (AuxiliaryPrefix.solveStage L (CL.proj S y))) =
        CL.toBits (L (AuxiliaryPrefix.solveStage L (CL.proj S y))) := by
    change applyBits (matrixBits (LinearMap.toMatrix' L))
      (vectorBits (AuxiliaryPrefix.solveStage L (CL.proj S y))) =
      vectorBits (L (AuxiliaryPrefix.solveStage L (CL.proj S y)))
    rw [applyBits_matrixBits]
    congr 1
    exact congrArg (fun f => f (AuxiliaryPrefix.solveStage L (CL.proj S y)))
      (Matrix.toLin'_toMatrix' L)
  simp only [stage, pair_apply, AuxiliaryProgram.equal, ap₂_apply, comp_apply,
    encoded_apply, treeEq_apply]
  change (decide (encode (applyBits (m ctx)
    (solution f m (ctx, CL.toBits y, CL.toBits x))) =
      encode (target f (ctx, CL.toBits y, CL.toBits x))),
    xorBits (AuxiliarySource.inputPrefix ctx) (target f (ctx, CL.toBits y, CL.toBits x)),
    AuxiliaryBits.replace (f ctx, CL.toBits x,
      solution f m (ctx, CL.toBits y, CL.toBits x))) = _
  have hadd : xorBits (CL.toBits u) (CL.toBits (CL.proj S y)) =
      CL.toBits (u + CL.proj S y) := xorBits_vectorBits _ _
  rw [hL, hS, hu, hz, ht, hm, AuxiliaryBits.replace_correct, hadd]
  simp only [encode_injective.eq_iff, AuxiliaryProgram.toBits_injective.eq_iff]

end MIPRE.Introspection.AuxiliaryScan
end
