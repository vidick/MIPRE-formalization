/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryPrefixSolve
import MIPRE.Foundations.CL.DetypingProgParse

/-! # Fixed-width register operations for the executable hiding scan -/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryBits
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial

def mask : PolyTimeFun (BitStr × BitStr) BitStr :=
  (map (ite fst snd (const false))).comp zip

def complement : PolyTimeFun BitStr BitStr :=
  map (ite (PolyTimeFun.id _) (const false) (const true))

def replace : PolyTimeFun (BitStr × BitStr × BitStr) BitStr :=
  xorBitsProg.comp ((mask.comp ((complement.comp fst).pair (fst.comp snd))).pair
    (mask.comp (fst.pair (snd.comp snd))))

theorem mask_correct {n : ℕ} (S : Finset (Fin n)) (x : Fin n → CL.𝔽₂) :
    mask (CL.indicatorBits S, CL.toBits x) = CL.toBits (CL.proj S x) := by
  change ((CL.indicatorBits S).zip (CL.toBits x)).map
    (fun p => if p.1 then p.2 else false) = _
  apply List.ext_getElem
  · simp [CL.indicatorBits, CL.toBits]
  · intro i hi hj
    simp only [CL.indicatorBits, CL.toBits, List.getElem_map, List.getElem_zip,
      List.getElem_ofFn]
    by_cases h : (⟨i, by simpa [CL.toBits] using hj⟩ : Fin n) ∈ S
    · simp [CL.proj_apply, h]
    · simp [CL.proj_apply, h]

theorem complement_correct {n : ℕ} (S : Finset (Fin n)) :
    complement (CL.indicatorBits S) = CL.indicatorBits Sᶜ := by
  change (CL.indicatorBits S).map (fun b => if b then false else true) = _
  simp only [CL.indicatorBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, Finset.mem_compl]
  by_cases h : i ∈ S <;> simp [h]

theorem replace_correct {n : ℕ} (S : Finset (Fin n)) (x z : Fin n → CL.𝔽₂) :
    replace (CL.indicatorBits S, CL.toBits x, CL.toBits z) =
      CL.toBits (CL.proj Sᶜ x + CL.proj S z) := by
  change xorBits (mask (complement (CL.indicatorBits S), CL.toBits x))
    (mask (CL.indicatorBits S, CL.toBits z)) = _
  rw [complement_correct, mask_correct, mask_correct]
  exact xorBits_vectorBits _ _

theorem matrixSolve_encoding {m n : ℕ} (A : Matrix (Fin m) (Fin n) CL.𝔽₂)
    (v : Fin m → CL.𝔽₂) :
    matrixSolveProg (unary n, matrixBits A, CL.toBits v) =
      CL.toBits (vectorValue n (matrixSolveProg (unary n, matrixBits A, CL.toBits v))) := by
  have he : matrixSolveProg (unary n, matrixBits A, CL.toBits v) =
      vectorBits (typedReduce (typedBasis (columnRows A)) (v, 0)).2 := by
    change basisSolveProg (unary n,
      coordinateRows (transposeBits (unary n).length (matrixBits A)), vectorBits v) = _
    rw [length_unary, coordinateRows_matrixBits, basisSolveProg_encoding]
  rw [he]
  change vectorBits _ = vectorBits (vectorValue n (vectorBits _))
  rw [vectorValue_vectorBits]

end MIPRE.Introspection.AuxiliaryBits
end
