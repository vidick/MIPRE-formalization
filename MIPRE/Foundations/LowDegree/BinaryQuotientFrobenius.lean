/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotient
import MIPRE.Foundations.LowDegree.BinaryKernel
import Mathlib.FieldTheory.Finite.Basic

/-! # Computing Frobenius matrices in arbitrary monic binary quotients -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost BinaryPolynomial BinaryLinear

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

/-- Quotient bit encodings agree with the generic binary linear coordinates. -/
theorem toBits_eq_vectorBits (x : AdjoinRoot f) :
    toBits f hf x = vectorBits (coordinateEquiv f hf x) := rfl

/-- A power-basis vector has the corresponding standard unit-vector encoding. -/
theorem toBits_basis (j : Fin f.natDegree) :
    toBits f hf ((AdjoinRoot.powerBasisAux' hf) j) = unitBits f.natDegree j := by
  rw [toBits_eq_vectorBits, unitBits_eq_vectorBits]
  congr 1
  ext i
  by_cases h : j = i <;> simp [coordinateEquiv, h]

/-- Frobenius is binary linear even when the quotient is not a field. -/
def frobeniusLinear : AdjoinRoot f →ₗ[ZMod 2] AdjoinRoot f :=
  (FiniteField.frobeniusAlgHom (ZMod 2) (AdjoinRoot f)).toLinearMap

/-- In a binary algebra the Frobenius map is squaring. -/
@[simp] theorem frobeniusLinear_apply (x : AdjoinRoot f) :
    frobeniusLinear f x = x ^ 2 := by
  simp [frobeniusLinear, FiniteField.frobeniusAlgHom]

/-- Frobenius in the specified monic power basis. -/
def frobeniusMatrix : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod 2) :=
  LinearMap.toMatrix (AdjoinRoot.powerBasisAux' hf) (AdjoinRoot.powerBasisAux' hf)
    (frobeniusLinear f)

/-- Squaring modulo a supplied monic polynomial, without constructing a field. -/
def squareProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  mulReduceProg.comp (PolyTimeFun.fst.pair (PolyTimeFun.snd.pair PolyTimeFun.snd))

/-- The supplied-modulus squaring program prints the canonical quotient encoding. -/
theorem squareProg_correct (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true]))
    (x : AdjoinRoot f) :
    squareProg (p, toBits f hf x) = toBits f hf (frobeniusLinear f x) := by
  have h := ofBits_mulReduce f hf p (toBits f hf x) (toBits f hf x) hp hpoly
    (length_toBits f hf x) (length_toBits f hf x)
  have hw : (mulReduceProg (p, toBits f hf x, toBits f hf x)).length = f.natDegree := by
    rw [mulReduceProg_apply, length_mulReduce p _ _ ((length_toBits f hf x).trans hp.symm), hp]
  have he := congrArg (toBits f hf) h
  rw [toBits_ofBits f hf _ hw, ofBits_toBits] at he
  simpa only [squareProg, Cost.PolyTimeFun.comp_apply, Cost.PolyTimeFun.pair_apply,
    Cost.PolyTimeFun.fst_apply, Cost.PolyTimeFun.snd_apply,
    frobeniusLinear_apply, pow_two] using he

/-- Compute the squares of the power-basis vectors and transpose their columns. -/
def frobeniusMatrixProg : PolyTimeFun BitStr (List BitStr) :=
  let columns := (PolyTimeFun.mapWith
    (squareProg.comp (PolyTimeFun.snd.pair PolyTimeFun.fst))).comp
      ((identityBitsProg.comp PolyTimeFun.length).pair (PolyTimeFun.id _))
  transposeBitsProg.comp (PolyTimeFun.length.pair columns)

/-- The ambient program computes the exact Frobenius matrix of a monic quotient.
Its columns encode the squares of `1,X,...,X^(d-1)`, not repeated squarings of `X`. -/
theorem frobeniusMatrixProg_correct (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true])) :
    frobeniusMatrixProg p = matrixBits (frobeniusMatrix f hf) := by
  let A := frobeniusMatrix f hf
  have hc : (identityBits f.natDegree).map (fun v => squareProg (p, v)) =
      matrixBits A.transpose := by
    apply List.ext_getElem
    · simp [identityBits, matrixBits]
    · intro j hj hj'
      have hjk : j < f.natDegree := by simpa [identityBits] using hj
      simp only [identityBits, List.getElem_map, List.getElem_range, matrixBits,
        List.getElem_ofFn]
      rw [← toBits_basis f hf (⟨j, hjk⟩ : Fin f.natDegree),
        squareProg_correct f hf p hp hpoly, toBits_eq_vectorBits]
      congr 1
      funext i
      exact (LinearMap.toMatrix_apply (AdjoinRoot.powerBasisAux' hf)
        (AdjoinRoot.powerBasisAux' hf) (frobeniusLinear f) i ⟨j, hjk⟩).symm
  simp only [frobeniusMatrixProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.id_apply,
    Cost.PolyTimeFun.mapWith_apply, Cost.PolyTimeFun.fst_apply,
    Cost.PolyTimeFun.snd_apply, Cost.PolyTimeFun.length_apply]
  change transposeBits (unary p.length).length
    ((identityBits (unary p.length).length).map (fun v => squareProg (p, v))) = _
  rw [length_unary, hp, hc, transposeBits_matrixBits, Matrix.transpose_transpose]

/-- The fixed-space equation for quotient Frobenius. -/
def fixedMatrix : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod 2) :=
  frobeniusMatrix f hf + 1

/-- The binary matrix kernel is exactly the set of quotient idempotents. -/
theorem fixedMatrix_ker (x : AdjoinRoot f) :
    coordinateEquiv f hf x ∈ (fixedMatrix f hf).mulVecLin.ker ↔ x * x = x := by
  rw [LinearMap.mem_ker]
  change (frobeniusMatrix f hf + 1).mulVec (coordinateEquiv f hf x) = 0 ↔ _
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hs : (frobeniusMatrix f hf).mulVec (coordinateEquiv f hf x) =
      coordinateEquiv f hf (x * x) := by
    simpa only [coordinateEquiv, frobeniusMatrix, Module.Basis.equivFun_apply,
      frobeniusLinear_apply, pow_two]
      using LinearMap.toMatrix_mulVec_repr (AdjoinRoot.powerBasisAux' hf)
        (AdjoinRoot.powerBasisAux' hf) (frobeniusLinear f) x
  rw [hs, ← map_add, ← (coordinateEquiv f hf).map_zero,
    (coordinateEquiv f hf).injective.eq_iff]
  by_cases ht : Nontrivial (AdjoinRoot f)
  · let : Nontrivial (AdjoinRoot f) := ht
    let : CharP (AdjoinRoot f) 2 :=
      charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
    exact CharTwo.add_eq_zero
  · have : Subsingleton (AdjoinRoot f) := not_nontrivial_iff_subsingleton.mp ht
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

/-- Compute Frobenius plus identity on coefficient vectors. -/
def fixedMatrixProg : PolyTimeFun BitStr (List BitStr) :=
  addMatrixBitsProg.comp
    (frobeniusMatrixProg.pair (identityBitsProg.comp PolyTimeFun.length))

/-- The fixed-space equation is generated uniformly from the supplied modulus. -/
theorem fixedMatrixProg_correct (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true])) :
    fixedMatrixProg p = matrixBits (fixedMatrix f hf) := by
  simp only [fixedMatrixProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.length_apply]
  change addMatrixBitsProg (frobeniusMatrixProg p, identityBits (unary p.length).length) = _
  rw [length_unary, hp, frobeniusMatrixProg_correct f hf p hp hpoly,
    identityBits_eq_matrixBits, addMatrixBitsProg_correct]
  rfl

/-- Print a bounded family spanning the quotient's complete Frobenius fixed space. -/
def fixedGeneratorsProg : PolyTimeFun BitStr (List BitStr) :=
  kernelGeneratorsProg.comp (PolyTimeFun.length.pair fixedMatrixProg)

/-- Abstract interpretation of the computed kernel generators in the quotient. -/
def fixedGenerator (j : Fin f.natDegree) : AdjoinRoot f :=
  (coordinateEquiv f hf).symm (kernelMap (fixedMatrix f hf) (Pi.single j 1))

/-- Every generated quotient element is idempotent. -/
theorem fixedGenerator_idempotent (j : Fin f.natDegree) :
    fixedGenerator f hf j * fixedGenerator f hf j = fixedGenerator f hf j := by
  apply (fixedMatrix_ker f hf _).mp
  rw [fixedGenerator, LinearEquiv.apply_symm_apply]
  exact kernelMap_mem_ker _ _

/-- All idempotents lie in the binary span of the computed generator family. -/
theorem fixedGenerator_spans (x : AdjoinRoot f) (hx : x * x = x) :
    x ∈ Submodule.span (ZMod 2) (Set.range (fixedGenerator f hf)) := by
  have hc := (fixedMatrix_ker f hf x).mpr hx
  rw [← kernel_generators_span] at hc
  have hm : x ∈ Submodule.map (coordinateEquiv f hf).symm.toLinearMap
      (Submodule.span (ZMod 2) (Set.range (fun j : Fin f.natDegree =>
        kernelMap (fixedMatrix f hf) (Pi.single j 1)))) :=
    Submodule.mem_map.mpr
      ⟨coordinateEquiv f hf x, hc, (coordinateEquiv f hf).symm_apply_apply x⟩
  rw [Submodule.map_span, ← Set.range_comp] at hm
  exact hm

/-- The program prints exactly the canonical coordinates of these generators. -/
theorem fixedGeneratorsProg_correct (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true])) :
    fixedGeneratorsProg p = List.ofFn (fun j => toBits f hf (fixedGenerator f hf j)) := by
  simp only [fixedGeneratorsProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.length_apply]
  rw [hp, fixedMatrixProg_correct f hf p hp hpoly, kernelGeneratorsProg_encoding]
  apply congrArg List.ofFn
  funext j
  rw [toBits_eq_vectorBits, fixedGenerator, LinearEquiv.apply_symm_apply]

end MIPRE.LowDegree.BinaryQuotient

end
