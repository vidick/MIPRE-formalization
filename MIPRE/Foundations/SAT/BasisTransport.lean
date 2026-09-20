/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.FieldCoordinates
import MIPRE.Foundations.LowDegree.BinaryMatrixInverse

/-! # Polynomial-time transport to any supplied binary field basis -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Columns of a new basis in the original, effective polynomial basis. -/
def shoupBasisMatrix (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  LinearMap.toMatrix b (shoupPowerBasis k hk) LinearMap.id

/-- The supplied basis vectors are exactly the columns of the change-of-basis matrix. -/
theorem shoupBasisMatrix_encoding (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    transposeBits k (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) =
      matrixBits (shoupBasisMatrix k hk b) := by
  have hc : List.ofFn (fun i => (shoupBinField k hk).toBits (b i)) =
      matrixBits (shoupBasisMatrix k hk b).transpose := by
    apply congrArg List.ofFn
    funext j
    rw [← shoupCoordinateEquiv_encoding]
    congr 1
    funext i
    exact (LinearMap.toMatrix_apply b (shoupPowerBasis k hk) LinearMap.id i j).symm
  rw [hc, transposeBits_matrixBits, Matrix.transpose_transpose]

/-- Matrix application sends the new coordinates to the original coordinates. -/
theorem shoupBasisMatrix_mulVec (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    (shoupBasisMatrix k hk b).mulVec (b.equivFun a) = shoupCoordinateEquiv k hk a :=
  LinearMap.toMatrix_mulVec_repr b (shoupPowerBasis k hk) LinearMap.id a

theorem shoupBasisMatrix_surjective (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    Function.Surjective (shoupBasisMatrix k hk b).mulVec := by
  intro v
  refine ⟨b.equivFun ((shoupCoordinateEquiv k hk).symm v), ?_⟩
  rw [shoupBasisMatrix_mulVec, LinearEquiv.apply_symm_apply]

/-- Read a field element in an arbitrary basis supplied as polynomial-basis vectors. -/
def shoupInBasisProg : PolyTimeFun (Unary × List BitStr × BitStr) BitStr :=
  matrixSolveProg.comp (PolyTimeFun.fst.pair
    ((transposeBitsProg.comp (PolyTimeFun.fst.pair (PolyTimeFun.fst.comp PolyTimeFun.snd))).pair
      (PolyTimeFun.snd.comp PolyTimeFun.snd)))

/-- The computed coordinates are exactly the mathematical basis coordinates. -/
theorem shoupInBasisProg_correct (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    shoupInBasisProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)),
      (shoupBinField k hk).toBits a) = vectorBits (b.equivFun a) := by
  change matrixSolveProg (unary k,
    transposeBits (unary k).length (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))),
    (shoupBinField k hk).toBits a) = _
  rw [length_unary, shoupBasisMatrix_encoding, ← shoupCoordinateEquiv_encoding,
    matrixSolveProg_encoding]
  congr 1
  have hi : Function.Injective (shoupBasisMatrix k hk b).mulVecLin :=
    LinearMap.injective_iff_surjective.mpr (shoupBasisMatrix_surjective k hk b)
  apply hi
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, matrixSolution_correct _ _
    (shoupBasisMatrix_surjective k hk b _), shoupBasisMatrix_mulVec]

/-- All multiplication-table bits, with the two basis indices as the first two list indices. -/
def shoupMultiplicationTableProg : PolyTimeFun (Unary × List BitStr) (List (List BitStr)) :=
  let entry : PolyTimeFun (BitStr × BitStr × Unary × List BitStr) BitStr :=
    let degree := PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)
    let basis := PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)
    let product := shoupMulProg.comp (degree.pair
      ((PolyTimeFun.fst.comp PolyTimeFun.snd).pair PolyTimeFun.fst))
    shoupInBasisProg.comp (degree.pair (basis.pair product))
  let row : PolyTimeFun (BitStr × Unary × List BitStr) (List BitStr) :=
    (PolyTimeFun.mapWith entry).comp
      ((PolyTimeFun.snd.comp PolyTimeFun.snd).pair (PolyTimeFun.id _))
  (PolyTimeFun.mapWith row).comp (PolyTimeFun.snd.pair (PolyTimeFun.id _))

/-- Table transport is correct for every supplied basis, including a self-dual normal basis. -/
theorem shoupMultiplicationTableProg_correct (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    shoupMultiplicationTableProg
      (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) =
      List.ofFn (fun i => List.ofFn (fun j => vectorBits (b.equivFun (b i * b j)))) := by
  change (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))).map (fun a =>
    (List.ofFn (fun j => (shoupBinField k hk).toBits (b j))).map (fun c =>
      shoupInBasisProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)),
        shoupMulProg (unary k, a, c)))) = _
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  change shoupInBasisProg (unary k, _, shoupMulProg (unary k,
    (shoupBinField k hk).toBits (b i), (shoupBinField k hk).toBits (b j))) = _
  rw [shoupMulProg_encoding, shoupInBasisProg_correct]

/-- A `k`-vector field basis has quadratic encoded size. -/
theorem esize_shoupBasis (k : ℕ) (hk : 1 ≤ k)
    (v : Fin k → (shoupBinField k hk).carrier) :
    esize (List.ofFn (fun i => (shoupBinField k hk).toBits (v i))) ≤ k * (4 * k + 2) + 1 := by
  have hsize (l : List BitStr) (hl : ∀ a ∈ l, a.length = k) :
      esize l ≤ l.length * (4 * k + 2) + 1 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha := esize_bitStr_le a
      rw [hl a (by simp)] at ha
      have ht := ih (fun x hx => hl x (by simp [hx]))
      rw [esize_list_cons, List.length_cons]
      nlinarith
  simpa using hsize (List.ofFn (fun i => (shoupBinField k hk).toBits (v i))) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (shoupBinField k hk).length_toBits (v i))

/-- Printing all `k³` table bits, including every solve, takes polynomial time in `k`. -/
theorem shoupMultiplicationTableProg_time_le : ∃ R : Polynomial ℕ, ∀ k : ℕ, ∀ hk : 1 ≤ k,
    ∀ b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier,
    ∃ t ≤ R.eval k, shoupMultiplicationTableProg.code.Runs
      (encode (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))
      (encode (shoupMultiplicationTableProg
        (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))) t := by
  refine ⟨shoupMultiplicationTableProg.timeBound.comp
    (4 * Polynomial.X ^ 2 + 4 * Polynomial.X + 3), fun k hk b => ?_⟩
  obtain ⟨t, ht, hr⟩ := shoupMultiplicationTableProg.computes
    (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)))
  refine ⟨t, ht.trans ?_, hr⟩
  have hs : esize (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) ≤
      4 * k ^ 2 + 4 * k + 3 := by
    rw [esize_prod, esize_unary]
    have h := esize_shoupBasis k hk b
    nlinarith
  simpa using polynomial_eval_mono shoupMultiplicationTableProg.timeBound hs

end MIPRE.SAT

end
