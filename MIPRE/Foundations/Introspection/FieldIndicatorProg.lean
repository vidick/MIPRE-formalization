/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.NormalElementProg
import MIPRE.Foundations.SAT.TraceGram
import MIPRE.Foundations.LowDegree.Anticomm

/-! # Executable multilinear indicator weights

A full Pauli outcome is evaluated by weighting each field entry by its Boolean
cube indicator. This module supplies the uniform weight program, including its
exact connection to `LowDegree.indVec`. No field values or cube points are
tabulated by the program: it scans the supplied coordinate/bit pairs.
-/

noncomputable section
namespace MIPRE.Introspection.FieldIndicatorProgram
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryPolynomial SAT

/-- Modular multiplication of canonical field rows computes their product. -/
theorem shoupArithmeticFold_mul_correct (k : ℕ) (hk : 1 ≤ k)
    (values : List (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) :
    arithmeticFold true (shoupLowerCoeffs (unary k)) ((shoupBinField k hk).toBits a)
      (values.map (shoupBinField k hk).toBits) =
      (shoupBinField k hk).toBits (a * values.prod) := by
  induction values generalizing a with
  | nil => simp [arithmeticFold]
  | cons b values ih =>
    rw [List.map_cons, arithmeticFold_cons]
    change arithmeticFold true (shoupLowerCoeffs (unary k))
      (shoupMulProg (unary k, (shoupBinField k hk).toBits a, (shoupBinField k hk).toBits b))
      (values.map (shoupBinField k hk).toBits) = _
    rw [shoupMulProg_encoding, ih, List.prod_cons, mul_assoc]

/-- `x` for a true cube coordinate, and `1-x` for a false coordinate. -/
def factorProg : PolyTimeFun (BitStr × Bool) BitStr :=
  ite snd fst (xorBitsProg.comp ((oneBitsProg.comp fst).pair fst))

theorem factorProg_correct (k : ℕ) (hk : 1 ≤ k)
    (x : (shoupBinField k hk).carrier) (b : Bool) :
    factorProg ((shoupBinField k hk).toBits x, b) =
      (shoupBinField k hk).toBits (if b then x else 1 - x) := by
  cases b with
  | true => rfl
  | false =>
    change xorBits (oneBits ((shoupBinField k hk).toBits x))
      ((shoupBinField k hk).toBits x) = _
    rw [shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits x),
      shoupXorBits_correct, CharTwo.sub_eq_add]
    rfl

/-- The field modulus is computed once for the entire coordinate product. -/
def indicatorProg : PolyTimeFun (Unary × List (BitStr × Bool)) BitStr :=
  (arithmeticFoldProg true).comp
    ((shoupLowerCoeffs.comp fst).pair
      ((oneBitsProg.comp (shoupZeroProg.comp fst)).pair ((map factorProg).comp snd)))

theorem indicatorProg_correct (k : ℕ) (hk : 1 ≤ k)
    (coords : List ((shoupBinField k hk).carrier × Bool)) :
    indicatorProg (unary k, coords.map (fun p => ((shoupBinField k hk).toBits p.1, p.2))) =
      (shoupBinField k hk).toBits ((coords.map (fun p => if p.2 then p.1 else 1 - p.1)).prod) := by
  have hmap :
      (coords.map (fun p => ((shoupBinField k hk).toBits p.1, p.2))).map factorProg =
      (coords.map (fun p => if p.2 then p.1 else 1 - p.1)).map (shoupBinField k hk).toBits := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    exact factorProg_correct k hk p.1 p.2
  change arithmeticFold true (shoupLowerCoeffs (unary k))
    (oneBits (shoupZeroProg (unary k)))
    ((coords.map (fun p => ((shoupBinField k hk).toBits p.1, p.2))).map factorProg) = _
  rw [hmap, shoupZeroProg_correct k hk,
    shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits 0),
    shoupArithmeticFold_mul_correct, one_mul]

/-- Exact indicator semantics at an arbitrary field point, not only on the cube. -/
theorem indicatorProg_indVec (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Fin m → (shoupBinField k hk).carrier) (y : Fin m → Bool) :
    indicatorProg (unary k, List.ofFn (fun i => ((shoupBinField k hk).toBits (x i), y i))) =
      (shoupBinField k hk).toBits (indVec x y) := by
  have h := indicatorProg_correct k hk (List.ofFn fun i => (x i, y i))
  simpa only [List.map_ofFn, List.prod_ofFn, indVec_apply, Function.comp_def] using h

/-- The raw indicator program has one ambient input-size polynomial. -/
theorem indicatorProg_runs (input : Unary × List (BitStr × Bool)) :
    ∃ t ≤ indicatorProg.timeBound.eval (esize input),
      indicatorProg.code.Runs (encode input) (encode (indicatorProg input)) t :=
  indicatorProg.computes input

end MIPRE.Introspection.FieldIndicatorProgram
end
