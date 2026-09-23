/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.FieldIndicatorProg

/-! # Computing the Pauli commutation bit

The dot product of the two exponentially long indicator vectors factors as a
product over the supplied coordinates. The program uses this product, followed
by the field trace, and never constructs either indicator vector.
-/

noncomputable section
namespace MIPRE.Introspection.FieldGammaProgram
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryPolynomial
  LowDegree.BinaryLinear FieldIndicatorProgram

theorem indPair_eq_prod {K : Type*} [CommRing K] {m : ℕ} (x z : Fin m → K) :
    indPair x z = ∏ i, ((1 - x i) * (1 - z i) + x i * z i) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset Bool))
    (fun i b => (if b then x i else 1 - x i) * (if b then z i else 1 - z i))
  rw [Fintype.piFinset_univ] at h
  have hsum : ∀ i : Fin m,
      (∑ b : Bool, (if b then x i else 1 - x i) * (if b then z i else 1 - z i)) =
      (1 - x i) * (1 - z i) + x i * z i := by
    intro i
    simp [add_comm]
  rw [Finset.prod_congr rfl fun i _ => hsum i] at h
  rw [indPair]
  rw [Finset.sum_congr rfl fun y _ => by
    rw [indVec_apply, indVec_apply, ← Finset.prod_mul_distrib]]
  exact h.symm

theorem indPair_eq_prod_charTwo {K : Type*} [CommRing K] [CharP K 2]
    {m : ℕ} (x z : Fin m → K) : indPair x z = ∏ i, (1 + x i + z i) := by
  rw [indPair_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [CharTwo.sub_eq_add]
  calc
    (1 + x i) * (1 + z i) + x i * z i =
        1 + x i + z i + (x i * z i + x i * z i) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

def pairFactorProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  xorBitsProg.comp
    ((xorBitsProg.comp ((oneBitsProg.comp fst).pair fst)).pair snd)

theorem pairFactorProg_correct (k : ℕ) (hk : 1 ≤ k)
    (x z : (shoupBinField k hk).carrier) :
    pairFactorProg ((shoupBinField k hk).toBits x, (shoupBinField k hk).toBits z) =
      (shoupBinField k hk).toBits (1 + x + z) := by
  change xorBits (xorBits (oneBits ((shoupBinField k hk).toBits x))
    ((shoupBinField k hk).toBits x)) ((shoupBinField k hk).toBits z) = _
  rw [shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits x),
    shoupXorBits_correct, shoupXorBits_correct]

def pairingProg : PolyTimeFun (Unary × List (BitStr × BitStr)) BitStr :=
  (arithmeticFoldProg true).comp
    ((shoupLowerCoeffs.comp fst).pair
      ((oneBitsProg.comp (shoupZeroProg.comp fst)).pair ((map pairFactorProg).comp snd)))

theorem pairingProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x z : Fin m → (shoupBinField k hk).carrier) :
    pairingProg (unary k,
      List.ofFn fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (z i))) =
      (shoupBinField k hk).toBits (indPair x z) := by
  have hmap :
      (List.ofFn fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (z i))).map pairFactorProg =
      (List.ofFn fun i => 1 + x i + z i).map (shoupBinField k hk).toBits := by
    simp only [List.map_ofFn, Function.comp_def, pairFactorProg_correct]
  change arithmeticFold true (shoupLowerCoeffs (unary k))
    (oneBits (shoupZeroProg (unary k)))
    ((List.ofFn fun i => ((shoupBinField k hk).toBits (x i),
      (shoupBinField k hk).toBits (z i))).map pairFactorProg) = _
  rw [hmap, shoupZeroProg_correct k hk,
    shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits 0),
    shoupArithmeticFold_mul_correct, one_mul, List.prod_ofFn, indPair_eq_prod_charTwo]

/-- Width, coordinate pairs, and the two scalar probe multipliers. -/
def gammaProg : PolyTimeFun (Unary × List (BitStr × BitStr) × BitStr × BitStr) Bool :=
  let width := fst
  let pairing := pairingProg.comp (width.pair (fst.comp snd))
  let scalars := shoupMulProg.comp (width.pair (snd.comp snd))
  let value := shoupMulProg.comp (width.pair (scalars.pair pairing))
  shoupTraceBitProg.comp (width.pair value)

theorem gammaProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x z : Fin m → (shoupBinField k hk).carrier)
    (rX rZ : (shoupBinField k hk).carrier) :
    gammaProg (unary k,
      List.ofFn (fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (z i))),
      (shoupBinField k hk).toBits rX, (shoupBinField k hk).toBits rZ) =
      bit (acGamma (ZMod 2) x z rX rZ) := by
  simp only [gammaProg, comp_apply, pair_apply, fst_apply, snd_apply]
  rw [pairingProg_correct, shoupMulProg_encoding, shoupMulProg_encoding,
    shoupTraceBitProg_correct]
  rfl

theorem gammaProg_runs (input : Unary × List (BitStr × BitStr) × BitStr × BitStr) :
    ∃ t ≤ gammaProg.timeBound.eval (esize input),
      gammaProg.code.Runs (encode input) (encode (gammaProg input)) t :=
  gammaProg.computes input

/-- The two-outcome scalar probe used by the point consistency rules. -/
def probeProg : PolyTimeFun (Unary × BitStr × BitStr) Bool :=
  shoupTraceBitProg.comp (fst.pair shoupMulProg)

theorem probeProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a r : (shoupBinField k hk).carrier) :
    probeProg (unary k, (shoupBinField k hk).toBits a, (shoupBinField k hk).toBits r) =
      bit (Algebra.trace (ZMod 2) (shoupBinField k hk).carrier (a * r)) := by
  change shoupTraceBitProg (unary k, shoupMulProg
    (unary k, (shoupBinField k hk).toBits a, (shoupBinField k hk).toBits r)) = _
  rw [shoupMulProg_encoding, shoupTraceBitProg_correct]

end MIPRE.Introspection.FieldGammaProgram
end
