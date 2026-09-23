/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.FieldIndicatorProg
import MIPRE.Foundations.SAT.FmlProg

/-! # Evaluating a faithfully ordered full Pauli answer

The answer table is ordered by the little-endian binary rank of its Boolean
cube argument. The evaluator scans only the supplied rows, so even a malformed
short answer is processed in polynomial time. On a full canonical table it
computes the low-degree encoding at an arbitrary field point.
-/

noncomputable section
namespace MIPRE.Introspection.FieldTableProgram
open Cost Cost.PolyTimeFun SAT LowDegree FieldIndicatorProgram

/-- The standard little-endian rank of a Boolean cube point. -/
def cubeIndex {m : ℕ} (y : Fin m → Bool) : Fin (2 ^ m) :=
  ⟨bitsVal (List.ofFn y), by simpa using bitsVal_lt (List.ofFn y)⟩

theorem cubeIndex_injective (m : ℕ) : Function.Injective (@cubeIndex m) := by
  intro y z h
  apply List.ofFn_injective
  exact bitsVal_injective (by simp) (congrArg Fin.val h)

/-- A faithful cube enumeration; finite choice is used only for its inverse. -/
def cubeEnumeration (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  Equiv.ofBijective cubeIndex
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨cubeIndex_injective m, by simp⟩)

theorem cubeEnumeration_bits {m : ℕ} (y : Fin m → Bool) :
    padBits m (cubeEnumeration m y).val.bits = List.ofFn y := by
  apply bitsVal_injective
  · rw [length_padBits, List.length_ofFn]
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (cubeEnumeration m y).isLt
  · rw [bitsVal_padBits, bitsVal_bits]
    rfl

theorem cubeEnumeration_symm_bits {m : ℕ} (i : Fin (2 ^ m)) :
    padBits m i.val.bits = List.ofFn (cubeEnumeration m |>.symm i) := by
  simpa using cubeEnumeration_bits ((cubeEnumeration m).symm i)

/-- One supplied answer row, weighted by the indicator at its binary index. -/
def termProg : PolyTimeFun ((BitStr × ℕ) × (Unary × List BitStr)) BitStr :=
  let row := fst.comp fst
  let index := snd.comp fst
  let width := fst.comp snd
  let point := snd.comp snd
  let cube := padP.comp ((length.comp point).pair (natBits.comp index))
  let weight := indicatorProg.comp (width.pair (zip.comp (point.pair cube)))
  shoupMulProg.comp (width.pair (row.pair weight))

theorem termProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Fin m → (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) (i : Fin (2 ^ m)) :
    termProg (((shoupBinField k hk).toBits a, i.val),
      (unary k, List.ofFn fun j => (shoupBinField k hk).toBits (x j))) =
      (shoupBinField k hk).toBits (a * indVec x ((cubeEnumeration m).symm i)) := by
  have hzip :
      (List.ofFn fun j => (shoupBinField k hk).toBits (x j)).zip
        (List.ofFn ((cubeEnumeration m).symm i)) =
      List.ofFn (fun j => ((shoupBinField k hk).toBits (x j),
        (cubeEnumeration m).symm i j)) := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp
  simp only [termProg, comp_apply, pair_apply, fst_apply, snd_apply,
    length_apply, natBits_apply, padP_apply, zip_apply, length_unary, List.length_ofFn]
  rw [cubeEnumeration_symm_bits, hzip, indicatorProg_indVec, shoupMulProg_encoding]

/-- Width, evaluation point, and supplied answer rows. The range is bounded by
the actual answer length, not by a binary size claimed in the answer. -/
def tableProg : PolyTimeFun (Unary × List BitStr × List BitStr) BitStr :=
  let rows := snd.comp snd
  let indices := range'P.comp ((const 0).pair (length.comp rows))
  let entries := zip.comp (rows.pair indices)
  let terms := (mapWith termProg).comp
    (entries.pair (fst.pair (fst.comp snd)))
  shoupSumProg.comp (fst.pair terms)

theorem tableProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Fin m → (shoupBinField k hk).carrier)
    (h : (Fin m → Bool) → (shoupBinField k hk).carrier) :
    tableProg (unary k, List.ofFn (fun j => (shoupBinField k hk).toBits (x j)),
      List.ofFn (fun i : Fin (2 ^ m) =>
        (shoupBinField k hk).toBits (h ((cubeEnumeration m).symm i)))) =
      (shoupBinField k hk).toBits (MvPolynomial.eval x (ldEnc h)) := by
  classical
  have hzip :
      (List.ofFn fun i : Fin (2 ^ m) =>
        (shoupBinField k hk).toBits (h ((cubeEnumeration m).symm i))).zip
        (List.range' 0 (2 ^ m)) =
      List.ofFn (fun i : Fin (2 ^ m) =>
        ((shoupBinField k hk).toBits (h ((cubeEnumeration m).symm i)), i.val)) := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp
  simp only [tableProg, comp_apply, pair_apply, fst_apply, snd_apply,
    range'P_apply, length_apply, length_unary, List.length_ofFn, zip_apply,
    mapWith_apply, const_apply, hzip, List.map_ofFn, Function.comp_def]
  simp only [termProg_correct]
  have hsum := shoupSumProg_correct k hk
    (List.ofFn fun i : Fin (2 ^ m) =>
      h ((cubeEnumeration m).symm i) * indVec x ((cubeEnumeration m).symm i))
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn] at hsum
  rw [hsum]
  congr 1
  rw [ldEnc, map_sum]
  simp only [map_mul, MvPolynomial.eval_C]
  exact (Equiv.sum_comp (cubeEnumeration m).symm
    (fun y => h y * indVec x y))

/-- A single ambient polynomial bounds the evaluator on every raw input. -/
theorem tableProg_runs (input : Unary × List BitStr × List BitStr) :
    ∃ t ≤ tableProg.timeBound.eval (esize input),
      tableProg.code.Runs (encode input) (encode (tableProg input)) t :=
  tableProg.computes input

end MIPRE.Introspection.FieldTableProgram
end
