/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.PauliHideProg

@[expose] public section

/-!
# The Pauli constraints at unit vectors

A linear check's constraint vector (`LinCheck.toCon`) is its value at the unit vectors of the
answer bits, then its target (`toCon_eq_ofFn`); the `k` coordinate checks of a field equation
`E(z) = κ` are the coordinates of `E` at the unit vectors (`fieldChecks_toCon`). A unit vector is
the bit vector of a unit bit string (`bitVec_unitBits`), so its value under a check of
`PauliCons` is the check's expression on the two answers that string decodes to: `line_value`,
`pauli_value`, `prb_value`, `bitEq_value` evaluate the checks of the line, table, probe and
bit-equality rules on readings of the answers. This is what the programs of
`PauliConsProg` compute.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.PauliConsUnit

open Cost MIPRE.SAT MIPRE.LowDegree MIPRE.QLD MIPRE.QLD.PauliAnswerProgram
open MIPRE.Introspection.FieldTableProgram MIPRE.Tailored.Intro.PauliCons
open MIPRE.Tailored.Intro.PauliHideProg (unitV getv_unitV)
open MvPolynomial (eval)

variable {N : ℕ}

/-! ## Constraint vectors from unit evaluations -/

theorem toCon_eq_ofFn (χ : LinCheck N) :
    χ.toCon = (List.ofFn fun p => BinaryLinear.bit (χ.φ (unitV p))) ++
      [BinaryLinear.bit χ.c] := rfl

variable (k : ℕ) (hk : 1 ≤ k)

theorem bit_coord (x : (shoupBinField k hk).carrier) (s : Fin k) :
    BinaryLinear.bit (shoupCoordinateEquiv k hk x s) =
      ((shoupBinField k hk).toBits x).getD s false := by
  simp [shoupCoordinateEquiv_apply, BinaryLinear.vectorValue]

/-- The constraint vectors of a field equation: coordinate `s` of `E` at every unit vector. -/
theorem fieldChecks_toCon (E : (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField k hk).carrier)
    (κ : (shoupBinField k hk).carrier) :
    (fieldChecks k hk E κ).map LinCheck.toCon =
      List.ofFn fun s : Fin k =>
        (List.ofFn fun p : Fin N => ((shoupBinField k hk).toBits (E (unitV p))).getD s false) ++
          [((shoupBinField k hk).toBits κ).getD s false] := by
  simp only [fieldChecks, List.map_ofFn]
  apply congrArg List.ofFn
  funext s
  simp only [Function.comp_apply, toCon_eq_ofFn, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearMap.coe_proj, Function.eval, bit_coord]

theorem toBits_zero : (shoupBinField k hk).toBits 0 = List.replicate k false := by
  rw [PauliHideProg.toBits_eq_vectorBits, map_zero]
  apply List.ext_getElem (by simp [BinaryLinear.vectorBits])
  intro i h1 h2
  simp [BinaryLinear.vectorBits, BinaryLinear.bit]

theorem bitVec_unitBits (p : Fin N) : bitVec N (BinaryLinear.unitBits N p) = unitV p := by
  funext l
  simp only [bitVec, BinaryLinear.unitBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range l.2, Option.map_some, Option.getD_some, unitV]
  by_cases h : (l : ℕ) = p
  · simp [h, Fin.ext_iff, ofBool]
  · have : ¬p = l := fun e => h (by rw [e])
    simp [h, this, ofBool]

/-! ## The values of the checks -/

variable {k hk} {M : ℕ} (v : Fin N → ZMod 2)

theorem line_value {n : ℕ} {oP oL : ℕ} (τ : (shoupBinField k hk).carrier)
    {f : Fin (n + 1) → (shoupBinField k hk).carrier} {a : (shoupBinField k hk).carrier}
    (hP : fldAt k hk N oP v = a) (hL : ∀ i : Fin (n + 1), fldAt k hk N (oL + i * k) v = f i) :
    ((∑ i : Fin (n + 1), LinearMap.mulRight (ZMod 2) (τ ^ (i : ℕ)) ∘ₗ
        fldAt k hk N (oL + i * k)) - fldAt k hk N oP) v = (∑ i, f i * τ ^ (i : ℕ)) + a := by
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, hP, hL, CharTwo.sub_eq_add]

theorem pauli_value {oP oQ : ℕ} (y : Fin M → (shoupBinField k hk).carrier)
    {h : (Fin M → Bool) → (shoupBinField k hk).carrier} {a : (shoupBinField k hk).carrier}
    (hP : fldAt k hk N oP v = a)
    (hQ : ∀ z, fldAt k hk N (oQ + (cubeEnumeration M z : ℕ) * k) v = h z) :
    ((∑ z : Fin M → Bool, LinearMap.mulRight (ZMod 2)
        (eval y (ind z : MvPolynomial (Fin M) (shoupBinField k hk).carrier)) ∘ₗ
          fldAt k hk N (oQ + (cubeEnumeration M z : ℕ) * k)) - fldAt k hk N oP) v =
      eval y (ldEnc h) + a := by
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, hP, hQ, CharTwo.sub_eq_add, ldEnc, map_sum, map_mul,
    MvPolynomial.eval_C]

theorem prb_value (r : (shoupBinField k hk).carrier) {oP oB : ℕ}
    {a : (shoupBinField k hk).carrier} {b : ZMod 2}
    (hP : fldAt k hk N oP v = a) (hB : getv N oB v = b) :
    (prbCheck k hk N r oP oB).φ v = prb a r + b := by
  simp only [prbCheck, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, hP,
    hB, prb]

theorem bitEq_value {o o' : ℕ} {b b' : ZMod 2} (h : getv N o v = b) (h' : getv N o' v = b') :
    (bitEq N o o').φ v = b + b' := by
  simp only [bitEq, LinearMap.add_apply, h, h']

end MIPRE.Tailored.Intro.PauliConsUnit

end

end
