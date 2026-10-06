/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArRoutine
public import MIPRE.Background.Tailored.Intro.PauliConsUnit
public import MIPRE.Tailored.AnsRed.IndicatorProg
public import MIPRE.Foundations.Introspection.FieldLineCheckProg

@[expose] public section

/-!
# Field equations as constraints, as programs

Slice P4h of `planning/aldous-lyons-track.md`: the generic part of the answer-reduced verifier's
linear-constraints processor. Every check of the answer-reduced game is a list of field equations
`E(z) = κ` over `F_{2^t}` on the answer bits `z`, each giving `t` constraints (`eqsCons`): the
coordinates of `E` at the unit vectors of the bits, then those of `κ` (`fieldChecks_toCon`).
A program computing `E(z)` for every `z` therefore computes the constraints, by running on the unit
vectors and transposing (`fieldConsF`, `fieldConsF_eq`); `eqsConsF` does it for an indexed list of
equations (`eqsConsF_eq`). This is how the introspection stage computes its Pauli constraints
(`MIPRE.Tailored.Intro.PauliConsProg.fieldCons`), here with targets.

A field element in the answer bits is a window of `t` bits (`window`, `toBits_elt`), read by
`windowF`.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.Tailored.Intro

variable {t : ℕ} {ht : 1 ≤ t}

/-! ## Windows -/

/-- **The `t` bits of a string from position `o`**, bits beyond the string read as `0`. -/
def window (z : BitStr) (o t : ℕ) : BitStr := List.ofFn fun i : Fin t => z.getD (o + i) false

@[simp] theorem length_window (z : BitStr) (o t : ℕ) : (window z o t).length = t := by
  simp [window]

/-- **The bits of the field element at position `o`** are the window there. -/
theorem toBits_elt (z : BitStr) (o : ℕ) :
    (shoupBinField t ht).toBits (elt t ht z o) = window z o t := by
  rw [PauliHideProg.toBits_eq_vectorBits, elt, LinearEquiv.apply_symm_apply]
  simp only [BinaryLinear.vectorBits, BinaryLinear.bit_ofBool, window]

/-- The window program, on `(t, o, z)` with `t` and `o` in unary. -/
def windowF : PolyTimeFun (Unary × Unary × BitStr) BitStr :=
  take.comp ((append.comp ((drop.comp ((snd.comp snd).pair (fst.comp snd))).pair
    (replicate.comp (fst.pair (const false))))).pair fst)

theorem windowF_apply (t o : ℕ) (z : BitStr) : windowF (unary t, unary o, z) = window z o t := by
  simp only [windowF, comp_apply, pair_apply, fst_apply, snd_apply, take_apply, drop_apply,
    append_apply, replicate_apply, const_apply, length_unary]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [length_window] at h2
  simp only [List.getElem_take, window, List.getElem_ofFn, List.getD_eq_getElem?_getD]
  by_cases h : o + i < z.length
  · rw [List.getElem_append_left (by simp; omega), List.getElem_drop,
      List.getElem?_eq_getElem h, Option.getD_some]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate,
      List.getElem?_eq_none (by omega), Option.getD_none]

/-! ## Constraints from values at the unit vectors -/

section Cons

variable {I : Type} [SizedEncoding I]

/-- **The constraints of a field equation**, from a program computing its value at every string
of answer bits and one computing its target: coordinate `s` of the values at the `N` unit
vectors, then coordinate `s` of the target, for `s < t`. -/
def fieldConsF (uT uN : PolyTimeFun I Unary) (val : PolyTimeFun (I × BitStr) BitStr)
    (κ : PolyTimeFun I BitStr) : PolyTimeFun I (List BitStr) :=
  let rows := BinaryLinear.transposeBitsProg.comp (uT.pair ((mapWith (val.comp (snd.pair fst))).comp
    ((BinaryLinear.identityBitsProg.comp uN).pair (PolyTimeFun.id _))))
  (map (append.comp (fst.pair (PolyTimeFun.cons snd (const []))))).comp (zip.comp (rows.pair κ))

theorem range_map_unitBits (N : ℕ) (g : BitStr → BitStr) :
    (BinaryLinear.identityBits N).map g =
      List.ofFn fun p : Fin N => g (BinaryLinear.unitBits N p) := by
  apply List.ext_getElem (by simp [BinaryLinear.identityBits])
  intro i h1 h2
  simp [BinaryLinear.identityBits]

/-- **A program of the values of a field equation computes its constraints.** -/
theorem fieldConsF_eq (uT uN : PolyTimeFun I Unary) (val : PolyTimeFun (I × BitStr) BitStr)
    (κ : PolyTimeFun I BitStr) {inp : I} {N : ℕ} (hT : uT inp = unary t)
    (hN : uN inp = unary N) (E : (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier)
    (c : (shoupBinField t ht).carrier)
    (hval : ∀ z : BitStr, z.length = N →
      val (inp, z) = (shoupBinField t ht).toBits (E (Intro.bitVec N z)))
    (hκ : κ inp = (shoupBinField t ht).toBits c) :
    fieldConsF uT uN val κ inp = (fieldChecks t ht E c).map LinCheck.toCon := by
  rw [PauliConsUnit.fieldChecks_toCon]
  have hu : ∀ p : Fin N, val (inp, BinaryLinear.unitBits N p) =
      (shoupBinField t ht).toBits (E (PauliHideProg.unitV p)) := by
    intro p
    rw [hval _ (by simp [BinaryLinear.unitBits]), PauliConsUnit.bitVec_unitBits]
  simp only [fieldConsF, comp_apply, pair_apply, id_apply, mapWith_apply, hT, hN, hκ,
    BinaryLinear.identityBitsProg, congr_apply, length_unary, fst_apply, snd_apply,
    BinaryLinear.transposeBitsProg_apply, zip_apply, map_apply]
  rw [range_map_unitBits N (fun u => val (inp, u))]
  simp only [hu, BinaryLinear.transposeBits]
  apply List.ext_getElem (by simp [BinField.length_toBits])
  intro s h1 h2
  simp only [List.length_ofFn] at h2
  have hs : s < ((shoupBinField t ht).toBits c).length := by
    rw [BinField.length_toBits]; exact h2
  simp only [List.getElem_map, List.getElem_zip, List.getElem_range, List.getElem_ofFn,
    comp_apply, pair_apply, append_apply, fst_apply, snd_apply, cons_apply, const_apply,
    List.map_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some]
  rfl

/-- **The constraints of an indexed list of field equations**: those of each equation, in the
order of the indices. -/
def eqsConsF {J : Type} [SizedEncoding J] (uT uN : PolyTimeFun I Unary)
    (idx : PolyTimeFun I (List J)) (val : PolyTimeFun ((J × I) × BitStr) BitStr)
    (κ : PolyTimeFun (J × I) BitStr) : PolyTimeFun I (List BitStr) :=
  flatMapR (fieldConsF (uT.comp snd) (uN.comp snd) val κ) idx

/-- **Programs of the values of indexed field equations compute their constraints.** -/
theorem eqsConsF_eq {J : Type} [SizedEncoding J] (uT uN : PolyTimeFun I Unary)
    (idx : PolyTimeFun I (List J)) (val : PolyTimeFun ((J × I) × BitStr) BitStr)
    (κ : PolyTimeFun (J × I) BitStr) {inp : I} {N : ℕ} (hT : uT inp = unary t)
    (hN : uN inp = unary N) {is : List J} (hidx : idx inp = is)
    (E : J → (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier)
    (c : J → (shoupBinField t ht).carrier)
    (hval : ∀ i ∈ is, ∀ z : BitStr, z.length = N →
      val ((i, inp), z) = (shoupBinField t ht).toBits (E i (Intro.bitVec N z)))
    (hκ : ∀ i ∈ is, κ (i, inp) = (shoupBinField t ht).toBits (c i)) :
    eqsConsF uT uN idx val κ inp = eqsCons t ht (is.map fun i => (E i, c i)) := by
  simp only [eqsConsF, flatMapR_apply, hidx, eqsCons, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro i hi
  exact fieldConsF_eq _ _ val κ (by simpa using hT) (by simpa using hN) (E i) (c i)
    (hval i hi) (hκ i hi)

end Cons

end MIPRE.Tailored.AnsRed.Typed

end
