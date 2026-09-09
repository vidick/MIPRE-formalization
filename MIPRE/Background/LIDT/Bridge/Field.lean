/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DiagonalLine
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.AxisParallelLine
import Mathlib.FieldTheory.Finite.Basic

/-!
# Bridge, part 1: parameters and the field coding

The MIPStarRE development works with a coded field `Fq params := Fin params.q` together
with a `FieldModel params.q` instance carrying an actual field `K` and an equivalence
`K ≃ Fin q`; all arithmetic is transported through the coding (`encodeScalar`,
`decodeScalar`, `addCoord`, ...). This file instantiates that setup for our finite field
`F`: the parameters `lidtParams F m d` (with `q = Fintype.card F`) and the field model
with `K := F`, and it records how the coding interacts with points, lines and the
arithmetic of `F`.
-/

open MIPStarRE.LDT

noncomputable section

namespace MIPRE.LIDT.Bridge

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d : ℕ) [NeZero m]

/-- The MIPStarRE parameters of the `(m, q, d)` test, `q = |F|`. -/
abbrev lidtParams : Parameters where
  m := m
  q := Fintype.card F
  d := d
  hm := NeZero.pos m
  hq := Fintype.card_pos
  hqPrimePower := by
    obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' (K := F)
    exact ⟨p, n, hp, n.pos, hcard⟩

/-- The field model with carrier `F` itself, coded by an arbitrary enumeration. -/
instance fieldModel : FieldModel (Fintype.card F) where
  K := F
  instField := inferInstance
  instFintype := inferInstance
  instDecidableEq := inferInstance
  equiv := Fintype.equivFin F

variable {F m d}

/-! ## Coding of scalars and points -/

/-- Encode a scalar of `F` into the coded field of the parameters. -/
abbrev enc (x : F) : Fq (lidtParams F m d) := encodeScalar (params := lidtParams F m d) x

/-- Decode a coded scalar into `F`. -/
abbrev dec (x : Fq (lidtParams F m d)) : F := decodeScalar (params := lidtParams F m d) x

/-- Encode a point of `F^m`. -/
abbrev encP (u : Point F m) : MIPStarRE.LDT.Point (lidtParams F m d) := fun i => enc (u i)

/-- Decode a coded point. -/
abbrev decP (u : MIPStarRE.LDT.Point (lidtParams F m d)) : Point F m := fun i => dec (u i)

@[simp] theorem dec_enc (x : F) : dec (enc (m := m) (d := d) x) = x :=
  decode_encodeScalar (params := lidtParams F m d) x

@[simp] theorem enc_dec (x : Fq (lidtParams F m d)) : enc (dec x) = x :=
  encode_decodeScalar (params := lidtParams F m d) x

theorem enc_injective : Function.Injective (enc (F := F) (m := m) (d := d)) :=
  fun x y h => by simpa using congrArg dec h

theorem dec_injective : Function.Injective (dec (F := F) (m := m) (d := d)) :=
  fun x y h => by simpa using congrArg (enc (m := m) (d := d)) h

@[simp] theorem decP_encP (u : Point F m) : decP (encP (d := d) u) = u := by
  funext i; simp

@[simp] theorem encP_decP (u : MIPStarRE.LDT.Point (lidtParams F m d)) : encP (decP u) = u := by
  funext i; simp

/-- The coding of points, as an equivalence. -/
def pointEquiv : Point F m ≃ MIPStarRE.LDT.Point (lidtParams F m d) where
  toFun := encP
  invFun := decP
  left_inv := decP_encP
  right_inv := encP_decP

@[simp] theorem pointEquiv_apply (u : Point F m) : pointEquiv (d := d) u = encP u := rfl
@[simp] theorem pointEquiv_symm_apply (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    (pointEquiv (F := F) (m := m) (d := d)).symm u = decP u := rfl

/-- The coding of scalars, as an equivalence. -/
def scalarEquiv : F ≃ Fq (lidtParams F m d) where
  toFun := enc
  invFun := dec
  left_inv := dec_enc
  right_inv := enc_dec

@[simp] theorem scalarEquiv_apply (x : F) : scalarEquiv (m := m) (d := d) x = enc x := rfl
@[simp] theorem scalarEquiv_symm_apply (x : Fq (lidtParams F m d)) :
    (scalarEquiv (F := F) (m := m) (d := d)).symm x = dec x := rfl

@[simp] theorem decodePoint_eq (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    decodePoint (params := lidtParams F m d) u = decP u := rfl

/-! ## Arithmetic through the coding -/

@[simp] theorem dec_zeroCoord : dec (zeroCoord (params := lidtParams F m d)) = (0 : F) := by
  simp [zeroCoord]

@[simp] theorem dec_addCoord (x y : Fq (lidtParams F m d)) :
    dec (addCoord x y) = dec x + dec y := by
  simp [addCoord]

@[simp] theorem dec_mulCoord (x y : Fq (lidtParams F m d)) :
    dec (mulCoord x y) = dec x * dec y := by
  simp [mulCoord]

@[simp] theorem decP_addPoint (u v : MIPStarRE.LDT.Point (lidtParams F m d)) :
    decP (addPoint u v) = decP u + decP v := by
  funext i
  show dec (addCoord (u i) (v i)) = dec (u i) + dec (v i)
  exact dec_addCoord _ _

@[simp] theorem decP_smulPoint (t : Fq (lidtParams F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    decP (smulPoint t u) = dec t • decP u := by
  funext i
  show dec (mulCoord t (u i)) = dec t * dec (u i)
  exact dec_mulCoord _ _

@[simp] theorem decP_zeroPoint : decP (zeroPoint (params := lidtParams F m d)) = (0 : Point F m) := by
  funext i
  show dec zeroCoord = 0
  exact dec_zeroCoord

/-- The decoded point at parameter `t` of an axis-parallel line. -/
theorem decP_axis_pointAt (ℓ : AxisParallelLine (lidtParams F m d)) (t : Fq (lidtParams F m d)) :
    decP (ℓ.pointAt t) = decP ℓ.base + dec t • Pi.single ℓ.direction (1 : F) := by
  funext i
  by_cases h : i = ℓ.direction
  · show dec (if i = ℓ.direction then addCoord (ℓ.base i) t else ℓ.base i) = _
    simp [h]
  · show dec (if i = ℓ.direction then addCoord (ℓ.base i) t else ℓ.base i) = _
    simp [h]

/-- The decoded point at parameter `t` of a diagonal line. -/
theorem decP_diag_pointAt (ℓ : DiagonalLine (lidtParams F m d)) (t : Fq (lidtParams F m d)) :
    decP (ℓ.pointAt t) = decP ℓ.base + dec t • decP ℓ.direction := by
  show decP (addPoint ℓ.base (smulPoint t ℓ.direction)) = _
  rw [decP_addPoint, decP_smulPoint]

end MIPRE.LIDT.Bridge

end
