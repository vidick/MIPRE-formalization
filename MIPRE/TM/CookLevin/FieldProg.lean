/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.LayoutProg

/-!
# The fields of a literal, as programs

`FieldsR ι` is a record of *readers*: one program per field of `FieldsF`, all of them reading
the same input `ι`. `FieldsR.ev A i` is the field record its programs produce on the input
`i`, and it is a structure literal whose components are, definitionally, the values of those
programs — so every formula built from a `FieldsR` matches the same formula built from
`FieldsR.ev` by `rfl`, and the whole family of programs of `FamilyProg.lean` costs one `rfl`
each.

`litFieldsR` is the record of programs for `litFields`: the one place where the constants of
the layout have to be produced, and the only proof in the program layer that is not
definitional (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## Records of readers -/

variable {ι : Type*} [SizedEncoding ι]

/-- A field record of programs, all reading the same input. -/
structure FieldsR (ι : Type*) [SizedEncoding ι] where
  flag : PolyTimeFun ι Fml
  tag : PolyTimeFun ι (List Fml)
  t : PolyTimeFun ι (List Fml)
  d : PolyTimeFun ι (List Fml)
  p : PolyTimeFun ι (List Fml)
  v : PolyTimeFun ι (List Fml)
  q : PolyTimeFun ι (List Fml)
  js : Fin 13 → PolyTimeFun ι (List Fml)
  g : PolyTimeFun ι (List Fml)
  ansOk : PolyTimeFun ι Fml

/-- The field record the programs produce on an input. -/
def FieldsR.ev (A : FieldsR ι) (i : ι) : FieldsF :=
  ⟨A.flag i, A.tag i, A.t i, A.d i, A.p i, A.v i, A.q i, fun k => A.js k i, A.g i, A.ansOk i⟩

/-- A candidate of programs. -/
structure CandR (ι : Type*) [SizedEncoding ι] where
  A₁ : FieldsR ι
  σ₁ : PolyTimeFun ι Fml
  A₂ : FieldsR ι
  σ₂ : PolyTimeFun ι Fml
  A₃ : FieldsR ι
  σ₃ : PolyTimeFun ι Fml

/-- The candidate the programs produce on an input. -/
def CandR.ev (C : CandR ι) (i : ι) : CandF :=
  ⟨C.A₁.ev i, C.σ₁ i, C.A₂.ev i, C.σ₂ i, C.A₃.ev i, C.σ₃ i⟩

/-! ## The constants of the layout -/

theorem cstR_zero (w : PolyTimeFun ι Unary) (i : ι) :
    cstR w (bitsR 0) i = cst (w i).length 0 := cstR_apply 0 (bitsR_spec 0 i)

theorem cstR_const (w : PolyTimeFun ι Unary) (k : ℕ) (i : ι) :
    cstR w (bitsR k) i = cst (w i).length k := cstR_apply k (bitsR_spec k i)

theorem nbitsR_const (w : PolyTimeFun ι Unary) (k : ℕ) (i : ι) :
    nbitsR w (bitsR k) i = nbits (w i).length k := nbitsR_apply k (bitsR_spec k i)

/-- Twice a number, as a bit string. -/
noncomputable def dblR (T : PolyTimeFun ι ℕ) : PolyTimeFun ι BitStr :=
  ap₁ dblP (ap₁ natBits T)

theorem dblR_spec (T : PolyTimeFun ι ℕ) (i : ι) :
    ∀ j, (dblR T i).getD j false = (2 * T i).testBit j :=
  getD_false_cons _ _ (getD_bits (T i))

/-- Four times a number, as a bit string. -/
noncomputable def quadR (T : PolyTimeFun ι ℕ) : PolyTimeFun ι BitStr := ap₁ dblP (dblR T)

theorem quadR_spec (T : PolyTimeFun ι ℕ) (i : ι) :
    ∀ j, (quadR T i).getD j false = (4 * T i).testBit j := by
  intro j
  have h := getD_false_cons _ _ (dblR_spec T i) j
  rw [show 2 * (2 * T i) = 4 * T i by ring] at h
  exact h

/-! ## The fields of a literal -/

section Lit

variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)

/-- An index into a field, from an offset in unary. -/
noncomputable def offR (o : PolyTimeFun ι Unary) : PolyTimeFun ι ℕ :=
  ap₁ unaryToBin (ap₂ addU b o)

@[simp] theorem offR_apply (o : PolyTimeFun ι Unary) (i : ι) :
    offR b o i = (b i).length + (o i).length := by
  rw [offR, ap₁_apply, ap₂_apply, unaryToBin_apply, length_addU]

/-- `flagF`. -/
noncomputable def flagR : PolyTimeFun ι Fml := ap₁ Fml.inpF (offR b (flagOffU eu))

theorem flagR_apply (i : ι) : flagR eu b i = flagF (eu i).length Gc (b i).length := by
  rw [flagR, ap₁_apply, Fml.inpF_apply, offR_apply, length_flagOffU, flagF]

/-- `jF`. -/
noncomputable def jR : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin b) (flagOffU eu)

theorem jR_apply (i : ι) : jR eu b i = jF (eu i).length Gc (b i).length := by
  rw [jR, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, length_flagOffU, jF]

/-- `twoTb`. -/
noncomputable def twoTbR : PolyTimeFun ι BitStr := nbitsR (flagOffU eu) (dblR TR)

theorem twoTbR_apply (i : ι) : twoTbR eu TR i = twoTb (eu i).length Gc (TR i) := by
  rw [twoTbR, nbitsR_apply _ (dblR_spec TR i), length_flagOffU, twoTb]

/-- `lt2TF`. -/
noncomputable def lt2TR : PolyTimeFun ι Fml := ap₂ ltConstP (jR eu b) (twoTbR eu TR)

theorem lt2TR_apply (i : ι) : lt2TR eu TR b i = lt2TF (eu i).length Gc (TR i) (b i).length := by
  rw [lt2TR, ap₂_apply, ltConstP_apply, jR_apply, twoTbR_apply, lt2TF]

/-- `rF`. -/
noncomputable def rR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (lt2TR eu TR b) (jR eu b) (ap₂ subConstBitsP (jR eu b) (twoTbR eu TR))

theorem rR_apply (i : ι) : rR eu TR b i = rF (eu i).length Gc (TR i) (b i).length := by
  rw [rR, ap₃_apply, muxListP_apply, ap₂_apply, subConstBitsP_apply, lt2TR_apply, jR_apply,
    twoTbR_apply, rF]

/-- `pAnsF`. -/
noncomputable def pAnsR : PolyTimeFun ι (List Fml) :=
  ap₂ addConstBitsP (ap₂ take (ap₁ tail (rR eu TR b)) (WU eu)) (nbitsR (WU eu) (bitsR 3))

theorem pAnsR_apply (i : ι) : pAnsR eu TR b i = pAnsF (eu i).length Gc (TR i) (b i).length := by
  rw [pAnsR, ap₂_apply, addConstBitsP_apply, ap₂_apply, take_apply, ap₁_apply, tail_apply,
    rR_apply, nbitsR_const, length_WU, pAnsF]

/-! ### The ten fields -/

/-- The `tag` field. -/
noncomputable def tagR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (ap₁ unaryToBin b) threeU) (cstR threeU (bitsR 0))

theorem tagR_apply (i : ι) : tagR eu b i =
    muxList (flagF (eu i).length Gc (b i).length) (Fml.field ((b i).length + tagOff) 3)
      (cst 3 0) := by
  simp only [tagR, ap₃_apply, muxListP_apply, ap₂_apply, ap₁_apply, fieldP_apply,
    unaryToBin_apply, cstR_zero, length_threeU, flagR_apply, tagOff, Nat.add_zero]

/-- The `t` field. -/
noncomputable def tR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b threeU) (WU eu)) (cstR (WU eu) (bitsR 0))

theorem tR_apply (i : ι) : tR eu b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + tOff) (W (eu i).length)) (cst (W (eu i).length) 0) := by
  simp only [tR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_threeU, length_WU, flagR_apply, tOff]

/-- The `d` field. -/
noncomputable def dR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (dOffU eu)) fourU)
    (ap₃ muxListP (lt2TR eu TR b) (cstR fourU (bitsR 5)) (cstR fourU (bitsR 6)))

theorem dR_apply (i : ι) : dR eu TR b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + dOff (eu i).length) 4)
      (muxList (lt2TF (eu i).length Gc (TR i) (b i).length) (cst 4 5) (cst 4 6)) := by
  simp only [dR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_const,
    length_fourU, length_dOffU, flagR_apply, lt2TR_apply]

/-- The `p` field. -/
noncomputable def pR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (pOffU eu)) (WU eu)) (pAnsR eu TR b)

theorem pR_apply (i : ι) : pR eu TR b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + pOff (eu i).length) (W (eu i).length))
      (pAnsF (eu i).length Gc (TR i) (b i).length) := by
  simp only [pR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, length_WU,
    length_pOffU, flagR_apply, pAnsR_apply]

/-- The `v` field. -/
noncomputable def vR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (vOffU eu)) threeU)
    (ap₃ muxListP (ap₁ (headD (Fml.const false)) (rR eu TR b)) (cstR threeU (bitsR 1))
      (cstR threeU (bitsR 5)))

theorem vR_apply (i : ι) : vR eu TR b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + vOff (eu i).length) 3)
      (muxList ((rF (eu i).length Gc (TR i) (b i).length).headD (Fml.const false)) (cst 3 1)
        (cst 3 5)) := by
  simp only [vR, ap₃_apply, muxListP_apply, ap₂_apply, ap₁_apply, fieldP_apply, offR_apply,
    cstR_const, length_threeU, length_vOffU, flagR_apply, headD_apply, rR_apply]

/-- The `q` field. -/
noncomputable def qR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (qOffU eu)) QbU) (cstR QbU (bitsR 0))

theorem qR_apply (i : ι) : qR eu b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + qOff (eu i).length) Qb) (cst Qb 0) := by
  simp only [qR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_QbU, length_qOffU, flagR_apply]

/-- The `js` fields. -/
noncomputable def jsR (k : ℕ) : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (jsOffU eu k)) (WU eu)) (cstR (WU eu) (bitsR 0))

theorem jsR_apply (k : ℕ) (i : ι) : jsR eu b k i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + jsOff (eu i).length k) (W (eu i).length))
      (cst (W (eu i).length) 0) := by
  simp only [jsR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_WU, length_jsOffU, flagR_apply]

/-- The `g` field. -/
noncomputable def gR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (gOffU eu)) GbU) (cstR GbU (bitsR 0))

theorem gR_apply (i : ι) : gR eu b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + gOff (eu i).length) (Gb Gc)) (cst (Gb Gc) 0) := by
  simp only [gR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_GbU, length_gOffU, flagR_apply]

/-- The `ansOk` field. -/
noncomputable def ansOkR : PolyTimeFun ι Fml :=
  ap₂ Fml.andF (ap₁ Fml.notF (flagR eu b))
    (ap₂ ltConstP (jR eu b) (nbitsR (flagOffU eu) (quadR TR)))

theorem ansOkR_apply (i : ι) : ansOkR eu TR b i =
    Fml.and (Fml.not (flagF (eu i).length Gc (b i).length))
      (Fml.ltConst (jF (eu i).length Gc (b i).length)
        (nbits (flagOff (eu i).length Gc) (4 * TR i))) := by
  have hquad : nbitsR (flagOffU eu) (quadR TR) i =
      nbits (flagOff (eu i).length Gc) (4 * TR i) := by
    rw [nbitsR_apply _ (quadR_spec TR i), length_flagOffU]
  simp only [ansOkR, ap₂_apply, ap₁_apply, Fml.andF_apply, Fml.notF_apply, ltConstP_apply,
    flagR_apply, jR_apply, hquad]

/-- The field programs of the literal with base `b`. -/
noncomputable def litFieldsR : FieldsR ι where
  flag := flagR eu b
  tag := tagR eu b
  t := tR eu b
  d := dR eu TR b
  p := pR eu TR b
  v := vR eu TR b
  q := qR eu b
  js := fun k => jsR eu b k
  g := gR eu b
  ansOk := ansOkR eu TR b

/-- **The field programs are the field formulas**: the record of programs for `litFields`
produces `litFields`. -/
theorem litFieldsR_ev (i : ι) :
    (litFieldsR eu TR b).ev i = litFields (eu i).length Gc (TR i) (b i).length := by
  simp only [FieldsR.ev, litFieldsR, litFields, FieldsF.mk.injEq]
  exact ⟨flagR_apply eu b i, tagR_apply eu b i, tR_apply eu b i, dR_apply eu TR b i,
    pR_apply eu TR b i, vR_apply eu TR b i, qR_apply eu b i, funext fun k => jsR_apply eu b k i,
    gR_apply eu b i, ansOkR_apply eu TR b i⟩

end Lit

end MIPRE.TM.CookLevin.Desc
