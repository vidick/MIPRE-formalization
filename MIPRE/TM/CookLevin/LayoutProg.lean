/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Describer
import MIPRE.Foundations.Cost.Reader
import MIPRE.Foundations.SAT.FmlProg

/-!
# The layout arithmetic as programs

The widths and offsets of the index layout (`Layout.lean`) as programs. Two conventions make
them cheap:

* **widths and offsets are unary.** `W e`, `mOf e G`, the field offsets: all are affine in
  `e` with small coefficients, so in unary they are `append` and iterated `append`, and no
  arithmetic program is needed. `e` itself must be unary in any case — the formulas are of
  size polynomial in `e`, so a binary `e` would make the output exponential in the input.
* **a constant of a field is a resize of a bit string.** `resize w bs` keeps the low `w` bits
  of `bs`, padding with `false`, and `resize_eq_nbits` identifies it with `nbits w k` for any
  `bs` whose bits are those of `k`. So `nbits w (2 * T)` is a resize of `false :: T.bits` and
  `nbits w (T + 3)` one of `incBits (incBits (incBits T.bits))`, with no multiplication or
  addition on numbers (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## Unary arithmetic -/

/-- Unary addition. -/
noncomputable def addU : PolyTimeFun (Unary × Unary) Unary := append

@[simp] theorem addU_apply (p : Unary × Unary) : addU p = p.1 ++ p.2 := rfl

@[simp] theorem length_addU (p : Unary × Unary) : (addU p).length = p.1.length + p.2.length := by
  rw [addU_apply, List.length_append]

/-- Unary multiplication by a constant. -/
noncomputable def nsmulU : ℕ → PolyTimeFun Unary Unary
  | 0 => const []
  | k + 1 => ap₂ addU (nsmulU k) (PolyTimeFun.id _)

@[simp] theorem length_nsmulU : ∀ (k : ℕ) (u : Unary), (nsmulU k u).length = k * u.length
  | 0, u => by rw [nsmulU, const_apply, List.length_nil, Nat.zero_mul]
  | k + 1, u => by
    rw [nsmulU, ap₂_apply, length_addU, length_nsmulU k u, PolyTimeFun.id_apply]
    ring

/-! ## Resizing a bit string -/

/-- The low `w` bits of a bit string, padded with `false` to the width `w`. -/
def resize (w : ℕ) (bs : BitStr) : BitStr := (bs ++ List.replicate w false).take w

theorem length_resize (w : ℕ) (bs : BitStr) : (resize w bs).length = w := by
  rw [resize, List.length_take, List.length_append, List.length_replicate]
  omega

theorem getD_append_replicate (bs : BitStr) (w i : ℕ) :
    (bs ++ List.replicate w false).getD i false = bs.getD i false := by
  rcases lt_or_ge i bs.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h,
      List.getElem?_eq_none h]
    rcases lt_or_ge (i - bs.length) w with h' | h'
    · rw [List.getElem?_replicate_of_lt h']; rfl
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact h')]

theorem getD_resize {w : ℕ} (bs : BitStr) {i : ℕ} (hi : i < w) :
    (resize w bs).getD i false = bs.getD i false := by
  rw [resize, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
    ← List.getD_eq_getElem?_getD, getD_append_replicate]

/-- **A constant of a width is a resize**: if the bits of `bs` are those of `k`, then the low
`w` bits of `bs` are the `w`-bit constant `k`. -/
theorem resize_eq_nbits (w : ℕ) (bs : BitStr) (k : ℕ)
    (h : ∀ i, bs.getD i false = k.testBit i) : resize w bs = nbits w k := by
  refine List.ext_getElem (by rw [length_resize, length_nbits]) fun i h1 h2 => ?_
  have hi : i < w := by rw [length_resize] at h1; exact h1
  rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2, getD_resize bs hi,
    h i, nbits, getD_bitsOfNat k hi]

/-! ### The bit strings of the numbers the describer needs -/

theorem getD_bits (k : ℕ) (i : ℕ) : k.bits.getD i false = k.testBit i := by
  rw [Nat.testBit_eq_inth]
  rfl

theorem getD_false_cons (bs : BitStr) (k : ℕ) (h : ∀ i, bs.getD i false = k.testBit i) :
    ∀ i, (false :: bs).getD i false = (2 * k).testBit i := by
  intro i
  cases i with
  | zero => rw [List.getD_cons_zero, Nat.testBit_zero]; simp [Nat.mul_mod_right]
  | succ i =>
    rw [List.getD_cons_succ, h i, Nat.testBit_succ]
    congr 1
    omega

theorem getD_replicate_false_append (e : ℕ) :
    ∀ i, (List.replicate e false ++ [true]).getD i false = (2 ^ e).testBit i := by
  intro i
  rcases lt_trichotomy i e with h | h | h
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [List.length_replicate]; omega),
      List.getElem?_replicate_of_lt h, Option.getD_some,
      Nat.testBit_two_pow_of_ne (by omega)]
  · subst h
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_replicate]), List.length_replicate,
      Nat.testBit_two_pow_self]
    simp
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_replicate]; omega), List.length_replicate,
      List.getElem?_eq_none (by simp; omega), Option.getD_none,
      Nat.testBit_two_pow_of_ne (by omega)]

/-! ### Powers of two -/

theorem bits_two_pow : ∀ e : ℕ, (2 ^ e).bits = List.replicate e false ++ [true]
  | 0 => by rw [pow_zero, Nat.one_bits, List.replicate_zero, List.nil_append]
  | e + 1 => by
    rw [pow_succ, mul_comm, Nat.bit0_bits _ (Nat.two_pow_pos e).ne', bits_two_pow e,
      List.replicate_succ, List.cons_append]

/-! ## Resizing, as a program -/

/-- `resize`, the width in unary. -/
noncomputable def resizeP : PolyTimeFun (Unary × BitStr) BitStr :=
  congr (ap₂ take (ap₂ append snd (ap₂ replicate fst (const false))) fst)
    (fun p => resize p.1.length p.2) fun _ => rfl

@[simp] theorem resizeP_apply (p : Unary × BitStr) : resizeP p = resize p.1.length p.2 := rfl

/-- Doubling a bit string: a `false` in front. -/
noncomputable def dblP : PolyTimeFun BitStr BitStr := cons (const false) (PolyTimeFun.id _)

@[simp] theorem dblP_apply (bs : BitStr) : dblP bs = false :: bs := rfl

/-- `2 ^ e`, from `e` in unary: its bit string is `e` zeros and a one. -/
noncomputable def pow2P : PolyTimeFun Unary ℕ :=
  PolyTimeFun.cast (ap₂ append (ap₂ replicate (PolyTimeFun.id _) (const false)) (const [true]))
    (fun u => 2 ^ u.length) (by
      intro u
      show (encode (2 ^ u.length) : Data) = encode (List.replicate u.length false ++ [true])
      rw [show (encode (2 ^ u.length) : Data) = encode ((2 ^ u.length).bits) from rfl,
        bits_two_pow])

@[simp] theorem pow2P_apply (u : Unary) : pow2P u = 2 ^ u.length := rfl

/-- Adding a constant to a number. -/
noncomputable def incN : ℕ → PolyTimeFun ℕ ℕ
  | 0 => PolyTimeFun.id _
  | k + 1 => PolyTimeFun.inc.comp (incN k)

@[simp] theorem incN_apply : ∀ (k n : ℕ), incN k n = n + k
  | 0, n => rfl
  | k + 1, n => by rw [incN, comp_apply, PolyTimeFun.inc_apply, incN_apply k n, Nat.add_assoc]

/-! ## Readers of the layout -/

section Reader

variable {ι : Type*} [SizedEncoding ι]

/-- The constant `k` on `w` bits, read off a width in unary and the bits of `k`. -/
noncomputable def nbitsR (w : PolyTimeFun ι Unary) (bs : PolyTimeFun ι BitStr) :
    PolyTimeFun ι BitStr := ap₂ resizeP w bs

theorem nbitsR_apply {w : PolyTimeFun ι Unary} {bs : PolyTimeFun ι BitStr} {i : ι} (k : ℕ)
    (h : ∀ j, (bs i).getD j false = k.testBit j) : nbitsR w bs i = nbits (w i).length k :=
  resize_eq_nbits _ _ _ h

/-- The formulas of the constant `k` on `w` bits. -/
noncomputable def cstR (w : PolyTimeFun ι Unary) (bs : PolyTimeFun ι BitStr) :
    PolyTimeFun ι (List Fml) := ap₁ constBitsP (nbitsR w bs)

theorem cstR_apply {w : PolyTimeFun ι Unary} {bs : PolyTimeFun ι BitStr} {i : ι} (k : ℕ)
    (h : ∀ j, (bs i).getD j false = k.testBit j) : cstR w bs i = cst (w i).length k := by
  rw [cstR, ap₁_apply, nbitsR_apply k h, constBitsP_apply, cst, nbits]

/-- The constant read off a width in unary and a reader of the number itself. -/
theorem nbitsR_num (w : PolyTimeFun ι Unary) (kR : PolyTimeFun ι ℕ) (i : ι) :
    nbitsR w (ap₁ natBits kR) i = nbits (w i).length (kR i) :=
  nbitsR_apply _ (getD_bits (kR i))

theorem cstR_num (w : PolyTimeFun ι Unary) (kR : PolyTimeFun ι ℕ) (i : ι) :
    cstR w (ap₁ natBits kR) i = cst (w i).length (kR i) :=
  cstR_apply _ (getD_bits (kR i))

/-- The bits of a numeral, as a reader. -/
noncomputable def bitsR (k : ℕ) : PolyTimeFun ι BitStr := const k.bits

theorem bitsR_spec (k : ℕ) (i : ι) : ∀ j, ((bitsR k : PolyTimeFun ι BitStr) i).getD j false =
    k.testBit j := getD_bits k

/-! ### The widths and offsets -/

variable (eu : PolyTimeFun ι Unary)

/-- `W e`, in unary. -/
noncomputable def WU : PolyTimeFun ι Unary := ap₂ addU eu (const (unary 4))

@[simp] theorem length_WU (i : ι) : (WU eu i).length = W (eu i).length := by
  rw [WU, ap₂_apply, length_addU, const_apply, length_unary, W]

/-- `3`, `4` and `Qb` and `Gb Gc`, in unary: the widths that do not depend on `e`. -/
noncomputable def threeU : PolyTimeFun ι Unary := const (unary 3)
noncomputable def fourU : PolyTimeFun ι Unary := const (unary 4)
noncomputable def QbU : PolyTimeFun ι Unary := const (unary Qb)
noncomputable def GbU : PolyTimeFun ι Unary := const (unary (Gb Gc))

@[simp] theorem length_threeU (i : ι) : (threeU i : Unary).length = 3 := length_unary 3
@[simp] theorem length_fourU (i : ι) : (fourU i : Unary).length = 4 := length_unary 4
@[simp] theorem length_QbU (i : ι) : (QbU i : Unary).length = Qb := length_unary Qb
@[simp] theorem length_GbU (i : ι) : (GbU i : Unary).length = Gb Gc := length_unary (Gb Gc)

/-- `mOf e Gc`, in unary. -/
noncomputable def mU : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (ap₂ addU (const (unary 11)) (ap₁ (nsmulU 15) (WU eu))) QbU) GbU

@[simp] theorem length_mU (i : ι) : (mU eu i).length = mOf (eu i).length Gc := by
  rw [mU, ap₂_apply, length_addU, ap₂_apply, length_addU, ap₂_apply, length_addU, const_apply,
    length_unary, ap₁_apply, length_nsmulU, length_WU, length_QbU, length_GbU, mOf]

/-- `flagOff e Gc`, in unary. -/
noncomputable def flagOffU : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (ap₂ addU (const (unary 10)) (ap₁ (nsmulU 15) (WU eu))) QbU) GbU

@[simp] theorem length_flagOffU (i : ι) : (flagOffU eu i).length = flagOff (eu i).length Gc := by
  rw [flagOffU, ap₂_apply, length_addU, ap₂_apply, length_addU, ap₂_apply, length_addU,
    const_apply, length_unary, ap₁_apply, length_nsmulU, length_WU, length_QbU, length_GbU,
    flagOff]

/-- `gOff e`, in unary. -/
noncomputable def gOffU : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (const (unary 10)) (ap₁ (nsmulU 15) (WU eu))) QbU

@[simp] theorem length_gOffU (i : ι) : (gOffU eu i).length = gOff (eu i).length := by
  rw [gOffU, ap₂_apply, length_addU, ap₂_apply, length_addU, const_apply, length_unary,
    ap₁_apply, length_nsmulU, length_WU, length_QbU, gOff]

/-- `dOff e`, in unary. -/
noncomputable def dOffU : PolyTimeFun ι Unary := ap₂ addU (const (unary 3)) (WU eu)

@[simp] theorem length_dOffU (i : ι) : (dOffU eu i).length = dOff (eu i).length := by
  rw [dOffU, ap₂_apply, length_addU, const_apply, length_unary, length_WU, dOff]

/-- `pOff e`, in unary. -/
noncomputable def pOffU : PolyTimeFun ι Unary := ap₂ addU (const (unary 7)) (WU eu)

@[simp] theorem length_pOffU (i : ι) : (pOffU eu i).length = pOff (eu i).length := by
  rw [pOffU, ap₂_apply, length_addU, const_apply, length_unary, length_WU, pOff]

/-- `vOff e`, in unary. -/
noncomputable def vOffU : PolyTimeFun ι Unary :=
  ap₂ addU (const (unary 7)) (ap₁ (nsmulU 2) (WU eu))

@[simp] theorem length_vOffU (i : ι) : (vOffU eu i).length = vOff (eu i).length := by
  rw [vOffU, ap₂_apply, length_addU, const_apply, length_unary, ap₁_apply, length_nsmulU,
    length_WU, vOff]

/-- `qOff e`, in unary. -/
noncomputable def qOffU : PolyTimeFun ι Unary :=
  ap₂ addU (const (unary 10)) (ap₁ (nsmulU 2) (WU eu))

@[simp] theorem length_qOffU (i : ι) : (qOffU eu i).length = qOff (eu i).length := by
  rw [qOffU, ap₂_apply, length_addU, const_apply, length_unary, ap₁_apply, length_nsmulU,
    length_WU, qOff]

/-- `jsOff e d`, in unary. -/
noncomputable def jsOffU (d : ℕ) : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (qOffU eu) QbU) (ap₁ (nsmulU d) (WU eu))

@[simp] theorem length_jsOffU (d : ℕ) (i : ι) :
    (jsOffU eu d i).length = jsOff (eu i).length d := by
  rw [jsOffU, ap₂_apply, length_addU, ap₂_apply, length_addU, length_qOffU, length_QbU,
    ap₁_apply, length_nsmulU, length_WU, jsOff, qOff]

end Reader

/-! ## `muxList`, as a program -/

/-- `muxList`. -/
noncomputable def muxListP : PolyTimeFun (Fml × List Fml × List Fml) (List Fml) :=
  congr ((mapWith (ap₃ muxP snd (ap₁ fst fst) (ap₁ snd fst))).comp
      ((ap₂ zip (ap₁ fst snd) (ap₁ snd snd)).pair fst))
    (fun p => muxList p.1 p.2.1 p.2.2) (by
      intro p
      show (p.2.1.zip p.2.2).map (fun a => Fml.mux p.1 a.1 a.2) = muxList p.1 p.2.1 p.2.2
      exact List.map_zip_eq_zipWith)

@[simp] theorem muxListP_apply (p : Fml × List Fml × List Fml) :
    muxListP p = muxList p.1 p.2.1 p.2.2 := rfl

end MIPRE.TM.CookLevin.Desc
