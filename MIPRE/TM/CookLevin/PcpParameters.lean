/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.PaddingParams
import MIPRE.Foundations.SAT.Pcp
import MIPRE.Foundations.LowDegree.UnaryDegreeArithmetic

/-!
# Effective parameters for the classical PCP

The odd extension degree makes the field admissible. Its size is large enough
for the classical majority argument, and both power-of-two dimensions divide
the field size. It is also *eventually larger than every fixed power* of
`8 (Q + 1) m'` (`pcpParams_field_eventually_large`): the degree carries the square of
`s = size Q + size m' + 3`, and `8 (Q + 1) m' < 2^s`, so `(8 (Q + 1) m')^e < 2^{s e} ≤ q` once
`s ≥ e`. Answer reduction's low-degree test needs a field polynomially larger than `m'` with an
exponent this module need not know; the degree stays polylogarithmic
(`fieldDegree_le`).
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Desc

/-- The base of the field degree: `8 (Q + 1) m' < 2^{fieldBase}`. -/
noncomputable def fieldBase (n T Q σ : ℕ) : ℕ := Nat.size Q + Nat.size (outerDim n T Q σ) + 3

/-- An odd degree giving at least 82 field elements per outer coordinate, and eventually more
than any fixed power of `8 (Q + 1) m'`. -/
noncomputable def fieldDegree (n T Q σ : ℕ) : ℕ :=
  2 * (fieldBase n T Q σ ^ 2 + Nat.size (outerDim n T Q σ)) + 7

/-- The complete classical PCP parameters. -/
noncomputable def pcpParams (n T Q σ : ℕ) : PcpParams :=
  ⟨fieldDegree n T Q σ, innerDim T σ, gateCount n T Q σ⟩

theorem pcpParams_outer (n T Q σ : ℕ) : (pcpParams n T Q σ).m' = outerDim n T Q σ :=
  inputs_add_gateCount n T Q σ

theorem pcpParams_odd (n T Q σ : ℕ) : Odd (pcpParams n T Q σ).k := by
  refine ⟨fieldBase n T Q σ ^ 2 + Nat.size (outerDim n T Q σ) + 3, ?_⟩
  simp only [pcpParams, fieldDegree]
  omega

theorem pcpParams_field_large (n T Q σ : ℕ) :
    82 * (pcpParams n T Q σ).m' ≤ (pcpParams n T Q σ).q := by
  rw [pcpParams_outer]
  let e := Nat.size (outerDim n T Q σ)
  have h := Nat.lt_size_self (outerDim n T Q σ)
  have hp := Nat.two_pow_pos e
  have he : 2 ^ (2 * e + 7) = (2 ^ e) ^ 2 * 128 := by
    rw [pow_add, Nat.mul_comm 2 e, pow_mul]
    norm_num
  have hle : 2 ^ (2 * e + 7) ≤ (pcpParams n T Q σ).q := by
    change 2 ^ (2 * e + 7) ≤ 2 ^ fieldDegree n T Q σ
    exact Nat.pow_le_pow_right (by norm_num) (by unfold fieldDegree; nlinarith)
  refine le_trans ?_ hle
  rw [he]
  change outerDim n T Q σ < 2 ^ e at h
  nlinarith

private theorem power_dvd_of_le {j k : ℕ} (h : 2 ^ j ≤ 2 ^ k) : 2 ^ j ∣ 2 ^ k := by
  have hj : j ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h
  exact pow_dvd_pow 2 hj

theorem pcpParams_outer_dvd (n T Q σ : ℕ) :
    (pcpParams n T Q σ).m' ∣ (pcpParams n T Q σ).q := by
  obtain ⟨j, hj⟩ := outerDim_isPow n T Q σ
  have h := pcpParams_field_large n T Q σ
  rw [pcpParams_outer, hj] at h ⊢
  apply power_dvd_of_le
  change 2 ^ j ≤ (pcpParams n T Q σ).q
  omega

theorem pcpParams_inner_dvd (n T Q σ : ℕ) :
    (pcpParams n T Q σ).m ∣ (pcpParams n T Q σ).q := by
  obtain ⟨j, hj⟩ := innerDim_isPow T σ
  have ho := inputs_add_gateCount n T Q σ
  have h := pcpParams_field_large n T Q σ
  rw [pcpParams_outer] at h
  change innerDim T σ ∣ _
  rw [hj]
  apply power_dvd_of_le
  change 2 ^ j ≤ (pcpParams n T Q σ).q
  rw [hj] at ho
  omega

/-- **The field is eventually large**: for every exponent `e`, once `Q ≥ 2^e` the field has at
least `(8 (Q + 1) m')^e` elements. -/
theorem pcpParams_field_eventually_large (e : ℕ) : ∀ n T Q σ, 2 ^ e ≤ Q →
    (8 * ((Q + 1) * (pcpParams n T Q σ).m')) ^ e ≤ (pcpParams n T Q σ).q := by
  intro n T Q σ hQ
  rw [pcpParams_outer]
  set m' := outerDim n T Q σ
  set s := fieldBase n T Q σ with hs
  have hsQ : e < Nat.size Q := Nat.lt_size.mpr hQ
  have hes : e ≤ s := by rw [hs, fieldBase]; omega
  have hQs : Q + 1 ≤ 2 ^ Nat.size Q := Nat.lt_size_self Q
  have hms : m' < 2 ^ Nat.size m' := Nat.lt_size_self m'
  have hY : 8 * ((Q + 1) * m') ≤ 2 ^ s := by
    have : 2 ^ s = 8 * (2 ^ Nat.size Q * 2 ^ Nat.size m') := by
      rw [hs, fieldBase, pow_add, pow_add]; ring
    rw [this]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hQs hms.le)
  calc (8 * ((Q + 1) * m')) ^ e ≤ (2 ^ s) ^ e := Nat.pow_le_pow_left hY _
    _ = 2 ^ (s * e) := by rw [← pow_mul]
    _ ≤ 2 ^ fieldDegree n T Q σ := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have : s * e ≤ s * s := Nat.mul_le_mul_left _ hes
        unfold fieldDegree
        rw [← hs]
        nlinarith

/-- The field degree is polylogarithmic in `Q m'`: at most `2 ((Q + m' + 3)^2 + m') + 7`. -/
theorem fieldDegree_le (n T Q σ : ℕ) :
    fieldDegree n T Q σ ≤ 2 * ((Q + outerDim n T Q σ + 3) ^ 2 + outerDim n T Q σ) + 7 := by
  have h1 := size_le_self Q
  have h2 := size_le_self (outerDim n T Q σ)
  have h3 : fieldBase n T Q σ ≤ Q + outerDim n T Q σ + 3 := by unfold fieldBase; omega
  have h4 := Nat.pow_le_pow_left h3 2
  unfold fieldDegree
  omega

/-- The field degree's base, in unary. -/
noncomputable def fieldBaseU : PolyTimeFun ParamInput Unary :=
  ap₂ addU (ap₂ addU (sizeU.comp (fst.comp (snd.comp snd))) (sizeU.comp outerDimProg))
    (const (unary 3))

@[simp] theorem length_fieldBaseU (p : ParamInput) :
    (fieldBaseU p).length = fieldBase p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [fieldBaseU, fieldBase, outerDimProg_apply]
  omega

/-- The field degree in unary, for the existing Shoup modulus program. -/
noncomputable def fieldDegreeU : PolyTimeFun ParamInput Unary :=
  ap₂ addU (ap₁ (nsmulU 2) (ap₂ addU
      (LowDegree.DegreeArithmetic.mulUnaryProg.comp (fieldBaseU.pair fieldBaseU))
      (sizeU.comp outerDimProg)))
    (const (unary 7))

theorem fieldDegreeU_length (p : ParamInput) :
    (fieldDegreeU p).length = (pcpParams p.1 p.2.1 p.2.2.1 p.2.2.2).k := by
  simp [fieldDegreeU, pcpParams, fieldDegree, outerDimProg_apply, sq]

/-- Compute the extension degree from binary parameters without expanding the field. -/
noncomputable def fieldDegreeProg : PolyTimeFun ParamInput ℕ :=
  unaryToBin.comp fieldDegreeU

theorem fieldDegreeProg_apply (p : ParamInput) :
    fieldDegreeProg p = fieldDegree p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  rw [fieldDegreeProg, comp_apply, unaryToBin_apply, fieldDegreeU_length]
  rfl

/-- The actual program for the three fields of `PcpDecider.paramsProg`. -/
noncomputable def pcpParamsProg : PolyTimeFun ParamInput (ℕ × ℕ × ℕ) :=
  fieldDegreeProg.pair paddingParams

theorem pcpParamsProg_apply (n T Q σ : ℕ) :
    pcpParamsProg (n, T, Q, σ) =
      ((pcpParams n T Q σ).k, (pcpParams n T Q σ).m, (pcpParams n T Q σ).s) := by
  simp [pcpParamsProg, fieldDegreeProg_apply, paddingParams_apply, pcpParams]

end MIPRE.TM.CookLevin.Pad
