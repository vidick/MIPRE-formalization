/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.PaddingParams
import MIPRE.Foundations.SAT.Pcp

/-!
# Effective parameters for the classical PCP

The odd extension degree makes the field admissible. Its size is large enough
for the classical majority argument, and both power-of-two dimensions divide
the field size. Stronger field-size requirements of later low-degree-test
consumers are separate from this classical PCP contract.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Desc

/-- An odd degree giving at least 82 field elements per outer coordinate. -/
noncomputable def fieldDegree (n T Q σ : ℕ) : ℕ := 2 * Nat.size (outerDim n T Q σ) + 7

/-- The complete classical PCP parameters. -/
noncomputable def pcpParams (n T Q σ : ℕ) : PcpParams :=
  ⟨fieldDegree n T Q σ, innerDim T σ, gateCount n T Q σ⟩

theorem pcpParams_outer (n T Q σ : ℕ) : (pcpParams n T Q σ).m' = outerDim n T Q σ :=
  inputs_add_gateCount n T Q σ

theorem pcpParams_odd (n T Q σ : ℕ) : Odd (pcpParams n T Q σ).k := by
  refine ⟨Nat.size (outerDim n T Q σ) + 3, ?_⟩
  simp only [pcpParams, fieldDegree]
  omega

theorem pcpParams_field_large (n T Q σ : ℕ) :
    82 * (pcpParams n T Q σ).m' ≤ (pcpParams n T Q σ).q := by
  rw [pcpParams_outer]
  let e := Nat.size (outerDim n T Q σ)
  have h := Nat.lt_size_self (outerDim n T Q σ)
  have hp := Nat.two_pow_pos e
  have he : (pcpParams n T Q σ).q = (2 ^ e) ^ 2 * 128 := by
    change 2 ^ (2 * e + 7) = _
    rw [pow_add, Nat.mul_comm 2 e, pow_mul]
    norm_num
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

/-- Compute the extension degree from binary parameters without expanding the field. -/
noncomputable def fieldDegreeProg : PolyTimeFun ParamInput ℕ :=
  unaryToBin.comp (ap₂ addU (ap₁ (nsmulU 2) (sizeU.comp outerDimProg)) (const (unary 7)))

theorem fieldDegreeProg_apply (p : ParamInput) :
    fieldDegreeProg p = fieldDegree p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [fieldDegreeProg, outerDimProg_apply, fieldDegree]

/-- The actual program for the three fields of `PcpDecider.paramsProg`. -/
noncomputable def pcpParamsProg : PolyTimeFun ParamInput (ℕ × ℕ × ℕ) :=
  fieldDegreeProg.pair paddingParams

theorem pcpParamsProg_apply (n T Q σ : ℕ) :
    pcpParamsProg (n, T, Q, σ) =
      ((pcpParams n T Q σ).k, (pcpParams n T Q σ).m, (pcpParams n T Q σ).s) := by
  simp [pcpParamsProg, fieldDegreeProg_apply, paddingParams_apply, pcpParams]

end MIPRE.TM.CookLevin.Pad
