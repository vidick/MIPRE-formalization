/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.PcpParameters

/-!
# The source runtime bound for formatted PCP views

An ambient polynomial-time program is polynomial in encoded input size. This
module bounds that size in the paper's parameter `log n + log T + Q + sigma`,
including all field coordinates in the view.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Desc Polynomial

theorem esize_bitBlocks_le (l : List BitStr) (k : ℕ) (h : ∀ b ∈ l, b.length = k) :
    esize l ≤ (4 * k + 2) * l.length + 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb := esize_bitStr_le b
    rw [h b (by simp)] at hb
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [esize_list_cons, List.length_cons]
    nlinarith

theorem esize_view_le (P : PcpParams) (z ev : List BitStr) (h : ViewFormat P z ev) :
    esize (z, ev) ≤ (4 * P.k + 2) * (2 * P.m' + 6) + 3 := by
  have hz := esize_bitBlocks_le z P.k h.width_z
  have he := esize_bitBlocks_le ev P.k h.width_ev
  rw [h.length_z] at hz
  rw [h.length_ev] at he
  rw [esize_prod]
  nlinarith

/-- The complete encoded verifier input is polynomially bounded in precisely
the source's four runtime parameters. -/
theorem pcpInput_size_polynomial : ∃ B : Polynomial ℕ, ∀ D n T Q σ x y z ev,
    Valid D n T Q σ x y → ViewFormat (pcpParams n T Q σ) z ev →
      esize (pcpInput D n T Q σ x y z ev) ≤ B.eval (LOf n T Q σ) := by
  obtain ⟨R, hR⟩ := outerDim_polynomial
  set K : Polynomial ℕ := 2 * ((X + R + 3) ^ 2 + R) + 7 with hK
  refine ⟨25 * X + 16 + (4 * K + 2) * (2 * R + 6), ?_⟩
  intro D n T Q σ x y z ev hV hf
  have hd := esize_descInput_le D n T Q σ x y hV
  have hv := esize_view_le (pcpParams n T Q σ) z ev hf
  have hm : (pcpParams n T Q σ).m' ≤ R.eval (LOf n T Q σ) := by
    rw [pcpParams_outer]
    exact hR n T Q σ
  have hk : (pcpParams n T Q σ).k ≤ K.eval (LOf n T Q σ) := by
    have h1 := fieldDegree_le n T Q σ
    have hQ : Q ≤ LOf n T Q σ := by unfold LOf; omega
    have ho := hR n T Q σ
    have h2 : (Q + outerDim n T Q σ + 3) ^ 2 ≤ (LOf n T Q σ + R.eval (LOf n T Q σ) + 3) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    change fieldDegree n T Q σ ≤ _
    simp only [hK, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  have hprod := Nat.mul_le_mul
    (show 4 * (pcpParams n T Q σ).k + 2 ≤ 4 * K.eval (LOf n T Q σ) + 2 by omega)
    (show 2 * (pcpParams n T Q σ).m' + 6 ≤ 2 * R.eval (LOf n T Q σ) + 6 by omega)
  change esize (((D, n, T, Q, σ), x, y) : DescInput) + esize (z, ev) + 1 ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- Any ambient polynomial-time PCP program has the prescribed source runtime
bound on valid formatted views, for the constructed parameter family. -/
theorem pcpProgram_time_le (verify : PolyTimeFun PcpInput Bool) :
    ∃ R : Polynomial ℕ, ∀ D n T Q σ x y z ev, Valid D n T Q σ x y →
      ViewFormat (pcpParams n T Q σ) z ev →
      ∃ t ≤ R.eval (Nat.size n + Nat.size T + Q + σ),
        verify.code.Runs (encode (pcpInput D n T Q σ x y z ev))
          (encode (verify (pcpInput D n T Q σ x y z ev))) t := by
  obtain ⟨B, hB⟩ := pcpInput_size_polynomial
  refine ⟨verify.timeBound.comp B, ?_⟩
  intro D n T Q σ x y z ev hV hf
  obtain ⟨t, ht, hr⟩ := verify.computes (pcpInput D n T Q σ x y z ev)
  refine ⟨t, ht.trans ?_, hr⟩
  simpa only [Polynomial.eval_comp, LOf] using
    polynomial_eval_mono verify.timeBound (hB D n T Q σ x y z ev hV hf)

end MIPRE.TM.CookLevin.Pad
