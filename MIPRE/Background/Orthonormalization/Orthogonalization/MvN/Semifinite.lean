/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Semifinite.lean
-/
/-
# Tier T3, step S: the semifinite reduction (Section 4 of the paper)

If `(p_α)` is a net of projections of `M` below a central projection `z`,
converging strongly to `z`, and Theorem 1.2 holds at every `p_α` (for normal
functionals), then it holds at `z`. This is the paper's Section 4 with the
slack bookkeeping written out: for a normal `φ` with `φ z = 1` and a POVM `(aᵢ)`
supported in `z`, Lemma 4.1 (`IsNormalOn.tendsto_re` along the net) gives
`φ(p_α) → 1` and `φ(∑ p_α aᵢ p_α aᵢ p_α) → φ(∑ aᵢ²)`, so for `α` large the
compressed POVM `p_α aᵢ p_α` with the normalized functional `φ(p_α)⁻¹ φ` is in
the hypothesis of the finite case with a slightly smaller `ε − δ`; the PVM
`(q_α,i)` it produces is completed by `z − p_α` on one output, and the error is
controlled by the weighted triangle inequality
`‖Y + W‖² ≤ (1 + s)‖Y‖² + (1 + s⁻¹)‖W‖²` with `‖W‖² → 0`. Proof-side only.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Local

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder
open Filter Topology CommutingRepetition.VN Blocks

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The semifinite reduction (step S).** -/
theorem orthAtN_of_net (M : VonNeumannAlgebra H) {z : H →L[ℂ] H} (hz : IsCentralProj M z)
    {κ : Type u} [Preorder κ] [IsDirected κ (· ≤ ·)] [Nonempty κ] (p : κ → H →L[ℂ] H)
    (hp : ∀ α, IsStarProjection (p α) ∧ p α ∈ M ∧ p α * z = p α)
    (hlim : TendstoStrongBdd atTop p z) (ι : Type*) [Fintype ι]
    (h : ∀ α, OrthAtN M (p α) ι) : OrthAtN M z ι := by
  classical
  intro φ hφn hφ hφz a haM ha0 haz ε hε
  -- the output set is nonempty
  rcases isEmpty_or_nonempty ι with hι | hι
  · exfalso
    rw [Fintype.sum_empty] at haz
    have h0 : φ z = 0 := by rw [← haz, map_zero]
    rw [hφz] at h0
    exact one_ne_zero h0
  obtain ⟨i₀⟩ := hι
  have hzP := hz.isStarProjection
  have hzM := hz.mem
  have hpP : ∀ α, IsStarProjection (p α) := fun α => (hp α).1
  have hpM : ∀ α, p α ∈ M := fun α => (hp α).2.1
  have hpz : ∀ α, p α * z = p α := fun α => (hp α).2.2
  have hzp : ∀ α, z * p α = p α := fun α => by rw [(hz.commute _ (hpM α)).eq, hpz α]
  have haz' : ∀ i, a i * z = a i := mul_eq_self_of_sum_eq hzP ha0 haz
  have hza : ∀ i, z * a i = a i := fun i => by rw [(hz.commute _ (haM i)).eq, haz' i]
  have hasa : ∀ i, star (a i) = a i := fun i => (IsSelfAdjoint.of_nonneg (ha0 i)).star_eq
  -- `p_α ≤ z`
  have hzsubP : ∀ α, IsStarProjection (z - p α) := fun α => by
    refine ⟨?_, ?_⟩
    · show (z - p α) * (z - p α) = z - p α
      rw [sub_mul, mul_sub, mul_sub, hzP.isIdempotentElem.eq, hzp α, hpz α,
        (hpP α).isIdempotentElem.eq]
      abel
    · rw [IsSelfAdjoint, star_sub, hzP.isSelfAdjoint.star_eq, (hpP α).isSelfAdjoint.star_eq]
  have hple : ∀ α, p α ≤ z := fun α => sub_nonneg.mp (hzsubP α).nonneg
  -- the numbers
  set S := (φ (∑ i, a i * a i)).re with hS
  have hQM : (∑ i, a i * a i) ∈ M := sum_mem fun i _ => mul_mem (haM i) (haM i)
  have hz1 : z ≤ 1 := hzP.le_one
  have hQle : ∑ i, a i * a i ≤ z := by
    rw [← haz]
    exact Finset.sum_le_sum fun i _ =>
      sq_le_self_of_le_one (ha0 i) (le_trans (le_of_sum_eq ha0 haz i) hz1)
  have hS1 : S ≤ 1 := by
    have := re_map_le_of_mem hφ hQM hzM hQle
    rwa [hφz, Complex.one_re] at this
  have hε0 : 0 < ε := by linarith
  set δ : ℝ := (S - (1 - ε)) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hεδ : 0 < ε - δ := by rw [hδ]; linarith
  set s : ℝ := δ / (2 * ε) with hs
  have hs0 : 0 < s := by positivity
  -- Lemma 4.1 along the net
  have h_m : Tendsto (fun α => (φ (p α)).re) atTop (𝓝 1) := by
    have := hφn.tendsto_re hpM hzM hlim
    rwa [hφz, Complex.one_re] at this
  have hQα : ∀ α, (∑ i, p α * a i * p α * a i * p α) ∈ M := fun α =>
    sum_mem fun i _ => mul_mem (mul_mem (mul_mem (mul_mem (hpM α) (haM i)) (hpM α)) (haM i)) (hpM α)
  have h_Q : Tendsto (fun α => (φ (∑ i, p α * a i * p α * a i * p α)).re) atTop (𝓝 S) := by
    refine hφn.tendsto_re hQα hQM ?_
    refine TendstoStrongBdd.finset_sum Finset.univ fun i _ => ?_
    have h1 := (((hlim.mul_right (a i)).mul hlim).mul_right (a i)).mul hlim
    have h2 : z * a i * z * a i * z = a i * a i := by rw [hza i, haz' i, mul_assoc, haz' i]
    rwa [h2] at h1
  -- the compressed POVM and the remainder
  set X : κ → ι → H →L[ℂ] H := fun α i => a i - p α * a i * p α with hX
  set W : κ → ι → H →L[ℂ] H := fun α i => X α i - (if i = i₀ then z - p α else 0) with hW
  have hWM : ∀ α i, W α i ∈ M := fun α i => by
    refine sub_mem (sub_mem (haM i) (mul_mem (mul_mem (hpM α) (haM i)) (hpM α))) ?_
    split_ifs
    exacts [sub_mem hzM (hpM α), zero_mem M]
  have hWsa : ∀ α i, star (W α i) = W α i := fun α i => by
    simp only [hW, hX, star_sub, star_mul, hasa, (hpP α).isSelfAdjoint.star_eq, mul_assoc]
    split_ifs <;> simp [star_sub, hzP.isSelfAdjoint.star_eq, (hpP α).isSelfAdjoint.star_eq]
  have hWlim : ∀ i, TendstoStrongBdd atTop (fun α => W α i) 0 := by
    intro i
    have hXlim : TendstoStrongBdd atTop (fun α => X α i) 0 := by
      have h1 := (TendstoStrongBdd.const (l := atTop) (a i)).sub ((hlim.mul_right (a i)).mul hlim)
      have h2 : a i - z * a i * z = 0 := by rw [hza i, haz' i, sub_self]
      rwa [h2] at h1
    have hRlim : TendstoStrongBdd atTop (fun α => (if i = i₀ then z - p α else 0)) 0 := by
      split_ifs
      · have := (TendstoStrongBdd.const (l := atTop) z).sub hlim
        rwa [sub_self] at this
      · exact TendstoStrongBdd.const 0
    have := hXlim.sub hRlim
    rwa [sub_zero] at this
  have h_W : Tendsto (fun α => (φ (∑ i, star (W α i) * W α i)).re) atTop (𝓝 0) := by
    have hlim0 : TendstoStrongBdd atTop (fun α => ∑ i, star (W α i) * W α i) 0 := by
      have : ∀ i, TendstoStrongBdd atTop (fun α => star (W α i) * W α i) 0 := fun i => by
        have := (hWlim i).mul (hWlim i)
        simp only [hWsa, mul_zero] at this ⊢
        exact this
      have := TendstoStrongBdd.finset_sum Finset.univ fun i _ => this i
      rwa [Finset.sum_const_zero] at this
    have := hφn.tendsto_re (fun α => sum_mem fun i _ => mul_mem (star_mem (hWM α i)) (hWM α i))
      (zero_mem M) hlim0
    rwa [map_zero, Complex.zero_re] at this
  -- "for α large enough"
  have E0 : ∀ᶠ α in atTop, (1 / 2 : ℝ) < (φ (p α)).re := h_m.eventually (lt_mem_nhds (by norm_num))
  have E1 : ∀ᶠ α in atTop,
      1 - ε + δ < ((φ (p α)).re)⁻¹ * (φ (∑ i, p α * a i * p α * a i * p α)).re := by
    have hprod : Tendsto (fun α => ((φ (p α)).re)⁻¹ * (φ (∑ i, p α * a i * p α * a i * p α)).re)
        atTop (𝓝 S) := by
      have := (h_m.inv₀ one_ne_zero).mul h_Q
      rwa [inv_one, one_mul] at this
    exact hprod.eventually (lt_mem_nhds (by rw [hδ]; linarith))
  have E2 : ∀ᶠ α in atTop, (1 + s⁻¹) * (φ (∑ i, star (W α i) * W α i)).re < 9 * δ / 2 := by
    have : Tendsto (fun α => (1 + s⁻¹) * (φ (∑ i, star (W α i) * W α i)).re) atTop (𝓝 0) := by
      have := h_W.const_mul (1 + s⁻¹)
      rwa [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨α, hα0, hα1, hα2⟩ := (E0.and (E1.and E2)).exists
  -- the finite case at `p α`
  set m : ℝ := (φ (p α)).re with hm
  have hm0 : 0 < m := by linarith
  have hm1 : m ≤ 1 := by
    have := re_map_le_of_mem hφ (hpM α) hzM (hple α)
    rwa [hφz, Complex.one_re] at this
  set ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ := ((m : ℂ))⁻¹ • φ with hψ
  have hψapp : ∀ x, ψ x = ((m : ℂ))⁻¹ * φ x := fun x => by
    rw [hψ, LinearMap.smul_apply, smul_eq_mul]
  have hψre : ∀ x, (ψ x).re = m⁻¹ * (φ x).re := fun x => by
    rw [hψapp, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  have hψn : IsNormalOn M ψ := hφn.smul _
  have hψpos : ∀ x ∈ M, 0 ≤ ψ (star x * x) := fun x hx => by
    rw [hψapp]
    have hinv : (0 : ℂ) ≤ ((m : ℂ))⁻¹ := by
      rw [← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (inv_nonneg.mpr hm0.le)
    exact mul_nonneg hinv (hφ x hx)
  have hψp : ψ (p α) = 1 := by
    rw [hψapp, map_eq_ofReal_re_of_mem hφ (hpM α) (hpP α).nonneg]
    show ((m : ℂ))⁻¹ * ((m : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ hm0.ne', Complex.ofReal_one]
  have hbM : ∀ i, p α * a i * p α ∈ M := fun i => mul_mem (mul_mem (hpM α) (haM i)) (hpM α)
  have hb0 : ∀ i, 0 ≤ p α * a i * p α := fun i => by
    have := conj_nonneg (ha0 i) (p α)
    rwa [(hpP α).isSelfAdjoint.star_eq] at this
  have hbsum : ∑ i, p α * a i * p α = p α := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, haz, hpz α, (hpP α).isIdempotentElem.eq]
  have hbsq : ∑ i, (p α * a i * p α) * (p α * a i * p α) = ∑ i, p α * a i * p α * a i * p α := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (p α * a i * p α) * (p α * a i * p α) = p α * a i * (p α * p α) * a i * p α := by
          noncomm_ring
      _ = p α * a i * p α * a i * p α := by rw [(hpP α).isIdempotentElem.eq]
  have hhyp : 1 - (ε - δ) < (ψ (∑ i, (p α * a i * p α) * (p α * a i * p α))).re := by
    rw [hψre, hbsq]
    have : 1 - (ε - δ) = 1 - ε + δ := by ring
    rw [this]
    exact hα1
  obtain ⟨q, hqM, hqP, hqp, hqs, hqb⟩ :=
    h α ψ hψn hψpos hψp (fun i => p α * a i * p α) hbM hb0 hbsum (ε - δ) hhyp
  -- the error of the finite case, back to `φ`
  have hY : (φ (∑ i, star (p α * a i * p α - q i) * (p α * a i * p α - q i))).re
      < 9 * (ε - δ) := by
    rw [hψre] at hqb
    have h2 := mul_lt_mul_of_pos_left hqb hm0
    rw [mul_inv_cancel_left₀ hm0.ne'] at h2
    calc _ < m * (9 * (ε - δ)) := h2
      _ ≤ 1 * (9 * (ε - δ)) := by gcongr
      _ = 9 * (ε - δ) := one_mul _
  -- the completed PVM
  have hqz : ∀ i, q i * z = q i := fun i => by
    rw [← hqp i, mul_assoc, hpz α]
  have hzq : ∀ i, z * q i = q i := fun i => by
    rw [(hz.commute _ (hqM i)).eq, hqz i]
  have hqzp : ∀ i, q i * (z - p α) = 0 := fun i => by
    rw [mul_sub, hqz i, hqp i, sub_self]
  have hzpq : ∀ i, (z - p α) * q i = 0 := fun i => by
    have := congrArg star (hqzp i)
    rwa [star_mul, (hzsubP α).isSelfAdjoint.star_eq, (hqP i).isSelfAdjoint.star_eq, star_zero]
      at this
  refine ⟨fun i => q i + (if i = i₀ then z - p α else 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine add_mem (hqM i) ?_
    split_ifs
    exacts [sub_mem hzM (hpM α), zero_mem M]
  · intro i
    by_cases hi : i = i₀
    · simp only [hi, if_true]
      refine ⟨?_, ?_⟩
      · show (q i₀ + (z - p α)) * (q i₀ + (z - p α)) = q i₀ + (z - p α)
        rw [add_mul, mul_add, mul_add, (hqP i₀).isIdempotentElem.eq, hqzp i₀, hzpq i₀,
          (hzsubP α).isIdempotentElem.eq]
        abel
      · rw [IsSelfAdjoint, star_add, (hqP i₀).isSelfAdjoint.star_eq,
          (hzsubP α).isSelfAdjoint.star_eq]
    · simp only [hi, if_false, add_zero]
      exact hqP i
  · intro i
    rw [add_mul, hqz i]
    congr 1
    split_ifs
    · rw [sub_mul, hzP.isIdempotentElem.eq, hpz α]
    · exact zero_mul _
  · rw [Finset.sum_add_distrib, hqs, Finset.sum_ite_eq' Finset.univ i₀]
    simp
  · -- the estimate: `a i − P i = (p a p − q) + W`
    have hdecomp : ∀ i, a i - (q i + (if i = i₀ then z - p α else 0))
        = (p α * a i * p α - q i) + W α i := fun i => by
      simp only [hW, hX]
      abel
    simp only [hdecomp]
    have hYM : ∀ i, p α * a i * p α - q i ∈ M := fun i => sub_mem (hbM i) (hqM i)
    have hle := sum_re_map_star_add_mul_add_le hφ hYM (hWM α) hs0
    calc (φ (∑ i, star (p α * a i * p α - q i + W α i) * (p α * a i * p α - q i + W α i))).re
        ≤ (1 + s) * (φ (∑ i, star (p α * a i * p α - q i) * (p α * a i * p α - q i))).re
          + (1 + s⁻¹) * (φ (∑ i, star (W α i) * W α i)).re := hle
      _ < (1 + s) * (9 * (ε - δ)) + 9 * δ / 2 := by
          have h1 : 0 ≤ 1 + s := by positivity
          have h2 : 0 ≤ (φ (∑ i, star (p α * a i * p α - q i) * (p α * a i * p α - q i))).re :=
            re_map_nonneg_of_mem hφ (sum_mem fun i _ => mul_mem (star_mem (hYM i)) (hYM i))
              (Finset.sum_nonneg fun i _ => star_mul_self_nonneg _)
          have h3 := mul_le_mul_of_nonneg_left hY.le h1
          linarith
      _ ≤ 9 * ε := by
          have : (1 + s) * (9 * (ε - δ)) = 9 * (ε - δ) + 9 * (s * (ε - δ)) := by ring
          have hsε : s * (ε - δ) ≤ s * ε := mul_le_mul_of_nonneg_left (by linarith) hs0.le
          have hsε' : s * ε = δ / 2 := by rw [hs]; field_simp
          nlinarith

end Orthogonalization.MvN
