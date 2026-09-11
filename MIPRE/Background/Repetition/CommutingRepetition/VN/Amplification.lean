/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Amplification.lean
-/
/-
# The amplification `N ⊗ 1` on `ℓ²(ℕ, H)` (density stage E3.4)

`H^∞ := ℓ²(ℕ, H)` and `x ⊗ 1 : (f_k) ↦ (x f_k)`.  The amplification of a von
Neumann algebra `N ⊆ B(H)` is a von Neumann algebra on `H^∞`: an operator
commuting with the matrix units `e_j e_k*` is diagonal with constant entry
`x₀`, and commuting with `y ⊗ 1` for `y ∈ N′` puts `x₀` in `N″ = N`.  A vector
`Ξ = (ξ_k)` realizes the trace-class state `T ↦ ∑ ⟪ξ_k, T ξ_k⟫` as the vector
state `⟪Ξ, (T ⊗ 1) Ξ⟫`, and is separating for `B(H) ⊗ 1` when that state is
faithful.  Used (E3.6) to put `(N, φ)` in standard form.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cyclic

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

open scoped InnerProductSpace ENNReal
open Filter Topology

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `H^∞ = ℓ²(ℕ, H)`. -/
abbrev Hinf (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Type _ :=
  lp (fun _ : ℕ => H) 2

/-! ## ℓ² bookkeeping -/

theorem two_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num

theorem summable_norm_sq (f : Hinf H) : Summable fun i => ‖f i‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp f)
  simpa only [two_toReal, Real.rpow_two] using this

theorem norm_sq_eq_tsum (f : Hinf H) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simpa only [two_toReal, Real.rpow_two] using this

theorem memℓp_of_summable_sq {g : ℕ → H} (hg : Summable fun i => ‖g i‖ ^ 2) :
    Memℓp g (2 : ℝ≥0∞) := by
  refine memℓp_gen ?_
  simpa only [two_toReal, Real.rpow_two] using hg

/-- The element of `ℓ²(ℕ, H)` with coordinates `g`. -/
noncomputable def mkVec (g : ℕ → H) (hg : Summable fun i => ‖g i‖ ^ 2) : Hinf H :=
  ⟨g, memℓp_of_summable_sq hg⟩

theorem mkVec_apply (g : ℕ → H) (hg : Summable fun i => ‖g i‖ ^ 2) (i : ℕ) : mkVec g hg i = g i :=
  rfl

theorem norm_le_of_tsum_sq_le {f : Hinf H} {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' i, ‖f i‖ ^ 2 ≤ C ^ 2) : ‖f‖ ≤ C := by
  refine lp.norm_le_of_tsum_le (p := 2) (by norm_num) hC ?_
  simpa only [two_toReal, Real.rpow_two] using h

/-! ## The amplification of an operator -/

theorem summable_norm_sq_apply (x : H →L[ℂ] H) (f : Hinf H) :
    Summable fun i => ‖x (f i)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_norm_sq f).mul_left (‖x‖ ^ 2))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (x.le_opNorm _) 2

/-- `x ⊗ 1` as a linear map. -/
noncomputable def amplPre (x : H →L[ℂ] H) : Hinf H →ₗ[ℂ] Hinf H where
  toFun f := mkVec (fun i => x (f i)) (summable_norm_sq_apply x f)
  map_add' f g := by
    apply lp.ext
    funext i
    simp only [mkVec_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply lp.ext
    funext i
    simp only [mkVec_apply, lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

theorem amplPre_apply (x : H →L[ℂ] H) (f : Hinf H) (i : ℕ) : amplPre x f i = x (f i) := rfl

theorem norm_amplPre_le (x : H →L[ℂ] H) (f : Hinf H) : ‖amplPre x f‖ ≤ ‖x‖ * ‖f‖ := by
  refine norm_le_of_tsum_sq_le (by positivity) ?_
  simp only [amplPre_apply]
  calc ∑' i, ‖x (f i)‖ ^ 2 ≤ ∑' i, ‖x‖ ^ 2 * ‖f i‖ ^ 2 := by
        refine (summable_norm_sq_apply x f).tsum_le_tsum (fun i => ?_)
          ((summable_norm_sq f).mul_left _)
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (x.le_opNorm _) 2
    _ = ‖x‖ ^ 2 * ∑' i, ‖f i‖ ^ 2 := tsum_mul_left
    _ = (‖x‖ * ‖f‖) ^ 2 := by rw [← norm_sq_eq_tsum, mul_pow]

/-- The amplification `x ⊗ 1` on `ℓ²(ℕ, H)`. -/
noncomputable def ampl (x : H →L[ℂ] H) : Hinf H →L[ℂ] Hinf H :=
  (amplPre x).mkContinuous ‖x‖ (norm_amplPre_le x)

theorem ampl_apply (x : H →L[ℂ] H) (f : Hinf H) (i : ℕ) : ampl x f i = x (f i) := rfl

theorem norm_ampl_le (x : H →L[ℂ] H) : ‖ampl x‖ ≤ ‖x‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

theorem ampl_ext {x : H →L[ℂ] H} {T : Hinf H →L[ℂ] Hinf H} (h : ∀ f i, T f i = x (f i)) :
    T = ampl x := by
  ext f i
  rw [h, ampl_apply]

theorem ampl_add (x y : H →L[ℂ] H) : ampl (x + y) = ampl x + ampl y := by
  ext f i
  simp only [ampl_apply, _root_.add_apply, lp.coeFn_add, Pi.add_apply]

theorem ampl_smul (c : ℂ) (x : H →L[ℂ] H) : ampl (c • x) = c • ampl x := by
  ext f i
  simp only [ampl_apply, _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply]

theorem ampl_zero : ampl (0 : H →L[ℂ] H) = 0 := by
  ext f i
  simp only [ampl_apply, _root_.zero_apply, lp.coeFn_zero, Pi.zero_apply]

theorem ampl_one : ampl (1 : H →L[ℂ] H) = 1 := by
  ext f i
  simp only [ampl_apply, one_apply_eq_self]

theorem ampl_mul (x y : H →L[ℂ] H) : ampl (x * y) = ampl x * ampl y := by
  ext f i
  simp only [ampl_apply, mul_apply_eq_comp]

theorem inner_ampl (x : H →L[ℂ] H) (f g : Hinf H) :
    ⟪ampl x f, g⟫_ℂ = ∑' i, ⟪x (f i), g i⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  rfl

theorem inner_ampl_right (x : H →L[ℂ] H) (f g : Hinf H) :
    ⟪f, ampl x g⟫_ℂ = ∑' i, ⟪f i, x (g i)⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  rfl

theorem ampl_star (x : H →L[ℂ] H) : ampl (star x) = star (ampl x) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [inner_ampl, inner_ampl_right]
  congr 1
  funext i
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- Amplification preserves bounded strong convergence. -/
theorem isNormalMap_ampl : IsNormalMap (ampl : (H →L[ℂ] H) → Hinf H →L[ℂ] Hinf H) := by
  intro ι l T L ⟨⟨C, hC⟩, ht⟩
  refine ⟨⟨C, fun i => (norm_ampl_le _).trans (hC i)⟩, fun f => ?_⟩
  -- `‖ampl (T i) f - ampl L f‖² = ∑ ‖(T i - L) f_k‖² → 0` by dominated convergence
  have hsq : Tendsto (fun i => ‖ampl (T i) f - ampl L f‖ ^ 2) l (𝓝 0) := by
    have hdom : Tendsto (fun i => ∑' k, ‖T i (f k) - L (f k)‖ ^ 2) l (𝓝 (∑' _k : ℕ, (0 : ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun k => (max C 0 + ‖L‖) ^ 2 * ‖f k‖ ^ 2)
        ((summable_norm_sq f).mul_left _) (fun k => ?_) (Eventually.of_forall fun i k => ?_)
      · have : Tendsto (fun i => T i (f k) - L (f k)) l (𝓝 0) := by
          simpa using (ht (f k)).sub_const (L (f k))
        simpa using (this.norm).pow 2
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        calc ‖T i (f k) - L (f k)‖ ≤ ‖T i (f k)‖ + ‖L (f k)‖ := norm_sub_le _ _
          _ ≤ ‖T i‖ * ‖f k‖ + ‖L‖ * ‖f k‖ := add_le_add ((T i).le_opNorm _) (L.le_opNorm _)
          _ ≤ max C 0 * ‖f k‖ + ‖L‖ * ‖f k‖ := by
              gcongr
              exact (hC i).trans (le_max_left _ _)
          _ = (max C 0 + ‖L‖) * ‖f k‖ := by ring
    rw [tsum_zero] at hdom
    refine hdom.congr fun i => ?_
    rw [norm_sq_eq_tsum]
    congr 1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := hsq.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using this

/-! ## Coordinate embeddings and matrix units -/

/-- The `j`-th coordinate embedding `H → ℓ²(ℕ, H)`. -/
noncomputable def sgl (j : ℕ) : H →L[ℂ] Hinf H := lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 j

/-- The `j`-th coordinate evaluation `ℓ²(ℕ, H) → H`. -/
noncomputable def ev (j : ℕ) : Hinf H →L[ℂ] H := lp.evalCLM ℂ (fun _ : ℕ => H) 2 j

theorem ev_apply (j : ℕ) (f : Hinf H) : ev j f = f j := rfl

theorem sgl_apply_self (j : ℕ) (v : H) : sgl j v j = v :=
  lp.single_apply_self (E := fun _ : ℕ => H) 2 j v

theorem sgl_apply_ne (j : ℕ) (v : H) {i : ℕ} (h : i ≠ j) : sgl j v i = 0 :=
  lp.single_apply_ne (E := fun _ : ℕ => H) 2 j v h

theorem ev_sgl_self (j : ℕ) (v : H) : ev j (sgl j v) = v := sgl_apply_self j v

theorem ev_sgl_ne {i j : ℕ} (h : i ≠ j) (v : H) : ev i (sgl j v) = 0 := sgl_apply_ne j v h

theorem ampl_sgl (x : H →L[ℂ] H) (j : ℕ) (v : H) : ampl x (sgl j v) = sgl j (x v) := by
  apply lp.ext
  funext i
  by_cases h : i = j
  · subst h
    rw [ampl_apply, sgl_apply_self, sgl_apply_self]
  · rw [ampl_apply, sgl_apply_ne j v h, sgl_apply_ne j (x v) h, map_zero]

theorem ev_ampl (x : H →L[ℂ] H) (j : ℕ) (f : Hinf H) : ev j (ampl x f) = x (ev j f) := rfl

theorem ev_ampl_sgl (x : H →L[ℂ] H) (j : ℕ) (v : H) : ev j (ampl x (sgl j v)) = x v := by
  rw [ev_ampl, ev_sgl_self]

theorem ampl_injective : Function.Injective (ampl : (H →L[ℂ] H) → Hinf H →L[ℂ] Hinf H) := by
  intro x y h
  ext v
  rw [← ev_ampl_sgl x 0 v, ← ev_ampl_sgl y 0 v, h]

/-- The matrix unit `e_j e_k*`. -/
noncomputable def unit (j k : ℕ) : Hinf H →L[ℂ] Hinf H := sgl j ∘L ev k

theorem unit_apply (j k : ℕ) (f : Hinf H) : unit j k f = sgl j (f k) := rfl

theorem unit_mul_ampl (x : H →L[ℂ] H) (j k : ℕ) : unit j k * ampl x = ampl x * unit j k := by
  ext f
  rw [mul_apply_eq_comp, mul_apply_eq_comp, unit_apply, unit_apply, ampl_apply, ampl_sgl]

theorem hasSum_sgl (f : Hinf H) : HasSum (fun k => sgl k (f k)) f :=
  lp.hasSum_single (p := 2) ENNReal.ofNat_ne_top f

/-! ## The amplified von Neumann algebra -/

variable (N : VonNeumannAlgebra H)

/-- An operator on `ℓ²(ℕ, H)` commuting with all matrix units is an amplification. -/
theorem eq_ampl_of_commute_units (T : Hinf H →L[ℂ] Hinf H)
    (h : ∀ j k, unit j k * T = T * unit j k) : T = ampl (ev 0 ∘L T ∘L sgl 0) := by
  refine ampl_ext fun f j => ?_
  -- `T (sgl k v) = sgl k (x₀ v)`
  have hT : ∀ k (v : H), T (sgl k v) = sgl k (ev 0 (T (sgl 0 v))) := by
    intro k v
    have := congrArg (fun S : Hinf H →L[ℂ] Hinf H => S (sgl 0 v)) (h k 0)
    simp only [mul_apply_eq_comp, unit_apply, sgl_apply_self] at this
    exact this.symm
  have h1 : HasSum (fun k => ev j (T (sgl k (f k)))) (ev j (T f)) :=
    ((ev j ∘L T).hasSum (hasSum_sgl f))
  have h2 : HasSum (fun k => ev j (T (sgl k (f k)))) (ev 0 (T (sgl 0 (f j)))) := by
    have : ∀ k, ev j (T (sgl k (f k))) =
        if k = j then ev 0 (T (sgl 0 (f j))) else 0 := by
      intro k
      rw [hT]
      by_cases hk : k = j
      · subst hk
        rw [if_pos rfl, ev_sgl_self]
      · rw [if_neg hk, ev_sgl_ne (Ne.symm hk)]
    simp only [this]
    exact hasSum_ite_eq j _
  exact h1.unique h2

/-- The amplification `N ⊗ 1` of a von Neumann algebra. -/
noncomputable def amplAlg : VonNeumannAlgebra (Hinf H) where
  toStarSubalgebra :=
    { carrier := {T | ∃ x ∈ N, ampl x = T}
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, mul_mem hx hy, ampl_mul x y⟩
      one_mem' := ⟨1, one_mem N, ampl_one⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, add_mem hx hy, ampl_add x y⟩
      zero_mem' := ⟨0, zero_mem N, ampl_zero⟩
      algebraMap_mem' := fun c => ⟨algebraMap ℂ _ c,
        VonNeumannAlgebra.mem_carrier.mp (N.toStarSubalgebra.algebraMap_mem c), by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ampl_smul, ampl_one]⟩
      star_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨star x, star_mem hx, ampl_star x⟩ }
  centralizer_centralizer' := by
    refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
    intro T hT
    have hunit : ∀ j k, unit j k ∈ Set.centralizer {T : Hinf H →L[ℂ] Hinf H | ∃ x ∈ N, ampl x = T} := by
      intro j k
      rintro _ ⟨x, hx, rfl⟩
      exact (unit_mul_ampl x j k).symm
    have hTu : ∀ j k, unit j k * T = T * unit j k := fun j k => hT _ (hunit j k)
    have hTe := eq_ampl_of_commute_units T hTu
    refine ⟨ev 0 ∘L T ∘L sgl 0, ?_, hTe.symm⟩
    refine mem_of_commute_commutant N fun y hy => ?_
    have hy' : ampl y ∈ Set.centralizer {T : Hinf H →L[ℂ] Hinf H | ∃ x ∈ N, ampl x = T} := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← ampl_mul, ← ampl_mul, commutant_mul_of_mem hx hy]
    have := hT _ hy'
    rw [hTe, ← ampl_mul, ← ampl_mul] at this
    exact ampl_injective this

theorem mem_amplAlg_iff {T : Hinf H →L[ℂ] Hinf H} : T ∈ amplAlg N ↔ ∃ x ∈ N, ampl x = T := Iff.rfl

theorem ampl_mem_amplAlg {x : H →L[ℂ] H} (hx : x ∈ N) : ampl x ∈ amplAlg N := ⟨x, hx, rfl⟩

/-! ## Vector states -/

/-- `⟪Ξ, (T ⊗ 1) Ξ⟫ = ∑ ⟪ξ_k, T ξ_k⟫`. -/
theorem inner_mkVec_ampl (g : ℕ → H) (hg : Summable fun i => ‖g i‖ ^ 2) (T : H →L[ℂ] H) :
    ⟪mkVec g hg, ampl T (mkVec g hg)⟫_ℂ = ∑' k, ⟪g k, T (g k)⟫_ℂ :=
  inner_ampl_right T _ _

/-- If the state `T ↦ ∑ ⟪g k, T (g k)⟫` is faithful on `S`, the vector `(g k)` is separating for
the amplification of `S`. -/
theorem isSeparating_mkVec (g : ℕ → H) (hg : Summable fun i => ‖g i‖ ^ 2)
    {S : Set (H →L[ℂ] H)} (hS : ∀ x ∈ S, ∑' k, ⟪g k, (star x * x) (g k)⟫_ℂ = 0 → x = 0) :
    IsSeparating (ampl '' S) (mkVec g hg) := by
  refine isSeparating_of_faithful ?_
  rintro _ ⟨x, hx, rfl⟩ h
  rw [← ampl_star, ← ampl_mul, inner_mkVec_ampl] at h
  rw [hS x hx h, ampl_zero]

end VN

end CommutingRepetition
