/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/LeftModulusData.lean
-/
/-
# The spectral package of a vector (Stage D3 of `PLAN-modulus-family.md`)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

With the graph data `E` of `x`, the modulus vector `hvec = lim ψₙ(E)Ω` and the
polar element `v = W*` of `VN/LeftModulus.lean`, we assemble the consumed
`SpectralData M.vnModel x`:
* `μ := ψ_* ν_Ω` (`ν_Ω` the spectral measure of `E` at the trace vector), a
  probability measure on `[0, ∞)` with `∫ b² dμ = ∫ ψ² dν_Ω = ‖x‖²` (monotone
  convergence from `∫ ψₙ² dν_Ω = ‖P[0,aₙ] x‖² ≤ ‖x‖²`);
* `proj I := P (ψ⁻¹ I)`: the ∗-lattice identities are those of the PVM `P`, the
  trace masses are `μ`, the support absorption is `P(0,1) P(ψ⁻¹ I) = P(ψ⁻¹ I)`
  for `I ⊆ (0, ∞)`;
* the two pairings `⟪P(ψ⁻¹I) Ω, hvec⟫ = ∫_I b dμ` and
  `⟪hvec, Rop (P(ψ⁻¹I)) hvec⟫ = ∫_I b² dμ` by monotone convergence along `ψₙ`.
Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.LeftModulus

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace GraphMod

open scoped InnerProductSpace Topology ENNReal
open Filter MeasureTheory BorelCalc

set_option linter.unusedSectionVars false

universe u

/-! ### Pointwise convergence of truncations -/

theorem indicator_iUnion_tendsto' {I : ℕ → Set ℝ} (hmono : Monotone I) (f : ℝ → ℝ) (t : ℝ) :
    Tendsto (fun n => (I n).indicator f t) atTop (𝓝 ((⋃ n, I n).indicator f t)) := by
  by_cases ht : t ∈ ⋃ n, I n
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    rw [Set.indicator_of_mem ht]
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨i, fun n hn => ?_⟩)
    show f t = (I n).indicator f t
    rw [Set.indicator_of_mem (hmono hn hi)]
  · rw [Set.indicator_of_notMem ht]
    refine tendsto_const_nhds.congr fun n => ?_
    show (0 : ℝ) = (I n).indicator f t
    rw [Set.indicator_of_notMem fun h => ht (Set.mem_iUnion.mpr ⟨n, h⟩)]

theorem ψ_eq_indicator : ψ = (Set.Ico 0 1).indicator ψ := by
  funext t
  by_cases ht : t ∈ Set.Ico (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, ψ_of_not fun h => ht ⟨h.1.le, h.2⟩]

theorem ψn_tendsto (t : ℝ) : Tendsto (fun n => ψn n t) atTop (𝓝 (ψ t)) := by
  have := indicator_iUnion_tendsto' monotone_Icc_aN ψ t
  rwa [iUnion_Icc_aN, ← ψ_eq_indicator] at this

theorem ψn_mono (t : ℝ) : Monotone fun n => ψn n t := fun m n h => by
  show ψn m t ≤ ψn n t
  unfold ψn
  by_cases ht : t ∈ Set.Icc 0 (aN m)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (monotone_Icc_aN h ht)]
  · rw [Set.indicator_of_notMem ht]; exact ψn_nonneg n t

theorem ψn_le_ψ (n : ℕ) (t : ℝ) : ψn n t ≤ ψ t := by
  unfold ψn
  by_cases ht : t ∈ Set.Icc 0 (aN n)
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]; exact ψ_nonneg t

theorem ψn_sq_mono (t : ℝ) : Monotone fun n => ψn n t ^ 2 := fun m n h =>
  pow_le_pow_left₀ (ψn_nonneg m t) (ψn_mono t h) 2

theorem ψn_sq_tendsto (t : ℝ) : Tendsto (fun n => ψn n t ^ 2) atTop (𝓝 (ψ t ^ 2)) :=
  (ψn_tendsto t).pow 2

theorem Bdd.sq {g : ℝ → ℝ} (hg : Bdd g) : Bdd fun t => g t ^ 2 := by
  have : (fun t => g t ^ 2) = g * g := by funext t; rw [Pi.mul_apply, pow_two]
  rw [this]; exact hg.mul hg

/-! ### The spectral distribution of the modulus -/

variable (M : StdTracialAlgebra.{u}) (x : M.H)

local notation "bE" => BorelCalc.bfc (Eop M x) (Eop_sa M x)
local notation "PE" => BorelCalc.P (Eop M x) (Eop_sa M x)
local notation "Ω" => M.traceVector
local notation "ν₀" => BorelCalc.ν (Eop M x) (Eop_sa M x) M.traceVector

theorem ν₀_univ : ν₀ Set.univ = 1 := by
  have h := BorelCalc.ν_univ_toReal (Eop M x) (Eop_sa M x) Ω
  rw [M.norm_traceVector, one_pow] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

instance ν₀_isProbabilityMeasure : IsProbabilityMeasure ν₀ := ⟨ν₀_univ M x⟩

/-- The spectral distribution `μ = ψ_* ν_Ω` of the left modulus. -/
noncomputable def μx : Measure ℝ := Measure.map ψ ν₀

theorem μx_prob : IsProbabilityMeasure (μx M x) :=
  ⟨by rw [μx, Measure.map_apply ψ_measurable MeasurableSet.univ, Set.preimage_univ, ν₀_univ M x]⟩

theorem μx_apply {I : Set ℝ} (hI : MeasurableSet I) : μx M x I = ν₀ (ψ ⁻¹' I) :=
  Measure.map_apply ψ_measurable hI

theorem μx_Iio : μx M x (Set.Iio 0) = 0 := by
  rw [μx_apply M x measurableSet_Iio]
  have : ψ ⁻¹' Set.Iio 0 = ∅ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact ψ_nonneg t
  rw [this, measure_empty]

/-! ### Integrability of the modulus -/

theorem integral_ψn_sq (n : ℕ) : ∫ t, ψn n t ^ 2 ∂ν₀ = ‖PE (Set.Icc 0 (aN n)) x‖ ^ 2 := by
  have h := BorelCalc.norm_bfc_apply_sq (Eop M x) (Eop_sa M x) (ψn_bdd n) Ω
  rw [norm_ψn_traceVector_sq] at h
  rw [h]
  congr 1
  funext t
  rw [Pi.mul_apply, pow_two]

theorem lintegral_ψ_sq_le : ∫⁻ t, ENNReal.ofReal (ψ t ^ 2) ∂ν₀ ≤ ENNReal.ofReal (‖x‖ ^ 2) := by
  have hmono : Monotone fun n => fun t => ENNReal.ofReal (ψn n t ^ 2) :=
    fun m n h t => ENNReal.ofReal_le_ofReal (ψn_sq_mono t h)
  have hmeas : ∀ n, Measurable fun t => ENNReal.ofReal (ψn n t ^ 2) :=
    fun n => ((ψn_bdd n).1.pow_const 2).ennreal_ofReal
  have hsup : ∀ t, ⨆ n, ENNReal.ofReal (ψn n t ^ 2) = ENNReal.ofReal (ψ t ^ 2) := fun t => by
    have h1 := (ENNReal.continuous_ofReal.tendsto _).comp (ψn_sq_tendsto t)
    have h2 := tendsto_atTop_iSup
      (fun m n h => ENNReal.ofReal_le_ofReal (ψn_sq_mono t h) :
        Monotone fun n => ENNReal.ofReal (ψn n t ^ 2))
    exact tendsto_nhds_unique h2 h1
  calc ∫⁻ t, ENNReal.ofReal (ψ t ^ 2) ∂ν₀
      = ∫⁻ t, ⨆ n, ENNReal.ofReal (ψn n t ^ 2) ∂ν₀ := by
        refine lintegral_congr fun t => ?_
        rw [hsup]
    _ = ⨆ n, ∫⁻ t, ENNReal.ofReal (ψn n t ^ 2) ∂ν₀ := lintegral_iSup hmeas hmono
    _ ≤ ENNReal.ofReal (‖x‖ ^ 2) := by
        refine iSup_le fun n => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal ((Bdd.sq (ψn_bdd n)).integrable _)
          (ae_of_all _ fun t => sq_nonneg _), integral_ψn_sq]
        exact ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (norm_PE_Icc_aN_le M x n) 2)

theorem integrable_ψ_sq : Integrable (fun t => ψ t ^ 2) ν₀ := by
  refine ⟨(ψ_measurable.pow_const 2).aestronglyMeasurable, ?_⟩
  show ∫⁻ t, ‖ψ t ^ 2‖ₑ ∂ν₀ < ⊤
  have : ∀ t, ‖ψ t ^ 2‖ₑ = ENNReal.ofReal (ψ t ^ 2) := fun t => Real.enorm_eq_ofReal (sq_nonneg _)
  simp only [this]
  exact (lintegral_ψ_sq_le M x).trans_lt ENNReal.ofReal_lt_top

theorem integral_ψ_sq : ∫ t, ψ t ^ 2 ∂ν₀ = ‖x‖ ^ 2 := by
  have h1 : Tendsto (fun n => ∫ t, ψn n t ^ 2 ∂ν₀) atTop (𝓝 (∫ t, ψ t ^ 2 ∂ν₀)) :=
    integral_tendsto_of_tendsto_of_monotone (fun n => (Bdd.sq (ψn_bdd n)).integrable _)
      (integrable_ψ_sq M x) (ae_of_all _ ψn_sq_mono) (ae_of_all _ ψn_sq_tendsto)
  have h2 : Tendsto (fun n => ∫ t, ψn n t ^ 2 ∂ν₀) atTop (𝓝 (‖x‖ ^ 2)) := by
    refine (tendsto_norm_PE_Icc_aN M x).congr fun n => ?_
    rw [integral_ψn_sq]
  exact tendsto_nhds_unique h1 h2

theorem integrable_ψ : Integrable ψ ν₀ :=
  Integrable.mono' (g := fun t => 1 + ψ t ^ 2) ((integrable_const (1 : ℝ)).add (integrable_ψ_sq M x))
    ψ_measurable.aestronglyMeasurable (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ψ_nonneg t)]
      nlinarith [sq_nonneg (ψ t - 1)])

theorem moment2 : ∫ b, b ^ 2 ∂(μx M x) = ‖x‖ ^ 2 := by
  rw [μx, integral_map (f := fun b : ℝ => b ^ 2) ψ_measurable.aemeasurable
    (measurable_id.pow_const 2 : Measurable fun b : ℝ => b ^ 2).aestronglyMeasurable]
  exact integral_ψ_sq M x

/-! ### The band projections -/

/-- `proj I = 1_I(h_x) = P (ψ⁻¹ I)`, as an element of the von Neumann algebra. -/
noncomputable def projx (I : Set ℝ) : ↥M.vnAlg := ⟨PE (ψ ⁻¹' I), PE_mem M x _⟩

theorem projx_val (I : Set ℝ) : (projx M x I).1 = PE (ψ ⁻¹' I) := rfl

theorem projx_star (I : Set ℝ) : star (projx M x I) = projx M x I :=
  Subtype.ext (BorelCalc.star_P _ _ _)

theorem projx_empty : projx M x ∅ = 0 :=
  Subtype.ext (by show PE (ψ ⁻¹' ∅) = 0; rw [Set.preimage_empty, BorelCalc.P_empty])

theorem projx_inter {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    projx M x I * projx M x J = projx M x (I ∩ J) :=
  Subtype.ext (by
    show PE (ψ ⁻¹' I) * PE (ψ ⁻¹' J) = PE (ψ ⁻¹' (I ∩ J))
    rw [Set.preimage_inter, BorelCalc.P_inter _ _ (ψ_measurable hI) (ψ_measurable hJ)])

theorem projx_union {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hd : Disjoint I J) : projx M x (I ∪ J) = projx M x I + projx M x J :=
  Subtype.ext (by
    show PE (ψ ⁻¹' (I ∪ J)) = PE (ψ ⁻¹' I) + PE (ψ ⁻¹' J)
    rw [Set.preimage_union,
      BorelCalc.P_union _ _ (ψ_measurable hI) (ψ_measurable hJ) (hd.preimage ψ)])

theorem projx_trace {I : Set ℝ} (hI : MeasurableSet I) :
    M.vnModel.τ (projx M x I) = (((μx M x) I).toReal : ℂ) := by
  rw [M.vnModel_τ, μx_apply M x hI]
  exact BorelCalc.inner_P _ _ (ψ_measurable hI) Ω

theorem preimage_ψ_subset {I : Set ℝ} (hsub : I ⊆ Set.Ioi 0) : ψ ⁻¹' I ⊆ Set.Ioo 0 1 :=
  fun t ht => (ψ_pos_iff t).mp (hsub ht)

theorem projx_absorb {I : Set ℝ} (hI : MeasurableSet I) (hsub : I ⊆ Set.Ioi 0) :
    (vEl M x * star (vEl M x)) * projx M x I = projx M x I :=
  Subtype.ext (by
    show (vEl M x * star (vEl M x)).1 * PE (ψ ⁻¹' I) = PE (ψ ⁻¹' I)
    rw [vEl_mul_star_vEl_val, BorelCalc.P_inter _ _ measurableSet_Ioo (ψ_measurable hI),
      Set.inter_eq_right.mpr (preimage_ψ_subset hsub)])

/-! ### The two pairings -/

theorem indicator_one_mul_eq {J : Set ℝ} (f : ℝ → ℝ) (t : ℝ) :
    J.indicator (1 : ℝ → ℝ) t * f t = J.indicator f t := by
  by_cases ht : t ∈ J
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]

/-- `⟪P J Ω, ψₙ(E) Ω⟫ = ∫ 1_J ψₙ dν_Ω`. -/
theorem inner_PE_ψn {J : Set ℝ} (hJ : MeasurableSet J) (n : ℕ) :
    ⟪PE J Ω, bE (ψn n) Ω⟫_ℂ = ((∫ t, J.indicator (1 : ℝ → ℝ) t * ψn n t ∂ν₀ : ℝ) : ℂ) := by
  rw [BorelCalc.P, inner_bE_bE M x (Bdd.indicator hJ) (ψn_bdd n),
    inner_bE_traceVector M x ((Bdd.indicator hJ).mul (ψn_bdd n))]
  rfl

/-- `⟪ψₙ(E) Ω, P J ψₙ(E) Ω⟫ = ∫ ψₙ 1_J ψₙ dν_Ω`. -/
theorem inner_ψn_PE_ψn {J : Set ℝ} (hJ : MeasurableSet J) (n : ℕ) :
    ⟪bE (ψn n) Ω, PE J (bE (ψn n) Ω)⟫_ℂ
      = ((∫ t, ψn n t * (J.indicator (1 : ℝ → ℝ) t * ψn n t) ∂ν₀ : ℝ) : ℂ) := by
  rw [BorelCalc.P, ← Resolver.Douglas.mulA, ← BorelCalc.bfc_mul _ _ (Bdd.indicator hJ) (ψn_bdd n),
    inner_bE_bE M x (ψn_bdd n) ((Bdd.indicator hJ).mul (ψn_bdd n)),
    inner_bE_traceVector M x ((ψn_bdd n).mul ((Bdd.indicator hJ).mul (ψn_bdd n)))]
  rfl

theorem indicator_ψn_mono {J : Set ℝ} (t : ℝ) :
    Monotone fun n => J.indicator (1 : ℝ → ℝ) t * ψn n t := fun m n h =>
  mul_le_mul_of_nonneg_left (ψn_mono t h) (indicator_one_nonneg J t)

theorem indicator_ψn_tendsto {J : Set ℝ} (t : ℝ) :
    Tendsto (fun n => J.indicator (1 : ℝ → ℝ) t * ψn n t) atTop (𝓝 (J.indicator ψ t)) := by
  rw [← indicator_one_mul_eq ψ t]
  exact tendsto_const_nhds.mul (ψn_tendsto t)

theorem indicator_ψn_ψn_mono {J : Set ℝ} (t : ℝ) :
    Monotone fun n => ψn n t * (J.indicator (1 : ℝ → ℝ) t * ψn n t) := fun m n h => by
  show ψn m t * (J.indicator (1 : ℝ → ℝ) t * ψn m t) ≤ ψn n t * (J.indicator (1 : ℝ → ℝ) t * ψn n t)
  by_cases ht : t ∈ J
  · rw [Set.indicator_of_mem ht, Pi.one_apply, one_mul, one_mul]
    exact mul_le_mul (ψn_mono t h) (ψn_mono t h) (ψn_nonneg m t) (ψn_nonneg n t)
  · rw [Set.indicator_of_notMem ht]; simp

theorem indicator_ψn_ψn_tendsto {J : Set ℝ} (t : ℝ) :
    Tendsto (fun n => ψn n t * (J.indicator (1 : ℝ → ℝ) t * ψn n t)) atTop
      (𝓝 (J.indicator (fun t => ψ t ^ 2) t)) := by
  by_cases ht : t ∈ J
  · simp only [Set.indicator_of_mem ht, Pi.one_apply, one_mul]
    rw [sq]
    exact (ψn_tendsto t).mul (ψn_tendsto t)
  · simp only [Set.indicator_of_notMem ht, zero_mul, mul_zero]
    exact tendsto_const_nhds

/-- The first pairing: `⟪P(ψ⁻¹I) Ω, hvec⟫ = ∫_I b dμ`. -/
theorem pairing1 {I : Set ℝ} (hI : MeasurableSet I) :
    ⟪M.vnModel.ι (projx M x I), hvec M x⟫_ℂ = ((∫ b in I, b ∂(μx M x) : ℝ) : ℂ) := by
  have hJ : MeasurableSet (ψ ⁻¹' I) := ψ_measurable hI
  rw [M.vnModel_ι, projx_val]
  have hrhs : ∫ b in I, b ∂(μx M x) = ∫ t, (ψ ⁻¹' I).indicator ψ t ∂ν₀ := by
    rw [← integral_indicator hI, μx, integral_map (f := I.indicator fun b : ℝ => b)
      ψ_measurable.aemeasurable
      (measurable_id.indicator hI : Measurable (I.indicator fun b : ℝ => b)).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    exact (Set.indicator_comp_right (g := fun b : ℝ => b) ψ (s := I) (x := t)).symm
  rw [hrhs]
  have h1 : Tendsto (fun n => ⟪PE (ψ ⁻¹' I) Ω, bE (ψn n) Ω⟫_ℂ) atTop
      (𝓝 ⟪PE (ψ ⁻¹' I) Ω, hvec M x⟫_ℂ) := tendsto_const_nhds.inner (hvec_tendsto M x)
  have h2 : Tendsto (fun n => ⟪PE (ψ ⁻¹' I) Ω, bE (ψn n) Ω⟫_ℂ) atTop
      (𝓝 (((∫ t, (ψ ⁻¹' I).indicator ψ t ∂ν₀ : ℝ) : ℂ))) := by
    have hint : Tendsto (fun n => ∫ t, (ψ ⁻¹' I).indicator (1 : ℝ → ℝ) t * ψn n t ∂ν₀) atTop
        (𝓝 (∫ t, (ψ ⁻¹' I).indicator ψ t ∂ν₀)) :=
      integral_tendsto_of_tendsto_of_monotone
        (fun n => ((Bdd.indicator hJ).mul (ψn_bdd n)).integrable _)
        ((integrable_ψ M x).indicator hJ) (ae_of_all _ indicator_ψn_mono)
        (ae_of_all _ indicator_ψn_tendsto)
    exact ((Complex.continuous_ofReal.tendsto _).comp hint).congr fun n =>
      (inner_PE_ψn M x hJ n).symm
  exact tendsto_nhds_unique h1 h2

theorem J_PE_hvec {J : Set ℝ} (hJ : MeasurableSet J) :
    M.J (PE J (hvec M x)) = PE J (hvec M x) := by
  have hn : ∀ n, M.J (PE J (bE (ψn n) Ω)) = PE J (bE (ψn n) Ω) := fun n => by
    rw [← Resolver.Douglas.mulA, M.J_apply_traceVector (mul_mem (PE_mem M x J) (bE_mem M x (ψn_bdd n))),
      star_mul, (BorelCalc.bfc_isSelfAdjoint _ _ (ψn_bdd n)).star_eq, BorelCalc.star_P,
      BorelCalc.P_comm_bfc _ _ hJ (ψn_bdd n)]
  have h1 : Tendsto (fun n => M.J (PE J (bE (ψn n) Ω))) atTop (𝓝 (M.J (PE J (hvec M x)))) :=
    (M.J.continuous.tendsto _).comp (((PE J).continuous.tendsto _).comp (hvec_tendsto M x))
  have h2 : Tendsto (fun n => M.J (PE J (bE (ψn n) Ω))) atTop (𝓝 (PE J (hvec M x))) :=
    (((PE J).continuous.tendsto _).comp (hvec_tendsto M x)).congr fun n => (hn n).symm
  exact tendsto_nhds_unique h1 h2

/-- The second pairing: `⟪hvec, Rop (P(ψ⁻¹I)) hvec⟫ = ∫_I b² dμ`. -/
theorem pairing2 {I : Set ℝ} (hI : MeasurableSet I) :
    ⟪hvec M x, M.vnModel.Rop (projx M x I) (hvec M x)⟫_ℂ
      = ((∫ b in I, b ^ 2 ∂(μx M x) : ℝ) : ℂ) := by
  have hJ : MeasurableSet (ψ ⁻¹' I) := ψ_measurable hI
  have hRop : M.vnModel.Rop (projx M x I) (hvec M x) = PE (ψ ⁻¹' I) (hvec M x) := by
    rw [M.vnModel_Rop_eq]
    show M.J ((star (projx M x I)).1 (M.J (hvec M x))) = _
    rw [projx_star, projx_val, J_hvec, J_PE_hvec M x hJ]
  rw [hRop]
  have hrhs : ∫ b in I, b ^ 2 ∂(μx M x) = ∫ t, (ψ ⁻¹' I).indicator (fun t => ψ t ^ 2) t ∂ν₀ := by
    rw [← integral_indicator hI, μx, integral_map (f := I.indicator fun b : ℝ => b ^ 2)
      ψ_measurable.aemeasurable
      ((measurable_id.pow_const 2).indicator hI :
        Measurable (I.indicator fun b : ℝ => b ^ 2)).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    exact (Set.indicator_comp_right (g := fun b : ℝ => b ^ 2) ψ (s := I) (x := t)).symm
  rw [hrhs]
  have h1 : Tendsto (fun n => ⟪bE (ψn n) Ω, PE (ψ ⁻¹' I) (bE (ψn n) Ω)⟫_ℂ) atTop
      (𝓝 ⟪hvec M x, PE (ψ ⁻¹' I) (hvec M x)⟫_ℂ) :=
    (hvec_tendsto M x).inner (((PE (ψ ⁻¹' I)).continuous.tendsto _).comp (hvec_tendsto M x))
  have h2 : Tendsto (fun n => ⟪bE (ψn n) Ω, PE (ψ ⁻¹' I) (bE (ψn n) Ω)⟫_ℂ) atTop
      (𝓝 (((∫ t, (ψ ⁻¹' I).indicator (fun t => ψ t ^ 2) t ∂ν₀ : ℝ) : ℂ))) := by
    have hint : Tendsto
        (fun n => ∫ t, ψn n t * ((ψ ⁻¹' I).indicator (1 : ℝ → ℝ) t * ψn n t) ∂ν₀) atTop
        (𝓝 (∫ t, (ψ ⁻¹' I).indicator (fun t => ψ t ^ 2) t ∂ν₀)) :=
      integral_tendsto_of_tendsto_of_monotone
        (fun n => ((ψn_bdd n).mul ((Bdd.indicator hJ).mul (ψn_bdd n))).integrable _)
        ((integrable_ψ_sq M x).indicator hJ) (ae_of_all _ indicator_ψn_ψn_mono)
        (ae_of_all _ indicator_ψn_ψn_tendsto)
    exact ((Complex.continuous_ofReal.tendsto _).comp hint).congr fun n =>
      (inner_ψn_PE_ψn M x hJ n).symm
  exact tendsto_nhds_unique h1 h2

/-! ### Assembly -/

/-- **The left-modulus spectral package** of `x` in the von Neumann model. -/
noncomputable def spectralData : SpectralData M.vnModel x where
  μ := μx M x
  μ_prob := μx_prob M x
  μ_nonneg := μx_Iio M x
  hvec := hvec M x
  hvec_norm := norm_hvec M x
  moment2 := moment2 M x
  v := vEl M x
  polar := vnModel_Rop_vEl_hvec M x
  supp_vec := vnModel_Rop_vEl_mul_star_hvec M x
  proj := projx M x
  proj_star := projx_star M x
  proj_empty := projx_empty M x
  proj_inter := fun _ _ hI hJ => projx_inter M x hI hJ
  proj_union := fun _ _ hI hJ hd => projx_union M x hI hJ hd
  proj_trace := fun _ hI => projx_trace M x hI
  absorb := fun _ hI hsub => projx_absorb M x hI hsub
  pairing1 := fun _ hI => pairing1 M x hI
  pairing2 := fun _ hI => pairing2 M x hI

theorem spectralData_hvec : (spectralData M x).hvec = hvec M x := rfl

theorem spectralData_μ : (spectralData M x).μ = μx M x := rfl

theorem spectralData_proj (I : Set ℝ) : ((spectralData M x).proj I).1 = PE (ψ ⁻¹' I) := rfl

end GraphMod

end CommutingRepetition
