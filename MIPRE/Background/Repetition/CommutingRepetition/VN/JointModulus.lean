/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/JointModulus.lean
-/
/-
# The joint left–right spectral coupling of two moduli (WP-B7, stage G)

For `x, y ∈ L²(M)` the operators `Eₓ ∈ R(M)′` and `J E_y J ∈ L(M)′` commute
(`vnAlg_comm_conjJ`), so `VN/JointSpectral` gives their joint spectral measure
at the trace vector; pushing it forward by `ψ × ψ` gives the coupling `ν_{x,y}`
of the two modulus distributions `μₓ = ψ_* ν_{Eₓ, Ω}`, `μ_y`. This file proves
the five facts consumed by `JointSpectralData` (OTQCS/JointMeasure.lean):
probability, both marginals, the rectangle identity
`τ(1_I(hₓ) 1_J(h_y)) = ν_{x,y}(I × J)` and the cross moment
`∫ (s − t)² dν_{x,y} = ‖hvec x − hvec y‖²` (by truncation `ψₙ ↑ ψ` and the
product formula `∫ ψₙ(s) ψₙ(t) dν = ⟪ψₙ(Eₓ) Ω, ψₙ(E_y) Ω⟫`). The structures
themselves are assembled in OTQCS/JointMeasure.lean, which imports this file.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.ModulusStability
import MIPRE.Background.Repetition.CommutingRepetition.VN.JointSpectral
import MIPRE.Background.Repetition.CommutingRepetition.VN.ConjJCalc

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace GraphMod

open scoped InnerProductSpace Topology ENNReal
open Filter MeasureTheory BorelCalc

set_option linter.unusedSectionVars false

universe u

variable (M : StdTracialAlgebra.{u}) (x y : M.H)

local notation "Ω" => M.traceVector
local notation "PEx" => BorelCalc.P (Eop M x) (Eop_sa M x)
local notation "PEy" => BorelCalc.P (Eop M y) (Eop_sa M y)
local notation "bEx" => BorelCalc.bfc (Eop M x) (Eop_sa M x)
local notation "bEy" => BorelCalc.bfc (Eop M y) (Eop_sa M y)
local notation "νx" => BorelCalc.ν (Eop M x) (Eop_sa M x) M.traceVector
local notation "νy" => BorelCalc.ν (Eop M y) (Eop_sa M y) M.traceVector

/-- `Eₓ ∈ R(M)′` commutes with `J E_y J`. -/
theorem Eop_comm_conjJ : Commute (Eop M x) (M.conjJ (Eop M y)) :=
  M.vnAlg_comm_conjJ (Eop_mem M x) (Eop_mem M y)

theorem conjJ_Eop_sa : IsSelfAdjoint (M.conjJ (Eop M y)) :=
  M.conjJ_isSelfAdjoint (Eop_sa M y)

/-- The joint spectral measure of `(Eₓ, J E_y J)` at the trace vector. -/
noncomputable def νxy : Measure (ℝ × ℝ) :=
  νP (Eop M x) (M.conjJ (Eop M y)) (Eop_sa M x) (conjJ_Eop_sa M y) (Eop_comm_conjJ M x y) Ω

instance νxy_isFiniteMeasure : IsFiniteMeasure (νxy M x y) := by
  unfold νxy; infer_instance

theorem νxy_map_fst : (νxy M x y).map Prod.fst = νx := νP_map_fst _ _ _ _ _ Ω

theorem νxy_map_snd : (νxy M x y).map Prod.snd = νy := by
  unfold νxy
  rw [νP_map_snd, M.ν_conjJ (Eop_sa M y), M.J_traceVector]

theorem νxy_univ : νxy M x y Set.univ = 1 := by
  have h := νP_univ_toReal (Eop M x) (M.conjJ (Eop M y)) (Eop_sa M x) (conjJ_Eop_sa M y)
    (Eop_comm_conjJ M x y) Ω
  rw [M.norm_traceVector, one_pow] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

instance νxy_isProbabilityMeasure : IsProbabilityMeasure (νxy M x y) := ⟨νxy_univ M x y⟩

/-- Rectangle masses: `ν_{x,y}(K × K') = ⟪Ω, 1_K(Eₓ) 1_{K'}(E_y) Ω⟫`. -/
theorem νxy_prod {K K' : Set ℝ} (hK : MeasurableSet K) (hK' : MeasurableSet K') :
    ((νxy M x y (K ×ˢ K')).toReal : ℂ) = ⟪Ω, PEx K (PEy K' Ω)⟫_ℂ := by
  unfold νxy
  rw [νP_prod _ _ _ _ _ hK hK' Ω, M.P_conjJ (Eop_sa M y),
    M.conjJ_apply_traceVector_of_sa (PE_mem M y K') (P_isSelfAdjoint _ _ K')]

/-- The product formula at the trace vector, for bounded Borel `g, h`:
`∫ g(s) h(t) dν_{x,y} = re ⟪g(Eₓ) Ω, h(E_y) Ω⟫`. -/
theorem integral_νxy_mul {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) :
    ∫ p, g p.1 * h p.2 ∂(νxy M x y) = (⟪bEx g Ω, bEy h Ω⟫_ℂ).re := by
  unfold νxy
  rw [integral_νP_mul _ _ _ _ _ hg hh Ω, inner_sa (bfc_isSelfAdjoint _ _ hg),
    M.bfc_conjJ (Eop_sa M y), M.conjJ_apply_traceVector_of_sa (bE_mem M y hh)
    (bfc_isSelfAdjoint _ _ hh)]

/-! ### The coupling of the modulus distributions -/

theorem measurable_ψψ : Measurable (Prod.map ψ ψ) := ψ_measurable.prodMap ψ_measurable

/-- **The joint coupling** `ν_{x,y} = (ψ × ψ)_* ν_{Eₓ, JE_yJ; Ω}` of `μₓ` and `μ_y`. -/
noncomputable def νψ : Measure (ℝ × ℝ) := (νxy M x y).map (Prod.map ψ ψ)

theorem νψ_prob : IsProbabilityMeasure (νψ M x y) :=
  Measure.isProbabilityMeasure_map (measurable_ψψ).aemeasurable

theorem νψ_map_fst : (νψ M x y).map Prod.fst = μx M x := by
  rw [νψ, Measure.map_map measurable_fst measurable_ψψ,
    show Prod.fst ∘ Prod.map ψ ψ = ψ ∘ Prod.fst from rfl,
    ← Measure.map_map ψ_measurable measurable_fst, νxy_map_fst]
  rfl

theorem νψ_map_snd : (νψ M x y).map Prod.snd = μx M y := by
  rw [νψ, Measure.map_map measurable_snd measurable_ψψ,
    show Prod.snd ∘ Prod.map ψ ψ = ψ ∘ Prod.snd from rfl,
    ← Measure.map_map ψ_measurable measurable_snd, νxy_map_snd]
  rfl

/-- The rectangle identity in the form consumed by `JointSpectralData.cross`. -/
theorem cross {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    M.vnModel.τ (projx M x I * projx M y J) = ((νψ M x y (I ×ˢ J)).toReal : ℂ) := by
  rw [νψ, Measure.map_apply measurable_ψψ (hI.prod hJ), Set.preimage_prod_map_prod,
    νxy_prod M x y (ψ_measurable hI) (ψ_measurable hJ)]
  rfl

/-! ### The cross moment -/

theorem integrable_ψ_sq_fst : Integrable (fun p : ℝ × ℝ => ψ p.1 ^ 2) (νxy M x y) := by
  have h := integrable_ψ_sq M x
  rw [← νxy_map_fst M x y] at h
  exact (integrable_map_measure (ψ_measurable.pow_const 2).aestronglyMeasurable
    measurable_fst.aemeasurable).mp h

theorem integrable_ψ_sq_snd : Integrable (fun p : ℝ × ℝ => ψ p.2 ^ 2) (νxy M x y) := by
  have h := integrable_ψ_sq M y
  rw [← νxy_map_snd M x y] at h
  exact (integrable_map_measure (ψ_measurable.pow_const 2).aestronglyMeasurable
    measurable_snd.aemeasurable).mp h

theorem integrable_ψ_mul : Integrable (fun p : ℝ × ℝ => ψ p.1 * ψ p.2) (νxy M x y) :=
  Integrable.mono' ((integrable_ψ_sq_fst M x y).add (integrable_ψ_sq_snd M x y))
    ((ψ_measurable.comp measurable_fst).mul (ψ_measurable.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ψ_nonneg _) (ψ_nonneg _))]
      show ψ p.1 * ψ p.2 ≤ ψ p.1 ^ 2 + ψ p.2 ^ 2
      nlinarith [sq_nonneg (ψ p.1 - ψ p.2)])

theorem integral_ψ_sq_fst : ∫ p, ψ p.1 ^ 2 ∂(νxy M x y) = ‖x‖ ^ 2 := by
  have h := integral_ψ_sq M x
  rw [← νxy_map_fst M x y, integral_map measurable_fst.aemeasurable
    (ψ_measurable.pow_const 2).aestronglyMeasurable] at h
  exact h

theorem integral_ψ_sq_snd : ∫ p, ψ p.2 ^ 2 ∂(νxy M x y) = ‖y‖ ^ 2 := by
  have h := integral_ψ_sq M y
  rw [← νxy_map_snd M x y, integral_map measurable_snd.aemeasurable
    (ψ_measurable.pow_const 2).aestronglyMeasurable] at h
  exact h

theorem ψn_mul_mono (p : ℝ × ℝ) : Monotone fun n => ψn n p.1 * ψn n p.2 := fun _ _ h =>
  mul_le_mul (ψn_mono _ h) (ψn_mono _ h) (ψn_nonneg _ _) (ψn_nonneg _ _)

theorem ψn_mul_tendsto (p : ℝ × ℝ) :
    Tendsto (fun n => ψn n p.1 * ψn n p.2) atTop (𝓝 (ψ p.1 * ψ p.2)) :=
  (ψn_tendsto p.1).mul (ψn_tendsto p.2)

/-- The cross term: `∫ ψ(s) ψ(t) dν_{x,y} = re ⟪hvec x, hvec y⟫`. -/
theorem integral_ψ_mul : ∫ p, ψ p.1 * ψ p.2 ∂(νxy M x y) = (⟪hvec M x, hvec M y⟫_ℂ).re := by
  have h1 : Tendsto (fun n => ∫ p, ψn n p.1 * ψn n p.2 ∂(νxy M x y)) atTop
      (𝓝 (∫ p, ψ p.1 * ψ p.2 ∂(νxy M x y))) :=
    integral_tendsto_of_tendsto_of_monotone
      (fun n => by
        obtain ⟨C, hC⟩ := (ψn_bdd n).2
        refine integrable_of_bdd' (((ψn_bdd n).1.comp measurable_fst).mul
          ((ψn_bdd n).1.comp measurable_snd)) (C := C * C) fun p => ?_
        rw [abs_mul]
        exact mul_le_mul (hC _) (hC _) (abs_nonneg _) ((abs_nonneg _).trans (hC 0)))
      (integrable_ψ_mul M x y) (ae_of_all _ ψn_mul_mono) (ae_of_all _ ψn_mul_tendsto)
  have h2 : Tendsto (fun n => ∫ p, ψn n p.1 * ψn n p.2 ∂(νxy M x y)) atTop
      (𝓝 ((⟪hvec M x, hvec M y⟫_ℂ).re)) := by
    have := ((Complex.continuous_re.tendsto _).comp
      ((hvec_tendsto M x).inner (hvec_tendsto M y)))
    refine this.congr fun n => ?_
    simp only [Function.comp]
    rw [integral_νxy_mul M x y (ψn_bdd n) (ψn_bdd n)]
  exact tendsto_nhds_unique h1 h2

/-- **The cross moment**: `∫ (s − t)² dν_{x,y}(s, t) = ‖hvec x − hvec y‖²`. -/
theorem crossMoment :
    ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(νψ M x y) = ‖hvec M x - hvec M y‖ ^ 2 := by
  rw [νψ, integral_map (f := fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) measurable_ψψ.aemeasurable
    ((measurable_fst.sub measurable_snd).pow_const 2 :
      Measurable fun p : ℝ × ℝ => (p.1 - p.2) ^ 2).aestronglyMeasurable]
  have e : ∀ p : ℝ × ℝ, ((Prod.map ψ ψ p).1 - (Prod.map ψ ψ p).2) ^ 2 =
      (ψ p.1 ^ 2 + ψ p.2 ^ 2) - 2 * (ψ p.1 * ψ p.2) := fun p => by
    simp only [Prod.map_apply']; ring
  simp only [e]
  rw [integral_sub (f := fun p : ℝ × ℝ => ψ p.1 ^ 2 + ψ p.2 ^ 2)
    (g := fun p : ℝ × ℝ => 2 * (ψ p.1 * ψ p.2))
    ((integrable_ψ_sq_fst M x y).add (integrable_ψ_sq_snd M x y))
    ((integrable_ψ_mul M x y).const_mul 2),
    integral_add (f := fun p : ℝ × ℝ => ψ p.1 ^ 2) (g := fun p : ℝ × ℝ => ψ p.2 ^ 2)
    (integrable_ψ_sq_fst M x y) (integrable_ψ_sq_snd M x y), integral_const_mul,
    integral_ψ_sq_fst, integral_ψ_sq_snd, integral_ψ_mul, ← norm_hvec M x, ← norm_hvec M y]
  have hn : ‖hvec M x - hvec M y‖ ^ 2 =
      ‖hvec M x‖ ^ 2 - 2 * (⟪hvec M x, hvec M y⟫_ℂ).re + ‖hvec M y‖ ^ 2 :=
    norm_sub_sq (𝕜 := ℂ) (hvec M x) (hvec M y)
  rw [hn]
  ring

end GraphMod

end CommutingRepetition
