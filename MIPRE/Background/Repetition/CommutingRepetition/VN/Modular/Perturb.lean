/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/Perturb.lean
-/
/-
# The modular operator of a perturbed state (density stage E6.2, HJX (M3))

For a self-adjoint `a ∈ M` in the centralizer (`[a, R] = 0`) and `ξ = e^{-a/2}Ω`:

  `R(M, ξ) = 2 R (R + e^{a′−a}(2 − R))⁻¹`,   `Δ_ξ^{it} = e^{it(a′−a)} Δ^{it}`,

where `a′ = J a J ∈ M′`. Everything is built from the joint Borel calculus of the commuting
self-adjoint pair `(R, B)`, `B = a′ − a`: the inverse is the `jbfc` of an explicit bounded
continuous function, and the modular group comes out of the composition rule `cbfc_jbfc`
together with `θ(2l/(l + e^m(2−l))) = m + θ(l)` on `(0,2)`.

The identification uses the uniqueness lemma `R_eq_of_proj`: on `𝒦(M, ξ) = e^{-a′/2}𝒦(M, Ω)`
the candidate pair `(R', A')` is the identity of `(2 P_ξ)`, and it vanishes on `𝒦(M, ξ)ᗮ`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.CentralExp
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Uniqueness

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open Filter Topology MeasureTheory BorelCalc ClosedSubmodule

set_option linter.unusedSectionVars false

/-! ## The scalar functions -/

/-- Clamp to `[0,2]`. -/
noncomputable def clR (l : ℝ) : ℝ := max 0 (min l 2)

theorem continuous_clR : Continuous clR := by unfold clR; fun_prop

theorem clR_nonneg (l : ℝ) : 0 ≤ clR l := le_max_left _ _

theorem clR_le_two (l : ℝ) : clR l ≤ 2 := max_le (by norm_num) (min_le_right _ _)

theorem bdd_clR : Bdd clR :=
  Bdd.of_continuous continuous_clR (C := 2) fun l => by
    rw [abs_le]
    exact ⟨by linarith [clR_nonneg l], clR_le_two l⟩

theorem clR_eq_self {l : ℝ} (h : l ∈ Set.Icc (0 : ℝ) 2) : clR l = l := by
  unfold clR
  rw [min_eq_left h.2, max_eq_right h.1]

/-- `e^{clamp C m}`. -/
noncomputable def dfn (C m : ℝ) : ℝ := Real.exp (clamp C m)

theorem continuous_dfn (C : ℝ) : Continuous (dfn C) :=
  Real.continuous_exp.comp (continuous_clamp C)

theorem dfn_pos (C m : ℝ) : 0 < dfn C m := Real.exp_pos _

theorem dfn_ge {C : ℝ} (hC : 0 ≤ C) (m : ℝ) : Real.exp (-C) ≤ dfn C m := by
  rw [dfn]
  exact Real.exp_le_exp.mpr (abs_le.mp (abs_clamp_le hC m)).1

theorem bdd_dfn {C : ℝ} (hC : 0 ≤ C) : Bdd (dfn C) :=
  Bdd.of_continuous (continuous_dfn C) (C := Real.exp C) fun m => by
    rw [abs_of_pos (dfn_pos C m)]
    exact Real.exp_le_exp.mpr ((abs_le.mp (abs_clamp_le hC m)).2)

/-- The denominator `l + e^m(2 − l)` (with the clamps). -/
noncomputable def den (C : ℝ) (p : ℝ × ℝ) : ℝ := clR p.1 + dfn C p.2 * (2 - clR p.1)

/-- The lower bound for the denominator. -/
noncomputable def denLB (C : ℝ) : ℝ := 2 * min 1 (Real.exp (-C))

theorem denLB_pos (C : ℝ) : 0 < denLB C := by
  unfold denLB
  have : (0:ℝ) < min 1 (Real.exp (-C)) := lt_min one_pos (Real.exp_pos _)
  linarith

theorem den_ge {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : denLB C ≤ den C p := by
  set m := min 1 (Real.exp (-C)) with hm
  have h1 : m ≤ 1 := min_le_left _ _
  have h2 : m ≤ dfn C p.2 := (min_le_right _ _).trans (dfn_ge hC p.2)
  have h3 : 0 ≤ clR p.1 := clR_nonneg _
  have h4 : clR p.1 ≤ 2 := clR_le_two _
  have h5 : m * (2 - clR p.1) ≤ dfn C p.2 * (2 - clR p.1) :=
    mul_le_mul_of_nonneg_right h2 (by linarith)
  unfold denLB den
  nlinarith

theorem den_pos {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : 0 < den C p :=
  lt_of_lt_of_le (denLB_pos C) (den_ge hC p)

theorem den_ne_zero {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : den C p ≠ 0 := (den_pos hC p).ne'

theorem continuous_den (C : ℝ) : Continuous (den C) := by
  unfold den
  exact ((continuous_clR.comp continuous_fst)).add
    (((continuous_dfn C).comp continuous_snd).mul
      (continuous_const.sub (continuous_clR.comp continuous_fst)))

theorem den_le {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : den C p ≤ 2 + 2 * Real.exp C := by
  have h3 : 0 ≤ clR p.1 := clR_nonneg _
  have h4 : clR p.1 ≤ 2 := clR_le_two _
  have h5 : dfn C p.2 ≤ Real.exp C := by
    rw [dfn]
    exact Real.exp_le_exp.mpr ((abs_le.mp (abs_clamp_le hC p.2)).2)
  have h6 : dfn C p.2 * (2 - clR p.1) ≤ Real.exp C * 2 :=
    mul_le_mul h5 (by linarith) (by linarith) (Real.exp_pos C).le
  unfold den
  linarith

theorem bdd2_den {C : ℝ} (hC : 0 ≤ C) : Bdd2 (den C) :=
  Bdd2.of_continuous (continuous_den C) (C := 2 + 2 * Real.exp C) fun p => by
    rw [abs_of_pos (den_pos hC p)]
    exact den_le hC p

/-- `1/den`: the symbol of the inverse `(R + e^B(2−R))⁻¹`. -/
noncomputable def fN (C : ℝ) (p : ℝ × ℝ) : ℝ := 1 / den C p

/-- `2l/den`: the symbol of the perturbed modular operator. -/
noncomputable def fR (C : ℝ) (p : ℝ × ℝ) : ℝ := 2 * clR p.1 / den C p

theorem continuous_fN {C : ℝ} (hC : 0 ≤ C) : Continuous (fN C) :=
  continuous_const.div (continuous_den C) (den_ne_zero hC)

theorem continuous_fR {C : ℝ} (hC : 0 ≤ C) : Continuous (fR C) :=
  (continuous_const.mul (continuous_clR.comp continuous_fst)).div (continuous_den C)
    (den_ne_zero hC)

theorem fN_nonneg {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : 0 ≤ fN C p :=
  div_nonneg zero_le_one (den_pos hC p).le

theorem fN_le {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : fN C p ≤ 1 / denLB C :=
  one_div_le_one_div_of_le (denLB_pos C) (den_ge hC p)

theorem bdd2_fN {C : ℝ} (hC : 0 ≤ C) : Bdd2 (fN C) :=
  Bdd2.of_continuous (continuous_fN hC) (C := 1 / denLB C) fun p => by
    rw [abs_of_nonneg (fN_nonneg hC p)]
    exact fN_le hC p

theorem fR_nonneg {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : 0 ≤ fR C p :=
  div_nonneg (by linarith [clR_nonneg p.1]) (den_pos hC p).le

theorem fR_le_two {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : fR C p ≤ 2 := by
  rw [fR, div_le_iff₀ (den_pos hC p)]
  have h1 : 0 ≤ dfn C p.2 * (2 - clR p.1) :=
    mul_nonneg (dfn_pos C p.2).le (by linarith [clR_le_two p.1])
  unfold den
  linarith

theorem bdd2_fR {C : ℝ} (hC : 0 ≤ C) : Bdd2 (fR C) :=
  Bdd2.of_continuous (continuous_fR hC) (C := 2) fun p => by
    rw [abs_of_nonneg (fR_nonneg hC p)]
    exact fR_le_two hC p

theorem fN_mul_den {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : fN C p * den C p = 1 := by
  rw [fN, one_div, inv_mul_cancel₀ (den_ne_zero hC p)]

theorem fR_eq (C : ℝ) (p : ℝ × ℝ) : fR C p = 2 * (clR p.1 * fN C p) := by
  rw [fR, fN, mul_one_div, mul_div_assoc]

/-! ### The Fourier symbol: `θ(fR) = clamp C m + θ(l)` on `(0,2)` -/

theorem fR_mem_Ioo {C : ℝ} (hC : 0 ≤ C) {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo (0 : ℝ) 2) :
    fR C p ∈ Set.Ioo (0 : ℝ) 2 := by
  have hcl : clR p.1 = p.1 := clR_eq_self ⟨hp.1.le, hp.2.le⟩
  have hd := den_pos hC p
  constructor
  · rw [fR, hcl]
    exact div_pos (by linarith [hp.1]) hd
  · rw [fR, div_lt_iff₀ hd, den, hcl]
    have : 0 < dfn C p.2 * (2 - p.1) := mul_pos (dfn_pos C p.2) (by linarith [hp.2])
    linarith

theorem θ_fR {C : ℝ} (hC : 0 ≤ C) {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo (0 : ℝ) 2) :
    θ (fR C p) = clamp C p.2 + θ p.1 := by
  have hcl : clR p.1 = p.1 := clR_eq_self ⟨hp.1.le, hp.2.le⟩
  have hd := den_pos hC p
  have hp1 : (0 : ℝ) < p.1 := hp.1
  have hp2 : p.1 < 2 := hp.2
  have hdf : 0 < dfn C p.2 := dfn_pos C p.2
  have hden : den C p = p.1 + dfn C p.2 * (2 - p.1) := by rw [den, hcl]
  have hne1 : p.1 ≠ 0 := hp1.ne'
  have hne2 : p.1 + dfn C p.2 * (2 - p.1) ≠ 0 := by rw [← hden]; exact hd.ne'
  have h1 : (2 - fR C p) / fR C p = dfn C p.2 * ((2 - p.1) / p.1) := by
    have hfr : fR C p = 2 * p.1 / den C p := by rw [fR, hcl]
    rw [hfr, hden]
    field_simp
    ring
  unfold θ
  rw [if_pos (fR_mem_Ioo hC hp), if_pos hp, h1,
    Real.log_mul hdf.ne' (div_pos (by linarith) hp1).ne', dfn, Real.log_exp]

/-- The Fourier symbol of the perturbed modular operator on `(0,2)`. -/
theorem gDel_fR {C : ℝ} (hC : 0 ≤ C) (t : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo (0 : ℝ) 2) :
    gDel t (fR C p) = eitf t (clamp C p.2) * gDel t p.1 := by
  unfold gDel eitf
  rw [← Complex.exp_add, θ_fR hC hp]
  congr 1
  push_cast
  ring

/-! ## The operators for a commuting pair `(E, B)` -/

section Pair

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {E B : K →L[ℂ] K} (hE : IsSelfAdjoint E) (hB : IsSelfAdjoint B) (hcm : Commute E B)

theorem bdd2_clR_fst : Bdd2 fun p : ℝ × ℝ => clR p.1 := Bdd2.comp_fst bdd_clR

theorem bdd2_two_sub_clR : Bdd2 fun p : ℝ × ℝ => 2 - clR p.1 :=
  (Bdd2.const 2).sub bdd2_clR_fst

theorem bdd2_dfn_snd {C : ℝ} (hC : 0 ≤ C) : Bdd2 fun p : ℝ × ℝ => dfn C p.2 :=
  Bdd2.comp_snd (bdd_dfn hC)

include hE in
/-- `clR` is the identity on the spectrum of `E` when `spectrum E ⊆ [0,2]`. -/
theorem bfc_clR (hsp : spectrum ℝ E ⊆ Set.Icc 0 2) : bfc E hE clR = E := by
  rw [bfc_cfc E hE bdd_clR continuous_clR]
  rw [cfc_congr (f := clR) (g := id) fun l hl => clR_eq_self (hsp hl), cfc_id ℝ E]

include hB in
theorem bfc_dfn : bfc B hB (dfn ‖B‖) = expA B 1 := by
  rw [expA_eq_bfc hB (le_refl ‖B‖) 1]
  congr 1
  funext l
  rw [dfn, one_mul]

include hE hB hcm in
theorem jbfc_clR_fst (hsp : spectrum ℝ E ⊆ Set.Icc 0 2) :
    jbfc E B hE hB hcm (fun p => clR p.1) = E := by
  rw [jbfc_fst E B hE hB hcm bdd_clR, bfc_clR hE hsp]

include hE hB hcm in
theorem jbfc_dfn_snd : jbfc E B hE hB hcm (fun p => dfn ‖B‖ p.2) = expA B 1 := by
  rw [jbfc_snd E B hE hB hcm (bdd_dfn (norm_nonneg B)), bfc_dfn hB]

include hE hB hcm in
theorem jbfc_two_sub_clR (hsp : spectrum ℝ E ⊆ Set.Icc 0 2) :
    jbfc E B hE hB hcm (fun p => 2 - clR p.1) = 2 - E := by
  have h1 : (fun p : ℝ × ℝ => 2 - clR p.1) =
      (fun _ : ℝ × ℝ => (2 : ℝ)) - fun p : ℝ × ℝ => clR p.1 := rfl
  rw [h1, jbfc_sub E B hE hB hcm (Bdd2.const 2) bdd2_clR_fst, jbfc_const,
    jbfc_clR_fst hE hB hcm hsp, Complex.ofReal_ofNat]
  congr 1
  rw [two_smul, one_add_one_eq_two]

include hE hB hcm in
/-- `E + e^B(2 − E)` is the `jbfc` of the denominator. -/
theorem jbfc_den (hsp : spectrum ℝ E ⊆ Set.Icc 0 2) :
    jbfc E B hE hB hcm (den ‖B‖) = E + expA B 1 * (2 - E) := by
  have hnb : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have hsum : den ‖B‖ = (fun p : ℝ × ℝ => clR p.1) +
      ((fun p : ℝ × ℝ => dfn ‖B‖ p.2) * fun p : ℝ × ℝ => 2 - clR p.1) := by
    funext p; rfl
  rw [hsum, jbfc_add E B hE hB hcm bdd2_clR_fst ((bdd2_dfn_snd hnb).mul bdd2_two_sub_clR),
    jbfc_clR_fst hE hB hcm hsp, jbfc_mul E B hE hB hcm (bdd2_dfn_snd hnb) bdd2_two_sub_clR,
    jbfc_dfn_snd hE hB hcm, jbfc_two_sub_clR hE hB hcm hsp]

include hE hB hcm in
/-- The inverse relation: `(E + e^B(2−E))⁻¹ (E + e^B(2−E)) = 1`. -/
theorem jbfc_fN_mul (hsp : spectrum ℝ E ⊆ Set.Icc 0 2) :
    jbfc E B hE hB hcm (fN ‖B‖) * (E + expA B 1 * (2 - E)) = 1 := by
  have hnb : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  rw [← jbfc_den hE hB hcm hsp,
    ← jbfc_mul E B hE hB hcm (bdd2_fN hnb) (bdd2_den hnb)]
  have h1 : fN ‖B‖ * den ‖B‖ = 1 := by
    funext p; exact fN_mul_den hnb p
  rw [h1, jbfc_one]

include hE hB hcm in
/-- `2E(E + e^B(2−E))⁻¹` is the `jbfc` of `fR`. -/
theorem jbfc_fR_eq (hsp : spectrum ℝ E ⊆ Set.Icc 0 2) :
    jbfc E B hE hB hcm (fR ‖B‖) =
      ((2 : ℝ) : ℂ) • (E * jbfc E B hE hB hcm (fN ‖B‖)) := by
  have hnb : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have h1 : fR ‖B‖ = fun p => 2 * ((fun p : ℝ × ℝ => clR p.1) * fN ‖B‖) p := by
    funext p; exact fR_eq ‖B‖ p
  rw [h1, jbfc_const_mul E B hE hB hcm 2 (bdd2_clR_fst.mul (bdd2_fN hnb)),
    jbfc_mul E B hE hB hcm bdd2_clR_fst (bdd2_fN hnb), jbfc_clR_fst hE hB hcm hsp]

include hE hB hcm in
theorem commute_jbfc_fN {T : K →L[ℂ] K} (h1 : Commute E T) (h2 : Commute B T) :
    Commute (jbfc E B hE hB hcm (fN ‖B‖)) T :=
  commute_jbfc E B hE hB hcm h1 h2 (bdd2_fN (norm_nonneg B))

/-! ### The modular group of the perturbed operator -/

include hE hB hcm in
theorem ae_fst_mem_Ioo (hν : ∀ ζ : K, ν E hE ζ (Set.Ioo (0 : ℝ) 2)ᶜ = 0) (ζ : K) :
    ∀ᵐ p ∂(νP E B hE hB hcm ζ), p.1 ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [ae_iff]
  have h1 : {p : ℝ × ℝ | ¬ p.1 ∈ Set.Ioo (0 : ℝ) 2} = Prod.fst ⁻¹' (Set.Ioo (0 : ℝ) 2)ᶜ := rfl
  rw [h1, ← Measure.map_apply measurable_fst measurableSet_Ioo.compl,
    νP_map_fst E B hE hB hcm ζ, hν ζ]

include hE hB hcm in
/-- **The modular group of the perturbed operator**: `(fR)(E,B)^{it} = e^{itB} E^{it}`
in the sense of the Fourier symbols `gDel`. -/
theorem cbfc_jbfc_fR_gDel (hν : ∀ ζ : K, ν E hE ζ (Set.Ioo (0 : ℝ) 2)ᶜ = 0) (t : ℝ) :
    cbfc (jbfc E B hE hB hcm (fR ‖B‖))
        (jbfc_isSelfAdjoint E B hE hB hcm (bdd2_fR (norm_nonneg B))) (gDel t) =
      eit B hB t * cbfc E hE (gDel t) := by
  have hnb : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  rw [cbfc_jbfc E B hE hB hcm (bdd2_fR hnb) (continuous_fR hnb) (cbdd_gDel t)]
  have hF1 : CBdd2 fun p : ℝ × ℝ => gDel t (fR ‖B‖ p) :=
    CBdd2.comp (cbdd_gDel t) (bdd2_fR hnb).1
  have hF2 : CBdd2 ((fun p : ℝ × ℝ => eitf t (trunc B p.2)) * fun p : ℝ × ℝ => gDel t p.1) :=
    (CBdd2.comp_snd (cbdd_eitf_trunc B t)).mul (CBdd2.comp_fst (cbdd_gDel t))
  rw [cjbfc_congr_ae E B hE hB hcm hF1 hF2 fun ζ => ?_]
  · rw [cjbfc_mul E B hE hB hcm (CBdd2.comp_snd (cbdd_eitf_trunc B t))
      (CBdd2.comp_fst (cbdd_gDel t)),
      cjbfc_snd E B hE hB hcm (cbdd_eitf_trunc B t), cjbfc_fst E B hE hB hcm (cbdd_gDel t),
      eit, cbfc_comp_trunc hB (cbdd_eitf t) (continuous_eitf t)]
  · filter_upwards [ae_fst_mem_Ioo hE hB hcm hν ζ] with p hp
    exact gDel_fR hnb t hp

end Pair

/-! ## (M3): the modular data of `ξ = e^{-a/2}Ω` -/

section Perturbed

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)
variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)
variable (a : K →L[ℂ] K) (ha : a ∈ M) (hsa : IsSelfAdjoint a) (haR : Commute a (R M Ω))

theorem commute_apply {x y : K →L[ℂ] K} (h : Commute x y) (ζ : K) : x (y ζ) = y (x ζ) := by
  rw [← mul_apply_eq_comp, h.eq, mul_apply_eq_comp]

/-- `B = a′ − a`, with `a′ = J a J`. -/
noncomputable def Bp : K →L[ℂ] K := conjJm M Ω a - a

include hs hc hsa in
theorem isSelfAdjoint_Bp : IsSelfAdjoint (Bp M Ω a) :=
  (conjJm_isSelfAdjoint M Ω hs hc hsa).sub hsa

include hs hc haR in
theorem commute_R_Bp : Commute (R M Ω) (Bp M Ω a) :=
  (((commute_conjJm_R M Ω hs hc haR).sub_left haR)).symm

include hs hc ha in
theorem commute_a_conjJm : Commute a (conjJm M Ω a) :=
  VonNeumannAlgebra.mem_commutant_iff.mp (conjJm_mem_commutant M Ω hs hc ha) a ha

include hs hc ha in
theorem commute_Bp_expA_a (r : ℝ) : Commute (Bp M Ω a) (expA a r) := by
  rw [Bp]
  exact Commute.sub_left ((commute_expA (commute_a_conjJm M Ω hs hc a ha) r).symm)
    ((commute_expA (Commute.refl a) r).symm)

include hs hc ha in
theorem commute_Bp_expA_conjJm (r : ℝ) : Commute (Bp M Ω a) (expA (conjJm M Ω a) r) := by
  rw [Bp]
  exact Commute.sub_left ((commute_expA (Commute.refl (conjJm M Ω a)) r).symm)
    ((commute_expA (commute_a_conjJm M Ω hs hc a ha).symm r).symm)

/-- The inverse `(R + e^B(2−R))⁻¹`. -/
noncomputable def Nop : K →L[ℂ] K :=
  jbfc (R M Ω) (Bp M Ω a) (R_isSelfAdjoint M Ω) (isSelfAdjoint_Bp M Ω hs hc a hsa)
    (commute_R_Bp M Ω hs hc a haR) (fN ‖Bp M Ω a‖)

/-- The perturbed modular operator `2R(R + e^B(2−R))⁻¹`. -/
noncomputable def Rpert : K →L[ℂ] K :=
  jbfc (R M Ω) (Bp M Ω a) (R_isSelfAdjoint M Ω) (isSelfAdjoint_Bp M Ω hs hc a hsa)
    (commute_R_Bp M Ω hs hc a haR) (fR ‖Bp M Ω a‖)

/-- `e^{-a/2}e^{a′/2}`. -/
noncomputable def Emul : K →L[ℂ] K := expA a (-(1 / 2)) * expA (conjJm M Ω a) (1 / 2)

/-- `e^{a/2}e^{-a′/2}`, the inverse of `Emul`. -/
noncomputable def Einv : K →L[ℂ] K := expA a (1 / 2) * expA (conjJm M Ω a) (-(1 / 2))

include hs hc ha hsa in
theorem Emul_mul_Einv : Emul M Ω a * Einv M Ω a = 1 := by
  have hc1 : Commute (expA (conjJm M Ω a) (1 / 2)) (expA a (1 / 2)) :=
    (commute_expA_expA_conjJm M Ω hs hc ha (1 / 2) (1 / 2)).symm
  rw [Emul, Einv]
  simp only [mul_assoc]
  rw [← mul_assoc (expA (conjJm M Ω a) (1 / 2)), hc1.eq, mul_assoc,
    ← mul_assoc (expA a (-(1 / 2))), expA_neg_mul hsa, one_mul,
    expA_mul_neg (conjJm_isSelfAdjoint M Ω hs hc hsa)]

include hs hc ha hsa in
theorem Emul_mul_Emul : Emul M Ω a * Emul M Ω a = expA (Bp M Ω a) 1 := by
  have hnorm : ‖a‖ ≤ max ‖a‖ ‖conjJm M Ω a‖ := le_max_left _ _
  have hnorm' : ‖conjJm M Ω a‖ ≤ max ‖a‖ ‖conjJm M Ω a‖ := le_max_right _ _
  have hE : Emul M Ω a = expA (Bp M Ω a) (1 / 2) := by
    rw [Bp, expA_sub hsa (conjJm_isSelfAdjoint M Ω hs hc hsa)
      (commute_a_conjJm M Ω hs hc a ha) hnorm hnorm' (1 / 2), Emul,
      (commute_expA_expA_conjJm M Ω hs hc ha (-(1 / 2)) (1 / 2)).eq]
  rw [hE, expA_mul (isSelfAdjoint_Bp M Ω hs hc a hsa)]
  norm_num

theorem commute_Nop {T : K →L[ℂ] K} (h1 : Commute (R M Ω) T) (h2 : Commute (Bp M Ω a) T) :
    Commute (Nop M Ω hs hc a hsa haR) T :=
  commute_jbfc_fN (R_isSelfAdjoint M Ω) (isSelfAdjoint_Bp M Ω hs hc a hsa)
    (commute_R_Bp M Ω hs hc a haR) h1 h2

theorem commute_Nop_R : Commute (Nop M Ω hs hc a hsa haR) (R M Ω) :=
  commute_Nop M Ω hs hc a hsa haR (Commute.refl _) (commute_R_Bp M Ω hs hc a haR).symm

include ha in
theorem commute_Nop_expA_a (r : ℝ) : Commute (Nop M Ω hs hc a hsa haR) (expA a r) :=
  commute_Nop M Ω hs hc a hsa haR (commute_expA haR r).symm (commute_Bp_expA_a M Ω hs hc a ha r)

include ha in
theorem commute_Nop_expA_conjJm (r : ℝ) :
    Commute (Nop M Ω hs hc a hsa haR) (expA (conjJm M Ω a) r) :=
  commute_Nop M Ω hs hc a hsa haR (commute_expA_conjJm_R M Ω hs hc haR r).symm
    (commute_Bp_expA_conjJm M Ω hs hc a ha r)

include ha in
theorem commute_Nop_Emul : Commute (Nop M Ω hs hc a hsa haR) (Emul M Ω a) :=
  (commute_Nop_expA_a M Ω hs hc a ha hsa haR _).mul_right
    (commute_Nop_expA_conjJm M Ω hs hc a ha hsa haR _)

include ha in
theorem commute_Nop_Einv : Commute (Nop M Ω hs hc a hsa haR) (Einv M Ω a) :=
  (commute_Nop_expA_a M Ω hs hc a ha hsa haR _).mul_right
    (commute_Nop_expA_conjJm M Ω hs hc a ha hsa haR _)

theorem Nop_mul_den :
    Nop M Ω hs hc a hsa haR * (R M Ω + expA (Bp M Ω a) 1 * (2 - R M Ω)) = 1 :=
  jbfc_fN_mul (R_isSelfAdjoint M Ω) (isSelfAdjoint_Bp M Ω hs hc a hsa)
    (commute_R_Bp M Ω hs hc a haR) (spectrum_R_subset M Ω)

theorem Rpert_eq : Rpert M Ω hs hc a hsa haR =
    ((2 : ℝ) : ℂ) • (R M Ω * Nop M Ω hs hc a hsa haR) :=
  jbfc_fR_eq (R_isSelfAdjoint M Ω) (isSelfAdjoint_Bp M Ω hs hc a hsa)
    (commute_R_Bp M Ω hs hc a haR) (spectrum_R_subset M Ω)

/-! ### The candidate conjugate-linear part -/

/-- The complex-linear factor of `A_ξ`. -/
noncomputable def Xpert : K →L[ℂ] K :=
  ((2 : ℝ) : ℂ) • (Emul M Ω a * Nop M Ω hs hc a hsa haR * Tm M Ω)

/-- The candidate for `T_ξ J_ξ`. -/
noncomputable def Apert : K →SL[starRingEnd ℂ] K :=
  (Xpert M Ω hs hc a hsa haR).comp (Jm M Ω)

theorem Apert_apply (ζ : K) :
    Apert M Ω hs hc a hsa haR ζ =
      ((2 : ℝ) : ℂ) • (Emul M Ω a) ((Nop M Ω hs hc a hsa haR) (Tm M Ω (Jm M Ω ζ))) := by
  rw [Apert, ContinuousLinearMap.comp_apply, Xpert, smul_apply, mul_apply_eq_comp,
    mul_apply_eq_comp]

include hs hc hsa haR in
/-- The transport of `T J` past `e^{ra′}`. -/
theorem Tm_Jm_expA_conjJm (r : ℝ) (ζ : K) :
    Tm M Ω (Jm M Ω (expA (conjJm M Ω a) r ζ)) = expA a r (Tm M Ω (Jm M Ω ζ)) := by
  rw [Jm_expA_conjJm M Ω hs hc hsa, commute_apply (commute_expA_Tm M Ω haR r).symm]

/-! ### The projection identities -/

include ha in
theorem hfix_pert {k : K} (hk : k ∈ Kre M (pvec Ω a)) :
    Rpert M Ω hs hc a hsa haR k + Apert M Ω hs hc a hsa haR k = (2 : ℂ) • k := by
  have hnb : (0 : ℝ) ≤ ‖Bp M Ω a‖ := norm_nonneg _
  -- the generator identity on `𝒦(M, ξ)`
  have hk' : expA (conjJm M Ω a) (1 / 2) k ∈ Kre M Ω :=
    expA_conjJm_mem_Kre_of_mem_Kre_pvec M Ω hs hc ha hsa haR hk
  have h2P := two_smul_Pre M Ω (expA (conjJm M Ω a) (1 / 2) k)
  rw [Pre_eq_self M Ω hk', ← Tm_Jm M Ω hs hc, Tm_Jm_expA_conjJm M Ω hs hc a hsa haR,
    ← commute_apply (commute_expA_conjJm_R M Ω hs hc haR (1 / 2))] at h2P
  -- solve for `T J k`
  have hEm : ∀ v : K, (Emul M Ω a) v = expA a (-(1 / 2)) (expA (conjJm M Ω a) (1 / 2) v) :=
    fun v => by rw [Emul, mul_apply_eq_comp]
  have hAk : Tm M Ω (Jm M Ω k) = (Emul M Ω a) ((2 - R M Ω) k) := by
    have h := congrArg (expA a (-(1 / 2))) h2P
    rw [map_smul, map_add, expA_neg_apply_expA hsa (1 / 2), ← hEm, ← hEm, two_smul] at h
    rw [sub_apply, two_apply_eq, map_sub, map_add, h]
    abel
  -- the operator identity
  have hop : ((2 : ℝ) : ℂ) • (R M Ω * Nop M Ω hs hc a hsa haR) +
      ((2 : ℝ) : ℂ) • (Emul M Ω a * Nop M Ω hs hc a hsa haR * Emul M Ω a * (2 - R M Ω)) =
      (2 : K →L[ℂ] K) := by
    have h1 : Emul M Ω a * Nop M Ω hs hc a hsa haR * Emul M Ω a =
        Nop M Ω hs hc a hsa haR * expA (Bp M Ω a) 1 := by
      rw [← (commute_Nop_Emul M Ω hs hc a ha hsa haR).eq, mul_assoc,
        Emul_mul_Emul M Ω hs hc a ha hsa]
    have h2 : R M Ω * Nop M Ω hs hc a hsa haR = Nop M Ω hs hc a hsa haR * R M Ω :=
      (commute_Nop_R M Ω hs hc a hsa haR).eq.symm
    rw [h1, h2, ← smul_add, mul_assoc, ← mul_add, Nop_mul_den M Ω hs hc a hsa haR,
      Complex.ofReal_ofNat, two_smul, one_add_one_eq_two]
  -- conclude
  rw [Rpert_eq M Ω hs hc a hsa haR, Apert_apply, hAk]
  have e1 : ((2 : ℝ) : ℂ) • (Emul M Ω a) ((Nop M Ω hs hc a hsa haR)
      ((Emul M Ω a) ((2 - R M Ω) k))) =
      (((2 : ℝ) : ℂ) • (Emul M Ω a * Nop M Ω hs hc a hsa haR * Emul M Ω a * (2 - R M Ω))) k := by
    rw [smul_apply, mul_apply_eq_comp, mul_apply_eq_comp, mul_apply_eq_comp]
  rw [e1, ← add_apply, hop, two_apply_eq, two_smul]

include ha in
theorem hker_pert {η : K} (hη : η ∈ ((Kre M (pvec Ω a)).toSubmodule)ᗮ) :
    Rpert M Ω hs hc a hsa haR η + Apert M Ω hs hc a hsa haR η = 0 := by
  have hη' : expA (conjJm M Ω a) (-(1 / 2)) η ∈ ((Kre M Ω).toSubmodule)ᗮ :=
    expA_conjJm_mem_orthogonal M Ω hs hc ha hsa haR hη
  have h2P := two_smul_Pre M Ω (expA (conjJm M Ω a) (-(1 / 2)) η)
  rw [(Pre_eq_zero_iff M Ω).mpr hη', smul_zero, ← Tm_Jm M Ω hs hc,
    Tm_Jm_expA_conjJm M Ω hs hc a hsa haR,
    ← commute_apply (commute_expA_conjJm_R M Ω hs hc haR (-(1 / 2)))] at h2P
  -- solve for `T J η`
  have hEi : ∀ v : K, (Einv M Ω a) v = expA a (1 / 2) (expA (conjJm M Ω a) (-(1 / 2)) v) :=
    fun v => by rw [Einv, mul_apply_eq_comp]
  have hAη : Tm M Ω (Jm M Ω η) = -((Einv M Ω a) (R M Ω η)) := by
    have h := congrArg (expA a (1 / 2)) h2P
    rw [map_zero, map_add, expA_apply_expA_neg hsa (1 / 2), ← hEi] at h
    exact (neg_eq_iff_add_eq_zero.mpr h.symm).symm
  rw [Rpert_eq M Ω hs hc a hsa haR, Apert_apply, hAη, map_neg, map_neg, smul_neg]
  have e1 : ((2 : ℝ) : ℂ) • (Emul M Ω a) ((Nop M Ω hs hc a hsa haR) ((Einv M Ω a) (R M Ω η))) =
      (((2 : ℝ) : ℂ) • (R M Ω * Nop M Ω hs hc a hsa haR)) η := by
    rw [smul_apply]
    congr 1
    rw [mul_apply_eq_comp, commute_apply (commute_Nop_Einv M Ω hs hc a ha hsa haR),
      ← mul_apply_eq_comp (Emul M Ω a), Emul_mul_Einv M Ω hs hc a ha hsa, one_apply_eq_self,
      commute_apply (commute_Nop_R M Ω hs hc a hsa haR)]
  rw [e1, add_neg_cancel]

/-! ### (M3) -/

include ha in
/-- **(M3), the modular operator**: `R(M, ξ) = 2R(R + e^{a′−a}(2 − R))⁻¹` for `ξ = e^{-a/2}Ω`. -/
theorem R_pvec : R M (pvec Ω a) = Rpert M Ω hs hc a hsa haR :=
  (R_eq_of_proj M (pvec Ω a) (Rpert M Ω hs hc a hsa haR) (Apert M Ω hs hc a hsa haR)
    (fun _ hk => hfix_pert M Ω hs hc a ha hsa haR hk)
    (fun _ hη => hker_pert M Ω hs hc a ha hsa haR hη)).1.symm

include ha haR in
/-- **(M3), the modular group**: `Δ_ξ^{it} = e^{it(a′−a)}Δ^{it}`. -/
theorem Δit_pvec (t : ℝ) :
    Δit M (pvec Ω a) t =
      eit (Bp M Ω a) (isSelfAdjoint_Bp M Ω hs hc a hsa) t * Δit M Ω t := by
  have hsaj : IsSelfAdjoint (Rpert M Ω hs hc a hsa haR) :=
    jbfc_isSelfAdjoint (R M Ω) (Bp M Ω a) (R_isSelfAdjoint M Ω)
      (isSelfAdjoint_Bp M Ω hs hc a hsa) (commute_R_Bp M Ω hs hc a haR)
      (bdd2_fR (norm_nonneg (Bp M Ω a)))
  unfold Δit
  rw [BorelCalc.cbfc_congr_op (R_pvec M Ω hs hc a ha hsa haR) (R_isSelfAdjoint M (pvec Ω a)) hsaj]
  exact cbfc_jbfc_fR_gDel (R_isSelfAdjoint M Ω) (isSelfAdjoint_Bp M Ω hs hc a hsa)
    (commute_R_Bp M Ω hs hc a haR) (ν_R_compl_Ioo M Ω hs hc) t

include hs ha hsa in
/-- `ξ = e^{-a/2}Ω` is cyclic and separating, so the whole modular package applies to it. -/
theorem isSeparating_pvec' : IsSeparating (M : Set (K →L[ℂ] K)) (pvec Ω a) :=
  isSeparating_pvec M Ω hs ha hsa

include hc ha hsa in
theorem isCyclic_pvec' : IsCyclic (M : Set (K →L[ℂ] K)) (pvec Ω a) :=
  isCyclic_pvec M Ω hc ha hsa

include hs hc ha hsa in
/-- A fixed point of the perturbed modular group is in the perturbed centralizer, hence
`ψ_ξ`-tracial (`IsCentral.tracial`). -/
theorem isCentral_pvec_of_σ_eq_self {x : K →L[ℂ] K} (hx : x ∈ M)
    (h : ∀ t, σ M (pvec Ω a) t x = x) : IsCentral M (pvec Ω a) x :=
  isCentral_of_σ_eq_self M (pvec Ω a) (isSeparating_pvec M Ω hs ha hsa)
    (isCyclic_pvec M Ω hc ha hsa) hx h

end Perturbed

end Modular

end VN

end CommutingRepetition
