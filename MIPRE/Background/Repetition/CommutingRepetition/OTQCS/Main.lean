/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/Main.lean
-/
/-
# Averaged operational tracial correlated sampling (Section 6, root)

Audit node 1.3. Anchors: 06_otqcs.tex, thm otqcs, eq otqcs-main. The
interfaces it is stated over (`tracialPairLaw`, `piAlignment`,
`SamplingResource`) live in `OTQCS/PairLaw.lean`; the §6 construction it is
proved from is `OTQCS/Compile.lean` and the grid slab `OTQCS/GridAverage.lean`;
the proof layer of node 1.3.9 (the grid ↔ band bridge and the assembly lemmas)
is `OTQCS/Bands.lean` + `OTQCS/Assembly.lean`.

The proof follows 06_otqcs.tex §"Parameter choice and output error" (eqs
cutoff-choice, R-choice, vector-to-l1, and the degenerate range with the trivial
resource). One deliberate simplification: the rounding parameter is taken as
`α = Δ^{1/6} + ξ` rather than eq alpha-choice's `α₀ = (√D̄ + ξ³)^{1/3}`; with
`D̄ ≤ 4Δ` (eq Dbar-Delta) this gives `√D̄/α ≤ 2Δ^{1/3}` directly and the same
final shape `C_OT (Δ^{1/6} + ξ)`.

The conclusion is stated in consumed form: the theorem produces SOME
standard-form algebra carrying the resource (the manuscript's finer
description "obtained from N by finitely many normalized matrix
amplifications and tensor powers" is a property of the construction that
nothing downstream consumes; recorded in DIFFERENCES.md).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.PairLaw
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Assembly

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

/-- **Averaged operational tracial correlated sampling** (node 1.3;
06_otqcs.tex, thm otqcs, eq otqcs-main): there is a universal constant
`C_OT ≥ 1` such that for every finite standard-form algebra `N`, finite
label sets, label law `π`, unit vectors `x_s, y_t, u_{st}`, full POVMs
`(A_s^a), (B_t^b)` in `N`, and every `0 < ξ ≤ 1`, some question-independent
sampling resource reproduces the ideal pair law up to unhalved average ℓ¹
error `C_OT (Δ^{1/6} + ξ)`. The constant is quantified before all data:
independent of family sizes, center, supports, and dimensions. -/
theorem otqcs_sampling :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (S T A B : Type) [Fintype S] [Fintype T] [Fintype A] [Fintype B]
        [Nonempty A] [Nonempty B]
        (N : StdTracialAlgebra.{0}) (π : S → T → ℝ)
        (_hπ_nonneg : ∀ s t, 0 ≤ π s t)
        (_hπ_sum : (∑ s : S, ∑ t : T, π s t) = 1)
        (xv : S → N.H) (yv : T → N.H) (u : S → T → N.H)
        (_hx : ∀ s, ‖xv s‖ = 1) (_hy : ∀ t, ‖yv t‖ = 1)
        (_hu : ∀ s t, ‖u s t‖ = 1)
        (E : S → A → N.A) (F : T → B → N.A)
        (_hE_pos : ∀ s a, IsPosElem (E s a))
        (_hF_pos : ∀ t b, IsPosElem (F t b))
        (_hE_sum : ∀ s, (∑ a : A, E s a) = 1)
        (_hF_sum : ∀ t, (∑ b : B, F t b) = 1)
        (ξ : ℝ), 0 < ξ → ξ ≤ 1 →
        ∃ R : SamplingResource S T A B,
          (∑ s : S, ∑ t : T, π s t * ∑ a : A, ∑ b : B,
              |R.answerLaw s t a b - tracialPairLaw N u E F s t a b|)
            ≤ C * ((piAlignment π u xv yv) ^ ((1 : ℝ) / 6) + ξ) := by
  classical
  -- the two universal constants of the grid slab (nodes 1.3.3, 1.3.4)
  obtain ⟨C₀, hC₀, hshift⟩ := exists_common_shift
  obtain ⟨C₁, -, hgrid⟩ := grid_disagreement
  refine ⟨4 * Real.sqrt (6 * C₀) + 24 * C₀ + 12, ?_, ?_⟩
  · have := Real.sqrt_nonneg (6 * C₀); linarith
  intro S T A B _ _ _ _ _ _ N π hπ hπ1 xv yv u hx hy hu E F hE hF hEs hFs ξ hξ hξ1
  -- the alignment defect `Δ` and its sixth root `δ`
  set Δ := piAlignment π u xv yv with hΔdef
  have hΔ0 : 0 ≤ Δ :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ =>
      mul_nonneg (hπ s t) (by positivity)
  set δ := Δ ^ ((1 : ℝ) / 6) with hδdef
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hΔ0 _
  have hδ6 : δ ^ 6 = Δ := rpow_sixth_pow Δ hΔ0
  set C := 4 * Real.sqrt (6 * C₀) + 24 * C₀ + 12 with hCdef
  have hC4 : 4 ≤ C := by have := Real.sqrt_nonneg (6 * C₀); linarith
  by_cases hcase : δ + ξ ≤ 1 / 2
  swap
  · -- Degenerate range (06_otqcs.tex, "If α₀ > 1/2"): the trivial resource; an
    -- unhalved ℓ¹ distance between two laws is at most 2 ≤ 4(δ + ξ).
    replace hcase := not_le.mp hcase
    refine ⟨trivialResource S T A B N, ?_⟩
    set Rt := trivialResource S T A B N with hRt
    have hlaw : ∀ s t,
        (∑ a, ∑ b, |Rt.answerLaw s t a b - tracialPairLaw N u E F s t a b|) ≤ 2 := by
      intro s t
      exact l1_le_two (fun a b => Rt.answerLaw s t a b) (fun a b => tracialPairLaw N u E F s t a b)
        (fun a b => tracialPairLaw_nonneg Rt.N (fun _ _ => Rt.Ω) Rt.E Rt.F Rt.E_pos Rt.F_pos s t a b)
        (fun a b => tracialPairLaw_nonneg N u E F hE hF s t a b)
        (tracialPairLaw_sum Rt.N (fun _ _ => Rt.Ω) Rt.E Rt.F (fun _ _ => Rt.Ω_norm) Rt.E_sum
          Rt.F_sum s t)
        (tracialPairLaw_sum N u E F hu hEs hFs s t)
    calc (∑ s, ∑ t, π s t * ∑ a, ∑ b, |Rt.answerLaw s t a b - tracialPairLaw N u E F s t a b|)
        ≤ ∑ s, ∑ t, π s t * 2 :=
          Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left (hlaw s t) (hπ s t)
      _ = 2 := by simp only [← Finset.sum_mul, hπ1, one_mul]
      _ ≤ C * (δ + ξ) := by nlinarith
  -- Nontrivial range: the construction of §6 with the parameter choice of
  -- 06_otqcs.tex, eqs cutoff-choice / alpha-choice / R-choice
  -- (`ρ = ξ²/32`, `L = ξ/8`, `α = δ + ξ` with `δ = Δ^{1/6}`, `R = ⌈2Z log(2/ξ²)⌉`).
  have hξ2 : ξ ≤ 1 / 2 := by linarith
  set α := δ + ξ with hαdef
  have hα0 : 0 < α := by linarith
  have hr : 1 < 1 + α := by linarith
  set ρ := ξ ^ 2 / 32 with hρdef
  set L := ξ / 8 with hLdef
  have hρ : 0 < ρ := by positivity
  have hL : 0 < L := by positivity
  have hρL : ρ + L ^ 2 ≤ 1 / 2 := by rw [hρdef, hLdef]; nlinarith
  -- Step 0 (nodes 1.3.1 + 1.3.2): the modulus family over a tracial extension,
  -- and the transport of all data along the spatial isometry `U`.
  obtain ⟨ext, ⟨Fm⟩⟩ := exists_modulusFamily N xv yv
  have hx' : ∀ s, ‖ext.U (xv s)‖ = 1 := fun s => by rw [LinearIsometryEquiv.norm_map, hx s]
  have hy' : ∀ t, ‖ext.U (yv t)‖ = 1 := fun t => by rw [LinearIsometryEquiv.norm_map, hy t]
  have hu' : ∀ s t, ‖ext.U (u s t)‖ = 1 := fun s t => by
    rw [LinearIsometryEquiv.norm_map, hu s t]
  set E' : S → A → ext.N'.A := fun s a => ext.emb (E s a) with hE'def
  set F' : T → B → ext.N'.A := fun t b => ext.emb (F t b) with hF'def
  have hE' : ∀ s a, IsPosElem (E' s a) := fun s a => ext.emb_isPosElem (hE s a)
  have hF' : ∀ t b, IsPosElem (F' t b) := fun t b => ext.emb_isPosElem (hF t b)
  have hEs' : ∀ s, (∑ a, E' s a) = 1 := fun s => ext.emb_sum_eq_one (E s) (hEs s)
  have hFs' : ∀ t, (∑ b, F' t b) = 1 := fun t => ext.emb_sum_eq_one (F t) (hFs t)
  have hq : ∀ s t a b,
      tracialPairLaw ext.N' (fun s t => ext.U (u s t)) E' F' s t a b
        = tracialPairLaw N u E F s t a b :=
    fun s t a b => ext.tracialPairLaw_map u E F s t a b
  have hΔ' : piAlignment π (fun s t => ext.U (u s t)) (fun s => ext.U (xv s))
      (fun t => ext.U (yv t)) = Δ := ext.piAlignment_map π u xv yv
  -- Step 1: one finite cutoff `H > L` for all spectral distributions.
  let μfam : S ⊕ T → MeasureTheory.Measure ℝ :=
    Sum.elim (fun s => (Fm.dataA s).μ) (fun t => (Fm.dataB t).μ)
  have : ∀ i, MeasureTheory.IsProbabilityMeasure (μfam i) := fun i => by
    cases i with
    | inl s => exact (Fm.dataA s).μ_prob
    | inr t => exact (Fm.dataB t).μ_prob
  have hint : ∀ i, MeasureTheory.Integrable (fun b : ℝ => b ^ 2) (μfam i) := by
    intro i
    cases i with
    | inl s =>
      exact integrable_sq_of_integral_eq_one (μ := (Fm.dataA s).μ)
        (by rw [(Fm.dataA s).moment2, hx' s, one_pow])
    | inr t =>
      exact integrable_sq_of_integral_eq_one (μ := (Fm.dataB t).μ)
        (by rw [(Fm.dataB t).moment2, hy' t, one_pow])
  obtain ⟨H, hLH, htails⟩ := exists_tail_cutoff μfam hint hρ L
  have htailA : ∀ s, (∫ b in Set.Ioi H, b ^ 2 ∂(Fm.dataA s).μ) ≤ ρ := fun s => htails (Sum.inl s)
  have htailB : ∀ t, (∫ b in Set.Ioi H, b ^ 2 ∂(Fm.dataB t).μ) ≤ ρ := fun t => htails (Sum.inr t)
  -- Step 2 (nodes 1.3.3 + 1.3.4): the couplings and the common shift `θ₀`.
  let ν : S × T → MeasureTheory.Measure (ℝ × ℝ) := fun p => (Fm.joint p.1 p.2).ν
  have hνprob : ∀ p, MeasureTheory.IsProbabilityMeasure (ν p) := fun p => (Fm.joint p.1 p.2).ν_prob
  have hnn : ∀ p, ∀ᵐ q ∂(ν p), 0 ≤ q.1 ∧ 0 ≤ q.2 := fun p => (Fm.joint p.1 p.2).ae_nonneg
  have h1 : ∀ p, (∫ q : ℝ × ℝ, q.1 ^ 2 ∂(ν p)) = 1 := fun p => by
    rw [(Fm.joint p.1 p.2).integral_fst_sq, hx' p.1, one_pow]
  have h2 : ∀ p, (∫ q : ℝ × ℝ, q.2 ^ 2 ∂(ν p)) = 1 := fun p => by
    rw [(Fm.joint p.1 p.2).integral_snd_sq, hy' p.2, one_pow]
  have ht1 : ∀ p, (∫ q in {q : ℝ × ℝ | H < q.1}, q.1 ^ 2 ∂(ν p)) ≤ ρ := fun p => by
    rw [(Fm.joint p.1 p.2).setIntegral_fst_sq_tail]; exact htailA p.1
  have ht2 : ∀ p, (∫ q in {q : ℝ × ℝ | H < q.2}, q.2 ^ 2 ∂(ν p)) ≤ ρ := fun p => by
    rw [(Fm.joint p.1 p.2).setIntegral_snd_sq_tail]; exact htailB p.2
  have hπ' : ∀ p : S × T, 0 ≤ π p.1 p.2 := fun p => hπ p.1 p.2
  have hπ1' : (∑ p : S × T, π p.1 p.2) = 1 := by rw [Fintype.sum_prod_type]; exact hπ1
  obtain ⟨θ₀, hθ₀, hΓavg⟩ := hshift (S × T) (fun p => π p.1 p.2) ν α L H ρ hα0 hcase hL hLH
    hρ.le hπ' hπ1' hnn h1 h2 ht1 ht2
  -- Step 3 (node 1.3.5 input): the retained bins at the common shift.
  set r := 1 + α with hrdef
  set m := binCount r θ₀ L H with hmdef
  set Bf := retainedBin r θ₀ L H with hBfdef
  set tv := retainedVal r θ₀ L H with htvdef
  have hB : IsBandFamily Bf tv := isBandFamily_retained hr hL
  have hm : 0 < m := binCount_pos hr hL hLH.le
  have hZ : 0 < bandZ tv := bandZ_pos_of_pos hm hB.tpos
  set Z := bandZ tv with hZdef
  have hU : (⋃ k, Bf k) = Set.Icc L H := iUnion_retainedBin hr hL
  have hband : ∀ k, Bf k ⊆ Set.Icc (tv k / r) (tv k) := retainedBin_subset hr hL
  -- Step 4 (node 1.3.8): the trial count, the tensor power, the resource.
  set Rn : ℕ := ⌈2 * Z * Real.log (2 / ξ ^ 2)⌉₊ with hRndef
  obtain ⟨D⟩ := exists_tensorPowerData (StdTracialAlgebra.amplify ext.N' (m + 1)) Rn
  let a₀ : A := Classical.arbitrary A
  let b₀ : B := Classical.arbitrary B
  let Rres : SamplingResource S T A B :=
    { N := D.Nhat
      Ω := tensorState D (trialUnitMat ext.N' m tv)
      Ω_norm := tensorState_norm D _ (trialState_norm ext.N' m tv hZ)
      E := fun s a => hatA Fm Bf D E' a₀ s a
      F := fun t b => hatB Fm Bf D F' b₀ t b
      E_pos := fun s a => hatA_isPosElem Fm Bf tv D E' a₀ s hB hE' a
      F_pos := fun t b => hatB_isPosElem Fm Bf tv D F' b₀ t hB hF' b
      E_sum := fun s => hatA_sum Fm Bf tv D E' a₀ s hB (hEs' s)
      F_sum := fun t => hatB_sum Fm Bf tv D F' b₀ t hB (hFs' t) }
  refine ⟨Rres, ?_⟩
  -- Step 5: the per-pair estimate (eqs finite-bad, selected-state-preopt,
  -- vector-to-l1 and the branch decomposition of node 1.3.8).
  set κ := Real.sqrt (ρ + L ^ 2) with hκdef
  have hpair : ∀ p : S × T,
      (∑ a, ∑ b, |Rres.answerLaw p.1 p.2 a b - tracialPairLaw N u E F p.1 p.2 a b|) ≤
        4 * Real.sqrt (gridGamma (Fm.joint p.1 p.2).ν r θ₀ L H) + 4 * α + 4 * κ
          + 2 * ‖ext.U (yv p.2) - ext.U (u p.1 p.2)‖
          + 4 * gridGamma (Fm.joint p.1 p.2).ν r θ₀ L H + 2 * ξ ^ 2 := by
    rintro ⟨s, t⟩
    dsimp only
    have : MeasureTheory.IsProbabilityMeasure (Fm.joint s t).ν := (Fm.joint s t).ν_prob
    -- the grid masses at the common shift (node 1.3.3 (i))
    obtain ⟨hab, -⟩ := hgrid (Fm.joint s t).ν α L H ρ hα0 hcase hL hLH hρ.le (hnn (s, t))
      (h1 (s, t)) (h2 (s, t)) (ht1 (s, t)) (ht2 (s, t))
    obtain ⟨haL, -, hbL, -⟩ := hab θ₀ hθ₀
    -- the bridge: the grid masses are the band masses
    have ha_eq : gridA (Fm.joint s t).ν r θ₀ L H = bandMassA Fm Bf tv s := by
      rw [gridA_eq_sum_retained hr hL, (Fm.joint s t).margA]; rfl
    have hb_eq : gridB (Fm.joint s t).ν r θ₀ L H = bandMassB Fm Bf tv t := by
      rw [gridB_eq_sum_retained hr hL, (Fm.joint s t).margB]; rfl
    have hc_eq : gridC (Fm.joint s t).ν r θ₀ L H = bandCross Fm Bf tv s t := by
      rw [gridC_eq_sum_retained hr hL]; rfl
    have hΓ_eq : gridGamma (Fm.joint s t).ν r θ₀ L H
        = bandMassA Fm Bf tv s + bandMassB Fm Bf tv t - 2 * bandCross Fm Bf tv s t := by
      rw [gridGamma, ha_eq, hb_eq, hc_eq]
    have ha : 1 / 2 ≤ bandMassA Fm Bf tv s := by rw [← ha_eq]; linarith
    have hb : 1 / 2 ≤ bandMassB Fm Bf tv t := by rw [← hb_eq]; linarith
    have hc0 : 0 ≤ bandCross Fm Bf tv s t := bandCross_nonneg Fm Bf tv s t
    have hca : bandCross Fm Bf tv s t ≤ bandMassA Fm Bf tv s :=
      bandCross_le_bandMassA Fm Bf tv hB s t
    have hcb : bandCross Fm Bf tv s t ≤ bandMassB Fm Bf tv t :=
      bandCross_le_bandMassB Fm Bf tv hB s t
    have hle : bandMassA Fm Bf tv s + bandMassB Fm Bf tv t - bandCross Fm Bf tv s t ≤ Z :=
      bandMass_add_sub_cross_le_bandZ Fm Bf tv hB s t
    -- the branch decomposition (node 1.3.8) and the bad-branch mass (node 1.3.6)
    obtain ⟨rem, hrem0, hremsum, hdec⟩ :=
      compile_decomposition Fm Bf tv D E' F' a₀ b₀ hB hZ hE' hF' hEs' hFs' s t
    have hcm0 : 0 ≤ commonMass (bandMassA Fm Bf tv s) (bandMassB Fm Bf tv t)
        (bandCross Fm Bf tv s t) Z Rn :=
      commonMass_nonneg _ _ _ _ _ hZ hc0 hle
    have hbad : 1 - commonMass (bandMassA Fm Bf tv s) (bandMassB Fm Bf tv t)
        (bandCross Fm Bf tv s t) Z Rn ≤ 2 * gridGamma (Fm.joint s t).ν r θ₀ L H + ξ ^ 2 := by
      rw [hΓ_eq]
      exact one_sub_commonMass_le _ _ _ _ ξ hZ hξ ha hb hc0 hca hcb hle
    -- the selected state and its law
    set z := selState (Fm.dataA s) (Fm.dataB t) (Fm.joint s t) Bf tv with hzdef
    have hz : ‖z‖ = 1 := selState_norm (Fm.dataA s) (Fm.dataB t) (Fm.joint s t) Bf tv hB
    have hl1 : (∑ a, ∑ b, |Rres.answerLaw s t a b - tracialPairLaw N u E F s t a b|) ≤
        (∑ a, ∑ b, |tracialPairLaw ext.N' (fun _ _ => z) E' F' s t a b
          - tracialPairLaw N u E F s t a b|)
        + 2 * (1 - commonMass (bandMassA Fm Bf tv s) (bandMassB Fm Bf tv t)
          (bandCross Fm Bf tv s t) Z Rn) := by
      refine l1_le_of_decomposition (fun a b => Rres.answerLaw s t a b)
        (fun a b => tracialPairLaw ext.N' (fun _ _ => z) E' F' s t a b)
        (fun a b => tracialPairLaw N u E F s t a b) rem _ hcm0 hrem0 hremsum
        (fun a b => tracialPairLaw_nonneg N u E F hE hF s t a b)
        (tracialPairLaw_sum N u E F hu hEs hFs s t) ?_
      intro a b
      exact hdec a b
    -- vector-to-ℓ¹ (eq vector-to-l1)
    have hq' : ∀ a b, tracialPairLaw ext.N' (fun _ _ => ext.U (u s t)) E' F' s t a b
        = tracialPairLaw N u E F s t a b := fun a b => hq s t a b
    have hvec : (∑ a, ∑ b, |tracialPairLaw ext.N' (fun _ _ => z) E' F' s t a b
        - tracialPairLaw N u E F s t a b|) ≤ 2 * ‖z - ext.U (u s t)‖ := by
      have h := sum_abs_tracialPairLaw_sub_le ext.N' E' F' hE' hF' hEs' hFs' s t hz (hu' s t)
      simp only [hq'] at h
      exact h
    -- the selected-state chain (eq selected-state-preopt)
    have hcut : ‖(Fm.dataB t).hvec - selCutVec (Fm.dataB t) Bf‖ ≤ κ :=
      hvec_sub_selCutVec_le (Fm.dataB t) Bf tv hB (hy' t) hL hLH hU (htailB t)
    have hchain : ‖z - ext.U (u s t)‖ ≤
        2 * Real.sqrt (gridGamma (Fm.joint s t).ν r θ₀ L H) + 2 * ((r - 1) + κ)
          + ‖ext.U (yv t) - ext.U (u s t)‖ := by
      have h := selState_sub_le (Fm.dataA s) (Fm.dataB t) (Fm.joint s t) Bf tv hB (hy' t) ha hb
        r hr.le hband κ hcut (ext.U (u s t))
      rw [hΓ_eq]
      exact h
    calc (∑ a, ∑ b, |Rres.answerLaw s t a b - tracialPairLaw N u E F s t a b|)
        ≤ (∑ a, ∑ b, |tracialPairLaw ext.N' (fun _ _ => z) E' F' s t a b
            - tracialPairLaw N u E F s t a b|)
          + 2 * (1 - commonMass (bandMassA Fm Bf tv s) (bandMassB Fm Bf tv t)
            (bandCross Fm Bf tv s t) Z Rn) := hl1
      _ ≤ 2 * ‖z - ext.U (u s t)‖
          + 2 * (2 * gridGamma (Fm.joint s t).ν r θ₀ L H + ξ ^ 2) := by linarith
      _ ≤ 2 * (2 * Real.sqrt (gridGamma (Fm.joint s t).ν r θ₀ L H) + 2 * ((r - 1) + κ)
            + ‖ext.U (yv t) - ext.U (u s t)‖)
          + 2 * (2 * gridGamma (Fm.joint s t).ν r θ₀ L H + ξ ^ 2) := by linarith
      _ = 4 * Real.sqrt (gridGamma (Fm.joint s t).ν r θ₀ L H) + 4 * α + 4 * κ
          + 2 * ‖ext.U (yv t) - ext.U (u s t)‖
          + 4 * gridGamma (Fm.joint s t).ν r θ₀ L H + 2 * ξ ^ 2 := by
          rw [hrdef]; ring
  -- Step 6: average over `π` (eqs Dbar-Delta, common-shift, the final display).
  have hΓnn : ∀ p : S × T, 0 ≤ gridGamma (Fm.joint p.1 p.2).ν r θ₀ L H := by
    intro p
    have : MeasureTheory.IsProbabilityMeasure (Fm.joint p.1 p.2).ν := (Fm.joint p.1 p.2).ν_prob
    exact gridGamma_nonneg hr hL θ₀ (integrable_of_integral_eq_one (h1 p))
      (integrable_of_integral_eq_one (h2 p))
  have hℓ : ∀ p : S × T,
      (∑ a, ∑ b, |Rres.answerLaw p.1 p.2 a b - tracialPairLaw N u E F p.1 p.2 a b|) ≤
        4 * Real.sqrt (gridGamma (Fm.joint p.1 p.2).ν r θ₀ L H) + 4 * (δ + ξ)
          + 4 * Real.sqrt (ξ ^ 2 / 32 + (ξ / 8) ^ 2)
          + 2 * Real.sqrt (‖ext.U (yv p.2) - ext.U (u p.1 p.2)‖ ^ 2)
          + 4 * gridGamma (Fm.joint p.1 p.2).ν r θ₀ L H + 2 * ξ ^ 2 := by
    intro p
    have h := hpair p
    rw [Real.sqrt_sq (norm_nonneg _)]
    exact h
  -- `D̄ ≤ 4Δ` (eq Dbar-Delta via the stability bound of node 1.3.1)
  have hDbar : (∑ p : S × T, π p.1 p.2 * ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂(ν p)) ≤ 4 * δ ^ 6 := by
    have hterm : ∀ p : S × T, π p.1 p.2 * ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂(ν p) ≤
        π p.1 p.2 * (4 * (‖ext.U (u p.1 p.2) - ext.U (xv p.1)‖ ^ 2
          + ‖ext.U (u p.1 p.2) - ext.U (yv p.2)‖ ^ 2)) := by
      intro p
      apply mul_le_mul_of_nonneg_left _ (hπ p.1 p.2)
      have hstab := Fm.stability p.1 p.2
      have hxy := norm_sub_sq_le_two_mul (ext.U (xv p.1)) (ext.U (yv p.2)) (ext.U (u p.1 p.2))
      calc (∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂(ν p))
          = ‖(Fm.dataA p.1).hvec - (Fm.dataB p.2).hvec‖ ^ 2 := (Fm.joint p.1 p.2).crossMoment
        _ ≤ _ := by linarith
    calc (∑ p : S × T, π p.1 p.2 * ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂(ν p))
        ≤ ∑ p : S × T, π p.1 p.2 * (4 * (‖ext.U (u p.1 p.2) - ext.U (xv p.1)‖ ^ 2
            + ‖ext.U (u p.1 p.2) - ext.U (yv p.2)‖ ^ 2)) := Finset.sum_le_sum fun p _ => hterm p
      _ = 4 * piAlignment π (fun s t => ext.U (u s t)) (fun s => ext.U (xv s))
            (fun t => ext.U (yv t)) := by
          simp only [piAlignment]
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ = 4 * δ ^ 6 := by rw [hΔ', hδ6]
  -- `E_π ‖y_t − u_{st}‖² ≤ Δ`
  have hYavg : (∑ p : S × T, π p.1 p.2 * ‖ext.U (yv p.2) - ext.U (u p.1 p.2)‖ ^ 2) ≤ δ ^ 6 := by
    rw [hδ6, ← hΔ']
    simp only [piAlignment]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
    apply mul_le_mul_of_nonneg_left _ (hπ s t)
    rw [norm_sub_rev]
    nlinarith [sq_nonneg ‖ext.U (u s t) - ext.U (xv s)‖]
  have hfinal := average_bound (fun p : S × T => π p.1 p.2)
    (fun p => gridGamma (Fm.joint p.1 p.2).ν r θ₀ L H)
    (fun p => ‖ext.U (yv p.2) - ext.U (u p.1 p.2)‖ ^ 2)
    (fun p => ∑ a, ∑ b, |Rres.answerLaw p.1 p.2 a b - tracialPairLaw N u E F p.1 p.2 a b|)
    C₀ δ ξ (∑ p : S × T, π p.1 p.2 * ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂(ν p))
    hπ' hπ1' hΓnn (fun p => sq_nonneg _) hℓ hC₀ hδ0 hξ hcase hΓavg hDbar hYavg
  calc (∑ s, ∑ t, π s t * ∑ a, ∑ b, |Rres.answerLaw s t a b - tracialPairLaw N u E F s t a b|)
      = ∑ p : S × T, π p.1 p.2 *
          ∑ a, ∑ b, |Rres.answerLaw p.1 p.2 a b - tracialPairLaw N u E F p.1 p.2 a b| :=
        (Fintype.sum_prod_type (fun p : S × T => π p.1 p.2 *
          ∑ a, ∑ b, |Rres.answerLaw p.1 p.2 a b - tracialPairLaw N u E F p.1 p.2 a b|)).symm
    _ ≤ (4 * Real.sqrt (6 * C₀) + 24 * C₀ + 8) * (δ + ξ) := hfinal
    _ ≤ C * (δ + ξ) := by rw [hCdef]; nlinarith

end CommutingRepetition
