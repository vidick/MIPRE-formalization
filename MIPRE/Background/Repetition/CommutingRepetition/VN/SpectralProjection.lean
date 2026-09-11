/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/SpectralProjection.lean
-/
/-
# Spectral projections: monotone limits, membership, the PVM (Stage C3)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

For the Borel functional calculus `bfc E hE` of `VN/BorelCalculus.lean`:

* **monotone convergence**: if `0 ≤ gₙ ↑ G ≤ 1` pointwise then `bfc gₙ → bfc G`
  strongly (Stage B `StrongLimit.monotoneLimit` + monotone convergence of the
  integrals against every spectral measure), and the antitone version;
* **membership**: for a star subalgebra `S ∋ E` closed under strong sequential
  limits, `cfc g E ∈ S` (the elemental C*-algebra of `E` is contained in the
  closed `S`) and `bfc (1_I) ∈ S` for every Borel `I` — by
  `MeasurableSpace.induction_on_inter` on the π-system of rational half-lines
  `Iic a`, whose indicators are antitone limits of continuous functions,
  complements via `1 − P`, disjoint unions via increasing accumulated unions;
* **the projection-valued measure** `P I := bfc (1_I)`: self-adjoint
  idempotents, `P ∅ = 0`, `P univ = 1`, `P (I ∩ J) = P I P J`, additivity on
  disjoint sets, `⟪ξ, P I ξ⟫ = ν_ξ(I)`, `P (spectrum) = 1`, all `P I ∈ S`.
  On non-measurable sets `P I = 0` (junk), so `star (P I) = P I` holds
  unconditionally — the shape of `SpectralData.proj_star`.

Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.BorelCalculus

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace BorelCalc

open scoped InnerProductSpace Topology
open Filter MeasureTheory

set_option linter.unusedSectionVars false

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-! ### Monotone convergence -/

theorem Bdd.of_unit {g : ℝ → ℝ} (hg : Measurable g) (h0 : ∀ t, 0 ≤ g t) (h1 : ∀ t, g t ≤ 1) :
    Bdd g :=
  ⟨hg, 1, fun t => abs_le.mpr ⟨by linarith [h0 t], h1 t⟩⟩

/-- **Monotone convergence** for the Borel calculus: `0 ≤ gₙ ↑ G ≤ 1` pointwise gives
`bfc gₙ → bfc G` strongly. -/
theorem bfc_tendsto_of_monotone {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} (hg : ∀ n, Measurable (g n))
    (hG : Measurable G) (h0 : ∀ n t, 0 ≤ g n t) (h1 : ∀ n t, g n t ≤ 1)
    (hmono : ∀ t, Monotone fun n => g n t)
    (hlim : ∀ t, Tendsto (fun n => g n t) atTop (𝓝 (G t))) (ξ : 𝓗) :
    Tendsto (fun n => bfc E hE (g n) ξ) atTop (𝓝 (bfc E hE G ξ)) := by
  have hgb : ∀ n, Bdd (g n) := fun n => Bdd.of_unit (hg n) (h0 n) (h1 n)
  have hG0 : ∀ t, 0 ≤ G t := fun t => ge_of_tendsto' (hlim t) fun n => h0 n t
  have hG1 : ∀ t, G t ≤ 1 := fun t => le_of_tendsto' (hlim t) fun n => h1 n t
  have hGb : Bdd G := Bdd.of_unit hG hG0 hG1
  set T : ℕ → 𝓗 →L[ℂ] 𝓗 := fun n => bfc E hE (g n) with hT
  have hTmono : Monotone T := monotone_nat_of_le_succ fun n =>
    bfc_mono E hE (hgb n) (hgb (n + 1)) fun t => hmono t (Nat.le_succ n)
  have hT0 : 0 ≤ T 0 := bfc_nonneg E hE (hgb 0) (h0 0)
  have hT1 : ∀ n, T n ≤ 1 := fun n => bfc_le_one E hE (hgb n) (h1 n)
  have hL : ∀ ζ, Tendsto (fun n => T n ζ) atTop
      (𝓝 (StrongLimit.monotoneLimit T hTmono hT0 hT1 ζ)) :=
    StrongLimit.monotoneLimit_tendsto T hTmono hT0 hT1
  have heq : StrongLimit.monotoneLimit T hTmono hT0 hT1 = bfc E hE G := by
    refine ext_of_inner_self fun ζ => ?_
    have h1' := StrongLimit.monotoneLimit_inner T hTmono hT0 hT1 ζ ζ
    have h2' : Tendsto (fun n => ⟪ζ, T n ζ⟫_ℂ) atTop (𝓝 ⟪ζ, bfc E hE G ζ⟫_ℂ) := by
      rw [inner_bfc_self E hE hGb, Q]
      have hint : Tendsto (fun n => ∫ t, g n t ∂(ν E hE ζ)) atTop (𝓝 (∫ t, G t ∂(ν E hE ζ))) :=
        integral_tendsto_of_tendsto_of_monotone (fun n => (hgb n).integrable _)
          (hGb.integrable _) (Eventually.of_forall hmono) (Eventually.of_forall hlim)
      have := (Complex.continuous_ofReal.tendsto _).comp hint
      refine this.congr fun n => ?_
      simp only [Function.comp, hT]
      rw [inner_bfc_self E hE (hgb n), Q]
    exact tendsto_nhds_unique h1' h2'
  rw [← heq]
  exact hL ξ

/-- **Antitone convergence**: `1 ≥ gₙ ↓ G ≥ 0` pointwise gives `bfc gₙ → bfc G` strongly. -/
theorem bfc_tendsto_of_antitone {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} (hg : ∀ n, Measurable (g n))
    (hG : Measurable G) (h0 : ∀ n t, 0 ≤ g n t) (h1 : ∀ n t, g n t ≤ 1)
    (hanti : ∀ t, Antitone fun n => g n t)
    (hlim : ∀ t, Tendsto (fun n => g n t) atTop (𝓝 (G t))) (ξ : 𝓗) :
    Tendsto (fun n => bfc E hE (g n) ξ) atTop (𝓝 (bfc E hE G ξ)) := by
  have hgb : ∀ n, Bdd (g n) := fun n => Bdd.of_unit (hg n) (h0 n) (h1 n)
  have hG0 : ∀ t, 0 ≤ G t := fun t => ge_of_tendsto' (hlim t) fun n => h0 n t
  have hG1 : ∀ t, G t ≤ 1 := fun t => le_of_tendsto' (hlim t) fun n => h1 n t
  have hGb : Bdd G := Bdd.of_unit hG hG0 hG1
  have key := bfc_tendsto_of_monotone E hE (g := fun n => (1 : ℝ → ℝ) - g n) (G := 1 - G)
    (fun n => measurable_const.sub (hg n)) (measurable_const.sub hG)
    (fun n t => by simp only [Pi.sub_apply, Pi.one_apply]; linarith [h1 n t])
    (fun n t => by simp only [Pi.sub_apply, Pi.one_apply]; linarith [h0 n t])
    (fun t => fun m n hmn => by
      simp only [Pi.sub_apply, Pi.one_apply]; linarith [hanti t hmn])
    (fun t => by
      simp only [Pi.sub_apply, Pi.one_apply]
      exact tendsto_const_nhds.sub (hlim t)) ξ
  simp only [bfc_sub E hE Bdd.one (hgb _), bfc_sub E hE Bdd.one hGb, bfc_one E hE,
    ContinuousLinearMap.sub_apply, Resolver.Douglas.oneA] at key
  have := tendsto_const_nhds (x := ξ) |>.sub key
  simpa using this

/-! ### Continuous approximants of half-line indicators -/

/-- The continuous approximants of `1_{Iic a}`: `t ↦ max 0 (min 1 (1 − n (t − a)))`. -/
noncomputable def stepApprox (a : ℝ) (n : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (1 - n * (t - a)))

theorem stepApprox_continuous (a : ℝ) (n : ℕ) : Continuous (stepApprox a n) := by
  unfold stepApprox; fun_prop

theorem stepApprox_nonneg (a : ℝ) (n : ℕ) (t : ℝ) : 0 ≤ stepApprox a n t := le_max_left _ _

theorem stepApprox_le_one (a : ℝ) (n : ℕ) (t : ℝ) : stepApprox a n t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem stepApprox_of_le (a : ℝ) (n : ℕ) {t : ℝ} (ht : t ≤ a) : stepApprox a n t = 1 := by
  unfold stepApprox
  have : 1 ≤ 1 - (n : ℝ) * (t - a) := by
    have : (n : ℝ) * (t - a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
      (sub_nonpos.mpr ht)
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem stepApprox_antitone (a t : ℝ) : Antitone fun n => stepApprox a n t := by
  refine antitone_nat_of_succ_le fun n => ?_
  by_cases ht : t ≤ a
  · rw [stepApprox_of_le a _ ht, stepApprox_of_le a _ ht]
  · unfold stepApprox
    refine max_le_max le_rfl (min_le_min le_rfl ?_)
    push Not at ht
    have : (0 : ℝ) ≤ t - a := (sub_pos.mpr ht).le
    push_cast
    nlinarith

theorem stepApprox_tendsto (a t : ℝ) :
    Tendsto (fun n => stepApprox a n t) atTop (𝓝 ((Set.Iic a).indicator 1 t)) := by
  by_cases ht : t ≤ a
  · have : (Set.Iic a).indicator (1 : ℝ → ℝ) t = 1 := by simp [Set.indicator, ht]
    rw [this]
    exact tendsto_const_nhds.congr fun n => (stepApprox_of_le a n ht).symm
  · push Not at ht
    have hpos : 0 < t - a := sub_pos.mpr ht
    have : (Set.Iic a).indicator (1 : ℝ → ℝ) t = 0 := by simp [Set.indicator, not_le.mpr ht]
    rw [this]
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨⌈1 / (t - a)⌉₊, fun n hn => ?_⟩)
    have hn' : 1 / (t - a) ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    have : 1 - (n : ℝ) * (t - a) ≤ 0 := by
      have := (div_le_iff₀ hpos).mp hn'
      linarith
    show (0 : ℝ) = stepApprox a n t
    unfold stepApprox
    rw [max_eq_left (min_le_of_right_le this)]

theorem indicator_one_nonneg (I : Set ℝ) (t : ℝ) : 0 ≤ I.indicator (1 : ℝ → ℝ) t := by
  by_cases h : t ∈ I <;> simp [Set.indicator, h]

theorem indicator_one_le_one (I : Set ℝ) (t : ℝ) : I.indicator (1 : ℝ → ℝ) t ≤ 1 := by
  by_cases h : t ∈ I <;> simp [Set.indicator, h]

/-! ### Membership in a strongly sequentially closed star subalgebra -/

section Membership

variable (S : StarSubalgebra ℂ (𝓗 →L[ℂ] 𝓗))
  (hS : ∀ (T : ℕ → 𝓗 →L[ℂ] 𝓗) (L : 𝓗 →L[ℂ] 𝓗), (∀ n, T n ∈ S) →
    (∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (L ξ))) → L ∈ S)
  (hES : E ∈ S)
include hS

theorem isClosed_of_strong : IsClosed (S : Set (𝓗 →L[ℂ] 𝓗)) := by
  refine IsSeqClosed.isClosed fun T L hT hTL => hS T L hT fun ξ => ?_
  exact ((ContinuousLinearMap.apply ℂ 𝓗 ξ).continuous.tendsto L).comp hTL

include hE hES

theorem cfc_mem (g : ℝ → ℝ) : cfc g E ∈ S := by
  rw [cfc_real_eq_complex g hE]
  exact (StarAlgebra.elemental.le_iff_mem (isClosed_of_strong S hS)).mpr hES
    (cfc_mem_elemental _ E)

theorem bfc_mem_of_continuous {g : ℝ → ℝ} (hg : Bdd g) (hc : Continuous g) :
    bfc E hE g ∈ S := by
  rw [bfc_cfc E hE hg hc]
  exact cfc_mem E hE S hS hES g

theorem bfc_indicator_Iic_mem (a : ℝ) : bfc E hE ((Set.Iic a).indicator 1) ∈ S := by
  refine hS (fun n => bfc E hE (stepApprox a n)) _ (fun n => bfc_mem_of_continuous E hE S hS hES
    (Bdd.of_unit (stepApprox_continuous a n).measurable (stepApprox_nonneg a n)
      (stepApprox_le_one a n)) (stepApprox_continuous a n)) fun ξ => ?_
  exact bfc_tendsto_of_antitone E hE (fun n => (stepApprox_continuous a n).measurable)
    (measurable_one.indicator measurableSet_Iic) (stepApprox_nonneg a) (stepApprox_le_one a)
    (stepApprox_antitone a) (stepApprox_tendsto a) ξ

/-- **Every spectral projection lies in `S`.** -/
theorem bfc_indicator_mem {I : Set ℝ} (hI : MeasurableSet I) :
    bfc E hE (I.indicator 1) ∈ S := by
  refine MeasurableSpace.induction_on_inter
    (C := fun I _ => bfc E hE (I.indicator (1 : ℝ → ℝ)) ∈ S)
    (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iic_rat) Real.isPiSystem_Iic_rat
    ?_ ?_ ?_ ?_ I hI
  · -- empty
    show bfc E hE ((∅ : Set ℝ).indicator (1 : ℝ → ℝ)) ∈ S
    rw [Set.indicator_empty]
    show bfc E hE 0 ∈ S
    rw [bfc_zero E hE]
    exact zero_mem S
  · -- basic half-lines
    intro t ht
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
    rw [Set.mem_singleton_iff] at ha
    show bfc E hE (t.indicator (1 : ℝ → ℝ)) ∈ S
    rw [ha]
    exact bfc_indicator_Iic_mem E hE S hS hES a
  · -- complements
    intro t htm ih
    show bfc E hE (tᶜ.indicator (1 : ℝ → ℝ)) ∈ S
    rw [Set.indicator_compl, bfc_sub E hE Bdd.one (Bdd.indicator htm), bfc_one E hE]
    exact sub_mem (one_mem S) ih
  · -- disjoint countable unions
    intro f hdisj hfm ih
    show bfc E hE ((⋃ i, f i).indicator (1 : ℝ → ℝ)) ∈ S
    have hA : ∀ n, MeasurableSet (Set.accumulate f n) := by
      intro n
      induction n with
      | zero => rw [Set.accumulate_zero_nat]; exact hfm 0
      | succ n ih => rw [Set.accumulate_succ]; exact ih.union (hfm _)
    have hAd : ∀ n, Disjoint (Set.accumulate f n) (f (n + 1)) := by
      intro n
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      obtain ⟨y, hy, hxy⟩ := Set.mem_accumulate.mp hx
      exact Set.disjoint_left.mp (hdisj (show y ≠ n + 1 by omega)) hxy hx'
    have hAmem : ∀ n, bfc E hE ((Set.accumulate f n).indicator (1 : ℝ → ℝ)) ∈ S := by
      intro n
      induction n with
      | zero => rw [Set.accumulate_zero_nat]; exact ih 0
      | succ n ihn =>
        rw [Set.accumulate_succ, Set.indicator_union_of_disjoint (hAd n)]
        show bfc E hE ((Set.accumulate f n).indicator (1 : ℝ → ℝ) + (f (n + 1)).indicator 1) ∈ S
        rw [bfc_add E hE (Bdd.indicator (hA n)) (Bdd.indicator (hfm _))]
        exact add_mem ihn (ih _)
    refine hS (fun n => bfc E hE ((Set.accumulate f n).indicator 1)) _ hAmem fun ξ => ?_
    refine bfc_tendsto_of_monotone E hE (fun n => measurable_one.indicator (hA n))
      (measurable_one.indicator (MeasurableSet.iUnion hfm)) (fun n => indicator_one_nonneg _)
      (fun n => indicator_one_le_one _) (fun t m n hmn =>
        Set.indicator_le_indicator_of_subset (Set.monotone_accumulate hmn)
          (fun _ => zero_le_one) t) (fun t => ?_) ξ
    by_cases ht : t ∈ ⋃ i, f i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      have h1 : (⋃ i, f i).indicator (1 : ℝ → ℝ) t = 1 := by simp [Set.indicator, ht]
      rw [h1]
      refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨i, fun n hn => ?_⟩)
      have : t ∈ Set.accumulate f n := Set.mem_accumulate.mpr ⟨i, hn, hi⟩
      simp [Set.indicator, this]
    · have h0 : (⋃ i, f i).indicator (1 : ℝ → ℝ) t = 0 := by simp [Set.indicator, ht]
      rw [h0]
      refine tendsto_const_nhds.congr fun n => ?_
      have : t ∉ Set.accumulate f n := fun h => by
        obtain ⟨y, _, hy⟩ := Set.mem_accumulate.mp h
        exact ht (Set.mem_iUnion.mpr ⟨y, hy⟩)
      simp [Set.indicator, this]

end Membership

/-! ### The projection-valued measure -/

/-- **The spectral projection** `P I = 1_I(E)` (junk `0` for non-measurable `I`). -/
noncomputable def P (I : Set ℝ) : 𝓗 →L[ℂ] 𝓗 := bfc E hE (I.indicator 1)

theorem P_of_not_measurable {I : Set ℝ} (hI : ¬ MeasurableSet I) : P E hE I = 0 :=
  bfc_of_not E hE fun h => hI (Bdd.measurableSet_of_indicator h)

theorem P_isSelfAdjoint (I : Set ℝ) : IsSelfAdjoint (P E hE I) := by
  by_cases hI : MeasurableSet I
  · exact bfc_isSelfAdjoint E hE (Bdd.indicator hI)
  · rw [P_of_not_measurable E hE hI]; exact star_zero _

theorem star_P (I : Set ℝ) : star (P E hE I) = P E hE I := (P_isSelfAdjoint E hE I).star_eq

theorem P_empty : P E hE ∅ = 0 := by
  unfold P
  rw [Set.indicator_empty]
  exact bfc_zero E hE

theorem P_univ : P E hE Set.univ = 1 := by
  unfold P
  rw [Set.indicator_univ]
  exact bfc_one E hE

theorem P_inter {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    P E hE I * P E hE J = P E hE (I ∩ J) := by
  unfold P
  rw [Set.inter_indicator_one, bfc_mul E hE (Bdd.indicator hI) (Bdd.indicator hJ)]

theorem P_union {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hd : Disjoint I J) : P E hE (I ∪ J) = P E hE I + P E hE J := by
  unfold P
  rw [Set.indicator_union_of_disjoint hd]
  exact bfc_add E hE (Bdd.indicator hI) (Bdd.indicator hJ)

theorem P_compl {I : Set ℝ} (hI : MeasurableSet I) : P E hE Iᶜ = 1 - P E hE I := by
  unfold P
  rw [Set.indicator_compl, bfc_sub E hE Bdd.one (Bdd.indicator hI), bfc_one E hE]

theorem P_idem {I : Set ℝ} (hI : MeasurableSet I) : P E hE I * P E hE I = P E hE I := by
  rw [P_inter E hE hI hI, Set.inter_self]

theorem P_nonneg (I : Set ℝ) : 0 ≤ P E hE I := by
  by_cases hI : MeasurableSet I
  · exact bfc_nonneg E hE (Bdd.indicator hI) (indicator_one_nonneg I)
  · rw [P_of_not_measurable E hE hI]

theorem P_le_one (I : Set ℝ) : P E hE I ≤ 1 := by
  by_cases hI : MeasurableSet I
  · exact bfc_le_one E hE (Bdd.indicator hI) (indicator_one_le_one I)
  · rw [P_of_not_measurable E hE hI]; exact zero_le_one

theorem P_norm_le_one (I : Set ℝ) : ‖P E hE I‖ ≤ 1 :=
  StrongLimit.norm_le_one_of_nonneg_le_one (P_nonneg E hE I) (P_le_one E hE I)

/-- The quadratic form of `P I` is the spectral measure: `⟪ξ, P I ξ⟫ = ν_ξ(I)`. -/
theorem inner_P {I : Set ℝ} (hI : MeasurableSet I) (ξ : 𝓗) :
    ⟪ξ, P E hE I ξ⟫_ℂ = (((ν E hE ξ) I).toReal : ℂ) := by
  rw [P, inner_bfc_self E hE (Bdd.indicator hI), Q, integral_indicator_one hI, measureReal_def]

theorem re_inner_P {I : Set ℝ} (hI : MeasurableSet I) (ξ : 𝓗) :
    (⟪ξ, P E hE I ξ⟫_ℂ).re = ((ν E hE ξ) I).toReal := by
  rw [inner_P E hE hI, Complex.ofReal_re]

theorem norm_P_apply_sq {I : Set ℝ} (hI : MeasurableSet I) (ξ : 𝓗) :
    ‖P E hE I ξ‖ ^ 2 = ((ν E hE ξ) I).toReal := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_sa (P_isSelfAdjoint E hE I),
    ← Resolver.Douglas.mulA, P_idem E hE hI, ← re_inner_P E hE hI]
  rfl

theorem P_mono {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) (h : I ⊆ J) :
    P E hE I ≤ P E hE J :=
  bfc_mono E hE (Bdd.indicator hI) (Bdd.indicator hJ) fun t =>
    Set.indicator_le_indicator_of_subset h (fun _ => zero_le_one) t

theorem P_compl_spectrum : P E hE (spectrum ℝ E)ᶜ = 0 := by
  refine ext_of_inner_self fun ξ => ?_
  rw [inner_P E hE (spectrum.isClosed E).measurableSet.compl, ν_compl_spectrum, ENNReal.toReal_zero,
    Complex.ofReal_zero, ContinuousLinearMap.zero_apply, inner_zero_right]

theorem P_spectrum : P E hE (spectrum ℝ E) = 1 := by
  have := P_compl E hE (spectrum.isClosed E).measurableSet
  rw [P_compl_spectrum] at this
  exact (sub_eq_zero.mp this.symm).symm

theorem P_eq_zero_of_disjoint_spectrum {I : Set ℝ} (hI : MeasurableSet I)
    (h : Disjoint I (spectrum ℝ E)) : P E hE I = 0 := by
  rw [← mul_one (P E hE I), ← P_spectrum E hE, P_inter E hE hI (spectrum.isClosed E).measurableSet,
    Set.disjoint_iff_inter_eq_empty.mp h, P_empty]

theorem P_comm_bfc {I : Set ℝ} (hI : MeasurableSet I) {g : ℝ → ℝ} (hg : Bdd g) :
    P E hE I * bfc E hE g = bfc E hE g * P E hE I :=
  bfc_comm E hE (Bdd.indicator hI) hg

theorem P_comm {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    P E hE I * P E hE J = P E hE J * P E hE I := by
  rw [P_inter E hE hI hJ, P_inter E hE hJ hI, Set.inter_comm]

/-- Membership of every spectral projection in a strongly sequentially closed star
subalgebra containing `E`. -/
theorem P_mem (S : StarSubalgebra ℂ (𝓗 →L[ℂ] 𝓗))
    (hS : ∀ (T : ℕ → 𝓗 →L[ℂ] 𝓗) (L : 𝓗 →L[ℂ] 𝓗), (∀ n, T n ∈ S) →
      (∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (L ξ))) → L ∈ S)
    (hES : E ∈ S) (I : Set ℝ) : P E hE I ∈ S := by
  by_cases hI : MeasurableSet I
  · exact bfc_indicator_mem E hE S hS hES hI
  · rw [P_of_not_measurable E hE hI]; exact zero_mem S

/-! ### Norm bounds, finite sums, and membership of every bounded Borel function -/

theorem norm_bfc_apply_sq {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) :
    ‖bfc E hE g ξ‖ ^ 2 = ∫ t, (g * g) t ∂(ν E hE ξ) := by
  have h1 : ⟪bfc E hE g ξ, bfc E hE g ξ⟫_ℂ = ⟪ξ, bfc E hE (g * g) ξ⟫_ℂ := by
    rw [← inner_sa (bfc_isSelfAdjoint E hE hg), ← Resolver.Douglas.mulA, ← bfc_mul E hE hg hg]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1, ← re_inner_bfc_self E hE (hg.mul hg)]
  rfl

theorem norm_bfc_apply_le {g : ℝ → ℝ} (hg : Bdd g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) (ξ : 𝓗) :
    ‖bfc E hE g ξ‖ ≤ C * ‖ξ‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hb : ∫ t, (g * g) t ∂(ν E hE ξ) ≤ C * C * ‖ξ‖ ^ 2 := by
    have := abs_integral_ν_le E hE ξ (g := g * g) (C := C * C) fun t => by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hC t) (hC t) (abs_nonneg _) hC0
    exact (le_abs_self _).trans this
  have hsq : ‖bfc E hE g ξ‖ ^ 2 ≤ (C * ‖ξ‖) ^ 2 := by
    rw [norm_bfc_apply_sq E hE hg ξ]
    calc _ ≤ C * C * ‖ξ‖ ^ 2 := hb
      _ = (C * ‖ξ‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _)) two_ne_zero).mp hsq

theorem norm_bfc_le {g : ℝ → ℝ} (hg : Bdd g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) :
    ‖bfc E hE g‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ ((abs_nonneg _).trans (hC 0))
    (norm_bfc_apply_le E hE hg hC)

theorem Bdd.finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ} (hg : ∀ i ∈ s, Bdd (g i)) :
    Bdd (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Bdd.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem bfc_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ} (hg : ∀ i ∈ s, Bdd (g i)) :
    bfc E hE (∑ i ∈ s, g i) = ∑ i ∈ s, bfc E hE (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact bfc_zero E hE
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      bfc_add E hE (hg a (Finset.mem_insert_self a s))
        (Bdd.finsetSum s fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- The dyadic approximant `⌊2ⁿ g⌋ / 2ⁿ` of a real function. -/
noncomputable def dyadic (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := (⌊(2 : ℝ) ^ n * g t⌋ : ℝ) / 2 ^ n

theorem dyadic_measurable {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) : Measurable (dyadic g n) :=
  (measurable_from_top.comp (measurable_const.mul hg).floor).div_const _

theorem dyadic_le (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : dyadic g n t ≤ g t := by
  unfold dyadic
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact Int.floor_le _

theorem lt_dyadic_add (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : g t < dyadic g n t + (1 / 2) ^ n := by
  unfold dyadic
  have h := Int.lt_floor_add_one ((2 : ℝ) ^ n * g t)
  rw [one_div_pow, ← add_div, lt_div_iff₀ (by positivity), mul_comm]
  exact h

theorem abs_sub_dyadic_le (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : |dyadic g n t - g t| ≤ (1 / 2) ^ n :=
  abs_le.mpr ⟨by linarith [lt_dyadic_add g n t],
    by linarith [dyadic_le g n t, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]⟩

theorem dyadic_bdd {g : ℝ → ℝ} (hg : Bdd g) (n : ℕ) : Bdd (dyadic g n) := by
  obtain ⟨C, hC⟩ := hg.2
  refine ⟨dyadic_measurable hg.1 n, C + 1, fun t => ?_⟩
  have h1 := abs_sub_dyadic_le g n t
  have h2 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc |dyadic g n t| = |(dyadic g n t - g t) + g t| := by ring_nf
    _ ≤ |dyadic g n t - g t| + |g t| := abs_add_le _ _
    _ ≤ C + 1 := by linarith [hC t]

/-- The dyadic approximant is a finite combination of indicators of level sets. -/
theorem dyadic_eq_sum {g : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |g t| ≤ C) (n : ℕ) :
    dyadic g n = ∑ k ∈ Finset.Icc (-(⌈(2 : ℝ) ^ n * C⌉ + 1)) (⌈(2 : ℝ) ^ n * C⌉ + 1),
      fun t => ((k : ℝ) / 2 ^ n) * {t | ⌊(2 : ℝ) ^ n * g t⌋ = k}.indicator 1 t := by
  funext t
  rw [Finset.sum_apply]
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  have hmem : ⌊(2 : ℝ) ^ n * g t⌋ ∈ Finset.Icc (-(⌈(2 : ℝ) ^ n * C⌉ + 1)) (⌈(2 : ℝ) ^ n * C⌉ + 1) := by
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    have hb : |(2 : ℝ) ^ n * g t| ≤ 2 ^ n * C := by
      rw [abs_mul, abs_of_pos hpos]; exact mul_le_mul_of_nonneg_left (hC t) hpos.le
    have hc : (2 : ℝ) ^ n * C ≤ ⌈(2 : ℝ) ^ n * C⌉ := Int.le_ceil _
    rw [Finset.mem_Icc]
    constructor
    · have : (-(⌈(2 : ℝ) ^ n * C⌉ + 1) : ℝ) ≤ ⌊(2 : ℝ) ^ n * g t⌋ := by
        have := Int.sub_one_lt_floor ((2 : ℝ) ^ n * g t)
        linarith [(abs_le.mp hb).1]
      exact_mod_cast this
    · have : (⌊(2 : ℝ) ^ n * g t⌋ : ℝ) ≤ ⌈(2 : ℝ) ^ n * C⌉ + 1 := by
        have := Int.floor_le ((2 : ℝ) ^ n * g t)
        linarith [(abs_le.mp hb).2]
      exact_mod_cast this
  rw [if_pos hmem]
  rfl

/-- **Every bounded Borel function of `E` lies in `S`**: the dyadic approximants are finite
combinations of spectral projections, and converge in operator norm. -/
theorem bfc_mem_of_bdd (S : StarSubalgebra ℂ (𝓗 →L[ℂ] 𝓗))
    (hS : ∀ (T : ℕ → 𝓗 →L[ℂ] 𝓗) (L : 𝓗 →L[ℂ] 𝓗), (∀ n, T n ∈ S) →
      (∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (L ξ))) → L ∈ S)
    (hES : E ∈ S) {g : ℝ → ℝ} (hg : Bdd g) : bfc E hE g ∈ S := by
  obtain ⟨C, hC⟩ := hg.2
  have hmem : ∀ n, bfc E hE (dyadic g n) ∈ S := by
    intro n
    have hlev : ∀ k : ℤ, MeasurableSet {t : ℝ | ⌊(2 : ℝ) ^ n * g t⌋ = k} := fun k =>
      measurableSet_eq_fun (measurable_const.mul hg.1).floor measurable_const
    have hbdd : ∀ k ∈ Finset.Icc (-(⌈(2 : ℝ) ^ n * C⌉ + 1)) (⌈(2 : ℝ) ^ n * C⌉ + 1),
        Bdd fun t => ((k : ℝ) / 2 ^ n) * {t | ⌊(2 : ℝ) ^ n * g t⌋ = k}.indicator 1 t :=
      fun k _ => Bdd.const_mul _ (Bdd.indicator (hlev k))
    rw [dyadic_eq_sum hC n, bfc_finsetSum E hE _ hbdd]
    refine sum_mem fun k _ => ?_
    rw [bfc_const_mul E hE _ (Bdd.indicator (hlev k))]
    exact S.smul_mem (bfc_indicator_mem E hE S hS hES (hlev k)) _
  have hlim : Tendsto (fun n => bfc E hE (dyadic g n)) atTop (𝓝 (bfc E hE g)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    rw [← bfc_sub E hE (dyadic_bdd hg n) hg]
    exact norm_bfc_le E hE ((dyadic_bdd hg n).sub hg) fun t => by
      rw [Pi.sub_apply]; exact abs_sub_dyadic_le g n t
  exact (isClosed_of_strong S hS).mem_of_tendsto hlim (Eventually.of_forall hmem)

/-! ### Spectral projections of increasing unions -/

theorem indicator_iUnion_tendsto {I : ℕ → Set ℝ} (hmono : Monotone I) (t : ℝ) :
    Tendsto (fun n => (I n).indicator (1 : ℝ → ℝ) t) atTop (𝓝 ((⋃ n, I n).indicator 1 t)) := by
  by_cases ht : t ∈ ⋃ n, I n
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    have h1 : (⋃ n, I n).indicator (1 : ℝ → ℝ) t = 1 := by simp [Set.indicator, ht]
    rw [h1]
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨i, fun n hn => ?_⟩)
    have : t ∈ I n := hmono hn hi
    simp [Set.indicator, this]
  · have h0 : (⋃ n, I n).indicator (1 : ℝ → ℝ) t = 0 := by simp [Set.indicator, ht]
    rw [h0]
    refine tendsto_const_nhds.congr fun n => ?_
    have : t ∉ I n := fun h => ht (Set.mem_iUnion.mpr ⟨n, h⟩)
    simp [Set.indicator, this]

/-- Strong convergence `P (I n) → P (⋃ n, I n)` for an increasing sequence of Borel sets. -/
theorem P_tendsto_iUnion {I : ℕ → Set ℝ} (hI : ∀ n, MeasurableSet (I n)) (hmono : Monotone I)
    (ξ : 𝓗) : Tendsto (fun n => P E hE (I n) ξ) atTop (𝓝 (P E hE (⋃ n, I n) ξ)) :=
  bfc_tendsto_of_monotone E hE (fun n => measurable_one.indicator (hI n))
    (measurable_one.indicator (MeasurableSet.iUnion hI)) (fun n => indicator_one_nonneg _)
    (fun n => indicator_one_le_one _)
    (fun t m n hmn => Set.indicator_le_indicator_of_subset (hmono hmn) (fun _ => zero_le_one) t)
    (indicator_iUnion_tendsto hmono) ξ

/-- The spectral projections of an operator with spectrum in `[0, 1]`. -/
theorem P_Icc_zero_one (h : spectrum ℝ E ⊆ Set.Icc 0 1) : P E hE (Set.Icc 0 1) = 1 := by
  have h1 : P E hE (Set.Icc 0 1)ᶜ = 0 :=
    P_eq_zero_of_disjoint_spectrum E hE measurableSet_Icc.compl
      (Set.disjoint_left.mpr fun t ht ht' => ht (h ht'))
  have h2 := P_compl E hE (measurableSet_Icc (a := (0 : ℝ)) (b := 1))
  rw [h1] at h2
  exact (sub_eq_zero.mp h2.symm).symm

end BorelCalc

end CommutingRepetition
