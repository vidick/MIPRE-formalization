/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Orthonormalization.CenterTrace
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.PolarDecomp

@[expose] public section

/-!
# The clauses of a centre-valued trace, from the centre-valued expectation

The algebraic, analytic and order clauses of the vendored `IsCenterValuedTrace M 1 E` for a
centre-valued expectation `E` (`IsCenterExpectation`,
`MIPRE/Background/Orthonormalization/CenterTrace.lean`) of a von Neumann algebra with a faithful
tracial vector functional. Each algebraic clause is an identity between central elements with the
same pairings with the centre, hence an equality by `eq_of_isCentralIn_of_pairing`; normality is a
weak-operator cluster-point argument (every cluster point of `E (T k)` is central with the pairings
of `L`); division in the centre takes a weak-operator cluster point of `a (c + ε)⁻¹`. The two
comparison clauses are `MIPRE/Background/Orthonormalization/CenterComparison.lean`.

Two facts about the centre `Z(M)` itself come first: it is closed in the weak operator topology
(`isClosed_setOf_isCentralIn_one`), and for central `0 ≤ a ≤ c` there is a central `0 ≤ z ≤ 1`
with `a = z c` (`exists_isCentralIn_eq_mul_of_le`), the functional calculus of the abelian algebra
`Z(M)` carried out inside `M`; neither uses the vector functional.
-/

namespace MIPRE.Orthonormalization

open scoped ComplexOrder InnerProductSpace
open Filter Topology Orthogonalization.MvN ContinuousLinearMapWOT

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {d : ℕ} {g : Fin d → H}

/-! ### The centre of `M` -/

/-- **The centre of `M` is weak-operator closed**: at `p = 1`, `IsCentralIn M 1 c` says `c ∈ M` and
`c` commutes with every element of `M`, two closed conditions (`isClosed_setOf_mem`,
`isClosed_setOf_commute`). -/
theorem isClosed_setOf_isCentralIn_one (M : VonNeumannAlgebra H) :
    IsClosed {A : H →WOT[ℂ] H | IsCentralIn M 1 (toCLM A)} := by
  have : {A : H →WOT[ℂ] H | IsCentralIn M 1 (toCLM A)} =
      {A | toCLM A ∈ M} ∩ ⋂ y ∈ M, {A | Commute (toCLM A) y} := by
    ext A
    simp [IsCentralIn]
  rw [this]
  exact (isClosed_setOf_mem M).inter (isClosed_biInter fun y _ => isClosed_setOf_commute y)

/-- **Approximate division in the centre**: for central `0 ≤ a ≤ c` and `ε > 0`, the central
element `z = a (c + ε)⁻¹` satisfies `0 ≤ z ≤ 1` and `‖z c - a‖ ≤ ε`, since `z c - a = -ε z`. -/
theorem exists_isCentralIn_norm_mul_sub_le {a c : H →L[ℂ] H} (ha : IsCentralIn M 1 a)
    (hc : IsCentralIn M 1 c) (ha0 : 0 ≤ a) (hac : a ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∃ z, IsCentralIn M 1 z ∧ 0 ≤ z ∧ z ≤ 1 ∧ ‖z * c - a‖ ≤ ε := by
  have hc0 : 0 ≤ c := ha0.trans hac
  have hpos : ∀ t ∈ spectrum ℝ c, 0 < t + ε := fun t ht => by
    linarith [spectrum_nonneg_of_nonneg hc0 ht]
  -- `w = (c + ε)⁻¹`, a positive element of `M` commuting with `M`
  set w := cfc (fun t : ℝ => (t + ε)⁻¹) c
  have hw0 : 0 ≤ w := cfc_nonneg fun t ht => (inv_pos.mpr (hpos t ht)).le
  have hw1 : c * w + ε • w = 1 := by
    have h : cfc (fun t : ℝ => (t + ε) * (t + ε)⁻¹) c = cfc (fun t : ℝ => t + ε) c * w :=
      cfc_mul _ _ c (hg := continuousOn_inv_add hc0 hε)
    rw [cfc_congr (g := fun _ => (1 : ℝ)) fun t ht => mul_inv_cancel₀ (hpos t ht).ne',
      cfc_const_one ℝ c, cfc_add_const ε (fun t : ℝ => t) c, cfc_id' ℝ c, add_mul,
      ← Algebra.smul_def] at h
    exact h.symm
  have hwc : Commute c w := ((Commute.refl c).cfc_real _).symm
  have hwa : Commute a w := ((hc.2.2 a ha.1 (by rw [one_mul, mul_one])).cfc_real _).symm
  -- `0 ≤ a w ≤ 1`, since `1 - a w = (c - a) w + ε w`
  have hz0 : 0 ≤ a * w := Commute.mul_nonneg ha0 hw0 hwa
  have hz1 : a * w ≤ 1 := by
    have h : 1 - a * w = (c - a) * w + ε • w := by rw [← hw1, sub_mul]; abel
    rw [← sub_nonneg, h]
    exact add_nonneg (Commute.mul_nonneg (sub_nonneg.mpr hac) hw0 (hwc.sub_left hwa))
      (smul_nonneg hε.le hw0)
  refine ⟨a * w, ⟨mul_mem ha.1 (CommutingRepetition.VN.cfc_real_mem M hc.1 _),
    by rw [one_mul, mul_one], fun y hy h1 => (ha.2.2 y hy h1).mul_left
      ((hc.2.2 y hy h1).cfc_real _)⟩, hz0, hz1, ?_⟩
  -- `a w c - a = -ε a w`, and `‖a w‖ ≤ ‖1‖ ≤ 1`
  have h : a * w * c - a = -(ε • (a * w)) := by
    rw [mul_assoc, ← hwc.eq, eq_sub_of_add_eq hw1, mul_sub, mul_one, mul_smul_comm]; abel
  rw [h, norm_neg, norm_smul, Real.norm_of_nonneg hε.le]
  exact mul_le_of_le_one_right hε.le
    ((CStarAlgebra.norm_le_norm_of_le_of_nonneg hz1 hz0).trans ContinuousLinearMap.norm_id_le)

/-- **Division in the centre**: for central `0 ≤ a ≤ c`, `a = z c` for a central `0 ≤ z ≤ 1`.
The approximate quotients `zⱼ` with `‖zⱼ c - a‖ ≤ 1/(j+1)` have a weak-operator cluster point `z`,
which is central with `0 ≤ z ≤ 1` (closed conditions); `z c` is a cluster point of `zⱼ c`, since
right multiplication by `c` is weak-operator continuous, and `zⱼ c → a`. -/
theorem exists_isCentralIn_eq_mul_of_le {a c : H →L[ℂ] H} (ha : IsCentralIn M 1 a)
    (hc : IsCentralIn M 1 c) (ha0 : 0 ≤ a) (hac : a ≤ c) :
    ∃ z, IsCentralIn M 1 z ∧ 0 ≤ z ∧ z ≤ 1 ∧ a = z * c := by
  choose z hzc hz0 hz1 hzε using fun j : ℕ =>
    exists_isCentralIn_norm_mul_sub_le ha hc ha0 hac (Nat.one_div_pos_of_nat (n := j))
  obtain ⟨z₀, -, hz₀⟩ := exists_clusterPt_of_norm_le (l := atTop) fun j =>
    (CStarAlgebra.norm_le_norm_of_le_of_nonneg (hz1 j) (hz0 j)).trans
      ContinuousLinearMap.norm_id_le
  have hz₀' : MapClusterPt (ofCLM z₀) atTop fun j => ofCLM (z j) := hz₀
  refine ⟨z₀, (isClosed_setOf_isCentralIn_one M).mem_of_mapClusterPt hz₀'
    (Eventually.of_forall hzc), isClosed_setOf_nonneg.mem_of_mapClusterPt hz₀'
    (Eventually.of_forall hz0), (isClosed_setOf_le 1).mem_of_mapClusterPt hz₀'
    (Eventually.of_forall hz1), ?_⟩
  have hlim : Tendsto (fun j => ofCLM (z j) * ofCLM c) atTop (𝓝 (ofCLM a)) := by
    refine (continuous_ofCLM.tendsto a).comp ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun j => norm_nonneg _) hzε tendsto_one_div_add_atTop_nhds_zero_nat
  have hcl := hz₀'.continuousAt_comp (continuous_mul_const (ofCLM c)).continuousAt
  exact congrArg toCLM (eq_of_nhds_neBot (hcl.neBot.mono (inf_le_inf_left _ hlim))).symm

/-! ### The clauses of `IsCenterValuedTrace M 1 E` -/

namespace IsCenterExpectation

variable {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} (hE : IsCenterExpectation M g E)
include hE

/-- `E` preserves the vector functional on `M` (the pairing with the central element `1`). -/
theorem vecFunctional_eq : ∀ x ∈ M, vecFunctional g (E x) = vecFunctional g x := fun x hx => by
  simpa only [mul_one] using
    hE.pairing x hx 1 isCentralIn_one_one

/-- The trace property of `E` on `M`. -/
theorem trace (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∀ x ∈ M, ∀ y ∈ M, E (x * y) = E (y * x) := by
  intro x hx y hy
  refine eq_of_isCentralIn_of_pairing hsep (hE.mem_center _ (mul_mem hx hy))
    (hE.mem_center _ (mul_mem hy hx)) fun c hc => ?_
  rw [hE.pairing _ (mul_mem hx hy) c hc, hE.pairing _ (mul_mem hy hx) c hc]
  calc vecFunctional g (x * y * c) = vecFunctional g (x * (y * c)) := by rw [mul_assoc]
    _ = vecFunctional g (y * c * x) := htr x hx (y * c) (mul_mem hy hc.1)
    _ = vecFunctional g (y * x * c) := by
      rw [mul_assoc, (hc.2.2 x hx (by rw [one_mul, mul_one])).eq, ← mul_assoc]

/-- `E` is the identity on the centre. -/
theorem center_fixed (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∀ c, IsCentralIn M 1 c → E c = c := fun c hc =>
  eq_of_isCentralIn_of_pairing hsep (hE.mem_center c hc.1) hc fun c' hc' =>
    hE.pairing c hc.1 c' hc'

/-- `E` is linear over the centre. -/
theorem center_mul (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∀ c, IsCentralIn M 1 c → ∀ x ∈ M, E (c * x) = c * E x := by
  intro c hc x hx
  have hEx := hE.mem_center x hx
  refine eq_of_isCentralIn_of_pairing hsep (hE.mem_center _ (mul_mem hc.1 hx))
    (isCentralIn_one_mul hc hEx) fun c' hc' => ?_
  -- `τ(E(c x) c') = τ(c x c')` and `τ(c E(x) c') = τ(E(x) (c c')) = τ(x (c c')) = τ(c x c')`
  rw [hE.pairing _ (mul_mem hc.1 hx) c' hc',
    (hEx.2.2 c hc.1 (by rw [one_mul, mul_one])).symm.eq, mul_assoc (E x),
    hE.pairing x hx _ (isCentralIn_one_mul hc hc'), ← mul_assoc,
    (hc.2.2 x hx (by rw [one_mul, mul_one])).eq]

/-- `E` is faithful on `M`. -/
theorem faithful (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∀ x ∈ M, E (star x * x) = 0 → x = 0 := by
  intro x hx h0
  -- `τ(x* x) = τ(E(x* x)) = 0`
  refine eq_zero_of_vecFunctional_star_mul_self_eq_zero hsep hx ?_
  rw [← hE.vecFunctional_eq _ (mul_mem (star_mem hx) hx), h0, map_zero]

/-- **Normality**: `E` is continuous along bounded weak-operator convergent nets of `M`. -/
theorem normal (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∀ {κ : Type u} (l : Filter κ) (T : κ → H →L[ℂ] H) (L : H →L[ℂ] H),
      (∀ k, T k ∈ M) → L ∈ M → TendstoWeakBdd l T L →
        TendstoWeakBdd l (fun k => E (T k)) (E L) := by
  intro κ l T L hT hL ⟨⟨C, hC⟩, hTL⟩
  have hbd : ∀ k, ‖E (T k)‖ ≤ C := fun k => (hE.norm_le _ (hT k)).trans (hC k)
  refine ⟨⟨C, hbd⟩, tendsto_ofCLM_iff.mp ?_⟩
  -- the net lives in a compact ball; every cluster point `A` of it is `E L`
  refine (isCompact_setOf_norm_le C).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall hbd) fun A _ hA => ?_
  have hAc : IsCentralIn M 1 (toCLM A) := (isClosed_setOf_isCentralIn_one M).mem_of_mapClusterPt
    hA (Eventually.of_forall fun k => hE.mem_center _ (hT k))
  -- `A` has the pairings of `L`: `τ(E(T k) c) = τ(T k c) → τ(L c)`, and `τ(· c)` is continuous
  have hAp : ∀ c, IsCentralIn M 1 c →
      vecFunctional g (toCLM A * c) = vecFunctional g (E L * c) := by
    intro c hc
    have hlim : Tendsto (fun k => vecFunctional g (E (T k) * c)) l
        (𝓝 (vecFunctional g (L * c))) := by
      refine Tendsto.congr (fun k => (hE.pairing _ (hT k) c hc).symm) ?_
      simp only [vecFunctional_apply, mul_apply_eq_comp]
      exact tendsto_finsetSum _ fun k _ => hTL _ _
    rw [hE.pairing L hL c hc]
    exact eq_of_nhds_neBot ((hA.continuousAt_comp
      (continuous_vecFunctional_mul g c).continuousAt).neBot.mono (inf_le_inf_left _ hlim))
  exact congrArg ofCLM (eq_of_isCentralIn_of_pairing hsep hAc (hE.mem_center L hL) hAp)

/-- **Division in the centre**: for `0 ≤ b ≤ r` with `r` a projection of `M`, `E b = z * E r` for
a central `0 ≤ z ≤ 1`. It does not use the vector functional. -/
theorem div :
    ∀ r, IsStarProjection r → r ∈ M → ∀ b ∈ M, 0 ≤ b → b ≤ r →
      ∃ z, IsCentralIn M 1 z ∧ 0 ≤ z ∧ z ≤ 1 ∧ E b = z * E r := by
  intro r _ hrM b hbM hb0 hbr
  refine exists_isCentralIn_eq_mul_of_le (hE.mem_center b hbM) (hE.mem_center r hrM)
    (hE.nonneg b hbM hb0) (sub_nonneg.mp ?_)
  rw [← map_sub]
  exact hE.nonneg _ (sub_mem hrM hbM) (sub_nonneg.mpr hbr)

end IsCenterExpectation

end MIPRE.Orthonormalization

end
