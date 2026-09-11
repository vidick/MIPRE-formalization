/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/CrossedTracial.lean
-/
/-
# From a standard-form strategy to a tracially embeddable correlation (stage E7.3b)

Given a commuting strategy in standard form (`StdStrategy`, E7.2) we form the discrete
crossed product `ℛ = crossed M Ω` by the modular group (E5), run Haagerup's reduction
(E6) to the tracial subalgebras `ℛ_n` with the conditional expectations `Φ_n`, and read
off a tracially embeddable correlation:

* Alice's effects are `Φ_n(π(A_a^x)) ∈ ℛ_n` — `Φ_n` is unital and positive, so this is
  again a POVM, and `Φ_n(x)Ω̂ → xΩ̂` (E6.5) makes the error uniformly small;
* Bob's effects are the amplifications `1 ⊗ B_b^y`, which lie in `ℛ′`
  (`amp_commutant_mem`), and enter through the positive functionals
  `ω_b^y(z) = ⟪Ω̂, z (1 ⊗ B_b^y) Ω̂⟫`;
* the tracial state is `τ = ‖ξ_n‖^{-2}⟪ξ_n, · ξ_n⟫` on `ℛ_n` (tracial by
  `tracial_Rn`) and the density is `σ = ‖ξ_n‖ · e^{a_n/2}`, so that
  `τ(σ · σ) = ⟪Ω̂, · Ω̂⟫` on `ℛ_n` (`inner_Ωh_eq_inner_xin_dn`).

`exists_tracial_approx` is the output: a tracially embeddable correlation entrywise
`η`-close to the correlation of the standard-form strategy. Proof-side.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.StandardStrategy
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.ClosedSubalg
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.RadonNikodym
import MIPRE.Background.Repetition.CommutingRepetition.VN.Haagerup.Density

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder
open VN VN.Crossed VN.Haagerup VN.Modular
open Filter Topology

set_option linter.unusedSectionVars false

/-! ## Positivity and finite sums for `π`, `amp` and `Φ_n` -/

section Pos

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)

theorem π_finset_sum {ι : Type*} (s : Finset ι) (f : ι → K →L[ℂ] K) :
    π M Ω (∑ i ∈ s, f i) = ∑ i ∈ s, π M Ω (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, π_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, π_add, ih]

theorem amp_finset_sum {ι : Type*} (s : Finset ι) (f : ι → K →L[ℂ] K) :
    amp (∑ i ∈ s, f i) = ∑ i ∈ s, amp (K := K) (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact diag_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, amp_add, ih]

/-- `π` preserves positivity: `y = c*c` gives `π y = (π c)*(π c)`. -/
theorem π_nonneg {y : K →L[ℂ] K} (hy : 0 ≤ y) : 0 ≤ π M Ω y := by
  have hsa : IsSelfAdjoint y := IsSelfAdjoint.of_nonneg hy
  set c := cfc Real.sqrt y with hc
  have hcsa : IsSelfAdjoint c := cfc_predicate _ _
  have hcc : c * c = y := by
    rw [hc, ← cfc_mul Real.sqrt Real.sqrt y Real.continuous_sqrt.continuousOn
      Real.continuous_sqrt.continuousOn]
    calc cfc (fun t : ℝ => Real.sqrt t * Real.sqrt t) y = cfc (fun t : ℝ => t) y :=
          cfc_congr fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hy ht)
      _ = y := cfc_id' ℝ y hsa
  have : π M Ω y = star (π M Ω c) * π M Ω c := by
    rw [← π_star, hcsa.star_eq, ← π_mul, hcc]
  rw [this]
  exact star_mul_self_nonneg _

/-- `amp` preserves positivity. -/
theorem amp_nonneg {y : K →L[ℂ] K} (hy : 0 ≤ y) : 0 ≤ amp (K := K) y := by
  have hsa : IsSelfAdjoint y := IsSelfAdjoint.of_nonneg hy
  set c := cfc Real.sqrt y with hc
  have hcsa : IsSelfAdjoint c := cfc_predicate _ _
  have hcc : c * c = y := by
    rw [hc, ← cfc_mul Real.sqrt Real.sqrt y Real.continuous_sqrt.continuousOn
      Real.continuous_sqrt.continuousOn]
    calc cfc (fun t : ℝ => Real.sqrt t * Real.sqrt t) y = cfc (fun t : ℝ => t) y :=
          cfc_congr fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hy ht)
      _ = y := cfc_id' ℝ y hsa
  have : amp (K := K) y = star (amp (K := K) c) * amp (K := K) c := by
    rw [← amp_star, hcsa.star_eq, ← amp_mul, hcc]
  rw [this]
  exact star_mul_self_nonneg _

theorem Phi_zero (n : ℕ) : Phi M Ω n (0 : L2Q K →L[ℂ] L2Q K) = 0 := by
  have := Phi_smul M Ω n 0 (0 : L2Q K →L[ℂ] L2Q K)
  simpa using this

theorem Phi_finset_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → L2Q K →L[ℂ] L2Q K) :
    Phi M Ω n (∑ i ∈ s, f i) = ∑ i ∈ s, Phi M Ω n (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Phi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Phi_add, ih]

/-! ### `e^{r a_n}` lies in `ℛ_n` -/

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
theorem expA_an_mem_Rn (n : ℕ) (r : ℝ) : expA (an (K := K) n) r ∈ Rn M Ω n := by
  have hcen := isCentral_expA_an M Ω hs hc n r
  refine (mem_Rn_iff_σ M Ω hs hc).mpr ⟨hcen.1, fun t => ?_⟩
  have hfix : σ (crossed M Ω) (Ωh Ω) t (expA (an (K := K) n) r) = expA (an (K := K) n) r :=
    σ_eq_self_of_commute_R (crossed M Ω) (Ωh Ω) hcen.2 t
  have hcomm : Commute (expA (an (K := K) n) r)
      (eit (an (K := K) n) (isSelfAdjoint_an n) t) :=
    commute_expA (commute_eit (isSelfAdjoint_an n) (Commute.refl (an (K := K) n)) t).symm r
  rw [σ_xin M Ω hs hc n t hcen.1, hfix]
  calc eit (an (K := K) n) (isSelfAdjoint_an n) (-t) * expA (an (K := K) n) r *
        eit (an (K := K) n) (isSelfAdjoint_an n) t
      = eit (an (K := K) n) (isSelfAdjoint_an n) (-t) *
          (eit (an (K := K) n) (isSelfAdjoint_an n) t * expA (an (K := K) n) r) := by
        rw [mul_assoc, ← hcomm.eq]
    _ = expA (an (K := K) n) r := by
        rw [← mul_assoc, eit_neg_mul, one_mul]

include hs hc in
theorem dn_mem_Rn (n : ℕ) : dn (K := K) n ∈ Rn M Ω n := expA_an_mem_Rn M Ω hs hc n 1

end Pos

/-! ## Alice and Bob inside the crossed product -/

namespace StdStrategy

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable (q : StdStrategy X Y A B)

/-- Alice's effect, transported into the crossed product by `π`. -/
noncomputable def Ai (x : X) (a : A) : L2Q q.K →L[ℂ] L2Q q.K := π q.M q.Ω (q.Aop x a)

/-- Bob's effect, transported into the commutant of the crossed product by `amp`. -/
noncomputable def Bi (y : Y) (b : B) : L2Q q.K →L[ℂ] L2Q q.K := amp (q.Bop y b)

theorem Ai_def (x : X) (a : A) : q.Ai x a = π q.M q.Ω (q.Aop x a) := rfl

theorem Bi_def (y : Y) (b : B) : q.Bi y b = amp (q.Bop y b) := rfl

theorem Ai_mem (x : X) (a : A) : q.Ai x a ∈ crossed q.M q.Ω :=
  π_mem q.M q.Ω (q.Aop_mem x a)

theorem Ai_nonneg (x : X) (a : A) : 0 ≤ q.Ai x a :=
  π_nonneg q.M q.Ω (q.Aop_nonneg x a)

theorem Ai_sum (x : X) : ∑ a : A, q.Ai x a = 1 := by
  rw [show (∑ a : A, q.Ai x a) = π q.M q.Ω (∑ a : A, q.Aop x a) from
    (π_finset_sum q.M q.Ω Finset.univ (q.Aop x)).symm, q.Aop_sum x, π_one]

theorem Bi_mem_commutant (y : Y) (b : B) : q.Bi y b ∈ (crossed q.M q.Ω).commutant :=
  amp_commutant_mem q.M q.Ω q.sep q.cyc (q.Bop_mem y b)

theorem Bi_nonneg (y : Y) (b : B) : 0 ≤ q.Bi y b :=
  amp_nonneg (q.Bop_nonneg y b)

theorem Bi_sum (y : Y) : ∑ b : B, q.Bi y b = 1 := by
  rw [show (∑ b : B, q.Bi y b) = amp (K := q.K) (∑ b : B, q.Bop y b) from
    (amp_finset_sum Finset.univ (q.Bop y)).symm, q.Bop_sum y, amp_one]

theorem norm_Bi_le [DecidableEq B] (y : Y) (b : B) : ‖q.Bi y b‖ ≤ 1 := by
  have h1 : ‖q.Bop y b‖ ≤ 1 :=
    norm_povm_le_one (fun b => q.Bop y b)
      (fun b => (ContinuousLinearMap.nonneg_iff_isPositive _).mp (q.Bop_nonneg y b))
      (q.Bop_sum y) b
  exact (norm_amp_le _).trans h1

theorem Bi_commute {z : L2Q q.K →L[ℂ] L2Q q.K} (hz : z ∈ crossed q.M q.Ω) (y : Y) (b : B) :
    Commute z (q.Bi y b) :=
  VonNeumannAlgebra.mem_commutant_iff.mp (q.Bi_mem_commutant y b) z hz

/-- The crossed product reproduces the correlation of `q`. -/
theorem inner_Ωh_Ai_Bi (x : X) (y : Y) (a : A) (b : B) :
    ⟪Ωh q.Ω, q.Ai x a (q.Bi y b (Ωh q.Ω))⟫_ℂ = ⟪q.Ω, q.Aop x a (q.Bop y b q.Ω)⟫_ℂ := by
  have hz : σ q.M q.Ω (-(((0 : ℚ) : ℝ))) (q.Aop x a) = q.Aop x a := by
    rw [show (-(((0 : ℚ) : ℝ))) = 0 by norm_num, σ_zero]
  rw [Bi_def, Ωh, amp_sgl, Ai_def, π_sgl, inner_sgl_sgl, if_pos rfl, hz]

end StdStrategy

/-! ## The tracial data at level `n` -/

namespace StdStrategy

section Level

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable (q : StdStrategy X Y A B) (n : ℕ)

theorem xin_eq : xin q.Ω n = expA (an (K := q.K) n) (-(1 / 2)) (Ωh q.Ω) := rfl

theorem norm_Ωh_eq_one : ‖Ωh q.Ω‖ = 1 := by rw [norm_Ωh, q.Ω_norm]

theorem norm_xin_pos : 0 < ‖xin q.Ω n‖ := by
  rw [norm_pos_iff]
  intro h0
  have h1 := expA_apply_expA_neg (isSelfAdjoint_an (K := q.K) n) (1 / 2) (Ωh q.Ω)
  rw [← xin_eq, h0, map_zero] at h1
  have h2 := q.norm_Ωh_eq_one
  rw [← h1] at h2
  simp at h2

/-- `⟪ξ_n, d_n ξ_n⟫ = 1`: the density `d_n` transports `ψ_{ξ_n}` back to the unit state. -/
theorem inner_xin_dn : ⟪xin q.Ω n, dn (K := q.K) n (xin q.Ω n)⟫_ℂ = 1 := by
  have h := inner_Ωh_eq_inner_xin_dn q.M q.Ω q.sep q.cyc n
    (one_mem (crossed q.M q.Ω) : (1 : L2Q q.K →L[ℂ] L2Q q.K) ∈ crossed q.M q.Ω)
  rw [mul_one] at h
  rw [← h, one_apply_eq_self, inner_self_eq_norm_sq_to_K, q.norm_Ωh_eq_one]
  norm_num

end Level

/-! ## The tracial approximation -/

set_option maxHeartbeats 4000000 in
/-- **Stage E7.3**: the correlation of a standard-form commuting strategy is entrywise
`η`-close to a tracially embeddable correlation. -/
theorem exists_tracial_approx {Xc Ac : Type} [Fintype Xc] [Fintype Ac] [Nonempty Ac]
    (q : StdStrategy Xc Xc Ac Ac) {η : ℝ} (hη : 0 < η) :
    ∃ t : TraciallyEmbeddableCorrelation Xc Ac,
      ∀ x y a b, |t.toCorrelation x y a b - q.corr x y a b| ≤ η := by
  classical
  -- (1) choose the Haagerup level `n` uniformly over Alice's finitely many effects
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ (x : Xc) (a : Ac),
      ‖Phi q.M q.Ω n (q.Ai x a) (Ωh q.Ω) - q.Ai x a (Ωh q.Ω)‖ < η := by
    refine Filter.Eventually.exists (f := atTop) ?_
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro a
    have h := tendsto_Phi_apply q.M q.Ω q.sep q.cyc (q.Ai_mem x a)
    exact (tendsto_iff_norm_sub_tendsto_zero.mp h).eventually (eventually_lt_nhds hη)
  -- (2) the tracial algebra `ℛ_n`
  have hcl : IsClosed
      ((Rn q.M q.Ω n : StarSubalgebra ℂ (L2Q q.K →L[ℂ] L2Q q.K)) :
        Set (L2Q q.K →L[ℂ] L2Q q.K)) := isClosed_Rn q.M q.Ω q.sep q.cyc n
  set 𝒞 := (Rn q.M q.Ω n : StarSubalgebra ℂ (L2Q q.K →L[ℂ] L2Q q.K)) with h𝒞
  set ξ := xin q.Ω n with hξdef
  have hzp : 0 < ‖ξ‖ := q.norm_xin_pos n
  have hz2 : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
  have hz2' : ‖ξ‖ ^ 2 ≠ 0 := ne_of_gt hz2
  -- (3) the tracial state
  set τ : ↥𝒞 →ₚ[ℂ] ℂ := subVecState 𝒞 (c := (‖ξ‖ ^ 2)⁻¹) (le_of_lt (by positivity)) ξ with hτdef
  have hτapp : ∀ z : ↥𝒞,
      τ z = (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ⟪ξ, (z : L2Q q.K →L[ℂ] L2Q q.K) ξ⟫_ℂ := fun z => rfl
  have hinner : ⟪ξ, ξ⟫_ℂ = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hτ1 : τ (1 : ↥𝒞) = 1 := by
    rw [hτapp]
    show (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ⟪ξ, (1 : L2Q q.K →L[ℂ] L2Q q.K) ξ⟫_ℂ = 1
    rw [one_apply_eq_self, hinner, ← Complex.ofReal_mul, inv_mul_cancel₀ hz2',
      Complex.ofReal_one]
  have hτcomm : ∀ z w : ↥𝒞, τ (z * w) = τ (w * z) := by
    intro z w
    rw [hτapp, hτapp]
    congr 1
    exact tracial_Rn q.M q.Ω q.sep q.cyc n z.2 w.2.1
  -- (4) the density `σ = ‖ξ‖ e^{a_n/2} = (√‖ξ‖ e^{a_n/4})²`
  have hb : ((Real.sqrt ‖ξ‖ : ℝ) : ℂ) • expA (an (K := q.K) n) (1 / 4) ∈ 𝒞 :=
    SMulMemClass.smul_mem _ (expA_an_mem_Rn q.M q.Ω q.sep q.cyc n (1 / 4))
  set bb : ↥𝒞 := ⟨((Real.sqrt ‖ξ‖ : ℝ) : ℂ) • expA (an (K := q.K) n) (1 / 4), hb⟩ with hbdef
  set sg : ↥𝒞 := star bb * bb with hsgdef
  have hsgsa : star sg = sg := by rw [hsgdef, star_mul, star_star]
  have hsan := isSelfAdjoint_an (K := q.K) n
  have hsgcoe : (sg : L2Q q.K →L[ℂ] L2Q q.K)
      = ((‖ξ‖ : ℝ) : ℂ) • expA (an (K := q.K) n) (1 / 2) := by
    show star (((Real.sqrt ‖ξ‖ : ℝ) : ℂ) • expA (an (K := q.K) n) (1 / 4)) *
      (((Real.sqrt ‖ξ‖ : ℝ) : ℂ) • expA (an (K := q.K) n) (1 / 4)) = _
    rw [star_smul, Complex.star_def, Complex.conj_ofReal,
      (expA_isSelfAdjoint (1 / 4 : ℝ)).star_eq, smul_mul_smul_comm, expA_mul hsan,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg _)]
    norm_num
  have hsgsq : ((sg * sg : ↥𝒞) : L2Q q.K →L[ℂ] L2Q q.K)
      = (((‖ξ‖ ^ 2 : ℝ)) : ℂ) • dn (K := q.K) n := by
    show (sg : L2Q q.K →L[ℂ] L2Q q.K) * (sg : L2Q q.K →L[ℂ] L2Q q.K) = _
    rw [hsgcoe, smul_mul_smul_comm, expA_mul hsan, dn]
    norm_num
    congr 1
    push_cast
    ring
  have hsg0 : 0 ≤ sg := star_mul_self_nonneg bb
  have hsg1 : τ (sg * sg) = 1 := by
    rw [hτapp, hsgsq, smul_apply, inner_smul_right, q.inner_xin_dn n,
      mul_one, ← Complex.ofReal_mul, inv_mul_cancel₀ hz2', Complex.ofReal_one]
  -- (5) Alice's POVM in `ℛ_n`
  set EE : Xc → Ac → ↥𝒞 := fun x a =>
    ⟨Phi q.M q.Ω n (q.Ai x a), Phi_mem_Rn q.M q.Ω q.sep q.cyc n (q.Ai_mem x a)⟩ with hEEdef
  have hEE0 : ∀ x a, 0 ≤ EE x a := fun x a =>
    (coe_nonneg_iff 𝒞 (EE x a)).mpr (Phi_nonneg q.M q.Ω n (q.Ai_nonneg x a))
  have hcoesum : ∀ (f : Ac → ↥𝒞),
      (((∑ a : Ac, f a) : ↥𝒞) : L2Q q.K →L[ℂ] L2Q q.K)
        = ∑ a : Ac, ((f a : ↥𝒞) : L2Q q.K →L[ℂ] L2Q q.K) := fun f =>
    map_sum (StarSubalgebra.subtype 𝒞) f Finset.univ
  have hEE1 : ∀ x, ∑ a : Ac, EE x a = 1 := by
    intro x
    refine Subtype.ext ?_
    rw [hcoesum]
    show (∑ a : Ac, Phi q.M q.Ω n (q.Ai x a)) = (1 : L2Q q.K →L[ℂ] L2Q q.K)
    rw [← Phi_finset_sum q.M q.Ω n Finset.univ (q.Ai x), q.Ai_sum x, Phi_one]
  -- (6) Bob's positive functionals
  have hBcom : ∀ (y : Xc) (b : Ac), ∀ z ∈ 𝒞, Commute z (q.Bi y b) := by
    intro y b z hz
    exact q.Bi_commute hz.1 y b
  set ω : Xc → Ac → ↥𝒞 →ₚ[ℂ] ℂ := fun y b =>
    subBobState 𝒞 (Ωh q.Ω) (q.Bi_nonneg y b) (hBcom y b) with hωdef
  have hωapp : ∀ y b (z : ↥𝒞),
      ω y b z = ⟪Ωh q.Ω, (z : L2Q q.K →L[ℂ] L2Q q.K) (q.Bi y b (Ωh q.Ω))⟫_ℂ :=
    fun y b z => rfl
  have hωsum : ∀ (y : Xc) (z : ↥𝒞), ∑ b : Ac, ω y b z = conjState τ sg z := by
    intro y z
    have hleft : ∑ b : Ac, ω y b z
        = ⟪Ωh q.Ω, (z : L2Q q.K →L[ℂ] L2Q q.K) (Ωh q.Ω)⟫_ℂ := by
      rw [Finset.sum_congr rfl fun b _ => hωapp y b z, ← inner_sum]
      congr 1
      rw [← map_sum]
      congr 1
      rw [← ContinuousLinearMap.sum_apply, q.Bi_sum y, one_apply_eq_self]
    have hright : conjState τ sg z = ⟪Ωh q.Ω, (z : L2Q q.K →L[ℂ] L2Q q.K) (Ωh q.Ω)⟫_ℂ := by
      rw [conjState_apply, hsgsa, hτcomm, mul_assoc, hτapp]
      have hmul : ((z * (sg * sg) : ↥𝒞) : L2Q q.K →L[ℂ] L2Q q.K)
          = (((‖ξ‖ ^ 2 : ℝ)) : ℂ) • ((z : L2Q q.K →L[ℂ] L2Q q.K) * dn (K := q.K) n) := by
        show (z : L2Q q.K →L[ℂ] L2Q q.K) * ((sg * sg : ↥𝒞) : L2Q q.K →L[ℂ] L2Q q.K) = _
        rw [hsgsq, mul_smul_comm]
      rw [hmul, smul_apply, inner_smul_right, ← mul_assoc,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hz2', Complex.ofReal_one, one_mul]
      rw [tracial_Rn q.M q.Ω q.sep q.cyc n z.2 (dn_mem q.M q.Ω n),
        ← inner_Ωh_eq_inner_xin_dn q.M q.Ω q.sep q.cyc n z.2.1]
    rw [hleft, hright]
  -- (7) package
  obtain ⟨t, ht⟩ := exists_traciallyEmbeddable (Xc := Xc) (Ac := Ac) τ sg hτ1
    (fun z w => hτcomm z w) hsg0 hsg1 EE hEE0 hEE1 ω hωsum
  refine ⟨t, fun x y a b => ?_⟩
  -- (8) the error bound
  rw [ht x y a b, hωapp]
  have hcomm1 : (EE x a : L2Q q.K →L[ℂ] L2Q q.K) (q.Bi y b (Ωh q.Ω))
      = q.Bi y b ((EE x a : L2Q q.K →L[ℂ] L2Q q.K) (Ωh q.Ω)) := by
    have h := (q.Bi_commute (EE x a).2.1 y b).eq
    have h2 := congrArg (fun T : L2Q q.K →L[ℂ] L2Q q.K => T (Ωh q.Ω)) h
    simpa only [ContinuousLinearMap.mul_apply] using h2
  have hcomm2 : q.Ai x a (q.Bi y b (Ωh q.Ω)) = q.Bi y b (q.Ai x a (Ωh q.Ω)) := by
    have h := (q.Bi_commute (q.Ai_mem x a) y b).eq
    have h2 := congrArg (fun T : L2Q q.K →L[ℂ] L2Q q.K => T (Ωh q.Ω)) h
    simpa only [ContinuousLinearMap.mul_apply] using h2
  have hcorr : q.corr x y a b
      = (⟪Ωh q.Ω, q.Bi y b (q.Ai x a (Ωh q.Ω))⟫_ℂ).re := by
    rw [StdStrategy.corr, ← q.inner_Ωh_Ai_Bi x y a b, hcomm2]
  rw [hcomm1, hcorr, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [← inner_sub_right, ← map_sub]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [q.norm_Ωh_eq_one, one_mul]
  refine ((q.Bi y b).le_opNorm _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) (q.norm_Bi_le y b)).trans ?_
  exact le_of_lt (hn x a)

end StdStrategy

end Density

end CommutingRepetition
