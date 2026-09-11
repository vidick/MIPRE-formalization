/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/CentralExp.lean
-/
/-
# Exponentials of central elements and the perturbed vector (density stage E6.2a)

For `a ∈ M` self-adjoint in the centralizer (`[a, R] = 0`): the exponentials `e^{ra}`, the
reflected element `a' = J a J ∈ M'`, the perturbed vector `ξ = e^{-a/2} Ω` (cyclic and
separating), the transport of the standard subspace `𝒦(M, ξ) = e^{-a'/2} 𝒦(M, Ω)`, and the
unitary groups `e^{itE}` with the factorization `e^{it(b-a)} = e^{itb} e^{-ita}` for commuting
`a, b` (via the joint Borel calculus).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.FourierConverse
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Smearing
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Uniqueness
import MIPRE.Background.Repetition.CommutingRepetition.VN.JointBorel

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open Filter Topology MeasureTheory BorelCalc ClosedSubmodule

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)
variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

/-! ## `J · J` as a real star-algebra homomorphism -/

theorem conjJm_real_smul (c : ℝ) (G : K →L[ℂ] K) : conjJm M Ω (c • G) = c • conjJm M Ω G := by
  rw [← Complex.coe_smul, conjJm_smul, Complex.conj_ofReal, Complex.coe_smul]

include hs hc in
theorem conjJm_isSelfAdjoint {E : K →L[ℂ] K} (hE : IsSelfAdjoint E) :
    IsSelfAdjoint (conjJm M Ω E) := by
  show star _ = _
  rw [star_conjJm M Ω hs hc, hE.star_eq]

include hs hc in
/-- `G ↦ J G J` as a unital real star-algebra homomorphism. -/
noncomputable def conjJmHom : (K →L[ℂ] K) →⋆ₐ[ℝ] (K →L[ℂ] K) where
  toFun := conjJm M Ω
  map_one' := conjJm_one M Ω hs hc
  map_mul' := conjJm_mul M Ω hs hc
  map_zero' := conjJm_zero M Ω
  map_add' := conjJm_add M Ω
  commutes' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, conjJm_real_smul, conjJm_one M Ω hs hc]
  map_star' := fun G => (star_conjJm M Ω hs hc G).symm

theorem conjJmHom_apply (G : K →L[ℂ] K) : conjJmHom M Ω hs hc G = conjJm M Ω G := rfl

theorem continuous_conjJmHom : Continuous (conjJmHom M Ω hs hc) :=
  AddMonoidHomClass.continuous_of_bound (conjJmHom M Ω hs hc) 1 fun G => by
    rw [one_mul]; exact norm_conjJm_le M Ω hs hc G

include hs hc in
/-- `J f(E) J = f(J E J)` for continuous real `f`. -/
theorem conjJm_cfc {E : K →L[ℂ] K} (hE : IsSelfAdjoint E) {f : ℝ → ℝ} (hf : Continuous f) :
    conjJm M Ω (cfc f E) = cfc f (conjJm M Ω E) :=
  (conjJmHom M Ω hs hc).map_cfc f E hf.continuousOn (continuous_conjJmHom M Ω hs hc) hE
    (conjJm_isSelfAdjoint M Ω hs hc hE)

include hs hc in
theorem conjJm_commute {G H : K →L[ℂ] K} (h : Commute G H) :
    Commute (conjJm M Ω G) (conjJm M Ω H) := by
  rw [Commute, SemiconjBy, ← conjJm_mul M Ω hs hc, ← conjJm_mul M Ω hs hc, h.eq]

include hs hc in
theorem conjJm_R : conjJm M Ω (R M Ω) = 2 - R M Ω := by
  ext ξ
  rw [conjJm_apply, Jm_R M Ω hs hc, Jm_Jm M Ω hs hc]

include hs hc in
/-- `J a J` commutes with `R` when `a` does. -/
theorem commute_conjJm_R {a : K →L[ℂ] K} (h : Commute a (R M Ω)) :
    Commute (conjJm M Ω a) (R M Ω) := by
  have h1 : Commute (conjJm M Ω a) (2 - R M Ω) := by
    rw [← conjJm_R M Ω hs hc]; exact conjJm_commute M Ω hs hc h
  have h2 : Commute (conjJm M Ω a) (2 : K →L[ℂ] K) := Commute.ofNat_right _ 2
  have := h2.sub_right h1
  rwa [sub_sub_cancel] at this

include hs hc in
theorem Jm_conjJm_apply (G : K →L[ℂ] K) (ξ : K) :
    Jm M Ω (conjJm M Ω G ξ) = G (Jm M Ω ξ) := by
  rw [conjJm_apply, Jm_Jm M Ω hs hc]

/-! ## Exponentials of a self-adjoint operator -/

/-- `e^{r E}` for a self-adjoint `E`. -/
noncomputable def expA (E : K →L[ℂ] K) (r : ℝ) : K →L[ℂ] K :=
  cfc (fun l : ℝ => Real.exp (r * l)) E

section expA

variable {E : K →L[ℂ] K} (hE : IsSelfAdjoint E)

theorem expA_isSelfAdjoint (r : ℝ) : IsSelfAdjoint (expA E r) := cfc_predicate _ _

include hE in
theorem expA_mul (r s : ℝ) : expA E r * expA E s = expA E (r + s) := by
  unfold expA
  rw [← cfc_mul (fun l : ℝ => Real.exp (r * l)) (fun l : ℝ => Real.exp (s * l)) E]
  congr 1
  funext l
  rw [← Real.exp_add]
  ring_nf

include hE in
theorem expA_zero : expA E 0 = 1 := by
  unfold expA
  have : (fun l : ℝ => Real.exp (0 * l)) = 1 := by funext l; simp
  rw [this, cfc_one ℝ E]

include hE in
theorem expA_mul_neg (r : ℝ) : expA E r * expA E (-r) = 1 := by
  rw [expA_mul hE, add_neg_cancel, expA_zero hE]

include hE in
theorem expA_neg_mul (r : ℝ) : expA E (-r) * expA E r = 1 := by
  rw [expA_mul hE, neg_add_cancel, expA_zero hE]

include hE in
theorem expA_comm (r s : ℝ) : expA E r * expA E s = expA E s * expA E r := by
  rw [expA_mul hE, expA_mul hE, add_comm]

include hE in
theorem expA_apply_expA_neg (r : ℝ) (ξ : K) : expA E r (expA E (-r) ξ) = ξ := by
  rw [← mul_apply_eq_comp, expA_mul_neg hE, one_apply_eq_self]

include hE in
theorem expA_neg_apply_expA (r : ℝ) (ξ : K) : expA E (-r) (expA E r ξ) = ξ := by
  rw [← mul_apply_eq_comp, expA_neg_mul hE, one_apply_eq_self]

theorem expA_real_smul (E : K →L[ℂ] K) (r c : ℝ) (x : K) :
    expA E r (c • x) = c • expA E r x := by
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul]

theorem expA_mem (N : VonNeumannAlgebra K) (hEN : E ∈ N) (r : ℝ) : expA E r ∈ N :=
  VN.cfc_real_mem N hEN _

theorem commute_expA {T : K →L[ℂ] K} (h : Commute E T) (r : ℝ) : Commute (expA E r) T :=
  h.cfc_real _

end expA

/-! ## The reflected element `a' = J a J` -/

section Central

variable {a : K →L[ℂ] K} (ha : a ∈ M) (hsa : IsSelfAdjoint a) (haR : Commute a (R M Ω))

include hs hc hsa in
theorem conjJm_expA (r : ℝ) : conjJm M Ω (expA a r) = expA (conjJm M Ω a) r :=
  conjJm_cfc M Ω hs hc hsa (by fun_prop)

include hs hc hsa in
theorem Jm_expA_conjJm (r : ℝ) (ξ : K) :
    Jm M Ω (expA (conjJm M Ω a) r ξ) = expA a r (Jm M Ω ξ) := by
  rw [← conjJm_expA M Ω hs hc hsa, Jm_conjJm_apply M Ω hs hc]

include hs hc ha in
theorem expA_conjJm_mem_commutant (r : ℝ) : expA (conjJm M Ω a) r ∈ M.commutant :=
  expA_mem M.commutant (conjJm_mem_commutant M Ω hs hc ha) r

include hs hc ha in
theorem commute_expA_expA_conjJm (r s : ℝ) :
    Commute (expA a r) (expA (conjJm M Ω a) s) :=
  VonNeumannAlgebra.mem_commutant_iff.mp (expA_conjJm_mem_commutant M Ω hs hc ha s) _
    (expA_mem M ha r)

include haR in
theorem commute_expA_R (r : ℝ) : Commute (expA a r) (R M Ω) := commute_expA haR r

include haR in
theorem commute_expA_Tm (r : ℝ) : Commute (expA a r) (Tm M Ω) := by
  unfold Tm
  exact ((commute_expA haR r).symm.cfc_real gT).symm

include hs hc haR in
theorem commute_expA_conjJm_R (r : ℝ) : Commute (expA (conjJm M Ω a) r) (R M Ω) :=
  commute_expA (commute_conjJm_R M Ω hs hc haR) r

include hs hc haR in
theorem commute_expA_conjJm_Tm (r : ℝ) : Commute (expA (conjJm M Ω a) r) (Tm M Ω) := by
  unfold Tm
  exact ((commute_expA_conjJm_R M Ω hs hc haR r).symm.cfc_real gT).symm

/-! ## The perturbed vector `ξ = e^{-a/2} Ω` -/

include hs hc in
/-- On `𝒦`, `R k = k` forces `J k = k`. -/
theorem Jm_eq_self_of_R_eq {k : K} (hk : k ∈ Kre M Ω) (hR : R M Ω k = k) : Jm M Ω k = k := by
  have h1 : Am M Ω k = k := by
    have := two_smul_Pre M Ω k
    rw [Pre_eq_self M Ω hk, hR, two_smul] at this
    exact (add_left_cancel this).symm
  have h2 : Tm M Ω k = k := by
    rw [Tm_eq_bfc, bfc_eigen _ _ bdd_gT (c := 1) (by rw [hR]; simp), gT_one]
    simp
  have h3 : Tm M Ω (Jm M Ω k - k) = 0 := by
    rw [map_sub, Tm_Jm M Ω hs hc, h1, h2, sub_self]
  exact sub_eq_zero.mp ((Tm_eq_zero_iff M Ω hs hc).mp h3)

/-- The perturbed vector `e^{-a/2} Ω`. -/
noncomputable def pvec (a : K →L[ℂ] K) : K := expA a (-(1 / 2)) Ω

include hs hc ha hsa haR in
theorem expA_Ω_eq_conjJm (r : ℝ) : expA (conjJm M Ω a) r Ω = expA a r Ω := by
  have hk : expA a r Ω ∈ Kre M Ω :=
    mem_Kre_of_sa M Ω (expA_mem M ha r) (expA_isSelfAdjoint r)
  have hR : R M Ω (expA a r Ω) = expA a r Ω := by
    rw [← mul_apply_eq_comp, ← (commute_expA_R M Ω haR r).eq, mul_apply_eq_comp, R_Ω]
  have hJv : Jm M Ω (expA (conjJm M Ω a) r Ω) = expA a r Ω := by
    rw [Jm_expA_conjJm M Ω hs hc hsa, Jm_Ω M Ω hs hc]
  calc expA (conjJm M Ω a) r Ω
      = Jm M Ω (Jm M Ω (expA (conjJm M Ω a) r Ω)) := (Jm_Jm M Ω hs hc _).symm
    _ = Jm M Ω (expA a r Ω) := by rw [hJv]
    _ = expA a r Ω := Jm_eq_self_of_R_eq M Ω hs hc hk hR

include hs hc ha hsa haR in
theorem pvec_eq_conjJm : expA (conjJm M Ω a) (-(1 / 2)) Ω = pvec Ω a :=
  expA_Ω_eq_conjJm M Ω hs hc ha hsa haR _

include hc ha hsa in
theorem isCyclic_pvec : IsCyclic (M : Set (K →L[ℂ] K)) (pvec Ω a) := by
  refine Dense.mono ?_ hc
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨y, hy, rfl⟩
  show y Ω ∈ (orbit (M : Set (K →L[ℂ] K)) (pvec Ω a) : Set K)
  have : y Ω = (y * expA a (1 / 2)) (pvec Ω a) := by
    rw [mul_apply_eq_comp, pvec, expA_apply_expA_neg hsa]
  rw [this]
  exact apply_mem_orbit (mul_mem hy (expA_mem M ha _))

include hs ha hsa in
theorem isSeparating_pvec : IsSeparating (M : Set (K →L[ℂ] K)) (pvec Ω a) := by
  intro y hy h
  have h1 : (y * expA a (-(1 / 2))) Ω = 0 := by rwa [mul_apply_eq_comp]
  have h2 := hs _ (mul_mem hy (expA_mem M ha _)) h1
  calc y = y * expA a (-(1 / 2)) * expA a (1 / 2) := by
        rw [mul_assoc, expA_neg_mul hsa, mul_one]
    _ = 0 := by rw [h2, zero_mul]

/-! ## Transport of the standard subspace: `𝒦(M, ξ) = e^{-a'/2} 𝒦(M, Ω)` -/

include hs hc ha hsa haR in
/-- `e^{-a'/2} 𝒦(M, Ω) ⊆ 𝒦(M, ξ)`. -/
theorem expA_conjJm_mem_Kre_pvec {k : K} (hk : k ∈ Kre M Ω) :
    expA (conjJm M Ω a) (-(1 / 2)) k ∈ Kre M (pvec Ω a) := by
  refine Kre_induction M Ω (p := fun k => expA (conjJm M Ω a) (-(1 / 2)) k ∈ Kre M (pvec Ω a))
    ?_ ?_ ?_ ?_ ?_ hk
  · exact (Kre M (pvec Ω a)).isClosed.preimage (expA _ _).continuous
  · simp only [map_zero]; exact zero_mem _
  · intro x y hx hy; simp only [map_add]; exact add_mem hx hy
  · intro c x hx; rw [expA_real_smul]; exact SMulMemClass.smul_mem c hx
  · intro y hy hys
    have : expA (conjJm M Ω a) (-(1 / 2)) (y Ω) = y (pvec Ω a) := by
      rw [← pvec_eq_conjJm M Ω hs hc ha hsa haR, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
        (VonNeumannAlgebra.mem_commutant_iff.mp (expA_conjJm_mem_commutant M Ω hs hc ha _) y hy)]
    rw [this]
    exact mem_Kre_of_sa M _ hy hys

include hs hc ha hsa haR in
/-- `e^{a'/2} 𝒦(M, ξ) ⊆ 𝒦(M, Ω)`. -/
theorem expA_conjJm_mem_Kre_of_mem_Kre_pvec {η : K} (hη : η ∈ Kre M (pvec Ω a)) :
    expA (conjJm M Ω a) (1 / 2) η ∈ Kre M Ω := by
  refine Kre_induction M (pvec Ω a) (p := fun η => expA (conjJm M Ω a) (1 / 2) η ∈ Kre M Ω)
    ?_ ?_ ?_ ?_ ?_ hη
  · exact (Kre M Ω).isClosed.preimage (expA _ _).continuous
  · simp only [map_zero]; exact zero_mem _
  · intro x y hx hy; simp only [map_add]; exact add_mem hx hy
  · intro c x hx; rw [expA_real_smul]; exact SMulMemClass.smul_mem c hx
  · intro y hy hys
    have : expA (conjJm M Ω a) (1 / 2) (y (pvec Ω a)) = y Ω := by
      rw [← pvec_eq_conjJm M Ω hs hc ha hsa haR, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
        ← (VonNeumannAlgebra.mem_commutant_iff.mp (expA_conjJm_mem_commutant M Ω hs hc ha _) y hy),
        mul_apply_eq_comp, mul_apply_eq_comp,
        show (1 : ℝ) / 2 = -(-(1 / 2)) by norm_num,
        expA_apply_expA_neg (conjJm_isSelfAdjoint M Ω hs hc hsa)]
    rw [this]
    exact mem_Kre_of_sa M Ω hy hys

include hs hc ha hsa haR in
/-- `e^{-a'/2} 𝒦(M, ξ)ᗮ ⊆ 𝒦(M, Ω)ᗮ`. -/
theorem expA_conjJm_mem_orthogonal {η : K} (hη : η ∈ ((Kre M (pvec Ω a)).toSubmodule)ᗮ) :
    expA (conjJm M Ω a) (-(1 / 2)) η ∈ ((Kre M Ω).toSubmodule)ᗮ := by
  rw [Submodule.mem_orthogonal] at hη ⊢
  intro k hk
  have hk' : k ∈ Kre M Ω := hk
  have hsa' : IsSelfAdjoint (expA (conjJm M Ω a) (-(1 / 2))) := expA_isSelfAdjoint _
  rw [inner_real_eq_re_inner, BorelCalc.inner_sa hsa', ← inner_real_eq_re_inner]
  exact hη _ (expA_conjJm_mem_Kre_pvec M Ω hs hc ha hsa haR hk')

end Central

/-! ## Unitary groups and the factorization `e^{it(b-a)} = e^{itb} e^{-ita}` -/

section UnitaryGroup

variable {E : K →L[ℂ] K} (hE : IsSelfAdjoint E)

/-- The function `l ↦ e^{itl}`. -/
noncomputable def eitf (t l : ℝ) : ℂ := Complex.exp (((t * l : ℝ) : ℂ) * Complex.I)

theorem norm_eitf (t l : ℝ) : ‖eitf t l‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_eitf (t : ℝ) : Continuous (eitf t) := by unfold eitf; fun_prop

theorem cbdd_eitf (t : ℝ) : CBdd (eitf t) :=
  ⟨(continuous_eitf t).measurable, 1, fun l => (norm_eitf t l).le⟩


theorem eitf_add (s t l : ℝ) : eitf (s + t) l = eitf s l * eitf t l := by
  unfold eitf
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eitf_zero (l : ℝ) : eitf 0 l = 1 := by simp [eitf]

theorem eitf_sub_arg (t u v : ℝ) : eitf t (v - u) = eitf t v * eitf (-t) u := by
  unfold eitf
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The unitary group `e^{itE}`. -/
noncomputable def eit (E : K →L[ℂ] K) (hE : IsSelfAdjoint E) (t : ℝ) : K →L[ℂ] K :=
  cbfc E hE (eitf t)

include hE in
theorem eit_add (s t : ℝ) : eit E hE (s + t) = eit E hE s * eit E hE t := by
  unfold eit
  rw [← cbfc_mul E hE (cbdd_eitf s) (cbdd_eitf t)]
  congr 1
  funext l
  exact eitf_add s t l

include hE in
theorem eit_zero : eit E hE 0 = 1 := by
  unfold eit
  have : eitf 0 = fun _ => (1 : ℂ) := funext eitf_zero
  rw [this, cbfc_one]

include hE in
theorem eit_mul_neg (t : ℝ) : eit E hE t * eit E hE (-t) = 1 := by
  rw [← eit_add hE, add_neg_cancel, eit_zero hE]

include hE in
theorem eit_neg_mul (t : ℝ) : eit E hE (-t) * eit E hE t = 1 := by
  rw [← eit_add hE, neg_add_cancel, eit_zero hE]

include hE in
theorem eit_comm (s t : ℝ) : eit E hE s * eit E hE t = eit E hE t * eit E hE s := by
  rw [← eit_add hE, ← eit_add hE, add_comm]

include hE in
theorem eit_star (t : ℝ) : star (eit E hE t) = eit E hE (-t) := by
  unfold eit
  rw [cbfc_star E hE (cbdd_eitf t)]
  congr 1
  funext l
  unfold eitf
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem eit_mem (N : VonNeumannAlgebra K) (hEN : E ∈ N) (t : ℝ) : eit E hE t ∈ N :=
  cbfc_mem E hE N hEN (cbdd_eitf t)

theorem commute_eit {T : K →L[ℂ] K} (h : Commute E T) (t : ℝ) : Commute (eit E hE t) T :=
  (commute_cbfc E hE h (cbdd_eitf t))

/-- `cbfc` only sees the spectral measures. -/
theorem cbfc_congr_ae {G H : ℝ → ℂ} (hG : CBdd G) (hH : CBdd H)
    (h : ∀ ξ, G =ᵐ[ν E hE ξ] H) : cbfc E hE G = cbfc E hE H := by
  ext ξ
  rw [← sub_eq_zero, ← _root_.sub_apply, ← cbfc_sub E hE hG hH, ← norm_eq_zero,
    ← pow_eq_zero_iff (two_ne_zero : (2 : ℕ) ≠ 0), norm_sq_cbfc E hE (hG.sub hH)]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h ξ] with t ht
  simp [Pi.sub_apply, ht]

/-- A continuous bounded function may be truncated: `cbfc E (G ∘ trunc E) = cbfc E G`. -/
theorem cbfc_comp_trunc {G : ℝ → ℂ} (hG : CBdd G) (hGc : Continuous G) :
    cbfc E hE (fun l => G (trunc E l)) = cbfc E hE G := by
  refine cbfc_congr_ae hE ⟨hGc.measurable.comp (continuous_trunc E).measurable, ?_⟩ hG
    fun ξ => ?_
  · obtain ⟨C, hC⟩ := hG.2
    exact ⟨C, fun l => hC _⟩
  · filter_upwards [ae_norm_le E hE ξ] with l hl
    exact congrArg G (trunc_of_mem E (abs_le.mp hl))

end UnitaryGroup

/-! ## Clamped representatives of exponentials

`clamp`, `continuous_clamp`, `abs_clamp_le`, `bdd_clamp` and `clamp_eq_of_abs_le` come from
`VN/Modular/LinearRN.lean`. -/

theorem trunc_eq_clamp (E : K →L[ℂ] K) : trunc E = clamp ‖E‖ := rfl

theorem abs_le_of_mem_spectrum {E : K →L[ℂ] K} {l : ℝ} (hl : l ∈ spectrum ℝ E) : |l| ≤ ‖E‖ :=
  abs_le.mpr (spectrum_subset_Icc_norm E hl)

theorem bfc_clamp {E : K →L[ℂ] K} (hE : IsSelfAdjoint E) {C : ℝ} (hC : ‖E‖ ≤ C) :
    bfc E hE (clamp C) = E := by
  have hC0 : 0 ≤ C := (norm_nonneg E).trans hC
  rw [bfc_cfc E hE (bdd_clamp hC0) (continuous_clamp C)]
  have : (spectrum ℝ E).EqOn (clamp C) id := fun l hl =>
    clamp_eq_of_abs_le ((abs_le_of_mem_spectrum hl).trans hC)
  rw [cfc_congr this, cfc_id ℝ E]

/-- `l ↦ e^{r·clamp C l}` is a bounded Borel function. -/
theorem continuous_exp_clamp (r C : ℝ) : Continuous fun l => Real.exp (r * clamp C l) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_clamp C))

theorem bdd_exp_clamp (r : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    Bdd fun l => Real.exp (r * clamp C l) := by
  refine Bdd.of_continuous (continuous_exp_clamp r C) (C := Real.exp (|r| * C)) fun l => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc r * clamp C l ≤ |r * clamp C l| := le_abs_self _
    _ = |r| * |clamp C l| := abs_mul r _
    _ ≤ |r| * C := by
        exact mul_le_mul_of_nonneg_left (abs_clamp_le hC l) (abs_nonneg r)

/-- The clamped representative of `e^{rE}` in the bounded Borel calculus. -/
theorem expA_eq_bfc {E : K →L[ℂ] K} (hE : IsSelfAdjoint E) {C : ℝ} (hC : ‖E‖ ≤ C) (r : ℝ) :
    expA E r = bfc E hE (fun l => Real.exp (r * clamp C l)) := by
  have hC0 : 0 ≤ C := (norm_nonneg E).trans hC
  rw [bfc_cfc E hE (bdd_exp_clamp r hC0) (continuous_exp_clamp r C)]
  refine cfc_congr fun l hl => ?_
  rw [clamp_eq_of_abs_le ((abs_le_of_mem_spectrum hl).trans hC)]

section Pair

variable {a b : K →L[ℂ] K} (hsa : IsSelfAdjoint a) (hsb : IsSelfAdjoint b) (hab : Commute a b)

include hsa hsb hab in
/-- `b − a` as a joint Borel function of the commuting pair `(a, b)`. -/
theorem sub_eq_jbfc :
    b - a = jbfc a b hsa hsb hab (fun p => trunc b p.2 - trunc a p.1) := by
  have h1 : (fun p : ℝ × ℝ => trunc b p.2 - trunc a p.1) =
      (fun p : ℝ × ℝ => trunc b p.2) - fun p => trunc a p.1 := rfl
  rw [h1, jbfc_sub a b hsa hsb hab (Bdd2.comp_snd (bdd_trunc b)) (Bdd2.comp_fst (bdd_trunc a)),
    jbfc_fst a b hsa hsb hab (bdd_trunc a), jbfc_snd a b hsa hsb hab (bdd_trunc b), bfc_trunc,
    bfc_trunc]

theorem bdd2_sub_trunc : Bdd2 fun p : ℝ × ℝ => trunc b p.2 - trunc a p.1 :=
  (Bdd2.comp_snd (bdd_trunc b)).sub (Bdd2.comp_fst (bdd_trunc a))

theorem continuous_sub_trunc : Continuous fun p : ℝ × ℝ => trunc b p.2 - trunc a p.1 :=
  ((continuous_trunc b).comp continuous_snd).sub ((continuous_trunc a).comp continuous_fst)

theorem cbdd_eitf_trunc (E : K →L[ℂ] K) (t : ℝ) : CBdd fun l => eitf t (trunc E l) :=
  ⟨((continuous_eitf t).comp (continuous_trunc E)).measurable, 1, fun _ => (norm_eitf _ _).le⟩

include hsa hsb hab in
/-- `e^{it(b − a)} = e^{itb} e^{−ita}` for commuting self-adjoint `a`, `b`. -/
theorem eit_sub (t : ℝ) :
    eit (b - a) (hsb.sub hsa) t = eit b hsb t * eit a hsa (-t) := by
  unfold eit
  rw [cbfc_congr_op (sub_eq_jbfc hsa hsb hab) (hsb.sub hsa)
    (jbfc_isSelfAdjoint a b hsa hsb hab bdd2_sub_trunc) (eitf t),
    cbfc_jbfc a b hsa hsb hab bdd2_sub_trunc continuous_sub_trunc (cbdd_eitf t)]
  have e : (fun p : ℝ × ℝ => eitf t (trunc b p.2 - trunc a p.1)) =
      (fun p : ℝ × ℝ => eitf t (trunc b p.2)) * fun p => eitf (-t) (trunc a p.1) := by
    funext p
    exact eitf_sub_arg t _ _
  rw [e, cjbfc_mul a b hsa hsb hab (CBdd2.comp_snd (cbdd_eitf_trunc b t))
    (CBdd2.comp_fst (cbdd_eitf_trunc a (-t))),
    cjbfc_snd a b hsa hsb hab (cbdd_eitf_trunc b t),
    cjbfc_fst a b hsa hsb hab (cbdd_eitf_trunc a (-t)),
    cbfc_comp_trunc hsb (cbdd_eitf t) (continuous_eitf t),
    cbfc_comp_trunc hsa (cbdd_eitf (-t)) (continuous_eitf (-t))]


/-! ### The product rule for exponentials of a commuting pair -/

section ClampPair

variable {C : ℝ} (hCa : ‖a‖ ≤ C) (hCb : ‖b‖ ≤ C)

include hCa in
theorem clamp_nonneg_of_le : 0 ≤ C := (norm_nonneg a).trans hCa

include hCa in
theorem bdd2_clamp_sub : Bdd2 fun p : ℝ × ℝ => clamp C p.2 - clamp C p.1 :=
  (Bdd2.comp_snd (bdd_clamp (clamp_nonneg_of_le hCa))).sub
    (Bdd2.comp_fst (bdd_clamp (clamp_nonneg_of_le hCa)))

theorem continuous_clamp_sub : Continuous fun p : ℝ × ℝ => clamp C p.2 - clamp C p.1 :=
  ((continuous_clamp C).comp continuous_snd).sub ((continuous_clamp C).comp continuous_fst)

include hCa in
theorem abs_clamp_sub_le (p : ℝ × ℝ) : |clamp C p.2 - clamp C p.1| ≤ 2 * C := by
  have h0 := clamp_nonneg_of_le (a := a) hCa
  have h1 := abs_clamp_le h0 p.1
  have h2 := abs_clamp_le h0 p.2
  calc |clamp C p.2 - clamp C p.1| ≤ |clamp C p.2| + |clamp C p.1| := abs_sub _ _
    _ ≤ 2 * C := by linarith

include hsa hsb hab hCa hCb in
/-- `b − a` as a joint Borel function of the commuting pair `(a, b)`, with a common clamp. -/
theorem sub_eq_jbfc_clamp :
    b - a = jbfc a b hsa hsb hab (fun p => clamp C p.2 - clamp C p.1) := by
  have h1 : (fun p : ℝ × ℝ => clamp C p.2 - clamp C p.1) =
      (fun p : ℝ × ℝ => clamp C p.2) - fun p => clamp C p.1 := rfl
  have h0 := clamp_nonneg_of_le (a := a) hCa
  rw [h1, jbfc_sub a b hsa hsb hab (Bdd2.comp_snd (bdd_clamp h0)) (Bdd2.comp_fst (bdd_clamp h0)),
    jbfc_fst a b hsa hsb hab (bdd_clamp h0), jbfc_snd a b hsa hsb hab (bdd_clamp h0),
    bfc_clamp hsa hCa, bfc_clamp hsb hCb]

include hsa hsb hab hCa hCb in
/-- `e^{r(b − a)} = e^{rb} e^{−ra}` for commuting self-adjoint `a`, `b`. -/
theorem expA_sub (r : ℝ) : expA (b - a) r = expA b r * expA a (-r) := by
  have h0 := clamp_nonneg_of_le (a := a) hCa
  have h2C : (0:ℝ) ≤ 2 * C := by linarith
  have hsub : ‖b - a‖ ≤ 2 * C := (norm_sub_le b a).trans (by linarith)
  have hF := bdd2_clamp_sub (a := a) (C := C) hCa
  have hsaj : IsSelfAdjoint (jbfc a b hsa hsb hab (fun p => clamp C p.2 - clamp C p.1)) :=
    jbfc_isSelfAdjoint a b hsa hsb hab hF
  have e1 : expA (b - a) r = bfc (jbfc a b hsa hsb hab (fun p => clamp C p.2 - clamp C p.1)) hsaj
      (fun l => Real.exp (r * clamp (2 * C) l)) := by
    rw [expA_eq_bfc (hsb.sub hsa) hsub r]
    exact bfc_congr_op (sub_eq_jbfc_clamp hsa hsb hab hCa hCb) (hsb.sub hsa) hsaj _
  have e2 : bfc (jbfc a b hsa hsb hab (fun p => clamp C p.2 - clamp C p.1)) hsaj
      (fun l => Real.exp (r * clamp (2 * C) l)) =
      jbfc a b hsa hsb hab
        (fun p => Real.exp (r * clamp (2 * C) (clamp C p.2 - clamp C p.1))) :=
    bfc_jbfc a b hsa hsb hab hF (continuous_clamp_sub (C := C)) (bdd_exp_clamp r h2C)
  have e3 : (fun p : ℝ × ℝ => Real.exp (r * clamp (2 * C) (clamp C p.2 - clamp C p.1))) =
      (fun p : ℝ × ℝ => Real.exp (r * clamp C p.2)) *
        fun p : ℝ × ℝ => Real.exp (-r * clamp C p.1) := by
    funext p
    rw [clamp_eq_of_abs_le (abs_clamp_sub_le (a := a) hCa p)]
    show Real.exp (r * (clamp C p.2 - clamp C p.1)) =
      Real.exp (r * clamp C p.2) * Real.exp (-r * clamp C p.1)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e1, e2, e3, jbfc_mul a b hsa hsb hab (Bdd2.comp_snd (bdd_exp_clamp r h0))
      (Bdd2.comp_fst (bdd_exp_clamp (-r) h0)),
    jbfc_snd a b hsa hsb hab (bdd_exp_clamp r h0),
    jbfc_fst a b hsa hsb hab (bdd_exp_clamp (-r) h0),
    ← expA_eq_bfc hsb hCb, ← expA_eq_bfc hsa hCa]

end ClampPair

end Pair

end Modular

end VN

end CommutingRepetition
