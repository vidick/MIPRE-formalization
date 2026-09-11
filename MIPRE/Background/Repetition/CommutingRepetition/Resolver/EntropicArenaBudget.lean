/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/EntropicArenaBudget.lean
-/
/-
# The entropic resolver arena: the entropy budgets (node 1.2.6, proof layer)

The two telescoped budgets of `resolver_arena_entropic` for the arena of
`Resolver/EntropicArena.lean`, from the abstract budget of
`Resolver/EntropicBudget.lean`:

* the squared branch increments are the values of the vector states
  `ω_j(C) = ⟪ξ, C ξ⟫`, `ξ = L(σ) √(L Gⱼ) Ω` (Alice) and `ω_i(C) = ⟪ζ, C ζ⟫`,
  `ζ = L(σ*) √(L Fᵢ) Ω` (Bob), on the polarized kernels — the trace
  computation of eq random-martingale-increment through the corner copy,
  with the vector-state form of eq positive-functional obtained from the
  traciality of the trace-vector state on `vnAlg M`;
* the masses `ω_j(1) = re τ(σ* σ Gⱼ) ≤ τ(σ* σ) = 1` and
  `ω_i(1) = re τ(σ* Fᵢ σ) ≤ 1` (the contraction hypotheses);
* the martingale tower condition transports along `L`.

Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.EntropicArena
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.EntropicBudget

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace EntropicArena

noncomputable section

open scoped BigOperators InnerProductSpace
open StdTracialAlgebra Resolver Block

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

variable (M : StdTracialAlgebra.{0})

/-! ## Vector states -/

/-- The vector state `C ↦ re ⟪ξ, C ξ⟫` as a real-linear functional. -/
def vecState (ξ : M.H) : (M.H →L[ℂ] M.H) →ₗ[ℝ] ℝ where
  toFun C := (⟪ξ, C ξ⟫_ℂ).re
  map_add' C C' := by
    show (⟪ξ, (C + C') ξ⟫_ℂ).re = (⟪ξ, C ξ⟫_ℂ).re + (⟪ξ, C' ξ⟫_ℂ).re
    rw [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' r C := by
    show (⟪ξ, (r • C) ξ⟫_ℂ).re = r * (⟪ξ, C ξ⟫_ℂ).re
    rw [ContinuousLinearMap.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    exact RCLike.re_ofReal_mul (K := ℂ) r _

theorem vecState_apply (ξ : M.H) (C : M.H →L[ℂ] M.H) : vecState M ξ C = (⟪ξ, C ξ⟫_ℂ).re := rfl

theorem vecState_mono (ξ : M.H) {C C' : M.H →L[ℂ] M.H} (hCC : C ≤ C') :
    vecState M ξ C ≤ vecState M ξ C' := by
  have h := Douglas.re_inner_nonneg_of_nonneg (sub_nonneg.mpr hCC) ξ
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at h
  simp only [vecState_apply]
  linarith

theorem sqrt_mem_vnAlg {P : M.H →L[ℂ] M.H} (hP0 : 0 ≤ P) (hP : P ∈ M.vnAlg) :
    CFC.sqrt P ∈ M.vnAlg := by
  rw [CFC.sqrt_eq_real_sqrt _ hP0, cfcₙ_eq_cfc (hf0 := by simp)]
  exact cfc_mem (𝕜' := ℂ) (hs := M.isClosed_vnAlg) Real.sqrt hP

theorem sqrt_sa {P : M.H →L[ℂ] M.H} : IsSelfAdjoint (CFC.sqrt P) := by
  have h0 : 0 ≤ CFC.sqrt P := CFC.sqrt_nonneg _
  exact IsSelfAdjoint.of_nonneg h0

/-- **Alice's vector-state form of the positive functional**:
`φ(L(σ*) C L(σ) P) = ⟪ξ, C ξ⟫` with `ξ = L(σ) √P Ω`. -/
theorem traceState_conj_eq_inner (σ : M.A) {C P : M.H →L[ℂ] M.H} (hC : C ∈ M.vnAlg)
    (hP : P ∈ M.vnAlg) (hP0 : 0 ≤ P) :
    M.traceState (M.L (star σ) * C * M.L σ * P)
      = ⟪M.L σ (CFC.sqrt P M.traceVector), C (M.L σ (CFC.sqrt P M.traceVector))⟫_ℂ := by
  have hsq : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP0
  have hmem : CFC.sqrt P ∈ M.vnAlg := sqrt_mem_vnAlg M hP0 hP
  have hmem' : M.L (star σ) * C * M.L σ * CFC.sqrt P ∈ M.vnAlg :=
    mul_mem (mul_mem (mul_mem (M.L_mem_vnAlg _) hC) (M.L_mem_vnAlg _)) hmem
  have e : M.L (star σ) * C * M.L σ * P
      = (M.L (star σ) * C * M.L σ * CFC.sqrt P) * CFC.sqrt P := by
    rw [mul_assoc (M.L (star σ) * C * M.L σ) (CFC.sqrt P) (CFC.sqrt P), hsq]
  rw [e, M.traceState_mul_comm_vn hmem' hmem]
  unfold StdTracialAlgebra.traceState
  rw [show (CFC.sqrt P * (M.L (star σ) * C * M.L σ * CFC.sqrt P)) M.traceVector
      = CFC.sqrt P (M.L (star σ) (C (M.L σ (CFC.sqrt P M.traceVector)))) from rfl,
    ← ContinuousLinearMap.adjoint_inner_left (CFC.sqrt P)
      (M.L (star σ) (C (M.L σ (CFC.sqrt P M.traceVector)))) M.traceVector,
    ← ContinuousLinearMap.star_eq_adjoint, (sqrt_sa M (P := P)).star_eq, map_star,
    ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right (M.L σ) (CFC.sqrt P M.traceVector)
      (C (M.L σ (CFC.sqrt P M.traceVector)))]

/-- **Bob's vector-state form**: `φ(L(σ*) P L(σ) C) = ⟪ζ, C ζ⟫` with `ζ = L(σ*) √P Ω`. -/
theorem traceState_conj_eq_inner' (σ : M.A) {C P : M.H →L[ℂ] M.H} (hC : C ∈ M.vnAlg)
    (hP : P ∈ M.vnAlg) (hP0 : 0 ≤ P) :
    M.traceState (M.L (star σ) * P * M.L σ * C)
      = ⟪M.L (star σ) (CFC.sqrt P M.traceVector),
          C (M.L (star σ) (CFC.sqrt P M.traceVector))⟫_ℂ := by
  have hsq : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP0
  have hmem : CFC.sqrt P ∈ M.vnAlg := sqrt_mem_vnAlg M hP0 hP
  have hmem1 : M.L (star σ) * P * M.L σ ∈ M.vnAlg :=
    mul_mem (mul_mem (M.L_mem_vnAlg _) hP) (M.L_mem_vnAlg _)
  rw [M.traceState_mul_comm_vn hmem1 hC]
  have e : C * (M.L (star σ) * P * M.L σ)
      = (C * M.L (star σ) * CFC.sqrt P) * (CFC.sqrt P * M.L σ) := by
    conv_lhs => rw [← hsq]
    simp only [mul_assoc]
  rw [e, M.traceState_mul_comm_vn (mul_mem (mul_mem hC (M.L_mem_vnAlg _)) hmem)
    (mul_mem hmem (M.L_mem_vnAlg _))]
  unfold StdTracialAlgebra.traceState
  rw [show (CFC.sqrt P * M.L σ * (C * M.L (star σ) * CFC.sqrt P)) M.traceVector
      = CFC.sqrt P (M.L σ (C (M.L (star σ) (CFC.sqrt P M.traceVector)))) from rfl,
    ← ContinuousLinearMap.adjoint_inner_left (CFC.sqrt P)
      (M.L σ (C (M.L (star σ) (CFC.sqrt P M.traceVector)))) M.traceVector,
    ← ContinuousLinearMap.star_eq_adjoint, (sqrt_sa M (P := P)).star_eq,
    ← ContinuousLinearMap.adjoint_inner_left (M.L σ)
      (C (M.L (star σ) (CFC.sqrt P M.traceVector))) (CFC.sqrt P M.traceVector),
    ← ContinuousLinearMap.star_eq_adjoint, ← map_star]

/-! ## The increments -/

variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
variable [Nonempty A] [Nonempty B]
variable {F : I → A → M.A} {G : J → B → M.A} (h : Hyp M F G)
variable (kA : I → A → ℕ) (xA : ∀ i a, Fin (kA i a) → M.A)
  (hxA : ∀ i a, F i a = ∑ k, star (xA i a k) * xA i a k)
variable (kB : J → B → ℕ) (yB : ∀ j b, Fin (kB j b) → M.A)
  (hyB : ∀ j b, G j b = ∑ l, star (yB j b l) * yB j b l)
include h

omit h in
theorem sq_norm_smul_ι (W : ↥(𝔑 M I J)) :
    ‖((Real.sqrt (d I J) : ℝ) : ℂ) • (N M I J).ι (lft M W)‖ ^ 2
      = (d I J : ℝ) * ((N M I J).τ (lft M (star W * W))).re := by
  rw [← RCLike.re_to_complex, ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right,
    StdTracialAlgebra.ι_inner, ← map_star, ← map_mul, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (d_pos (I := I) (J := J)).le]
  rw [RCLike.re_to_complex, Complex.re_ofReal_mul]
  rfl

omit h in
theorem d_mul_re_τ_Ecor (T : ↥M.vnAlg) :
    (d I J : ℝ) * ((N M I J).τ (lft M (Ecor M (I := I) (J := J) T))).re
      = (M.traceState T.1).re := by
  rw [τ_lift_E]
  have : ((d I J : ℂ))⁻¹ = (((d I J : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [this, Complex.re_ofReal_mul, ← mul_assoc, mul_inv_cancel₀ (d_pos (I := I) (J := J)).ne',
    one_mul]

/-- Alice's polarized kernel `K_ii − K_ii' − (K_i'i − K_i'i')`. -/
def ΔA (i i' : I) : ↥M.vnAlg := (KA M h i i - KA M h i i') - (KA M h i' i - KA M h i' i')

/-- Bob's polarized kernel. -/
def ΔB (j j' : J) : ↥M.vnAlg := (KB M h j j - KB M h j j') - (KB M h j' j - KB M h j' j')

theorem ΔA_val (i i' : I) : (ΔA M h i i').1
    = kern (LF M F i) (LF M F i) - kern (LF M F i) (LF M F i') - kern (LF M F i') (LF M F i)
      + kern (LF M F i') (LF M F i') := by
  show kern (LF M F i) (LF M F i) - kern (LF M F i) (LF M F i')
    - (kern (LF M F i') (LF M F i) - kern (LF M F i') (LF M F i')) = _
  abel

theorem ΔB_val (j j' : J) : (ΔB M h j j').1
    = kern (LG M G j) (LG M G j) - kern (LG M G j) (LG M G j') - kern (LG M G j') (LG M G j)
      + kern (LG M G j') (LG M G j') := by
  show kern (LG M G j) (LG M G j) - kern (LG M G j) (LG M G j')
    - (kern (LG M G j') (LG M G j) - kern (LG M G j') (LG M G j')) = _
  abel

theorem star_diffA_mul_diffA (i i' : I) :
    star (cA M h i - cA M h i') * (cA M h i - cA M h i') = Ecor M (ΔA M h i i') := by
  rw [star_sub, sub_mul, mul_sub, mul_sub, star_cA_mul_cA, star_cA_mul_cA, star_cA_mul_cA,
    star_cA_mul_cA]
  unfold ΔA
  rw [← E_sub, ← E_sub, ← E_sub]

theorem diffB_mul_star_diffB (j j' : J) :
    (dB M h j - dB M h j') * star (dB M h j - dB M h j') = Ecor M (ΔB M h j j') := by
  rw [star_sub, sub_mul, mul_sub, mul_sub, dB_mul_star_dB, dB_mul_star_dB, dB_mul_star_dB,
    dB_mul_star_dB]
  unfold ΔB
  rw [← E_sub, ← E_sub, ← E_sub]

/-- **Alice's increment**: `‖Φ(σ,i,j) − Φ(σ,i',j)‖² = re φ(L(σ*) Δ_A L(σ) L(Gⱼ))`. -/
theorem sq_norm_branch_sub_A (σ : M.A) (i i' : I) (j : J) :
    ‖branch M h σ i j - branch M h σ i' j‖ ^ 2
      = (M.traceState (M.L (star σ) * (ΔA M h i i').1 * M.L σ * LG M G j)).re := by
  have e0 : branch M h σ i j - branch M h σ i' j
      = ((Real.sqrt (d I J) : ℝ) : ℂ) • (N M I J).ι
          (lft M ((cA M h i - cA M h i') * Ecor M (Lv M σ) * dB M h j)) := by
    unfold branch Xb
    rw [← smul_sub, ← map_sub, ← map_sub, sub_mul, sub_mul]
  rw [e0, sq_norm_smul_ι]
  have e1 : star ((cA M h i - cA M h i') * Ecor M (Lv M σ) * dB M h j)
      * ((cA M h i - cA M h i') * Ecor M (Lv M σ) * dB M h j)
      = star (dB M h j) * (star (Ecor M (Lv M σ))
          * (star (cA M h i - cA M h i') * (cA M h i - cA M h i')) * Ecor M (Lv M σ))
          * dB M h j := by
    rw [star_mul, star_mul]
    noncomm_ring
  rw [e1, star_diffA_mul_diffA, star_Ecor_Lv, τ_conj, dB_mul_star_dB_self, ← E_mul, ← E_mul,
    ← E_mul, d_mul_re_τ_Ecor]
  rfl

/-- **Bob's increment**: `‖Φ(σ,i,j) − Φ(σ,i,j')‖² = re φ(L(σ*) L(Fᵢ) L(σ) Δ_B)`. -/
theorem sq_norm_branch_sub_B (σ : M.A) (i : I) (j j' : J) :
    ‖branch M h σ i j - branch M h σ i j'‖ ^ 2
      = (M.traceState (M.L (star σ) * LF M F i * M.L σ * (ΔB M h j j').1)).re := by
  have e0 : branch M h σ i j - branch M h σ i j'
      = ((Real.sqrt (d I J) : ℝ) : ℂ) • (N M I J).ι
          (lft M (cA M h i * Ecor M (Lv M σ) * (dB M h j - dB M h j'))) := by
    unfold branch Xb
    rw [← smul_sub, ← map_sub, ← map_sub, mul_sub]
  rw [e0, sq_norm_smul_ι]
  have e1 : star (cA M h i * Ecor M (Lv M σ) * (dB M h j - dB M h j'))
      * (cA M h i * Ecor M (Lv M σ) * (dB M h j - dB M h j'))
      = star (dB M h j - dB M h j') * (star (Ecor M (Lv M σ))
          * (star (cA M h i) * cA M h i) * Ecor M (Lv M σ)) * (dB M h j - dB M h j') := by
    rw [star_mul, star_mul]
    noncomm_ring
  rw [e1, star_cA_mul_cA_self, star_Ecor_Lv, τ_conj, diffB_mul_star_diffB, ← E_mul, ← E_mul,
    ← E_mul, d_mul_re_τ_Ecor]
  rfl

/-! ## The functionals -/

/-- Alice's functional `ω_j(C) = re ⟪ξ, C ξ⟫`, `ξ = L(σ) √(L Gⱼ) Ω`. -/
def ωA (G : J → B → M.A) (σ : M.A) (j : J) : (M.H →L[ℂ] M.H) →ₗ[ℝ] ℝ :=
  vecState M (M.L σ (CFC.sqrt (LG M G j) M.traceVector))

/-- Bob's functional `ω_i(C) = re ⟪ζ, C ζ⟫`, `ζ = L(σ*) √(L Fᵢ) Ω`. -/
def ωB (F : I → A → M.A) (σ : M.A) (i : I) : (M.H →L[ℂ] M.H) →ₗ[ℝ] ℝ :=
  vecState M (M.L (star σ) (CFC.sqrt (LF M F i) M.traceVector))

theorem ωA_eq (σ : M.A) (j : J) {C : M.H →L[ℂ] M.H} (hC : C ∈ M.vnAlg) :
    ωA M G σ j C = (M.traceState (M.L (star σ) * C * M.L σ * LG M G j)).re := by
  rw [ωA, vecState_apply, traceState_conj_eq_inner M σ hC (M.L_mem_vnAlg _) (LG_nonneg M h j)]

theorem ωB_eq (σ : M.A) (i : I) {C : M.H →L[ℂ] M.H} (hC : C ∈ M.vnAlg) :
    ωB M F σ i C = (M.traceState (M.L (star σ) * LF M F i * M.L σ * C)).re := by
  rw [ωB, vecState_apply, traceState_conj_eq_inner' M σ hC (M.L_mem_vnAlg _) (LF_nonneg M h i)]

theorem ωA_mono (σ : M.A) (j : J) {C C' : M.H →L[ℂ] M.H} (hCC : C ≤ C') :
    ωA M G σ j C ≤ ωA M G σ j C' := vecState_mono M _ hCC

theorem ωB_mono (σ : M.A) (i : I) {C C' : M.H →L[ℂ] M.H} (hCC : C ≤ C') :
    ωB M F σ i C ≤ ωB M F σ i C' := vecState_mono M _ hCC

theorem ωA_LF (σ : M.A) (j : J) (i : I) :
    ωA M G σ j (LF M F i) = (M.τ (star σ * (FA M F i * σ * GB M G j))).re := by
  rw [ωA_eq M h σ j (M.L_mem_vnAlg _), ← map_mul, ← map_mul, ← map_mul, M.traceState_L]
  simp only [mul_assoc]

theorem ωB_LG (σ : M.A) (i : I) (j : J) :
    ωB M F σ i (LG M G j) = (M.τ (star σ * (FA M F i * σ * GB M G j))).re := by
  rw [ωB_eq M h σ i (M.L_mem_vnAlg _), ← map_mul, ← map_mul, ← map_mul, M.traceState_L]
  simp only [mul_assoc]

theorem ωA_mass (σ : M.A) (hσ : M.τ (star σ * σ) = 1) (j : J) : ωA M G σ j 1 ≤ 1 := by
  rw [ωA_eq M h σ j (one_mem _), mul_one, ← map_mul, ← map_mul, M.traceState_L]
  have h1 : IsPosElem (1 : M.A) := by simpa using isPosElem_star_mul_self (1 : M.A)
  have hp := M.pairing_nonneg σ h1 (h.hG1 j)
  rw [show star σ * (1 * σ * (1 - GB M G j)) = star σ * σ - star σ * σ * GB M G j by
      noncomm_ring, map_sub, hσ, Complex.sub_re, Complex.one_re] at hp
  linarith

theorem ωB_mass (σ : M.A) (hσ : M.τ (star σ * σ) = 1) (i : I) : ωB M F σ i 1 ≤ 1 := by
  rw [ωB_eq M h σ i (one_mem _), mul_one, ← map_mul, ← map_mul, M.traceState_L]
  have h1 : IsPosElem (1 : M.A) := by simpa using isPosElem_star_mul_self (1 : M.A)
  have hp := M.pairing_nonneg σ (h.hF1 i) h1
  rw [show star σ * ((1 - FA M F i) * σ * 1) = star σ * σ - star σ * FA M F i * σ by
      noncomm_ring, map_sub, hσ, Complex.sub_re, Complex.one_re] at hp
  linarith

theorem hinc_A (σ : M.A) (j : J) (i i' : I) :
    ‖branch M h σ i j - branch M h σ i' j‖ ^ 2
      = ωA M G σ j (kern (LF M F i) (LF M F i) - kern (LF M F i) (LF M F i')
          - kern (LF M F i') (LF M F i) + kern (LF M F i') (LF M F i')) := by
  rw [sq_norm_branch_sub_A, ← ΔA_val M h i i', ωA_eq M h σ j (ΔA M h i i').2]

theorem hinc_B (σ : M.A) (i : I) (j j' : J) :
    ‖branch M h σ i j - branch M h σ i j'‖ ^ 2
      = ωB M F σ i (kern (LG M G j) (LG M G j) - kern (LG M G j) (LG M G j')
          - kern (LG M G j') (LG M G j) + kern (LG M G j') (LG M G j')) := by
  rw [sq_norm_branch_sub_B, ← ΔB_val M h j j', ωB_eq M h σ i (ΔB M h j j').2]

/-! ## The tower condition along `L` -/

omit h in
theorem tower_L {steps : ℕ} {Ω : Type} [Fintype Ω] (law : Ω → ℝ) {K : Type} [DecidableEq K]
    (idx : Fin (steps + 1) → Ω → K) (E : K → M.A)
    (hX : ∀ (s : Fin steps) (i : K),
      (((∑ ω ∈ Finset.univ.filter fun ω => idx s.castSucc ω = i, law ω : ℝ) : ℂ)) • E i
        = ∑ ω ∈ Finset.univ.filter fun ω => idx s.castSucc ω = i,
            (((law ω : ℝ) : ℂ)) • E (idx s.succ ω))
    (s : Fin steps) (i : K) :
    ∑ ω, (if idx s.castSucc ω = i then law ω else 0) • M.L (E (idx s.succ ω))
      = (∑ ω, if idx s.castSucc ω = i then law ω else 0) • M.L (E i) := by
  have := congrArg M.L (hX s i)
  rw [map_smul, map_sum, Finset.sum_filter, Finset.sum_filter] at this
  simp only [map_smul] at this
  rw [Complex.coe_smul] at this
  refine Eq.trans ?_ this.symm
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs
  · exact (Complex.coe_smul _ _).symm
  · exact zero_smul ℝ _

/-! ## The budgets -/

include hxA hyB in
/-- **The Alice-column budget** for the entropic arena (unbundled form of
`ResolverArena.ColEntropyBudget`). -/
theorem col_budget (steps : ℕ) {Ω : Type} [Fintype Ω] (law : Ω → ℝ) (hlaw : ∀ ω, 0 ≤ law ω)
    (hsum : ∑ ω, law ω = 1) (idx : Fin (steps + 1) → Ω → I) (hidx0 : ∀ ω ω', idx 0 ω = idx 0 ω')
    (hX : ∀ (s : Fin steps) (i : I),
      (((∑ ω ∈ Finset.univ.filter fun ω => idx s.castSucc ω = i, law ω : ℝ) : ℂ)) • FA M F i
        = ∑ ω ∈ Finset.univ.filter fun ω => idx s.castSucc ω = i,
            (((law ω : ℝ) : ℂ)) • FA M F (idx s.succ ω))
    (σ : M.A) (hσ : M.τ (star σ * σ) = 1) (j : J) (ω₀ : Ω) :
    ∑ s : Fin steps, ∑ ω, law ω *
        ‖(arena M h kA xA hxA kB yB hyB).branch σ (idx s.succ ω) j
          - (arena M h kA xA hxA kB yB hyB).branch σ (idx s.castSucc ω) j‖ ^ 2
      ≤ Real.negMulLog (M.τ (star σ * (FA M F (idx 0 ω₀) * σ * GB M G j))).re := by
  have key := entropy_budget (LF M F) (LF_nonneg M h) (LF_le_one M h) (ωA M G σ j)
    (fun {C C'} hCC => ωA_mono M h σ j hCC) (ωA_mass M h σ hσ j) (fun i => branch M h σ i j)
    (fun i i' => hinc_A M h σ j i i') law hlaw hsum idx hidx0
    (tower_L M law idx (FA M F) hX) ω₀
  rwa [ωA_LF M h] at key

include hxA hyB in
/-- **The Bob-row budget** for the entropic arena (unbundled form of
`ResolverArena.RowEntropyBudget`). -/
theorem row_budget (steps : ℕ) {Ω : Type} [Fintype Ω] (law : Ω → ℝ) (hlaw : ∀ ω, 0 ≤ law ω)
    (hsum : ∑ ω, law ω = 1) (idx : Fin (steps + 1) → Ω → J) (hidx0 : ∀ ω ω', idx 0 ω = idx 0 ω')
    (hX : ∀ (s : Fin steps) (j : J),
      (((∑ ω ∈ Finset.univ.filter fun ω => idx s.castSucc ω = j, law ω : ℝ) : ℂ)) • GB M G j
        = ∑ ω ∈ Finset.univ.filter fun ω => idx s.castSucc ω = j,
            (((law ω : ℝ) : ℂ)) • GB M G (idx s.succ ω))
    (σ : M.A) (hσ : M.τ (star σ * σ) = 1) (i : I) (ω₀ : Ω) :
    ∑ s : Fin steps, ∑ ω, law ω *
        ‖(arena M h kA xA hxA kB yB hyB).branch σ i (idx s.succ ω)
          - (arena M h kA xA hxA kB yB hyB).branch σ i (idx s.castSucc ω)‖ ^ 2
      ≤ Real.negMulLog (M.τ (star σ * (FA M F i * σ * GB M G (idx 0 ω₀)))).re := by
  have key := entropy_budget (LG M G) (LG_nonneg M h) (LG_le_one M h) (ωB M F σ i)
    (fun {C C'} hCC => ωB_mono M h σ i hCC) (ωB_mass M h σ hσ i) (fun j => branch M h σ i j)
    (fun j j' => hinc_B M h σ i j j') law hlaw hsum idx hidx0
    (tower_L M law idx (GB M G) hX) ω₀
  rwa [ωB_LG M h] at key

end

end EntropicArena

end CommutingRepetition
