/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/StandardFormOf.lean
-/
/-
# The standard form of a von Neumann algebra with a faithful vector-form state (stage E3.6)

Let `N ⊆ B(H)` be a von Neumann algebra and `φ(T) = ∑ₖ ⟪gₖ, T gₖ⟫` (with
`∑ ‖gₖ‖² < ∞`) a state faithful on `N`.  Put `Ξ := (gₖ) ∈ ℓ²(ℕ, H)`, which is
separating for `N ⊗ 1`, and `K := [(N ⊗ 1) Ξ]`.  The compression of `N ⊗ 1` to
`K` is a von Neumann algebra `M` on `K` (VN/Cutdown.lean), `Ξ ∈ K` is cyclic and
separating for `M`, and `θ : x ↦ P (x ⊗ 1) ι` is a normal `*`-isomorphism
`N → M` with normal inverse and `⟪Ξ, θ(T) Ξ⟫ = φ(T)`.  This is the standard
form `(M, K, Ξ)` of `(N, φ)`, the input of Tomita–Takesaki theory (stage E4).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cutdown
import MIPRE.Background.Repetition.CommutingRepetition.VN.Amplification

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

open scoped InnerProductSpace
open Filter Topology

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section StandardForm

variable (N : VonNeumannAlgebra H) (g : ℕ → H) (hg : Summable fun k => ‖g k‖ ^ 2)
  (hfaith : ∀ x ∈ N, ∑' k, ⟪g k, (star x * x) (g k)⟫_ℂ = 0 → x = 0)

/-- The vector `Ξ = (gₖ) ∈ ℓ²(ℕ, H)`. -/
noncomputable def sfXi : Hinf H := mkVec g hg

include hfaith in
theorem sfXi_separating : IsSeparating (amplAlg N : Set (Hinf H →L[ℂ] Hinf H)) (sfXi g hg) := by
  refine (isSeparating_mkVec g hg (S := (N : Set (H →L[ℂ] H))) hfaith).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

/-- The standard-form Hilbert space `K = [(N ⊗ 1) Ξ]`. -/
noncomputable def sfSpace : Submodule ℂ (Hinf H) :=
  cyclicSpace (amplAlg N : Set (Hinf H →L[ℂ] Hinf H)) (sfXi g hg)

instance : CompleteSpace (sfSpace N g hg) := completeSpace_cyclicSpace _ _

theorem sfSpace_invariant :
    ∀ x ∈ amplAlg N, ∀ v ∈ sfSpace N g hg, x v ∈ sfSpace N g hg :=
  cyclicSpace_invariant (amplAlg N) (sfXi g hg)

theorem sfXi_mem : sfXi g hg ∈ sfSpace N g hg := mem_cyclicSpace_self (amplAlg N) (sfXi g hg)

/-- The vector `Ξ` as an element of `K`. -/
noncomputable def sfVec : sfSpace N g hg := ⟨sfXi g hg, sfXi_mem N g hg⟩

theorem coe_sfVec : (sfVec N g hg : Hinf H) = sfXi g hg := rfl

/-- The standard-form von Neumann algebra `M = P (N ⊗ 1) ι` on `K`. -/
noncomputable def sfAlg : VonNeumannAlgebra (sfSpace N g hg) :=
  cutdown (sfSpace N g hg) (amplAlg N) (sfSpace_invariant N g hg) (sfXi g hg) (sfXi_mem N g hg)
    (sfXi_separating N g hg hfaith)

theorem sfVec_isCyclic :
    IsCyclic (sfAlg N g hg hfaith : Set (sfSpace N g hg →L[ℂ] sfSpace N g hg)) (sfVec N g hg) :=
  isCyclic_cutdown_cyclicSpace (amplAlg N) (sfXi g hg) (sfXi_separating N g hg hfaith)

theorem sfVec_isSeparating :
    IsSeparating (sfAlg N g hg hfaith : Set (sfSpace N g hg →L[ℂ] sfSpace N g hg)) (sfVec N g hg) :=
  isSeparating_cutdown (sfSpace N g hg) (amplAlg N) (sfSpace_invariant N g hg) (sfXi g hg)
    (sfXi_mem N g hg) (sfXi_separating N g hg hfaith)

/-- The map `θ : B(H) → B(K)`, `T ↦ P (T ⊗ 1) ι`. -/
noncomputable def sfMap (T : H →L[ℂ] H) : sfSpace N g hg →L[ℂ] sfSpace N g hg :=
  compressTo (sfSpace N g hg) (ampl T)

theorem sfMap_mem {x : H →L[ℂ] H} (hx : x ∈ N) : sfMap N g hg x ∈ sfAlg N g hg hfaith :=
  compressTo_mem_cutdown _ _ _ _ _ _ (ampl_mem_amplAlg N hx)

theorem sfMap_surjective {S : sfSpace N g hg →L[ℂ] sfSpace N g hg} (hS : S ∈ sfAlg N g hg hfaith) :
    ∃ x ∈ N, sfMap N g hg x = S := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hS
  exact ⟨x, hx, rfl⟩

include hfaith in
theorem sfMap_injective {x y : H →L[ℂ] H} (hx : x ∈ N) (hy : y ∈ N)
    (h : sfMap N g hg x = sfMap N g hg y) : x = y := by
  refine ampl_injective ?_
  exact compressTo_injective (sfSpace N g hg) (amplAlg N) (sfSpace_invariant N g hg) (sfXi g hg)
    (sfXi_mem N g hg) (sfXi_separating N g hg hfaith) (ampl_mem_amplAlg N hx)
    (ampl_mem_amplAlg N hy) h

theorem sfMap_one : sfMap N g hg 1 = 1 := by
  rw [sfMap, ampl_one, compressTo_one]

theorem sfMap_add (x y : H →L[ℂ] H) : sfMap N g hg (x + y) = sfMap N g hg x + sfMap N g hg y := by
  rw [sfMap, ampl_add, compressTo_add]
  rfl

theorem sfMap_smul (c : ℂ) (x : H →L[ℂ] H) : sfMap N g hg (c • x) = c • sfMap N g hg x := by
  rw [sfMap, ampl_smul, compressTo_smul]
  rfl

theorem sfMap_star (x : H →L[ℂ] H) : sfMap N g hg (star x) = star (sfMap N g hg x) := by
  rw [sfMap, ampl_star, compressTo_star]
  rfl

theorem sfMap_mul (x : H →L[ℂ] H) {y : H →L[ℂ] H} (hy : y ∈ N) :
    sfMap N g hg (x * y) = sfMap N g hg x * sfMap N g hg y := by
  rw [sfMap, ampl_mul]
  exact compressTo_mul_of_invariant _ _ (sfSpace_invariant N g hg _ (ampl_mem_amplAlg N hy))

theorem norm_sfMap_le (x : H →L[ℂ] H) : ‖sfMap N g hg x‖ ≤ ‖x‖ :=
  (norm_compressTo_le _ _).trans (norm_ampl_le x)

/-- `θ` is normal. -/
theorem isNormalMap_sfMap : IsNormalMap (sfMap N g hg) :=
  IsNormalMap.comp (isNormalMap_compressTo (sfSpace N g hg)) isNormalMap_ampl

/-- `⟪Ξ, θ(T) Ξ⟫ = ∑ₖ ⟪gₖ, T gₖ⟫`: the vector state of `Ξ` is `φ`. -/
theorem inner_sfVec_sfMap (T : H →L[ℂ] H) :
    ⟪sfVec N g hg, sfMap N g hg T (sfVec N g hg)⟫_ℂ = ∑' k, ⟪g k, T (g k)⟫_ℂ := by
  rw [sfMap, inner_compressTo_right]
  exact inner_mkVec_ampl g hg T

theorem coe_sfMap_apply (T : H →L[ℂ] H) (hT : T ∈ N) (v : sfSpace N g hg) :
    (sfMap N g hg T v : Hinf H) = ampl T v :=
  coe_compressTo_apply_of_invariant _ (sfSpace_invariant N g hg _ (ampl_mem_amplAlg N hT)) v

include hfaith in
/-- The inverse of `θ` is normal: bounded convergence of `θ(T i) Ξ` alone forces bounded strong
convergence of `T i` on `H`. -/
theorem tendstoStrongBdd_of_sfMap {ι : Type*} {l : Filter ι} {T : ι → H →L[ℂ] H}
    {L : H →L[ℂ] H} (hT : ∀ i, T i ∈ N) (hL : L ∈ N) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C)
    (h : Tendsto (fun i => sfMap N g hg (T i) (sfVec N g hg)) l
      (𝓝 (sfMap N g hg L (sfVec N g hg)))) :
    TendstoStrongBdd l T L := by
  -- convergence in `ℓ²(ℕ, H)` at `Ξ`
  have h1 : Tendsto (fun i => ampl (T i) (sfXi g hg)) l (𝓝 (ampl L (sfXi g hg))) := by
    have := ((sfSpace N g hg).subtypeL.continuous.tendsto _).comp h
    simpa only [Function.comp_def, Submodule.subtypeL_apply, coe_sfMap_apply N g hg _ (hT _),
      coe_sfMap_apply N g hg _ hL, coe_sfVec] using this
  have h2 : TendstoStrongBdd l (fun i => ampl (T i)) (ampl L) :=
    tendstoStrongBdd_of_tendsto_separating (amplAlg N) (sfXi_separating N g hg hfaith)
      (fun i => ampl_mem_amplAlg N (hT i)) (ampl_mem_amplAlg N hL)
      (C := C) (fun i => (norm_ampl_le _).trans (hC i)) h1
  refine ⟨⟨C, hC⟩, fun v => ?_⟩
  have := ((ev 0).continuous.tendsto _).comp (h2.tendsto (sgl 0 v))
  simpa only [Function.comp_def, ev_ampl_sgl] using this

end StandardForm

end VN

end CommutingRepetition
