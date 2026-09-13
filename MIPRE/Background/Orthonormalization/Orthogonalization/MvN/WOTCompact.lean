/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/WOTCompact.lean
-/
/-
# Compactness of norm-bounded sets in the weak operator topology

Proof-side topology for tier T3 of the formalization of M. de la Salle,
*Orthogonalization of Positive Operator Valued Measures* (arXiv:2103.14126v2):
the limiting arguments of Section 5 (type III case, and the passage from finite
to general von Neumann algebras) extract, from a bounded net of operators, a
weak-operator cluster point that still lies in the algebra, is still positive,
still commutes with a fixed operator, and so on.

This file works with Mathlib's type copy `H →WOT[ℂ] H` of `H →L[ℂ] H` carrying the
weak operator topology (`ContinuousLinearMapWOT`, with `ofCLM`/`toCLM` the two
directions of the identity) and proves:

* bridging lemmas: the matrix coefficients `T ↦ ⟪ξ, T η⟫` are WOT-continuous
  (`continuous_inner_apply`) and convergence in the WOT is convergence of all
  matrix coefficients (`tendsto_iff_forall_inner_tendsto`, `tendsto_ofCLM_iff`),
  using the Riesz representation `InnerProductSpace.toDual` to identify the
  strong dual of `H` with `H`;
* **compactness**: every norm-bounded set `{T | ‖toCLM T‖ ≤ r}` is WOT-compact
  (`isCompact_setOf_norm_le`). The proof is the ultrafilter criterion: along an
  ultrafilter on the set, every coefficient `⟪T ξ, η⟫` lives in a compact disc and
  converges; the limit is a bounded sesquilinear form, hence `⟪L ξ, η⟫` for a unique
  operator `L` (`InnerProductSpace.continuousLinearMapOfBilin`) with `‖L‖ ≤ r`, and
  the ultrafilter converges to `ofCLM L`;
* closedness of the conditions used downstream: self-adjointness, positivity,
  order bounds `T ≤ a`, `a ≤ T`, membership in a von Neumann algebra `M` (written
  as commutation with the commutant `M′`), commutation with a fixed operator, and
  the support condition `a T b = T`; with the corresponding "limits stay in the
  set" corollaries, and convexity of the positive cone, the order intervals and
  the norm balls.

Nothing in this file is a statement of the paper.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped InnerProductSpace ComplexOrder ComplexConjugate
open Filter Topology ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Bridging: matrix coefficients and convergence -/

/-- The matrix coefficient `T ↦ ⟪ξ, T η⟫` is continuous for the weak operator topology. -/
theorem continuous_inner_apply (ξ η : H) :
    Continuous fun T : H →WOT[ℂ] H => ⟪ξ, T η⟫_ℂ := by
  have h := continuous_dual_apply (σ := RingHom.id ℂ) (E := H) (F := H) η
    (InnerProductSpace.toDual ℂ H ξ)
  simpa only [InnerProductSpace.toDual_apply_apply] using h

/-- The matrix coefficient `T ↦ ⟪T ξ, η⟫` is continuous for the weak operator topology. -/
theorem continuous_inner_apply' (ξ η : H) :
    Continuous fun T : H →WOT[ℂ] H => ⟪T ξ, η⟫_ℂ := by
  have h := Complex.continuous_conj.comp (continuous_inner_apply η ξ)
  simpa only [Function.comp_def, inner_conj_symm] using h

/-- Convergence in the weak operator topology is convergence of every matrix coefficient
`⟪ξ, · η⟫`: Mathlib's `tendsto_iff_forall_dual_apply_tendsto` through the Riesz
representation of the dual of `H`. -/
theorem tendsto_iff_forall_inner_tendsto {κ : Type*} {l : Filter κ} {f : κ → H →WOT[ℂ] H}
    {A : H →WOT[ℂ] H} :
    Tendsto f l (𝓝 A) ↔ ∀ ξ η : H, Tendsto (fun k => ⟪ξ, f k η⟫_ℂ) l (𝓝 ⟪ξ, A η⟫_ℂ) := by
  rw [tendsto_iff_forall_dual_apply_tendsto]
  constructor
  · intro h ξ η
    simpa only [InnerProductSpace.toDual_apply_apply] using h η (InnerProductSpace.toDual ℂ H ξ)
  · intro h η y
    obtain ⟨ξ, rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective y
    simpa only [InnerProductSpace.toDual_apply_apply] using h ξ η

/-- Convergence in the weak operator topology, through the coefficients `⟪· ξ, η⟫`. -/
theorem tendsto_iff_forall_inner_tendsto' {κ : Type*} {l : Filter κ} {f : κ → H →WOT[ℂ] H}
    {A : H →WOT[ℂ] H} :
    Tendsto f l (𝓝 A) ↔ ∀ ξ η : H, Tendsto (fun k => ⟪f k ξ, η⟫_ℂ) l (𝓝 ⟪A ξ, η⟫_ℂ) := by
  rw [tendsto_iff_forall_inner_tendsto]
  constructor
  · intro h ξ η
    have h' := (Complex.continuous_conj.tendsto _).comp (h η ξ)
    simpa only [Function.comp_def, inner_conj_symm] using h'
  · intro h ξ η
    have h' := (Complex.continuous_conj.tendsto _).comp (h η ξ)
    simpa only [Function.comp_def, inner_conj_symm] using h'

/-- Convergence in the weak operator topology of a family of operators of `H →L[ℂ] H`,
in terms of matrix coefficients. -/
theorem tendsto_ofCLM_iff {κ : Type*} {l : Filter κ} {T : κ → H →L[ℂ] H} {L : H →L[ℂ] H} :
    Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L)) ↔
      ∀ ξ η : H, Tendsto (fun k => ⟪ξ, T k η⟫_ℂ) l (𝓝 ⟪ξ, L η⟫_ℂ) :=
  tendsto_iff_forall_inner_tendsto

/-! ### Compactness of the norm-bounded sets -/

/-- **WOT-compactness of the norm-bounded sets of `B(H)`.** Proof by the ultrafilter
criterion: along an ultrafilter `𝒰` on `{T | ‖T‖ ≤ r}`, each coefficient `⟪T ξ, η⟫`
lies in the compact disc of radius `r ‖ξ‖ ‖η‖`, hence converges to some `c ξ η`; the
limit `c` is sesquilinear and bounded by `r ‖ξ‖ ‖η‖`, so it is `⟪L ξ, η⟫` for an operator
`L` with `‖L‖ ≤ r`, and `𝒰` converges to `ofCLM L` in the weak operator topology. -/
theorem isCompact_setOf_norm_le (r : ℝ) : IsCompact {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ r} := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  have hS : {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ r} ∈ (𝒰 : Filter _) := le_principal_iff.mp h𝒰
  obtain ⟨T₀, hT₀⟩ := Filter.nonempty_of_mem hS
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hT₀
  -- The coefficient functions are eventually bounded along `𝒰`.
  have hbdd : ∀ ξ η : H, ∀ᶠ T : H →WOT[ℂ] H in 𝒰, ‖⟪T ξ, η⟫_ℂ‖ ≤ r * ‖ξ‖ * ‖η‖ := by
    intro ξ η
    filter_upwards [hS] with T hT
    have hT' : ‖toCLM T‖ ≤ r := hT
    calc ‖⟪T ξ, η⟫_ℂ‖ ≤ ‖T ξ‖ * ‖η‖ := norm_inner_le_norm _ _
      _ ≤ ‖toCLM T‖ * ‖ξ‖ * ‖η‖ := by
          gcongr
          exact (toCLM T).le_opNorm ξ
      _ ≤ r * ‖ξ‖ * ‖η‖ := by gcongr
  -- Each coefficient converges along `𝒰` (closed discs are compact).
  have hlim : ∀ ξ η : H, ∃ z : ℂ, Tendsto (fun T : H →WOT[ℂ] H => ⟪T ξ, η⟫_ℂ) 𝒰 (𝓝 z) := by
    intro ξ η
    have hle : (Ultrafilter.map (fun T : H →WOT[ℂ] H => ⟪T ξ, η⟫_ℂ) 𝒰 : Filter ℂ)
        ≤ 𝓟 (Metric.closedBall 0 (r * ‖ξ‖ * ‖η‖)) := by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact Filter.mem_of_superset (hbdd ξ η) fun T hT => by
        simp only [Set.mem_preimage, mem_closedBall_zero_iff]
        exact hT
    obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : ℂ) _).ultrafilter_le_nhds _ hle
    rw [Ultrafilter.coe_map] at hz
    exact ⟨z, hz⟩
  choose c hc using hlim
  -- The limit is a bounded sesquilinear form.
  have huniq : ∀ {ξ η : H} {z : ℂ},
      Tendsto (fun T : H →WOT[ℂ] H => ⟪T ξ, η⟫_ℂ) 𝒰 (𝓝 z) → c ξ η = z :=
    fun h => tendsto_nhds_unique (hc _ _) h
  have hadd_right : ∀ ξ η₁ η₂ : H, c ξ (η₁ + η₂) = c ξ η₁ + c ξ η₂ := fun ξ η₁ η₂ =>
    huniq (by simpa only [inner_add_right] using (hc ξ η₁).add (hc ξ η₂))
  have hsmul_right : ∀ (ξ η : H) (a : ℂ), c ξ (a • η) = a * c ξ η := fun ξ η a =>
    huniq (by simpa only [inner_smul_right] using (hc ξ η).const_mul a)
  have hadd_left : ∀ ξ₁ ξ₂ η : H, c (ξ₁ + ξ₂) η = c ξ₁ η + c ξ₂ η := fun ξ₁ ξ₂ η =>
    huniq (by simpa only [map_add, inner_add_left] using (hc ξ₁ η).add (hc ξ₂ η))
  have hsmul_left : ∀ (ξ η : H) (a : ℂ), c (a • ξ) η = conj a * c ξ η := fun ξ η a =>
    huniq (by simpa only [map_smul, inner_smul_left] using (hc ξ η).const_mul (conj a))
  have hbound : ∀ ξ η : H, ‖c ξ η‖ ≤ r * ‖ξ‖ * ‖η‖ := fun ξ η =>
    le_of_tendsto (hc ξ η).norm (hbdd ξ η)
  let B : H →L⋆[ℂ] H →L[ℂ] ℂ :=
    LinearMap.mkContinuous₂
      { toFun := fun ξ =>
          { toFun := fun η => c ξ η
            map_add' := hadd_right ξ
            map_smul' := fun a η => by
              simp only [RingHom.id_apply, smul_eq_mul]
              exact hsmul_right ξ η a }
        map_add' := fun ξ₁ ξ₂ => LinearMap.ext fun η => hadd_left ξ₁ ξ₂ η
        map_smul' := fun a ξ => LinearMap.ext fun η => by
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul]
          exact hsmul_left ξ η a }
      r hbound
  -- The operator representing the form, and its norm bound.
  let L : H →L[ℂ] H := InnerProductSpace.continuousLinearMapOfBilin B
  have hL : ∀ ξ η : H, ⟪L ξ, η⟫_ℂ = c ξ η := fun ξ η =>
    InnerProductSpace.continuousLinearMapOfBilin_apply B ξ η
  have hLnorm : ‖L‖ ≤ r := by
    refine ContinuousLinearMap.opNorm_le_bound _ hr0 fun ξ => ?_
    have hBnorm : ‖B‖ ≤ r := LinearMap.mkContinuous₂_norm_le _ hr0 _
    have e : L ξ = (InnerProductSpace.toDual ℂ H).symm (B ξ) := rfl
    rw [e, LinearIsometryEquiv.norm_map]
    calc ‖B ξ‖ ≤ ‖B‖ * ‖ξ‖ := B.le_opNorm ξ
      _ ≤ r * ‖ξ‖ := by gcongr
  -- `𝒰` converges to `ofCLM L`.
  refine ⟨ofCLM L, hLnorm, ?_⟩
  rw [le_nhds_iff_forall_dual_apply_le_nhds]
  intro x y
  obtain ⟨ξ, rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective y
  simp only [InnerProductSpace.toDual_apply_apply, ofCLM_apply]
  have h := (Complex.continuous_conj.tendsto _).comp (hc x ξ)
  rw [← hL x ξ] at h
  simp only [Function.comp_def, inner_conj_symm] at h
  exact h

/-- A closed set of operators bounded in norm is WOT-compact. -/
theorem isCompact_of_isClosed_of_norm_le {S : Set (H →WOT[ℂ] H)} (hS : IsClosed S) {r : ℝ}
    (hr : ∀ T ∈ S, ‖toCLM T‖ ≤ r) : IsCompact S :=
  (isCompact_setOf_norm_le r).of_isClosed_subset hS hr

/-- A norm-bounded family of operators has a WOT cluster point of the same norm bound. -/
theorem exists_clusterPt_of_norm_le {κ : Type*} {l : Filter κ} [l.NeBot] {T : κ → H →L[ℂ] H}
    {r : ℝ} (hT : ∀ k, ‖T k‖ ≤ r) :
    ∃ L : H →L[ℂ] H, ‖L‖ ≤ r ∧ ClusterPt (ofCLM L) (map (fun k => ofCLM (T k)) l) := by
  have hle : map (fun k => ofCLM (T k)) l ≤ 𝓟 {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ r} :=
    le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall hT))
  obtain ⟨A, hA, hcl⟩ := (isCompact_setOf_norm_le r).exists_clusterPt hle
  exact ⟨toCLM A, hA, hcl⟩

/-! ### Closed conditions in the weak operator topology -/

/-- Fixing one matrix coefficient is a closed condition. -/
theorem isClosed_setOf_inner_eq (ξ η : H) (z : ℂ) :
    IsClosed {T : H →WOT[ℂ] H | ⟪ξ, T η⟫_ℂ = z} :=
  isClosed_eq (continuous_inner_apply ξ η) continuous_const

/-- Self-adjointness is a closed condition: it says `⟪T ξ, η⟫ = ⟪ξ, T η⟫` for all `ξ, η`. -/
theorem isClosed_setOf_isSelfAdjoint :
    IsClosed {T : H →WOT[ℂ] H | IsSelfAdjoint (toCLM T)} := by
  have : {T : H →WOT[ℂ] H | IsSelfAdjoint (toCLM T)}
      = ⋂ ξ, ⋂ η, {T : H →WOT[ℂ] H | ⟪T ξ, η⟫_ℂ = ⟪ξ, T η⟫_ℂ} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
  rw [this]
  exact isClosed_iInter fun ξ => isClosed_iInter fun η =>
    isClosed_eq (continuous_inner_apply' ξ η) (continuous_inner_apply ξ η)

/-- Positivity is a closed condition: self-adjointness and `0 ≤ ⟪T ξ, ξ⟫` for all `ξ`. -/
theorem isClosed_setOf_nonneg : IsClosed {T : H →WOT[ℂ] H | 0 ≤ toCLM T} := by
  have : {T : H →WOT[ℂ] H | 0 ≤ toCLM T}
      = {T : H →WOT[ℂ] H | IsSelfAdjoint (toCLM T)}
        ∩ ⋂ ξ, {T : H →WOT[ℂ] H | 0 ≤ ⟪T ξ, ξ⟫_ℂ} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff',
      toCLM_apply]
  rw [this]
  exact isClosed_setOf_isSelfAdjoint.inter
    (isClosed_iInter fun ξ => isClosed_le continuous_const (continuous_inner_apply' ξ ξ))

/-- `T ≤ a` is a closed condition. -/
theorem isClosed_setOf_le (a : H →L[ℂ] H) : IsClosed {T : H →WOT[ℂ] H | toCLM T ≤ a} := by
  have : {T : H →WOT[ℂ] H | toCLM T ≤ a}
      = (fun T : H →WOT[ℂ] H => ofCLM a - T) ⁻¹' {T | 0 ≤ toCLM T} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, toCLM_sub, sub_nonneg]
  rw [this]
  exact isClosed_setOf_nonneg.preimage (continuous_const.sub continuous_id)

/-- `a ≤ T` is a closed condition. -/
theorem isClosed_setOf_ge (a : H →L[ℂ] H) : IsClosed {T : H →WOT[ℂ] H | a ≤ toCLM T} := by
  have : {T : H →WOT[ℂ] H | a ≤ toCLM T}
      = (fun T : H →WOT[ℂ] H => T - ofCLM a) ⁻¹' {T | 0 ≤ toCLM T} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, toCLM_sub, sub_nonneg]
  rw [this]
  exact isClosed_setOf_nonneg.preimage (continuous_id.sub continuous_const)

/-- `T ≤ 1` is a closed condition. -/
theorem isClosed_setOf_le_one : IsClosed {T : H →WOT[ℂ] H | toCLM T ≤ 1} :=
  isClosed_setOf_le 1

omit [CompleteSpace H] in
/-- The support condition `a T b = T` is closed: left and right multiplication by a fixed
operator are WOT-continuous. -/
theorem isClosed_setOf_mul_eq (a b : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | a * toCLM T * b = toCLM T} := by
  have : {T : H →WOT[ℂ] H | a * toCLM T * b = toCLM T}
      = {T : H →WOT[ℂ] H | ofCLM a * T * ofCLM b = T} := by
    ext T
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have h' : toCLM (ofCLM a * T * ofCLM b) = toCLM T := h
      exact toCLM_injective h'
    · intro h
      exact congrArg toCLM h
  rw [this]
  exact isClosed_eq ((continuous_mul_const (ofCLM b)).comp (continuous_const_mul (ofCLM a)))
    continuous_id

omit [CompleteSpace H] in
/-- Commutation with a fixed operator is a closed condition. -/
theorem isClosed_setOf_commute (a : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | Commute (toCLM T) a} := by
  have : {T : H →WOT[ℂ] H | Commute (toCLM T) a}
      = {T : H →WOT[ℂ] H | T * ofCLM a = ofCLM a * T} := by
    ext T
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have h' : toCLM (T * ofCLM a) = toCLM (ofCLM a * T) := h.eq
      exact toCLM_injective h'
    · intro h
      exact congrArg toCLM h
  rw [this]
  exact isClosed_eq (continuous_mul_const (ofCLM a)) (continuous_const_mul (ofCLM a))

/-- Membership in a von Neumann algebra is a closed condition: `T ∈ M = M′′` says that `T`
commutes with every element of the commutant `M′`. -/
theorem isClosed_setOf_mem (M : VonNeumannAlgebra H) :
    IsClosed {T : H →WOT[ℂ] H | toCLM T ∈ M} := by
  have : {T : H →WOT[ℂ] H | toCLM T ∈ M}
      = ⋂ y ∈ M.commutant, {T : H →WOT[ℂ] H | ofCLM y * T = T * ofCLM y} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h y hy
      have h' : toCLM (ofCLM y * T) = toCLM (T * ofCLM y) :=
        (VonNeumannAlgebra.mem_commutant_iff.mp hy (toCLM T) h).symm
      exact toCLM_injective h'
    · intro h
      rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
      intro y hy
      exact congrArg toCLM (h y hy)
  rw [this]
  exact isClosed_biInter fun y _ =>
    isClosed_eq (continuous_const_mul (ofCLM y)) (continuous_mul_const (ofCLM y))

/-! ### Limits stay in the closed sets -/

section Limits

variable {κ : Type*} {l : Filter κ} [l.NeBot] {T : κ → H →L[ℂ] H} {L : H →L[ℂ] H}

/-- A WOT-limit of elements of `M` lies in `M`. -/
theorem mem_of_tendsto_ofCLM (M : VonNeumannAlgebra H)
    (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L))) (hT : ∀ k, T k ∈ M) : L ∈ M :=
  (isClosed_setOf_mem M).mem_of_tendsto h (Eventually.of_forall hT)

/-- A WOT-limit of positive operators is positive. -/
theorem nonneg_of_tendsto_ofCLM (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L)))
    (hT : ∀ k, 0 ≤ T k) : 0 ≤ L :=
  isClosed_setOf_nonneg.mem_of_tendsto h (Eventually.of_forall hT)

/-- A WOT-limit of operators `≤ a` is `≤ a`. -/
theorem le_of_tendsto_ofCLM {a : H →L[ℂ] H} (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L)))
    (hT : ∀ k, T k ≤ a) : L ≤ a :=
  (isClosed_setOf_le a).mem_of_tendsto h (Eventually.of_forall hT)

/-- A WOT-limit of operators `≥ a` is `≥ a`. -/
theorem ge_of_tendsto_ofCLM {a : H →L[ℂ] H} (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L)))
    (hT : ∀ k, a ≤ T k) : a ≤ L :=
  (isClosed_setOf_ge a).mem_of_tendsto h (Eventually.of_forall hT)

/-- A WOT-limit of self-adjoint operators is self-adjoint. -/
theorem isSelfAdjoint_of_tendsto_ofCLM (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L)))
    (hT : ∀ k, IsSelfAdjoint (T k)) : IsSelfAdjoint L :=
  isClosed_setOf_isSelfAdjoint.mem_of_tendsto h (Eventually.of_forall hT)

omit [CompleteSpace H] in
/-- A WOT-limit of operators commuting with `a` commutes with `a`. -/
theorem commute_of_tendsto_ofCLM {a : H →L[ℂ] H}
    (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L))) (hT : ∀ k, Commute (T k) a) :
    Commute L a :=
  (isClosed_setOf_commute a).mem_of_tendsto h (Eventually.of_forall hT)

omit [CompleteSpace H] in
/-- A WOT-limit of operators supported in `(a, b)` (`a T b = T`) is so supported. -/
theorem mul_eq_of_tendsto_ofCLM {a b : H →L[ℂ] H}
    (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L))) (hT : ∀ k, a * T k * b = T k) :
    a * L * b = L :=
  (isClosed_setOf_mul_eq a b).mem_of_tendsto h (Eventually.of_forall hT)

/-- The norm bound passes to WOT-limits (as a closed-set statement it is the compactness
lemma's set; here it is the direct coefficient estimate). -/
theorem norm_le_of_tendsto_ofCLM {r : ℝ} (h : Tendsto (fun k => ofCLM (T k)) l (𝓝 (ofCLM L)))
    (hT : ∀ k, ‖T k‖ ≤ r) : ‖L‖ ≤ r := by
  have hr0 : 0 ≤ r := by
    obtain ⟨k⟩ := l.nonempty_of_neBot
    exact (norm_nonneg _).trans (hT k)
  refine ContinuousLinearMap.opNorm_le_bound _ hr0 fun ξ => ?_
  have hcoef := (tendsto_ofCLM_iff.mp h) (L ξ) ξ
  have hbdd : ∀ᶠ k in l, ‖⟪L ξ, T k ξ⟫_ℂ‖ ≤ r * ‖ξ‖ * ‖L ξ‖ :=
    Eventually.of_forall fun k =>
      calc ‖⟪L ξ, T k ξ⟫_ℂ‖ ≤ ‖L ξ‖ * ‖T k ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖L ξ‖ * (‖T k‖ * ‖ξ‖) := by gcongr; exact (T k).le_opNorm ξ
        _ ≤ ‖L ξ‖ * (r * ‖ξ‖) := by gcongr; exact hT k
        _ = r * ‖ξ‖ * ‖L ξ‖ := by ring
  have hlim : ‖⟪L ξ, L ξ⟫_ℂ‖ ≤ r * ‖ξ‖ * ‖L ξ‖ := le_of_tendsto hcoef.norm hbdd
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq] at hlim
  by_cases h0 : ‖L ξ‖ = 0
  · rw [h0]; positivity
  · exact le_of_mul_le_mul_right hlim (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

end Limits

/-! ### Convexity -/

/-- The positive cone is convex. -/
theorem convex_setOf_nonneg : Convex ℝ {T : H →WOT[ℂ] H | 0 ≤ toCLM T} := by
  intro x hx y hy s t hs ht _
  show 0 ≤ s • toCLM x + t • toCLM y
  exact add_nonneg (smul_nonneg hs hx) (smul_nonneg ht hy)

/-- The order interval `{T | T ≤ a}` is convex. -/
theorem convex_setOf_le (a : H →L[ℂ] H) : Convex ℝ {T : H →WOT[ℂ] H | toCLM T ≤ a} := by
  intro x hx y hy s t hs ht hst
  show s • toCLM x + t • toCLM y ≤ a
  calc s • toCLM x + t • toCLM y ≤ s • a + t • a :=
        add_le_add (smul_le_smul_of_nonneg_left hx hs) (smul_le_smul_of_nonneg_left hy ht)
    _ = a := by rw [← add_smul, hst, one_smul]

/-- The order interval `{T | a ≤ T}` is convex. -/
theorem convex_setOf_ge (a : H →L[ℂ] H) : Convex ℝ {T : H →WOT[ℂ] H | a ≤ toCLM T} := by
  intro x hx y hy s t hs ht hst
  show a ≤ s • toCLM x + t • toCLM y
  calc a = s • a + t • a := by rw [← add_smul, hst, one_smul]
    _ ≤ s • toCLM x + t • toCLM y :=
        add_le_add (smul_le_smul_of_nonneg_left hx hs) (smul_le_smul_of_nonneg_left hy ht)

omit [CompleteSpace H] in
/-- The norm balls are convex. -/
theorem convex_setOf_norm_le (r : ℝ) : Convex ℝ {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ r} := by
  intro x hx y hy s t hs ht hst
  show ‖s • toCLM x + t • toCLM y‖ ≤ r
  calc ‖s • toCLM x + t • toCLM y‖ ≤ ‖s • toCLM x‖ + ‖t • toCLM y‖ := norm_add_le _ _
    _ = s * ‖toCLM x‖ + t * ‖toCLM y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ ≤ s * r + t * r := by gcongr <;> assumption
    _ = r := by rw [← add_mul, hst, one_mul]

end Orthogonalization.MvN
