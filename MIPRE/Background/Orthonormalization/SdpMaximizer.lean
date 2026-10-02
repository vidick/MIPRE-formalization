/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.WOTCompact
public import MIPRE.Foundations.FinitePair
public import MIPRE.Foundations.SummedSdp

@[expose] public section

/-!
# The summed semidefinite form: a maximizer, and the theorem

`MIPRE/Foundations/SummedSdp.lean` proves that a maximizer of `T ↦ ∑ᵢ Re τ(Tᵢ Aᵢ)` over the
measurements of the commutant of a set `t` of operators, with `τ` a faithful tracial vector
functional there, gives the summed semidefinite form: `Z = ∑ᵢ Tᵢ Aᵢ` self-adjoint, `Aᵢ ≤ Z` and
`Tᵢ Z = Tᵢ Aᵢ`. This file supplies the maximizer and assembles the theorem
(`reports/c6b-paper-proofs.md`, §5, Lemma 4 and Theorem 10).

* **Lemma 4** (`exists_isMaxOn_obj`): in the product of weak operator topologies, the
  measurements of the commutant form a closed subset of a product of unit balls, which is
  compact (the vendored `Orthogonalization.MvN.isCompact_setOf_norm_le`), and the objective is a
  finite sum of matrix coefficients, hence continuous. A finite sum of vector functionals is
  weak-operator continuous, so no σ-weak topology and no predual are needed.
* **Theorem 10** (`exists_isSummedSdp`, and `exists_isSummedSdp_centralizer` with the measurement
  and `Z` in the commutant as a `⋆`-subalgebra, carrying the order of `B(H)`).
* **In a finite pair** (`exists_isSummedSdp_finitePairA`, `exists_isSummedSdp_finitePairB`): the
  commutant of the second player's operators, `StarSubalgebra.centralizer ℂ M.opsB`, is the first
  player's operators, and the pair's `VecTrace` is faithful and tracial on it; symmetrically for
  the second player. These are the two components of the doubled model's local algebra
  `centralizer ℂ M.opsB × centralizer ℂ M.opsA` (item M2 of `planning/c6b-plan.md`), in which the
  join stage solves the program componentwise (Corollary 12) and pulls the solution back to the
  abstract algebras by order agreement (Lemma 13); neither is done here.

The weak-operator compactness lives in the vendored tree, which only `MIPRE/Background/` may name,
so this file is here and the core chain is in `MIPRE/Foundations`.
-/

namespace MIPRE.Orthonormalization

open scoped InnerProductSpace
open ContinuousLinearMapWOT MIPRE.SummedSdp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] {G : Type*} [Fintype G] {t : Set (H →L[ℂ] H)} {ξ : ι → H}

/-- **The commutant of a set of operators as a von Neumann algebra**: its `M″ = M` field is
`t‴ = t′`, so no bicommutant theorem is needed. -/
noncomputable def centralizerVN (t : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ t
  centralizer_centralizer' := by
    show Set.centralizer (Set.centralizer (SetLike.coe (StarSubalgebra.centralizer ℂ t))) =
      SetLike.coe (StarSubalgebra.centralizer ℂ t)
    rw [StarSubalgebra.coe_centralizer, Set.centralizer_centralizer_centralizer]

/-- **A maximizer exists** (`reports/c6b-paper-proofs.md`, §5, Lemma 4): the objective
`T ↦ ∑ᵢ Re τ(Tᵢ Aᵢ)` attains its maximum on the measurements of the commutant of `t`, by
weak-operator compactness of the unit ball. -/
theorem exists_isMaxOn_obj [Nonempty G] (t : Set (H →L[ℂ] H)) (ξ : ι → H)
    (A : G → H →L[ℂ] H) : ∃ T, IsMeasIn t T ∧ IsMaxOn (obj ξ A) {T | IsMeasIn t T} T := by
  classical
  -- the measurements, in the product of weak operator topologies
  set S : Set (G → H →WOT[ℂ] H) := {T | IsMeasIn t fun i => toCLM (T i)}
  have hsum : ∀ T : G → H →WOT[ℂ] H, ∑ i, toCLM (T i) = toCLM (∑ i, T i) := fun T =>
    (map_sum (ContinuousLinearMapWOT.ringEquiv (𝕜₁ := ℂ) (E := H)) T Finset.univ).symm
  have hSeq : S = ((⋂ i, (fun T : G → H →WOT[ℂ] H => T i) ⁻¹' {X | toCLM X ∈ centralizerVN t}) ∩
      ⋂ i, (fun T : G → H →WOT[ℂ] H => T i) ⁻¹' {X | 0 ≤ toCLM X}) ∩ {T | ∑ i, T i = 1} := by
    ext T
    simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, toCLM_injective (by rw [← hsum]; exact h3)⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, by rw [hsum, h3]; rfl⟩
  have hSc : IsClosed S := by
    rw [hSeq]
    exact ((isClosed_iInter fun i => (Orthogonalization.MvN.isClosed_setOf_mem
      (centralizerVN t)).preimage (continuous_apply i)).inter
      (isClosed_iInter fun i => Orthogonalization.MvN.isClosed_setOf_nonneg.preimage
        (continuous_apply i))).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  -- closed in a product of unit balls, hence compact
  have hScpt : IsCompact S :=
    (isCompact_univ_pi fun _ => Orthogonalization.MvN.isCompact_setOf_norm_le (H := H) 1)
      |>.of_isClosed_subset hSc fun T hT i _ => IsMeasIn.norm_le_one hT i
  -- nonempty: all the weight on one outcome
  obtain ⟨i₀⟩ := ‹Nonempty G›
  have hne : S.Nonempty := by
    let T₁ : G → H →L[ℂ] H := fun i => if i = i₀ then 1 else 0
    have hT₁ : IsMeasIn t T₁ := by
      refine ⟨fun i => ?_, fun i => ?_, by simp [T₁]⟩
      · by_cases hi : i = i₀ <;> simp [T₁, hi, one_mem, zero_mem]
      · by_cases hi : i = i₀ <;> simp [T₁, hi]
    exact ⟨fun i => ofCLM (T₁ i), hT₁⟩
  -- the objective is a finite sum of matrix coefficients
  have hcont : Continuous fun T : G → H →WOT[ℂ] H => obj ξ A fun i => toCLM (T i) := by
    change Continuous fun T : G → H →WOT[ℂ] H => ∑ i, (∑ k, ⟪ξ k, T i (A i (ξ k))⟫_ℂ).re
    exact continuous_finsetSum _ fun i _ => Complex.continuous_re.comp
      (continuous_finsetSum _ fun k _ =>
        (Orthogonalization.MvN.continuous_inner_apply _ _).comp (continuous_apply i))
  obtain ⟨T₀, hT₀, hmax⟩ := hScpt.exists_isMaxOn hne hcont.continuousOn
  exact ⟨fun i => toCLM (T₀ i), hT₀, isMaxOn_iff.2 fun T hT =>
    isMaxOn_iff.1 hmax (fun i => ofCLM (T i)) hT⟩

/-- **Theorem 10** (`reports/c6b-paper-proofs.md`, §5): in the commutant of a set `t` of
operators, with a faithful tracial vector functional, for finitely many self-adjoint `Aᵢ` of the
commutant there is a measurement `T` of the commutant with `Z = ∑ᵢ Tᵢ Aᵢ` self-adjoint,
`Aᵢ ≤ Z` and `Tᵢ Z = Tᵢ Aᵢ` for every `i`. -/
theorem exists_isSummedSdp [Nonempty G] (hS : IsFaithfulTrace t ξ) {A : G → H →L[ℂ] H}
    (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t) (hAsa : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T, IsMeasIn t T ∧ IsSummedSdp A T (∑ i, T i * A i) := by
  obtain ⟨T, hT, hmax⟩ := exists_isMaxOn_obj t ξ A
  exact ⟨T, hT, isSummedSdp_of_isMaxOn hS hT hA hAsa hmax⟩

/-- **Theorem 10 in the commutant as a `⋆`-subalgebra**: for finitely many self-adjoint `Aᵢ` of the
commutant, there is a measurement `T` of the commutant, in its own order (that of `B(H)`), with
`Z = ∑ᵢ Tᵢ Aᵢ` self-adjoint, `Aᵢ ≤ Z` and `Tᵢ Z = Tᵢ Aᵢ` for every `i`. -/
theorem exists_isSummedSdp_centralizer [Nonempty G] (hS : IsFaithfulTrace t ξ)
    (A : G → StarSubalgebra.centralizer ℂ t) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → StarSubalgebra.centralizer ℂ t, IsSummedSdp A T (∑ i, T i * A i) := by
  obtain ⟨T, hT, hsdp⟩ := exists_isSummedSdp hS (A := fun i => (A i : H →L[ℂ] H))
    (fun i => (A i).2) fun i => (hA i).map (StarSubalgebra.centralizer ℂ t).subtype
  refine ⟨fun i => ⟨T i, hT.mem i⟩, isSummedSdp_coe_iff.1 ?_⟩
  simpa using hsdp

/-- **A vector trace is a faithful trace on a commutant inside its set.** -/
theorem _root_.MIPRE.SummedSdp.IsFaithfulTrace.of_vecTrace {s : Set (H →L[ℂ] H)} (τ : VecTrace s)
    (h : ∀ x ∈ StarSubalgebra.centralizer ℂ t, x ∈ s) : IsFaithfulTrace t τ.g :=
  ⟨fun x hx y hy => τ.trace_mul_comm x (h x hx) y (h y hy),
    fun x hx => τ.separating x (h x hx)⟩

section FinitePair

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- **Theorem 10 for the first player of a finite pair**: in the commutant of the second player's
operators (which are the first player's operators), for finitely many self-adjoint `Aᵢ` there is
a measurement `T` with `Z = ∑ᵢ Tᵢ Aᵢ` self-adjoint, `Aᵢ ≤ Z` and `Tᵢ Z = Tᵢ Aᵢ`. -/
theorem exists_isSummedSdp_finitePairA (M : BipartiteModel 𝒞 𝒜 ℬ) (hM : M.IsFinitePair)
    [Nonempty G] (A : G → StarSubalgebra.centralizer ℂ M.opsB) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → StarSubalgebra.centralizer ℂ M.opsB, IsSummedSdp A T (∑ i, T i * A i) := by
  obtain ⟨τ⟩ := hM.traceA
  exact exists_isSummedSdp_centralizer (IsFaithfulTrace.of_vecTrace τ fun x hx =>
    hM.commutantA x fun b =>
      ((StarSubalgebra.mem_centralizer_iff ℂ).1 hx _ (Set.mem_range_self b)).1.symm) A hA

/-- **Theorem 10 for the second player of a finite pair**: in the commutant of the first player's
operators (which are the second player's operators), for finitely many self-adjoint `Aᵢ` there is
a measurement `T` with `Z = ∑ᵢ Tᵢ Aᵢ` self-adjoint, `Aᵢ ≤ Z` and `Tᵢ Z = Tᵢ Aᵢ`. -/
theorem exists_isSummedSdp_finitePairB (M : BipartiteModel 𝒞 𝒜 ℬ) (hM : M.IsFinitePair)
    [Nonempty G] (A : G → StarSubalgebra.centralizer ℂ M.opsA) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → StarSubalgebra.centralizer ℂ M.opsA, IsSummedSdp A T (∑ i, T i * A i) := by
  obtain ⟨τ⟩ := hM.traceB
  exact exists_isSummedSdp_centralizer (IsFaithfulTrace.of_vecTrace τ fun x hx =>
    hM.commutantB x fun a =>
      ((StarSubalgebra.mem_centralizer_iff ℂ).1 hx _ (Set.mem_range_self a)).1.symm) A hA

end FinitePair

end MIPRE.Orthonormalization

end
