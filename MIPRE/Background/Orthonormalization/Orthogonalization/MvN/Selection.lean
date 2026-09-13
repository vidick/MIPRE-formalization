/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Selection.lean
-/
/-
# The Krein–Milman step of Lemma 3.1: an extreme maximizer in a corner

Proof-side topology for tier T3 of the formalization of M. de la Salle,
*Orthogonalization of Positive Operator Valued Measures* (arXiv:2103.14126v2):
the first paragraph of the proof of Lemma 3.1 (Section 3). Inside the finite
corner `p M p`, with its center-valued trace `E`, and inside the corner `c M c`
of a central projection `c` of `p M p`, the set

  `C = {(x₁, …, xₙ) | xᵢ ∈ c M c, 0 ≤ xᵢ ≤ 1, xᵢ aᵢ = aᵢ xᵢ, ∑ᵢ E(xᵢ) = c}`

is convex, weak-operator closed (normality of `E` on bounded sets) and contained
in the unit ball of `(c M c)ⁿ`, hence weak-operator compact
(`Orthogonalization/MvN/WOTCompact.lean`); the affine functional
`f(x) = Re φ(∑ᵢ xᵢ aᵢ)` is continuous on it when `φ` is normal; so `f` attains
its maximum on `C`, the maximizing face is a compact extreme subset of `C`, and
the Krein–Milman lemma (`IsCompact.extremePoints_nonempty`) produces an extreme
point of `C` maximizing `f`. This file proves exactly that
(`exists_extreme_maximizer`), recording extremality in the coordinatewise form
consumed by the type II₁ and type I cases of the paper: no nonzero self-adjoint
`b ∈ c M c` commuting with `aᵢ` and with `E b = 0` keeps `xᵢ ± t b` in `[0, 1]`.

Normality of `φ` enters through the representation `φ = ∑ₖ ⟪gₖ, · gₖ⟫` on `M`
with `∑ ‖gₖ‖² < ∞` (hypothesis `hφg`, the trace-class form of `φ`, interface field H0),
which gives continuity along bounded
weak-operator convergent nets by Tannery's theorem
(`tendsto_of_tendstoWeakBdd`); normality of `E` enters through the field
`normal` of `IsCenterValuedTrace`.

Nothing in this file is a statement of the paper.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Defs
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.WOTCompact
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology ContinuousLinearMapWOT Blocks

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Preliminaries on the corners `c M c ⊆ p M p` -/

/-- A central element `c` of `p M p` satisfies `p c = c`. -/
theorem IsCentralIn.proj_mul_self {M : VonNeumannAlgebra H} {p c : H →L[ℂ] H}
    (hp : IsStarProjection p) (hcc : IsCentralIn M p c) : p * c = c := by
  have h := hcc.2.1
  calc p * c = p * (p * c * p) := by rw [h]
    _ = p * p * c * p := by simp only [mul_assoc]
    _ = c := by rw [hp.isIdempotentElem.eq, h]

/-- A central element `c` of `p M p` satisfies `c p = c`. -/
theorem IsCentralIn.self_mul_proj {M : VonNeumannAlgebra H} {p c : H →L[ℂ] H}
    (hp : IsStarProjection p) (hcc : IsCentralIn M p c) : c * p = c := by
  have h := hcc.2.1
  calc c * p = p * c * p * p := by rw [h]
    _ = p * c * (p * p) := by simp only [mul_assoc]
    _ = c := by rw [hp.isIdempotentElem.eq, h]

omit [CompleteSpace H] in
/-- An element of the corner `c M c` lies in the corner `p M p` when `p c = c = c p`. -/
theorem corner_of_corner {p c x : H →L[ℂ] H} (hpc : p * c = c) (hcp : c * p = c)
    (hx : c * x * c = x) : p * x * p = x := by
  calc p * x * p = p * (c * x * c) * p := by rw [hx]
    _ = (p * c) * x * (c * p) := by simp only [mul_assoc]
    _ = x := by rw [hpc, hcp, hx]

/-- Each term of a POVM summing to the projection `c` lies in the corner `c M c`. -/
theorem corner_of_sum_eq {n : ℕ} {a : Fin n → H →L[ℂ] H} {c : H →L[ℂ] H}
    (hc : IsStarProjection c) (ha0 : ∀ i, 0 ≤ a i) (hac : ∑ i, a i = c) (i : Fin n) :
    c * a i * c = a i := by
  have h1 : a i * c = a i := mul_eq_self_of_sum_eq hc ha0 hac i
  have h2 : c * a i = a i := by
    have := congrArg star h1
    rwa [star_mul, hc.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg (ha0 i)).star_eq] at this
  rw [h2, h1]

/-- Each term of a POVM summing to a projection is `≤ 1`. -/
theorem le_one_of_sum_eq {n : ℕ} {a : Fin n → H →L[ℂ] H} {c : H →L[ℂ] H}
    (hc : IsStarProjection c) (ha0 : ∀ i, 0 ≤ a i) (hac : ∑ i, a i = c) (i : Fin n) :
    a i ≤ 1 :=
  (le_of_sum_eq ha0 hac i).trans (sub_nonneg.mp hc.one_sub_nonneg)

/-! ### Normal functionals along bounded weak-operator convergent nets -/

/-- A functional of the form `x ↦ ∑ₖ ⟪gₖ, x gₖ⟫` on `M`, with `∑ ‖gₖ‖² < ∞`, is continuous
along bounded weak-operator convergent nets of `M` (Tannery's theorem). -/
theorem tendsto_of_tendstoWeakBdd_of_tsum {M : VonNeumannAlgebra H} {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    {g : ℕ → H} (hg : Summable fun k => ‖g k‖ ^ 2)
    (hφg : ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ)
    {κ : Type*} {l : Filter κ} {T : κ → H →L[ℂ] H} {L : H →L[ℂ] H}
    (hT : ∀ k, T k ∈ M) (hL : L ∈ M) (h : TendstoWeakBdd l T L) :
    Tendsto (fun k => φ (T k)) l (𝓝 (φ L)) := by
  obtain ⟨⟨C, hC⟩, hconv⟩ := h
  have hφT : (fun k => φ (T k)) = fun k => ∑' j, ⟪g j, T k (g j)⟫_ℂ :=
    funext fun k => hφg _ (hT k)
  rw [hφT, hφg L hL]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => C * ‖g j‖ ^ 2) (hg.mul_left C)
    (fun j => hconv (g j) (g j)) (Eventually.of_forall fun k j => ?_)
  calc ‖⟪g j, T k (g j)⟫_ℂ‖ ≤ ‖g j‖ * ‖T k (g j)‖ := norm_inner_le_norm _ _
    _ ≤ ‖g j‖ * (‖T k‖ * ‖g j‖) := by gcongr; exact (T k).le_opNorm _
    _ ≤ ‖g j‖ * (C * ‖g j‖) := by gcongr; exact hC k
    _ = C * ‖g j‖ ^ 2 := by ring

/-- **Bounded weak-operator continuity of a normal functional.** Under the representation
hypothesis `hH0` (a functional positive and normal on `M` is `∑ₖ ⟪gₖ, · gₖ⟫` on `M` with
`∑ ‖gₖ‖² < ∞`), such a functional is continuous along bounded weak-operator convergent
nets of `M`, indexed by any type. -/
theorem tendsto_of_tendstoWeakBdd {M : VonNeumannAlgebra H} {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hH0 : ∀ φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ, (∀ x ∈ M, 0 ≤ φ (star x * x)) → IsNormalOn M φ →
      ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ)
    (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) (hφn : IsNormalOn M φ)
    {κ : Type*} {l : Filter κ} {T : κ → H →L[ℂ] H} {L : H →L[ℂ] H}
    (hT : ∀ k, T k ∈ M) (hL : L ∈ M) (h : TendstoWeakBdd l T L) :
    Tendsto (fun k => φ (T k)) l (𝓝 (φ L)) := by
  obtain ⟨g, hg, hφg⟩ := hH0 φ hφ hφn
  exact tendsto_of_tendstoWeakBdd_of_tsum hg hφg hT hL h

/-! ### The constraint set `C` -/

/-- The one-coordinate constraint: `T ∈ c M c`, `0 ≤ T ≤ 1`, `T` commuting with `a`, as a set
of operators with the weak operator topology. -/
def coordSet (M : VonNeumannAlgebra H) (c a : H →L[ℂ] H) : Set (H →WOT[ℂ] H) :=
  {T | toCLM T ∈ M ∧ c * toCLM T * c = toCLM T ∧ 0 ≤ toCLM T ∧ toCLM T ≤ 1 ∧
    Commute (toCLM T) a}

theorem mem_coordSet {M : VonNeumannAlgebra H} {c a : H →L[ℂ] H} {T : H →WOT[ℂ] H} :
    T ∈ coordSet M c a ↔ toCLM T ∈ M ∧ c * toCLM T * c = toCLM T ∧ 0 ≤ toCLM T ∧
      toCLM T ≤ 1 ∧ Commute (toCLM T) a :=
  Iff.rfl

/-- `0 ≤ T ≤ 1` forces `‖T‖ ≤ 1`. -/
theorem norm_le_one_of_mem_coordSet {M : VonNeumannAlgebra H} {c a : H →L[ℂ] H}
    {T : H →WOT[ℂ] H} (h : T ∈ coordSet M c a) : ‖toCLM T‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ h.2.2.1).mpr h.2.2.2.1

/-- The one-coordinate constraint set is weak-operator closed. -/
theorem isClosed_coordSet (M : VonNeumannAlgebra H) (c a : H →L[ℂ] H) :
    IsClosed (coordSet M c a) := by
  have : coordSet M c a = {T : H →WOT[ℂ] H | toCLM T ∈ M} ∩
      ({T | c * toCLM T * c = toCLM T} ∩ ({T | 0 ≤ toCLM T} ∩
        ({T | toCLM T ≤ 1} ∩ {T | Commute (toCLM T) a}))) :=
    Set.ext fun _ => Iff.rfl
  rw [this]
  exact (isClosed_setOf_mem M).inter ((isClosed_setOf_mul_eq c c).inter
    (isClosed_setOf_nonneg.inter (isClosed_setOf_le_one.inter (isClosed_setOf_commute a))))

/-- The one-coordinate constraint set is convex. -/
theorem convex_coordSet (M : VonNeumannAlgebra H) (c a : H →L[ℂ] H) :
    Convex ℝ (coordSet M c a) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hxM, hxc, hx0, hx1, hxa⟩ := hx
  obtain ⟨hyM, hyc, hy0, hy1, hya⟩ := hy
  have e : toCLM (s • x + t • y) = s • toCLM x + t • toCLM y := by
    rw [toCLM_add, toCLM_smul, toCLM_smul]
  rw [mem_coordSet, e]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Complex.coe_smul, ← Complex.coe_smul]
    exact add_mem (smul_mem_vn M _ hxM) (smul_mem_vn M _ hyM)
  · rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hxc, hyc]
  · exact add_nonneg (smul_nonneg hs hx0) (smul_nonneg ht hy0)
  · calc s • toCLM x + t • toCLM y ≤ s • (1 : H →L[ℂ] H) + t • (1 : H →L[ℂ] H) :=
          add_le_add (smul_le_smul_of_nonneg_left hx1 hs) (smul_le_smul_of_nonneg_left hy1 ht)
      _ = 1 := by rw [← add_smul, hst, one_smul]
  · exact (hxa.smul_left s).add_left (hya.smul_left t)

/-- The box of tuples with every coordinate in the one-coordinate constraint set. -/
def coordBox (M : VonNeumannAlgebra H) (c : H →L[ℂ] H) {n : ℕ} (a : Fin n → H →L[ℂ] H) :
    Set (Fin n → (H →WOT[ℂ] H)) :=
  Set.univ.pi fun i => coordSet M c (a i)

theorem mem_coordBox {M : VonNeumannAlgebra H} {c : H →L[ℂ] H} {n : ℕ} {a : Fin n → H →L[ℂ] H}
    {x : Fin n → (H →WOT[ℂ] H)} : x ∈ coordBox M c a ↔ ∀ i, x i ∈ coordSet M c (a i) :=
  Set.mem_univ_pi

theorem isClosed_coordBox (M : VonNeumannAlgebra H) (c : H →L[ℂ] H) {n : ℕ}
    (a : Fin n → H →L[ℂ] H) : IsClosed (coordBox M c a) :=
  isClosed_set_pi fun i _ => isClosed_coordSet M c (a i)

/-- The set `C` of Lemma 3.1: tuples of the corner `c M c` with `0 ≤ xᵢ ≤ 1`, `xᵢ` commuting
with `aᵢ`, and `∑ᵢ E(xᵢ) = c`, as a subset of the product of weak-operator topologies. -/
def selectionSet (M : VonNeumannAlgebra H) (c : H →L[ℂ] H)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) {n : ℕ} (a : Fin n → H →L[ℂ] H) :
    Set (Fin n → (H →WOT[ℂ] H)) :=
  coordBox M c a ∩ {x | ∑ i, E (toCLM (x i)) = c}

theorem mem_selectionSet {M : VonNeumannAlgebra H} {c : H →L[ℂ] H}
    {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {n : ℕ} {a : Fin n → H →L[ℂ] H}
    {x : Fin n → (H →WOT[ℂ] H)} :
    x ∈ selectionSet M c E a ↔ x ∈ coordBox M c a ∧ ∑ i, E (toCLM (x i)) = c :=
  Iff.rfl

/-- `C` lies in the unit ball of the product. -/
theorem selectionSet_subset_pi_norm_le (M : VonNeumannAlgebra H) (c : H →L[ℂ] H)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) {n : ℕ} (a : Fin n → H →L[ℂ] H) :
    selectionSet M c E a ⊆ Set.univ.pi fun _ => {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ 1} :=
  fun _ hx i _ => norm_le_one_of_mem_coordSet (mem_coordBox.mp hx.1 i)

/-- `(a₁, …, aₙ)` belongs to `C`. -/
theorem ofCLM_mem_selectionSet (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    {c : H →L[ℂ] H} (hc : IsStarProjection c) (hcc : IsCentralIn M p c)
    {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} (hE : IsCenterValuedTrace M p E)
    {n : ℕ} {a : Fin n → H →L[ℂ] H} (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i)
    (hac : ∑ i, a i = c) : (fun i => ofCLM (a i)) ∈ selectionSet M c E a := by
  rw [mem_selectionSet, mem_coordBox]
  refine ⟨fun i => ?_, ?_⟩
  · rw [mem_coordSet, toCLM_ofCLM]
    exact ⟨haM i, corner_of_sum_eq hc ha0 hac i, ha0 i, le_one_of_sum_eq hc ha0 hac i,
      Commute.refl _⟩
  · show ∑ i, E (a i) = c
    rw [← map_sum, hac, hE.center_fixed c hcc]

/-- `C` is convex. -/
theorem convex_selectionSet (M : VonNeumannAlgebra H) (c : H →L[ℂ] H)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) {n : ℕ} (a : Fin n → H →L[ℂ] H) :
    Convex ℝ (selectionSet M c E a) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hxP, hxE⟩ := mem_selectionSet.mp hx
  obtain ⟨hyP, hyE⟩ := mem_selectionSet.mp hy
  rw [mem_selectionSet, mem_coordBox]
  refine ⟨fun i => convex_coordSet M c (a i) (mem_coordBox.mp hxP i) (mem_coordBox.mp hyP i)
    hs ht hst, ?_⟩
  have : ∀ i, E (toCLM ((s • x + t • y) i)) = s • E (toCLM (x i)) + t • E (toCLM (y i)) :=
    fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, toCLM_add, toCLM_smul, map_add,
        LinearMap.map_smul_of_tower]
  simp only [this, Finset.sum_add_distrib, ← Finset.smul_sum, hxE, hyE, ← add_smul, hst, one_smul]

/-- **`C` is weak-operator closed.** For `x` in the closure of `C`, the truncated coordinate
nets `y ↦ yᵢ` (along the trace of `𝓝 x` on `C`) are bounded and weak-operator convergent to
`xᵢ`, so by normality of `E` the nets `E(yᵢ)` converge weakly to `E(xᵢ)`; summing, the constant
value `c` of `∑ᵢ E(yᵢ)` on `C` is the weak limit `∑ᵢ E(xᵢ)`. -/
theorem isClosed_selectionSet (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) {c : H →L[ℂ] H} (hcc : IsCentralIn M p c)
    {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} (hE : IsCenterValuedTrace M p E)
    {n : ℕ} (a : Fin n → H →L[ℂ] H) : IsClosed (selectionSet M c E a) := by
  have hpc : p * c = c := hcc.proj_mul_self hp
  have hcp : c * p = c := hcc.self_mul_proj hp
  refine isClosed_of_closure_subset fun x hx => ?_
  have : (𝓝[selectionSet M c E a] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hxP : x ∈ coordBox M c a :=
    (isClosed_coordBox M c a).closure_subset
      (closure_mono (fun y hy => (mem_selectionSet.mp hy).1) hx)
  have hCl : selectionSet M c E a ∈ 𝓝[selectionSet M c E a] x := self_mem_nhdsWithin
  rw [mem_selectionSet]
  refine ⟨hxP, ?_⟩
  -- the truncated coordinate nets
  have hTmem : ∀ i (y : Fin n → (H →WOT[ℂ] H)),
      (coordBox M c a).indicator (fun y => toCLM (y i)) y ∈ M ∧
        p * (coordBox M c a).indicator (fun y => toCLM (y i)) y * p =
          (coordBox M c a).indicator (fun y => toCLM (y i)) y := by
    intro i y
    by_cases hy : y ∈ coordBox M c a
    · rw [Set.indicator_of_mem hy]
      have h := mem_coordBox.mp hy i
      exact ⟨h.1, corner_of_corner hpc hcp h.2.1⟩
    · rw [Set.indicator_of_notMem hy]
      exact ⟨zero_mem _, by simp⟩
  have hTw : ∀ i, TendstoWeakBdd (𝓝[selectionSet M c E a] x)
      ((coordBox M c a).indicator fun y => toCLM (y i)) (toCLM (x i)) := by
    intro i
    refine ⟨⟨1, fun y => ?_⟩, fun ξ η => ?_⟩
    · by_cases hy : y ∈ coordBox M c a
      · rw [Set.indicator_of_mem hy]
        exact norm_le_one_of_mem_coordSet (mem_coordBox.mp hy i)
      · rw [Set.indicator_of_notMem hy, norm_zero]
        exact zero_le_one
    · have hc : Continuous fun y : Fin n → (H →WOT[ℂ] H) => ⟪ξ, toCLM (y i) η⟫_ℂ :=
        (MvN.continuous_inner_apply ξ η).comp (continuous_apply i)
      refine ((hc.tendsto x).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hCl] with y hy
      rw [Set.indicator_of_mem (mem_selectionSet.mp hy).1]
  have hEw : ∀ i, TendstoWeakBdd (𝓝[selectionSet M c E a] x)
      (fun y => E ((coordBox M c a).indicator (fun y => toCLM (y i)) y)) (E (toCLM (x i))) :=
    fun i =>
      hE.normal _ _ _ (hTmem i) (mem_coordBox.mp hxP i).1
        (corner_of_corner hpc hcp (mem_coordBox.mp hxP i).2.1) (hTw i)
  have hlim : ∀ ξ η : H,
      Tendsto (fun y => ⟪ξ, (∑ i, E ((coordBox M c a).indicator (fun y => toCLM (y i)) y)) η⟫_ℂ)
        (𝓝[selectionSet M c E a] x) (𝓝 ⟪ξ, (∑ i, E (toCLM (x i))) η⟫_ℂ) := by
    intro ξ η
    simp only [sum_apply, inner_sum]
    exact tendsto_finsetSum _ fun i _ => (hEw i).2 ξ η
  have hconst : ∀ ξ η : H,
      Tendsto (fun y => ⟪ξ, (∑ i, E ((coordBox M c a).indicator (fun y => toCLM (y i)) y)) η⟫_ℂ)
        (𝓝[selectionSet M c E a] x) (𝓝 ⟪ξ, c η⟫_ℂ) := by
    intro ξ η
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hCl] with y hy
    have : ∑ i, E ((coordBox M c a).indicator (fun y => toCLM (y i)) y) = c := by
      simp only [Set.indicator_of_mem (mem_selectionSet.mp hy).1]
      exact (mem_selectionSet.mp hy).2
    rw [this]
  refine ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => ?_
  exact tendsto_nhds_unique (hlim ξ η) (hconst ξ η)

/-- **`C` is weak-operator compact**: closed and contained in the unit ball of the product,
which is compact by `isCompact_setOf_norm_le`. -/
theorem isCompact_selectionSet (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) {c : H →L[ℂ] H} (hcc : IsCentralIn M p c)
    {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} (hE : IsCenterValuedTrace M p E)
    {n : ℕ} (a : Fin n → H →L[ℂ] H) : IsCompact (selectionSet M c E a) :=
  (isCompact_univ_pi fun _ => isCompact_setOf_norm_le 1).of_isClosed_subset
    (isClosed_selectionSet M hp hcc hE a) (selectionSet_subset_pi_norm_le M c E a)

/-! ### The objective `x ↦ Re φ(∑ᵢ xᵢ aᵢ)` -/

/-- The objective functional of Lemma 3.1 on the product of weak-operator topologies. -/
def objective (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) {n : ℕ} (a : Fin n → H →L[ℂ] H)
    (x : Fin n → (H →WOT[ℂ] H)) : ℝ :=
  (φ (∑ i, toCLM (x i) * a i)).re

omit [CompleteSpace H] in
/-- The objective is affine. -/
theorem objective_affine (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) {n : ℕ} (a : Fin n → H →L[ℂ] H)
    (x y : Fin n → (H →WOT[ℂ] H)) (s t : ℝ) :
    objective φ a (s • x + t • y) = s * objective φ a x + t * objective φ a y := by
  simp only [objective, Pi.add_apply, Pi.smul_apply, toCLM_add, toCLM_smul, add_mul,
    smul_mul_assoc, Finset.sum_add_distrib, ← Finset.smul_sum, map_add,
    LinearMap.map_smul_of_tower, Complex.add_re, Complex.smul_re, smul_eq_mul]

/-- **The objective is continuous on `C`** for a normal `φ`: along the trace of `𝓝 x` on `C`,
the net `∑ᵢ yᵢ aᵢ` is bounded, in `M`, and weak-operator convergent to `∑ᵢ xᵢ aᵢ`. -/
theorem continuousOn_objective {M : VonNeumannAlgebra H} {c : H →L[ℂ] H}
    {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {n : ℕ} {a : Fin n → H →L[ℂ] H} (haM : ∀ i, a i ∈ M)
    {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ) :
    ContinuousOn (objective φ a) (selectionSet M c E a) := by
  obtain ⟨g, hg, hφg⟩ := hφg
  intro x hx
  show Tendsto (objective φ a) (𝓝[selectionSet M c E a] x) (𝓝 (objective φ a x))
  have hCl : selectionSet M c E a ∈ 𝓝[selectionSet M c E a] x := self_mem_nhdsWithin
  have hxP : x ∈ coordBox M c a := (mem_selectionSet.mp hx).1
  have hTmem : ∀ y : Fin n → (H →WOT[ℂ] H),
      (coordBox M c a).indicator (fun y => ∑ i, toCLM (y i) * a i) y ∈ M := by
    intro y
    by_cases hy : y ∈ coordBox M c a
    · rw [Set.indicator_of_mem hy]
      exact sum_mem fun i _ => mul_mem (mem_coordBox.mp hy i).1 (haM i)
    · rw [Set.indicator_of_notMem hy]
      exact zero_mem _
  have hL : ∑ i, toCLM (x i) * a i ∈ M :=
    sum_mem fun i _ => mul_mem (mem_coordBox.mp hxP i).1 (haM i)
  have hTw : TendstoWeakBdd (𝓝[selectionSet M c E a] x)
      ((coordBox M c a).indicator fun y => ∑ i, toCLM (y i) * a i) (∑ i, toCLM (x i) * a i) := by
    refine ⟨⟨∑ i, ‖a i‖, fun y => ?_⟩, fun ξ η => ?_⟩
    · by_cases hy : y ∈ coordBox M c a
      · rw [Set.indicator_of_mem hy]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        calc ‖toCLM (y i) * a i‖ ≤ ‖toCLM (y i)‖ * ‖a i‖ := norm_mul_le _ _
          _ ≤ 1 * ‖a i‖ := by
              gcongr
              exact norm_le_one_of_mem_coordSet (mem_coordBox.mp hy i)
          _ = ‖a i‖ := one_mul _
      · rw [Set.indicator_of_notMem hy, norm_zero]
        positivity
    · have hc : ∀ i, Continuous fun y : Fin n → (H →WOT[ℂ] H) => ⟪ξ, toCLM (y i) (a i η)⟫_ℂ :=
        fun i => (MvN.continuous_inner_apply ξ (a i η)).comp (continuous_apply i)
      have h1 : Tendsto (fun y : Fin n → (H →WOT[ℂ] H) => ∑ i, ⟪ξ, toCLM (y i) (a i η)⟫_ℂ)
          (𝓝[selectionSet M c E a] x) (𝓝 (∑ i, ⟪ξ, toCLM (x i) (a i η)⟫_ℂ)) :=
        tendsto_finsetSum _ fun i _ => ((hc i).tendsto x).mono_left nhdsWithin_le_nhds
      simp only [sum_apply, inner_sum, mul_apply_eq_comp]
      refine h1.congr' ?_
      filter_upwards [hCl] with y hy
      rw [Set.indicator_of_mem (mem_selectionSet.mp hy).1]
      simp only [sum_apply, inner_sum, mul_apply_eq_comp]
  have h2 := tendsto_of_tendstoWeakBdd_of_tsum hg hφg hTmem hL hTw
  refine ((Complex.continuous_re.tendsto _).comp h2).congr' ?_
  filter_upwards [hCl] with y hy
  simp only [Function.comp_def, Set.indicator_of_mem (mem_selectionSet.mp hy).1, objective]

/-! ### Perturbing one coordinate -/

/-- The tuple `e` with its `i`-th coordinate replaced by `eᵢ + t b`. -/
def perturb {n : ℕ} (e : Fin n → (H →WOT[ℂ] H)) (i : Fin n) (b : H →L[ℂ] H) (t : ℝ) :
    Fin n → (H →WOT[ℂ] H) :=
  Function.update e i (ofCLM (toCLM (e i) + (t : ℂ) • b))

omit [CompleteSpace H] in
theorem perturb_apply_self {n : ℕ} (e : Fin n → (H →WOT[ℂ] H)) (i : Fin n) (b : H →L[ℂ] H)
    (t : ℝ) : perturb e i b t i = ofCLM (toCLM (e i) + (t : ℂ) • b) := by
  simp only [perturb, Function.update_self]

omit [CompleteSpace H] in
theorem perturb_apply_of_ne {n : ℕ} (e : Fin n → (H →WOT[ℂ] H)) {i j : Fin n} (hji : j ≠ i)
    (b : H →L[ℂ] H) (t : ℝ) : perturb e i b t j = e j := by
  simp only [perturb, Function.update_of_ne hji]

omit [CompleteSpace H] in
/-- `e` is the midpoint of its two perturbations `e ± t b`. -/
theorem midpoint_perturb {n : ℕ} (e : Fin n → (H →WOT[ℂ] H)) (i : Fin n) (b : H →L[ℂ] H)
    (t : ℝ) : (1 / 2 : ℝ) • perturb e i b (-t) + (1 / 2 : ℝ) • perturb e i b t = e := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply]
  by_cases hji : j = i
  · rw [hji, perturb_apply_self, perturb_apply_self]
    apply toCLM_injective
    rw [toCLM_add, toCLM_smul, toCLM_smul, toCLM_ofCLM, toCLM_ofCLM, ← Complex.coe_smul,
      ← Complex.coe_smul]
    push_cast
    module
  · rw [perturb_apply_of_ne e hji, perturb_apply_of_ne e hji]
    apply toCLM_injective
    rw [toCLM_add, toCLM_smul, ← add_smul]
    norm_num

omit [CompleteSpace H] in
/-- Sums over a tuple with one coordinate replaced. -/
theorem sum_map_update {n : ℕ} (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (e : Fin n → (H →WOT[ℂ] H)) (i : Fin n) (v : H →WOT[ℂ] H) :
    ∑ j, E (toCLM (Function.update e i v j)) =
      ∑ j, E (toCLM (e j)) + (E (toCLM v) - E (toCLM (e i))) := by
  rw [← Finset.add_sum_erase Finset.univ (fun j => E (toCLM (Function.update e i v j)))
    (Finset.mem_univ i), ← Finset.add_sum_erase Finset.univ (fun j => E (toCLM (e j)))
    (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, E (toCLM (Function.update e i v j)) =
      ∑ j ∈ Finset.univ.erase i, E (toCLM (e j)) :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  abel

/-- A perturbation `e + t b` along a self-adjoint `b ∈ c M c` commuting with `aᵢ`, with
`E b = 0` and keeping the `i`-th coordinate in `[0, 1]`, stays in `C`. -/
theorem perturb_mem_selectionSet {M : VonNeumannAlgebra H} {c : H →L[ℂ] H}
    {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {n : ℕ} {a : Fin n → H →L[ℂ] H}
    {e : Fin n → (H →WOT[ℂ] H)} (he : e ∈ selectionSet M c E a) (i : Fin n)
    {b : H →L[ℂ] H} (hbM : b ∈ M) (hbc : c * b * c = b) (hba : Commute b (a i)) (hEb : E b = 0)
    (t : ℝ) (h0 : 0 ≤ toCLM (e i) + (t : ℂ) • b) (h1 : toCLM (e i) + (t : ℂ) • b ≤ 1) :
    perturb e i b t ∈ selectionSet M c E a := by
  obtain ⟨heP, heE⟩ := mem_selectionSet.mp he
  rw [mem_selectionSet, mem_coordBox]
  refine ⟨fun j => ?_, ?_⟩
  · by_cases hji : j = i
    · rw [hji, perturb_apply_self, mem_coordSet, toCLM_ofCLM]
      obtain ⟨hM, hcorner, -, -, hcomm⟩ := mem_coordBox.mp heP i
      refine ⟨add_mem hM (smul_mem_vn M _ hbM), ?_, h0, h1, hcomm.add_left (hba.smul_left _)⟩
      rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hcorner, hbc]
    · rw [perturb_apply_of_ne e hji]
      exact mem_coordBox.mp heP j
  · rw [perturb, sum_map_update, heE, toCLM_ofCLM, map_add, map_smul, hEb, smul_zero, add_zero,
      sub_self, add_zero]

/-! ### The Krein–Milman step -/

-- The hypothesis `hpM : p ∈ M` belongs to the fixed interface of the finite corner `p M p` and
-- is not needed for this step; the statement is kept verbatim.
set_option linter.unusedVariables false in
/-- **The Krein–Milman step of Lemma 3.1** (paper, Section 3): on the corner `c M c` of the
finite corner `p M p` with center-valued trace `E`, the set `C` of tuples `(xᵢ)` of `c M c` with
`0 ≤ xᵢ ≤ 1`, `xᵢ` commuting with `aᵢ` and `∑ E(xᵢ) = c` is weak-operator compact and convex, the
functional `x ↦ φ(∑ xᵢ aᵢ)` is continuous on it, and an extreme point of the maximizing face
exists; extremality is recorded coordinatewise: no nonzero self-adjoint `b ∈ c M c` commuting with
`aᵢ` with `E b = 0` keeps `xᵢ ± t b` in `[0, 1]` for small `t`. -/
theorem exists_extreme_maximizer (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M)
    {c : H →L[ℂ] H} (hc : IsStarProjection c) (hcc : IsCentralIn M p c)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hE : IsCenterValuedTrace M p E)
    {n : ℕ} (a : Fin n → H →L[ℂ] H) (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i)
    (hac : ∑ i, a i = c)
    (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ) :
    ∃ x : Fin n → H →L[ℂ] H,
      (∀ i, x i ∈ M ∧ c * x i * c = x i ∧ 0 ≤ x i ∧ x i ≤ 1 ∧ Commute (x i) (a i)) ∧
      ∑ i, E (x i) = c ∧
      (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, x i * a i)).re ∧
      ∀ i (b : H →L[ℂ] H), b ∈ M → c * b * c = b → IsSelfAdjoint b → Commute b (a i) →
        E b = 0 →
        (∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| ≤ t₀ → 0 ≤ x i + (t : ℂ) • b ∧ x i + (t : ℂ) • b ≤ 1) →
        b = 0 := by
  have hclosed : IsClosed (selectionSet M c E a) := isClosed_selectionSet M hp hcc hE a
  have hcomp : IsCompact (selectionSet M c E a) := isCompact_selectionSet M hp hcc hE a
  have hamem : (fun i => ofCLM (a i)) ∈ selectionSet M c E a :=
    ofCLM_mem_selectionSet M hc hcc hE haM ha0 hac
  have hcont : ContinuousOn (objective φ a) (selectionSet M c E a) :=
    continuousOn_objective haM hφg
  -- a maximizer and the maximizing face
  obtain ⟨x₀, hx₀S, hx₀max⟩ := hcomp.exists_isMaxOn ⟨_, hamem⟩ hcont
  have hmax : ∀ y ∈ selectionSet M c E a, objective φ a y ≤ objective φ a x₀ :=
    isMaxOn_iff.mp hx₀max
  have hFclosed : IsClosed (selectionSet M c E a ∩ objective φ a ⁻¹' {objective φ a x₀}) :=
    hcont.preimage_isClosed_of_isClosed hclosed isClosed_singleton
  have hFcomp : IsCompact (selectionSet M c E a ∩ objective φ a ⁻¹' {objective φ a x₀}) :=
    hcomp.of_isClosed_subset hFclosed Set.inter_subset_left
  have hFne : (selectionSet M c E a ∩ objective φ a ⁻¹' {objective φ a x₀}).Nonempty :=
    ⟨x₀, hx₀S, rfl⟩
  have hFext : IsExtreme ℝ (selectionSet M c E a)
      (selectionSet M c E a ∩ objective φ a ⁻¹' {objective φ a x₀}) := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro x₁ hx₁ x₂ hx₂ z hz hzseg
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hzseg
    refine ⟨hx₁, ?_⟩
    have hz' : objective φ a (s • x₁ + t • x₂) = objective φ a x₀ := hz.2
    rw [objective_affine] at hz'
    have h1 : objective φ a x₁ ≤ objective φ a x₀ := hmax x₁ hx₁
    have h2 : objective φ a x₂ ≤ objective φ a x₀ := hmax x₂ hx₂
    have h3 : t * objective φ a x₂ ≤ t * objective φ a x₀ := mul_le_mul_of_nonneg_left h2 ht.le
    have h4 : s * objective φ a x₀ + t * objective φ a x₀ = objective φ a x₀ := by
      rw [← add_mul, hst, one_mul]
    have h5 : s * objective φ a x₀ ≤ s * objective φ a x₁ := by linarith
    have h6 : objective φ a x₀ ≤ objective φ a x₁ := le_of_mul_le_mul_left h5 hs
    show objective φ a x₁ = objective φ a x₀
    exact le_antisymm h1 h6
  -- Krein–Milman on the face
  obtain ⟨e, heF⟩ := hFcomp.extremePoints_nonempty hFne
  have heS : e ∈ (selectionSet M c E a).extremePoints ℝ :=
    hFext.extremePoints_subset_extremePoints heF
  obtain ⟨heS', hext⟩ := mem_extremePoints.mp heS
  obtain ⟨heP, heE⟩ := mem_selectionSet.mp heS'
  refine ⟨fun i => toCLM (e i), fun i => mem_coordSet.mp (mem_coordBox.mp heP i), heE, ?_, ?_⟩
  · -- the maximum is at least the value at `(a₁, …, aₙ)`
    have h1 : objective φ a (fun i => ofCLM (a i)) ≤ objective φ a x₀ := hmax _ hamem
    have h2 : objective φ a e = objective φ a x₀ := heF.1.2
    show objective φ a (fun i => ofCLM (a i)) ≤ objective φ a e
    rw [h2]
    exact h1
  · -- extremality, coordinatewise
    intro i b hbM hbc _ hba hEb ⟨t₀, ht₀, ht⟩
    have hmem : ∀ t : ℝ, |t| ≤ t₀ → perturb e i b t ∈ selectionSet M c E a := fun t htt =>
      perturb_mem_selectionSet heS' i hbM hbc hba hEb t (ht t htt).1 (ht t htt).2
    have hseg : e ∈ openSegment ℝ (perturb e i b (-t₀)) (perturb e i b t₀) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, midpoint_perturb e i b t₀⟩
    have hyeq : perturb e i b t₀ = e :=
      (hext _ (hmem (-t₀) (by rw [abs_neg, abs_of_pos ht₀])) _
        (hmem t₀ (by rw [abs_of_pos ht₀])) hseg).2
    have hi : toCLM (perturb e i b t₀ i) = toCLM (e i) := congrArg toCLM (congrFun hyeq i)
    rw [perturb_apply_self, toCLM_ofCLM] at hi
    have h0 : (t₀ : ℂ) • b = 0 := add_left_cancel (hi.trans (add_zero _).symm)
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd (Complex.ofReal_eq_zero.mp h) ht₀.ne'
    · exact h

end Orthogonalization.MvN
