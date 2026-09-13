/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Finite.lean
-/
/-
# Tier T3, the finite case: Lemma 3.1 ⇒ Theorem 1.2 at a finite projection

The glue of Section 3 of the paper, relative to a finite projection `p` of `M`
(the corner `p M p` is the paper's finite algebra, `E` its center-valued trace):

* `exists_selection_typeII₁`: **Lemma 3.1 on the type II₁ part** — the extreme
  maximizer of `MvN/Selection.lean` is made of projections by the perturbation
  of `MvN/Perturb.lean` (for `φ` given in the trace-class form of field H0);
* `selection_of_split` / `hasSelection_of_split`: Lemma 3.1 at `p` from Lemma
  3.1 on the type I part `c M c` (interface field H5) and on the type II₁ part
  `(p − c) M (p − c)`, `c` a central projection of `p M p`;
* `exists_pvm_bound_of_selection` / `orthAtN_fin_of_hasSelection`: from Lemma
  3.1 at `p`, Lemma 3.2 in `M_n(M)` (`MvN/Polar.lean`) and the three-term
  estimate (`MvN/AssemblyRel.lean`), Theorem 1.2 at `p` for the functionals
  normal on `M` (the pointwise forms, for a fixed functional, serve tier T4a);
* `orthAtN_fin_of_isFiniteProj`: the finite case of Theorem 1.2 under the
  interface `MvNStructureTheory` (fields H0, H1', H3, H5, H6).

Proof-side only; no statement of the paper.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Polar
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.AssemblyRel
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Selection
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Perturb
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Interface

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology CommutingRepetition.VN Blocks FinDim

universe u

-- instance search for `CFC.sqrt` on `H^n` (as in `MvN/BlockCalc.lean`)
set_option synthInstance.maxHeartbeats 100000

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A projection is `≤ 1`. -/
theorem proj_le_one {p : H →L[ℂ] H} (hp : IsStarProjection p) : p ≤ 1 := by
  have h := star_mul_self_nonneg (1 - p)
  rw [hp.one_sub.isSelfAdjoint.star_eq, hp.one_sub.isIdempotentElem.eq] at h
  exact le_of_nonneg_sub h

/-- **Lemma 3.1 at `p`** as a predicate: for every POVM `(aᵢ)` of the corner `p M p` and
every functional positive on `M` and normal, there are projections `qᵢ ≤ p` of `M`
commuting with `aᵢ`, with `∑ E(qᵢ) = p` and `φ(∑ aᵢ²) ≤ φ(∑ qᵢ aᵢ)`. -/
def HasSelection (M : VonNeumannAlgebra H) (p : H →L[ℂ] H)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (n : ℕ) : Prop :=
  ∀ (a : Fin n → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) → ∑ i, a i = p →
    ∀ φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ, (∀ x ∈ M, 0 ≤ φ (star x * x)) → IsNormalOn M φ →
      ∃ q : Fin n → H →L[ℂ] H,
        (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * p = q i ∧ Commute (q i) (a i)) ∧
        ∑ i, E (q i) = p ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re

/-! ### Lemma 3.1 on the type II₁ part -/

/-- **Lemma 3.1 on the type II₁ part** (paper, Section 3, "The latter case is easier"):
the extreme maximizer of `exists_extreme_maximizer` consists of projections, since a
non-projection coordinate admits the perturbation of `exists_perturbation`. -/
theorem exists_selection_typeII₁ (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M)
    {c : H →L[ℂ] H} (hc : IsStarProjection c) (hcc : IsCentralIn M p c)
    (hII : ∀ r, IsAbelianProj M r → r * c = r → r = 0)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hE : IsCenterValuedTrace M p E)
    {n : ℕ} (a : Fin n → H →L[ℂ] H) (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i)
    (hac : ∑ i, a i = c)
    (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ) :
    ∃ q : Fin n → H →L[ℂ] H,
      (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * c = q i ∧ Commute (q i) (a i)) ∧
      ∑ i, E (q i) = c ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re := by
  obtain ⟨x, hx, hxE, hxineq, hext⟩ :=
    exists_extreme_maximizer M hp hpM hc hcc E hE a haM ha0 hac φ hφg
  have hac' : ∀ i, a i * c = a i := mul_eq_self_of_sum_eq hc ha0 hac
  have hca : ∀ i, c * a i = a i := fun i => by
    have := congrArg star (hac' i)
    rwa [star_mul, hc.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg (ha0 i)).star_eq] at this
  have hcac : ∀ i, c * a i * c = a i := fun i => by rw [hca i, hac' i]
  refine ⟨x, fun i => ⟨?_, (hx i).1, ?_, (hx i).2.2.2.2⟩, hxE, hxineq⟩
  · by_contra hne
    obtain ⟨b, hb0, hbM, hbc, hbsa, hba, hbE, ht⟩ :=
      exists_perturbation M hp hpM hc hcc hII E hE (haM i) (hcac i) (ha0 i) (hx i).1
        (hx i).2.1 (hx i).2.2.1 (hx i).2.2.2.1 (hx i).2.2.2.2 hne
    exact hb0 (hext i b hbM hbc hbsa hba hbE ht)
  · -- `x i ≤ c`: `x i = c * x i * c` gives `x i * c = x i`
    have := (hx i).2.1
    calc x i * c = c * x i * c * c := by rw [this]
      _ = c * x i * c := by rw [mul_assoc, hc.isIdempotentElem.eq]
      _ = x i := this

/-! ### Lemma 3.1 at `p` from the split `p = c + (p − c)` -/

/-- **Lemma 3.1 at `p` for a fixed functional `φ`** from Lemma 3.1 on the type I part
`c M c` (`hI`) and on the type II₁ part `(p − c) M (p − c)` (`hII`), for a central
projection `c` of `p M p`: the two families of projections are added. -/
theorem selection_of_split (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M) (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    {c : H →L[ℂ] H} (hc : IsStarProjection c) (hcc : IsCentralIn M p c)
    (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hI : ∀ (n : ℕ) (a : Fin n → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) →
      ∑ i, a i = c →
      ∃ q : Fin n → H →L[ℂ] H,
        (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * c = q i ∧ Commute (q i) (a i)) ∧
        ∑ i, E (q i) = c ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re)
    (hII : ∀ (n : ℕ) (a : Fin n → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) →
      ∑ i, a i = p - c →
      ∃ q : Fin n → H →L[ℂ] H,
        (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * (p - c) = q i ∧ Commute (q i) (a i)) ∧
        ∑ i, E (q i) = p - c ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re)
    (n : ℕ) (a : Fin n → H →L[ℂ] H) (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i)
    (hap : ∑ i, a i = p) :
    ∃ q : Fin n → H →L[ℂ] H,
      (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * p = q i ∧ Commute (q i) (a i)) ∧
      ∑ i, E (q i) = p ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re := by
  -- `c ≤ p`, `p − c` a projection
  have hpcp : p * c * p = c := hcc.2.1
  have hcp : c * p = c := by
    calc c * p = p * c * p * p := by rw [hpcp]
      _ = p * c * p := by rw [mul_assoc, hp.isIdempotentElem.eq]
      _ = c := hpcp
  have hpc : p * c = c := proj_mul_left_of_mul_right hc hp hcp
  have hd : IsStarProjection (p - c) := isStarProjection_sub_of_le hp hc hcp hpc
  have hdp : (p - c) * p = p - c := by rw [sub_mul, hp.isIdempotentElem.eq, hcp]
  have hcd : c * (p - c) = 0 := by rw [mul_sub, hcp, hc.isIdempotentElem.eq, sub_self]
  have hdc : (p - c) * c = 0 := by rw [sub_mul, hpc, hc.isIdempotentElem.eq, sub_self]
  -- the `aᵢ` lie in `p M p` and commute with `c` and `p − c`
  have hap' : ∀ i, a i * p = a i := mul_eq_self_of_sum_eq hp ha0 hap
  have hpa : ∀ i, p * a i = a i := fun i => by
    have := congrArg star (hap' i)
    rwa [star_mul, hp.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg (ha0 i)).star_eq] at this
  have hpap : ∀ i, p * a i * p = a i := fun i => by rw [hpa i, hap' i]
  have hca : ∀ i, Commute c (a i) := fun i => hcc.2.2 (a i) (haM i) (hpap i)
  have hpa' : ∀ i, Commute p (a i) := fun i => by
    show p * a i = a i * p
    rw [hpa i, hap' i]
  have hda : ∀ i, Commute (p - c) (a i) := fun i => (hpa' i).sub_left (hca i)
  -- the two POVMs
  set a₁ : Fin n → H →L[ℂ] H := fun i => c * a i with ha₁
  set a₂ : Fin n → H →L[ℂ] H := fun i => (p - c) * a i with ha₂
  have ha₁M : ∀ i, a₁ i ∈ M := fun i => mul_mem hcc.1 (haM i)
  have ha₂M : ∀ i, a₂ i ∈ M := fun i => mul_mem (sub_mem hpM hcc.1) (haM i)
  have ha₁0 : ∀ i, 0 ≤ a₁ i := fun i =>
    Orthogonalization.IsStarProjection.mul_nonneg_of_commute hc (ha0 i) (hca i)
  have ha₂0 : ∀ i, 0 ≤ a₂ i := fun i =>
    Orthogonalization.IsStarProjection.mul_nonneg_of_commute hd (ha0 i) (hda i)
  have ha₁sum : ∑ i, a₁ i = c := by
    simp only [ha₁]
    rw [← Finset.mul_sum, hap, hcp]
  have ha₂sum : ∑ i, a₂ i = p - c := by
    simp only [ha₂]
    rw [← Finset.mul_sum, hap, hdp]
  obtain ⟨q₁, hq₁, hq₁E, hq₁ineq⟩ := hI n a₁ ha₁M ha₁0 ha₁sum
  obtain ⟨q₂, hq₂, hq₂E, hq₂ineq⟩ := hII n a₂ ha₂M ha₂0 ha₂sum
  have hcq₁ : ∀ i, c * q₁ i = q₁ i := fun i =>
    proj_mul_left_of_mul_right (hq₁ i).1 hc (hq₁ i).2.2.1
  have hdq₂ : ∀ i, (p - c) * q₂ i = q₂ i := fun i =>
    proj_mul_left_of_mul_right (hq₂ i).1 hd (hq₂ i).2.2.1
  have hq₁q₂ : ∀ i, q₁ i * q₂ i = 0 := fun i => by
    rw [← (hq₁ i).2.2.1, ← hdq₂ i, mul_assoc, ← mul_assoc c, hcd, zero_mul, mul_zero]
  have hq₂q₁ : ∀ i, q₂ i * q₁ i = 0 := fun i => by
    rw [← (hq₂ i).2.2.1, ← hcq₁ i, mul_assoc, ← mul_assoc (p - c), hdc, zero_mul, mul_zero]
  -- commutation with `aᵢ`
  have hq₁a : ∀ i, Commute (q₁ i) (a i) := fun i => by
    have h := (hq₁ i).2.2.2
    show q₁ i * a i = a i * q₁ i
    calc q₁ i * a i = q₁ i * (c * a i) := by rw [← mul_assoc, (hq₁ i).2.2.1]
      _ = c * a i * q₁ i := h.eq
      _ = a i * (c * q₁ i) := by rw [(hca i).eq, mul_assoc]
      _ = a i * q₁ i := by rw [hcq₁ i]
  have hq₂a : ∀ i, Commute (q₂ i) (a i) := fun i => by
    have h := (hq₂ i).2.2.2
    show q₂ i * a i = a i * q₂ i
    calc q₂ i * a i = q₂ i * ((p - c) * a i) := by rw [← mul_assoc, (hq₂ i).2.2.1]
      _ = (p - c) * a i * q₂ i := h.eq
      _ = a i * ((p - c) * q₂ i) := by rw [(hda i).eq, mul_assoc]
      _ = a i * q₂ i := by rw [hdq₂ i]
  refine ⟨fun i => q₁ i + q₂ i, fun i => ⟨⟨?_, ?_⟩, add_mem (hq₁ i).2.1 (hq₂ i).2.1, ?_,
    (hq₁a i).add_left (hq₂a i)⟩, ?_, ?_⟩
  · show (q₁ i + q₂ i) * (q₁ i + q₂ i) = q₁ i + q₂ i
    rw [add_mul, mul_add, mul_add, (hq₁ i).1.isIdempotentElem.eq, (hq₂ i).1.isIdempotentElem.eq,
      hq₁q₂ i, hq₂q₁ i, add_zero, zero_add]
  · rw [IsSelfAdjoint, star_add, (hq₁ i).1.isSelfAdjoint.star_eq, (hq₂ i).1.isSelfAdjoint.star_eq]
  · rw [add_mul]
    congr 1
    · rw [← (hq₁ i).2.2.1, mul_assoc, hcp]
    · rw [← (hq₂ i).2.2.1, mul_assoc, hdp]
  · simp only [map_add, Finset.sum_add_distrib, hq₁E, hq₂E, add_sub_cancel]
  · -- the inequality: split `aᵢ² = (c aᵢ)² + ((p − c) aᵢ)²` and `qᵢ aᵢ = q₁ᵢ (c aᵢ) + q₂ᵢ ((p − c) aᵢ)`
    have hsq : ∑ i, a i * a i = ∑ i, a₁ i * a₁ i + ∑ i, a₂ i * a₂ i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha₁, ha₂]
      have h1 : c * a i * (c * a i) = c * (a i * a i) := by
        rw [mul_assoc, ← mul_assoc (a i), ← (hca i).eq, mul_assoc, ← mul_assoc c c,
          hc.isIdempotentElem.eq]
      have h2 : (p - c) * a i * ((p - c) * a i) = (p - c) * (a i * a i) := by
        rw [mul_assoc, ← mul_assoc (a i), ← (hda i).eq, mul_assoc, ← mul_assoc (p - c) (p - c),
          hd.isIdempotentElem.eq]
      rw [h1, h2, ← add_mul, add_sub_cancel, ← mul_assoc, hpa i]
    have hqa : ∑ i, (q₁ i + q₂ i) * a i = ∑ i, q₁ i * a₁ i + ∑ i, q₂ i * a₂ i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha₁, ha₂]
      rw [add_mul, ← mul_assoc, (hq₁ i).2.2.1, ← mul_assoc, (hq₂ i).2.2.1]
    rw [hsq, hqa, map_add, map_add, Complex.add_re, Complex.add_re]
    exact add_le_add hq₁ineq hq₂ineq

/-- **Lemma 3.1 at `p`** (`HasSelection`) from Lemma 3.1 on the type I part (`hI`, the
shape of interface field H5) and on the type II₁ part (`hII`). -/
theorem hasSelection_of_split (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M) (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    {c : H →L[ℂ] H} (hc : IsStarProjection c) (hcc : IsCentralIn M p c)
    (hI : ∀ (n : ℕ) (a : Fin n → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) →
      ∑ i, a i = c →
      ∀ φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ, (∀ x ∈ M, 0 ≤ φ (star x * x)) → IsNormalOn M φ →
      ∃ q : Fin n → H →L[ℂ] H,
        (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * c = q i ∧ Commute (q i) (a i)) ∧
        ∑ i, E (q i) = c ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re)
    (hII : ∀ (n : ℕ) (a : Fin n → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) →
      ∑ i, a i = p - c →
      ∀ φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ, (∀ x ∈ M, 0 ≤ φ (star x * x)) → IsNormalOn M φ →
      ∃ q : Fin n → H →L[ℂ] H,
        (∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * (p - c) = q i ∧ Commute (q i) (a i)) ∧
        ∑ i, E (q i) = p - c ∧ (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re)
    (n : ℕ) : HasSelection M p E n :=
  fun a haM ha0 hap φ hφ hφn =>
    selection_of_split M hp hpM E hc hcc φ (fun m a' ha'M ha'0 ha'c => hI m a' ha'M ha'0 ha'c φ hφ hφn)
      (fun m a' ha'M ha'0 ha'c => hII m a' ha'M ha'0 ha'c φ hφ hφn) n a haM ha0 hap

/-! ### Theorem 1.2 at a finite projection from Lemma 3.1 -/

/-- **Theorem 1.2 at `p` for a fixed functional**: from the projections `qᵢ` of Lemma 3.1
for `φ` and the POVM `(aᵢ)`, Lemma 3.2 in `M_n(M)` and the three-term estimate give the
PVM. The hypotheses `hEp`, `hEtr`, `hcomp`, `hpolar` are instances of the interface fields
(`center_fixed`, `trace`, `equiv_of_eq_matrix` of `IsCenterValuedTrace`, and H6 applied
to `matrixAlgebra M n`). -/
theorem exists_pvm_bound_of_selection (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hEp : E p = p)
    (hEtr : ∀ x ∈ M, p * x * p = x → ∀ y ∈ M, p * y * p = y → E (x * y) = E (y * x))
    {n : ℕ}
    (hcomp : ∀ P Q : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
      P ∈ matrixAlgebra M n → IsStarProjection P → P * amplify n p = P →
      Q ∈ matrixAlgebra M n → IsStarProjection Q → Q * amplify n p = Q →
      ∑ i, E (entry P i i) = ∑ i, E (entry Q i i) → MvNEquiv (matrixAlgebra M n) P Q)
    (hpolar : ∀ x ∈ matrixAlgebra M n, ∃ u ∈ matrixAlgebra M n,
      star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
        x = u * CFC.sqrt (star x * x))
    (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) (hφp : φ p = 1)
    (a : Fin n → H →L[ℂ] H) (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i) (hap : ∑ i, a i = p)
    (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (q : Fin n → H →L[ℂ] H)
    (hq : ∀ i, IsStarProjection (q i) ∧ q i ∈ M ∧ q i * p = q i ∧ Commute (q i) (a i))
    (hqE : ∑ i, E (q i) = p) (hqineq : (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re) :
    ∃ p' : Fin n → H →L[ℂ] H, (∀ i, p' i ∈ M) ∧ (∀ i, IsStarProjection (p' i)) ∧
      (∀ i, p' i * p = p' i) ∧ ∑ i, p' i = p ∧
      (φ (∑ i, star (a i - p' i) * (a i - p' i))).re < 9 * ε := by
  obtain ⟨p', hp'proj, hp'M, hp'p, hp'sum, hp'id⟩ :=
    exists_pvm_of_selection M hp hpM E hEp hEtr hcomp hpolar a q haM ha0 hap
      (fun i => (hq i).1) (fun i => (hq i).2.1) (fun i => (hq i).2.2.1)
      (fun i => (hq i).2.2.2) hqE
  -- the square root `s = √(∑ⱼ qⱼ aⱼ)`
  have hyM : (∑ j, q j * a j) ∈ M := sum_mem fun j _ => mul_mem (hq j).2.1 (haM j)
  have hy0 : (0 : H →L[ℂ] H) ≤ ∑ j, q j * a j := Finset.sum_nonneg fun j _ =>
    Orthogonalization.IsStarProjection.mul_nonneg_of_commute (hq j).1 (ha0 j) (hq j).2.2.2
  have hyp : ∑ j, q j * a j ≤ p := by
    rw [← hap]
    exact Finset.sum_le_sum fun j _ =>
      Orthogonalization.IsStarProjection.mul_le_of_commute (hq j).1 (ha0 j) (hq j).2.2.2
  have hy1 : ∑ j, q j * a j ≤ 1 := hyp.trans (proj_le_one hp)
  have hyp' : (∑ j, q j * a j) * p = ∑ j, q j * a j := mul_eq_self_of_le_proj hp hy0 hyp
  refine ⟨p', hp'M, hp'proj, hp'p, hp'sum, ?_⟩
  exact assembled_bound_rel M φ hφ hp hpM hφp a q p' (CFC.sqrt (∑ j, q j * a j)) haM ha0 hap
    (fun i => (hq i).1) (fun i => (hq i).2.1) (fun i => (hq i).2.2.2) hp'proj hp'M hp'sum
    (sqrt_mem M hyM hy0) (sqrt_nonneg _) (sqrt_le_one_of_le_one hy1)
    (sqrt_mul_proj_eq_self hy0 hyp') (sqrt_mul_sqrt_self hy0) hp'id ε hε (hε.le.trans hqineq)

/-- **Theorem 1.2 at a finite projection `p`** for the functionals normal on `M`, from
Lemma 3.1 at `p` (`hsel`). -/
theorem orthAtN_fin_of_hasSelection (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hEp : E p = p)
    (hEtr : ∀ x ∈ M, p * x * p = x → ∀ y ∈ M, p * y * p = y → E (x * y) = E (y * x))
    (n : ℕ)
    (hcomp : ∀ P Q : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
      P ∈ matrixAlgebra M n → IsStarProjection P → P * amplify n p = P →
      Q ∈ matrixAlgebra M n → IsStarProjection Q → Q * amplify n p = Q →
      ∑ i, E (entry P i i) = ∑ i, E (entry Q i i) → MvNEquiv (matrixAlgebra M n) P Q)
    (hpolar : ∀ x ∈ matrixAlgebra M n, ∃ u ∈ matrixAlgebra M n,
      star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
        x = u * CFC.sqrt (star x * x))
    (hsel : HasSelection M p E n) : OrthAtN M p (Fin n) := by
  intro φ hφn hφ hφp a haM ha0 hap ε hε
  obtain ⟨q, hq, hqE, hqineq⟩ := hsel a haM ha0 hap φ hφ hφn
  exact exists_pvm_bound_of_selection M hp hpM E hEp hEtr hcomp hpolar φ hφ hφp a haM ha0 hap
    ε hε q hq hqE hqineq

/-! ### The finite case under the interface -/

/-- **Theorem 1.2 at a finite projection `p`**, for the functionals normal on `M` and the
output set `Fin n`, under the structure-theory interface: H3 supplies the center-valued
trace of `p M p`, H1' the split `p = c + (p − c)` into the type I and type II₁ parts, H5
Lemma 3.1 on the type I part, `exists_selection_typeII₁` (with H0) Lemma 3.1 on the type
II₁ part, and H6 (applied to `M_n(M)`) the polar decomposition of Lemma 3.2. -/
theorem orthAtN_fin_of_isFiniteProj (hS : MvNStructureTheory.{u}) (M : VonNeumannAlgebra H)
    {p : H →L[ℂ] H} (hp : IsFiniteProj M p) (n : ℕ) : OrthAtN M p (Fin n) := by
  obtain ⟨E, hE⟩ := hS.center_valued_trace M p hp
  obtain ⟨c, hc, hcc, hcI, hcII⟩ := hS.finite_decomposition M p hp
  have hpP : IsStarProjection p := hp.1
  have hpM : p ∈ M := hp.2.1
  have hcp : c * p = c := hcc.self_mul_proj hpP
  have hpc : p * c = c := hcc.proj_mul_self hpP
  refine orthAtN_fin_of_hasSelection M hpP hpM E
    (hE.center_fixed p (isCentralIn_proj M hpP hpM)) hE.trace n (hE.equiv_of_eq_matrix n)
    (fun x hx => hS.polar (matrixAlgebra M n) x hx) ?_
  refine hasSelection_of_split M hpP hpM E hc hcc
    (fun m a haM ha0 hac φ hφ hφn =>
      hS.selection_typeI M p c hp hc hcc hcI E hE m a haM ha0 hac φ hφ hφn)
    (fun m a haM ha0 hac φ hφ hφn =>
      exists_selection_typeII₁ M hpP hpM (isStarProjection_sub_of_le hpP hc hcp hpc)
        ((isCentralIn_proj M hpP hpM).sub hcc) hcII.2 E hE a haM ha0 hac φ
        (hS.normal_traceClass M φ hφ hφn)) n

end Orthogonalization.MvN
