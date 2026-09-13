/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Main.lean
-/
/-
# Tier T1a: Theorem 1.2 for `B(H)`, `H` finite-dimensional

Assembly of the three finite-dimensional steps (`PLAN.md` §1, §3):

* **F1** `FinDim.exists_commuting_projections` (Lemma 3.1): projections `q i`
  commuting with `a i`, total trace `dim H`, `φ(∑ q i a i) ≥ φ(∑ a i a i)`;
* **F2** `FinDim.exists_isometryData` (Lemma 3.2 in `M_n(B(H))`): the block
  partial isometry `w` with `w i* w i` summing to `1`, `w i w j* = δ q i`,
  `w i √y = q i √(a i)`;
* **F3** `assembled_bound`: the PVM `p i = w i* w i` and the three-term estimate
  `φ(∑ |a i − p i|²) < 9ε`.

`povm_orthogonalization_finDim` is the engine, stated for an arbitrary state
`φ` on `B(H)` (a positive normalized linear functional: normality is automatic
in finite dimension and is not used); `povm_orthogonalization_of_mem_all` and
`povm_orthogonalization_fullAlgebra` are the literal instances of the signed
statement `povm_orthogonalization` (Theorem 1.2) for a von Neumann algebra
containing every operator, resp. for `fullAlgebra H = B(H)` (encoding decision
E6 of `PLAN.md`; FIDELITY.md, "Instances").
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Basic
import MIPRE.Background.Orthonormalization.Orthogonalization.Assembly
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Selection
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Completion

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped BigOperators ComplexOrder
open Module

section Full

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H) in
/-- The von Neumann algebra `B(H)` of all bounded operators on `H`. -/
noncomputable def fullAlgebra : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' := by
    show Set.centralizer (Set.centralizer (Set.univ : Set (H →L[ℂ] H))) = Set.univ
    rw [Set.centralizer_univ]
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    rw [Set.mem_centralizer_iff]
    intro m hm
    exact (Set.mem_center_iff.mp hm).comm x

@[simp] theorem mem_fullAlgebra (x : H →L[ℂ] H) : x ∈ fullAlgebra H := StarSubalgebra.mem_top

end Full

section FinDim

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]

/-- **Theorem 1.2 for `B(H)`, `H` finite-dimensional, any state.** A POVM `(a i)`
on a finite-dimensional Hilbert space and a positive normalized linear functional
`φ` on `B(H)` with `φ(∑ a i²) > 1 − ε` admit a PVM `(p i)` on `H` with
`φ(∑ |a i − p i|²) < 9ε`. -/
theorem povm_orthogonalization_finDim (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, (∀ i, IsStarProjection (p i)) ∧ ∑ i, p i = 1 ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  classical
  obtain ⟨q, hq, hqa, htr, hqa'⟩ := FinDim.exists_commuting_projections φ a ha0 ha1
  obtain ⟨w, hw⟩ := FinDim.exists_isometryData a q ha0 hq hqa htr
  exact ⟨assembledPVM w, assembledPVM_isStarProjection hw, sum_assembledPVM hw,
    assembled_bound φ hφ hφ1 a q w ha0 ha1 hq hqa hw ε hε (le_trans hε.le hqa')⟩

/-- Theorem 1.2 (`povm_orthogonalization`) for a von Neumann algebra `M` containing
every operator of the finite-dimensional space `H`: the instance of the signed
statement delivered by tier T1a. -/
theorem povm_orthogonalization_of_mem_all (M : VonNeumannAlgebra H)
    (hM : ∀ x : H →L[ℂ] H, x ∈ M) (φ : NormalState M)
    (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  obtain ⟨p, hp, hsum, hlt⟩ := povm_orthogonalization_finDim φ.toLinearMap
    (fun x => φ.nonneg' x (hM x)) φ.map_one' a
    (fun i => (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (ha.2.1 i)) ha.2.2 ε hε
  exact ⟨p, ⟨fun i => hM _, hp, hsum⟩, hlt⟩

/-- Theorem 1.2 (`povm_orthogonalization`) for `M = B(H)`, `H` finite-dimensional. -/
theorem povm_orthogonalization_fullAlgebra (φ : NormalState (fullAlgebra H))
    (a : ι → H →L[ℂ] H) (ha : IsPOVM (fullAlgebra H) a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM (fullAlgebra H) p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε :=
  povm_orthogonalization_of_mem_all (fullAlgebra H) mem_fullAlgebra φ a ha ε hε

end FinDim

end Orthogonalization
