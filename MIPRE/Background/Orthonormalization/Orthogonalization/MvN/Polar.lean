/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Polar.lean
-/
/-
# Lemma 3.2 of the paper inside `M_n(M)`: the PVM of the finite case

Proof-side step **F2** of the finite case of Theorem 1.2 (Section 3 of the
paper). Given the projections `qᵢ ≤ p` produced by Lemma 3.1 (`qᵢ` commuting with
`aᵢ`, `∑ E(qᵢ) = p` for the center-valued trace `E` of the finite corner
`p M p`), Lemma 3.2 applied in `M_n(M)` to the column `x = ∑ᵢ e_{i0} ⊗ qᵢ √aᵢ`
produces a partial isometry `u ∈ M_n(M)` with `u* u = e_{00} ⊗ p`,
`u u* = ⊕ᵢ qᵢ` and `x = u √(x* x)`, hence a PVM `p'ᵢ = (u* (e_{ii} ⊗ qᵢ) u)₀₀` of
the corner `p M p` with `√y p'ᵢ √y = qᵢ aᵢ`, `y = ∑ⱼ qⱼ aⱼ`.

* `exists_partial_isometry_of_supports` is Lemma 3.2 itself, in `M_n(M)`: for
  `x ∈ M_n(M)` and projections `Q, P ≤ 1_n ⊗ p` of `M_n(M)` with `x Q = x`,
  `P x = x` and equal diagonal traces, there is `u` with `u* u = Q`, `u u* = P`
  and `x = u √(x* x)`. The two ingredients enter as explicit hypotheses: the
  polar decomposition inside `M_n(M)` (field H6 of the interface) and the
  comparison of projections of `M_n(p M p)` with equal diagonal trace (the
  matrix clause of the center-valued trace, field H3). The equality
  `E(Q − R) = E(P − L)` of the diagonal traces of the two defect projections is
  the trace identity `E(u₀* u₀) = E(u₀ u₀*)` read entrywise.
* `exists_pvm_of_partial_isometry` extracts the PVM from the partial isometry.
* `exists_pvm_of_selection` assembles the two for the column of Lemma 3.1.

Everything is stated on the ambient space `H`; no statement of the paper is
made here.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.BlockCalc
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Isometries

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

/- The real-algebra structure of `H^n →L[ℂ] H^n` (needed by `CFC.sqrt`) is found by instance
search only after unfolding `PiLp`, which exceeds the default heartbeat budget. -/
set_option synthInstance.maxHeartbeats 100000

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open FinDim Blocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Two C⋆-algebraic steps of Lemma 3.2 -/

/-- If `S = S*` and `S R = S` for a projection `R ≤ Q`, then `v (Q − R) = v` forces `v S = 0`. -/
theorem mul_eq_zero_of_mul_sub_eq_self {v Q R S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    (hR : IsStarProjection R) (hSR : S * R = S) (hQR : Q * R = R) (hvQR : v * (Q - R) = v) :
    v * S = 0 := by
  have hRS : R * S = S := by
    have := congrArg star hSR
    rwa [star_mul, hS.star_eq, hR.isSelfAdjoint.star_eq] at this
  have hQS : Q * S = S := by
    calc Q * S = Q * (R * S) := by rw [hRS]
      _ = (Q * R) * S := (mul_assoc _ _ _).symm
      _ = S := by rw [hQR, hRS]
  calc v * S = v * (Q - R) * S := by rw [hvQR]
    _ = v * ((Q - R) * S) := mul_assoc _ _ _
    _ = 0 := by rw [sub_mul, hQS, hRS, sub_self, mul_zero]

/-- The sum of two partial isometries `u₀ : R → L` and `v : Q − R → P − L`, for projections
`R ≤ Q` and `L ≤ P`, is a partial isometry `Q → P`: the cross terms `u₀* v`, `u₀ v*` vanish
because `L (P − L) = 0` and `R (Q − R) = 0`. -/
theorem star_add_mul_add_eq_of_le {u₀ v Q R P L : H →L[ℂ] H} (hR : IsStarProjection R)
    (hL : IsStarProjection L) (hQR : IsStarProjection (Q - R)) (hPL : IsStarProjection (P - L))
    (hu₀R : star u₀ * u₀ = R) (hu₀L : u₀ * star u₀ = L) (hv1 : star v * v = Q - R)
    (hv2 : v * star v = P - L) (hRQ : R * Q = R) (hLP : L * P = L) :
    star (u₀ + v) * (u₀ + v) = Q ∧ (u₀ + v) * star (u₀ + v) = P := by
  have hu₀R' : u₀ * R = u₀ := mul_eq_self_of_star_mul_self_eq hR hu₀R
  have hu₀L' : star u₀ * L = star u₀ := by
    rw [← hu₀L]
    exact star_mul_self_mul_star (by rw [hu₀R]; exact hR)
  have hQRv : (Q - R) * star v = star v := proj_mul_star_eq_self_of_star_mul_self_eq hQR hv1
  have hvPL : star v * (P - L) = star v := by
    rw [← hv2]
    exact star_mul_self_mul_star (by rw [hv1]; exact hQR)
  have hPLv : (P - L) * v = v := by
    have := congrArg star hvPL
    rwa [star_mul, star_star, hPL.isSelfAdjoint.star_eq] at this
  have hL0 : L * (P - L) = 0 := proj_mul_sub_eq_zero hL hLP
  have hR0 : R * (Q - R) = 0 := proj_mul_sub_eq_zero hR hRQ
  have h1 : star u₀ * v = 0 := by
    calc star u₀ * v = (star u₀ * L) * ((P - L) * v) := by rw [hu₀L', hPLv]
      _ = star u₀ * (L * (P - L)) * v := by simp only [mul_assoc]
      _ = 0 := by rw [hL0, mul_zero, zero_mul]
  have h2 : star v * u₀ = 0 := by
    have := congrArg star h1
    rwa [star_mul, star_star, star_zero] at this
  have h3 : u₀ * star v = 0 := by
    calc u₀ * star v = (u₀ * R) * ((Q - R) * star v) := by rw [hu₀R', hQRv]
      _ = u₀ * (R * (Q - R)) * star v := by simp only [mul_assoc]
      _ = 0 := by rw [hR0, mul_zero, zero_mul]
  have h4 : v * star u₀ = 0 := by
    have := congrArg star h3
    rwa [star_mul, star_star, star_zero] at this
  constructor
  · rw [star_add, add_mul, mul_add, mul_add, hu₀R, h1, h2, hv1]
    abel
  · rw [star_add, add_mul, mul_add, mul_add, hu₀L, h3, h4, hv2]
    abel

/-! ### Lemma 3.2 in `M_n(M)` -/

/-- **Lemma 3.2 in `M_n(M)`.** For `x ∈ M_n(M)` and projections `Q, P ≤ 1_n ⊗ p` of `M_n(M)`
with `x Q = x`, `P x = x` and `∑ᵢ E(Qᵢᵢ) = ∑ᵢ E(Pᵢᵢ)`, there is a partial isometry
`u ∈ M_n(M)` with `u* u = Q`, `u u* = P` and `x = u √(x* x)`: write `x = u₀ √(x* x)` with
`u₀* u₀ = R ≤ Q`, `u₀ u₀* = L ≤ P` the supports of `x`, compare `Q − R ∼ P − L` by a partial
isometry `v`, and take `u = u₀ + v`. -/
theorem exists_partial_isometry_of_supports (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (hEtr : ∀ x ∈ M, p * x * p = x → ∀ y ∈ M, p * y * p = y → E (x * y) = E (y * x))
    {n : ℕ}
    (hcomp : ∀ P Q : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
      P ∈ matrixAlgebra M n → IsStarProjection P → P * amplify n p = P →
      Q ∈ matrixAlgebra M n → IsStarProjection Q → Q * amplify n p = Q →
      ∑ i, E (entry P i i) = ∑ i, E (entry Q i i) → MvNEquiv (matrixAlgebra M n) P Q)
    (hpolar : ∀ x ∈ matrixAlgebra M n, ∃ u ∈ matrixAlgebra M n,
      star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
        x = u * CFC.sqrt (star x * x))
    {x Q P : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (hxM : x ∈ matrixAlgebra M n)
    (hQ : IsStarProjection Q) (hQM : Q ∈ matrixAlgebra M n) (hQamp : Q * amplify n p = Q)
    (hP : IsStarProjection P) (hPM : P ∈ matrixAlgebra M n) (hPamp : P * amplify n p = P)
    (hxQ : x * Q = x) (hPx : P * x = x)
    (hE : ∑ i, E (entry Q i i) = ∑ i, E (entry P i i)) :
    ∃ u ∈ matrixAlgebra M n, star u * u = Q ∧ u * star u = P ∧
      u * CFC.sqrt (star x * x) = x := by
  obtain ⟨u₀, hu₀M, hu₀R, hu₀L, hxu₀⟩ := hpolar x hxM
  /- The modulus `S = √(x* x)` and the supports `R`, `L` enter only through the facts recorded
  here; they are then replaced by variables. -/
  have hSsa : IsSelfAdjoint (CFC.sqrt (star x * x)) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (star x * x))
  have hSR : CFC.sqrt (star x * x) * rightSupport x = CFC.sqrt (star x * x) :=
    sqrt_star_mul_self_mul_rightSupport x
  generalize CFC.sqrt (star x * x) = S at hxu₀ hSsa hSR ⊢
  have hRproj : IsStarProjection (rightSupport x) := isStarProjection_rightSupport x
  have hLproj : IsStarProjection (leftSupport x) := isStarProjection_leftSupport x
  have hRQ : rightSupport x * Q = rightSupport x := rightSupport_mul_eq_self_of hxQ
  have hLP : leftSupport x * P = leftSupport x := leftSupport_mul_eq_self_of hP hPx
  generalize rightSupport x = R at hu₀R hSR hRproj hRQ
  generalize leftSupport x = L at hu₀L hLproj hLP
  have hRM : R ∈ matrixAlgebra M n := by rw [← hu₀R]; exact mul_mem (star_mem hu₀M) hu₀M
  have hLM : L ∈ matrixAlgebra M n := by rw [← hu₀L]; exact mul_mem hu₀M (star_mem hu₀M)
  have hQR : Q * R = R := proj_mul_left_of_mul_right hRproj hQ hRQ
  have hPL : P * L = L := proj_mul_left_of_mul_right hLproj hP hLP
  have hu₀R' : u₀ * R = u₀ := mul_eq_self_of_star_mul_self_eq hRproj hu₀R
  have hu₀L' : star u₀ * L = star u₀ := by
    rw [← hu₀L]
    exact star_mul_self_mul_star (by rw [hu₀R]; exact hRproj)
  have hLu₀ : L * u₀ = u₀ := by
    have := congrArg star hu₀L'
    rwa [star_mul, star_star, hLproj.isSelfAdjoint.star_eq] at this
  have hu₀Q : u₀ * Q = u₀ := by
    calc u₀ * Q = u₀ * R * Q := by rw [hu₀R']
      _ = u₀ * (R * Q) := mul_assoc _ _ _
      _ = u₀ := by rw [hRQ, hu₀R']
  have hPu₀ : P * u₀ = u₀ := by
    calc P * u₀ = P * (L * u₀) := by rw [hLu₀]
      _ = (P * L) * u₀ := (mul_assoc _ _ _).symm
      _ = u₀ := by rw [hPL, hLu₀]
  /- The entries of `u₀` lie in the corner `p M p`, so the diagonal traces of `R = u₀* u₀`
  and `L = u₀ u₀*` agree, hence so do those of `Q − R` and `P − L`. -/
  have hampP : amplify n p * P = P :=
    proj_mul_left_of_mul_right hP (isStarProjection_amplify hp) hPamp
  have hamp : amplify n p * u₀ * amplify n p = u₀ := by
    calc amplify n p * u₀ * amplify n p
        = amplify n p * (P * u₀ * Q) * amplify n p := by rw [hPu₀, hu₀Q]
      _ = (amplify n p * P) * u₀ * (Q * amplify n p) := by simp only [mul_assoc]
      _ = u₀ := by rw [hampP, hQamp, hPu₀, hu₀Q]
  have hER : ∑ i, E (entry R i i) = ∑ i, E (entry L i i) := by
    rw [← hu₀R, ← hu₀L]
    exact sum_entry_star_mul_self_eq_of_corner hp E hEtr (entry_mem hu₀M)
      (corner_entry_of_amplify hamp)
  have hEdiff : ∑ i, E (entry (Q - R) i i) = ∑ i, E (entry (P - L) i i) := by
    simp only [entry_sub, map_sub, Finset.sum_sub_distrib]
    rw [hE, hER]
  /- Comparison of the defect projections `Q − R ∼ P − L` in `M_n(p M p)`, and the sum
  `u = u₀ + v`. -/
  have hQR' : IsStarProjection (Q - R) := isStarProjection_sub_of_le hQ hRproj hRQ hQR
  have hPL' : IsStarProjection (P - L) := isStarProjection_sub_of_le hP hLproj hLP hPL
  have hRamp : R * amplify n p = R := by
    calc R * amplify n p = R * Q * amplify n p := by rw [hRQ]
      _ = R * (Q * amplify n p) := mul_assoc _ _ _
      _ = R := by rw [hQamp, hRQ]
  have hLamp : L * amplify n p = L := by
    calc L * amplify n p = L * P * amplify n p := by rw [hLP]
      _ = L * (P * amplify n p) := mul_assoc _ _ _
      _ = L := by rw [hPamp, hLP]
  obtain ⟨v, hvM, hv1, hv2⟩ := hcomp (Q - R) (P - L) (sub_mem hQM hRM) hQR'
    (by rw [sub_mul, hQamp, hRamp]) (sub_mem hPM hLM) hPL' (by rw [sub_mul, hPamp, hLamp]) hEdiff
  obtain ⟨huu, huu'⟩ :=
    star_add_mul_add_eq_of_le hRproj hLproj hQR' hPL' hu₀R hu₀L hv1 hv2 hRQ hLP
  have hvS : v * S = 0 :=
    mul_eq_zero_of_mul_sub_eq_self hSsa hRproj hSR hQR (mul_eq_self_of_star_mul_self_eq hQR' hv1)
  refine ⟨u₀ + v, add_mem hu₀M hvM, huu, huu', ?_⟩
  rw [add_mul, hvS, add_zero, ← hxu₀]

/-- From a partial isometry `u ∈ M_n(M)` with `u* u = e_{00} ⊗ p`, `u u* = ⊕ᵢ qᵢ` and
`u (e_{00} ⊗ s) = ∑ᵢ e_{i0} ⊗ X i` (`s = √y`): the operators `p'ᵢ = (u* (e_{ii} ⊗ qᵢ) u)₀₀`
form a PVM of the corner `p M p` with `s p'ᵢ s = (X i)* qᵢ (X i)`. -/
theorem exists_pvm_of_partial_isometry (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) {n : ℕ} [NeZero n] {q : Fin n → H →L[ℂ] H}
    (hq : ∀ i, IsStarProjection (q i)) (hqM : ∀ i, q i ∈ M)
    {u : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (huM : u ∈ matrixAlgebra M n)
    (huu : star u * u = single 0 p) (huu' : u * star u = blockProj q)
    {X : Fin n → H →L[ℂ] H} {y : H →L[ℂ] H} (hux : u * single 0 (CFC.sqrt y) = col 0 X) :
    ∃ p' : Fin n → H →L[ℂ] H, (∀ i, IsStarProjection (p' i)) ∧ (∀ i, p' i ∈ M) ∧
      (∀ i, p' i * p = p' i) ∧ ∑ i, p' i = p ∧
      ∀ i, CFC.sqrt y * p' i * CFC.sqrt y = star (X i) * q i * X i := by
  have hQ : IsStarProjection (single (0 : Fin n) p) := isStarProjection_single 0 hp
  have hut : u * single 0 p = u := mul_eq_self_of_star_mul_self_eq hQ huu
  have hQu : single 0 p * star u = star u := proj_mul_star_eq_self_of_star_mul_self_eq hQ huu
  /- The projections `tᵢ = e_{ii} ⊗ qᵢ`, summing to `⊕ᵢ qᵢ = u u*`. -/
  obtain ⟨t, ht⟩ : ∃ t : Fin n → BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
    ∀ i, t i = single i (q i) := ⟨_, fun _ => rfl⟩
  have htsum : ∑ i, t i = blockProj q := by
    rw [← sum_single]
    exact Finset.sum_congr rfl fun i _ => ht i
  have htP : ∀ i, t i * blockProj q = t i := fun i => by
    rw [ht i, single_mul_blockProj, (hq i).isIdempotentElem.eq]
  have htt : ∀ i, t i * t i = t i := fun i => by
    rw [ht i, single_mul_single_same, (hq i).isIdempotentElem.eq]
  have htsa : ∀ i, star (t i) = t i := fun i => by
    rw [ht i, single_star, (hq i).isSelfAdjoint.star_eq]
  have htM : ∀ i, t i ∈ matrixAlgebra M n := fun i => by
    rw [ht i]; exact single_mem i (hqM i)
  /- `Yᵢ = u* tᵢ u` is a projection of `M_n(M)` supported in the `(0, 0)` block. -/
  obtain ⟨Y, hY⟩ : ∃ Y : Fin n → BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
    ∀ i, Y i = star u * t i * u := ⟨_, fun _ => rfl⟩
  have hYconj : ∀ i, single 0 p * Y i * single 0 p = Y i := fun i => by
    rw [hY i]
    calc single 0 p * (star u * t i * u) * single 0 p
        = (single 0 p * star u) * t i * (u * single 0 p) := by simp only [mul_assoc]
      _ = star u * t i * u := by rw [hQu, hut]
  have hYM : ∀ i, Y i ∈ matrixAlgebra M n := fun i => by
    rw [hY i]; exact mul_mem (mul_mem (star_mem huM) (htM i)) huM
  have hYproj : ∀ i, IsStarProjection (Y i) := fun i => by
    refine ⟨?_, ?_⟩
    · show Y i * Y i = Y i
      rw [hY i]
      calc star u * t i * u * (star u * t i * u)
          = star u * (t i * (u * star u) * t i) * u := by simp only [mul_assoc]
        _ = star u * t i * u := by rw [huu', htP i, htt i]
    · rw [IsSelfAdjoint, hY i, star_mul, star_mul, star_star, htsa i, mul_assoc]
  obtain ⟨p', hp'⟩ : ∃ p' : Fin n → H →L[ℂ] H, ∀ i, p' i = entry (Y i) 0 0 := ⟨_, fun _ => rfl⟩
  have hYs : ∀ i, Y i = single 0 (p' i) := fun i => by
    rw [hp' i]
    exact eq_single_of_conj (hYconj i)
  have hp'M : ∀ i, p' i ∈ M := fun i => by rw [hp' i]; exact entry_mem (hYM i) 0 0
  have hp'c : ∀ i, p * p' i * p = p' i := fun i => by
    rw [hp' i]
    exact entry_eq_conj_of_conj (hYconj i)
  have hp'p : ∀ i, p' i * p = p' i := fun i => by
    calc p' i * p = p * p' i * p * p := by rw [hp'c i]
      _ = p * p' i * (p * p) := by rw [mul_assoc]
      _ = p' i := by rw [hp.isIdempotentElem.eq, hp'c i]
  have hp'proj : ∀ i, IsStarProjection (p' i) := fun i =>
    isStarProjection_of_single (by rw [← hYs i]; exact hYproj i)
  /- `∑ᵢ Yᵢ = u* (u u*) u = (u* u)² = e_{00} ⊗ p`, so `∑ᵢ p'ᵢ = p`. -/
  have hp'sum : ∑ i, p' i = p := by
    have hsum : ∑ i, Y i = single 0 p := by
      calc ∑ i, Y i = star u * (∑ i, t i) * u := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => hY i
        _ = star u * (u * star u) * u := by rw [htsum, huu']
        _ = (star u * u) * (star u * u) := by simp only [mul_assoc]
        _ = single 0 p := by rw [huu, hQ.isIdempotentElem.eq]
    refine single_inj (i := (0 : Fin n)) ?_
    rw [single_sum, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hYs i).symm
  /- `e_{00} ⊗ s p'ᵢ s = (e_{00} ⊗ s) Yᵢ (e_{00} ⊗ s) = (u (e_{00} ⊗ s))* tᵢ (u (e_{00} ⊗ s))`. -/
  refine ⟨p', hp'proj, hp'M, hp'p, hp'sum, fun i => ?_⟩
  have hssa : IsSelfAdjoint (single (0 : Fin n) (CFC.sqrt y)) := by
    rw [IsSelfAdjoint, single_star, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg y)).star_eq]
  refine single_inj (i := (0 : Fin n)) ?_
  calc single 0 (CFC.sqrt y * p' i * CFC.sqrt y)
      = single 0 (CFC.sqrt y) * single 0 (p' i) * single 0 (CFC.sqrt y) := by
        rw [single_mul_single_same, single_mul_single_same]
    _ = single 0 (CFC.sqrt y) * Y i * single 0 (CFC.sqrt y) := by rw [hYs i]
    _ = star (u * single 0 (CFC.sqrt y)) * t i * (u * single 0 (CFC.sqrt y)) := by
        rw [hY i, star_mul, hssa.star_eq]
        simp only [mul_assoc]
    _ = star (col 0 X) * t i * col 0 X := by rw [hux]
    _ = single 0 (star (X i) * q i * X i) := by rw [ht i, star_col_mul_single_mul_col]

/-- Lemma 3.2 in `M_n(M)` for `n ≥ 1` (the index `0 : Fin n` carries the column). -/
theorem exists_pvm_of_selection_of_neZero (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hEp : E p = p)
    (hEtr : ∀ x ∈ M, p * x * p = x → ∀ y ∈ M, p * y * p = y → E (x * y) = E (y * x))
    {n : ℕ} [NeZero n]
    (hcomp : ∀ P Q : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
      P ∈ matrixAlgebra M n → IsStarProjection P → P * amplify n p = P →
      Q ∈ matrixAlgebra M n → IsStarProjection Q → Q * amplify n p = Q →
      ∑ i, E (entry P i i) = ∑ i, E (entry Q i i) → MvNEquiv (matrixAlgebra M n) P Q)
    (hpolar : ∀ x ∈ matrixAlgebra M n, ∃ u ∈ matrixAlgebra M n,
      star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
        x = u * CFC.sqrt (star x * x))
    (a q : Fin n → H →L[ℂ] H)
    (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i) (hap : ∑ i, a i = p)
    (hq : ∀ i, IsStarProjection (q i)) (hqM : ∀ i, q i ∈ M) (hqp : ∀ i, q i * p = q i)
    (hqa : ∀ i, Commute (q i) (a i)) (hqE : ∑ i, E (q i) = p) :
    ∃ p' : Fin n → H →L[ℂ] H, (∀ i, IsStarProjection (p' i)) ∧ (∀ i, p' i ∈ M) ∧
      (∀ i, p' i * p = p' i) ∧ ∑ i, p' i = p ∧
      ∀ i, CFC.sqrt (∑ j, q j * a j) * p' i * CFC.sqrt (∑ j, q j * a j) = q i * a i := by
  /- The POVM `aᵢ` and the square roots `√aᵢ` are supported in `p`, and `qᵢ` commutes
  with `√aᵢ`. -/
  have hap' : ∀ i, a i * p = a i := fun i => mul_eq_self_of_sum_eq hp ha0 hap i
  have hsa : ∀ i, CFC.sqrt (a i) * p = CFC.sqrt (a i) := fun i =>
    sqrt_mul_proj_eq_self (ha0 i) (hap' i)
  have hqs : ∀ i, Commute (q i) (CFC.sqrt (a i)) := fun i => Orthogonalization.Commute.sqrt (hqa i)
  have hsqM : ∀ i, CFC.sqrt (a i) ∈ M := fun i => sqrt_mem M (haM i) (ha0 i)
  have hsqsa : ∀ i, star (CFC.sqrt (a i)) = CFC.sqrt (a i) := fun i =>
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  /- The column `x = ∑ᵢ e_{i0} ⊗ qᵢ √aᵢ ∈ M_n(M)` and the projections `Q = e_{00} ⊗ p`,
  `P = ⊕ᵢ qᵢ`, both below `1_n ⊗ p`, with `x Q = x` and `P x = x`. -/
  obtain ⟨X, hX⟩ : ∃ X : Fin n → H →L[ℂ] H, ∀ i, X i = q i * CFC.sqrt (a i) := ⟨_, fun _ => rfl⟩
  have hqX : ∀ i, q i * X i = X i := fun i => by
    rw [hX i, ← mul_assoc, (hq i).isIdempotentElem.eq]
  have hXp : ∀ i, X i * p = X i := fun i => by rw [hX i, mul_assoc, hsa i]
  have hXM : ∀ i, X i ∈ M := fun i => by rw [hX i]; exact mul_mem (hqM i) (hsqM i)
  have hxM : col (0 : Fin n) X ∈ matrixAlgebra M n := col_mem hXM 0
  have hQ : IsStarProjection (single (0 : Fin n) p) := isStarProjection_single 0 hp
  have hP : IsStarProjection (blockProj q) := isStarProjection_blockProj hq
  have hQM : single (0 : Fin n) p ∈ matrixAlgebra M n := single_mem 0 hpM
  have hPM : blockProj q ∈ matrixAlgebra M n := blockProj_mem hqM
  have hQamp : single (0 : Fin n) p * amplify n p = single 0 p := by
    rw [single_mul_amplify, hp.isIdempotentElem.eq]
  have hPamp : blockProj q * amplify n p = blockProj q := by
    rw [blockProj_mul_amplify]
    congr 1
    funext i
    exact hqp i
  have hxQ : col (0 : Fin n) X * single 0 p = col 0 X := by
    rw [col_mul_single]
    congr 1
    funext i
    exact hXp i
  have hPx : blockProj q * col (0 : Fin n) X = col 0 X := by
    rw [blockProj_mul_col]
    congr 1
    funext i
    exact hqX i
  /- `x* x = e_{00} ⊗ y` with `y = ∑ⱼ qⱼ aⱼ ≥ 0`, so `√(x* x) = e_{00} ⊗ √y`. -/
  have hy0 : 0 ≤ ∑ j, q j * a j :=
    Finset.sum_nonneg fun j _ =>
      Orthogonalization.IsStarProjection.mul_nonneg_of_commute (hq j) (ha0 j) (hqa j)
  have hterm : ∀ i, star (X i) * X i = q i * a i := fun i => by
    rw [hX i, star_mul, hsqsa i, (hq i).isSelfAdjoint.star_eq]
    calc CFC.sqrt (a i) * q i * (q i * CFC.sqrt (a i))
        = CFC.sqrt (a i) * (q i * q i) * CFC.sqrt (a i) := by simp only [mul_assoc]
      _ = q i * (CFC.sqrt (a i) * CFC.sqrt (a i)) := by
          rw [(hq i).isIdempotentElem.eq, ← (hqs i).eq, mul_assoc]
      _ = q i * a i := by rw [sqrt_mul_sqrt_self (ha0 i)]
  have hxx : star (col (0 : Fin n) X) * col 0 X = single 0 (∑ j, q j * a j) := by
    rw [star_col_mul_col]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hterm i
  have hsqrt : CFC.sqrt (star (col (0 : Fin n) X) * col 0 X) =
      single 0 (CFC.sqrt (∑ j, q j * a j)) := by
    rw [hxx, sqrt_single 0 hy0]
  /- `E(Q) = E(p) = p = ∑ E(qᵢ) = E(P)`. -/
  have hEQ : ∑ i, E (entry (single (0 : Fin n) p) i i) = p := by
    simp only [entry_single_diag]
    rw [Finset.sum_eq_single (0 : Fin n)]
    · rw [if_pos rfl, hEp]
    · intro b _ hb
      rw [if_neg hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hEP : ∑ i, E (entry (blockProj q) i i) = p := by
    simp only [entry_blockProj, if_true]
    exact hqE
  /- Lemma 3.2 gives the partial isometry; it yields the PVM. -/
  obtain ⟨u, huM, huu, huu', hux⟩ := exists_partial_isometry_of_supports M hp E hEtr hcomp hpolar
    hxM hQ hQM hQamp hP hPM hPamp hxQ hPx (hEQ.trans hEP.symm)
  rw [hsqrt] at hux
  obtain ⟨p', h1, h2, h3, h4, h5⟩ := exists_pvm_of_partial_isometry M hp hq hqM huM huu huu' hux
  refine ⟨p', h1, h2, h3, h4, fun i => ?_⟩
  rw [h5 i, mul_assoc, hqX i, hterm i]

/-- Lemma 3.2 of the paper applied in `M_n(M)` (proof of Theorem 1.2, finite case, Section 3):
given the projections `qᵢ ≤ p` of Lemma 3.1 (`qᵢ` commuting with `aᵢ`, `∑ E(qᵢ) = p`), there is a
PVM `p'ᵢ` of the corner `p M p` with `√y p'ᵢ √y = qᵢ aᵢ`, `y = ∑ⱼ qⱼ aⱼ`. -/
theorem exists_pvm_of_selection (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hEp : E p = p)
    (hEtr : ∀ x ∈ M, p * x * p = x → ∀ y ∈ M, p * y * p = y → E (x * y) = E (y * x))
    {n : ℕ}
    (hcomp : ∀ P Q : FinDim.BlockSpace H (Fin n) →L[ℂ] FinDim.BlockSpace H (Fin n),
      P ∈ matrixAlgebra M n → IsStarProjection P → P * amplify n p = P →
      Q ∈ matrixAlgebra M n → IsStarProjection Q → Q * amplify n p = Q →
      ∑ i, E (entry P i i) = ∑ i, E (entry Q i i) → MvNEquiv (matrixAlgebra M n) P Q)
    (hpolar : ∀ x ∈ matrixAlgebra M n, ∃ u ∈ matrixAlgebra M n,
      star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
        x = u * CFC.sqrt (star x * x))
    (a q : Fin n → H →L[ℂ] H)
    (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i) (hap : ∑ i, a i = p)
    (hq : ∀ i, IsStarProjection (q i)) (hqM : ∀ i, q i ∈ M) (hqp : ∀ i, q i * p = q i)
    (hqa : ∀ i, Commute (q i) (a i)) (hqE : ∑ i, E (q i) = p) :
    ∃ p' : Fin n → H →L[ℂ] H, (∀ i, IsStarProjection (p' i)) ∧ (∀ i, p' i ∈ M) ∧
      (∀ i, p' i * p = p' i) ∧ ∑ i, p' i = p ∧
      ∀ i, CFC.sqrt (∑ j, q j * a j) * p' i * CFC.sqrt (∑ j, q j * a j) = q i * a i := by
  cases n with
  | zero =>
    -- no index: `p = ∑ aᵢ = 0` and the empty family is the PVM
    refine ⟨fun _ => 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    rw [← hap]
    simp
  | succ m =>
    exact exists_pvm_of_selection_of_neZero M hp hpM E hEp hEtr hcomp hpolar a q haM ha0 hap
      hq hqM hqp hqa hqE

end Orthogonalization.MvN
