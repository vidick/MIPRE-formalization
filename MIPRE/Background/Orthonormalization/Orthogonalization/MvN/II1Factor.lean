/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/II1Factor.lean
-/
/-
# Tier T4a: Theorem 1.2 for II₁ factors (unconditional, trace-class states)

For a **II₁ factor** `M` — a von Neumann algebra with trivial center, no nonzero
abelian projection, and a faithful tracial state `τ` of trace-class form
`∑ₖ ⟪gₖ, · gₖ⟫` (e.g. the trace vector state of the standard form) — Theorem 1.2
holds for every state `φ` of trace-class form, with no structure-theory
hypothesis: the interface `MvNStructureTheory` is discharged locally, at the
finite projection `p = 1` only (the semifinite net is constant, the type III
summand is `0`, the type I part is `0`):

* H3 — the center-valued trace of `M = 1 M 1` is `x ↦ τ(x) • 1`
  (`isCenterValuedTrace_scalarTrace`): the comparison clauses come from
  `MvN/Comparison.lean` applied to `M` and to `M_n(M)` (`MvN/MatrixFactor.lean`
  makes `M_n(M)` a factor with the diagonal trace);
* H6 — the polar decomposition `MvN/PolarDecomp.lean`;
* H0 — the trace-class forms of `τ` and `φ` are hypotheses;
* H1' / H5 — the type I part is `c = 0`, for which Lemma 3.1 is trivial; the type
  II₁ part is all of `M` (`MvN/Finite.lean`, `exists_selection_typeII₁`).

`povm_orthogonalization_II₁Factor` is an instance of the signed statement
`povm_orthogonalization` (FIDELITY.md, "Instances") for such `M` and the states
of trace-class form (every such state is a `NormalState`; the converse is the
direction of D3 not formalized).
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Finite
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.TypeIII
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.PolarDecomp
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Comparison
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.MatrixFactor

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

/-! ### Scalar multiples of the identity -/

/-- The scalar-valued center-valued trace `x ↦ τ(x) • 1`. -/
noncomputable def scalarTrace (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  τ.smulRight 1

omit [CompleteSpace H] in
theorem scalarTrace_apply (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (x : H →L[ℂ] H) :
    scalarTrace τ x = τ x • 1 := rfl

theorem smul_one_nonneg_of_nonneg {z : ℂ} (hz : 0 ≤ z) : 0 ≤ z • (1 : H →L[ℂ] H) := by
  have hre : z = ((z.re : ℝ) : ℂ) := by
    obtain ⟨-, him⟩ := Complex.nonneg_iff.mp hz
    exact Complex.ext (by simp) (by simp [← him])
  rw [hre]
  exact smul_nonneg_real (Complex.nonneg_iff.mp hz).1 (star_mul_self_nonneg 1 |>.trans_eq
    (by rw [star_one, one_mul]))

theorem isCentralIn_smul_one (M : VonNeumannAlgebra H) (z : ℂ) :
    IsCentralIn M 1 (z • (1 : H →L[ℂ] H)) :=
  ⟨Blocks.smul_mem_vn M z (one_mem M), by rw [one_mul, mul_one], fun y _ _ => by
    show z • (1 : H →L[ℂ] H) * y = y * z • 1
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]⟩

theorem eq_smul_one_of_isCentralIn {M : VonNeumannAlgebra H}
    (hfactor : ∀ z ∈ M, (∀ y ∈ M, Commute z y) → ∃ c : ℂ, z = c • (1 : H →L[ℂ] H))
    {c : H →L[ℂ] H} (hc : IsCentralIn M 1 c) : ∃ l : ℂ, c = l • 1 :=
  hfactor c hc.1 fun y hy => hc.2.2 y hy (by rw [one_mul, mul_one])

/-- A functional of trace-class form is bounded on `M`: `‖τ x‖ ≤ (∑ ‖gₖ‖²) ‖x‖`. -/
theorem norm_map_le_of_tsum {M : VonNeumannAlgebra H} {τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    {g : ℕ → H} (hg : Summable fun k => ‖g k‖ ^ 2)
    (hτg : ∀ x ∈ M, τ x = ∑' k, ⟪g k, x (g k)⟫_ℂ) {x : H →L[ℂ] H} (hx : x ∈ M) :
    ‖τ x‖ ≤ (∑' k, ‖g k‖ ^ 2) * ‖x‖ := by
  rw [hτg x hx]
  have hb : ∀ k, ‖⟪g k, x (g k)⟫_ℂ‖ ≤ ‖g k‖ ^ 2 * ‖x‖ := fun k => by
    calc ‖⟪g k, x (g k)⟫_ℂ‖ ≤ ‖g k‖ * ‖x (g k)‖ := norm_inner_le_norm _ _
      _ ≤ ‖g k‖ * (‖x‖ * ‖g k‖) :=
          mul_le_mul_of_nonneg_left (x.le_opNorm _) (norm_nonneg _)
      _ = ‖g k‖ ^ 2 * ‖x‖ := by ring
  have hs : Summable fun k => ‖g k‖ ^ 2 * ‖x‖ := hg.mul_right _
  calc ‖∑' k, ⟪g k, x (g k)⟫_ℂ‖ ≤ ∑' k, ‖⟪g k, x (g k)⟫_ℂ‖ :=
        norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun k => norm_nonneg _) hb)
    _ ≤ ∑' k, ‖g k‖ ^ 2 * ‖x‖ :=
        Summable.tsum_le_tsum hb (hs.of_nonneg_of_le (fun k => norm_nonneg _) hb) hs
    _ = (∑' k, ‖g k‖ ^ 2) * ‖x‖ := tsum_mul_right

/-! ### The scalar trace is a center-valued trace of `M = 1 M 1` -/

/-- **H3 for a factor with a faithful tracial trace-class state**: `x ↦ τ(x) • 1` is a
center-valued trace of `M` (at the finite projection `1`); the comparison clauses are
`mvNEquiv_of_trace_eq` for `M` and for `M_n(M)`. -/
theorem isCenterValuedTrace_scalarTrace (M : VonNeumannAlgebra H)
    (hfactor : ∀ z ∈ M, (∀ y ∈ M, Commute z y) → ∃ c : ℂ, z = c • (1 : H →L[ℂ] H))
    (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hτ1 : τ 1 = 1) (hτ0 : ∀ x ∈ M, 0 ≤ τ (star x * x))
    (hτtr : ∀ x ∈ M, ∀ y ∈ M, τ (x * y) = τ (y * x))
    (hτf : ∀ x ∈ M, τ (star x * x) = 0 → x = 0)
    (hτg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, τ x = ∑' k, ⟪g k, x (g k)⟫_ℂ) :
    IsCenterValuedTrace M 1 (scalarTrace τ) where
  mem_center x _ _ := isCentralIn_smul_one M (τ x)
  nonneg x hx _ hx0 := smul_one_nonneg_of_nonneg (map_nonneg_of_mem hτ0 hx hx0)
  trace x hx _ y hy _ := by rw [scalarTrace_apply, scalarTrace_apply, hτtr x hx y hy]
  center_fixed c hc := by
    obtain ⟨l, rfl⟩ := eq_smul_one_of_isCentralIn hfactor hc
    rw [scalarTrace_apply, map_smul, hτ1, smul_eq_mul, mul_one]
  center_mul c hc x _ _ := by
    obtain ⟨l, rfl⟩ := eq_smul_one_of_isCentralIn hfactor hc
    rw [scalarTrace_apply, scalarTrace_apply, smul_mul_assoc, one_mul, map_smul, smul_eq_mul,
      mul_smul, smul_mul_assoc, one_mul]
  faithful x hx _ h := by
    rw [scalarTrace_apply] at h
    rcases smul_eq_zero.mp h with h0 | h1
    · exact hτf x hx h0
    · rw [← mul_one x, h1, mul_zero]
  normal l T L hT hL _ hTL := by
    obtain ⟨g, hg, hτg'⟩ := hτg
    have h := tendsto_of_tendstoWeakBdd_of_tsum hg hτg' (fun k => (hT k).1) hL hTL
    refine ⟨?_, fun ξ η => ?_⟩
    · obtain ⟨⟨C, hC⟩, -⟩ := hTL
      refine ⟨(∑' k, ‖g k‖ ^ 2) * C, fun k => ?_⟩
      show ‖scalarTrace τ (T k)‖ ≤ _
      rw [scalarTrace_apply, norm_smul]
      calc ‖τ (T k)‖ * ‖(1 : H →L[ℂ] H)‖ ≤ ‖τ (T k)‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ = ‖τ (T k)‖ := mul_one _
        _ ≤ (∑' j, ‖g j‖ ^ 2) * ‖T k‖ := norm_map_le_of_tsum hg hτg' (hT k).1
        _ ≤ (∑' j, ‖g j‖ ^ 2) * C :=
            mul_le_mul_of_nonneg_left (hC k) (tsum_nonneg fun j => by positivity)
    · simp only [scalarTrace_apply, smul_apply, one_apply_eq_self, inner_smul_right]
      exact h.mul_const _
  equiv_of_eq q q' hq hqM _ hq' hq'M _ h := by
    rw [scalarTrace_apply, scalarTrace_apply] at h
    rcases eq_or_ne (1 : H →L[ℂ] H) 0 with h1 | h1
    · have hq0 : q = 0 := by rw [← mul_one q, h1, mul_zero]
      have hq'0 : q' = 0 := by rw [← mul_one q', h1, mul_zero]
      rw [hq0, hq'0]
      exact MvNEquiv.refl (IsStarProjection.zero _) (zero_mem M)
    · exact mvNEquiv_of_trace_eq M hfactor τ hτ0 hτtr hτf (exists_polar M) hq hqM hq' hq'M
        (smul_left_injective ℂ h1 h)
  equiv_of_eq_matrix n P Q hPM hP _ hQM hQ _ h := by
    simp only [scalarTrace_apply, ← Finset.sum_smul] at h
    rcases eq_or_ne (1 : H →L[ℂ] H) 0 with h1 | h1
    · have hP0 : P = 0 := by
        refine ext_entry fun i j => ?_
        rw [entry_zero, ← mul_one (entry P i j), h1, mul_zero]
      have hQ0 : Q = 0 := by
        refine ext_entry fun i j => ?_
        rw [entry_zero, ← mul_one (entry Q i j), h1, mul_zero]
      rw [hP0, hQ0]
      exact MvNEquiv.refl (IsStarProjection.zero _) (zero_mem _)
    · have h' : diagTrace τ n P = diagTrace τ n Q := by
        rw [diagTrace_apply, diagTrace_apply]
        exact smul_left_injective ℂ h1 h
      exact mvNEquiv_of_trace_eq (matrixAlgebra M n) (matrixAlgebra_factor M hfactor n)
        (diagTrace τ n) (diagTrace_nonneg M τ hτ0 n) (diagTrace_trace M τ hτtr n)
        (diagTrace_faithful M τ hτ0 hτf n) (exists_polar _) hP hPM hQ hQM h'
  div r hr hrM _ b hbM hb0 hbr := by
    set tb : ℝ := (τ b).re with htb
    set tr : ℝ := (τ r).re with htr
    have hb0' : 0 ≤ tb := re_map_nonneg_of_mem hτ0 hbM hb0
    have hbre : τ b = (tb : ℂ) := map_eq_ofReal_re_of_mem hτ0 hbM hb0
    have hrre : τ r = (tr : ℂ) := map_eq_ofReal_re_of_mem hτ0 hrM hr.nonneg
    have hbr' : tb ≤ tr := re_map_le_of_mem hτ0 hbM hrM hbr
    have h10 : (0 : H →L[ℂ] H) ≤ 1 := star_mul_self_nonneg 1 |>.trans_eq (by rw [star_one, one_mul])
    rcases eq_or_ne tr 0 with hτr | hτr
    · -- `r = 0`, hence `b = 0`
      have hr0 : r = 0 := hτf r hrM (by
        rw [hr.isSelfAdjoint.star_eq, hr.isIdempotentElem.eq, hrre, hτr, Complex.ofReal_zero])
      have hb : b = 0 := le_antisymm (hr0 ▸ hbr) hb0
      refine ⟨0, isCentralIn_zero M 1, le_rfl, ?_, ?_⟩
      · exact le_one_of_isStarProjection (IsStarProjection.zero _)
      · rw [hb, map_zero, zero_mul]
    · have hτr' : 0 < tr := lt_of_le_of_ne (hb0'.trans hbr') (Ne.symm hτr)
      refine ⟨((tb / tr : ℝ) : ℂ) • 1, isCentralIn_smul_one M _, ?_, ?_, ?_⟩
      · exact smul_nonneg_real (div_nonneg hb0' hτr'.le) h10
      · have h := smul_le_smul_scalar (x := (1 : H →L[ℂ] H)) (div_le_one_of_le₀ hbr' hτr'.le) h10
        rwa [Complex.ofReal_one, one_smul] at h
      · rw [scalarTrace_apply, scalarTrace_apply, hbre, hrre, smul_mul_assoc, one_mul, smul_smul,
          ← Complex.ofReal_mul, div_mul_cancel₀ _ hτr]

end Orthogonalization.MvN

namespace Orthogonalization

open scoped BigOperators ComplexOrder InnerProductSpace
open MvN Blocks

universe u

set_option synthInstance.maxHeartbeats 100000

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Lemma 3.1 at `1` and the theorem -/

/-- **Theorem 1.2 for II₁ factors with a trace-class trace and trace-class states**: an
instance of the signed statement `povm_orthogonalization` (tier T4a). `M` has trivial
center (`hfactor`), no nonzero abelian projection (`hII`), and a faithful tracial state
`τ` of trace-class form; `φ` is a normal state of trace-class form. -/
theorem povm_orthogonalization_II₁Factor (M : VonNeumannAlgebra H)
    (hfactor : ∀ z ∈ M, (∀ y ∈ M, Commute z y) → ∃ c : ℂ, z = c • (1 : H →L[ℂ] H))
    (hII : ∀ r, IsAbelianProj M r → r = 0)
    (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hτ1 : τ 1 = 1) (hτ0 : ∀ x ∈ M, 0 ≤ τ (star x * x))
    (hτtr : ∀ x ∈ M, ∀ y ∈ M, τ (x * y) = τ (y * x))
    (hτf : ∀ x ∈ M, τ (star x * x) = 0 → x = 0)
    (hτg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, τ x = ∑' k, ⟪g k, x (g k)⟫_ℂ)
    (φ : NormalState M)
    (hφg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ)
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  set E := scalarTrace τ with hEdef
  have hE : IsCenterValuedTrace M 1 E :=
    isCenterValuedTrace_scalarTrace M hfactor τ hτ1 hτ0 hτtr hτf hτg
  have h1 : IsStarProjection (1 : H →L[ℂ] H) := IsStarProjection.one _
  -- the finite case at `p = 1`, output set `Fin n`, for the functional `φ`
  have hfin : ∀ n : ℕ, ∀ a : Fin n → H →L[ℂ] H, (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) →
      ∑ i, a i = 1 → ∀ ε : ℝ, 1 - ε < (φ (∑ i, a i * a i)).re →
      ∃ p : Fin n → H →L[ℂ] H, (∀ i, p i ∈ M) ∧ (∀ i, IsStarProjection (p i)) ∧
        ∑ i, p i = 1 ∧ (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
    intro n a haM ha0 ha1 ε hε
    -- Lemma 3.1 at `1`: the type I part is `c = 0`, the type II₁ part is all of `M`
    have hsel := selection_of_split M h1 (one_mem M) E (IsStarProjection.zero _) (isCentralIn_zero M 1)
      φ.toLinearMap
      (fun m a' ha'M ha'0 ha'c => by
        -- POVM summing to `0`: all `a'ᵢ = 0`
        have ha'z : ∀ i, a' i = 0 := fun i => by
          have := mul_eq_self_of_sum_eq (IsStarProjection.zero _) ha'0 ha'c i
          rwa [mul_zero, eq_comm] at this
        refine ⟨fun _ => 0, fun i => ⟨IsStarProjection.zero _, zero_mem M, mul_zero 0,
          Commute.zero_left _⟩, by simp, ?_⟩
        simp [ha'z])
      (fun m a' ha'M ha'0 ha'c =>
        exists_selection_typeII₁ M h1 (one_mem M) (c := 1 - 0)
          (by rw [sub_zero]; exact h1) (by rw [sub_zero]; exact isCentralIn_proj M h1 (one_mem M))
          (fun r hr _ => hII r hr) E hE a' ha'M ha'0 ha'c φ.toLinearMap hφg)
      n a haM ha0 ha1
    obtain ⟨q, hq, hqE, hqineq⟩ := hsel
    obtain ⟨p, hpM, hp, -, hsum, hlt⟩ := exists_pvm_bound_of_selection M h1 (one_mem M) E
      (hE.center_fixed 1 (isCentralIn_proj M h1 (one_mem M))) hE.trace (hE.equiv_of_eq_matrix n)
      (fun x hx => exists_polar (matrixAlgebra M n) x hx) φ.toLinearMap φ.nonneg' φ.map_one'
      a haM ha0 ha1 ε hε q hq hqE hqineq
    exact ⟨p, hpM, hp, hsum, hlt⟩
  -- transport to the output set `ι` along `Fintype.equivFin ι`
  set e := Fintype.equivFin ι with he
  have haM' : ∀ i, a (e.symm i) ∈ M := fun i => ha.1 _
  have ha0' : ∀ i, 0 ≤ a (e.symm i) := fun i =>
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (ha.2.1 _)
  have ha1' : ∑ i, a (e.symm i) = 1 := by rw [Equiv.sum_comp e.symm a]; exact ha.2.2
  have hε' : 1 - ε < (φ (∑ i, a (e.symm i) * a (e.symm i))).re := by
    rw [Equiv.sum_comp e.symm (fun i => a i * a i)]; exact hε
  obtain ⟨p', hp'M, hp', hp'sum, hlt⟩ := hfin _ (fun i => a (e.symm i)) haM' ha0' ha1' ε hε'
  refine ⟨fun i => p' (e i), ⟨fun i => hp'M _, fun i => hp' _, ?_⟩, ?_⟩
  · rw [← hp'sum]; exact Equiv.sum_comp e p'
  · have hsum : ∑ i, star (a i - p' (e i)) * (a i - p' (e i)) =
        ∑ j, star (a (e.symm j) - p' j) * (a (e.symm j) - p' j) := by
      rw [← Equiv.sum_comp e.symm (fun i => star (a i - p' (e i)) * (a i - p' (e i)))]
      simp only [Equiv.apply_symm_apply]
    rw [hsum]; exact hlt

end Orthogonalization
