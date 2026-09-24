/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Tsirelson.Positivstellensatz

/-!
# Exact certificates for upper bounds on the commuting-operator value

Step §3.5 of the Tsirelson route (`planning/tsirelson-campaign.md`): finite certificates, with
Gaussian-integer coefficients and an exact test, for strict upper bounds on the
commuting-operator value of a game, at the level of the game algebra `NCPoly (Gen X Y A B)`.
The coded layer only has to show that its checker computes this test on decoded data.

**Certificates.** Fix `κ > 0`; the coded layer takes `κ = q·W_d` and `r = p/q`, so that
`κ r·1 - κ W_G` has Gaussian-integer coefficients. A certificate is a scale `N ≥ 1`, a list `σ`
of hermitian squares `(g, s)` standing for `s⋆ g s`, with `g = none` read as `1` (`sosPoly`),
and a list `ι` of ideal monomials `(c, w, ρ, w')` standing for `c · w ρ w'`, with `w, w'` words
and `ρ ∈ rels X Y A B` (`idealPoly`), all with Gaussian-integer coefficients. The test is that
the hermitian part `T + T⋆` of the residual

  `T = N² (κ r·1 - κ W_G) - Σ s⋆ g s - Σ c · w ρ w'`

is *dominant* (`Dominant`): the real part of its constant coefficient strictly exceeds the
taxicab mass `Σ_{w ≠ 1} (|Re z_w| + |Im z_w|)` of its other coefficients.

**Soundness** (`commutingOperatorValue_lt_of_dominant`,
`commutingOperatorValue_lt_of_certificate`). Every word evaluates to a contraction, so the state
`φ` of a strategy satisfies `Re φ(z) ≥ Re z_1 - Σ_{w ≠ 1} (|Re z_w| + |Im z_w|)`
(`re_map_ge_of_norm_le`, `re_inner_eval_ge`). The state is hermitian, nonnegative on hermitian
squares, and zero on the relation ideal, so `Re φ(T + T⋆) = 2 Re φ(T) ≤ 2κ (r - value)`. The
dominance margin `δ` of `T + T⋆` depends only on `T`, so every strategy has value at most
`r - δ / (2κ)`, and so does the supremum (`ciSup_le`, which needs a strategy: the answer sets are
nonempty).

**Completeness** (`exists_certificate_of_lt`). Take `value < r' < r`. The Positivstellensatz
puts `κ (r'·1 - W_G)` in the cone `M`, and every element of `M` is `Σ s⋆ g s + j + a` with `j` in
the relation ideal and `a` anti-hermitian (`exists_decomp_of_mem_qmod`), where
`j = Σ c · w ρ w'` (`exists_idealPoly_eq_of_mem_relSpan`). So

  `κ r·1 - κ W_G = ε·1 + Σ s⋆ g s + Σ c · w ρ w' + a`,  `ε = κ (r - r') > 0`.

Round the coefficients of every `N s` and every `N² c` to Gaussian integers (`roundPoly`,
`roundC`), with taxicab error at most `1` per coefficient (`abs_sub_round`). The residual is then
`T = N² ε·1 + N² a + E`, where the rounding error satisfies `‖E‖₁ ≤ N C` for a constant `C` of the
decomposition (`l1_sq_smul_sosPoly_sub_le`, `l1_sq_smul_idealPoly_sub_le`: the `ℓ¹` norm
`NCPoly.l1` is subadditive, submultiplicative and invariant under the star). Symmetrizing kills
`N² a`: `T + T⋆ = 2 N² ε·1 + (E + E⋆)`, which is dominant as soon as `2 N C < 2 N² ε`
(`dominant_smul_one_add`), that is for `N > C / ε`. Completeness needs no integrality of
`κ r·1 - κ W_G`; that hypothesis is what makes the certificate encodable.

Together: for nonempty answer sets and any `κ > 0`, the value is below `r` exactly when a
certificate exists (`exists_certificate_iff`).

`Dominant` is defined with classical decidable equality of words; `dominant_iff` and
`dominant_iff_of_subset` restate it for any decidable equality, and as a sum over the nonempty
words of any finite set containing the support, which is the form the coded checker computes.

## Main declarations

* `sosPoly`, `idealPoly`, `sosPoly_mem_qmod`, `idealPoly_mem_relSpan`,
  `exists_idealPoly_eq_of_mem_relSpan`, `exists_decomp_of_mem_qmod`;
* `Dominant`, `dominant_iff`, `dominant_iff_of_subset`, `dominant_iff_l1`,
  `dominant_smul_one_add`, `re_map_ge_of_norm_le`;
* `roundC`, `roundPoly`, `roundSos`, `roundIdeal`, `l1_sq_smul_sub_roundPoly_le`,
  `l1_sq_smul_sub_roundC_le`, `l1_sq_smul_sosPoly_sub_le`, `l1_sq_smul_idealPoly_sub_le`;
* `re_inner_eval_ge`, `commutingOperatorValue_lt_of_dominant`,
  `commutingOperatorValue_lt_of_certificate`, `exists_certificate_of_lt`,
  `exists_certificate_iff`.
-/

noncomputable section

open ComplexConjugate
open scoped InnerProductSpace

namespace MIPRE

namespace Tsirelson

open NCPoly

/-! ## Sums of squares and ideal monomials -/

section Poly

variable {G : Type*}

/-- The sum of hermitian squares `Σ s⋆ g s` of a list of terms `(g, s)`, where `g = none` stands
for `1` and `g = some g'` for the letter `g'`. -/
def sosPoly (σ : List (Option G × NCPoly G)) : NCPoly G :=
  (σ.map fun p => star p.2 * p.1.elim 1 gen * p.2).sum

/-- The element `Σ c · w ρ w'` of the relation ideal of a list of ideal monomials
`(c, w, ρ, w')`: a scalar, two words, and a relation. -/
def idealPoly {R : Set (NCPoly G)} (ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) :
    NCPoly G :=
  (ι.map fun t => t.1 • (single t.2.1 1 * t.2.2.1.1 * single t.2.2.2 1)).sum

/-- The empty sum of hermitian squares. -/
@[simp] theorem sosPoly_nil : sosPoly ([] : List (Option G × NCPoly G)) = 0 := rfl

/-- A sum of hermitian squares, one term at a time. -/
@[simp] theorem sosPoly_cons (p : Option G × NCPoly G) (σ : List (Option G × NCPoly G)) :
    sosPoly (p :: σ) = star p.2 * p.1.elim 1 gen * p.2 + sosPoly σ := by
  simp [sosPoly]

/-- Sums of hermitian squares add under concatenation. -/
@[simp] theorem sosPoly_append (σ σ' : List (Option G × NCPoly G)) :
    sosPoly (σ ++ σ') = sosPoly σ + sosPoly σ' := by
  simp [sosPoly]

variable {R : Set (NCPoly G)}

/-- The empty combination of ideal monomials. -/
@[simp] theorem idealPoly_nil :
    idealPoly ([] : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) = 0 := rfl

/-- A combination of ideal monomials, one term at a time. -/
@[simp] theorem idealPoly_cons (t : ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)
    (ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) :
    idealPoly (t :: ι) = t.1 • (single t.2.1 1 * t.2.2.1.1 * single t.2.2.2 1) + idealPoly ι := by
  simp [idealPoly]

/-- Combinations of ideal monomials add under concatenation. -/
@[simp] theorem idealPoly_append (ι ι' : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) :
    idealPoly (ι ++ ι') = idealPoly ι + idealPoly ι' := by
  simp [idealPoly]

/-- The hermitian square `s⋆ g s` lies in the quadratic module. -/
theorem star_mul_elim_mul_mem_qmod (s : NCPoly G) (g : Option G) :
    star s * g.elim 1 gen * s ∈ qmod R :=
  PointedCone.subset_hull (Or.inl (Or.inl ⟨s, g, rfl⟩))

/-- A sum of hermitian squares lies in the quadratic module. -/
theorem sosPoly_mem_qmod (σ : List (Option G × NCPoly G)) : sosPoly σ ∈ qmod R := by
  induction σ with
  | nil => exact Submodule.zero_mem _
  | cons p σ ih => rw [sosPoly_cons]; exact Submodule.add_mem _ (star_mul_elim_mul_mem_qmod _ _) ih

/-- A combination of ideal monomials lies in the relation ideal. -/
theorem idealPoly_mem_relSpan (ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) :
    idealPoly ι ∈ relSpan R := by
  induction ι with
  | nil => exact Submodule.zero_mem _
  | cons t ι ih =>
    rw [idealPoly_cons]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (mul_mem_relSpan (mem_relSpan_of_mem t.2.2.1.2) _ _)) ih

/-- Scaling the scalars of a list of ideal monomials. -/
theorem idealPoly_map_mul (c : ℂ) (ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) :
    idealPoly (ι.map fun t => (c * t.1, t.2)) = c • idealPoly ι := by
  induction ι with
  | nil => simp
  | cons t ι ih => simp [ih, smul_add, mul_smul]

/-- Scaling the vectors of a list of hermitian squares. -/
theorem sosPoly_map_smul (c : ℂ) (σ : List (Option G × NCPoly G)) :
    sosPoly (σ.map fun p => (p.1, c • p.2)) = (conj c * c) • sosPoly σ := by
  induction σ with
  | nil => simp
  | cons p σ ih =>
    simp only [List.map_cons, sosPoly_cons, ih, smul_add, star_smul, smul_mul_assoc,
      mul_smul_comm, smul_smul, Complex.star_def]
    ring_nf

/-- Every `u ρ v` is a combination of ideal monomials `c · w ρ w'`. -/
theorem exists_idealPoly_eq_mul_mul (u : NCPoly G) {ρ : NCPoly G} (hρ : ρ ∈ R) (v : NCPoly G) :
    ∃ ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G), idealPoly ι = u * ρ * v := by
  induction u using induction_linear with
  | zero => exact ⟨[], by simp⟩
  | add u₁ u₂ h₁ h₂ =>
    obtain ⟨ι₁, e₁⟩ := h₁
    obtain ⟨ι₂, e₂⟩ := h₂
    exact ⟨ι₁ ++ ι₂, by rw [idealPoly_append, e₁, e₂, add_mul, add_mul]⟩
  | single w c =>
    induction v using induction_linear with
    | zero => exact ⟨[], by simp⟩
    | add v₁ v₂ h₁ h₂ =>
      obtain ⟨ι₁, e₁⟩ := h₁
      obtain ⟨ι₂, e₂⟩ := h₂
      exact ⟨ι₁ ++ ι₂, by rw [idealPoly_append, e₁, e₂, mul_add]⟩
    | single w' c' =>
      refine ⟨[(c * c', w, ⟨ρ, hρ⟩, w')], ?_⟩
      rw [idealPoly_cons, idealPoly_nil, add_zero, single_eq_smul_single_one w c,
        single_eq_smul_single_one w' c', smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        smul_smul]

/-- **Monomial decomposition of the relation ideal.** Every element of the relation ideal is a
finite combination of ideal monomials `c · w ρ w'`, with `w, w'` words and `ρ ∈ R`. -/
theorem exists_idealPoly_eq_of_mem_relSpan {j : NCPoly G} (hj : j ∈ relSpan R) :
    ∃ ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G), idealPoly ι = j := by
  induction hj using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, ρ, v, hρ, rfl⟩ := hx
    exact exists_idealPoly_eq_mul_mul u hρ v
  | zero => exact ⟨[], rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨ι₁, rfl⟩ := hx
    obtain ⟨ι₂, rfl⟩ := hy
    exact ⟨ι₁ ++ ι₂, idealPoly_append _ _⟩
  | smul c x _ hx =>
    obtain ⟨ι, rfl⟩ := hx
    exact ⟨ι.map fun t => (c * t.1, t.2), idealPoly_map_mul c ι⟩

/-- **Decomposition of the quadratic module.** Every element of `qmod R` is a sum of hermitian
squares `s⋆ g s`, an element of the relation ideal, and an anti-hermitian element. -/
theorem exists_decomp_of_mem_qmod {m : NCPoly G} (hm : m ∈ qmod R) :
    ∃ (σ : List (Option G × NCPoly G)) (j a : NCPoly G),
      j ∈ relSpan R ∧ star a = -a ∧ m = sosPoly σ + j + a := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rcases hx with (⟨s, g, rfl⟩ | hx) | hx
    · exact ⟨[(g, s)], 0, 0, Submodule.zero_mem _, by simp, by simp⟩
    · exact ⟨[], x, 0, hx, by simp, by simp⟩
    · exact ⟨[], 0, x, Submodule.zero_mem _, skewAdjoint.mem_iff.mp hx, by simp⟩
  | zero => exact ⟨[], 0, 0, Submodule.zero_mem _, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨σ₁, j₁, a₁, hj₁, ha₁, rfl⟩ := hx
    obtain ⟨σ₂, j₂, a₂, hj₂, ha₂, rfl⟩ := hy
    refine ⟨σ₁ ++ σ₂, j₁ + j₂, a₁ + a₂, Submodule.add_mem _ hj₁ hj₂, ?_, ?_⟩
    · rw [star_add, ha₁, ha₂, neg_add]
    · rw [sosPoly_append]; abel
  | smul c x _ hx =>
    obtain ⟨σ, j, a, hj, ha, rfl⟩ := hx
    have hc : ∀ z : NCPoly G, c • z = ((c : ℝ) : ℂ) • z := fun _ => rfl
    have hsq : conj ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt c.2]
    refine ⟨σ.map fun p => (p.1, ((Real.sqrt c : ℝ) : ℂ) • p.2), ((c : ℝ) : ℂ) • j,
      ((c : ℝ) : ℂ) • a, Submodule.smul_mem _ _ hj, ?_, ?_⟩
    · rw [star_smul, ha, smul_neg, Complex.star_def, Complex.conj_ofReal]
    · rw [hc, sosPoly_map_smul, hsq, smul_add, smul_add]

end Poly

/-! ## Dominance -/

section Dominance

variable {G : Type*}

open Classical in
/-- A polynomial is **dominant** if the real part of its constant coefficient strictly exceeds
the taxicab mass of its other coefficients:
`Σ_{w ≠ 1} (|Re z_w| + |Im z_w|) < Re z_1`. -/
def Dominant (z : NCPoly G) : Prop :=
  ∑ w ∈ z.coeff.support.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) < (z.coeff 1).re

/-- The off-unit mass as a sum over the nonempty words of any finite set of words containing
the support. -/
theorem sum_erase_one_eq_of_subset [DecidableEq (FreeMonoid G)] (z : NCPoly G)
    {s : Finset (FreeMonoid G)} (hs : z.coeff.support ⊆ s) :
    ∑ w ∈ z.coeff.support.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) =
      ∑ w ∈ s.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) :=
  Finset.sum_subset (Finset.erase_subset_erase 1 hs) fun w hws hw => by
    have : w ∉ z.coeff.support := fun h => hw (Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hws).1, h⟩)
    simp [Finsupp.notMem_support_iff.mp this]

/-- Dominance, over the nonempty words of any finite set of words containing the support. -/
theorem dominant_iff_of_subset [DecidableEq (FreeMonoid G)] (z : NCPoly G)
    {s : Finset (FreeMonoid G)} (hs : z.coeff.support ⊆ s) :
    Dominant z ↔
      ∑ w ∈ s.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) < (z.coeff 1).re := by
  rw [← sum_erase_one_eq_of_subset z hs, Dominant]
  congr! 3

/-- Dominance, for any decidable equality on words. -/
theorem dominant_iff [DecidableEq (FreeMonoid G)] (z : NCPoly G) :
    Dominant z ↔ ∑ w ∈ z.coeff.support.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) <
      (z.coeff 1).re :=
  dominant_iff_of_subset z subset_rfl

/-- The `ℓ¹` norm splits into the constant coefficient and the off-unit mass. -/
theorem l1_eq_add_sum_erase_one [DecidableEq (FreeMonoid G)] (z : NCPoly G) :
    l1 z = (|(z.coeff 1).re| + |(z.coeff 1).im|) +
      ∑ w ∈ z.coeff.support.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) := by
  rw [sum_erase_one_eq_of_subset z (Finset.subset_insert 1 _),
    l1_eq_sum_of_subset z (Finset.subset_insert 1 _)]
  exact (Finset.add_sum_erase _ (fun w => |(z.coeff w).re| + |(z.coeff w).im|)
    (Finset.mem_insert_self 1 _)).symm

/-- Dominance in terms of the `ℓ¹` norm. -/
theorem dominant_iff_l1 (z : NCPoly G) :
    Dominant z ↔ l1 z < (z.coeff 1).re + (|(z.coeff 1).re| + |(z.coeff 1).im|) := by
  classical
  rw [dominant_iff, l1_eq_add_sum_erase_one]
  constructor <;> intro h <;> linarith

/-- **A perturbation of a positive multiple of the unit is dominant**: if `‖e‖₁ < c`, then
`c·1 + e` is dominant. -/
theorem dominant_smul_one_add {c : ℝ} {e : NCPoly G} (h : l1 e < c) :
    Dominant ((c : ℂ) • (1 : NCPoly G) + e) := by
  classical
  have hcoeff : ∀ w, ((c : ℂ) • (1 : NCPoly G) + e).coeff w =
      (if (1 : FreeMonoid G) = w then (c : ℂ) else 0) + e.coeff w := by
    intro w
    rw [coeff_add, coeff_smul, coeff_one, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  have hs : ((c : ℂ) • (1 : NCPoly G) + e).coeff.support ⊆ insert 1 e.coeff.support := by
    intro w hw
    rw [Finsupp.mem_support_iff, hcoeff] at hw
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases h1 : (1 : FreeMonoid G) = w
    · exact Or.inl h1.symm
    · right; simpa [h1] using hw
  rw [dominant_iff_of_subset _ hs, hcoeff, if_pos rfl]
  have hsum : ∑ w ∈ (insert 1 e.coeff.support).erase 1,
      (|(((c : ℂ) • (1 : NCPoly G) + e).coeff w).re| +
        |(((c : ℂ) • (1 : NCPoly G) + e).coeff w).im|) =
      ∑ w ∈ e.coeff.support.erase 1, (|(e.coeff w).re| + |(e.coeff w).im|) := by
    rw [Finset.erase_insert_eq_erase]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hcoeff, if_neg (Ne.symm (Finset.mem_erase.mp hw).1), zero_add]
  rw [hsum]
  have hl1 := l1_eq_add_sum_erase_one e
  have hre := neg_abs_le (e.coeff 1).re
  have him := abs_nonneg (e.coeff 1).im
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

/-- **The dominance margin bounds every normalized functional that is bounded by `1` on
words.** For a `ℂ`-linear functional `L` with `L 1 = 1` and `‖L w‖ ≤ 1` on every word,
`Re L z ≥ Re z_1 - Σ_{w ≠ 1} (|Re z_w| + |Im z_w|)`; in particular `Re L z > 0` when `z` is
dominant. -/
theorem re_map_ge_of_norm_le [DecidableEq (FreeMonoid G)] (L : NCPoly G →ₗ[ℂ] ℂ)
    (h1 : L 1 = 1) (hw : ∀ w, ‖L (single w 1)‖ ≤ 1) (z : NCPoly G) :
    (z.coeff 1).re - ∑ w ∈ z.coeff.support.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) ≤
      (L z).re := by
  set s := insert 1 z.coeff.support
  have hz : z = ∑ w ∈ s, z.coeff w • single w 1 := by
    conv_lhs => rw [← sum_support_single z]
    refine Finset.sum_subset (Finset.subset_insert 1 _) (fun w _ hw => ?_) |>.trans ?_
    · rw [Finsupp.notMem_support_iff.mp hw, single_zero]
    · exact Finset.sum_congr rfl fun w _ => single_eq_smul_single_one w _
  have hLz : L z = z.coeff 1 + ∑ w ∈ s.erase 1, z.coeff w * L (single w 1) := by
    conv_lhs => rw [hz]
    rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self 1 _), map_smul,
      ← one_def, h1, smul_eq_mul, mul_one]
    simp only [map_smul, smul_eq_mul]
    rfl
  have hterm : ∀ w, -(|(z.coeff w).re| + |(z.coeff w).im|) ≤ (z.coeff w * L (single w 1)).re := by
    intro w
    have h2 : ‖z.coeff w * L (single w 1)‖ ≤ ‖z.coeff w‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hw w)
    have h3 := Complex.norm_le_abs_re_add_abs_im (z.coeff w)
    have h4 := Complex.abs_re_le_norm (z.coeff w * L (single w 1))
    have h5 := neg_abs_le (z.coeff w * L (single w 1)).re
    linarith
  rw [hLz, Complex.add_re, Complex.re_sum, Finset.erase_insert_eq_erase]
  have := Finset.sum_le_sum fun w (_ : w ∈ z.coeff.support.erase 1) => hterm w
  rw [Finset.sum_neg_distrib] at this
  linarith

end Dominance

/-! ## Rounding to Gaussian integers -/

section Rounding

variable {G : Type*}

/-- Rounding a complex number to a nearest Gaussian integer, coordinatewise. -/
def roundC (z : ℂ) : ℂ := (round z.re : ℂ) + (round z.im : ℂ) * Complex.I

/-- A rounded complex number is a Gaussian integer. -/
theorem exists_roundC_eq (z : ℂ) : ∃ m n : ℤ, roundC z = m + n * Complex.I := ⟨_, _, rfl⟩

/-- Rounding fixes `0`. -/
@[simp] theorem roundC_zero : roundC 0 = 0 := by simp [roundC]

/-- The rounding error of a complex number has taxicab norm at most `1`. -/
theorem abs_re_add_abs_im_roundC_sub_le (z : ℂ) :
    |(roundC z - z).re| + |(roundC z - z).im| ≤ 1 := by
  have h1 := abs_sub_round z.re
  have h2 := abs_sub_round z.im
  rw [abs_sub_comm] at h1 h2
  simp only [roundC, Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.mul_re,
    Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im,
    Complex.mul_im]
  simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add]
  linarith

/-- Rounding a polynomial coefficientwise to Gaussian integers. -/
def roundPoly (s : NCPoly G) : NCPoly G := ofCoeff (s.coeff.mapRange roundC roundC_zero)

/-- The coefficients of a rounded polynomial. -/
@[simp] theorem coeff_roundPoly (s : NCPoly G) (w : FreeMonoid G) :
    (roundPoly s).coeff w = roundC (s.coeff w) := by
  simp [roundPoly]

/-- The coefficients of a rounded polynomial are Gaussian integers. -/
theorem exists_coeff_roundPoly_eq (s : NCPoly G) (w : FreeMonoid G) :
    ∃ m n : ℤ, (roundPoly s).coeff w = m + n * Complex.I := by
  rw [coeff_roundPoly]; exact exists_roundC_eq _

/-- The rounding error of a polynomial has `ℓ¹` norm at most the size of its support. -/
theorem l1_roundPoly_sub_le (s : NCPoly G) :
    l1 (roundPoly s - s) ≤ s.coeff.support.card := by
  have hs : (roundPoly s - s).coeff.support ⊆ s.coeff.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    intro h0
    apply hw
    simp [h0]
  rw [l1_eq_sum_of_subset _ hs, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun w _ => ?_
  simpa using abs_re_add_abs_im_roundC_sub_le (s.coeff w)

/-- The `ℓ¹` norm of a product of three factors. -/
theorem l1_mul_mul_le (x y z : NCPoly G) : l1 (x * y * z) ≤ l1 x * l1 y * l1 z :=
  (l1_mul_le _ _).trans (mul_le_mul_of_nonneg_right (l1_mul_le _ _) (l1_nonneg _))

/-- The unit and the letters have `ℓ¹` norm `1`. -/
theorem l1_elim_one_gen (g : Option G) : l1 (g.elim 1 gen : NCPoly G) = 1 := by
  cases g <;> simp [one_def, gen]

/-- A monomial `w ρ w'` has `ℓ¹` norm at most that of `ρ`. -/
theorem l1_single_mul_mul_single_le (w w' : FreeMonoid G) (ρ : NCPoly G) :
    l1 (single w 1 * ρ * single w' 1) ≤ l1 ρ := by
  simpa using l1_mul_mul_le (single w 1) ρ (single w' 1)

/-- **Rounding a hermitian square at scale `N`.** With `K` the size of the support of `s`, the
rounding `s̃` of `N s` satisfies `‖N² s⋆ g s - s̃⋆ g s̃‖₁ ≤ N (2 K ‖s‖₁ + K²)`. -/
theorem l1_sq_smul_sub_roundPoly_le {N : ℕ} (hN : 1 ≤ N) (g : Option G) (s : NCPoly G) :
    l1 (((N : ℂ) ^ 2) • (star s * g.elim 1 gen * s) -
        star (roundPoly ((N : ℂ) • s)) * g.elim 1 gen * roundPoly ((N : ℂ) • s)) ≤
      N * (2 * s.coeff.support.card * l1 s + (s.coeff.support.card : ℝ) ^ 2) := by
  set K : ℝ := (s.coeff.support.card : ℝ)
  set t : NCPoly G := (N : ℂ) • s
  set d : NCPoly G := roundPoly t - t
  set g' : NCPoly G := g.elim 1 gen
  have hK : l1 d ≤ K := by
    refine (l1_roundPoly_sub_le t).trans ?_
    have hsub : t.coeff.support ⊆ s.coeff.support := by
      rw [coeff_smul]; exact Finsupp.support_smul
    exact Nat.cast_le.mpr (Finset.card_le_card hsub)
  have ht : l1 t ≤ N * l1 s := by
    refine (l1_smul_le _ _).trans ?_
    simp
  have hg : l1 g' = 1 := l1_elim_one_gen g
  have hround : roundPoly t = t + d := by rw [add_sub_cancel]
  have hst : ((N : ℂ) ^ 2) • (star s * g' * s) = star t * g' * t := by
    rw [star_smul, Complex.star_def, Complex.conj_natCast, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm, smul_smul, sq]
  have key : ((N : ℂ) ^ 2) • (star s * g' * s) - star (roundPoly t) * g' * roundPoly t =
      -(star d * g' * t + star t * g' * d + star d * g' * d) := by
    rw [hst, hround, star_add]
    noncomm_ring
  rw [key, l1_neg]
  have hd0 := l1_nonneg d
  have ht0 := l1_nonneg t
  have hs0 := l1_nonneg s
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc l1 (star d * g' * t + star t * g' * d + star d * g' * d)
      ≤ l1 d * l1 t + l1 t * l1 d + l1 d * l1 d := by
        refine (l1_add_le _ _).trans (add_le_add ((l1_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · exact (l1_mul_mul_le _ _ _).trans (by rw [l1_star, hg, mul_one])
        · exact (l1_mul_mul_le _ _ _).trans (by rw [l1_star, hg, mul_one])
        · exact (l1_mul_mul_le _ _ _).trans (by rw [l1_star, hg, mul_one])
    _ ≤ K * (N * l1 s) + (N * l1 s) * K + K * K :=
        add_le_add (add_le_add (mul_le_mul hK ht ht0 hK0)
          (mul_le_mul ht hK hd0 (mul_nonneg (Nat.cast_nonneg _) hs0))) (mul_le_mul hK hK hd0 hK0)
    _ ≤ N * (2 * K * l1 s + K ^ 2) := by nlinarith

/-- **Rounding an ideal monomial at scale `N²`.** Rounding the scalar `N² c` of
`N² c · w ρ w'` costs at most `‖ρ‖₁`. -/
theorem l1_sq_smul_sub_roundC_le (N : ℕ) (c : ℂ) (w w' : FreeMonoid G) (ρ : NCPoly G) :
    l1 (((N : ℂ) ^ 2) • (c • (single w 1 * ρ * single w' 1)) -
        roundC ((N : ℂ) ^ 2 * c) • (single w 1 * ρ * single w' 1)) ≤ l1 ρ := by
  rw [smul_smul, ← sub_smul, ← neg_sub, neg_smul, l1_neg]
  refine (l1_smul_le _ _).trans ?_
  calc _ ≤ 1 * l1 (single w 1 * ρ * single w' 1) :=
        mul_le_mul_of_nonneg_right (abs_re_add_abs_im_roundC_sub_le _) (l1_nonneg _)
    _ ≤ l1 ρ := by rw [one_mul]; exact l1_single_mul_mul_single_le w w' ρ

/-- Rounding a list of hermitian squares at scale `N`. -/
def roundSos (N : ℕ) (σ : List (Option G × NCPoly G)) : List (Option G × NCPoly G) :=
  σ.map fun p => (p.1, roundPoly ((N : ℂ) • p.2))

/-- Rounding a list of ideal monomials at scale `N²`. -/
def roundIdeal {R : Set (NCPoly G)} (N : ℕ)
    (ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) :
    List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G) :=
  ι.map fun t => (roundC ((N : ℂ) ^ 2 * t.1), t.2)

/-- The error bound for rounding a list of hermitian squares at scale `N`. -/
theorem l1_sq_smul_sosPoly_sub_le {N : ℕ} (hN : 1 ≤ N) (σ : List (Option G × NCPoly G)) :
    l1 (((N : ℂ) ^ 2) • sosPoly σ - sosPoly (roundSos N σ)) ≤
      N * (σ.map fun p => 2 * p.2.coeff.support.card * l1 p.2 +
        (p.2.coeff.support.card : ℝ) ^ 2).sum := by
  induction σ with
  | nil => simp [roundSos]
  | cons p σ ih =>
    simp only [roundSos, List.map_cons, sosPoly_cons, List.sum_cons] at ih ⊢
    rw [smul_add, add_sub_add_comm, mul_add]
    exact (l1_add_le _ _).trans (add_le_add (l1_sq_smul_sub_roundPoly_le hN p.1 p.2) ih)

/-- The error bound for rounding a list of ideal monomials at scale `N²`. -/
theorem l1_sq_smul_idealPoly_sub_le {R : Set (NCPoly G)} (N : ℕ)
    (ι : List (ℂ × FreeMonoid G × {ρ // ρ ∈ R} × FreeMonoid G)) :
    l1 (((N : ℂ) ^ 2) • idealPoly ι - idealPoly (roundIdeal N ι)) ≤
      (ι.map fun t => l1 t.2.2.1.1).sum := by
  induction ι with
  | nil => simp [roundIdeal]
  | cons t ι ih =>
    simp only [roundIdeal, List.map_cons, idealPoly_cons, List.sum_cons] at ih ⊢
    rw [smul_add, add_sub_add_comm]
    exact (l1_add_le _ _).trans (add_le_add (l1_sq_smul_sub_roundC_le N _ _ _ _) ih)

end Rounding

/-! ## Certificates for the commuting-operator value -/

section Game

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **Every strategy is bounded below by the dominance margin.** For a commuting-operator
strategy `S` and a polynomial `z`, `Re ⟪ψ, π_S(z) ψ⟫ ≥ Re z_1 - Σ_{w ≠ 1} (|Re z_w| + |Im z_w|)`:
every word evaluates to a contraction. -/
theorem re_inner_eval_ge [DecidableEq (FreeMonoid (Gen X Y A B))]
    (S : CommutingOperatorStrategy X Y A B) (z : NCPoly (Gen X Y A B)) :
    (z.coeff 1).re - ∑ w ∈ z.coeff.support.erase 1, (|(z.coeff w).re| + |(z.coeff w).im|) ≤
      (⟪S.ψ, NCPoly.eval (stratEval S) z S.ψ⟫_ℂ).re :=
  re_map_ge_of_norm_le (stateOf S) (isConeState_stateOf S).map_one
    (norm_stateOf_single_one_le S) z

/-- **Soundness of dominant certificates.** Let `κ > 0`, `σ` a list of hermitian squares and
`j` an element of the relation ideal. If the hermitian part `T + T⋆` of
`T = κ r·1 - κ W_G - Σ s⋆ g s - j` is dominant, then the commuting-operator value of `G` is
strictly below `r`. The margin `δ` of `T + T⋆` bounds `2κ (r - value)` below for every strategy,
uniformly, so the supremum stays below `r - δ / (2κ)`. -/
theorem commutingOperatorValue_lt_of_dominant [Nonempty A] [Nonempty B] (G : Game X Y A B)
    {κ r : ℝ} (hκ : 0 < κ) (σ : List (Option (Gen X Y A B) × NCPoly (Gen X Y A B)))
    {j : NCPoly (Gen X Y A B)} (hj : j ∈ NCPoly.relSpan (rels X Y A B))
    (hT : Dominant (((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G - sosPoly σ - j) +
      star ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G - sosPoly σ - j))) :
    commutingOperatorValue G < r := by
  classical
  set T := (κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G - sosPoly σ - j with hTdef
  rw [dominant_iff] at hT
  set δ := ((T + star T).coeff 1).re - ∑ w ∈ (T + star T).coeff.support.erase 1,
    (|((T + star T).coeff w).re| + |((T + star T).coeff w).im|)
  have hδpos : 0 < δ := sub_pos.mpr hT
  have hS : ∀ S : CommutingOperatorStrategy X Y A B, S.value G ≤ r - δ / (2 * κ) := by
    intro S
    have hL := isConeState_stateOf S
    have h1 : δ ≤ (stateOf S (T + star T)).re :=
      re_map_ge_of_norm_le (stateOf S) hL.map_one (norm_stateOf_single_one_le S) _
    have h2 : (stateOf S (T + star T)).re = 2 * (stateOf S T).re := by
      rw [map_add, hL.map_star, Complex.add_re, Complex.conj_re]; ring
    have hsos : 0 ≤ (stateOf S (sosPoly σ)).re := hL.re_nonneg _ (sosPoly_mem_qmod σ)
    have hj0 : stateOf S j = 0 := hL.map_eq_zero_of_mem_relSpan hj
    have hreal : ∀ (c : ℝ) (x : NCPoly (Gen X Y A B)), c • x = (c : ℂ) • x := fun _ _ => rfl
    have h3 : (stateOf S T).re = κ * r - κ * S.value G - (stateOf S (sosPoly σ)).re := by
      rw [hTdef, map_sub, map_sub, map_sub, hreal, hreal, map_smul, map_smul, hL.map_one, hj0,
        ← re_stateOf_gamePoly S G]
      simp
    have h4 : δ ≤ 2 * κ * (r - S.value G) := by nlinarith
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by positivity)]
    linarith
  have hle : commutingOperatorValue G ≤ r - δ / (2 * κ) := ciSup_le hS
  have : 0 < δ / (2 * κ) := by positivity
  linarith

/-- **Soundness of exact certificates.** If, at a scale `N ≥ 1`, the hermitian part of
`T = N² (κ r·1 - κ W_G) - Σ s⋆ g s - Σ c · w ρ w'` is dominant, then the commuting-operator value
of `G` is strictly below `r`. This is `commutingOperatorValue_lt_of_dominant` at `N² κ`; the
coefficients need not be Gaussian integers. -/
theorem commutingOperatorValue_lt_of_certificate [Nonempty A] [Nonempty B] (G : Game X Y A B)
    {κ r : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N)
    (σ : List (Option (Gen X Y A B) × NCPoly (Gen X Y A B)))
    (ι : List (ℂ × FreeMonoid (Gen X Y A B) × {ρ // ρ ∈ rels X Y A B} ×
      FreeMonoid (Gen X Y A B)))
    (hdom : Dominant ((((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) -
        κ • gamePoly G) - sosPoly σ - idealPoly ι) +
      star (((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G) -
        sosPoly σ - idealPoly ι))) :
    commutingOperatorValue G < r := by
  have hN0 : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hreal : ∀ (c : ℝ) (x : NCPoly (Gen X Y A B)), c • x = (c : ℂ) • x := fun _ _ => rfl
  have heq : ((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G) =
      ((N ^ 2 * κ) * r) • (1 : NCPoly (Gen X Y A B)) - (N ^ 2 * κ) • gamePoly G := by
    rw [hreal, hreal, hreal, hreal, smul_sub, smul_smul, smul_smul]
    push_cast
    ring_nf
  rw [heq] at hdom
  exact commutingOperatorValue_lt_of_dominant G (mul_pos hN0 hκ) σ (idealPoly_mem_relSpan ι) hdom

/-- **Completeness of dominant certificates.** If the commuting-operator value of `G` is
strictly below `r` and `κ > 0`, then for some scale `N ≥ 1` there are hermitian squares `σ` and
ideal monomials `ι`, all with Gaussian-integer coefficients, such that the hermitian part of
`T = N² (κ r·1 - κ W_G) - Σ s⋆ g s - Σ c · w ρ w'` is dominant. -/
theorem exists_certificate_of_lt (G : Game X Y A B) {κ r : ℝ} (hκ : 0 < κ)
    (hlt : commutingOperatorValue G < r) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ (σ : List (Option (Gen X Y A B) × NCPoly (Gen X Y A B)))
      (ι : List (ℂ × FreeMonoid (Gen X Y A B) × {ρ // ρ ∈ rels X Y A B} ×
        FreeMonoid (Gen X Y A B))),
      (∀ p ∈ σ, ∀ w, ∃ m n : ℤ, p.2.coeff w = m + n * Complex.I) ∧
      (∀ t ∈ ι, ∃ m n : ℤ, t.1 = m + n * Complex.I) ∧
      Dominant ((((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G) -
          sosPoly σ - idealPoly ι) +
        star (((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G) -
          sosPoly σ - idealPoly ι)) := by
  obtain ⟨r', hr'1, hr'2⟩ := exists_between hlt
  have hm := PointedCone.smul_mem _ hκ.le (sub_gamePoly_mem_cone_of_lt G hr'1)
  obtain ⟨σ₀, j, a, hj, ha, hdec⟩ := exists_decomp_of_mem_qmod hm
  obtain ⟨ι₀, rfl⟩ := exists_idealPoly_eq_of_mem_relSpan hj
  set ε := κ * (r - r') with hεdef
  have hε : 0 < ε := mul_pos hκ (sub_pos.mpr hr'2)
  have hh₀ : (κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G =
      ε • 1 + (sosPoly σ₀ + idealPoly ι₀ + a) := by
    rw [← hdec, hεdef]
    module
  set C := (σ₀.map fun p => 2 * (p.2.coeff.support.card : ℝ) * l1 p.2 +
    (p.2.coeff.support.card : ℝ) ^ 2).sum + (ι₀.map fun t => l1 t.2.2.1.1).sum with hC
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hN1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have hNC : C < ((n + 1 : ℕ) : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hn
    push_cast
    nlinarith
  refine ⟨n + 1, hN1, roundSos (n + 1) σ₀, roundIdeal (n + 1) ι₀, ?_, ?_, ?_⟩
  · intro p hp w
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    exact exists_coeff_roundPoly_eq _ _
  · intro t ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
    exact exists_roundC_eq _
  set N : ℕ := n + 1
  set E := (((N : ℂ) ^ 2) • sosPoly σ₀ - sosPoly (roundSos N σ₀)) +
    (((N : ℂ) ^ 2) • idealPoly ι₀ - idealPoly (roundIdeal N ι₀)) with hE
  have hreal : ∀ (c : ℝ) (x : NCPoly (Gen X Y A B)), c • x = (c : ℂ) • x := fun _ _ => rfl
  have hT : ((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G) -
      sosPoly (roundSos N σ₀) - idealPoly (roundIdeal N ι₀) =
      ((N : ℂ) ^ 2 * ε) • 1 + (((N : ℂ) ^ 2) • a + E) := by
    rw [hh₀, hE, hreal ε, smul_add, smul_add, smul_add, smul_smul]
    abel
  have hsa : star (((N : ℂ) ^ 2) • a) = -(((N : ℂ) ^ 2) • a) := by
    rw [star_smul, ha, smul_neg, Complex.star_def, map_pow, Complex.conj_natCast]
  have hsc : star (((N : ℂ) ^ 2 * ε) • (1 : NCPoly (Gen X Y A B))) =
      ((N : ℂ) ^ 2 * ε) • 1 := by
    rw [star_smul, star_one, Complex.star_def, map_mul, map_pow, Complex.conj_natCast,
      Complex.conj_ofReal]
  have hTT : ((N : ℂ) ^ 2 * ε) • (1 : NCPoly (Gen X Y A B)) + (((N : ℂ) ^ 2) • a + E) +
      star (((N : ℂ) ^ 2 * ε) • (1 : NCPoly (Gen X Y A B)) + (((N : ℂ) ^ 2) • a + E)) =
      ((2 * (N ^ 2 * ε) : ℝ) : ℂ) • 1 + (E + star E) := by
    rw [star_add, star_add, hsa, hsc]
    push_cast
    rw [two_mul, add_smul]
    abel
  rw [hT, hTT]
  apply dominant_smul_one_add
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hCι : 0 ≤ (ι₀.map fun t => l1 t.2.2.1.1).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
      exact l1_nonneg _
  have hEle : l1 E ≤ N * C := by
    refine (l1_add_le _ _).trans ?_
    have h1 := l1_sq_smul_sosPoly_sub_le hN1 σ₀
    have h2 := l1_sq_smul_idealPoly_sub_le N ι₀
    rw [hC, mul_add]
    nlinarith
  calc l1 (E + star E) ≤ l1 E + l1 E := by simpa using l1_add_le E (star E)
    _ ≤ 2 * (N * C) := by linarith
    _ < 2 * (N ^ 2 * ε) := by
        have hN0 : (0 : ℝ) < N := by linarith
        nlinarith

/-- **Exact certificates characterize strict upper bounds on the commuting-operator value**, for
nonempty answer sets and any `κ > 0`: the value is below `r` exactly when, at some scale
`N ≥ 1`, hermitian squares and ideal monomials with Gaussian-integer coefficients make the
hermitian part of `N² (κ r·1 - κ W_G) - Σ s⋆ g s - Σ c · w ρ w'` dominant. -/
theorem exists_certificate_iff [Nonempty A] [Nonempty B] (G : Game X Y A B) {κ r : ℝ}
    (hκ : 0 < κ) :
    commutingOperatorValue G < r ↔
      ∃ N : ℕ, 1 ≤ N ∧ ∃ (σ : List (Option (Gen X Y A B) × NCPoly (Gen X Y A B)))
        (ι : List (ℂ × FreeMonoid (Gen X Y A B) × {ρ // ρ ∈ rels X Y A B} ×
          FreeMonoid (Gen X Y A B))),
        (∀ p ∈ σ, ∀ w, ∃ m n : ℤ, p.2.coeff w = m + n * Complex.I) ∧
        (∀ t ∈ ι, ∃ m n : ℤ, t.1 = m + n * Complex.I) ∧
        Dominant ((((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G) -
            sosPoly σ - idealPoly ι) +
          star (((N : ℂ) ^ 2) • ((κ * r) • (1 : NCPoly (Gen X Y A B)) - κ • gamePoly G) -
            sosPoly σ - idealPoly ι)) := by
  refine ⟨exists_certificate_of_lt G hκ, ?_⟩
  rintro ⟨N, hN, σ, ι, -, -, hdom⟩
  exact commutingOperatorValue_lt_of_certificate G hκ hN σ ι hdom

end Game

end Tsirelson

end MIPRE
