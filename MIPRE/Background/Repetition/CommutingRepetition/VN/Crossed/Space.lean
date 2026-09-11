/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Crossed/Space.lean
-/
/-
# The Hilbert space `ℓ²(ℚ, K)` of the discrete crossed product (density stage E5.2, part 1)

The crossed product of a von Neumann algebra by the modular group restricted to the
countable discrete group `G = ℚ ⊆ ℝ` acts on `ℓ²(ℚ, K)`. This file provides the
bookkeeping: coordinate embeddings `sgl g`, evaluations `ev g`, uniformly bounded
*diagonal* operators `diag x` (`(diag x f)(s) = x s (f s)`), their constant case
`amp y = 1 ⊗ y`, and the unitary shifts `shift g` (`(shift g f)(h) = f(h − g)`), with the
algebra relating them (`shift_diag`, `shift_sgl`, ...). The vector `sgl 0 Ω` and the
covariant representation are in `VN/Crossed/Product.lean`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Crossed

open scoped InnerProductSpace ENNReal
open Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `ℓ²(ℚ, K)`. -/
abbrev L2Q (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] : Type _ :=
  lp (fun _ : ℚ => K) 2

/-- Shortcut instance: the self-adjoint continuous functional calculus on `B(ℓ²(ℚ, K))`
(instance search otherwise gives up on this type). -/
noncomputable instance instCFC_L2Q :
    ContinuousFunctionalCalculus ℝ (L2Q K →L[ℂ] L2Q K) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-! ## ℓ² bookkeeping -/

theorem two_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num

theorem summable_norm_sq (f : L2Q K) : Summable fun s => ‖f s‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp f)
  simpa only [two_toReal, Real.rpow_two] using this

theorem norm_sq_eq_tsum (f : L2Q K) : ‖f‖ ^ 2 = ∑' s, ‖f s‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simpa only [two_toReal, Real.rpow_two] using this

theorem memℓp_of_summable_sq {g : ℚ → K} (hg : Summable fun s => ‖g s‖ ^ 2) :
    Memℓp g (2 : ℝ≥0∞) := by
  refine memℓp_gen ?_
  simpa only [two_toReal, Real.rpow_two] using hg

/-- The element of `ℓ²(ℚ, K)` with coordinates `g`. -/
noncomputable def mkVec (g : ℚ → K) (hg : Summable fun s => ‖g s‖ ^ 2) : L2Q K :=
  ⟨g, memℓp_of_summable_sq hg⟩

theorem mkVec_apply (g : ℚ → K) (hg : Summable fun s => ‖g s‖ ^ 2) (s : ℚ) : mkVec g hg s = g s :=
  rfl

theorem norm_le_of_tsum_sq_le {f : L2Q K} {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' s, ‖f s‖ ^ 2 ≤ C ^ 2) : ‖f‖ ≤ C := by
  refine lp.norm_le_of_tsum_le (p := 2) (by norm_num) hC ?_
  simpa only [two_toReal, Real.rpow_two] using h

theorem norm_apply_le (f : L2Q K) (s : ℚ) : ‖f s‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm (by norm_num) f s

/-! ## Coordinate embeddings and evaluations -/

/-- The `g`-th coordinate embedding `K → ℓ²(ℚ, K)`. -/
noncomputable def sgl (g : ℚ) : K →L[ℂ] L2Q K := lp.singleContinuousLinearMap ℂ (fun _ : ℚ => K) 2 g

/-- The `g`-th coordinate evaluation `ℓ²(ℚ, K) → K`. -/
noncomputable def ev (g : ℚ) : L2Q K →L[ℂ] K := lp.evalCLM ℂ (fun _ : ℚ => K) 2 g

theorem ev_apply (g : ℚ) (f : L2Q K) : ev g f = f g := rfl

theorem sgl_apply_self (g : ℚ) (v : K) : sgl g v g = v :=
  lp.single_apply_self (E := fun _ : ℚ => K) 2 g v

theorem sgl_apply_ne (g : ℚ) (v : K) {s : ℚ} (h : s ≠ g) : sgl g v s = 0 :=
  lp.single_apply_ne (E := fun _ : ℚ => K) 2 g v h

theorem sgl_apply (g : ℚ) (v : K) (s : ℚ) : sgl g v s = if s = g then v else 0 := by
  split_ifs with h
  · rw [h]; exact sgl_apply_self g v
  · exact sgl_apply_ne g v h

theorem ev_sgl_self (g : ℚ) (v : K) : ev g (sgl g v) = v := sgl_apply_self g v

theorem ev_sgl_ne {s g : ℚ} (h : s ≠ g) (v : K) : ev s (sgl g v) = 0 := sgl_apply_ne g v h

theorem norm_sgl (g : ℚ) (v : K) : ‖sgl g v‖ = ‖v‖ := by
  refine le_antisymm (norm_le_of_tsum_sq_le (norm_nonneg _) ?_) ?_
  · have : (fun s => ‖sgl g v s‖ ^ 2) = fun s => if s = g then ‖v‖ ^ 2 else 0 := by
      funext s; rw [sgl_apply]; split_ifs <;> simp
    rw [this, tsum_ite_eq]
  · calc ‖v‖ = ‖sgl g v g‖ := by rw [sgl_apply_self]
      _ ≤ ‖sgl g v‖ := norm_apply_le _ _

theorem inner_sgl_sgl (g h : ℚ) (v w : K) :
    ⟪sgl g v, sgl h w⟫_ℂ = if g = h then ⟪v, w⟫_ℂ else 0 := by
  rw [lp.inner_eq_tsum]
  have : (fun s => ⟪sgl g v s, sgl h w s⟫_ℂ) = fun s => if s = g then ⟪v, sgl h w g⟫_ℂ else 0 := by
    funext s
    rw [sgl_apply g v s]
    split_ifs with hs
    · subst hs; rfl
    · rw [inner_zero_left]
  rw [this, tsum_ite_eq, sgl_apply h w g]
  split_ifs <;> simp

theorem hasSum_sgl (f : L2Q K) : HasSum (fun s => sgl s (f s)) f :=
  lp.hasSum_single (p := 2) ENNReal.ofNat_ne_top f

/-- A closed submodule containing all `sgl s v` is everything. -/
theorem eq_top_of_sgl_mem {V : Submodule ℂ (L2Q K)} (hV : IsClosed (V : Set (L2Q K)))
    (h : ∀ s (v : K), sgl s v ∈ V) : V = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hs := hasSum_sgl f
  refine hV.mem_of_tendsto hs (Eventually.of_forall fun F => ?_)
  exact Submodule.sum_mem _ fun s _ => h s (f s)

/-- The matrix unit `e_g e_h*`. -/
noncomputable def unit (g h : ℚ) : L2Q K →L[ℂ] L2Q K := sgl g ∘L ev h

theorem unit_apply (g h : ℚ) (f : L2Q K) : unit g h f = sgl g (f h) := rfl

/-! ## Diagonal operators -/

/-- A uniformly bounded family of operators. -/
def IsBddFam (x : ℚ → K →L[ℂ] K) : Prop := ∃ C, ∀ s, ‖x s‖ ≤ C

theorem IsBddFam.const (y : K →L[ℂ] K) : IsBddFam fun _ : ℚ => y := ⟨‖y‖, fun _ => le_rfl⟩

theorem IsBddFam.mul {x y : ℚ → K →L[ℂ] K} (hx : IsBddFam x) (hy : IsBddFam y) :
    IsBddFam fun s => x s * y s := by
  obtain ⟨C, hC⟩ := hx
  obtain ⟨D, hD⟩ := hy
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  exact ⟨C * D, fun s => (norm_mul_le _ _).trans (mul_le_mul (hC s) (hD s) (norm_nonneg _) hC0)⟩

theorem IsBddFam.add {x y : ℚ → K →L[ℂ] K} (hx : IsBddFam x) (hy : IsBddFam y) :
    IsBddFam fun s => x s + y s := by
  obtain ⟨C, hC⟩ := hx
  obtain ⟨D, hD⟩ := hy
  exact ⟨C + D, fun s => (norm_add_le _ _).trans (add_le_add (hC s) (hD s))⟩

theorem IsBddFam.smul (c : ℂ) {x : ℚ → K →L[ℂ] K} (hx : IsBddFam x) :
    IsBddFam fun s => c • x s := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨‖c‖ * C, fun s => by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)⟩

theorem IsBddFam.star {x : ℚ → K →L[ℂ] K} (hx : IsBddFam x) : IsBddFam fun s => star (x s) := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨C, fun s => by rw [norm_star]; exact hC s⟩

theorem IsBddFam.comp {x : ℚ → K →L[ℂ] K} (hx : IsBddFam x) (φ : ℚ → ℚ) :
    IsBddFam fun s => x (φ s) := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨C, fun s => hC _⟩

theorem IsBddFam.of_le {x : ℚ → K →L[ℂ] K} {C : ℝ} (h : ∀ s, ‖x s‖ ≤ C) : IsBddFam x := ⟨C, h⟩

variable (x : ℚ → K →L[ℂ] K)

theorem summable_norm_sq_diag {C : ℝ} (hx : ∀ s, ‖x s‖ ≤ C) (f : L2Q K) :
    Summable fun s => ‖x s (f s)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun s => by positivity) (fun s => ?_)
    ((summable_norm_sq f).mul_left (C ^ 2))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (((x s).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hx s) (norm_nonneg _))) 2

/-- The diagonal operator of a uniformly bounded family, as a linear map. -/
noncomputable def diagPre {C : ℝ} (hx : ∀ s, ‖x s‖ ≤ C) : L2Q K →ₗ[ℂ] L2Q K where
  toFun f := mkVec (fun s => x s (f s)) (summable_norm_sq_diag x hx f)
  map_add' f g := by
    apply lp.ext
    funext s
    simp only [mkVec_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply lp.ext
    funext s
    simp only [mkVec_apply, lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

theorem diagPre_apply {C : ℝ} (hx : ∀ s, ‖x s‖ ≤ C) (f : L2Q K) (s : ℚ) :
    diagPre x hx f s = x s (f s) := rfl

theorem norm_diagPre_le {C : ℝ} (hx : ∀ s, ‖x s‖ ≤ C) (f : L2Q K) :
    ‖diagPre x hx f‖ ≤ max C 0 * ‖f‖ := by
  refine norm_le_of_tsum_sq_le (by positivity) ?_
  simp only [diagPre_apply]
  calc ∑' s, ‖x s (f s)‖ ^ 2 ≤ ∑' s, (max C 0) ^ 2 * ‖f s‖ ^ 2 := by
        refine (summable_norm_sq_diag x hx f).tsum_le_tsum (fun s => ?_)
          ((summable_norm_sq f).mul_left _)
        rw [← mul_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) (((x s).le_opNorm _).trans ?_) 2
        exact mul_le_mul_of_nonneg_right ((hx s).trans (le_max_left _ _)) (norm_nonneg _)
    _ = (max C 0) ^ 2 * ∑' s, ‖f s‖ ^ 2 := tsum_mul_left
    _ = (max C 0 * ‖f‖) ^ 2 := by rw [← norm_sq_eq_tsum, mul_pow]

/-- **The diagonal operator** `⊕_s x s` of a uniformly bounded family (junk `0` otherwise). -/
noncomputable def diag : L2Q K →L[ℂ] L2Q K := by
  classical
  exact if hx : IsBddFam x then
    (diagPre x hx.choose_spec).mkContinuous (max hx.choose 0) (norm_diagPre_le x hx.choose_spec)
  else 0

theorem diag_apply (hx : IsBddFam x) (f : L2Q K) (s : ℚ) : diag x f s = x s (f s) := by
  unfold diag
  rw [dif_pos hx]
  rfl

theorem diag_ext (hx : IsBddFam x) {T : L2Q K →L[ℂ] L2Q K} (h : ∀ f s, T f s = x s (f s)) :
    T = diag x := by
  ext f s
  rw [h, diag_apply x hx]

theorem norm_diag_le {C : ℝ} (hC : 0 ≤ C) (hx : ∀ s, ‖x s‖ ≤ C) : ‖diag x‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun f => ?_
  have h : diag x f = diagPre x hx f := by
    apply lp.ext; funext s; rw [diag_apply x ⟨C, hx⟩, diagPre_apply]
  rw [h]
  refine (norm_diagPre_le x hx f).trans ?_
  rw [max_eq_left hC]

theorem ev_diag (hx : IsBddFam x) (s : ℚ) (f : L2Q K) : ev s (diag x f) = x s (ev s f) :=
  diag_apply x hx f s

theorem diag_sgl (hx : IsBddFam x) (g : ℚ) (v : K) : diag x (sgl g v) = sgl g (x g v) := by
  apply lp.ext
  funext s
  by_cases h : s = g
  · subst h
    rw [diag_apply x hx, sgl_apply_self, sgl_apply_self]
  · rw [diag_apply x hx, sgl_apply_ne g v h, sgl_apply_ne g (x g v) h, map_zero]

variable {x}

theorem diag_add {y : ℚ → K →L[ℂ] K} (hx : IsBddFam x) (hy : IsBddFam y) :
    diag (fun s => x s + y s) = diag x + diag y := by
  ext f s
  simp only [diag_apply _ (hx.add hy), _root_.add_apply, lp.coeFn_add, Pi.add_apply,
    diag_apply x hx, diag_apply y hy]

theorem diag_smul (c : ℂ) (hx : IsBddFam x) : diag (fun s => c • x s) = c • diag x := by
  ext f s
  simp only [diag_apply _ (hx.smul c), _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    diag_apply x hx]

theorem diag_mul {y : ℚ → K →L[ℂ] K} (hx : IsBddFam x) (hy : IsBddFam y) :
    diag (fun s => x s * y s) = diag x * diag y := by
  ext f s
  simp only [diag_apply _ (hx.mul hy), mul_apply_eq_comp, diag_apply x hx, diag_apply y hy]

theorem diag_one : diag (fun _ : ℚ => (1 : K →L[ℂ] K)) = 1 := by
  ext f s
  simp only [diag_apply _ (IsBddFam.const 1), one_apply_eq_self]

theorem diag_zero : diag (fun _ : ℚ => (0 : K →L[ℂ] K)) = 0 := by
  ext f s
  simp only [diag_apply _ (IsBddFam.const 0), _root_.zero_apply, lp.coeFn_zero, Pi.zero_apply]

theorem inner_diag_right (hx : IsBddFam x) (f g : L2Q K) :
    ⟪f, diag x g⟫_ℂ = ∑' s, ⟪f s, x s (g s)⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  congr 1
  funext s
  rw [diag_apply x hx]

theorem diag_star (hx : IsBddFam x) : diag (fun s => star (x s)) = star (diag x) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [lp.inner_eq_tsum, inner_diag_right hx]
  congr 1
  funext s
  rw [diag_apply _ hx.star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem diag_isSelfAdjoint (hx : IsBddFam x) (h : ∀ s, IsSelfAdjoint (x s)) :
    IsSelfAdjoint (diag x) := by
  show star (diag x) = diag x
  rw [← diag_star hx]
  congr 1
  funext s
  exact (h s).star_eq

/-- `1 ⊗ y`. -/
noncomputable def amp (y : K →L[ℂ] K) : L2Q K →L[ℂ] L2Q K := diag fun _ : ℚ => y

theorem amp_apply (y : K →L[ℂ] K) (f : L2Q K) (s : ℚ) : amp y f s = y (f s) :=
  diag_apply _ (IsBddFam.const y) f s

theorem amp_one : amp (1 : K →L[ℂ] K) = 1 := diag_one

theorem amp_mul (y z : K →L[ℂ] K) : amp (y * z) = amp y * amp z :=
  diag_mul (IsBddFam.const y) (IsBddFam.const z)

theorem amp_star (y : K →L[ℂ] K) : amp (star y) = star (amp y) := diag_star (IsBddFam.const y)

theorem amp_add (y z : K →L[ℂ] K) : amp (y + z) = amp y + amp z :=
  diag_add (IsBddFam.const y) (IsBddFam.const z)

theorem amp_smul (c : ℂ) (y : K →L[ℂ] K) : amp (c • y) = c • amp y :=
  diag_smul c (IsBddFam.const y)

theorem amp_sgl (y : K →L[ℂ] K) (g : ℚ) (v : K) : amp y (sgl g v) = sgl g (y v) :=
  diag_sgl _ (IsBddFam.const y) g v

theorem norm_amp_le (y : K →L[ℂ] K) : ‖amp y‖ ≤ ‖y‖ :=
  norm_diag_le _ (norm_nonneg _) fun _ => le_rfl

theorem amp_diag_comm (hx : IsBddFam x) {y : K →L[ℂ] K} (h : ∀ s, Commute (x s) y) :
    Commute (diag x) (amp y) := by
  unfold amp
  rw [Commute, SemiconjBy, ← diag_mul hx (IsBddFam.const y), ← diag_mul (IsBddFam.const y) hx]
  congr 1
  funext s
  exact (h s).eq

/-! ## Shifts -/

theorem summable_norm_sq_shift (g : ℚ) (f : L2Q K) : Summable fun s => ‖f (s - g)‖ ^ 2 := by
  exact (Equiv.subRight g).summable_iff.mpr (summable_norm_sq f)

/-- The shift `(shift g f)(h) = f(h − g)` as a linear map. -/
noncomputable def shiftPre (g : ℚ) : L2Q K →ₗ[ℂ] L2Q K where
  toFun f := mkVec (fun s => f (s - g)) (summable_norm_sq_shift g f)
  map_add' f h := by
    apply lp.ext
    funext s
    simp only [mkVec_apply, lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    apply lp.ext
    funext s
    simp only [mkVec_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

theorem shiftPre_apply (g : ℚ) (f : L2Q K) (s : ℚ) : shiftPre g f s = f (s - g) := rfl

theorem norm_shiftPre (g : ℚ) (f : L2Q K) : ‖shiftPre g f‖ = ‖f‖ := by
  have h : ‖shiftPre g f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    simp only [shiftPre_apply]
    exact (Equiv.subRight g).tsum_eq fun s => ‖f s‖ ^ 2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The unitary shift** `λ(g)`: `(λ(g) f)(h) = f(h − g)`. -/
noncomputable def shift (g : ℚ) : L2Q K →L[ℂ] L2Q K :=
  (shiftPre g).mkContinuous 1 fun f => by rw [norm_shiftPre, one_mul]

theorem shift_apply (g : ℚ) (f : L2Q K) (s : ℚ) : shift g f s = f (s - g) := rfl

theorem norm_shift_apply (g : ℚ) (f : L2Q K) : ‖shift g f‖ = ‖f‖ := norm_shiftPre g f

theorem shift_zero : shift (0 : ℚ) = (1 : L2Q K →L[ℂ] L2Q K) := by
  ext f s
  simp only [shift_apply, sub_zero, one_apply_eq_self]

theorem shift_add (g h : ℚ) : shift (g + h) = (shift g : L2Q K →L[ℂ] L2Q K) * shift h := by
  ext f s
  simp only [shift_apply, mul_apply_eq_comp]
  rw [show s - (g + h) = s - g - h by ring]

theorem shift_neg_mul (g : ℚ) : shift (-g) * (shift g : L2Q K →L[ℂ] L2Q K) = 1 := by
  rw [← shift_add, neg_add_cancel, shift_zero]

theorem shift_mul_neg (g : ℚ) : shift g * (shift (-g) : L2Q K →L[ℂ] L2Q K) = 1 := by
  rw [← shift_add, add_neg_cancel, shift_zero]

theorem shift_comm (g h : ℚ) : shift g * (shift h : L2Q K →L[ℂ] L2Q K) = shift h * shift g := by
  rw [← shift_add, ← shift_add, add_comm]

theorem inner_shift (g : ℚ) (f k : L2Q K) : ⟪shift g f, shift g k⟫_ℂ = ⟪f, k⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [shift_apply]
  exact (Equiv.subRight g).tsum_eq fun s => ⟪f s, k s⟫_ℂ

theorem shift_star (g : ℚ) : star (shift g : L2Q K →L[ℂ] L2Q K) = shift (-g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f k
  have := inner_shift g (shift (-g) f) k
  rw [← mul_apply_eq_comp, shift_mul_neg, one_apply_eq_self] at this
  exact this.symm

theorem shift_sgl (g s : ℚ) (v : K) : shift g (sgl s v) = sgl (s + g) v := by
  apply lp.ext
  funext h
  rw [shift_apply, sgl_apply, sgl_apply]
  by_cases hh : h = s + g
  · rw [if_pos hh, if_pos (by rw [hh]; ring)]
  · rw [if_neg hh, if_neg fun h' => hh (by linarith)]

/-- Covariance of shifts and diagonal operators: `λ(g) ⊕ x_s = (⊕ x_{s−g}) λ(g)`. -/
theorem shift_diag (g : ℚ) (hx : IsBddFam x) :
    shift g * diag x = diag (fun s => x (s - g)) * shift g := by
  ext f s
  simp only [mul_apply_eq_comp, shift_apply, diag_apply x hx, diag_apply _ (hx.comp _)]

theorem shift_amp (g : ℚ) (y : K →L[ℂ] K) : shift g * amp y = amp y * shift g := by
  unfold amp
  exact shift_diag g (IsBddFam.const y)

theorem shift_mul_diag_mul_shift_neg (g : ℚ) (hx : IsBddFam x) :
    shift g * diag x * shift (-g) = diag fun s => x (s - g) := by
  rw [shift_diag g hx, mul_assoc, shift_mul_neg, mul_one]

end Crossed

end VN

end CommutingRepetition
