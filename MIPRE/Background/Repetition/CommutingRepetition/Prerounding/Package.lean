/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Package.lean
-/
/-
# Pre-rounding assembly: labels, candidate vectors, and answer POVMs (node 1.2.11)

The label structure of prop tracial-prerounding in the concretized form of
D8: histories are the flattened posterior tuples, the Alice label of
`(h, x)` is the canonical label at `{i} ∪ C_X` with the live question
inserted, the Bob label mirrors, and the "bar" labels are the canonical labels
at `C_X` resp. `C_Y`. Candidate vectors are the normalized arena branches
(eq normalized-candidates), with a fixed unit vector off the posterior
support ("Zero branches"); the answer POVMs are the arena's fully refined
POVMs coarse-grained at the live coordinate (eq live-refinements). The
positivity order of eq candidate-positivity-order shows the bar branches do
not vanish on positive posterior edges. Nothing here is a manuscript
statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Family
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryCore

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-! ### A fixed unit vector and normalization with fallback -/

namespace StdTracialAlgebra

variable (N : StdTracialAlgebra.{0})

theorem norm_ι_one : ‖N.ι 1‖ = 1 := by
  have h : ⟪N.ι 1, N.ι 1⟫_ℂ = 1 := by
    rw [N.ι_inner, star_one, one_mul, N.τ_one]
  have h4 := inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι 1)
  rw [h] at h4
  have h3 : ‖N.ι 1‖ ^ 2 = 1 := by simpa using h4.symm
  nlinarith [norm_nonneg (N.ι 1)]

open Classical in
/-- Normalize a vector, falling back to the fixed unit vector `ι 1` at zero. -/
noncomputable def unitOr (v : N.H) : N.H :=
  if v = 0 then N.ι 1 else ((‖v‖⁻¹ : ℝ) : ℂ) • v

theorem unitOr_norm (v : N.H) : ‖N.unitOr v‖ = 1 := by
  unfold unitOr
  split_ifs with hv
  · exact N.norm_ι_one
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem unitOr_of_ne (v : N.H) (hv : v ≠ 0) : N.unitOr v = ((‖v‖⁻¹ : ℝ) : ℂ) • v := by
  unfold unitOr
  rw [if_neg hv]

end StdTracialAlgebra

namespace ResolverArena

variable {M : StdTracialAlgebra.{0}}
variable {I J Af Bf : Type} [Fintype I] [Fintype J] [Fintype Af] [Fintype Bf]
variable {F : I → Af → M.A} {G : J → Bf → M.A}

theorem unitOr_branch (R : ResolverArena M F G) (σ : M.A) (i : I) (j : J)
    (hb : R.branch σ i j ≠ 0) :
    R.N.unitOr (R.branch σ i j) = R.candidate σ i j :=
  R.N.unitOr_of_ne _ hb

end ResolverArena

namespace RevealDatum

variable {D : Finset (Fin n)}

theorem mem_CY_of_ne (r : RevealDatum n D) {j : Fin n} (hj : j ≠ r.i)
    (hCX : j ∉ r.CX) : j ∈ r.CY := by
  have hmem : j ∈ r.CX ∪ r.CY := by
    rw [r.union_eq_compl_singleton]
    simpa using hj
  exact (Finset.mem_union.mp hmem).resolve_left hCX

theorem mem_CX_of_ne (r : RevealDatum n D) {j : Fin n} (hj : j ≠ r.i)
    (hCY : j ∉ r.CY) : j ∈ r.CX := by
  have hmem : j ∈ r.CX ∪ r.CY := by
    rw [r.union_eq_compl_singleton]
    simpa using hj
  exact (Finset.mem_union.mp hmem).resolve_right hCY

end RevealDatum

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}

/-! ### The labels of a history -/

/-- The Alice label `s = (i, r, x)`: canonical at `{i} ∪ C_X` with the live
question inserted. -/
noncomputable def labelA (D : Finset (Fin n)) (h : PostTuple n X Y A B D) (x : X) :
    ALabel n X Y A :=
  aLabel D (insert h.1.i h.1.CX) (Function.update h.2.1 h.1.i x) h.2.2.1 h.2.2.2.1

/-- The Bob label `t = (i, r, y)`. -/
noncomputable def labelB (D : Finset (Fin n)) (h : PostTuple n X Y A B D) (y : Y) :
    BLabel n X Y B :=
  bLabel D (insert h.1.i h.1.CY) h.2.1 (Function.update h.2.2.1 h.1.i y) h.2.2.2.2

/-- The bar Alice label (eq bar-HK, `H̄_{r,y}`): canonical at `C_X`, the live
Bob question inserted on the weight side. -/
noncomputable def barLabelA (D : Finset (Fin n)) (h : PostTuple n X Y A B D) (y : Y) :
    ALabel n X Y A :=
  aLabel D h.1.CX h.2.1 (Function.update h.2.2.1 h.1.i y) h.2.2.2.1

/-- The bar Bob label (`K̄_{r,x}`). -/
noncomputable def barLabelB (D : Finset (Fin n)) (h : PostTuple n X Y A B D) (x : X) :
    BLabel n X Y B :=
  bLabel D h.1.CY (Function.update h.2.1 h.1.i x) h.2.2.1 h.2.2.2.2

/-- The label of the flattened tuple is the posterior's canonical label. -/
theorem labelA_histCore (t : PostTuple n X Y A B D) :
    labelA D (histCore t) (t.2.1 t.1.i)
      = aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1 := by
  obtain ⟨r, xw, yw, zD⟩ := t
  unfold labelA histCore
  dsimp only
  refine aLabel_congr D _ zD.1 (fun j hj => ?_) (fun j hj => ?_)
  · rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [Function.update_self]
    · have hne : j ≠ r.i := fun h => r.i_notMem_CX (h ▸ hj)
      rw [Function.update_of_ne hne]
      simp [keepOn, hj]
  · have hne : j ≠ r.i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
    have hCX : j ∉ r.CX := fun h => hj (Finset.mem_insert_of_mem h)
    have hCY := r.mem_CY_of_ne hne hCX
    simp [keepOn, hCY]

theorem labelB_histCore (t : PostTuple n X Y A B D) :
    labelB D (histCore t) (t.2.2.1 t.1.i)
      = bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2 := by
  obtain ⟨r, xw, yw, zD⟩ := t
  unfold labelB histCore
  dsimp only
  refine bLabel_congr D _ zD.2 (fun j hj => ?_) (fun j hj => ?_)
  · have hne : j ≠ r.i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
    have hCY : j ∉ r.CY := fun h => hj (Finset.mem_insert_of_mem h)
    have hCX := r.mem_CX_of_ne hne hCY
    simp [keepOn, hCX]
  · rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [Function.update_self]
    · have hne : j ≠ r.i := fun h => r.i_notMem_CY (h ▸ hj)
      rw [Function.update_of_ne hne]
      simp [keepOn, hj]

theorem barLabelA_histCore (t : PostTuple n X Y A B D) :
    barLabelA D (histCore t) (t.2.2.1 t.1.i)
      = aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1 := by
  obtain ⟨r, xw, yw, zD⟩ := t
  unfold barLabelA histCore
  dsimp only
  refine aLabel_congr D _ zD.1 (fun j hj => ?_) (fun j hj => ?_)
  · simp [keepOn, hj]
  · by_cases hji : j = r.i
    · subst hji
      rw [Function.update_self]
    · rw [Function.update_of_ne hji]
      have hCY := r.mem_CY_of_ne hji hj
      simp [keepOn, hCY]

theorem barLabelB_histCore (t : PostTuple n X Y A B D) :
    barLabelB D (histCore t) (t.2.1 t.1.i)
      = bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2 := by
  obtain ⟨r, xw, yw, zD⟩ := t
  unfold barLabelB histCore
  dsimp only
  refine bLabel_congr D _ zD.2 (fun j hj => ?_) (fun j hj => ?_)
  · by_cases hji : j = r.i
    · subst hji
      rw [Function.update_self]
    · rw [Function.update_of_ne hji]
      have hCX := r.mem_CX_of_ne hji hj
      simp [keepOn, hCX]
  · simp [keepOn, hj]

/-! ### The package data over an arena -/

variable (μ : X → Y → ℝ)
variable (R : ResolverArena S.M (S.refinedA D μ) (S.refinedB D μ))

/-- `u_{st}`: the normalized ideal branch, fixed unit vector off the support. -/
noncomputable def uVec (s : PostTuple n X Y A B D × X) (t : PostTuple n X Y A B D × Y) :
    R.N.H :=
  R.N.unitOr (R.branch S.σ (labelA D s.1 s.2) (labelB D t.1 t.2))

/-- `x_s`: the normalized Alice-side branch (`φ^A_{r,x}`, Bob at the bar). -/
noncomputable def xVec (s : PostTuple n X Y A B D × X) : R.N.H :=
  R.N.unitOr (R.branch S.σ (labelA D s.1 s.2) (barLabelB D s.1 s.2))

/-- `y_t`: the normalized Bob-side branch (`φ^B_{r,y}`, Alice at the bar). -/
noncomputable def yVec (t : PostTuple n X Y A B D × Y) : R.N.H :=
  R.N.unitOr (R.branch S.σ (barLabelA D t.1 t.2) (labelB D t.1 t.2))

/-- Alice's answer POVM: the fully refined arena POVM coarse-grained at the
live coordinate (eq live-refinements). -/
noncomputable def Apov (s : PostTuple n X Y A B D × X) (a : A) : R.N.A :=
  ∑ as : Fin n → A, if as s.1.1.i = a then R.Ameas (labelA D s.1 s.2) as else 0

noncomputable def Bpov (t : PostTuple n X Y A B D × Y) (b : B) : R.N.A :=
  ∑ bs : Fin n → B, if bs t.1.1.i = b then R.Bmeas (labelB D t.1 t.2) bs else 0

theorem Apov_pos (s : PostTuple n X Y A B D × X) (a : A) : IsPosElem (S.Apov μ R s a) :=
  isPosElem_sum _ _ fun as _ => by
    split_ifs
    · exact R.Ameas_pos _ _
    · exact isPosElem_zero

theorem Bpov_pos (t : PostTuple n X Y A B D × Y) (b : B) : IsPosElem (S.Bpov μ R t b) :=
  isPosElem_sum _ _ fun bs _ => by
    split_ifs
    · exact R.Bmeas_pos _ _
    · exact isPosElem_zero

theorem Apov_sum (s : PostTuple n X Y A B D × X) : (∑ a : A, S.Apov μ R s a) = 1 := by
  unfold Apov
  rw [Finset.sum_comm]
  rw [← R.Ameas_sum (labelA D s.1 s.2)]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem Bpov_sum (t : PostTuple n X Y A B D × Y) : (∑ b : B, S.Bpov μ R t b) = 1 := by
  unfold Bpov
  rw [Finset.sum_comm]
  rw [← R.Bmeas_sum (labelB D t.1 t.2)]
  refine Finset.sum_congr rfl fun bs _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- **The ideal answer law** (eq ideal-answer-law, coarse-grained form): on a
nonzero branch, the candidate's answer pairing is the refined pairing mass at
the live answers divided by the branch mass. -/
theorem candidate_pairing (s : ALabel n X Y A) (t : BLabel n X Y B) (i : Fin n) (a : A) (b : B)
    (hb : R.branch S.σ s t ≠ 0) :
    (⟪R.candidate S.σ s t,
        R.N.L (∑ as : Fin n → A, if as i = a then R.Ameas s as else 0)
          (R.N.Rop (∑ bs : Fin n → B, if bs i = b then R.Bmeas t bs else 0)
            (R.candidate S.σ s t))⟫_ℂ).re
      = (∑ as : Fin n → A, ∑ bs : Fin n → B,
          if as i = a ∧ bs i = b then
            (S.M.τ (star S.σ * (S.refinedA D μ s as * S.σ * S.refinedB D μ t bs))).re
          else 0) / ‖R.branch S.σ s t‖ ^ 2 := by
  have hnorm : (S.M.τ (star S.σ * ((∑ as : Fin n → A, S.refinedA D μ s as) * S.σ *
      (∑ bs : Fin n → B, S.refinedB D μ t bs))))
      = ((‖R.branch S.σ s t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← R.branch_norm S.σ s t, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpos : (0 : ℝ) < ‖R.branch S.σ s t‖ ^ 2 := by
    have := norm_pos_iff.mpr hb
    positivity
  -- Expand the coarse-grained pairing by linearity.
  have hexp : ⟪R.candidate S.σ s t,
      R.N.L (∑ as : Fin n → A, if as i = a then R.Ameas s as else 0)
        (R.N.Rop (∑ bs : Fin n → B, if bs i = b then R.Bmeas t bs else 0)
          (R.candidate S.σ s t))⟫_ℂ
      = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          if as i = a ∧ bs i = b then
            ⟪R.candidate S.σ s t,
              R.N.L (R.Ameas s as) (R.N.Rop (R.Bmeas t bs) (R.candidate S.σ s t))⟫_ℂ
          else 0 := by
    simp only [StdTracialAlgebra.Rop, Finset.op_sum, map_sum, ContinuousLinearMap.sum_apply,
      inner_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl fun bs _ => ?_
    by_cases has : as i = a <;> by_cases hbs : bs i = b <;> simp [has, hbs]
  rw [hexp, Complex.re_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [Complex.re_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun bs _ => ?_
  split_ifs
  · rw [R.candidate_answer S.σ s t as bs hb, hnorm, Complex.div_ofReal_re]
  · simp

end TracialStrategy

end CommutingRepetition
