/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Family.lean
-/
/-
# Pre-rounding assembly: the fully refined effect family (node 1.2.11)

The generalized label family of `Prerounding/Costs.lean` is indexed by
`ALabel`/`BLabel` (revealed set, reference words, answer word) and refined,
per the manuscript's "The common finite resolver corner", by the live
answers. Since a label does not carry the live coordinate, the refinement
supplied to the resolver arena is the finest one — by the FULL answer word
(`Af := Fin n → A`) — and the live refinement `H^a_{r,x}` of eq
live-refinements is recovered at assembly by coarse-graining at the live
coordinate of the history. The refined effects are positive, sum to the
revealed-set effects (`htotF`/`htotG`), and the totals are contractions, so
`resolver_arena_entropic` applies. Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Costs
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.EntropyBudget

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-- `1` is algebraically positive. -/
theorem isPosElem_one {M : StdTracialAlgebra.{0}} : IsPosElem (1 : M.A) := by
  have := isPosElem_star_mul_self (1 : M.A)
  simpa using this

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))

/-- The fully refined Alice effect at a label: the revealed-set average of
the repeated effect at one full answer word (agreeing with the label's
core word). -/
noncomputable def refinedA (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (s : ALabel n X Y A) (as : Fin n → A) : S.M.A :=
  weightedAvg (setWeightX s.1 μ s.2.1 s.2.2.1) fun w =>
    if agreesOn D as s.2.2.2 then S.E w as else 0

/-- The fully refined Bob effect at a label. -/
noncomputable def refinedB (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (t : BLabel n X Y B) (bs : Fin n → B) : S.M.A :=
  weightedAvg (setWeightY t.1 μ t.2.1 t.2.2.1) fun v =>
    if agreesOn D bs t.2.2.2 then S.F v bs else 0

/-- The refined effects sum to the revealed-set effect (`htotF`). -/
theorem sum_refinedA (D : Finset (Fin n)) (μ : X → Y → ℝ) (s : ALabel n X Y A) :
    (∑ as : Fin n → A, S.refinedA D μ s as) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2 := by
  unfold refinedA setEffectA weightedAvg coreEffectA
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.smul_sum]

theorem sum_refinedB (D : Finset (Fin n)) (μ : X → Y → ℝ) (t : BLabel n X Y B) :
    (∑ bs : Fin n → B, S.refinedB D μ t bs) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2 := by
  unfold refinedB setEffectB weightedAvg coreEffectB
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.smul_sum]

theorem refinedA_isPosElem (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (s : ALabel n X Y A) (as : Fin n → A) : IsPosElem (S.refinedA D μ s as) := by
  unfold refinedA weightedAvg
  rw [show ((((∑ w : Fin n → X, setWeightX s.1 μ s.2.1 s.2.2.1 w : ℝ)) : ℂ))⁻¹
      = ((((∑ w : Fin n → X, setWeightX s.1 μ s.2.1 s.2.2.1 w)⁻¹ : ℝ)) : ℂ) from
    (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun w _ => setWeightX_nonneg s.1 μ hμ _ _ w))
  refine isPosElem_sum _ _ fun w _ => ?_
  refine IsPosElem.smul_ofReal ?_ (setWeightX_nonneg s.1 μ hμ _ _ w)
  split_ifs
  · exact S.E_pos _ _
  · exact isPosElem_zero

theorem refinedB_isPosElem (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (t : BLabel n X Y B) (bs : Fin n → B) : IsPosElem (S.refinedB D μ t bs) := by
  unfold refinedB weightedAvg
  rw [show ((((∑ v : Fin n → Y, setWeightY t.1 μ t.2.1 t.2.2.1 v : ℝ)) : ℂ))⁻¹
      = ((((∑ v : Fin n → Y, setWeightY t.1 μ t.2.1 t.2.2.1 v)⁻¹ : ℝ)) : ℂ) from
    (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun v _ => setWeightY_nonneg t.1 μ hμ _ _ v))
  refine isPosElem_sum _ _ fun v _ => ?_
  refine IsPosElem.smul_ofReal ?_ (setWeightY_nonneg t.1 μ hμ _ _ v)
  split_ifs
  · exact S.F_pos _ _
  · exact isPosElem_zero

/-- The complement of a core effect is positive (the remaining answer
words). -/
theorem one_sub_coreEffectA_isPosElem (D : Finset (Fin n)) (w : Fin n → X) (zA : Fin n → A) :
    IsPosElem (1 - S.coreEffectA D w zA) := by
  classical
  have h : (1 : S.M.A) - S.coreEffectA D w zA
      = ∑ as : Fin n → A, if agreesOn D as zA then 0 else S.E w as := by
    unfold coreEffectA
    rw [← S.E_sum w, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun as _ => ?_
    split_ifs <;> simp
  rw [h]
  refine isPosElem_sum _ _ fun as _ => ?_
  split_ifs
  · exact isPosElem_zero
  · exact S.E_pos _ _

theorem one_sub_coreEffectB_isPosElem (D : Finset (Fin n)) (v : Fin n → Y) (zB : Fin n → B) :
    IsPosElem (1 - S.coreEffectB D v zB) := by
  classical
  have h : (1 : S.M.A) - S.coreEffectB D v zB
      = ∑ bs : Fin n → B, if agreesOn D bs zB then 0 else S.F v bs := by
    unfold coreEffectB
    rw [← S.F_sum v, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun bs _ => ?_
    split_ifs <;> simp
  rw [h]
  refine isPosElem_sum _ _ fun bs _ => ?_
  split_ifs
  · exact isPosElem_zero
  · exact S.F_pos _ _

/-- A nonnegative weighted average of contractions is a contraction (the
`1 - ·` complement is positive); junk-safe at zero total weight. -/
theorem one_sub_weightedAvg_isPosElem {ι : Type} [Fintype ι] (wgt : ι → ℝ)
    (hwgt : ∀ i, 0 ≤ wgt i) (f : ι → S.M.A) (hf : ∀ i, IsPosElem (1 - f i)) :
    IsPosElem (1 - weightedAvg wgt f) := by
  classical
  by_cases hW : (∑ i, wgt i) = 0
  · unfold weightedAvg
    rw [hW]
    simp only [Complex.ofReal_zero, inv_zero, zero_smul, sub_zero]
    exact isPosElem_one
  · have h1 : (1 : S.M.A) = weightedAvg wgt fun _ => (1 : S.M.A) := by
      unfold weightedAvg
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, smul_smul,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hW), one_smul]
    have h2 : (1 : S.M.A) - weightedAvg wgt f = weightedAvg wgt fun i => 1 - f i := by
      conv_lhs => rw [h1]
      unfold weightedAvg
      rw [← smul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_sub]
    rw [h2]
    unfold weightedAvg
    rw [show ((((∑ i, wgt i : ℝ)) : ℂ))⁻¹ = ((((∑ i, wgt i)⁻¹ : ℝ)) : ℂ) from
      (Complex.ofReal_inv _).symm]
    refine IsPosElem.smul_ofReal ?_ (inv_nonneg.mpr (Finset.sum_nonneg fun i _ => hwgt i))
    exact isPosElem_sum _ _ fun i _ => (hf i).smul_ofReal (hwgt i)

theorem one_sub_setEffectA_isPosElem (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y) (zA : Fin n → A) :
    IsPosElem (1 - S.setEffectA D R₀ μ xref yref zA) :=
  S.one_sub_weightedAvg_isPosElem _ (setWeightX_nonneg R₀ μ hμ xref yref) _
    (fun w => S.one_sub_coreEffectA_isPosElem D w zA)

theorem one_sub_setEffectB_isPosElem (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y) (zB : Fin n → B) :
    IsPosElem (1 - S.setEffectB D R₀ μ xref yref zB) :=
  S.one_sub_weightedAvg_isPosElem _ (setWeightY_nonneg R₀ μ hμ xref yref) _
    (fun v => S.one_sub_coreEffectB_isPosElem D v zB)

/-- **The entropic arena over the fully refined family** (node 1.2.5 +
1.2.6 consumed at node 1.2.11). -/
theorem exists_refined_arena (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) :
    ∃ R : ResolverArena S.M (S.refinedA D μ) (S.refinedB D μ),
      R.ColEntropyBudget ∧ R.RowEntropyBudget :=
  resolver_arena_entropic S.M (S.refinedA D μ) (S.refinedB D μ)
    (fun s as => S.refinedA_isPosElem D μ hμ s as)
    (fun t bs => S.refinedB_isPosElem D μ hμ t bs)
    (fun s => by rw [S.sum_refinedA]; exact S.one_sub_setEffectA_isPosElem D _ μ hμ _ _ _)
    (fun t => by rw [S.sum_refinedB]; exact S.one_sub_setEffectB_isPosElem D _ μ hμ _ _ _)

end TracialStrategy

end CommutingRepetition
