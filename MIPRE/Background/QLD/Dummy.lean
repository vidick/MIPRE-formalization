/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.PaddedStrategy
public import MIPRE.Background.QLD.Uniform
public import MIPRE.Foundations.LowDegree.SchwartzZippel
public import MIPRE.Background.LIDT.Coefficients

@[expose] public section

/-!
# Removing the dummy coordinates (`lem:qld-global-dummy`)

The global polynomial measurements of `lem:qld-global-pvm` have outcomes in
`LowIndDegPoly F (4m) d`, polynomials in the `4m` coordinates of the padded point, while the
padded point measurements read only the `2m + 2` coordinates `xBlk`, `zBlk`, `alph`, `bet`
(`padPt_mats`). The remaining `2m - 2` coordinates are the paper's dummy coordinates `w`. This file
proves that an outcome which reads a dummy coordinate carries little state weight: if the
evaluated global measurement is `δ`-consistent, on average over a uniform point, with a point
measurement that does not read the dummy coordinates, then the total weight of such outcomes is at
most `2δ / (1 - 8md/q)`, hence `4δ` once `16 m d ≤ q`.

## The argument

Resample the dummy coordinates: for two independent uniform points `u`, `u'`, let `mix u u'` be
`u` with its dummy coordinates replaced by those of `u'`. The point measurement is the same at `u`
and at `mix u u'`, and `(u, u') ↦ (mix u u', mix u' u)` is an involution of the pairs, so the
consistency estimate holds at both points simultaneously. Adding the two, the operator
`P_u(g(u)) + P_u(g(mix u u'))` is at most `2 · 1` when the two values agree and at most `1` when
they differ (two distinct elements of a POVM sum to at most the identity; no projectivity is
used), which gives `∑_g ⟨G_g⟩ · Pr[g(u) = g(mix u u')] ≥ 1 - 2δ` (`sum_mass_mixAgree_ge`). For an
outcome that reads a dummy coordinate, `g(u) - g(mix u u')` is a nonzero polynomial in the `8m`
coordinates of the pair, of individual degree at most `d`, so Schwartz--Zippel bounds the
probability by `8md/q` (`card_mixAgree_le`); for one that does not, the probability is `1`
(`eval_mix_of_wIndep`). The two bounds give `sum_bad_mass_le`.

## The bridge to `MvPolynomial`

`LowIndDegPoly.toMv`, `degreeOf_rename_le` and `prob_agreeOn_le_individualDegree` (Schwartz--Zippel
for any finite variable type, which is what the pair `Fin (4m) ⊕ Fin (4m)` needs) were written
here and now live in `MIPRE/Background/LIDT/Coefficients.lean`, where the simultaneous low-degree
test can use them too.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The state is that of a
bipartite model `K` --- the model in which the low individual degree test is applied, `padModel`,
or any other --- the global measurement is a POVM `G` in the first player's algebra (`POVMIn`),
evaluated at a point by `evalPOVMIn`, the point measurement is a family of POVMs in the second
player's algebra, and the weight of an outcome is the Born probability `K.bornProb (G.op g) 1`.
That two distinct elements of a POVM sum to at most one holds in any star-ordered ring
(`POVMIn.add_le_one`), and the elements of `G` are nonnegative as those of a POVM, so neither
measurement needs to be projective. The second player's version is the first player's in the
exchanged model `K.swap` (`BipartiteModel.inconsistency_swap`, `BipartiteModel.bornProb_swap`).
The polynomial half is unchanged.
-/

noncomputable section

namespace MIPRE

open Finset

/-! ## Born-rule and POVM facts -/

section Born

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The Born probability is additive in the second player's operator. -/
theorem bornProb_add_right (M : BipartiteModel 𝒞 𝒜 ℬ) (X : 𝒜) (Y Z : ℬ) :
    M.bornProb X (Y + Z) = M.bornProb X Y + M.bornProb X Z := by
  have h := M.bornProb_sub_right X (Y + Z) Z
  rw [add_sub_cancel_right] at h
  linarith

end Born

/-- **Two distinct elements of a POVM sum to at most one**, in any star-ordered ring. -/
theorem POVMIn.add_le_one {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    {A : Type*} [Fintype A] [DecidableEq A] (M : POVMIn A R) {b b' : A} (h : b ≠ b') :
    M.op b + M.op b' ≤ 1 := by
  have hpair : M.op b + M.op b' = ∑ x ∈ ({b, b'} : Finset A), M.op x :=
    (Finset.sum_pair (f := fun x => M.op x) h).symm
  rw [← M.sum_op, hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun a _ _ => M.op_nonneg a

theorem sum_ite_eq_zero_sub {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup β] (a : α)
    (x : α → β) : (∑ b, if a = b then 0 else x b) = (∑ b, x b) - x a := by
  have h : ((∑ b, if a = b then 0 else x b) + ∑ b, if a = b then x b else 0) = ∑ b, x b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_ite_eq univ a x, if_pos (mem_univ a)] at h
  exact eq_sub_of_add_eq h

end MIPRE

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LIDT MvPolynomial

/-! ## The inconsistency of an evaluated global measurement, unfolded -/

section Mass

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}

/-- **A global measurement evaluated at a point**: the POVM with outcomes in `F` whose element at
`a` is the sum of the elements at the polynomials `g` with `g(u) = a`. The model form of
`LIDT.evalPOVM`, in any star-ordered ring. -/
def evalPOVMIn {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (G : POVMIn (LowIndDegPoly (F := F) (m := n) (d := d)) R) (u : Point F n) : POVMIn F R :=
  G.map fun g => g.eval u

theorem evalPOVMIn_op {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (G : POVMIn (LowIndDegPoly (F := F) (m := n) (d := d)) R) (u : Point F n) (a : F) :
    (evalPOVMIn G u).op a = ∑ g ∈ univ.filter fun g => g.eval u = a, G.op g :=
  POVMIn.map_op _ _ _

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]

/-- **The inconsistency of an evaluated global measurement with a point measurement** is one minus
the average weight the global outcome's value at the point receives from the point measurement:
`1 - ∑_u μ_u ∑_g ⟨G_g ⊗ P_u(g(u))⟩`. -/
theorem inconsistency_evalPOVM_eq [StarOrderedRing 𝒜] (μ : Point F n → ℝ) (hμ : ∑ u, μ u = 1)
    {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := n) (d := d)) 𝒜) (P : Point F n → POVMIn F ℬ) :
    K.inconsistency μ (evalPOVMIn G) P
      = 1 - ∑ u, μ u * ∑ g, K.bornProb (G.op g) ((P u).op (g.eval u)) := by
  have hfib : ∀ u, (∑ a : F, ∑ b : F, if a = b then 0 else
      K.bornProb ((evalPOVMIn G u).op a) ((P u).op b))
      = ∑ g, ∑ b : F, if g.eval u = b then 0 else K.bornProb (G.op g) ((P u).op b) := by
    intro u
    have h1 : ∀ a b : F, (if a = b then (0 : ℝ) else
        K.bornProb ((evalPOVMIn G u).op a) ((P u).op b))
        = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := n) (d := d) => g.eval u = a,
            if a = b then 0 else K.bornProb (G.op g) ((P u).op b) := by
      intro a b
      rw [evalPOVMIn_op, K.bornProb_sum_left]
      split_ifs
      · simp
      · rfl
    simp_rw [h1]
    rw [← Finset.sum_fiberwise univ fun g : LowIndDegPoly (F := F) (m := n) (d := d) => g.eval u]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [(mem_filter.mp hg).2]
  have hsum : ∀ u, (∑ g, ∑ b : F, if g.eval u = b then 0 else
      K.bornProb (G.op g) ((P u).op b))
      = 1 - ∑ g, K.bornProb (G.op g) ((P u).op (g.eval u)) := by
    intro u
    simp_rw [sum_ite_eq_zero_sub, ← K.bornProb_sum_right, (P u).sum_op]
    rw [Finset.sum_sub_distrib, ← K.bornProb_sum_left, G.sum_op, K.bornProb_one_one hK]
  unfold BipartiteModel.inconsistency
  simp only [hfib, hsum, mul_sub, mul_one, Finset.sum_sub_distrib, hμ]

omit [PartialOrder ℬ] in
/-- The total weight of a POVM's outcomes is one. -/
theorem sum_bornProb_M_one {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1) {A : Type*} [Fintype A]
    (G : POVMIn A 𝒜) : ∑ g, K.bornProb (G.op g) 1 = 1 := by
  rw [← K.bornProb_sum_left, G.sum_op, K.bornProb_one_one hK]

end Mass

/-! ## The dummy coordinates -/

section Dummy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- A coordinate of the padded point that no padded point measurement reads: everything past
`xBlk`, `zBlk`, `alph`, `bet`. -/
def IsDummy (i : Fin (4 * m)) : Prop := 2 * m + 2 ≤ (i : ℕ)

instance : DecidablePred (IsDummy (m := m)) := fun i =>
  inferInstanceAs (Decidable (2 * m + 2 ≤ (i : ℕ)))

theorem not_isDummy_xIdx (i : Fin m) : ¬ IsDummy (xIdx m i) := by
  simp only [IsDummy, xIdx_val, not_le]
  have := i.isLt
  omega

theorem not_isDummy_zIdx (i : Fin m) : ¬ IsDummy (zIdx m i) := by
  simp only [IsDummy, zIdx_val, not_le]
  have := i.isLt
  omega

theorem not_isDummy_aIdx : ¬ IsDummy (aIdx m) := by
  simp only [IsDummy, aIdx_val, not_le]
  omega

theorem not_isDummy_bIdx : ¬ IsDummy (bIdx m) := by
  simp only [IsDummy, bIdx_val, not_le]
  omega

omit [NeZero m] in
/-- For `m = 1` there are no dummy coordinates. -/
theorem not_isDummy_of_eq_one (hm : m = 1) (i : Fin (4 * m)) : ¬ IsDummy i := by
  simp only [IsDummy, not_le]
  have := i.isLt
  omega

/-- **Resampling the dummy coordinates**: `u` with its dummy coordinates replaced by those of
`u'`. -/
def mix (u u' : Point F (4 * m)) : Point F (4 * m) := fun i => if IsDummy i then u' i else u i

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem mix_apply_of_not (u u' : Point F (4 * m)) {i : Fin (4 * m)} (h : ¬ IsDummy i) :
    mix u u' i = u i := if_neg h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem mix_apply_of (u u' : Point F (4 * m)) {i : Fin (4 * m)} (h : IsDummy i) :
    mix u u' i = u' i := if_pos h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem xBlk_mix (u u' : Point F (4 * m)) : xBlk (mix u u') = xBlk u :=
  funext fun i => mix_apply_of_not u u' (not_isDummy_xIdx i)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem zBlk_mix (u u' : Point F (4 * m)) : zBlk (mix u u') = zBlk u :=
  funext fun i => mix_apply_of_not u u' (not_isDummy_zIdx i)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem alph_mix (u u' : Point F (4 * m)) : alph (mix u u') = alph u :=
  mix_apply_of_not u u' not_isDummy_aIdx

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem bet_mix (u u' : Point F (4 * m)) : bet (mix u u') = bet u :=
  mix_apply_of_not u u' not_isDummy_bIdx

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem mix_mix (u u' : Point F (4 * m)) : mix (mix u u') (mix u' u) = u := by
  funext i
  unfold mix
  split_ifs <;> rfl

/-- The involution of pairs of points that exchanges their dummy coordinates. -/
def mixSwap : Point F (4 * m) × Point F (4 * m) ≃ Point F (4 * m) × Point F (4 * m) where
  toFun p := (mix p.1 p.2, mix p.2 p.1)
  invFun p := (mix p.1 p.2, mix p.2 p.1)
  left_inv p := Prod.ext (mix_mix p.1 p.2) (mix_mix p.2 p.1)
  right_inv p := Prod.ext (mix_mix p.1 p.2) (mix_mix p.2 p.1)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mixSwap_apply_fst (p : Point F (4 * m) × Point F (4 * m)) :
    (mixSwap p).1 = mix p.1 p.2 := rfl

/-- **The padded point measurement does not read the dummy coordinates.** -/
theorem padPt_mix {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R]
    {S : Question F m → POVMIn (Answer F m d) R} (hS : ∀ q, IsPVMIn (S q).op)
    (u u' : Point F (4 * m)) : padPt hS (mix u u') = padPt hS u :=
  POVMIn.ext' fun a => by rw [padPt_mats, padPt_mats, xBlk_mix, zBlk_mix, alph_mix, bet_mix]

/-- **`w`-independence**: a coefficient vector with no monomial involving a dummy coordinate. -/
def WIndep (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) : Prop :=
  ∀ e : Fin (4 * m) → Fin (d + 1), (∃ i, IsDummy i ∧ e i ≠ 0) → g e = 0

instance : DecidablePred (WIndep (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (∀ e : Fin (4 * m) → Fin (d + 1),
    (∃ i, IsDummy i ∧ e i ≠ 0) → g e = 0))

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem wIndep_of_eq_one (hm : m = 1) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    WIndep g := fun _ ⟨i, hi, _⟩ => absurd hi (not_isDummy_of_eq_one hm i)

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A `w`-independent outcome takes the same value after resampling the dummy coordinates. -/
theorem eval_mix_of_wIndep {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : WIndep g)
    (u u' : Point F (4 * m)) : g.eval (mix u u') = g.eval u := by
  unfold LowIndDegPoly.eval
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : ∃ i, IsDummy i ∧ e i ≠ 0
  · rw [hg e he, zero_mul, zero_mul]
  · push Not at he
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : IsDummy i
    · rw [he i hi]
      simp
    · rw [mix_apply_of_not u u' hi]

/-! ### Schwartz--Zippel on the pair -/

/-- The substitution that reads the dummy coordinates from the second point of a pair. -/
def dumSub (i : Fin (4 * m)) : Fin (4 * m) ⊕ Fin (4 * m) :=
  if IsDummy i then Sum.inr i else Sum.inl i

omit [NeZero m] in
theorem dumSub_injective : Function.Injective (dumSub (m := m)) := by
  intro i j h
  unfold dumSub at h
  split_ifs at h <;> simp_all

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem comp_dumSub (x : Fin (4 * m) ⊕ Fin (4 * m) → F) :
    x ∘ dumSub = mix (x ∘ Sum.inl) (x ∘ Sum.inr) := by
  funext i
  simp only [Function.comp_apply, dumSub, mix]
  split_ifs <;> rfl

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- An outcome that reads a dummy coordinate is a different polynomial of the pair before and
after the resampling. -/
theorem rename_toMv_ne {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : ¬ WIndep g) :
    rename Sum.inl g.toMv ≠ rename dumSub g.toMv := by
  intro heq
  unfold WIndep at hg
  push Not at hg
  obtain ⟨e, ⟨i, hi, hei⟩, hge⟩ := hg
  set inl : Fin (4 * m) → Fin (4 * m) ⊕ Fin (4 * m) := Sum.inl with hinl
  have hinj : Function.Injective inl := Sum.inl_injective
  have h1 : (rename inl g.toMv).coeff (Finsupp.mapDomain inl (expFinsupp e)) = g e := by
    rw [coeff_rename_mapDomain _ hinj, LowIndDegPoly.coeff_toMv]
  have h2 : (rename dumSub g.toMv).coeff (Finsupp.mapDomain inl (expFinsupp e)) = 0 := by
    refine coeff_rename_eq_zero _ _ _ fun v hv => ?_
    exfalso
    have hval := congrArg (fun w : Fin (4 * m) ⊕ Fin (4 * m) →₀ ℕ => w (inl i)) hv
    have hnot : inl i ∉ Set.range (dumSub (m := m)) := by
      rintro ⟨j, hj⟩
      unfold dumSub at hj
      by_cases hD : IsDummy j
      · rw [if_pos hD, hinl] at hj
        exact absurd hj (by simp)
      · rw [if_neg hD, hinl, Sum.inl.injEq] at hj
        subst hj
        exact hD hi
    rw [Finsupp.mapDomain_of_notMem_range _ _ hnot, Finsupp.mapDomain_apply_of_injective hinj,
      expFinsupp_apply] at hval
    exact hei (Fin.ext (by simpa using hval.symm))
  rw [heq, h2] at h1
  exact hge h1.symm

/-- The pairs of points at which an outcome takes the same value before and after resampling
the dummy coordinates. -/
def mixAgree (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    Finset (Point F (4 * m) × Point F (4 * m)) :=
  univ.filter fun p => g.eval p.1 = g.eval (mix p.1 p.2)

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem mixAgree_eq_univ_of_wIndep {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : WIndep g) : mixAgree g = univ :=
  Finset.filter_true_of_mem fun p _ => (eval_mix_of_wIndep hg p.1 p.2).symm

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **Schwartz--Zippel for the dummy coordinates**: an outcome that reads a dummy coordinate
takes the same value before and after the resampling with probability at most `8md/q`. -/
theorem card_mixAgree_le {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : ¬ WIndep g) :
    ((mixAgree g).card : ℝ) / (Fintype.card F : ℝ) ^ (4 * m + 4 * m)
      ≤ ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F := by
  have h := LowDegree.prob_agreeOn_le_individualDegree (rename_toMv_ne hg)
    (degreeOf_rename_le Sum.inl_injective (LowIndDegPoly.degreeOf_toMv_le g))
    (degreeOf_rename_le dumSub_injective (LowIndDegPoly.degreeOf_toMv_le g))
  have hcard : (LowDegree.agreeOn (rename Sum.inl g.toMv) (rename dumSub g.toMv)).card
      = (mixAgree g).card := by
    refine Finset.card_equiv (Equiv.sumArrowEquivProdArrow _ _ _) fun x => ?_
    rw [LowDegree.mem_agreeOn, mixAgree, mem_filter, eval_rename, eval_rename,
      LowIndDegPoly.eval_toMv, LowIndDegPoly.eval_toMv, comp_dumSub]
    exact ⟨fun h => ⟨mem_univ _, h⟩, fun h => h.2⟩
  rw [hcard, Fintype.card_sum, Fintype.card_fin] at h
  exact h

/-! ### The weight of the outcomes that read a dummy coordinate -/

section Weight

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The resampling estimate.** If the evaluated global measurement is `δ`-consistent, on average
over a uniform point, with a point measurement that does not read the dummy coordinates, then
`∑_g ⟨G_g⟩ · Pr[g(u) = g(mix u u')] ≥ 1 - 2δ`: the consistency holds at `u` and at `mix u u'`
simultaneously, and two distinct elements of a POVM sum to at most one. -/
theorem sum_mass_mixAgree_ge {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜)
    (P : Point F (4 * m) → POVMIn F ℬ) (hP : ∀ u u', P (mix u u') = P u) {δ : ℝ}
    (hcons : K.inconsistency (uniform (Point F (4 * m))) (evalPOVMIn G) P ≤ δ) :
    1 - 2 * δ ≤ ∑ g, K.bornProb (G.op g) 1
      * (((mixAgree g).card : ℝ) / (Fintype.card F : ℝ) ^ (4 * m + 4 * m)) := by
  set μ := uniform (Point F (4 * m)) with hμdef
  have hμ1 : ∑ u, μ u = 1 := sum_uniform_eq_one _
  set c : ℝ := (Fintype.card (Point F (4 * m)) : ℝ)⁻¹ with hc
  have hcard_c : (Fintype.card (Point F (4 * m)) : ℝ) * c = 1 :=
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  set S : Point F (4 * m) → ℝ :=
    fun u => ∑ g, K.bornProb (G.op g) ((P u).op (g.eval u)) with hS
  have h1 : 1 - δ ≤ ∑ u, c * S u := by
    rw [inconsistency_evalPOVM_eq μ hμ1 hK G P] at hcons
    have : ∑ u, μ u * ∑ g, K.bornProb (G.op g) ((P u).op (g.eval u)) = ∑ u, c * S u := rfl
    linarith
  have hpair : ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S p.1 = ∑ u, c * S u := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    calc (Fintype.card (Point F (4 * m)) : ℝ) * (c * c * S u)
        = ((Fintype.card (Point F (4 * m)) : ℝ) * c) * (c * S u) := by ring
      _ = c * S u := by rw [hcard_c, one_mul]
  have hswap : ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S (mix p.1 p.2)
      = ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S p.1 := by
    have := Equiv.sum_comp mixSwap (fun p : Point F (4 * m) × Point F (4 * m) => c * c * S p.1)
    simpa only [mixSwap_apply_fst] using this
  have h2 : 2 * (1 - δ)
      ≤ ∑ p : Point F (4 * m) × Point F (4 * m), c * c * (S p.1 + S (mix p.1 p.2)) := by
    have e1 : 1 - δ ≤ ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S p.1 := by
      rw [hpair]; exact h1
    have e2 : 1 - δ ≤ ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S (mix p.1 p.2) := by
      rw [hswap]; exact e1
    simp only [mul_add, Finset.sum_add_distrib]
    linarith
  have hpt : ∀ (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) (u u' : Point F (4 * m)),
      K.bornProb (G.op g) ((P u).op (g.eval u))
        + K.bornProb (G.op g) ((P (mix u u')).op (g.eval (mix u u')))
        ≤ (1 + if g.eval u = g.eval (mix u u') then 1 else 0) * K.bornProb (G.op g) 1 := by
    intro g u u'
    have hG := G.op_nonneg g
    rw [hP, ← bornProb_add_right]
    split_ifs with heq
    · rw [heq]
      calc K.bornProb (G.op g)
            ((P u).op (g.eval (mix u u')) + (P u).op (g.eval (mix u u')))
          ≤ K.bornProb (G.op g) (1 + 1) :=
            bornProb_mono_right K hG (add_le_add ((P u).op_le_one _) ((P u).op_le_one _))
        _ = (1 + 1) * K.bornProb (G.op g) 1 := by rw [bornProb_add_right]; ring
    · calc K.bornProb (G.op g) ((P u).op (g.eval u) + (P u).op (g.eval (mix u u')))
          ≤ K.bornProb (G.op g) 1 := bornProb_mono_right K hG ((P u).add_le_one heq)
        _ = (1 + 0) * K.bornProb (G.op g) 1 := by ring
  have hc2 : ∑ _p : Point F (4 * m) × Point F (4 * m), c * c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
    push_cast
    calc ((Fintype.card (Point F (4 * m)) : ℝ) * Fintype.card (Point F (4 * m))) * (c * c)
        = ((Fintype.card (Point F (4 * m)) : ℝ) * c) * (Fintype.card (Point F (4 * m)) * c) := by
          ring
      _ = 1 := by rw [hcard_c, one_mul]
  have hsum : ∑ p : Point F (4 * m) × Point F (4 * m), c * c * (S p.1 + S (mix p.1 p.2))
      ≤ ∑ g, K.bornProb (G.op g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c)) := by
    calc ∑ p : Point F (4 * m) × Point F (4 * m), c * c * (S p.1 + S (mix p.1 p.2))
        = ∑ p : Point F (4 * m) × Point F (4 * m), ∑ g, c * c
            * (K.bornProb (G.op g) ((P p.1).op (g.eval p.1))
              + K.bornProb (G.op g) ((P (mix p.1 p.2)).op (g.eval (mix p.1 p.2)))) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          show c * c * (∑ g, K.bornProb (G.op g) ((P p.1).op (g.eval p.1))
            + ∑ g, K.bornProb (G.op g) ((P (mix p.1 p.2)).op (g.eval (mix p.1 p.2)))) = _
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ p : Point F (4 * m) × Point F (4 * m), ∑ g, c * c
            * ((1 + if g.eval p.1 = g.eval (mix p.1 p.2) then 1 else 0)
              * K.bornProb (G.op g) 1) := by
          refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun g _ => ?_
          exact mul_le_mul_of_nonneg_left (hpt g p.1 p.2) (by positivity)
      _ = ∑ g, K.bornProb (G.op g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          have hind : ∑ p : Point F (4 * m) × Point F (4 * m),
              c * c * (if g.eval p.1 = g.eval (mix p.1 p.2) then (1 : ℝ) else 0)
              = c * c * (mixAgree g).card := by
            rw [← Finset.mul_sum, Finset.sum_boole, mixAgree]
          calc ∑ p : Point F (4 * m) × Point F (4 * m), c * c
                * ((1 + if g.eval p.1 = g.eval (mix p.1 p.2) then (1 : ℝ) else 0)
                  * K.bornProb (G.op g) 1)
              = K.bornProb (G.op g) 1 * ((∑ _p : Point F (4 * m) × Point F (4 * m), c * c)
                + ∑ p : Point F (4 * m) × Point F (4 * m),
                    c * c * (if g.eval p.1 = g.eval (mix p.1 p.2) then (1 : ℝ) else 0)) := by
                rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun p _ => ?_
                ring
            _ = K.bornProb (G.op g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c)) := by
                rw [hc2, hind]
                ring
  have hmass : ∑ g, K.bornProb (G.op g) 1 = 1 := sum_bornProb_M_one hK G
  have hcc : c * c = ((Fintype.card F : ℝ) ^ (4 * m + 4 * m))⁻¹ := by
    rw [hc, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [← mul_inv, ← pow_add]
  have hfin : ∑ g, K.bornProb (G.op g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c))
      = 1 + ∑ g, K.bornProb (G.op g) 1
          * (((mixAgree g).card : ℝ) / (Fintype.card F : ℝ) ^ (4 * m + 4 * m)) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hmass, hcc, div_eq_mul_inv]
  linarith

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **`lem:qld-global-dummy`.** If the evaluated global measurement is `δ`-consistent with a point
measurement that does not read the dummy coordinates, the total weight of the outcomes that read
one satisfies `(1 - 8md/q) · weight ≤ 2δ`. -/
theorem sum_bad_mass_le {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜)
    (P : Point F (4 * m) → POVMIn F ℬ) (hP : ∀ u u', P (mix u u') = P u) {δ : ℝ}
    (hcons : K.inconsistency (uniform (Point F (4 * m))) (evalPOVMIn G) P ≤ δ) :
    (1 - ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F)
      * ∑ g ∈ univ.filter (fun g => ¬ WIndep g), K.bornProb (G.op g) 1 ≤ 2 * δ := by
  have h := sum_mass_mixAgree_ge hK G P hP hcons
  have hmass := sum_bornProb_M_one hK G
  set η : ℝ := ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F with hη
  set Q : ℝ := (Fintype.card F : ℝ) ^ (4 * m + 4 * m) with hQ
  have hQpos : 0 < Q := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  have hPQ : (Fintype.card (Point F (4 * m) × Point F (4 * m)) : ℝ) = Q := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [hQ, pow_add]
  rw [← Finset.sum_filter_add_sum_filter_not univ fun g => WIndep g] at h hmass
  have hgood : ∑ g ∈ univ.filter (fun g => WIndep g),
      K.bornProb (G.op g) 1 * (((mixAgree g).card : ℝ) / Q)
      = ∑ g ∈ univ.filter (fun g => WIndep g), K.bornProb (G.op g) 1 := by
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [mixAgree_eq_univ_of_wIndep (mem_filter.mp hg).2, Finset.card_univ, hPQ,
      div_self hQpos.ne', mul_one]
  have hbad : ∑ g ∈ univ.filter (fun g => ¬ WIndep g),
      K.bornProb (G.op g) 1 * (((mixAgree g).card : ℝ) / Q)
      ≤ η * ∑ g ∈ univ.filter (fun g => ¬ WIndep g), K.bornProb (G.op g) 1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun g hg => ?_
    rw [mul_comm η]
    exact mul_le_mul_of_nonneg_left (card_mixAgree_le (mem_filter.mp hg).2)
      (K.bornProb_nonneg (G.op_nonneg g) zero_le_one)
  rw [hgood] at h
  rw [sub_mul, one_mul]
  linarith

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- `lem:qld-global-dummy` with the standing assumption `16 m d ≤ q`: the weight of the outcomes
that read a dummy coordinate is at most `4δ`. -/
theorem sum_bad_mass_le_of_le {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜)
    (P : Point F (4 * m) → POVMIn F ℬ) (hP : ∀ u u', P (mix u u') = P u) {δ : ℝ}
    (hcons : K.inconsistency (uniform (Point F (4 * m))) (evalPOVMIn G) P ≤ δ)
    (hq : 16 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ WIndep g), K.bornProb (G.op g) 1 ≤ 4 * δ := by
  have h := sum_bad_mass_le hK G P hP hcons
  have hB : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ WIndep g), K.bornProb (G.op g) 1 :=
    Finset.sum_nonneg fun g _ => K.bornProb_nonneg (G.op_nonneg g) zero_le_one
  have hη : ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F ≤ 1 / 2 := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
    have : ((16 * m * d : ℕ) : ℝ) ≤ Fintype.card F := Nat.cast_le.mpr hq
    push_cast at this ⊢
    linarith
  nlinarith

end Weight

end Dummy

end MIPRE.QLD

end

end
