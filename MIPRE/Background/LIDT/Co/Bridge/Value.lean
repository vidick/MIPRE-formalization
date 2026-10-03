/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Bridge.Value
public import MIPRE.Background.LIDT.Co.Bridge.Strategy
public import MIPRE.Background.LIDT.Co.Bridge.Defect

@[expose] public section

/-!
# Bridge, part 6, over models: the value of a strategy bounds the failure surrogate

The model counterpart of the repository's matrix bridge `MIPRE/Background/LIDT/Bridge/Value.lean`
(not a vendored file; it serves the tensor instance and stays), in the port of
`planning/c6b-plan.md` (milestone M14, unit M14-1).

The port's soundness hypothesis is a bound on `lowIndividualDegreeFailureProbability`
(`Co/Test/StrategyBiProj/Measurements.lean`), the vendored failure surrogate verbatim: an average,
over the verifier's samples, of two-space consistency defects between coarse-grained
measurements. Our hypothesis is a bound on the value `S.value = M.povmValue (lidtGame F m d) S.PA
S.PB` of a projective strategy `S : M.ProjStrat (lidtGame F m d)` in a bipartite model `M`. This
file shows

  `(toCoProjStrat S).lowIndividualDegreeFailureProbability ≤ 1 - S.value` (`failure_le`).

The value is the sum over samples `s` of `s.weight · acc S s` where `acc S x y` is the acceptance
probability given the questions `(x, y)`, a sum of Born probabilities `M.bornProb` of the
strategy's projections (`value_eq_sum`, through the model's `condWin`). For each sample the defect
of the corresponding branch is at most the rejection probability `1 - acc S s`
(`qBipartiteConsDefect_postprocess_le`, `Co/Bridge/Defect.lean`), because acceptance forces the two
coarse-grained outcomes to agree (the coarse-graining of the line answer is its evaluation at the
sampled point, that of the point answer its value). The branch weights of the two developments
agree, which gives the bound after reindexing the sample spaces through the field coding
(`failure_eq_sum`); the surrogate being the vendored expression verbatim, the reindexing is the
matrix bridge's.

**Reused by import.** The classical declarations of the matrix bridge, which mention no
measurement or state, are imported from `MIPRE.Background.LIDT.Bridge.Value` and named through an
explicit `open MIPRE.LIDT.Bridge (…)` list, which names none of the declarations redeclared here:
`lidtGame_μ`, the five acceptance characterizations `accepts_axisLine_point`,
`accepts_point_axisLine`, `accepts_point_point`, `accepts_diagLine_point`,
`accepts_point_diagLine`, `decP_extendLam` and `sum_fin_fun`; `Sample.sum_weight` and
`Sample.equivSum` are those of `MIPRE/Background/LIDT/Game.lean`.

## Not ported

Of the matrix bridge, `born` and `born_eq_ev` are not carried over: `born S x y a b` is the Born
probability `star ψ ⬝ᵥ ((P ⊗ₖ Q) *ᵥ ψ)` of a tensor-product strategy, which is the model's
`M.bornProb ((S.PA x).op a) ((S.PB y).op b)` here, written out in `acc`. The equations
`pointMeasA_eq`, `pointMeasB_eq`, `axisMeasA_zero_eq`, `axisMeasB_zero_eq` and `diagMeas_zero_eq`
are stated in `Co/Bridge/Strategy.lean`, for `toCoProjStrat`. Every other declaration that
mentions a strategy is redeclared here under its name: `acc`, `value_eq_sum`, `one_sub_value`,
`defect_le_rej`, `axisA_defect_le`, `axisB_defect_le`, `point_defect_le`, `diagA_defect_le`,
`diagB_defect_le`, `mdef`, `mdef_le`, `failure_eq_sum` and `failure_le`.
-/

universe u

open MIPStarRE.LDT (Fq DiagonalLine zeroCoord)
open MIPRE.LIDT.Bridge (lidtParams enc decP encP axisPolyOf diagPolyOf codedValue eval_ofCoeffs
  pointEquiv pointEquiv_apply lidtGame_μ accepts_axisLine_point accepts_point_axisLine
  accepts_point_point accepts_diagLine_point accepts_point_diagLine decP_extendLam sum_fin_fun)

noncomputable section

namespace MIPRE.LIDT.Co.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ]
  [StarOrderedRing ℬ] {M : MIPRE.BipartiteModel.{u} 𝒞 𝒜 ℬ}

/-! ## The value as a sum over samples -/

/-- The acceptance probability of the strategy `S` given the questions `(x, y)`: the Born
probabilities of the answer pairs the verifier accepts. -/
def acc (S : M.ProjStrat (lidtGame F m d)) (x y : Question F m) : ℝ :=
  ∑ a, ∑ b, if accepts F m d x y a b then M.bornProb ((S.PA x).op a) ((S.PB y).op b) else 0

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The value of a strategy is the weighted sum, over the verifier's samples, of the acceptance
probabilities given their questions. -/
theorem value_eq_sum (S : M.ProjStrat (lidtGame F m d)) :
    S.value = ∑ s : Sample F m, s.weight * acc S s.questions.1 s.questions.2 := by
  have h1 : ∀ x y, M.condWin (lidtGame F m d) S.PA S.PB x y = acc S x y := by
    intro x y
    unfold MIPRE.BipartiteModel.condWin acc
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change (if accepts F m d x y a b = true then (1 : ℝ) else 0) * _ = _
    split_ifs <;> simp
  change ∑ x, ∑ y, (lidtGame F m d).μ x y * M.condWin (lidtGame F m d) S.PA S.PB x y = _
  simp only [h1, lidtGame_μ, Finset.sum_mul]
  rw [← Fintype.sum_prod_type', Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun s => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [ite_mul, one_mul, zero_mul, Prod.mk.eta, Fintype.sum_ite_eq]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The rejection probability of a strategy is the weighted sum, over the verifier's samples, of
the rejection probabilities given their questions. -/
theorem one_sub_value (S : M.ProjStrat (lidtGame F m d)) :
    1 - S.value = ∑ s : Sample F m, s.weight * (1 - acc S s.questions.1 s.questions.2) := by
  rw [value_eq_sum]
  conv_lhs => rw [← Sample.sum_weight (F := F) (m := m)]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]

/-! ## Pointwise bounds -/

/-- The defect of two coarse-grained measurements of a strategy is at most the rejection
probability whenever acceptance forces the coarse-grained outcomes to agree. -/
theorem defect_le_rej (S : M.ProjStrat (lidtGame F m d)) (x y : Question F m)
    (f g : Answer F m d → Fq (lidtParams F m d))
    (hD : ∀ a b, accepts F m d x y a b = true → f a = g b) :
    qBipartiteConsDefect (toCoProjStrat S).state
      (postprocess (toProjMeas S.PA S.projA x).toSubMeas f)
      (postprocess (toProjMeas S.PB S.projB y).toSubMeas g) ≤ 1 - acc S x y :=
  qBipartiteConsDefect_postprocess_le (toCoProjStrat S).state (toCoProjStrat S).isNormalized
    (toProjMeas S.PA S.projA x).toSubMeas (toProjMeas S.PB S.projB y).toSubMeas rfl rfl f g
    (fun a b => accepts F m d x y a b = true) hD

/-- Axis-parallel lines test, line to A. -/
theorem axisA_defect_le (S : M.ProjStrat (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    qBipartiteConsDefect (toCoProjStrat S).state
      (postprocess ((toCoProjStrat S).axisParallelMeasurementA ⟨u, i⟩).toSubMeas (· zeroCoord))
      ((toCoProjStrat S).pointMeasurementB u).toSubMeas ≤
    1 - acc S (.axisLine (Line.through (decP u) (Pi.single i 1))) (.point (decP u)) := by
  rw [axisMeasA_zero_eq, pointMeasB_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨c, v, rfl, rfl, -, hcv⟩ := (accepts_axisLine_point _ _ _ _).mp hab
  rw [Line.param_through_single] at hcv
  simp [axisPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-- Axis-parallel lines test, line to B. -/
theorem axisB_defect_le (S : M.ProjStrat (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    qBipartiteConsDefect (toCoProjStrat S).state ((toCoProjStrat S).pointMeasurementA u).toSubMeas
      (postprocess ((toCoProjStrat S).axisParallelMeasurementB ⟨u, i⟩).toSubMeas (· zeroCoord)) ≤
    1 - acc S (.point (decP u)) (.axisLine (Line.through (decP u) (Pi.single i 1))) := by
  rw [axisMeasB_zero_eq, pointMeasA_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨v, c, rfl, rfl, -, hcv⟩ := (accepts_point_axisLine _ _ _ _).mp hab
  rw [Line.param_through_single] at hcv
  simp [axisPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-- Self-consistency test. -/
theorem point_defect_le (S : M.ProjStrat (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    qBipartiteConsDefect (toCoProjStrat S).state ((toCoProjStrat S).pointMeasurementA u).toSubMeas
      ((toCoProjStrat S).pointMeasurementB u).toSubMeas ≤
    1 - acc S (.point (decP u)) (.point (decP u)) := by
  rw [pointMeasA_eq, pointMeasB_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨v, w, rfl, rfl, -, rfl⟩ := (accepts_point_point _ _ _ _).mp hab
  rfl

/-- Diagonal lines test, line to A. -/
theorem diagA_defect_le (S : M.ProjStrat (lidtGame F m d))
    (ℓ : DiagonalLine (lidtParams F m d)) :
    qBipartiteConsDefect (toCoProjStrat S).state
      (postprocess ((toCoProjStrat S).diagonalMeasurementA ℓ).toSubMeas (· zeroCoord))
      ((toCoProjStrat S).pointMeasurementB ℓ.base).toSubMeas ≤
    1 - acc S (.diagLine (Line.through (decP ℓ.base) (decP ℓ.direction)))
      (.point (decP ℓ.base)) := by
  rw [show (toCoProjStrat S).diagonalMeasurementA ℓ = diagMeas S.PA S.projA ℓ from rfl,
    diagMeas_zero_eq, pointMeasB_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨c, v, rfl, rfl, -, hcv⟩ := (accepts_diagLine_point _ _ _ _).mp hab
  simp [diagPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-- Diagonal lines test, line to B. -/
theorem diagB_defect_le (S : M.ProjStrat (lidtGame F m d))
    (ℓ : DiagonalLine (lidtParams F m d)) :
    qBipartiteConsDefect (toCoProjStrat S).state
      ((toCoProjStrat S).pointMeasurementA ℓ.base).toSubMeas
      (postprocess ((toCoProjStrat S).diagonalMeasurementB ℓ).toSubMeas (· zeroCoord)) ≤
    1 - acc S (.point (decP ℓ.base))
      (.diagLine (Line.through (decP ℓ.base) (decP ℓ.direction))) := by
  rw [show (toCoProjStrat S).diagonalMeasurementB ℓ = diagMeas S.PB S.projB ℓ from rfl,
    diagMeas_zero_eq, pointMeasA_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨v, c, rfl, rfl, -, hcv⟩ := (accepts_point_diagLine _ _ _ _).mp hab
  simp [diagPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-! ## The bound -/

/-- The two-space consistency defect of the branch of a sample of our game. -/
def mdef (S : M.ProjStrat (lidtGame F m d)) : Sample F m → ℝ
  | .axis false u i => qBipartiteConsDefect (toCoProjStrat S).state
      (postprocess ((toCoProjStrat S).axisParallelMeasurementA ⟨encP u, i⟩).toSubMeas
        (· zeroCoord))
      ((toCoProjStrat S).pointMeasurementB (encP u)).toSubMeas
  | .axis true u i => qBipartiteConsDefect (toCoProjStrat S).state
      ((toCoProjStrat S).pointMeasurementA (encP u)).toSubMeas
      (postprocess ((toCoProjStrat S).axisParallelMeasurementB ⟨encP u, i⟩).toSubMeas
        (· zeroCoord))
  | .selfConsistency u => qBipartiteConsDefect (toCoProjStrat S).state
      ((toCoProjStrat S).pointMeasurementA (encP u)).toSubMeas
      ((toCoProjStrat S).pointMeasurementB (encP u)).toSubMeas
  | .diag false u j v => qBipartiteConsDefect (toCoProjStrat S).state
      (postprocess ((toCoProjStrat S).diagonalMeasurementA
        ⟨encP u, fun k => if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩)
          else zeroCoord⟩).toSubMeas (· zeroCoord))
      ((toCoProjStrat S).pointMeasurementB (encP u)).toSubMeas
  | .diag true u j v => qBipartiteConsDefect (toCoProjStrat S).state
      ((toCoProjStrat S).pointMeasurementA (encP u)).toSubMeas
      (postprocess ((toCoProjStrat S).diagonalMeasurementB
        ⟨encP u, fun k => if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩)
          else zeroCoord⟩).toSubMeas (· zeroCoord))

/-- Each branch defect is at most the rejection probability of the sample. -/
theorem mdef_le (S : M.ProjStrat (lidtGame F m d)) (s : Sample F m) :
    mdef S s ≤ 1 - acc S s.questions.1 s.questions.2 := by
  rcases s with ⟨_ | _, u, i⟩ | u | ⟨_ | _, u, j, v⟩
  · simpa [mdef, Sample.questions] using axisA_defect_le S (encP u) i
  · simpa [mdef, Sample.questions] using axisB_defect_le S (encP u) i
  · simpa [mdef, Sample.questions] using point_defect_le S (encP u)
  · have h := diagA_defect_le S ⟨encP u, fun k => if h : k.val ≤ j.val then
      enc (v ⟨k.val, Nat.lt_succ_of_le h⟩) else zeroCoord⟩
    rw [decP_extendLam] at h
    simpa [mdef, Sample.questions] using h
  · have h := diagB_defect_le S ⟨encP u, fun k => if h : k.val ≤ j.val then
      enc (v ⟨k.val, Nat.lt_succ_of_le h⟩) else zeroCoord⟩
    rw [decP_extendLam] at h
    simpa [mdef, Sample.questions] using h

/-- The failure surrogate of the induced strategy is the weighted sum of the branch defects over
our samples. -/
theorem failure_eq_sum (S : M.ProjStrat (lidtGame F m d)) :
    (toCoProjStrat S).lowIndividualDegreeFailureProbability =
      ∑ s : Sample F m, s.weight * mdef S s := by
  rw [← Sample.equivSum.symm.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, Sample.equivSum,
    Equiv.coe_fn_symm_mk, Sample.weight, mdef, Fintype.sum_bool]
  unfold MIPRE.LIDT.Co.ProjStrat.lowIndividualDegreeFailureProbability
  simp only [bipartiteConsError_uniform, Fintype.sum_prod_type, ← pointEquiv.sum_comp,
    sum_fin_fun, pointEquiv_apply, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, IdxProjMeas.toIdxSubMeas]
  conv_rhs => enter [2, 2, 1]; rw [Finset.sum_comm]
  conv_rhs => enter [2, 2, 2]; rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hw : ∀ (j : Fin m) (X : ℝ),
      1 / (6 * (m : ℝ) * (Fintype.card F : ℝ) ^ m * (Fintype.card F : ℝ) ^ (j.val + 1)) * X =
        1 / (6 * (m : ℝ)) *
          (1 / ((Fintype.card F : ℝ) ^ m * (Fintype.card F : ℝ) ^ (j.val + 1)) * X) := by
    intro j X
    field_simp
  simp only [hw, ← Finset.mul_sum]
  ring

/-- **The failure surrogate of the induced strategy is at most the rejection probability of the
strategy in the game.** -/
theorem failure_le (S : M.ProjStrat (lidtGame F m d)) :
    (toCoProjStrat S).lowIndividualDegreeFailureProbability ≤ 1 - S.value := by
  rw [failure_eq_sum, one_sub_value]
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (mdef_le S s) s.weight_nonneg

end MIPRE.LIDT.Co.Bridge

end

end
