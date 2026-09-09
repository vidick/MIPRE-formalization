/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Bridge.Strategy
import MIPRE.Background.LIDT.Bridge.Defect
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProj.Measurements

/-!
# Bridge, part 6: the value of a strategy bounds the MIPStarRE failure probability

MIPStarRE's hypothesis is a bound on `lowIndividualDegreeFailureProbability`, a
trace-based surrogate for the failure probability: an average, over the verifier's
samples, of consistency defects between coarse-grained measurements. Our hypothesis is
a bound on the value `S.value` of the strategy in the game. This file shows

  `(toProjStrat S).lowIndividualDegreeFailureProbability ≤ 1 - S.value`.

The value is the sum over samples `s` of `s.weight · acc s` where `acc s` is the
acceptance probability given the questions of `s` (`value_eq_sum`). For each sample the
defect of the corresponding branch is at most the rejection probability `1 - acc s`,
by `qBipartiteConsDefect_postprocess_le`, because acceptance forces the two
coarse-grained outcomes to agree (the coarse-graining of the line answer is its
evaluation at the sampled point, that of the point answer is its value). The branch
weights of the two developments agree, which gives the bound after reindexing the
sample spaces through the field coding.
-/

open MIPStarRE.LDT (ProjStrat QuantumState ev opTensor qBipartiteConsDefect bipartiteConsError
  uniformDistribution avgOver Distribution SubMeas postprocess IdxSubMeas ProjMeas Fq zeroCoord
  AxisParallelLine DiagonalLine)
open scoped Kronecker
open Matrix

noncomputable section

namespace MIPRE.LIDT.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## The value as a sum over samples -/

/-- The Born-rule probability of the answers `(a, b)` to the questions `(x, y)`. -/
def born (S : TensorProductStrategy (lidtGame F m d)) (x y : Question F m) (a b : Answer F m d) :
    ℝ :=
  (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

theorem born_eq_ev (S : TensorProductStrategy (lidtGame F m d)) (x y : Question F m)
    (a b : Answer F m d) :
    born S x y a b = ev (toProjStrat S).state (opTensor (S.PA.M x a) (S.PB.M y b)) :=
  (ev_toProjStrat S _).symm

/-- The acceptance probability given the questions `(x, y)`. -/
def acc (S : TensorProductStrategy (lidtGame F m d)) (x y : Question F m) : ℝ :=
  ∑ a, ∑ b, if accepts F m d x y a b then born S x y a b else 0

theorem lidtGame_μ (x y : Question F m) :
    (lidtGame F m d).μ x y = ∑ s : Sample F m, s.weight * if s.questions = (x, y) then 1 else 0 :=
  rfl

theorem value_eq_sum (S : TensorProductStrategy (lidtGame F m d)) :
    S.value = ∑ s : Sample F m, s.weight * acc S s.questions.1 s.questions.2 := by
  change ∑ x, ∑ y, ∑ a, ∑ b, (lidtGame F m d).μ x y *
    (if accepts F m d x y a b then (1 : ℝ) else 0) * born S x y a b = _
  have h1 : ∀ x y, ∑ a, ∑ b, (lidtGame F m d).μ x y *
      (if accepts F m d x y a b then (1 : ℝ) else 0) * born S x y a b =
      (lidtGame F m d).μ x y * acc S x y := by
    intro x y
    simp only [acc, Finset.mul_sum, mul_assoc]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  simp only [h1]
  simp only [lidtGame_μ, Finset.sum_mul]
  rw [← Fintype.sum_prod_type', Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun s => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [ite_mul, one_mul, zero_mul, Prod.mk.eta, Fintype.sum_ite_eq]

theorem one_sub_value (S : TensorProductStrategy (lidtGame F m d)) :
    1 - S.value = ∑ s : Sample F m, s.weight * (1 - acc S s.questions.1 s.questions.2) := by
  rw [value_eq_sum]
  conv_lhs => rw [← Sample.sum_weight (F := F) (m := m)]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]

/-! ## Pointwise bounds -/

/-- The defect of two coarse-grained measurements of a strategy is at most the rejection
probability whenever acceptance forces the coarse-grained outcomes to agree. -/
theorem defect_le_rej (S : TensorProductStrategy (lidtGame F m d)) (x y : Question F m)
    (f g : Answer F m d → Fq (lidtParams F m d))
    (hD : ∀ a b, accepts F m d x y a b = true → f a = g b) :
    qBipartiteConsDefect (toProjStrat S).state (postprocess (toProjMeas S.PA x).toSubMeas f)
      (postprocess (toProjMeas S.PB y).toSubMeas g) ≤ 1 - acc S x y := by
  refine (qBipartiteConsDefect_postprocess_le (toProjStrat S).state (toProjStrat S).isNormalized
    (toProjMeas S.PA x).toSubMeas (toProjMeas S.PB y).toSubMeas rfl rfl f g
    (fun a b => accepts F m d x y a b = true) hD).trans (le_of_eq ?_)
  congr 1
  unfold acc
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [born_eq_ev, toProjMeas_outcome]

/-- The point measurement of player B at a coded point, in coarse-grained form. -/
theorem pointMeasB_eq (S : TensorProductStrategy (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    ((toProjStrat S).pointMeasurementB u).toSubMeas =
      postprocess (toProjMeas S.PB (.point (decP u))).toSubMeas codedValue := rfl

/-- The point measurement of player A at a coded point, in coarse-grained form. -/
theorem pointMeasA_eq (S : TensorProductStrategy (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    ((toProjStrat S).pointMeasurementA u).toSubMeas =
      postprocess (toProjMeas S.PA (.point (decP u))).toSubMeas codedValue := rfl

/-- The axis-parallel line measurement of player A evaluated at the coded parameter `0`,
in coarse-grained form. -/
theorem axisMeasA_zero_eq (S : TensorProductStrategy (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    postprocess ((toProjStrat S).axisParallelMeasurementA ⟨u, i⟩).toSubMeas (· zeroCoord) =
      postprocess (toProjMeas S.PA (.axisLine (Line.through (decP u) (Pi.single i 1)))).toSubMeas
        fun a => enc ((axisPolyOf a).eval (decP u i)) := by
  show postprocess (postprocess _ _) _ = _
  rw [MIPStarRE.LDT.SubMeas.postprocess_comp]
  simp only [axisAnswer_zeroCoord]
  rfl

theorem axisMeasB_zero_eq (S : TensorProductStrategy (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    postprocess ((toProjStrat S).axisParallelMeasurementB ⟨u, i⟩).toSubMeas (· zeroCoord) =
      postprocess (toProjMeas S.PB (.axisLine (Line.through (decP u) (Pi.single i 1)))).toSubMeas
        fun a => enc ((axisPolyOf a).eval (decP u i)) := by
  show postprocess (postprocess _ _) _ = _
  rw [MIPStarRE.LDT.SubMeas.postprocess_comp]
  simp only [axisAnswer_zeroCoord]
  rfl

/-- The diagonal line measurement of a player evaluated at the coded parameter `0`, in
coarse-grained form: the line answer is read at the parameter of the base point. -/
theorem diagMeas_zero_eq {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ))
    (ℓ : DiagonalLine (lidtParams F m d)) :
    postprocess (diagMeas P ℓ).toSubMeas (· zeroCoord) =
      postprocess (toProjMeas P (.diagLine (Line.through (decP ℓ.base) (decP ℓ.direction)))).toSubMeas
        fun a => enc ((diagPolyOf a).eval ((Line.through (decP ℓ.base) (decP ℓ.direction)).param
          (decP ℓ.base))) := by
  show postprocess (postprocess _ _) _ = _
  rw [MIPStarRE.LDT.SubMeas.postprocess_comp]
  simp only [diagAnswer_zeroCoord]
  have : (diagData ℓ).1 = (Line.through (decP ℓ.base) (decP ℓ.direction)).param (decP ℓ.base) := by
    rw [Line.param_through]
    unfold diagData
    split_ifs <;> rfl
  rw [this]
  rfl

omit [NeZero m] in
/-- Acceptance for an axis-parallel line question to A and a point question to B. -/
theorem accepts_axisLine_point (ℓ : Line F m) (x : Point F m) (a b : Answer F m d) :
    accepts F m d (.axisLine ℓ) (.point x) a b = true ↔
      ∃ c v, a = .axisPoly c ∧ b = .value v ∧ ℓ.Mem x ∧ c.eval (ℓ.param x) = v := by
  cases a <;> cases b <;> simp [accepts]
  constructor <;> rintro ⟨h1, h2⟩ <;> first | exact ⟨h2.symm, h1⟩ | exact ⟨h2, h1.symm⟩

omit [NeZero m] in
theorem accepts_point_axisLine (ℓ : Line F m) (x : Point F m) (a b : Answer F m d) :
    accepts F m d (.point x) (.axisLine ℓ) a b = true ↔
      ∃ v c, a = .value v ∧ b = .axisPoly c ∧ ℓ.Mem x ∧ c.eval (ℓ.param x) = v := by
  cases a <;> cases b <;> simp [accepts]
  constructor <;> rintro ⟨h1, h2⟩ <;> first | exact ⟨h2.symm, h1⟩ | exact ⟨h2, h1.symm⟩

omit [NeZero m] in
theorem accepts_point_point (x y : Point F m) (a b : Answer F m d) :
    accepts F m d (.point x) (.point y) a b = true ↔
      ∃ v w, a = .value v ∧ b = .value w ∧ x = y ∧ v = w := by
  cases a <;> cases b <;> simp [accepts]
  constructor <;> rintro ⟨h1, h2⟩ <;> first | exact ⟨h2.symm, h1⟩ | exact ⟨h2, h1.symm⟩

omit [NeZero m] in
theorem accepts_diagLine_point (ℓ : Line F m) (x : Point F m) (a b : Answer F m d) :
    accepts F m d (.diagLine ℓ) (.point x) a b = true ↔
      ∃ c v, a = .diagPoly c ∧ b = .value v ∧ ℓ.Mem x ∧ c.eval (ℓ.param x) = v := by
  cases a <;> cases b <;> simp [accepts]
  constructor <;> rintro ⟨h1, h2⟩ <;> first | exact ⟨h2.symm, h1⟩ | exact ⟨h2, h1.symm⟩

omit [NeZero m] in
theorem accepts_point_diagLine (ℓ : Line F m) (x : Point F m) (a b : Answer F m d) :
    accepts F m d (.point x) (.diagLine ℓ) a b = true ↔
      ∃ v c, a = .value v ∧ b = .diagPoly c ∧ ℓ.Mem x ∧ c.eval (ℓ.param x) = v := by
  cases a <;> cases b <;> simp [accepts]
  constructor <;> rintro ⟨h1, h2⟩ <;> first | exact ⟨h2.symm, h1⟩ | exact ⟨h2, h1.symm⟩

/-- Axis-parallel lines test, line to A. -/
theorem axisA_defect_le (S : TensorProductStrategy (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    qBipartiteConsDefect (toProjStrat S).state
      (postprocess ((toProjStrat S).axisParallelMeasurementA ⟨u, i⟩).toSubMeas (· zeroCoord))
      ((toProjStrat S).pointMeasurementB u).toSubMeas ≤
    1 - acc S (.axisLine (Line.through (decP u) (Pi.single i 1))) (.point (decP u)) := by
  rw [axisMeasA_zero_eq, pointMeasB_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨c, v, rfl, rfl, -, hcv⟩ := (accepts_axisLine_point _ _ _ _).mp hab
  rw [Line.param_through_single] at hcv
  simp [axisPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-- Axis-parallel lines test, line to B. -/
theorem axisB_defect_le (S : TensorProductStrategy (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    qBipartiteConsDefect (toProjStrat S).state ((toProjStrat S).pointMeasurementA u).toSubMeas
      (postprocess ((toProjStrat S).axisParallelMeasurementB ⟨u, i⟩).toSubMeas (· zeroCoord)) ≤
    1 - acc S (.point (decP u)) (.axisLine (Line.through (decP u) (Pi.single i 1))) := by
  rw [axisMeasB_zero_eq, pointMeasA_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨v, c, rfl, rfl, -, hcv⟩ := (accepts_point_axisLine _ _ _ _).mp hab
  rw [Line.param_through_single] at hcv
  simp [axisPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-- Self-consistency test. -/
theorem point_defect_le (S : TensorProductStrategy (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    qBipartiteConsDefect (toProjStrat S).state ((toProjStrat S).pointMeasurementA u).toSubMeas
      ((toProjStrat S).pointMeasurementB u).toSubMeas ≤
    1 - acc S (.point (decP u)) (.point (decP u)) := by
  rw [pointMeasA_eq, pointMeasB_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨v, w, rfl, rfl, -, rfl⟩ := (accepts_point_point _ _ _ _).mp hab
  rfl

/-- Diagonal lines test, line to A. -/
theorem diagA_defect_le (S : TensorProductStrategy (lidtGame F m d))
    (ℓ : DiagonalLine (lidtParams F m d)) :
    qBipartiteConsDefect (toProjStrat S).state
      (postprocess ((toProjStrat S).diagonalMeasurementA ℓ).toSubMeas (· zeroCoord))
      ((toProjStrat S).pointMeasurementB ℓ.base).toSubMeas ≤
    1 - acc S (.diagLine (Line.through (decP ℓ.base) (decP ℓ.direction))) (.point (decP ℓ.base)) := by
  rw [show (toProjStrat S).diagonalMeasurementA ℓ = diagMeas S.PA ℓ from rfl, diagMeas_zero_eq,
    pointMeasB_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨c, v, rfl, rfl, -, hcv⟩ := (accepts_diagLine_point _ _ _ _).mp hab
  simp [diagPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-- Diagonal lines test, line to B. -/
theorem diagB_defect_le (S : TensorProductStrategy (lidtGame F m d))
    (ℓ : DiagonalLine (lidtParams F m d)) :
    qBipartiteConsDefect (toProjStrat S).state ((toProjStrat S).pointMeasurementA ℓ.base).toSubMeas
      (postprocess ((toProjStrat S).diagonalMeasurementB ℓ).toSubMeas (· zeroCoord)) ≤
    1 - acc S (.point (decP ℓ.base)) (.diagLine (Line.through (decP ℓ.base) (decP ℓ.direction))) := by
  rw [show (toProjStrat S).diagonalMeasurementB ℓ = diagMeas S.PB ℓ from rfl, diagMeas_zero_eq,
    pointMeasA_eq]
  apply defect_le_rej
  intro a b hab
  obtain ⟨v, c, rfl, rfl, -, hcv⟩ := (accepts_point_diagLine _ _ _ _).mp hab
  simp [diagPolyOf, codedValue, Answer.toValue, eval_ofCoeffs, hcv]

/-- The decoded extension of a restricted direction, as sampled in
`lowIndividualDegreeFailureProbability`. -/
theorem decP_extendLam (j : Fin m) (v : Fin (j.val + 1) → F) :
    decP (fun k : Fin m => if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩)
      else zeroCoord (params := lidtParams F m d)) = Sample.extend v := by
  funext k
  show dec (if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩) else zeroCoord) = _
  unfold Sample.extend
  split_ifs <;> simp

/-! ## The bound -/

/-- Reindexing a sum over coded restricted directions. -/
theorem sum_fin_fun (j : Fin m) (g : (Fin (j.val + 1) → Fq (lidtParams F m d)) → ℝ) :
    ∑ v', g v' = ∑ v : Fin (j.val + 1) → F, g fun k => enc (v k) :=
  ((Equiv.piCongrRight fun _ => scalarEquiv (F := F) (m := m) (d := d)).sum_comp g).symm

/-- The MIPStarRE consistency defect of the branch of a sample of our game. -/
def mdef (S : TensorProductStrategy (lidtGame F m d)) : Sample F m → ℝ
  | .axis false u i => qBipartiteConsDefect (toProjStrat S).state
      (postprocess ((toProjStrat S).axisParallelMeasurementA ⟨encP u, i⟩).toSubMeas (· zeroCoord))
      ((toProjStrat S).pointMeasurementB (encP u)).toSubMeas
  | .axis true u i => qBipartiteConsDefect (toProjStrat S).state
      ((toProjStrat S).pointMeasurementA (encP u)).toSubMeas
      (postprocess ((toProjStrat S).axisParallelMeasurementB ⟨encP u, i⟩).toSubMeas (· zeroCoord))
  | .selfConsistency u => qBipartiteConsDefect (toProjStrat S).state
      ((toProjStrat S).pointMeasurementA (encP u)).toSubMeas
      ((toProjStrat S).pointMeasurementB (encP u)).toSubMeas
  | .diag false u j v => qBipartiteConsDefect (toProjStrat S).state
      (postprocess ((toProjStrat S).diagonalMeasurementA
        ⟨encP u, fun k => if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩) else zeroCoord⟩).toSubMeas (· zeroCoord))
      ((toProjStrat S).pointMeasurementB (encP u)).toSubMeas
  | .diag true u j v => qBipartiteConsDefect (toProjStrat S).state
      ((toProjStrat S).pointMeasurementA (encP u)).toSubMeas
      (postprocess ((toProjStrat S).diagonalMeasurementB
        ⟨encP u, fun k => if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩) else zeroCoord⟩).toSubMeas (· zeroCoord))

/-- Each branch defect is at most the rejection probability of the sample. -/
theorem mdef_le (S : TensorProductStrategy (lidtGame F m d)) (s : Sample F m) :
    mdef S s ≤ 1 - acc S s.questions.1 s.questions.2 := by
  rcases s with ⟨_ | _, u, i⟩ | u | ⟨_ | _, u, j, v⟩
  · simpa [mdef, Sample.questions] using axisA_defect_le S (encP u) i
  · simpa [mdef, Sample.questions] using axisB_defect_le S (encP u) i
  · simpa [mdef, Sample.questions] using point_defect_le S (encP u)
  · have h := diagA_defect_le S ⟨encP u, fun k => if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩) else zeroCoord⟩
    rw [decP_extendLam] at h
    simpa [mdef, Sample.questions] using h
  · have h := diagB_defect_le S ⟨encP u, fun k => if h : k.val ≤ j.val then enc (v ⟨k.val, Nat.lt_succ_of_le h⟩) else zeroCoord⟩
    rw [decP_extendLam] at h
    simpa [mdef, Sample.questions] using h

/-- The MIPStarRE failure probability is the weighted sum of the branch defects over our
samples. -/
theorem failure_eq_sum (S : TensorProductStrategy (lidtGame F m d)) :
    (toProjStrat S).lowIndividualDegreeFailureProbability = ∑ s : Sample F m, s.weight * mdef S s := by
  rw [← Sample.equivSum.symm.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, Sample.equivSum,
    Equiv.coe_fn_symm_mk, Sample.weight, mdef, Fintype.sum_bool]
  unfold ProjStrat.lowIndividualDegreeFailureProbability
  simp only [bipartiteConsError_uniform, Fintype.sum_prod_type, ← pointEquiv.sum_comp,
    sum_fin_fun, pointEquiv_apply, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas]
  conv_rhs => enter [2, 2, 1]; rw [Finset.sum_comm]
  conv_rhs => enter [2, 2, 2]; rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hw : ∀ (j : Fin m) (X : ℝ),
      1 / (6 * (m : ℝ) * (Fintype.card F : ℝ) ^ m * (Fintype.card F : ℝ) ^ (j.val + 1)) * X =
        1 / (6 * (m : ℝ)) * (1 / ((Fintype.card F : ℝ) ^ m * (Fintype.card F : ℝ) ^ (j.val + 1)) * X) := by
    intro j X
    field_simp
  simp only [hw, ← Finset.mul_sum]
  ring

/-- The MIPStarRE failure probability of the induced strategy is at most the rejection
probability of the strategy in the game. -/
theorem failure_le (S : TensorProductStrategy (lidtGame F m d)) :
    (toProjStrat S).lowIndividualDegreeFailureProbability ≤ 1 - S.value := by
  rw [failure_eq_sum, one_sub_value]
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (mdef_le S s) s.weight_nonneg

end MIPRE.LIDT.Bridge

end
