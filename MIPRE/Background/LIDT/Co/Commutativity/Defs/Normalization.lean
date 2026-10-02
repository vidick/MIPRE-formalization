/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Defs/Normalization.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Defs.Stability

@[expose] public section

/-!
# Section 11 commutativity: normalization definitions

The normalization-condition sandwich `C_{a,b} = Q_b P_a Q_b` and the associated indexed
submeasurement family used in `lem:normalization-condition`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Defs/Normalization.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

Nothing here reads a state: every declaration is about local operators, and is stated over any
C*-algebra `𝔓` with its order (the vendored `Op ι`). The vendored positive-semidefinite-matrix
steps become the C*-algebra facts `mul_star_self_nonneg`, `star_mul_self_nonneg` and
`IsSelfAdjoint.of_nonneg`, and `sq_le_self` is the keystone's (`Co/Basic/QuantumState.lean`).
The private `proj_conj_le` (`Q_b X Q_b ≤ Q_b` for `X ≤ 1`) is the step the two vendored sum
bounds repeat inline.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]

/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓)
    (a : OutcomeA) (b : OutcomeB) : 𝔓 :=
  Q.outcome b * P.outcome a * Q.outcome b

/-- A projection `Q_b` conjugating an effect bounded by `X ≤ 1` gives at most `Q_b`. -/
private theorem proj_conj_le {OutcomeB : Type*} [Fintype OutcomeB]
    (Q : ProjSubMeas OutcomeB 𝔓) (b : OutcomeB) {X : 𝔓} (hX : X ≤ 1) :
    Q.outcome b * X * Q.outcome b ≤ Q.outcome b :=
  (IsSelfAdjoint.conjugate_le_conjugate hX (Q.outcome_hermitian b)).trans_eq
    (by rw [mul_one, Q.proj b])

/-- The sandwiched operators sum to at most the identity. -/
theorem normalizationConditionSandwichedOperator_sum_le_one
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) (a : OutcomeA) :
    ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b ≤ 1 :=
  calc
    ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
      ≤ ∑ b : OutcomeB, Q.outcome b :=
        Finset.sum_le_sum fun b _ => proj_conj_le Q b (P.outcome_le_one a)
    _ = Q.total := Q.sum_eq_total
    _ ≤ 1 := Q.total_le_one

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
noncomputable def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) :
    IdxSubMeas OutcomeA OutcomeB 𝔓 :=
  fun a =>
    { outcome := fun b => normalizationConditionSandwichedOperator P Q a b
      total := ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
      outcome_pos := fun b =>
        IsSelfAdjoint.conjugate_nonneg (P.outcome_pos a) (Q.outcome_hermitian b)
      sum_eq_total := rfl
      total_le_one := normalizationConditionSandwichedOperator_sum_le_one P Q a }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) :
    IdxSubMeas OutcomeA Unit 𝔓 :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓)
    (a : OutcomeA) : 𝔓 :=
  (normalizationConditionSandwichedTotalFamily P Q a).total

/-- Operators below the totals `∑_b C_{a,b}` sum to at most the identity. -/
theorem normalizationConditionSandwichedTotalSum_le_one
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓)
    {F : OutcomeA → 𝔓}
    (hF : ∀ a, F a ≤ normalizationConditionSandwichedTotalOperator P Q a) :
    ∑ a : OutcomeA, F a ≤ 1 :=
  calc
    ∑ a : OutcomeA, F a
      ≤ ∑ a : OutcomeA, normalizationConditionSandwichedTotalOperator P Q a :=
        Finset.sum_le_sum fun a _ => hF a
    _ = ∑ a : OutcomeA, ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b := rfl
    _ = ∑ b : OutcomeB, ∑ a : OutcomeA, normalizationConditionSandwichedOperator P Q a b :=
        Finset.sum_comm
    _ = ∑ b : OutcomeB, Q.outcome b * P.total * Q.outcome b :=
        Finset.sum_congr rfl fun b _ => by
          simp only [normalizationConditionSandwichedOperator]
          rw [← Finset.sum_mul, ← Finset.mul_sum, P.sum_eq_total]
    _ ≤ ∑ b : OutcomeB, Q.outcome b :=
        Finset.sum_le_sum fun b _ => proj_conj_le Q b P.total_le_one
    _ = Q.total := Q.sum_eq_total
    _ ≤ 1 := Q.total_le_one

/-- The total `∑_b C_{a,b}` is self-adjoint. -/
theorem normalizationConditionSandwichedTotalOperator_hermitian
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) (a : OutcomeA) :
    star (normalizationConditionSandwichedTotalOperator P Q a) =
      normalizationConditionSandwichedTotalOperator P Q a :=
  (IsSelfAdjoint.of_nonneg
    (SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a))).star_eq

/-- The total `∑_b C_{a,b}` dominates its square. -/
theorem normCondSandwichedTotal_sq_le
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) (a : OutcomeA) :
    normalizationConditionSandwichedTotalOperator P Q a *
        normalizationConditionSandwichedTotalOperator P Q a ≤
      normalizationConditionSandwichedTotalOperator P Q a :=
  sq_le_self (SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a))
    (normalizationConditionSandwichedTotalFamily P Q a).total_le_one

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) :
    SubMeas OutcomeA 𝔓 where
  outcome := fun a =>
    normalizationConditionSandwichedTotalOperator P Q a *
      star (normalizationConditionSandwichedTotalOperator P Q a)
  total :=
    ∑ a : OutcomeA,
      normalizationConditionSandwichedTotalOperator P Q a *
        star (normalizationConditionSandwichedTotalOperator P Q a)
  outcome_pos := fun _ => mul_star_self_nonneg _
  sum_eq_total := rfl
  total_le_one := normalizationConditionSandwichedTotalSum_le_one P Q fun a =>
    (congrArg (_ * ·) (normalizationConditionSandwichedTotalOperator_hermitian P Q a)).trans_le
      (normCondSandwichedTotal_sq_le P Q a)

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) :
    SubMeas OutcomeA 𝔓 where
  outcome := fun a =>
    star (normalizationConditionSandwichedTotalOperator P Q a) *
      normalizationConditionSandwichedTotalOperator P Q a
  total :=
    ∑ a : OutcomeA,
      star (normalizationConditionSandwichedTotalOperator P Q a) *
        normalizationConditionSandwichedTotalOperator P Q a
  outcome_pos := fun _ => star_mul_self_nonneg _
  sum_eq_total := rfl
  total_le_one := normalizationConditionSandwichedTotalSum_le_one P Q fun a =>
    (congrArg (· * _) (normalizationConditionSandwichedTotalOperator_hermitian P Q a)).trans_le
      (normCondSandwichedTotal_sq_le P Q a)

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) : 𝔓 :=
  (normalizationConditionSquareFamily P Q).total

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓) (Q : ProjSubMeas OutcomeB 𝔓) : 𝔓 :=
  (normalizationConditionAdjointSquareFamily P Q).total

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (_P : SubMeas OutcomeA 𝔓) (_Q : ProjSubMeas OutcomeB 𝔓) : 𝔓 :=
  1

end MIPRE.LIDT.Co.Commutativity

end
