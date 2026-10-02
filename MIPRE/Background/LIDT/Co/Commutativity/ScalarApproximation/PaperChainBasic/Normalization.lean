/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Products
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.Core

@[expose] public section

/-!
# Section 11 commutativity: normalization helpers for the evaluated-slice paper chain

The normalization estimates `∑ C C^* ≤ 1` and `∑ C^* C ≤ 1` used as side conditions of
`closenessOfIP` and its adjoint form in the scalar approximation chain: the counterpart of
`Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

The vendored `leftTensor (ι₂ := ι)` and `rightTensor (ι₁ := ι)` are the placements `S.L` and
`S.R` of a symmetric model, so each normalization lemma takes `S : SymModel 𝔓 K` as an explicit
first argument, as M3's placement lemmas do (`planning/c6b-plan.md`, "Departures in M3 and M5").
`projSubMeas_total_mul_outcome_eq_outcome` does not mention the state and holds in any
C*-algebra with its order.

The vendored proofs expand `(∑_b L(X_b) R(P_b)) (∑_b L(X_b) R(P_b))^*` twice, in a calc of
Kronecker identities each time, and bound every summand separately. Here the expansion is one
private lemma for each order of the product (the cross terms vanish because the outcomes of the
projective measurement `P` are orthogonal), and a third private lemma reduces
`∑_a ∑_b L(Y_{a,b}) R(P_b) ≤ 1` to the local bounds `∑_a Y_{a,b} ≤ 1`, which are proved in `𝔓`
from three private inequalities of a C*-algebra: `c Y c ≤ c c` for self-adjoint `c` and `Y ≤ 1`,
`X X ≤ 1` for `0 ≤ X ≤ 1`, and `∑_a A_a A_a ≤ 1` for a submeasurement `A`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

section Local

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]

/-- The total projector of a projective submeasurement absorbs each outcome on the left. -/
lemma projSubMeas_total_mul_outcome_eq_outcome
    {α : Type*} [Fintype α] (A : ProjSubMeas α R) (a : α) :
    A.total * A.outcome a = A.outcome a := by
  have h := congrArg star (Preliminaries.projSubMeas_outcome_mul_total_eq_outcome A a)
  rwa [star_mul, A.outcome_hermitian, (IsSelfAdjoint.of_nonneg A.total_nonneg).star_eq] at h

/-- A conjugate `c Y c` of a contraction `Y ≤ 1` by a self-adjoint `c` is at most `c c`. -/
private theorem conj_le_mul_self {c Y : R} (hc : IsSelfAdjoint c) (hY : Y ≤ 1) :
    c * Y * c ≤ c * c :=
  (hc.conjugate_le_conjugate hY).trans_eq (by rw [mul_one])

/-- An operator between `0` and `1` has square at most `1`. -/
private theorem mul_self_le_one {X : R} (h0 : 0 ≤ X) (h1 : X ≤ 1) : X * X ≤ 1 :=
  (sq_le_self h0 h1).trans h1

/-- The squares of the outcomes of a submeasurement sum to at most `1`. -/
private theorem sum_mul_self_le_one {α : Type*} [Fintype α] (A : SubMeas α R) :
    ∑ a : α, A.outcome a * A.outcome a ≤ 1 :=
  (Finset.sum_le_sum fun a _ => sq_le_self (A.outcome_pos a) (A.outcome_le_one a)).trans
    (A.sum_eq_total.le.trans A.total_le_one)

end Local

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Against the orthogonal outcomes of a projective measurement on the right, the cross terms
of `(∑_b L(X_b) R(P_b)) (∑_b L(X_b) R(P_b))^*` vanish. -/
private theorem sum_L_mul_R_mul_star (S : SymModel 𝔓 K) {β : Type*} [Fintype β]
    (X : β → 𝔓) (P : ProjMeas β 𝔓) :
    (∑ b : β, S.L (X b) * S.R (P.outcome b)) * star (∑ b : β, S.L (X b) * S.R (P.outcome b)) =
      ∑ b : β, S.L (X b * star (X b)) * S.R (P.outcome b) := by
  classical
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b]
  · change S.opTensor _ _ * star (S.opTensor _ _) = S.opTensor _ _
    rw [S.conjTranspose_opTensor, S.opTensor_mul, P.outcome_hermitian, P.proj]
  · intro c _ hcb
    change S.opTensor _ _ * star (S.opTensor _ _) = 0
    rw [S.conjTranspose_opTensor, S.opTensor_mul, P.outcome_hermitian,
      P.outcome_orthogonal b c (Ne.symm hcb), SymModel.opTensor, map_zero, mul_zero]
  · exact fun h => absurd (Finset.mem_univ b) h

/-- Adjoint-side form of `sum_L_mul_R_mul_star`. -/
private theorem star_sum_L_mul_R_mul (S : SymModel 𝔓 K) {β : Type*} [Fintype β]
    (X : β → 𝔓) (P : ProjMeas β 𝔓) :
    star (∑ b : β, S.L (X b) * S.R (P.outcome b)) * (∑ b : β, S.L (X b) * S.R (P.outcome b)) =
      ∑ b : β, S.L (star (X b) * X b) * S.R (P.outcome b) := by
  classical
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b]
  · change star (S.opTensor _ _) * S.opTensor _ _ = S.opTensor _ _
    rw [S.conjTranspose_opTensor, S.opTensor_mul, P.outcome_hermitian, P.proj]
  · intro c _ hcb
    change star (S.opTensor _ _) * S.opTensor _ _ = 0
    rw [S.conjTranspose_opTensor, S.opTensor_mul, P.outcome_hermitian,
      P.outcome_orthogonal b c (Ne.symm hcb), SymModel.opTensor, map_zero, mul_zero]
  · exact fun h => absurd (Finset.mem_univ b) h

/-- If `∑_a Y_{a,b} ≤ 1` for every `b`, then `∑_a ∑_b L(Y_{a,b}) R(P_b) ≤ 1` for a projective
measurement `P`. -/
private theorem sum_sum_L_mul_R_le_one (S : SymModel 𝔓 K) {α β : Type*} [Fintype α]
    [Fintype β] (Y : α → β → 𝔓) (P : ProjMeas β 𝔓) (hY : ∀ b, ∑ a : α, Y a b ≤ 1) :
    ∑ a : α, ∑ b : β, S.L (Y a b) * S.R (P.outcome b) ≤ 1 := by
  rw [Finset.sum_comm]
  calc
    ∑ b : β, ∑ a : α, S.L (Y a b) * S.R (P.outcome b)
        = ∑ b : β, S.opTensor (∑ a : α, Y a b) (P.outcome b) :=
          Finset.sum_congr rfl fun b _ => (S.opTensor_sum_left_univ _ _).symm
    _ ≤ ∑ b : β, S.opTensor 1 (P.outcome b) :=
          Finset.sum_le_sum fun b _ => S.opTensor_mono_left (hY b) (P.outcome_pos b)
    _ = 1 := by
          rw [← S.opTensor_sum_right_univ, P.sum_eq, SymModel.opTensor, S.leftTensor_one,
            S.rightTensor_one, one_mul]

/-- Normalization side condition for the paper line-86 insertion.

For fixed evaluated-slice question `q`, this bounds the `closenessOfIP` family
`C_{a,b} = (A_a B_b) \otimes P_b`, where `P` is a projective point
measurement. -/
lemma leftRightTensor_prefix_pointMeasurement_normalization
    (S : SymModel 𝔓 K)
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) (R : ProjMeas β 𝔓) :
    ∑ a : α,
        (∑ b : β, S.L (A.outcome a * B.outcome b) * S.R (R.outcome b)) *
        star (∑ b : β, S.L (A.outcome a * B.outcome b) * S.R (R.outcome b)) ≤
      1 := by
  simp only [sum_L_mul_R_mul_star S _ R]
  refine sum_sum_L_mul_R_le_one S _ R fun b => ?_
  calc
    ∑ a : α, A.outcome a * B.outcome b * star (A.outcome a * B.outcome b)
        = ∑ a : α, A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
          simp only [star_mul, A.outcome_hermitian, B.outcome_hermitian, mul_assoc]
    _ ≤ ∑ a : α, A.outcome a * A.outcome a :=
          Finset.sum_le_sum fun a _ => conj_le_mul_self (.of_nonneg (A.outcome_pos a))
            (mul_self_le_one (B.outcome_pos b) (B.outcome_le_one b))
    _ ≤ 1 := sum_mul_self_le_one A

/-- Adjoint-side normalization for
`C_{a,b} = (A_a B_b) \otimes R_b`.

This is the side condition needed by `closenessOfIPAdjoint` for the first
reverse `eq:add-an-a` move after paper `eq:gcom10`. -/
lemma leftRightTensor_prefix_pointMeasurement_adjoint_normalization
    (S : SymModel 𝔓 K)
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) (R : ProjMeas β 𝔓) :
    ∑ a : α,
        star (∑ b : β, S.L (A.outcome a * B.outcome b) * S.R (R.outcome b)) *
        (∑ b : β, S.L (A.outcome a * B.outcome b) * S.R (R.outcome b)) ≤
      1 := by
  simp only [star_sum_L_mul_R_mul S _ R]
  refine sum_sum_L_mul_R_le_one S _ R fun b => ?_
  calc
    ∑ a : α, star (A.outcome a * B.outcome b) * (A.outcome a * B.outcome b)
        = B.outcome b * (∑ a : α, A.outcome a * A.outcome a) * B.outcome b := by
          simp only [star_mul, A.outcome_hermitian, B.outcome_hermitian, Finset.mul_sum,
            Finset.sum_mul, mul_assoc]
    _ ≤ B.outcome b * B.outcome b :=
          conj_le_mul_self (.of_nonneg (B.outcome_pos b)) (sum_mul_self_le_one A)
    _ ≤ 1 := mul_self_le_one (B.outcome_pos b) (B.outcome_le_one b)

/-- Normalization for `C_{b,a}=A_a B_b` placed on the left tensor factor. -/
lemma leftTensor_pair_prefix_normalization
    (S : SymModel 𝔓 K)
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) :
    ∑ b : β,
        (∑ a : α, S.L (A.outcome a * B.outcome b)) *
        star (∑ a : α, S.L (A.outcome a * B.outcome b)) ≤
      1 := by
  simp only [← Finset.sum_mul, S.leftTensor_finset_sum, A.sum_eq_total,
    S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  refine S.leftTensor_le_one ?_
  calc
    ∑ b : β, A.total * B.outcome b * star (A.total * B.outcome b)
        = A.total * (∑ b : β, B.outcome b * B.outcome b) * A.total := by
          simp only [star_mul, B.outcome_hermitian,
            (IsSelfAdjoint.of_nonneg A.total_nonneg).star_eq, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
    _ ≤ A.total * A.total :=
          conj_le_mul_self (.of_nonneg A.total_nonneg) (sum_mul_self_le_one B)
    _ ≤ 1 := mul_self_le_one A.total_nonneg A.total_le_one

/-- Adjoint-side version of `leftTensor_pair_prefix_normalization`. -/
lemma leftTensor_pair_prefix_adjoint_normalization
    (S : SymModel 𝔓 K)
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) :
    ∑ b : β,
        star (∑ a : α, S.L (A.outcome a * B.outcome b)) *
        (∑ a : α, S.L (A.outcome a * B.outcome b)) ≤
      1 := by
  simp only [← Finset.sum_mul, S.leftTensor_finset_sum, A.sum_eq_total,
    S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  refine S.leftTensor_le_one ?_
  calc
    ∑ b : β, star (A.total * B.outcome b) * (A.total * B.outcome b)
        = ∑ b : β, B.outcome b * (A.total * A.total) * B.outcome b := by
          simp only [star_mul, B.outcome_hermitian,
            (IsSelfAdjoint.of_nonneg A.total_nonneg).star_eq, mul_assoc]
    _ ≤ ∑ b : β, B.outcome b * B.outcome b :=
          Finset.sum_le_sum fun b _ => conj_le_mul_self (.of_nonneg (B.outcome_pos b))
            (mul_self_le_one A.total_nonneg A.total_le_one)
    _ ≤ 1 := sum_mul_self_le_one B

/-- Normalization side condition for the paper line-87 right-register point swap.

For fixed evaluated-slice question `q`, the swap uses the family
`C_{a,b} = (G^{u,x}_a G^{v,y}_b G^x) \otimes I`, represented here as a
left tensor.  The estimate only needs that the two evaluated-slice factors are
submeasurements and that the inserted total `T` is a positive contraction. -/
lemma leftTensor_prefix_total_normalization
    (S : SymModel 𝔓 K)
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓)
    (T : 𝔓)
    (hT_nonneg : 0 ≤ T) (hT_le_one : T ≤ 1) :
    ∑ ab : α × β,
        S.L (A.outcome ab.1 * B.outcome ab.2 * T) *
          star (S.L (A.outcome ab.1 * B.outcome ab.2 * T)) ≤
      1 := by
  simp only [S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor, S.leftTensor_finset_sum]
  refine S.leftTensor_le_one ?_
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_le_sum fun a _ => ?_).trans (sum_mul_self_le_one A)
  calc
    ∑ b : β, A.outcome a * B.outcome b * T * star (A.outcome a * B.outcome b * T)
        = ∑ b : β, A.outcome a * (B.outcome b * (T * T) * B.outcome b) * A.outcome a := by
          simp only [star_mul, A.outcome_hermitian, B.outcome_hermitian,
            (IsSelfAdjoint.of_nonneg hT_nonneg).star_eq, mul_assoc]
    _ ≤ ∑ b : β, A.outcome a * (B.outcome b * B.outcome b) * A.outcome a :=
          Finset.sum_le_sum fun b _ =>
            (IsSelfAdjoint.of_nonneg (A.outcome_pos a)).conjugate_le_conjugate
              (conj_le_mul_self (.of_nonneg (B.outcome_pos b))
                (mul_self_le_one hT_nonneg hT_le_one))
    _ = A.outcome a * (∑ b : β, B.outcome b * B.outcome b) * A.outcome a := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ A.outcome a * A.outcome a :=
          conj_le_mul_self (.of_nonneg (A.outcome_pos a)) (sum_mul_self_le_one B)

end MIPRE.LIDT.Co.Commutativity

end
