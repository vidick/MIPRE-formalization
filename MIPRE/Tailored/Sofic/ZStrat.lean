/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Assoc
public import MIPRE.Tailored.Data.Bridge
public import MIPRE.Tactics

@[expose] public section

/-!
# Z-aligned permutation strategies, without commutation along edges

A *Z-aligned permutation strategy* of a tailored game (paper I, Definition I:2026; paper II,
II:1056) is a `TailoredGameValue.PermStrategy` without its field `commEdges`: one signed
permutation matrix per formal variable, involutions commuting at each vertex, the identity
beyond `ℓ(x)`, and diagonal on the readable variables. Paper I's Proposition I:2279 produces
such a strategy from an action passing Checks 1–3 of the associated test, and the commutation
along edges plays no part there, nor in the value.

* `ZStrat`, `ZStrat.proj`, `ZStrat.value`: the strategy, its Fourier measurements and its value,
  spelled as `PermStrategy`'s.
* `ZStrat.toSync`, `ZStrat.value_toSync`, `ZStrat.value_le_gameValue`: it is a synchronous
  strategy with the same value, so its value bounds the synchronous value from below, as
  `Data/Bridge.lean` shows for `PermStrategy`, whose proof never uses `commEdges`.
* `ZStrat.value_eq_sum_rej`: the value is `∑ μ(x, y) (1 - rej(x, y))`, with `rej(x, y)` the
  probability of a rejected answer pair at `(x, y)`.
* `ZStrat.proj_eq_zero_of_not_wellFormatted`, `ZStrat.proj_mul_proj_of_ne`: malformed answers
  have zero projection, and distinct answers at one vertex orthogonal projections.
-/

namespace MIPRE.Tailored.Sofic

open TailoredGameValue

/-- **A Z-aligned permutation strategy** for a tailored game: `PermStrategy` without the
commutation along edges. -/
structure ZStrat (g : TailoredGameData) where
  /-- The dimension. -/
  m : ℕ
  m_pos : 0 < m
  /-- The observables. -/
  U : Fin (g.nV + 1) → Fin g.ansLen → Matrix (Fin m) (Fin m) ℂ
  signedPerm : ∀ x i, IsSignedPerm (U x i)
  invol : ∀ x i, U x i * U x i = 1
  comm : ∀ x i j, U x i * U x j = U x j * U x i
  pad : ∀ x (i : Fin g.ansLen), g.lenAt x.val ≤ i.val → U x i = 1
  zAligned : ∀ x (i : Fin g.ansLen), i.val < g.lenRAt x.val → (U x i).IsDiag

namespace ZStrat

variable {g : TailoredGameData} (S : ZStrat g)

/-- The measurement at `x`, the Fourier transform of the observables. -/
noncomputable def proj (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    Matrix (Fin S.m) (Fin S.m) ℂ :=
  fourierProj (S.U x) a

/-- The value, spelled as `PermStrategy.value`. -/
noncomputable def value : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    g.toGame.μ x y * (if g.toGame.D x y a b then 1 else 0) *
      ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ))

theorem commute_U (x : Fin (g.nV + 1)) (i j : Fin g.ansLen) : Commute (S.U x i) (S.U x j) :=
  S.comm x i j

/-- The observables are self-adjoint. -/
theorem star_U (x : Fin (g.nV + 1)) (i : Fin g.ansLen) : star (S.U x i) = S.U x i :=
  ((S.signedPerm x i).isHermitian (S.invol x i)).eq

/-- The measurements are projective. -/
theorem isPVMIn_proj (x : Fin (g.nV + 1)) : MIPRE.IsPVMIn (S.proj x) :=
  isPVMIn_fourierProj (S.invol x) (S.star_U x) (S.commute_U x)

/-- **A Z-aligned permutation strategy is a synchronous strategy.** -/
noncomputable def toSync : MIPRE.SyncStrategy g.syncGame where
  d := S.m
  d_pos := S.m_pos
  P :=
    { M := S.proj
      selfAdjoint := fun x a => (S.isPVMIn_proj x).star_eq a
      projective := fun x a => (S.isPVMIn_proj x).idem a
      normalized := fun x => (S.isPVMIn_proj x).sum_eq_one }

/-- **It has the same value.** -/
theorem value_toSync : S.toSync.value = S.value := by
  rw [MIPRE.SyncStrategy.value_eq]
  rfl

/-- **The value of a Z-aligned permutation strategy is at most the synchronous value.** -/
theorem value_le_gameValue : S.value ≤ HaltingGameValue.gameValue g.toGame := by
  rw [g.toGame.gameValue_eq_syncValue, ← S.value_toSync]
  exact le_ciSup (MIPRE.SyncStrategy.bddAbove_range_value _) S.toSync

/-! ## Elementary facts about the measurements -/

/-- `P_a` lies in the `(-1)^{a_i}`-eigenspace of `U x i`. -/
theorem U_mul_proj (x : Fin (g.nV + 1)) (i : Fin g.ansLen) (a : Fin g.ansLen → Bool) :
    S.U x i * S.proj x a = bitSign (a i) • S.proj x a :=
  mul_fourierProj (S.invol x) (S.commute_U x) i a

theorem commute_U_proj (x : Fin (g.nV + 1)) (i : Fin g.ansLen) (a : Fin g.ansLen → Bool) :
    Commute (S.U x i) (S.proj x a) :=
  Commute.fourierProj_right (fun j => S.commute_U x i j) a

theorem proj_mul_U (x : Fin (g.nV + 1)) (i : Fin g.ansLen) (a : Fin g.ansLen → Bool) :
    S.proj x a * S.U x i = bitSign (a i) • S.proj x a := by
  rw [← (S.commute_U_proj x i a).eq, S.U_mul_proj]

/-- **Malformed answers have zero projection**: the padded observables are the identity. -/
theorem proj_eq_zero_of_not_wellFormatted (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool)
    (h : ¬g.WellFormatted x a) : S.proj x a = 0 := by
  simp only [TailoredGameData.WellFormatted, not_forall, Bool.not_eq_false] at h
  obtain ⟨i, hi, ha⟩ := h
  have h1 := S.U_mul_proj x i a
  rw [S.pad x i hi, one_mul, ha, bitSign_true, neg_one_smul] at h1
  have h2 : (2 : ℂ) • S.proj x a = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Distinct answers at one vertex have orthogonal projections. -/
theorem proj_mul_proj_of_ne (x : Fin (g.nV + 1)) {a b : Fin g.ansLen → Bool} (h : a ≠ b) :
    S.proj x a * S.proj x b = 0 :=
  (S.isPVMIn_proj x).orthogonal h

theorem star_proj (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    star (S.proj x a) = S.proj x a :=
  (S.isPVMIn_proj x).star_eq a

open Matrix ComplexOrder in
/-- `Tr(P_a Q_b) ≥ 0`. -/
theorem re_trace_proj_mul_proj_nonneg (x y : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool) :
    0 ≤ (S.proj x a * S.proj y b).trace.re := by
  set P := S.proj x a
  set Q := S.proj y b
  have hP : Pᴴ = P := S.star_proj x a
  have hQ : Qᴴ = Q := S.star_proj y b
  have hPP : P * P = P := (S.isPVMIn_proj x).idem a
  have hQQ : Q * Q = Q := (S.isPVMIn_proj y).idem b
  have h : ((P * Q)ᴴ * (P * Q)).trace = (P * Q).trace := by
    rw [conjTranspose_mul, hP, hQ]
    calc (Q * P * (P * Q)).trace = (Q * ((P * P) * Q)).trace := by simp only [Matrix.mul_assoc]
      _ = ((P * Q) * Q).trace := by rw [hPP, trace_mul_comm]
      _ = (P * Q).trace := by rw [Matrix.mul_assoc, hQQ]
  rw [← h]
  exact (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self (P * Q)).trace_nonneg).1

/-- `∑_{a, b} Tr(P_a Q_b) = m`. -/
theorem sum_trace_proj_mul_proj (x y : Fin (g.nV + 1)) :
    ∑ a, ∑ b, (S.proj x a * S.proj y b).trace = S.m := by
  have h : ∀ a, ∑ b, (S.proj x a * S.proj y b).trace = (S.proj x a).trace := fun a => by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, (S.isPVMIn_proj y).sum_eq_one, Matrix.mul_one]
  simp_rw [h]
  rw [← Matrix.trace_sum, (S.isPVMIn_proj x).sum_eq_one, Matrix.trace_one, Fintype.card_fin]

/-- The probability of a rejected answer pair at `(x, y)`. -/
noncomputable def rej (x y : Fin (g.nV + 1)) : ℝ :=
  ∑ a, ∑ b, (if g.Accepts x y a b then 0 else 1) *
    ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ))

theorem rej_nonneg (x y : Fin (g.nV + 1)) : 0 ≤ S.rej x y := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  refine mul_nonneg (by split_ifs <;> norm_num) ?_
  exact div_nonneg (S.re_trace_proj_mul_proj_nonneg x y a b) (Nat.cast_nonneg _)

/-- **The value as one minus the rejection probability.** -/
theorem value_eq_sum_rej :
    S.value = ∑ x, ∑ y, g.toGame.μ x y * (1 - S.rej x y) := by
  have hm : (S.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr S.m_pos.ne'
  have hone : ∀ x y : Fin (g.nV + 1),
      ∑ a, ∑ b, (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) = 1 := by
    intro x y
    have h := congrArg Complex.re (S.sum_trace_proj_mul_proj x y)
    simp only [Complex.re_sum, Complex.natCast_re] at h
    simp_rw [← Finset.sum_div, h, div_self hm]
  have hacc : ∀ x y : Fin (g.nV + 1), ∑ a, ∑ b, (if g.toGame.D x y a b then (1 : ℝ) else 0) *
      ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ)) = 1 - S.rej x y := by
    intro x y
    have hsplit : ∑ a, ∑ b, (if g.toGame.D x y a b then (1 : ℝ) else 0) *
        ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ)) + S.rej x y =
        ∑ a, ∑ b, (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) := by
      rw [rej, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hD : g.toGame.D x y a b = decide (g.Accepts x y a b) := rfl
      rw [hD]
      by_cases h : g.Accepts x y a b <;> simp [h]
    linarith [hone x y]
  unfold value
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← hacc x y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end ZStrat

/-- A permutation strategy, forgetting the commutation along edges. -/
def _root_.TailoredGameValue.PermStrategy.toZStrat {g : TailoredGameData} (S : TailoredGameValue.PermStrategy g) :
    ZStrat g where
  m := S.m
  m_pos := S.m_pos
  U := S.U
  signedPerm := S.signedPerm
  invol := S.invol
  comm := S.comm
  pad := S.pad
  zAligned := S.zAligned

theorem _root_.TailoredGameValue.PermStrategy.value_toZStrat {g : TailoredGameData}
    (S : TailoredGameValue.PermStrategy g) : S.toZStrat.value = S.value := rfl

end MIPRE.Tailored.Sofic

end
