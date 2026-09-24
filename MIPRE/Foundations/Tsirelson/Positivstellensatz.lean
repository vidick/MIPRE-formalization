/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Tsirelson.Algebra

/-!
# The Positivstellensatz for the commuting-operator value

Step §3.4 of the Tsirelson route (`planning/tsirelson-campaign.md`): every strict upper bound on
the commuting-operator value of a game has a certificate in the cone of the game algebra,

  `commutingOperatorValue G < r  →  r·1 - W_G ∈ M`,

where `W_G = gamePoly G = Σ μ(x, y) [D x y a b] e_xa f_yb` and `M = cone X Y A B`
(`sub_gamePoly_mem_cone_of_lt`). Together with the soundness of cone certificates
(`value_le_of_mem`) this says that the commuting-operator value is the infimum of the cone
certificates (`isGLB_commutingOperatorValue`); strict bounds are exactly those with a
certificate at a smaller level (`commutingOperatorValue_lt_iff`).

**Proof.** Suppose `h := r·1 - W_G ∉ M`. The cone is Archimedean, so a real functional `L₀` that
is `1` at the unit, nonnegative on `M` and `≤ 0` at `h` separates `h` from it; its
complexification `L z := L₀ z - i L₀ (i z)` is a cone state with `Re L h = L₀ h ≤ 0`
(`exists_isConeState_of_not_mem`). The GNS construction turns `L` into a commuting-operator
strategy of value `Re L (W_G) ≥ r` (`re_gamePoly_le_commutingOperatorValue`), which contradicts
`commutingOperatorValue G < r`.

**Hypotheses.** The implication needs nothing beyond finiteness of the alphabets. Its converse
needs a little more, because an empty answer set makes the cone degenerate: if `A` is empty and
`X` is not, `-1 = Σ_a e_xa - 1` is a relation, so every polynomial lies in `M`, while there is no
strategy and the value is `0`. Then `r'·1 - W_G ∈ M` for `r' = -2`, but the value is not below
`r = -1`. The converse is therefore stated twice: for nonempty answer sets, where the
deterministic strategy makes the supremum defining the value a supremum over a nonempty set
(`commutingOperatorValue_le_of_mem_of_nonempty`, `commutingOperatorValue_lt_iff`,
`isGLB_commutingOperatorValue`), and for `0 < r` with no condition on the alphabets
(`commutingOperatorValue_lt_iff_of_pos`).

Everything is stated for `X Y A B : Type`, since the GNS strategy's Hilbert space lives in the
universe of the generators and `CommutingOperatorStrategy.H : Type`.

## Main declarations

* `sub_gamePoly_mem_cone_of_lt`: the Positivstellensatz;
* `commutingOperatorValue_le_of_mem_of_nonempty`: soundness of a certificate at any level, for
  nonempty answer sets;
* `commutingOperatorValue_lt_iff`, `commutingOperatorValue_lt_iff_of_pos`: strict upper bounds
  are exactly those with a certificate below them;
* `isGLB_commutingOperatorValue`: the commuting-operator value is the greatest lower bound of the
  certificate levels.
-/

noncomputable section

namespace MIPRE

namespace Tsirelson

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A cone state takes the value `r - Re L (W_G)` at `r·1 - W_G`, in real part. -/
private theorem re_map_smul_one_sub_gamePoly {L : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ}
    (hL : IsConeState L) (G : Game X Y A B) (r : ℝ) :
    (L (r • (1 : NCPoly (Gen X Y A B)) - gamePoly G)).re = r - (L (gamePoly G)).re := by
  have hr : r • (1 : NCPoly (Gen X Y A B)) = ((r : ℝ) : ℂ) • 1 := rfl
  rw [hr, map_sub, map_smul, hL.map_one, smul_eq_mul, mul_one, Complex.sub_re,
    Complex.ofReal_re]

/-- **The Positivstellensatz for the commuting-operator value.** Every strict upper bound `r` on
the commuting-operator value of a game has a cone certificate: `r·1 - W_G ∈ M`. A polynomial
outside the cone is separated from it by a cone state, whose GNS strategy would have value at
least `r`. -/
theorem sub_gamePoly_mem_cone_of_lt (G : Game X Y A B) {r : ℝ}
    (h : commutingOperatorValue G < r) :
    r • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B := by
  by_contra hh
  obtain ⟨L, hL, hLh⟩ := exists_isConeState_of_not_mem hh
  rw [re_map_smul_one_sub_gamePoly hL G r] at hLh
  have hW := re_gamePoly_le_commutingOperatorValue hL G
  linarith

/-- **Soundness of a cone certificate, for nonempty answer sets**: `r·1 - W_G ∈ M` bounds the
commuting-operator value by `r`, for every real `r`. Nonemptiness of `A` and `B` provides a
strategy (`CommutingOperatorStrategy.instNonempty`), which the supremum needs (`ciSup_le`); the
sign condition of `commutingOperatorValue_le_of_mem` is then unnecessary. -/
theorem commutingOperatorValue_le_of_mem_of_nonempty [Nonempty A] [Nonempty B]
    (G : Game X Y A B) {r : ℝ}
    (h : r • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B) :
    commutingOperatorValue G ≤ r :=
  ciSup_le fun S => value_le_of_mem S G h

/-- **Strict upper bounds on the commuting-operator value**, for nonempty answer sets: the value
is below `r` exactly when some `r' < r` has a cone certificate `r'·1 - W_G ∈ M`. The forward
direction is the Positivstellensatz at a level strictly between the value and `r`. The converse
needs the answer sets to be nonempty (or `0 < r`, see `commutingOperatorValue_lt_iff_of_pos`):
if `A` is empty and `X` is not, every polynomial lies in the cone, while the value is `0`. -/
theorem commutingOperatorValue_lt_iff [Nonempty A] [Nonempty B] (G : Game X Y A B) {r : ℝ} :
    commutingOperatorValue G < r ↔
      ∃ r' < r, r' • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B := by
  constructor
  · intro h
    obtain ⟨r', h1, h2⟩ := exists_between h
    exact ⟨r', h2, sub_gamePoly_mem_cone_of_lt G h1⟩
  · rintro ⟨r', hr', h⟩
    exact (commutingOperatorValue_le_of_mem_of_nonempty G h).trans_lt hr'

/-- **Strict positive upper bounds on the commuting-operator value**, for arbitrary alphabets:
for `0 < r`, the value is below `r` exactly when some `r' < r` has a cone certificate
`r'·1 - W_G ∈ M`. For the converse, a certificate at a negative level `r'` is moved up to level
`0` by adding `-r'·1 ∈ M`, so that `commutingOperatorValue_le_of_mem` applies. -/
theorem commutingOperatorValue_lt_iff_of_pos (G : Game X Y A B) {r : ℝ} (hr : 0 < r) :
    commutingOperatorValue G < r ↔
      ∃ r' < r, r' • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B := by
  constructor
  · intro h
    obtain ⟨r', h1, h2⟩ := exists_between h
    exact ⟨r', h2, sub_gamePoly_mem_cone_of_lt G h1⟩
  · rintro ⟨r', hr', h⟩
    have hmax : max r' 0 • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B := by
      have hone : (max r' 0 - r') • (1 : NCPoly (Gen X Y A B)) ∈ cone X Y A B :=
        PointedCone.smul_mem _ (sub_nonneg.2 (le_max_left r' 0)) NCPoly.one_mem_qmod
      convert Submodule.add_mem _ h hone using 1
      rw [sub_smul]
      abel
    exact (commutingOperatorValue_le_of_mem G (le_max_right r' 0) hmax).trans_lt
      (max_lt hr' hr)

/-- **The commuting-operator value is the infimum of the cone certificates**, for nonempty
answer sets: it is the greatest lower bound of the levels `r` with `r·1 - W_G ∈ M`. -/
theorem isGLB_commutingOperatorValue [Nonempty A] [Nonempty B] (G : Game X Y A B) :
    IsGLB {r : ℝ | r • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B}
      (commutingOperatorValue G) := by
  refine ⟨fun r hr => commutingOperatorValue_le_of_mem_of_nonempty G hr, fun c hc => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨r', h1, h2⟩ := exists_between hlt
  exact (hc (sub_gamePoly_mem_cone_of_lt G h1)).not_gt h2

end Tsirelson

end MIPRE
