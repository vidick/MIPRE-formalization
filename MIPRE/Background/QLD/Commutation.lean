/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.WinMS

/-!
# Signed commutation of the point observables, on the anticommuting tuples

Blueprint `lem:qld-obs-commutation`, the anticommuting case. On a tuple `omega` with
`gamma(omega) = 1` the two point observables **anticommute** on the state:

```
X^{r_X}(u_X) Z^{r_Z}(u_Z) (x) Id  ~  - Z^{r_Z}(u_Z) X^{r_X}(u_X) (x) Id .
```

Three inputs, all already proved:

* **item 7** of `lem:qld-win` (`item_ms_consistency_X`, `item_ms_consistency_Z`): each point
  probe agrees with one of the two distinguished `Variable` bits on the *other* side. At the
  level of observables that is `X (x) Id ~ Id (x) V_1` and `Z (x) Id ~ Id (x) V_5`, at `344 eps`
  each --- item 7 at the two-outcome probe, then `xStateDist_obsOf_le`;
* **item 6** (`item_magicSquare`): those two `Variable` observables anticommute on the state, at
  `16049664 eps`;
* the **order reversal** `norm_stateVec_anticomm_le`, which is what carries an anticommutation
  from Bob's side to Alice's --- and is where the sign comes from.

## Why this case costs `eps` and not `sqrt(eps)`

The blueprint states `lem:qld-obs-commutation` at `O(sqrt(eps))`, and that is what the
*commuting* case costs: it needs the `Pair` measurement to be projective, which a general POVM
strategy's is not, so it goes through `cor:ortho-from-consistency` and pays a square root. The
anticommuting case does not: every input is already a squared-norm bound linear in `eps`, and the
only inequalities used are the triangle inequality and `(u+v+w)^2 <= 3(u^2+v^2+w^2)`. So the
constant here is honest and there is no square root --- `48157248 eps`, from
`12 * 344 + 12 * 344 + 3 * 16049664`.

That asymmetry is worth recording rather than rounding away: when the commuting case is
formalized the two halves will not combine into a single `O(sqrt(eps))` by adding constants, and
the square root will be attributable to exactly one of them.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

-- Every statement below mentions both players' spaces and the field, and the estimates are
-- inherited from `Win.lean` and `WinMS.lean`, whose variable blocks are the same. Omitting the
-- unused ones declaration by declaration would be a dozen `omit` lines with no consumer.
set_option linter.unusedSectionVars false

/-! ## The two observables -/

/-- **Alice's point observable**: the `±1`-observable of the trace probe of the `(Point, W)`
answer against the content's own `r_W`. This is the blueprint's `W^{r_W}(u_W)`. -/
def ptObs (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA) (W : Bas)
    (c : Content F m) : Matrix dA dA ℂ :=
  obs2 ((MA (c.question hm (.point W))).map (rdProbeAt W c))

/-- **Bob's variable observable**: the `±1`-observable of the bit a `Variable_j` answer
reports. -/
def varObs (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB)
    (j : Fin layout.s) (c : Content F m) : Matrix dB dB ℂ :=
  obs2 ((MB (c.question hm (.var j))).map rdBit)

theorem ptObs_mul_self_le_one (hm : m ∣ Fintype.card F)
    (MA : Question F m → POVM (Answer F m d) dA) (W : Bas) (c : Content F m) :
    (ptObs hm MA W c)ᴴ * ptObs hm MA W c ≤ (1 : Matrix dA dA ℂ) :=
  obs2_mul_self_le_one _

theorem varObs_mul_self_le_one (hm : m ∣ Fintype.card F)
    (MB : Question F m → POVM (Answer F m d) dB) (j : Fin layout.s) (c : Content F m) :
    (varObs hm MB j c)ᴴ * varObs hm MB j c ≤ (1 : Matrix dB dB ℂ) :=
  obs2_mul_self_le_one _

/-! ## The weight: uniform on the anticommuting tuples -/

/-- The weight the items of `lem:qld-win` carry on the anticommuting tuples: uniform over all
contents, supported on `acommSet`. It is not a probability distribution --- its total mass is the
fraction of tuples that anticommute --- which is exactly how the items are stated. -/
def acommWeight (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] (m : ℕ)
    [NeZero m] : Content F m → ℝ :=
  fun c => if c ∈ acommSet then (Fintype.card (Content F m) : ℝ)⁻¹ else 0

theorem acommWeight_nonneg (c : Content F m) : 0 ≤ acommWeight F m c := by
  rw [acommWeight]
  split_ifs
  · positivity
  · exact le_refl 0

theorem sum_acommWeight_mul (f : Content F m → ℝ) :
    ∑ c, acommWeight F m c * f c
      = ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ * f c := by
  classical
  rw [acommSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : gam c.omega ≠ 0
  · rw [if_pos h, acommWeight,
      if_pos (show c ∈ acommSet from Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)]
  · rw [if_neg h, acommWeight,
      if_neg fun hh => h (gam_ne_zero_of_mem_acommSet hh), zero_mul]

/-! ## Item 7 at the level of observables

Item 7 is a POVM-level agreement: the point probe and the `Variable` bit take the same value. The
observable form is `xStateDist_obsOf_le` at the weighting `sgn`, whose cost is the number of
outcomes of the probe --- two --- so `172 eps` becomes `344 eps`. Exactly the step
`pts_obs_consistency` makes for item 1, with the weight supported on the anticommuting tuples. -/

section Items

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- **The `X` point observable agrees with the `Variable_1` observable across the two parties**,
on the anticommuting tuples. Item 7 for `X`, then `xStateDist_obsOf_le`. -/
theorem xStateDist_ptObs_varObs_X (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    xStateDist (acommWeight F m) ψ (ptObs hm MA .X) (varObs hm MB (v 0)) ≤ 344 * ε := by
  have hobsA : ptObs hm MA .X
      = obsOf sgn fun c => (MA (c.question hm (.point .X))).map (rdProbeAt .X c) :=
    funext fun c => by rw [ptObs, obsOf_sgn_eq_obs2]
  have hobsB : varObs hm MB (v 0)
      = obsOf sgn fun c => (MB (c.question hm (.var (v 0)))).map rdBit :=
    funext fun c => by rw [varObs, obsOf_sgn_eq_obs2]
  rw [hobsA, hobsB]
  refine le_trans (xStateDist_obsOf_le (fun c => acommWeight_nonneg c) ψ _ _ sgn
    fun a => le_of_eq (norm_sgn a)) ?_
  rw [show (344 : ℝ) * ε = (Fintype.card (ZMod 2) : ℝ) * (172 * ε) from by
    rw [ZMod.card]; push_cast; ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [xPovmDist, sum_acommWeight_mul]
  exact item_ms_consistency_X hψ hfail

/-- **The `Z` point observable agrees with the `Variable_5` observable across the two parties**,
on the anticommuting tuples. -/
theorem xStateDist_ptObs_varObs_Z (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    xStateDist (acommWeight F m) ψ (ptObs hm MA .Z) (varObs hm MB (v 4)) ≤ 344 * ε := by
  have hobsA : ptObs hm MA .Z
      = obsOf sgn fun c => (MA (c.question hm (.point .Z))).map (rdProbeAt .Z c) :=
    funext fun c => by rw [ptObs, obsOf_sgn_eq_obs2]
  have hobsB : varObs hm MB (v 4)
      = obsOf sgn fun c => (MB (c.question hm (.var (v 4)))).map rdBit :=
    funext fun c => by rw [varObs, obsOf_sgn_eq_obs2]
  rw [hobsA, hobsB]
  refine le_trans (xStateDist_obsOf_le (fun c => acommWeight_nonneg c) ψ _ _ sgn
    fun a => le_of_eq (norm_sgn a)) ?_
  rw [show (344 : ℝ) * ε = (Fintype.card (ZMod 2) : ℝ) * (172 * ε) from by
    rw [ZMod.card]; push_cast; ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [xPovmDist, sum_acommWeight_mul]
  exact item_ms_consistency_Z hψ hfail

end Items

/-! ## Item 6's anticommutator, in terms of the variable observables

`item_magicSquare` states the bound for `MS.anti (msPOVM MB omega)`, the anticommutator of the
*conditional Magic Square strategy*'s two observables. Those are the same operators as
`varObs`: the conditional strategy at a `Variable` question is the Pauli test's measurement at
the corresponding question, with its answer relabelled to the bit it reports, and relabelling
along the injection `Sum.inr` does not change a coarse-grained POVM element. -/

section Anti

variable {MB : Question F m → POVM (Answer F m d) dB}

theorem question_var (hm : m ∣ Fintype.card F) (c : Content F m) (j : Fin layout.s) :
    c.question hm (.var j) = Question.var j c.omega :=
  question_msTy hm c (Sum.inr j)

theorem mats_msPOVM_var (ω : Omega F m) (j : Fin layout.s) (o : ZMod 2) :
    ((msPOVM MB ω (Sum.inr j)).mats (Sum.inr o)).val
      = (((MB (Question.var j ω)).map rdBit).mats o).val := by
  classical
  have hfil : (univ.filter fun a : Answer F m d =>
        msAns (Sum.inr j) a = (Sum.inr o : layout.Answer))
      = univ.filter fun a : Answer F m d => rdBit a = o :=
    Finset.filter_congr fun a _ => by simp [msAns]
  show ((∑ a ∈ univ.filter fun a : Answer F m d =>
      msAns (Sum.inr j) a = (Sum.inr o : layout.Answer),
        (MB (msQ ω (Sum.inr j))).mats a) : selfAdjoint (Matrix dB dB ℂ)).val = _
  rw [hfil]
  rfl

/-- **The conditional Magic Square strategy's variable observables are the `varObs`.** -/
theorem bobs_msPOVM (hm : m ∣ Fintype.card F) (c : Content F m) (j : Fin layout.s) :
    MS.bobs (msPOVM MB c.omega) j = varObs hm MB j c := by
  rw [MS.bobs, varObs, obs2, question_var hm c j, mats_msPOVM_var, mats_msPOVM_var]

/-- **Item 6's anticommutator is the anticommutator of the two point-tied variable
observables.** -/
theorem anti_eq_varObs (hm : m ∣ Fintype.card F) (c : Content F m) :
    MS.anti (msPOVM MB c.omega)
      = varObs hm MB (v 0) c * varObs hm MB (v 4) c
        + varObs hm MB (v 4) c * varObs hm MB (v 0) c := by
  rw [MS.anti, bobs_msPOVM hm c, bobs_msPOVM hm c]
  rfl

end Anti

/-! ## The lemma -/

section Main

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- The pointwise step: at a single content, the two point observables anticommute up to twice
each cross-party deviation plus Bob's own anticommutator. `norm_stateVec_anticomm_le` at the four
contraction bounds, squared by `(a+b+c)^2 <= 3(a^2+b^2+c^2)`. -/
theorem sq_norm_ptObs_anticomm_le (c : Content F m) :
    ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
        + ptObs hm MA .Z c * ptObs hm MA .X c)‖ ^ 2
      ≤ 12 * xSqNorm ψ (ptObs hm MA .X c) (varObs hm MB (v 0) c)
        + 12 * xSqNorm ψ (ptObs hm MA .Z c) (varObs hm MB (v 4) c)
        + 3 * ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2 := by
  have htr := norm_stateVec_anticomm_le (ψ := ψ) (ptObs hm MA .X c) (ptObs hm MA .Z c)
    (varObs hm MB (v 0) c) (varObs hm MB (v 4) c)
    (ptObs_mul_self_le_one hm MA .X c) (ptObs_mul_self_le_one hm MA .Z c)
    (varObs_mul_self_le_one hm MB (v 0) c) (varObs_mul_self_le_one hm MB (v 4) c)
  rw [← anti_eq_varObs hm c] at htr
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq]
  have h0 := norm_nonneg (stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
    + ptObs hm MA .Z c * ptObs hm MA .X c))
  have hu := xNorm_nonneg ψ (ptObs hm MA .X c) (varObs hm MB (v 0) c)
  have hv := xNorm_nonneg ψ (ptObs hm MA .Z c) (varObs hm MB (v 4) c)
  have ht := norm_nonneg (stateVecB ψ (MS.anti (msPOVM MB c.omega)))
  nlinarith [sq_nonneg (xNorm ψ (ptObs hm MA .X c) (varObs hm MB (v 0) c)
      - xNorm ψ (ptObs hm MA .Z c) (varObs hm MB (v 4) c)),
    sq_nonneg (2 * xNorm ψ (ptObs hm MA .X c) (varObs hm MB (v 0) c)
      - ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖),
    sq_nonneg (2 * xNorm ψ (ptObs hm MA .Z c) (varObs hm MB (v 4) c)
      - ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖)]

/-- **The anticommuting half of `lem:qld-obs-commutation`.** On the anticommuting tuples the two
point observables anticommute on the state --- which is the blueprint's `(-1)^{gamma(omega)}` at
`gamma = 1` --- at error `48157248 eps`, with no square root. -/
theorem acomm_signed_commutation (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
          + ptObs hm MA .Z c * ptObs hm MA .X c)‖ ^ 2
      ≤ 48157248 * ε := by
  classical
  have hX := xStateDist_ptObs_varObs_X (hm := hm) (MA := MA) (MB := MB) hψ hfail
  have hZ := xStateDist_ptObs_varObs_Z (hm := hm) (MA := MA) (MB := MB) hψ hfail
  have hanti : ∑ c, acommWeight F m c * ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2
      ≤ 16049664 * ε := by
    rw [sum_acommWeight_mul]
    exact item_magicSquare hψ hfail
  rw [← sum_acommWeight_mul]
  calc ∑ c, acommWeight F m c * ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
            + ptObs hm MA .Z c * ptObs hm MA .X c)‖ ^ 2
      ≤ ∑ c, (12 * (acommWeight F m c
              * xSqNorm ψ (ptObs hm MA .X c) (varObs hm MB (v 0) c))
            + 12 * (acommWeight F m c
              * xSqNorm ψ (ptObs hm MA .Z c) (varObs hm MB (v 4) c))
            + 3 * (acommWeight F m c
              * ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h := mul_le_mul_of_nonneg_left (sq_norm_ptObs_anticomm_le (hm := hm) (MA := MA)
          (MB := MB) (ψ := ψ) c) (acommWeight_nonneg (F := F) (m := m) c)
        linarith
    _ = 12 * (∑ c, acommWeight F m c
            * xSqNorm ψ (ptObs hm MA .X c) (varObs hm MB (v 0) c))
          + 12 * (∑ c, acommWeight F m c
            * xSqNorm ψ (ptObs hm MA .Z c) (varObs hm MB (v 4) c))
          + 3 * (∑ c, acommWeight F m c
            * ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ ≤ 12 * (344 * ε) + 12 * (344 * ε) + 3 * (16049664 * ε) := by
        have h1 : ∑ c, acommWeight F m c
            * xSqNorm ψ (ptObs hm MA .X c) (varObs hm MB (v 0) c) ≤ 344 * ε := hX
        have h2 : ∑ c, acommWeight F m c
            * xSqNorm ψ (ptObs hm MA .Z c) (varObs hm MB (v 4) c) ≤ 344 * ε := hZ
        linarith
    _ = 48157248 * ε := by ring

end Main

end MIPRE.QLD

end
