/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.WinMS
import MIPRE.Background.QLD.Consistency
import MIPRE.Foundations.Commutation

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

/-! ## The commuting case

The other half of `lem:qld-obs-commutation`. Here the two point observables **commute**, and the
route is the paper's: chain items 5, 4 and 1 so that each point probe is cross-party close to a
*marginal* of the `Pair` measurement on the other side, replace that measurement by a projective
one (`cor:ortho-from-consistency`), and apply the commutation analysis.

Two departures from the paper's bookkeeping, both forced by which side things live on.

**The analysis is run on Bob's observables and transferred back.** `commutation_analysis` wants the
two commuting families on one side and the joint projective measurement on the *other*, and
`exists_projective_of_consistent` produces a projective measurement on **Alice's** factor. So the
analysis is applied to *Bob's* point measurements against Alice's projectivized `Pair`
measurement, and the conclusion is carried to Alice's observables by the order-reversal rule
(`norm_stateVec_comm_le`) with `pts_obs_consistency`. The alternative --- a Bob-side orthonormali-
zation corollary --- would duplicate the whole of `Ortho.lean` through the swap.

**The chain is run in the mirrored orientation.** Every rule of `fig:decider_pauli` is stated in
both orientations, so items 5 and 1 are available with the players exchanged; item 4 is used as it
stands. The chain is
`A^{Pair}_{[beta_W = o]} ~ B^{Pair}_{[beta_W = o]} ~ A^{(Pair,W)}_o ~ B^{(Point,W)}_{probe = o}`,
three links at `172 eps` each, so `1548 eps` after one three-term triangle inequality.
-/

section Commuting

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- Alice's **joint** `Pair` measurement: both bits at once, which is the product outcome set the
commutation analysis needs. -/
def pairPOVM (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA)
    (c : Content F m) : POVM (ZMod 2 × ZMod 2) dA :=
  (MA (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)

/-- Alice's point-probe measurement, of which `ptObs` is the observable. -/
def ptPOVM (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA) (W : Bas)
    (c : Content F m) : POVM (ZMod 2) dA :=
  (MA (c.question hm (.point W))).map (rdProbeAt W c)

/-- Bob's **joint** `Pair` measurement. -/
def pairPOVMB (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB)
    (c : Content F m) : POVM (ZMod 2 × ZMod 2) dB :=
  (MB (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)

/-- Bob's point-probe measurement. -/
def ptPOVMB (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB) (W : Bas)
    (c : Content F m) : POVM (ZMod 2) dB :=
  (MB (c.question hm (.point W))).map (rdProbeAt W c)

/-- Bob's point observable. -/
def ptObsB (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB) (W : Bas)
    (c : Content F m) : Matrix dB dB ℂ :=
  obs2 (ptPOVMB hm MB W c)

theorem ptObs_eq_obs2 (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA)
    (W : Bas) (c : Content F m) : ptObs hm MA W c = obs2 (ptPOVM hm MA W c) := rfl

theorem ptObsB_mul_self_le_one (hm : m ∣ Fintype.card F)
    (MB : Question F m → POVM (Answer F m d) dB) (W : Bas) (c : Content F m) :
    (ptObsB hm MB W c)ᴴ * ptObsB hm MB W c ≤ (1 : Matrix dB dB ℂ) :=
  obs2_mul_self_le_one _

/-- The `W`-marginal of the joint `Pair` measurement is the `Pair` measurement read in `W`
alone. -/
theorem sum_pairPOVM_X (hm : m ∣ Fintype.card F)
    (MA : Question F m → POVM (Answer F m d) dA) (c : Content F m) (o : ZMod 2) :
    ∑ o' : ZMod 2, (((pairPOVM hm MA c).mats (o, o')).val)
      = ((((MA (c.question hm .pair)).map (rdBitPair .X)).mats o).val) :=
  POVM.sum_mats_map_prod _ _ _ o

theorem sum_pairPOVM_Z (hm : m ∣ Fintype.card F)
    (MA : Question F m → POVM (Answer F m d) dA) (c : Content F m) (o : ZMod 2) :
    ∑ o' : ZMod 2, (((pairPOVM hm MA c).mats (o', o)).val)
      = ((((MA (c.question hm .pair)).map (rdBitPair .Z)).mats o).val) :=
  POVM.sum_mats_map_prod' _ _ _ o

/-! ### The three links -/

theorem adj_pairB_point (W : Bas) : adj (.pairB W) (.point W) = true := by
  rw [adj_symm]; exact adj_point_pairB W

/-- **Item 5 in the mirrored orientation**: Alice's `(Pair, W)` bit agrees with Bob's point
probe. -/
theorem link_pairB_point (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          xSqNorm ψ ((((MA (c.question hm (.pairB W))).map rdBit).mats o).val)
            (((ptPOVMB hm MB W c).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail (adj_pairB_point W) commSet (fun _ => rdBit)
    (rdProbeAt W) fun c hc a b h => ?_
  have hγ := gam_eq_zero_of_mem_commSet hc
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_bit_of_fmtOk_pairB hfa
  obtain ⟨b', rfl⟩ := eq_val_of_fmtOk hfb
  have hs' : prb b' (c.omega.r W) = a' := by
    simpa [subtests, Question.ty, Content.question, pairTest, hγ] using hs
  exact hs'.symm

/-- **Item 1 at the `Pair` type**, read in one basis, restricted to the commuting tuples. -/
theorem link_pair_pair (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          xSqNorm ψ ((((MA (c.question hm .pair)).map (rdBitPair W)).mats o).val)
            ((((MB (c.question hm .pair)).map (rdBitPair W)).mats o).val)
      ≤ 172 * ε := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ commSet)
    fun c _ _ => ?_) (item_consistency hψ hfail .pair (rdBitPair W))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun o _ => xSqNorm_nonneg _ _ _)

/-- **The chain** (the paper's `eq:lc-11`, mirrored): Alice's `Pair` measurement read in one basis
is cross-party close to Bob's point probe, on the commuting tuples. Three links at `172 eps`, one
three-term triangle inequality. -/
theorem chain_pair_point (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          xSqNorm ψ ((((MA (c.question hm .pair)).map (rdBitPair W)).mats o).val)
            (((ptPOVMB hm MB W c).mats o).val)
      ≤ 1548 * ε := by
  classical
  have key := sum_weighted_snorm_sq_triangle3 (v := ψ)
    (w := fun _ : Content F m => (Fintype.card (Content F m) : ℝ)⁻¹)
    (fun _ => by positivity) commSet
    (fun c o => (aOp ((((MA (c.question hm .pair)).map (rdBitPair W)).mats o).val)
      : Matrix (dA × dB) (dA × dB) ℂ))
    (fun c o => (bOp ((((MB (c.question hm .pair)).map (rdBitPair W)).mats o).val)
      : Matrix (dA × dB) (dA × dB) ℂ))
    (fun c o => (aOp ((((MA (c.question hm (.pairB W))).map rdBit).mats o).val)
      : Matrix (dA × dB) (dA × dB) ℂ))
    (fun c o => (bOp (((ptPOVMB hm MB W c).mats o).val)
      : Matrix (dA × dB) (dA × dB) ℂ))
  rw [← sum_weighted_xSqNorm_eq ψ _ commSet
      (fun c o => (((MA (c.question hm .pair)).map (rdBitPair W)).mats o).val)
      (fun c o => ((ptPOVMB hm MB W c).mats o).val),
    ← sum_weighted_xSqNorm_eq ψ _ commSet
      (fun c o => (((MA (c.question hm .pair)).map (rdBitPair W)).mats o).val)
      (fun c o => (((MB (c.question hm .pair)).map (rdBitPair W)).mats o).val),
    ← sum_weighted_xSqNorm_eq' ψ _ commSet
      (fun c o => (((MA (c.question hm (.pairB W))).map rdBit).mats o).val)
      (fun c o => (((MB (c.question hm .pair)).map (rdBitPair W)).mats o).val),
    ← sum_weighted_xSqNorm_eq ψ _ commSet
      (fun c o => (((MA (c.question hm (.pairB W))).map rdBit).mats o).val)
      (fun c o => ((ptPOVMB hm MB W c).mats o).val)] at key
  have h1 := link_pair_pair hψ hfail W
  have h2 := item_commutation hψ hfail W
  have h3 := link_pairB_point hψ hfail W
  linarith

/-! ### The three averaged inputs -/

/-- The per-content quantity `chain_pair_point` bounds. -/
def chainQty (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (W : Bas) (c : Content F m) : ℝ :=
  ∑ o : ZMod 2, xSqNorm ψ ((((MA (c.question hm .pair)).map (rdBitPair W)).mats o).val)
    (((ptPOVMB hm MB W c).mats o).val)

/-- The inconsistency of the two players' joint `Pair` measurements at one content. -/
def incQty (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (c : Content F m) : ℝ :=
  pairInconsistency ψ (pairPOVM hm MA c) (pairPOVMB hm MB c)

theorem chainQty_nonneg (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (W : Bas) (c : Content F m) : 0 ≤ chainQty hm ψ MA MB W c :=
  Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _

theorem incQty_nonneg (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (c : Content F m) : 0 ≤ incQty hm ψ MA MB c :=
  pairInconsistency_nonneg _ _ _

/-- The weight the items carry on the commuting tuples. -/
def commWeight (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] (m : ℕ)
    [NeZero m] : Content F m → ℝ :=
  fun c => if c ∈ commSet then (Fintype.card (Content F m) : ℝ)⁻¹ else 0

theorem commWeight_nonneg (c : Content F m) : 0 ≤ commWeight F m c := by
  rw [commWeight]
  split_ifs
  · positivity
  · exact le_refl 0

theorem sum_commWeight_mul (f : Content F m → ℝ) :
    ∑ c, commWeight F m c * f c
      = ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ * f c := by
  classical
  rw [commSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : gam c.omega = 0
  · rw [if_pos h, commWeight,
      if_pos (show c ∈ commSet from Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)]
  · rw [if_neg h, commWeight,
      if_neg fun hh => h (gam_eq_zero_of_mem_commSet hh), zero_mul]

theorem sum_commWeight_le_one : ∑ c, commWeight F m c ≤ 1 := by
  classical
  have h := sum_commWeight_mul (F := F) (m := m) fun _ => (1 : ℝ)
  simp only [mul_one] at h
  rw [h]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ commSet)
    fun c _ _ => by positivity) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast card_Content_pos.ne')

/-- **The point observables are cross-party consistent at the content's own probe.** Item 1 at the
type `(Point, W)` with the reading `rdProbeAt W`, which is a *family* --- the probe depends on the
content --- and then `xStateDist_obsOf_le`. `pts_obs_consistency` is the same statement at a fixed
`r`; here the probe is the one the commutation check uses. -/
theorem xStateDist_ptObs_ptObsB (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    xStateDist (commWeight F m) ψ (ptObs hm MA W) (ptObsB hm MB W) ≤ 344 * ε := by
  classical
  have hpovm : xPovmDist (commWeight F m) ψ (ptPOVM hm MA W) (ptPOVMB hm MB W) ≤ 172 * ε := by
    rw [xPovmDist, sum_commWeight_mul]
    exact agree_subtest_le hψ hfail (adj_self' (.point W)) commSet (rdProbeAt W) (rdProbeAt W)
      fun c _ a b h => by
        have hs := (of_accepts h).2.2
        rw [subtests, if_pos rfl] at hs
        exact congrArg (rdProbeAt W c) (of_decide_eq_true hs)
  have hobsA : ptObs hm MA W = obsOf sgn (ptPOVM hm MA W) :=
    funext fun c => by rw [ptObs_eq_obs2, obsOf_sgn_eq_obs2]
  have hobsB : ptObsB hm MB W = obsOf sgn (ptPOVMB hm MB W) :=
    funext fun c => by rw [ptObsB, obsOf_sgn_eq_obs2]
  rw [hobsA, hobsB]
  refine le_trans (xStateDist_obsOf_le (fun c => commWeight_nonneg c) ψ _ _ sgn
    fun a => le_of_eq (norm_sgn a)) ?_
  rw [show (344 : ℝ) * ε = (Fintype.card (ZMod 2) : ℝ) * (172 * ε) from by
    rw [ZMod.card]; push_cast; ring]
  exact mul_le_mul_of_nonneg_left hpovm (by positivity)

/-- **The inconsistency of the two joint `Pair` measurements is a conditional failure.** Item 1
again, at the Born level, which is where data processing is available: `fact:data-processing` is a
statement about *consistency*, and NW19's own remark gives a counterexample for the
state-dependent distance. -/
theorem incQty_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) (c : Content F m) :
    incQty hm ψ MA MB c
      ≤ condFail (qldGame hm) ψ MA MB (c.question hm .pair) (c.question hm .pair) := by
  have hD : ∀ a b : Answer F m d,
      (qldGame hm).D (c.question hm .pair) (c.question hm .pair) a b = true →
      (rdBitPair .X a, rdBitPair .Z a) = (rdBitPair .X b, rdBitPair .Z b) := by
    intro a b h
    have hs := (of_accepts h).2.2
    rw [subtests, if_pos rfl] at hs
    exact congrArg (fun x => (rdBitPair .X x, rdBitPair .Z x)) (of_decide_eq_true hs)
  have h := one_sub_sum_bornProb_le_condFail (G := qldGame hm) (ψ := ψ) (MA := MA) (MB := MB)
    (x := c.question hm .pair) (y := c.question hm .pair)
    (fun a => (rdBitPair .X a, rdBitPair .Z a)) (fun a => (rdBitPair .X a, rdBitPair .Z a)) hD
  have hdiag := sum_diag_eq_one_sub hψ (pairPOVM hm MA c) (pairPOVMB hm MB c)
  rw [incQty]
  rw [show (∑ p : ZMod 2 × ZMod 2, bornProb ψ ((((MA (c.question hm .pair)).map
        fun a => (rdBitPair .X a, rdBitPair .Z a)).mats p).val)
      ((((MB (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)).mats p).val))
      = 1 - pairInconsistency ψ (pairPOVM hm MA c) (pairPOVMB hm MB c) from hdiag] at h
  linarith

theorem sum_incQty_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c, commWeight F m c * incQty hm ψ MA MB c ≤ 86 * ε := by
  classical
  rw [sum_commWeight_mul]
  refine le_trans (Finset.sum_le_sum fun c _ => ?_)
    (subtest_le hψ hfail (adj_self' .pair) commSet)
  exact mul_le_mul_of_nonneg_left (incQty_le_condFail hψ c) (by positivity)

/-! ### The per-content bound

The three inputs meet here. `chainQty` is what the chain bounds, `incQty` what
`cor:ortho-from-consistency` consumes, and the `eta` is the slack that corollary's hypothesis
asks for; it is sent to zero when the bound is averaged. -/

/-- **The per-content bound.** At one content, the two point observables commute on the state up
to the chain, the projectivization, and the two cross-party consistencies of the observables
themselves. `768 = 3 * 256`: the analysis contributes `16`, the observable expansion `16`, and the
final triangle inequality `3`. -/
theorem sq_norm_ptObs_comm_le_of_content (hψ : star ψ ⬝ᵥ ψ = 1) (c : Content F m)
    {η : ℝ} (hη : 0 < η) :
    ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
        - ptObs hm MA .Z c * ptObs hm MA .X c)‖ ^ 2
      ≤ 12 * xSqNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
        + 12 * xSqNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)
        + 768 * (2 * (chainQty hm ψ MA MB .X c + chainQty hm ψ MA MB .Z c)
          + 72 * (incQty hm ψ MA MB c + η)) := by
  classical
  -- the projective measurement close to Alice's joint `Pair` measurement
  obtain ⟨P, hsa, hidem, hsum, hbound⟩ := exists_projective_of_consistent hψ
    (pairPOVM hm MA c) (pairPOVMB hm MB c) (incQty hm ψ MA MB c + η)
    (by have := incQty_nonneg hm ψ MA MB c; linarith)
    (by rw [incQty]; linarith)
  have hPVM : IsPVM P := ⟨hsa, hidem, hsum⟩
  rw [Fintype.sum_prod_type] at hbound
  have hinc0 := incQty_nonneg hm ψ MA MB c
  have hchX0 := chainQty_nonneg hm ψ MA MB .X c
  have hchZ0 := chainQty_nonneg hm ψ MA MB .Z c
  -- the two hypotheses of the analysis, in the cross-party form
  have hX : ∑ b : ZMod 2, xSqNorm ψ (∑ o' : ZMod 2, P (b, o'))
      (((ptPOVMB hm MB .X c).mats b).val)
      ≤ 2 * (2 * (18 * (incQty hm ψ MA MB c + η))) + 2 * chainQty hm ψ MA MB .X c := by
    refine sum_xSqNorm_le_of_two_step _
      (fun b => ((((MA (c.question hm .pair)).map (rdBitPair .X)).mats b).val)) _ ?_
      (le_of_eq rfl)
    have hstep : ∀ b : ZMod 2, stateSqNorm ψ ((∑ o' : ZMod 2, P (b, o'))
        - ((((MA (c.question hm .pair)).map (rdBitPair .X)).mats b).val))
        ≤ 2 * ∑ o' : ZMod 2, stateSqNorm ψ ((((pairPOVM hm MA c).mats (b, o')).val) - P (b, o')) := by
      intro b
      rw [← sum_pairPOVM_X hm MA c b, ← Finset.sum_sub_distrib]
      refine le_trans (stateSqNorm_sum_le ψ fun o' => P (b, o') - (((pairPOVM hm MA c).mats (b, o')).val))
        ?_
      rw [show (Fintype.card (ZMod 2) : ℝ) = 2 from by rw [ZMod.card]; norm_num]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o' _ => ?_) (by norm_num)
      rw [stateSqNorm_sub_comm]
    refine le_trans (Finset.sum_le_sum fun b _ => hstep b) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (le_of_lt hbound) (by norm_num)
  have hZ : ∑ b : ZMod 2, xSqNorm ψ (∑ o' : ZMod 2, P (o', b))
      (((ptPOVMB hm MB .Z c).mats b).val)
      ≤ 2 * (2 * (18 * (incQty hm ψ MA MB c + η))) + 2 * chainQty hm ψ MA MB .Z c := by
    refine sum_xSqNorm_le_of_two_step _
      (fun b => ((((MA (c.question hm .pair)).map (rdBitPair .Z)).mats b).val)) _ ?_
      (le_of_eq rfl)
    have hstep : ∀ b : ZMod 2, stateSqNorm ψ ((∑ o' : ZMod 2, P (o', b))
        - ((((MA (c.question hm .pair)).map (rdBitPair .Z)).mats b).val))
        ≤ 2 * ∑ o' : ZMod 2, stateSqNorm ψ ((((pairPOVM hm MA c).mats (o', b)).val) - P (o', b)) := by
      intro b
      rw [← sum_pairPOVM_Z hm MA c b, ← Finset.sum_sub_distrib]
      refine le_trans (stateSqNorm_sum_le ψ fun o' => P (o', b) - (((pairPOVM hm MA c).mats (o', b)).val))
        ?_
      rw [show (Fintype.card (ZMod 2) : ℝ) = 2 from by rw [ZMod.card]; norm_num]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o' _ => ?_) (by norm_num)
      rw [stateSqNorm_sub_comm]
    refine le_trans (Finset.sum_le_sum fun b _ => hstep b) ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    exact mul_le_mul_of_nonneg_left (le_of_lt hbound) (by norm_num)
  -- transport them into the swapped frame
  set δ : ℝ := 2 * (chainQty hm ψ MA MB .X c + chainQty hm ψ MA MB .Z c)
    + 72 * (incQty hm ψ MA MB c + η) with hδ
  have hXs : ∑ b : ZMod 2, snorm (swapVec ψ)
      ((aOp ((((ptPOVMB hm MB .X c).mats b).val)) : Matrix (dB × dA) (dB × dA) ℂ)
        - bOp (∑ o' : ZMod 2, P (b, o'))) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) (le_trans hX ?_)
    · rw [snorm_swapVec_aOp_sub_bOp, ← xSqNorm_eq_sq]
    · rw [hδ]; linarith
  have hZs : ∑ b : ZMod 2, snorm (swapVec ψ)
      ((aOp ((((ptPOVMB hm MB .Z c).mats b).val)) : Matrix (dB × dA) (dB × dA) ℂ)
        - bOp (∑ o' : ZMod 2, P (o', b))) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) (le_trans hZ ?_)
    · rw [snorm_swapVec_aOp_sub_bOp, ← xSqNorm_eq_sq]
    · rw [hδ]; linarith
  -- the analysis, on Bob's observables
  have hanal := commutation_analysis_aOp (ψ := swapVec ψ) (A := ptPOVMB hm MB .X c)
    (Cm := ptPOVMB hm MB .Z c) (P := P) hPVM hXs hZs
  have hone : ‖stateVecB ψ ((((ptPOVMB hm MB .X c).mats 1).val)
        * (((ptPOVMB hm MB .Z c).mats 1).val)
      - (((ptPOVMB hm MB .Z c).mats 1).val) * (((ptPOVMB hm MB .X c).mats 1).val))‖ ^ 2
      ≤ 16 * δ := by
    refine le_trans (le_of_eq ?_) (le_trans (Finset.single_le_sum
      (f := fun p : ZMod 2 × ZMod 2 => snorm (swapVec ψ)
        (aOp ((((ptPOVMB hm MB .X c).mats p.1).val) * (((ptPOVMB hm MB .Z c).mats p.2).val)
          - (((ptPOVMB hm MB .Z c).mats p.2).val) * (((ptPOVMB hm MB .X c).mats p.1).val))
          : Matrix (dB × dA) (dB × dA) ℂ) ^ 2)
      (fun p _ => by positivity) (Finset.mem_univ ((1 : ZMod 2), (1 : ZMod 2)))) hanal)
    rw [snorm_swapVec_aOp]
  -- the observables, by the exact expansion
  have hobs : ‖stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
      - ptObsB hm MB .Z c * ptObsB hm MB .X c)‖ ^ 2 ≤ 256 * δ := by
    rw [ptObsB, ptObsB, obs2_commutator_eq, stateVecB_smul, norm_smul,
      show ‖(4 : ℂ)‖ = 4 from by norm_num, mul_pow]
    have : (4 : ℝ) ^ 2 = 16 := by norm_num
    rw [this]
    calc (16 : ℝ) * ‖stateVecB ψ _‖ ^ 2 ≤ 16 * (16 * δ) :=
          mul_le_mul_of_nonneg_left hone (by norm_num)
      _ = 256 * δ := by ring
  -- transfer to Alice's observables
  have htr := norm_stateVec_comm_le (ψ := ψ) (ptObs hm MA .X c) (ptObs hm MA .Z c)
    (ptObsB hm MB .X c) (ptObsB hm MB .Z c)
    (ptObs_mul_self_le_one hm MA .X c) (ptObs_mul_self_le_one hm MA .Z c)
    (ptObsB_mul_self_le_one hm MB .X c) (ptObsB_mul_self_le_one hm MB .Z c)
  rw [norm_stateVecB_sub_comm] at htr
  have hu := xNorm_nonneg ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
  have hv := xNorm_nonneg ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)
  have ht := norm_nonneg (stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
    - ptObsB hm MB .Z c * ptObsB hm MB .X c))
  have h0 := norm_nonneg (stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
    - ptObs hm MA .Z c * ptObs hm MA .X c))
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq, hδ] at *
  nlinarith [sq_nonneg (xNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
      - xNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)),
    sq_nonneg (2 * xNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
      - ‖stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
        - ptObsB hm MB .Z c * ptObsB hm MB .X c)‖),
    sq_nonneg (2 * xNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)
      - ‖stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
        - ptObsB hm MB .Z c * ptObsB hm MB .X c)‖)]

theorem sum_chainQty_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c, commWeight F m c * chainQty hm ψ MA MB W c ≤ 1548 * ε := by
  rw [sum_commWeight_mul]
  exact chain_pair_point hψ hfail W

/-- **The commuting half of `lem:qld-obs-commutation`.** On the commuting tuples the two point
observables commute on the state, at `9519168 eps` --- and, like the anticommuting half, with no
square root. -/
theorem comm_signed_commutation (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
          - ptObs hm MA .Z c * ptObs hm MA .X c)‖ ^ 2
      ≤ 9519168 * ε := by
  classical
  rw [← sum_commWeight_mul]
  refine le_of_forall_pos_le_add fun ξ hξ => ?_
  have hη : (0 : ℝ) < ξ / 55296 := by positivity
  refine le_trans (Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (sq_norm_ptObs_comm_le_of_content (MB := MB) hψ c hη)
      (commWeight_nonneg (F := F) (m := m) c)) ?_
  have hdist : ∑ c, commWeight F m c *
        (12 * xSqNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
          + 12 * xSqNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)
          + 768 * (2 * (chainQty hm ψ MA MB .X c + chainQty hm ψ MA MB .Z c)
            + 72 * (incQty hm ψ MA MB c + ξ / 55296)))
      = 12 * (∑ c, commWeight F m c * xSqNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c))
        + 12 * (∑ c, commWeight F m c * xSqNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c))
        + 1536 * (∑ c, commWeight F m c * chainQty hm ψ MA MB .X c)
        + 1536 * (∑ c, commWeight F m c * chainQty hm ψ MA MB .Z c)
        + 55296 * (∑ c, commWeight F m c * incQty hm ψ MA MB c)
        + 55296 * (ξ / 55296) * (∑ c, commWeight F m c) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hdist]
  have h1 : ∑ c, commWeight F m c * xSqNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c) ≤ 344 * ε :=
    xStateDist_ptObs_ptObsB hψ hfail .X
  have h2 : ∑ c, commWeight F m c * xSqNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c) ≤ 344 * ε :=
    xStateDist_ptObs_ptObsB hψ hfail .Z
  have h3 := sum_chainQty_le hψ hfail (MA := MA) (MB := MB) .X
  have h4 := sum_chainQty_le hψ hfail (MA := MA) (MB := MB) .Z
  have h5 := sum_incQty_le hψ hfail (MA := MA) (MB := MB)
  have h6 : ∑ c, commWeight F m c ≤ 1 := sum_commWeight_le_one
  have h7 : (0 : ℝ) ≤ ∑ c, commWeight F m c :=
    Finset.sum_nonneg fun c _ => commWeight_nonneg c
  have hcancel : (55296 : ℝ) * (ξ / 55296) = ξ := by field_simp
  rw [hcancel]
  nlinarith [hξ.le]

/-! ### Both halves

`lem:qld-obs-commutation` as the paper states it: one average over *all* contents, with the sign
`(-1)^{gamma(omega)}` inside. The two halves are the two branches of that sign, and the type graph's
content distribution is uniform, so the statement is the sum of the two restricted ones. -/

/-- **`lem:qld-obs-commutation`.** On average over the verifier's content, the two point
observables commute up to the sign `(-1)^{gamma(omega)}`, at `57676416 eps = 9519168 eps +
48157248 eps`. The blueprint states this at `O(sqrt(eps))`; it is `O(eps)`, and the two halves are
where that is decided. -/
theorem signed_commutation (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
          - sgn (gam c.omega) • (ptObs hm MA .Z c * ptObs hm MA .X c))‖ ^ 2
      ≤ 57676416 * ε := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Content F m))
    (fun c => gam c.omega = 0)
    (fun c => (Fintype.card (Content F m) : ℝ)⁻¹ *
      ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
        - sgn (gam c.omega) • (ptObs hm MA .Z c * ptObs hm MA .X c))‖ ^ 2)
  rw [← hsplit]
  have hcomm : ∑ c ∈ univ.filter (fun c : Content F m => gam c.omega = 0),
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
          - sgn (gam c.omega) • (ptObs hm MA .Z c * ptObs hm MA .X c))‖ ^ 2
      ≤ 9519168 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c hc => ?_))
      (comm_signed_commutation hψ hfail)
    rw [gam_eq_zero_of_mem_commSet (by rw [commSet]; exact hc), sgn_zero, one_smul]
  have hacomm : ∑ c ∈ univ.filter (fun c : Content F m => ¬ gam c.omega = 0),
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
          - sgn (gam c.omega) • (ptObs hm MA .Z c * ptObs hm MA .X c))‖ ^ 2
      ≤ 48157248 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c hc => ?_))
      (acomm_signed_commutation hψ hfail)
    have hγ : gam c.omega = 1 := by
      have h := gam_ne_zero_of_mem_acommSet (show c ∈ acommSet from by rw [acommSet]; exact hc)
      revert h
      generalize gam c.omega = x
      revert x
      decide
    rw [hγ, sgn_one, neg_one_smul, sub_neg_eq_add]
  linarith

end Commuting

end MIPRE.QLD

end
