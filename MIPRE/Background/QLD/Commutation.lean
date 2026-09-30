/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.WinMS
public import MIPRE.Foundations.Commutation

@[expose] public section

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
* the **order reversal** `BipartiteModel.stateNorm_anticomm_le`, which is what carries an
  anticommutation from Bob's side to Alice's --- and is where the sign comes from.

## Why this case costs `eps` and not `sqrt(eps)`

The blueprint states `lem:qld-obs-commutation` at `O(sqrt(eps))`, and that is what the paper's
*commuting* case costs: it needs the `Pair` measurement to be projective, which a general POVM
strategy's is not, so it goes through `cor:ortho-from-consistency` and pays a square root. The
anticommuting case does not: every input is already a squared-norm bound linear in `eps`, and the
only inequalities used are the triangle inequality and `(u+v+w)^2 <= 3(u^2+v^2+w^2)`. So the
constant here is honest and there is no square root --- `48157248 eps`, from
`12 * 344 + 12 * 344 + 3 * 16049664`.

The commuting case below is linear in `eps` as well: the strategy's `Pair` measurement is
projective, so no orthonormalization, and no square root, enters either half.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The strategy is a model
`M : BipartiteModel 𝒞 𝒜 ℬ` with `‖M.ψ‖ = 1` and two families of POVMs `PA`, `PB` in the players'
ordered algebras, the first of them **projective** (`IsPVMIn`), as every strategy of the Pauli
basis test is. The observables are elements of the players' algebras --- a two-outcome POVM's
`±1`-observable is the difference of its two elements, `POVMIn.obs2` --- their norms on the state
are `M.stateSqNorm`, `M.swap.stateSqNorm` and `M.xSqNorm`, and a two-outcome observable is a
contraction *on the Hilbert space* (`M.Bnd`, from `BipartiteModel.bnd_πA_sub`) rather than in the
algebra, which need not have a functional calculus.

The first player's projectivity is used twice: by item 6 (`item_magicSquare`, through
`lem:ms-direct-anticomm`), and in the commuting case, where Alice's joint `Pair` measurement is a
coarse-graining of her projective `Pair` measurement and so is projective itself
(`isPVMIn_pairPOVM`). That is the projective measurement the commutation analysis needs, so the
matrix route's de la Salle orthonormalization (`cor:ortho-from-consistency`, which replaced that
POVM by a nearby projective measurement) is gone, and with it the slack `η` its strict hypothesis
asked for. Every constant of the matrix statements is kept. On a unit vector
`ψ : dA × dB → ℂ` the statements are read at the tensor-product model `BipartiteModel.tensor ψ`
with the families `POVM.toIn`.
-/

noncomputable section

namespace MIPRE

/-! ## Two-outcome observables in an ordered `⋆`-ring

The model form of `MIPRE.obs2`: the `±1`-observable of a POVM with outcomes in `F_2` is the
difference of its two elements. -/

namespace POVMIn

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- The `±1`-observable of a POVM with outcomes in `F_2`. -/
def obs2 (P : POVMIn (ZMod 2) R) : R := P.op 0 - P.op 1

theorem star_obs2 (P : POVMIn (ZMod 2) R) : star P.obs2 = P.obs2 := by
  rw [obs2, star_sub, P.star_op, P.star_op]

/-- The two elements of a two-outcome POVM sum to one. -/
theorem op_zero_eq_one_sub (P : POVMIn (ZMod 2) R) : P.op 0 = 1 - P.op 1 := by
  have h := P.sum_op
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton] at h
  rw [← h, add_sub_cancel_right]

variable [Algebra ℂ R]

/-- The signed sum `pvmObs · sgn` of a two-outcome POVM is its `±1`-observable. -/
theorem pvmObs_sgn_eq_obs2 (P : POVMIn (ZMod 2) R) : pvmObs P.op sgn = P.obs2 := by
  rw [pvmObs, obs2, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, sgn_zero, sgn_one, one_smul,
    neg_one_smul, sub_eq_add_neg]

/-- **The observable of a coarse-grained POVM**, in terms of the original one. -/
theorem obs2_map [StarOrderedRing R] {A : Type*} [Fintype A] (P : POVMIn A R) (f : A → ZMod 2) :
    (P.map f).obs2 = ∑ x : A, sgn (f x) • P.op x := by
  classical
  rw [obs2, POVMIn.map_op, POVMIn.map_op,
    ← Finset.sum_fiberwise (Finset.univ : Finset A) f fun x => sgn (f x) • P.op x,
    show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h0 : (∑ x ∈ Finset.univ.filter fun x => f x = 0, sgn (f x) • P.op x)
      = ∑ x ∈ Finset.univ.filter fun x => f x = 0, P.op x :=
    Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2, sgn_zero, one_smul]
  have h1 : (∑ x ∈ Finset.univ.filter fun x => f x = 1, sgn (f x) • P.op x)
      = -∑ x ∈ Finset.univ.filter fun x => f x = 1, P.op x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x hx => by
      rw [(Finset.mem_filter.mp hx).2, sgn_one, neg_one_smul]
  rw [h0, h1, sub_eq_add_neg]

/-- **The commutator of two two-outcome observables is four times that of their `1`-elements**,
exactly: an observable is `1 - 2 P_1`, and the identity commutes with everything. So passing from
the POVM elements to the observables costs a factor `16` in a squared norm and no
approximation. -/
theorem obs2_commutator_eq (A C : POVMIn (ZMod 2) R) :
    A.obs2 * C.obs2 - C.obs2 * A.obs2 = (4 : ℂ) • (A.op 1 * C.op 1 - C.op 1 * A.op 1) := by
  rw [obs2, obs2, A.op_zero_eq_one_sub, C.op_zero_eq_one_sub,
    show (4 : ℂ) • (A.op 1 * C.op 1 - C.op 1 * A.op 1)
      = (4 : R) * (A.op 1 * C.op 1 - C.op 1 * A.op 1) by
        rw [Algebra.smul_def, map_ofNat]]
  noncomm_ring

end POVMIn

namespace QLD

open Finset MIPRE MIPRE.LCS.MagicSquare

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

-- Every statement below mentions both players' algebras and the field, and the estimates are
-- inherited from `Win.lean` and `WinMS.lean`, whose variable blocks are the same. Omitting the
-- unused ones declaration by declaration would be a dozen `omit` lines with no consumer.
set_option linter.unusedSectionVars false

/-! ## The two observables -/

/-- **Alice's point observable**: the `±1`-observable of the trace probe of the `(Point, W)`
answer against the content's own `r_W`. This is the blueprint's `W^{r_W}(u_W)`. -/
def ptObs {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (c : Content F m) : R :=
  ((P (c.question hm (.point W))).map (rdProbeAt W c)).obs2

/-- **Bob's variable observable**: the `±1`-observable of the bit a `Variable_j` answer
reports. -/
def varObs {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R)
    (j : Fin layout.s) (c : Content F m) : R :=
  ((P (c.question hm (.var j))).map rdBit).obs2

/-- Alice's point observable is a contraction on the Hilbert space: it is a difference of two POVM
elements, with no projectivity. -/
theorem ptObs_mul_self_le_one (M : BipartiteModel 𝒞 𝒜 ℬ) (hm : m ∣ Fintype.card F)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (W : Bas) (c : Content F m) :
    M.Bnd (M.πA (ptObs hm PA W c)) 1 :=
  M.bnd_πA_sub ((PA (c.question hm (.point W))).map (rdProbeAt W c)) 0 1

/-- Bob's variable observable is a contraction on the Hilbert space. -/
theorem varObs_mul_self_le_one (M : BipartiteModel 𝒞 𝒜 ℬ) (hm : m ∣ Fintype.card F)
    (PB : Question F m → POVMIn (Answer F m d) ℬ) (j : Fin layout.s) (c : Content F m) :
    M.Bnd (M.πB (varObs hm PB j c)) 1 :=
  M.swap.bnd_πA_sub ((PB (c.question hm (.var j))).map rdBit) 0 1

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
  · rw [ite_eq_left h, acommWeight,
      ite_eq_left (show c ∈ acommSet from Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)]
  · rw [ite_eq_right h, acommWeight,
      ite_eq_right fun hh => h (gam_ne_zero_of_mem_acommSet hh), zero_mul]

/-! ## Item 7 at the level of observables

Item 7 is a POVM-level agreement: the point probe and the `Variable` bit take the same value. The
observable form is `xStateDist_obsOf_le` at the weighting `sgn`, whose cost is the number of
outcomes of the probe --- two --- so `172 eps` becomes `344 eps`. Exactly the step
`pts_obs_consistency` makes for item 1, with the weight supported on the anticommuting tuples. -/

section Items

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-- **The `X` point observable agrees with the `Variable_1` observable across the two parties**,
on the anticommuting tuples. Item 7 for `X`, then `xStateDist_obsOf_le`. -/
theorem xStateDist_ptObs_varObs_X (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    M.xStateDist (acommWeight F m) (ptObs hm PA .X) (varObs hm PB (v 0)) ≤ 344 * ε := by
  have hobsA : ptObs hm PA .X
      = fun c => pvmObs ((PA (c.question hm (.point .X))).map (rdProbeAt .X c)).op sgn :=
    funext fun c => by rw [ptObs, POVMIn.pvmObs_sgn_eq_obs2]
  have hobsB : varObs hm PB (v 0)
      = fun c => pvmObs ((PB (c.question hm (.var (v 0)))).map rdBit).op sgn :=
    funext fun c => by rw [varObs, POVMIn.pvmObs_sgn_eq_obs2]
  rw [hobsA, hobsB]
  refine le_trans (M.xStateDist_obsOf_le (fun c => acommWeight_nonneg c) _ _ sgn
    fun a => le_of_eq (norm_sgn a)) ?_
  rw [show (344 : ℝ) * ε = (Fintype.card (ZMod 2) : ℝ) * (172 * ε) from by
    rw [ZMod.card]; push_cast; ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [BipartiteModel.xPovmDist, sum_acommWeight_mul]
  exact item_ms_consistency_X hM hfail

/-- **The `Z` point observable agrees with the `Variable_5` observable across the two parties**,
on the anticommuting tuples. -/
theorem xStateDist_ptObs_varObs_Z (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    M.xStateDist (acommWeight F m) (ptObs hm PA .Z) (varObs hm PB (v 4)) ≤ 344 * ε := by
  have hobsA : ptObs hm PA .Z
      = fun c => pvmObs ((PA (c.question hm (.point .Z))).map (rdProbeAt .Z c)).op sgn :=
    funext fun c => by rw [ptObs, POVMIn.pvmObs_sgn_eq_obs2]
  have hobsB : varObs hm PB (v 4)
      = fun c => pvmObs ((PB (c.question hm (.var (v 4)))).map rdBit).op sgn :=
    funext fun c => by rw [varObs, POVMIn.pvmObs_sgn_eq_obs2]
  rw [hobsA, hobsB]
  refine le_trans (M.xStateDist_obsOf_le (fun c => acommWeight_nonneg c) _ _ sgn
    fun a => le_of_eq (norm_sgn a)) ?_
  rw [show (344 : ℝ) * ε = (Fintype.card (ZMod 2) : ℝ) * (172 * ε) from by
    rw [ZMod.card]; push_cast; ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [BipartiteModel.xPovmDist, sum_acommWeight_mul]
  exact item_ms_consistency_Z hM hfail

end Items

/-! ## Item 6's anticommutator, in terms of the variable observables

`item_magicSquare` states the bound for `MS.anti (msPOVM PB omega)`, the anticommutator of the
*conditional Magic Square strategy*'s two observables. Those are the same operators as
`varObs`: the conditional strategy at a `Variable` question is the Pauli test's measurement at
the corresponding question, with its answer relabelled to the bit it reports, and relabelling
along the injection `Sum.inr` does not change a coarse-grained POVM element. -/

section Anti

variable {PB : Question F m → POVMIn (Answer F m d) ℬ}

theorem question_var (hm : m ∣ Fintype.card F) (c : Content F m) (j : Fin layout.s) :
    c.question hm (.var j) = Question.var j c.omega :=
  question_msTy hm c (Sum.inr j)

theorem mats_msPOVM_var (ω : Omega F m) (j : Fin layout.s) (o : ZMod 2) :
    (msPOVM PB ω (Sum.inr j)).op (Sum.inr o) = ((PB (Question.var j ω)).map rdBit).op o := by
  rw [msPOVM, POVMIn.map_op, POVMIn.map_op]
  exact Finset.sum_congr (Finset.filter_congr fun a _ => by simp [msAns]) fun _ _ => rfl

/-- **The conditional Magic Square strategy's variable observables are the `varObs`.** -/
theorem bobs_msPOVM (hm : m ∣ Fintype.card F) (c : Content F m) (j : Fin layout.s) :
    MS.bobs (msPOVM PB c.omega) j = varObs hm PB j c := by
  rw [MS.bobs, varObs, POVMIn.obs2, question_var hm c j, mats_msPOVM_var, mats_msPOVM_var]

/-- **Item 6's anticommutator is the anticommutator of the two point-tied variable
observables.** -/
theorem anti_eq_varObs (hm : m ∣ Fintype.card F) (c : Content F m) :
    MS.anti (msPOVM PB c.omega)
      = varObs hm PB (v 0) c * varObs hm PB (v 4) c
        + varObs hm PB (v 4) c * varObs hm PB (v 0) c := by
  rw [MS.anti, bobs_msPOVM hm c, bobs_msPOVM hm c]
  rfl

end Anti

/-! ## The lemma -/

section Main

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-- The pointwise step: at a single content, the two point observables anticommute up to twice
each cross-party deviation plus Bob's own anticommutator. `stateNorm_anticomm_le` at the four
contraction bounds, squared by `(a+b+c)^2 <= 3(a^2+b^2+c^2)`. -/
theorem sq_norm_ptObs_anticomm_le (c : Content F m) :
    M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c + ptObs hm PA .Z c * ptObs hm PA .X c)
      ≤ 12 * M.xSqNorm (ptObs hm PA .X c) (varObs hm PB (v 0) c)
        + 12 * M.xSqNorm (ptObs hm PA .Z c) (varObs hm PB (v 4) c)
        + 3 * M.swap.stateSqNorm (MS.anti (msPOVM PB c.omega)) := by
  have htr := M.stateNorm_anticomm_le (ptObs hm PA .X c) (ptObs hm PA .Z c)
    (varObs hm PB (v 0) c) (varObs hm PB (v 4) c)
    (ptObs_mul_self_le_one M hm PA .X c) (ptObs_mul_self_le_one M hm PA .Z c)
    (varObs_mul_self_le_one M hm PB (v 0) c) (varObs_mul_self_le_one M hm PB (v 4) c)
  rw [← anti_eq_varObs hm c] at htr
  simp only [BipartiteModel.stateSqNorm, BipartiteModel.xSqNorm]
  have h0 := M.stateNorm_nonneg (ptObs hm PA .X c * ptObs hm PA .Z c
    + ptObs hm PA .Z c * ptObs hm PA .X c)
  have hu := M.xNorm_nonneg (ptObs hm PA .X c) (varObs hm PB (v 0) c)
  have hv := M.xNorm_nonneg (ptObs hm PA .Z c) (varObs hm PB (v 4) c)
  have ht := M.swap.stateNorm_nonneg (MS.anti (msPOVM PB c.omega))
  nlinarith [sq_nonneg (M.xNorm (ptObs hm PA .X c) (varObs hm PB (v 0) c)
      - M.xNorm (ptObs hm PA .Z c) (varObs hm PB (v 4) c)),
    sq_nonneg (2 * M.xNorm (ptObs hm PA .X c) (varObs hm PB (v 0) c)
      - M.swap.stateNorm (MS.anti (msPOVM PB c.omega))),
    sq_nonneg (2 * M.xNorm (ptObs hm PA .Z c) (varObs hm PB (v 4) c)
      - M.swap.stateNorm (MS.anti (msPOVM PB c.omega)))]

/-- **The anticommuting half of `lem:qld-obs-commutation`.** On the anticommuting tuples the two
point observables anticommute on the state --- which is the blueprint's `(-1)^{gamma(omega)}` at
`gamma = 1` --- at error `48157248 eps`, with no square root. The first player's measurements are
projective, for item 6. -/
theorem acomm_signed_commutation [StarModule ℂ 𝒜] (hM : ‖M.ψ‖ = 1)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
          + ptObs hm PA .Z c * ptObs hm PA .X c)
      ≤ 48157248 * ε := by
  classical
  have hX := xStateDist_ptObs_varObs_X (hm := hm) (PA := PA) (PB := PB) hM hfail
  have hZ := xStateDist_ptObs_varObs_Z (hm := hm) (PA := PA) (PB := PB) hM hfail
  have hanti : ∑ c, acommWeight F m c * M.swap.stateSqNorm (MS.anti (msPOVM PB c.omega))
      ≤ 16049664 * ε := by
    rw [sum_acommWeight_mul]
    exact item_magicSquare hM hPA hfail
  rw [← sum_acommWeight_mul]
  calc ∑ c, acommWeight F m c * M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
            + ptObs hm PA .Z c * ptObs hm PA .X c)
      ≤ ∑ c, (12 * (acommWeight F m c
              * M.xSqNorm (ptObs hm PA .X c) (varObs hm PB (v 0) c))
            + 12 * (acommWeight F m c
              * M.xSqNorm (ptObs hm PA .Z c) (varObs hm PB (v 4) c))
            + 3 * (acommWeight F m c
              * M.swap.stateSqNorm (MS.anti (msPOVM PB c.omega)))) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h := mul_le_mul_of_nonneg_left (sq_norm_ptObs_anticomm_le (hm := hm) (M := M)
          (PA := PA) (PB := PB) c) (acommWeight_nonneg (F := F) (m := m) c)
        linarith
    _ = 12 * (∑ c, acommWeight F m c
            * M.xSqNorm (ptObs hm PA .X c) (varObs hm PB (v 0) c))
          + 12 * (∑ c, acommWeight F m c
            * M.xSqNorm (ptObs hm PA .Z c) (varObs hm PB (v 4) c))
          + 3 * (∑ c, acommWeight F m c
            * M.swap.stateSqNorm (MS.anti (msPOVM PB c.omega))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ ≤ 12 * (344 * ε) + 12 * (344 * ε) + 3 * (16049664 * ε) := by
        have h1 : ∑ c, acommWeight F m c
            * M.xSqNorm (ptObs hm PA .X c) (varObs hm PB (v 0) c) ≤ 344 * ε := hX
        have h2 : ∑ c, acommWeight F m c
            * M.xSqNorm (ptObs hm PA .Z c) (varObs hm PB (v 4) c) ≤ 344 * ε := hZ
        linarith
    _ = 48157248 * ε := by ring

end Main

/-! ## The inconsistency of a pair of POVMs

The weight of the outcome pairs on which the first player's `Q` and the second player's `R`
differ. On a unit vector it is the disagreement `BipartiteModel.dis` (`sum_diag_eq_one_sub`),
written as the off-diagonal sum, which is nonnegative without a normalization; the
question-averaged `BipartiteModel.inconsistency` is the weighted sum of these. -/

section PairInconsistency

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The inconsistency of one pair of POVMs in a bipartite model. -/
def pairInconsistency (M : BipartiteModel 𝒞 𝒜 ℬ) (Q : POVMIn A 𝒜) (R : POVMIn A ℬ) : ℝ :=
  ∑ a, ∑ b, if a = b then 0 else M.bornProb (Q.op a) (R.op b)

theorem pairInconsistency_nonneg (M : BipartiteModel 𝒞 𝒜 ℬ) (Q : POVMIn A 𝒜)
    (R : POVMIn A ℬ) : 0 ≤ pairInconsistency M Q R := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with h
  · exact le_refl 0
  · exact M.bornProb_nonneg (Q.op_nonneg a) (R.op_nonneg b)

/-- **The diagonal terms sum to `1 - γ`**, because the Born probabilities of a pair of POVMs sum
to one on a unit vector. -/
theorem sum_diag_eq_one_sub {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1) (Q : POVMIn A 𝒜)
    (R : POVMIn A ℬ) :
    ∑ a, M.bornProb (Q.op a) (R.op a) = 1 - pairInconsistency M Q R := by
  have hper : ∀ a, ∑ b, M.bornProb (Q.op a) (R.op b)
      = M.bornProb (Q.op a) (R.op a)
        + ∑ b, if a = b then 0 else M.bornProb (Q.op a) (R.op b) := by
    intro a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ a), ite_eq_left rfl, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by
      rw [ite_eq_right (Finset.ne_of_mem_erase hb).symm]
  have htot := M.sum_bornProb hM Q R
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hper a,
    Finset.sum_add_distrib] at htot
  rw [pairInconsistency]
  linarith

end PairInconsistency

/-! ## The commuting case

The other half of `lem:qld-obs-commutation`. Here the two point observables **commute**, and the
route is the paper's: chain items 5, 4 and 1 so that each point probe is cross-party close to a
*marginal* of the `Pair` measurement on the other side, and apply the commutation analysis. The
paper first replaces that measurement by a projective one (`cor:ortho-from-consistency`); here it
is projective already, being a coarse-graining of a projective measurement
(`isPVMIn_pairPOVM`).

Two departures from the paper's bookkeeping, both forced by which side things live on.

**The analysis is run on Bob's observables and transferred back.** `commutation_analysis` wants the
two commuting families on one side and the joint projective measurement on the *other*, and the
projective joint measurement at hand is **Alice's**. So the analysis is applied to *Bob's* point
measurements against Alice's joint `Pair` measurement, in the swapped model `M.swap`, and the
conclusion is carried to Alice's observables by the order-reversal rule
(`BipartiteModel.stateNorm_comm_le`) with the point observables' cross-party consistency. This half
therefore asks nothing of Bob's measurements, and it keeps the matrix route's constant.

**The chain is run in the mirrored orientation.** Every rule of `fig:decider_pauli` is stated in
both orientations, so items 5 and 1 are available with the players exchanged; item 4 is used as it
stands. The chain is
`A^{Pair}_{[beta_W = o]} ~ B^{Pair}_{[beta_W = o]} ~ A^{(Pair,W)}_o ~ B^{(Point,W)}_{probe = o}`,
three links at `172 eps` each, so `1548 eps` after one three-term triangle inequality.
-/

/-- Alice's **joint** `Pair` measurement: both bits at once, which is the product outcome set the
commutation analysis needs. -/
def pairPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (c : Content F m) :
    POVMIn (ZMod 2 × ZMod 2) R :=
  (P (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)

/-- Alice's point-probe measurement, of which `ptObs` is the observable. -/
def ptPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (c : Content F m) : POVMIn (ZMod 2) R :=
  (P (c.question hm (.point W))).map (rdProbeAt W c)

/-- Bob's **joint** `Pair` measurement. -/
def pairPOVMB {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (c : Content F m) :
    POVMIn (ZMod 2 × ZMod 2) R :=
  (P (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)

/-- Bob's point-probe measurement. -/
def ptPOVMB {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (c : Content F m) : POVMIn (ZMod 2) R :=
  (P (c.question hm (.point W))).map (rdProbeAt W c)

/-- Bob's point observable. -/
def ptObsB {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (c : Content F m) : R :=
  (ptPOVMB hm P W c).obs2

theorem ptObs_eq_obs2 {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (c : Content F m) : ptObs hm P W c = (ptPOVM hm P W c).obs2 := rfl

/-- Bob's point observable is a contraction on the Hilbert space. -/
theorem ptObsB_mul_self_le_one (M : BipartiteModel 𝒞 𝒜 ℬ) (hm : m ∣ Fintype.card F)
    (PB : Question F m → POVMIn (Answer F m d) ℬ) (W : Bas) (c : Content F m) :
    M.Bnd (M.πB (ptObsB hm PB W c)) 1 :=
  M.swap.bnd_πA_sub (ptPOVMB hm PB W c) 0 1

/-- **Alice's joint `Pair` measurement is projective** when her strategy is: it is a
coarse-graining of her projective `Pair` measurement. This is what replaces the matrix route's
orthonormalization. -/
theorem isPVMIn_pairPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) {P : Question F m → POVMIn (Answer F m d) R}
    (hP : ∀ q, IsPVMIn (P q).op) (c : Content F m) : IsPVMIn (pairPOVM hm P c).op := by
  rw [show (pairPOVM hm P c).op = _ from funext (POVMIn.map_op _ (P (c.question hm .pair)))]
  exact (hP _).coarse _

/-- The `W`-marginal of the joint `Pair` measurement is the `Pair` measurement read in `W`
alone. -/
theorem sum_pairPOVM_X {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (c : Content F m)
    (o : ZMod 2) :
    ∑ o' : ZMod 2, (pairPOVM hm P c).op (o, o')
      = ((P (c.question hm .pair)).map (rdBitPair .X)).op o :=
  POVMIn.sum_op_map_prod _ _ _ o

theorem sum_pairPOVM_Z {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (c : Content F m)
    (o : ZMod 2) :
    ∑ o' : ZMod 2, (pairPOVM hm P c).op (o', o)
      = ((P (c.question hm .pair)).map (rdBitPair .Z)).op o :=
  POVMIn.sum_op_map_prod' _ _ _ o

section Commuting

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-! ### The three links -/

theorem adj_pairB_point (W : Bas) : adj (.pairB W) (.point W) = true := by
  rw [adj_symm]; exact adj_point_pairB W

/-- **Item 5 in the mirrored orientation**: Alice's `(Pair, W)` bit agrees with Bob's point
probe. -/
theorem link_pairB_point (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          M.xSqNorm (((PA (c.question hm (.pairB W))).map rdBit).op o)
            ((ptPOVMB hm PB W c).op o)
      ≤ 172 * ε := by
  refine agree_subtest_le hM hfail (adj_pairB_point W) commSet (fun _ => rdBit)
    (rdProbeAt W) fun c hc a b h => ?_
  have hγ := gam_eq_zero_of_mem_commSet hc
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_bit_of_fmtOk_pairB hfa
  obtain ⟨b', rfl⟩ := eq_val_of_fmtOk hfb
  have hs' : prb b' (c.omega.r W) = a' := by
    simpa [subtests, Question.ty, Content.question, pairTest, hγ] using hs
  exact hs'.symm

/-- **Item 1 at the `Pair` type**, read in one basis, restricted to the commuting tuples. -/
theorem link_pair_pair (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          M.xSqNorm (((PA (c.question hm .pair)).map (rdBitPair W)).op o)
            (((PB (c.question hm .pair)).map (rdBitPair W)).op o)
      ≤ 172 * ε := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ commSet)
    fun c _ _ => ?_) (item_consistency hM hfail .pair (rdBitPair W))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun o _ => M.xSqNorm_nonneg _ _)

/-- **The chain** (the paper's `eq:lc-11`, mirrored): Alice's `Pair` measurement read in one basis
is cross-party close to Bob's point probe, on the commuting tuples. Three links at `172 eps`, one
three-term triangle inequality. -/
theorem chain_pair_point (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          M.xSqNorm (((PA (c.question hm .pair)).map (rdBitPair W)).op o)
            ((ptPOVMB hm PB W c).op o)
      ≤ 1548 * ε := by
  classical
  have key : ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2, M.xSqNorm (((PA (c.question hm .pair)).map (rdBitPair W)).op o)
          ((ptPOVMB hm PB W c).op o)
      ≤ 3 * ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : ZMod 2, M.xSqNorm (((PA (c.question hm .pair)).map (rdBitPair W)).op o)
            (((PB (c.question hm .pair)).map (rdBitPair W)).op o)
        + 3 * ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : ZMod 2, M.snorm (M.πB (((PB (c.question hm .pair)).map (rdBitPair W)).op o)
            - M.πA (((PA (c.question hm (.pairB W))).map rdBit).op o)) ^ 2
        + 3 * ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : ZMod 2, M.xSqNorm (((PA (c.question hm (.pairB W))).map rdBit).op o)
            ((ptPOVMB hm PB W c).op o) :=
    M.sum_weighted_snorm_sq_triangle3
      (w := fun _ : Content F m => (Fintype.card (Content F m) : ℝ)⁻¹)
      (fun _ => by positivity) commSet
      (fun c o => M.πA (((PA (c.question hm .pair)).map (rdBitPair W)).op o))
      (fun c o => M.πB (((PB (c.question hm .pair)).map (rdBitPair W)).op o))
      (fun c o => M.πA (((PA (c.question hm (.pairB W))).map rdBit).op o))
      (fun c o => M.πB ((ptPOVMB hm PB W c).op o))
  -- the middle link is item 4, read with the two sides of the deviation exchanged
  have e2 : ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2, M.snorm (M.πB (((PB (c.question hm .pair)).map (rdBitPair W)).op o)
          - M.πA (((PA (c.question hm (.pairB W))).map rdBit).op o)) ^ 2
      = ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2, M.xSqNorm (((PA (c.question hm (.pairB W))).map rdBit).op o)
          (((PB (c.question hm .pair)).map (rdBitPair W)).op o) :=
    Finset.sum_congr rfl fun c _ => congrArg _ (Finset.sum_congr rfl fun o _ => by
      rw [M.snorm_sub_comm]; rfl)
  rw [e2] at key
  have h1 := link_pair_pair hM hfail W
  have h2 := item_commutation hM hfail W
  have h3 := link_pairB_point hM hfail W
  linarith

/-! ### The three averaged inputs -/

/-- The per-content quantity `chain_pair_point` bounds. -/
def chainQty (hm : m ∣ Fintype.card F) (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (W : Bas) (c : Content F m) : ℝ :=
  ∑ o : ZMod 2, M.xSqNorm (((PA (c.question hm .pair)).map (rdBitPair W)).op o)
    ((ptPOVMB hm PB W c).op o)

/-- The inconsistency of the two players' joint `Pair` measurements at one content. -/
def incQty (hm : m ∣ Fintype.card F) (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (c : Content F m) : ℝ :=
  pairInconsistency M (pairPOVM hm PA c) (pairPOVMB hm PB c)

theorem chainQty_nonneg (hm : m ∣ Fintype.card F) (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (W : Bas) (c : Content F m) : 0 ≤ chainQty hm M PA PB W c :=
  Finset.sum_nonneg fun _ _ => M.xSqNorm_nonneg _ _

theorem incQty_nonneg (hm : m ∣ Fintype.card F) (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (c : Content F m) : 0 ≤ incQty hm M PA PB c :=
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
  · rw [ite_eq_left h, commWeight,
      ite_eq_left (show c ∈ commSet from Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)]
  · rw [ite_eq_right h, commWeight,
      ite_eq_right fun hh => h (gam_eq_zero_of_mem_commSet hh), zero_mul]

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
theorem xStateDist_ptObs_ptObsB (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    M.xStateDist (commWeight F m) (ptObs hm PA W) (ptObsB hm PB W) ≤ 344 * ε := by
  classical
  have hpovm : M.xPovmDist (commWeight F m) (ptPOVM hm PA W) (ptPOVMB hm PB W) ≤ 172 * ε := by
    rw [BipartiteModel.xPovmDist, sum_commWeight_mul]
    exact agree_subtest_le hM hfail (adj_self' (.point W)) commSet (rdProbeAt W) (rdProbeAt W)
      fun c _ a b h => by
        have hs := (of_accepts h).2.2
        rw [subtests, ite_eq_left rfl] at hs
        exact congrArg (rdProbeAt W c) (of_decide_eq_true hs)
  have hobsA : ptObs hm PA W = fun c => pvmObs (ptPOVM hm PA W c).op sgn :=
    funext fun c => by rw [ptObs_eq_obs2, POVMIn.pvmObs_sgn_eq_obs2]
  have hobsB : ptObsB hm PB W = fun c => pvmObs (ptPOVMB hm PB W c).op sgn :=
    funext fun c => by rw [ptObsB, POVMIn.pvmObs_sgn_eq_obs2]
  rw [hobsA, hobsB]
  refine le_trans (M.xStateDist_obsOf_le (fun c => commWeight_nonneg c) _ _ sgn
    fun a => le_of_eq (norm_sgn a)) ?_
  rw [show (344 : ℝ) * ε = (Fintype.card (ZMod 2) : ℝ) * (172 * ε) from by
    rw [ZMod.card]; push_cast; ring]
  exact mul_le_mul_of_nonneg_left hpovm (by positivity)

/-- **The inconsistency of the two joint `Pair` measurements is a conditional failure.** Item 1
again, at the Born level, which is where data processing is available: `fact:data-processing` is a
statement about *consistency*, and NW19's own remark gives a counterexample for the
state-dependent distance. -/
theorem incQty_le_condFail (hM : ‖M.ψ‖ = 1) (c : Content F m) :
    incQty hm M PA PB c
      ≤ M.condFail (qldGame hm) PA PB (c.question hm .pair) (c.question hm .pair) := by
  have hD : ∀ a b : Answer F m d,
      (qldGame hm).D (c.question hm .pair) (c.question hm .pair) a b = true →
      (rdBitPair .X a, rdBitPair .Z a) = (rdBitPair .X b, rdBitPair .Z b) := by
    intro a b h
    have hs := (of_accepts h).2.2
    rw [subtests, ite_eq_left rfl] at hs
    exact congrArg (fun x => (rdBitPair .X x, rdBitPair .Z x)) (of_decide_eq_true hs)
  have h := M.one_sub_sum_bornProb_le_condFail (G := qldGame hm) (MA := PA) (MB := PB)
    (x := c.question hm .pair) (y := c.question hm .pair)
    (fun a => (rdBitPair .X a, rdBitPair .Z a)) (fun a => (rdBitPair .X a, rdBitPair .Z a)) hD
  have hdiag := sum_diag_eq_one_sub hM (pairPOVM hm PA c) (pairPOVMB hm PB c)
  rw [incQty]
  rw [show (∑ p : ZMod 2 × ZMod 2, M.bornProb (((PA (c.question hm .pair)).map
        fun a => (rdBitPair .X a, rdBitPair .Z a)).op p)
      (((PB (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)).op p))
      = 1 - pairInconsistency M (pairPOVM hm PA c) (pairPOVMB hm PB c) from hdiag] at h
  linarith

theorem sum_incQty_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    ∑ c, commWeight F m c * incQty hm M PA PB c ≤ 86 * ε := by
  classical
  rw [sum_commWeight_mul]
  refine le_trans (Finset.sum_le_sum fun c _ => ?_)
    (subtest_le hM hfail (adj_self' .pair) commSet)
  exact mul_le_mul_of_nonneg_left (incQty_le_condFail hM c) (by positivity)

/-! ### The per-content bound

The inputs meet here: `chainQty` is what the chain bounds, and `incQty`, the inconsistency of the
two players' joint `Pair` measurements, is the term through which the matrix route paid for
projectivizing Alice's `Pair` measurement --- `18` times it from `cor:ortho-from-consistency`, and
a factor `2` for each marginal. That measurement is projective here, so the term costs nothing;
it is kept with its weight, so that every constant of the matrix statements survives, and so is
its bound `sum_incQty_le`. The slack `η` the orthonormalization's strict hypothesis asked for, and
the limit that removed it, are gone. -/

/-- **The per-content bound.** At one content, the two point observables commute on the state up
to the chain, the inconsistency term, and the two cross-party consistencies of the observables
themselves. `768 = 3 * 256`: the analysis contributes `16`, the observable expansion `16`, and the
final triangle inequality `3`. -/
theorem sq_norm_ptObs_comm_le_of_content (hPA : ∀ q, IsPVMIn (PA q).op) (c : Content F m) :
    M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c - ptObs hm PA .Z c * ptObs hm PA .X c)
      ≤ 12 * M.xSqNorm (ptObs hm PA .X c) (ptObsB hm PB .X c)
        + 12 * M.xSqNorm (ptObs hm PA .Z c) (ptObsB hm PB .Z c)
        + 768 * (2 * (chainQty hm M PA PB .X c + chainQty hm M PA PB .Z c)
          + 72 * incQty hm M PA PB c) := by
  classical
  have hinc0 := incQty_nonneg hm M PA PB c
  have hchX0 := chainQty_nonneg hm M PA PB .X c
  have hchZ0 := chainQty_nonneg hm M PA PB .Z c
  set δ : ℝ := 2 * (chainQty hm M PA PB .X c + chainQty hm M PA PB .Z c)
    + 72 * incQty hm M PA PB c with hδ
  -- the two hypotheses of the analysis, in the swapped frame: the marginals of Alice's joint
  -- `Pair` measurement are its one-basis readings, so each hypothesis is a chain quantity
  have hXs : ∑ b : ZMod 2, M.swap.xSqNorm ((ptPOVMB hm PB .X c).op b)
      (∑ o' : ZMod 2, (pairPOVM hm PA c).op (b, o')) ≤ δ := by
    have heq : ∑ b : ZMod 2, M.swap.xSqNorm ((ptPOVMB hm PB .X c).op b)
        (∑ o' : ZMod 2, (pairPOVM hm PA c).op (b, o')) = chainQty hm M PA PB .X c := by
      rw [chainQty]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [M.xSqNorm_swap, sum_pairPOVM_X]
    rw [heq, hδ]
    linarith
  have hZs : ∑ b : ZMod 2, M.swap.xSqNorm ((ptPOVMB hm PB .Z c).op b)
      (∑ o' : ZMod 2, (pairPOVM hm PA c).op (o', b)) ≤ δ := by
    have heq : ∑ b : ZMod 2, M.swap.xSqNorm ((ptPOVMB hm PB .Z c).op b)
        (∑ o' : ZMod 2, (pairPOVM hm PA c).op (o', b)) = chainQty hm M PA PB .Z c := by
      rw [chainQty]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [M.xSqNorm_swap, sum_pairPOVM_Z]
    rw [heq, hδ]
    linarith
  -- the analysis, on Bob's observables against Alice's projective joint `Pair` measurement
  have hanal := M.swap.commutation_analysis (A := ptPOVMB hm PB .X c) (Cm := ptPOVMB hm PB .Z c)
    (isPVMIn_pairPOVM hm hPA c) hXs hZs
  have hone : M.swap.stateSqNorm ((ptPOVMB hm PB .X c).op 1 * (ptPOVMB hm PB .Z c).op 1
      - (ptPOVMB hm PB .Z c).op 1 * (ptPOVMB hm PB .X c).op 1) ≤ 16 * δ := by
    have h11 := Finset.single_le_sum (f := fun p : ZMod 2 × ZMod 2 => M.swap.stateSqNorm
        ((ptPOVMB hm PB .X c).op p.1 * (ptPOVMB hm PB .Z c).op p.2
          - (ptPOVMB hm PB .Z c).op p.2 * (ptPOVMB hm PB .X c).op p.1))
      (fun p _ => M.swap.stateSqNorm_nonneg _)
      (Finset.mem_univ ((1 : ZMod 2), (1 : ZMod 2)))
    have h12 := le_trans h11 hanal
    -- reduce the redex before comparing with the goal; unifying through it is very slow
    beta_reduce at h12
    exact h12
  -- the observables, by the exact expansion
  have hobs : M.swap.stateSqNorm (ptObsB hm PB .X c * ptObsB hm PB .Z c
      - ptObsB hm PB .Z c * ptObsB hm PB .X c) ≤ 256 * δ := by
    rw [ptObsB, ptObsB, POVMIn.obs2_commutator_eq, BipartiteModel.stateSqNorm,
      BipartiteModel.stateNorm_smul, show ‖(4 : ℂ)‖ = 4 from by norm_num, mul_pow,
      show (4 : ℝ) ^ 2 = 16 from by norm_num]
    rw [BipartiteModel.stateSqNorm] at hone
    linarith
  -- transfer to Alice's observables
  have htr := M.stateNorm_comm_le (ptObs hm PA .X c) (ptObs hm PA .Z c)
    (ptObsB hm PB .X c) (ptObsB hm PB .Z c)
    (ptObs_mul_self_le_one M hm PA .X c) (ptObs_mul_self_le_one M hm PA .Z c)
    (ptObsB_mul_self_le_one M hm PB .X c) (ptObsB_mul_self_le_one M hm PB .Z c)
  rw [M.swap.stateNorm_sub_comm] at htr
  have hu := M.xNorm_nonneg (ptObs hm PA .X c) (ptObsB hm PB .X c)
  have hv := M.xNorm_nonneg (ptObs hm PA .Z c) (ptObsB hm PB .Z c)
  have ht := M.swap.stateNorm_nonneg (ptObsB hm PB .X c * ptObsB hm PB .Z c
    - ptObsB hm PB .Z c * ptObsB hm PB .X c)
  have h0 := M.stateNorm_nonneg (ptObs hm PA .X c * ptObs hm PA .Z c
    - ptObs hm PA .Z c * ptObs hm PA .X c)
  rw [BipartiteModel.stateSqNorm] at hobs
  rw [BipartiteModel.stateSqNorm, BipartiteModel.xSqNorm_eq_sq, BipartiteModel.xSqNorm_eq_sq]
  nlinarith [sq_nonneg (M.xNorm (ptObs hm PA .X c) (ptObsB hm PB .X c)
      - M.xNorm (ptObs hm PA .Z c) (ptObsB hm PB .Z c)),
    sq_nonneg (2 * M.xNorm (ptObs hm PA .X c) (ptObsB hm PB .X c)
      - M.swap.stateNorm (ptObsB hm PB .X c * ptObsB hm PB .Z c
        - ptObsB hm PB .Z c * ptObsB hm PB .X c)),
    sq_nonneg (2 * M.xNorm (ptObs hm PA .Z c) (ptObsB hm PB .Z c)
      - M.swap.stateNorm (ptObsB hm PB .X c * ptObsB hm PB .Z c
        - ptObsB hm PB .Z c * ptObsB hm PB .X c))]

theorem sum_chainQty_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ c, commWeight F m c * chainQty hm M PA PB W c ≤ 1548 * ε := by
  rw [sum_commWeight_mul]
  exact chain_pair_point hM hfail W

/-- **The commuting half of `lem:qld-obs-commutation`.** On the commuting tuples the two point
observables commute on the state, at `9519168 eps` --- and, like the anticommuting half, with no
square root. The first player's measurements are projective, so that her joint `Pair` measurement
is. -/
theorem comm_signed_commutation (hM : ‖M.ψ‖ = 1) (hPA : ∀ q, IsPVMIn (PA q).op)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
          - ptObs hm PA .Z c * ptObs hm PA .X c)
      ≤ 9519168 * ε := by
  classical
  rw [← sum_commWeight_mul]
  refine le_trans (Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (sq_norm_ptObs_comm_le_of_content (PB := PB) hPA c)
      (commWeight_nonneg (F := F) (m := m) c)) ?_
  have hdist : ∑ c, commWeight F m c *
        (12 * M.xSqNorm (ptObs hm PA .X c) (ptObsB hm PB .X c)
          + 12 * M.xSqNorm (ptObs hm PA .Z c) (ptObsB hm PB .Z c)
          + 768 * (2 * (chainQty hm M PA PB .X c + chainQty hm M PA PB .Z c)
            + 72 * incQty hm M PA PB c))
      = 12 * (∑ c, commWeight F m c * M.xSqNorm (ptObs hm PA .X c) (ptObsB hm PB .X c))
        + 12 * (∑ c, commWeight F m c * M.xSqNorm (ptObs hm PA .Z c) (ptObsB hm PB .Z c))
        + 1536 * (∑ c, commWeight F m c * chainQty hm M PA PB .X c)
        + 1536 * (∑ c, commWeight F m c * chainQty hm M PA PB .Z c)
        + 55296 * (∑ c, commWeight F m c * incQty hm M PA PB c) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hdist]
  have h1 : ∑ c, commWeight F m c * M.xSqNorm (ptObs hm PA .X c) (ptObsB hm PB .X c)
      ≤ 344 * ε :=
    xStateDist_ptObs_ptObsB hM hfail .X
  have h2 : ∑ c, commWeight F m c * M.xSqNorm (ptObs hm PA .Z c) (ptObsB hm PB .Z c)
      ≤ 344 * ε :=
    xStateDist_ptObs_ptObsB hM hfail .Z
  have h3 := sum_chainQty_le hM hfail (PA := PA) (PB := PB) .X
  have h4 := sum_chainQty_le hM hfail (PA := PA) (PB := PB) .Z
  have h5 := sum_incQty_le hM hfail (PA := PA) (PB := PB)
  linarith

/-! ### Both halves

`lem:qld-obs-commutation` as the paper states it: one average over *all* contents, with the sign
`(-1)^{gamma(omega)}` inside. The two halves are the two branches of that sign, and the type graph's
content distribution is uniform, so the statement is the sum of the two restricted ones. -/

/-- **`lem:qld-obs-commutation`.** On average over the verifier's content, the two point
observables commute up to the sign `(-1)^{gamma(omega)}`, at `57676416 eps = 9519168 eps +
48157248 eps`. The blueprint states this at `O(sqrt(eps))`; it is `O(eps)`, and the two halves are
where that is decided. The first player's measurements are projective, which both halves use. -/
theorem signed_commutation [StarModule ℂ 𝒜] (hM : ‖M.ψ‖ = 1) (hPA : ∀ q, IsPVMIn (PA q).op)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
          - sgn (gam c.omega) • (ptObs hm PA .Z c * ptObs hm PA .X c))
      ≤ 57676416 * ε := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Content F m))
    (fun c => gam c.omega = 0)
    (fun c => (Fintype.card (Content F m) : ℝ)⁻¹ *
      M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
        - sgn (gam c.omega) • (ptObs hm PA .Z c * ptObs hm PA .X c)))
  rw [← hsplit]
  have hcomm : ∑ c ∈ univ.filter (fun c : Content F m => gam c.omega = 0),
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
          - sgn (gam c.omega) • (ptObs hm PA .Z c * ptObs hm PA .X c))
      ≤ 9519168 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c hc => ?_))
      (comm_signed_commutation hM hPA hfail)
    rw [gam_eq_zero_of_mem_commSet (by rw [commSet]; exact hc), sgn_zero, one_smul]
  have hacomm : ∑ c ∈ univ.filter (fun c : Content F m => ¬ gam c.omega = 0),
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
          - sgn (gam c.omega) • (ptObs hm PA .Z c * ptObs hm PA .X c))
      ≤ 48157248 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c hc => ?_))
      (acomm_signed_commutation hM hPA hfail)
    have hγ : gam c.omega = 1 := by
      have h := gam_ne_zero_of_mem_acommSet (show c ∈ acommSet from by rw [acommSet]; exact hc)
      revert h
      generalize gam c.omega = x
      revert x
      decide
    rw [hγ, sgn_one, neg_one_smul, sub_neg_eq_add]
  linarith

end Commuting

end QLD

end MIPRE

end

end
