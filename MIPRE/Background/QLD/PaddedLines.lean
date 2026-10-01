/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Combine
public import MIPRE.Background.QLD.Legalize

@[expose] public section

/-!
# The padded line measurement's consistency

Blueprint `lem:qld-padded-lines`, the analytic half. `Combine.lean` built the measurement; this file
proves it consistent with the padded point measurement on the padded line-point law.

The paper chains three Cauchy--Schwarz claims here. They are not needed for this construction, and
`reports/padded-lines-product-law.md` says why: the joint law of the two sublines-with-points is
*exactly* a product of the two marginals at a fixed padded seed, so the product form of the
pairs-of-lines lemma applies directly. What is left is a single coarse-graining step, and that is
what this file adds.

* **Coarse-graining both sides the same way can only increase agreement.**
  `sum_bornProb_le_fibre`, for bare nonnegative families rather than `POVMIn` structures --- which
  is what the pasted line measurement is.
* **The two coarse-grained families.** `ptComb` is the combined point measurement read along the
  linear form `(a, b)`, the paper's `Q-hat^{x,z,alpha,beta}`; `lineComb` is the pasted line
  measurement coarse-grained by the combining map. `lineComb_eq_sum_pasteFib` identifies the second
  as a coarse-graining of the first coarse-graining, which is what makes them comparable.
* **The bound.** `padded_lines_consistency`: the two disagree by at most `m^2 * delta_P` on the
  padded line-point law, at every padded seed and line type.

The `m^2` and the functional form are discussed in the report: it is `poly(m) * poly(eps, md/q)`
rather than the `m * poly(eps, md/q)` the blueprint statement advertises, which
`lem:qld-simultaneous`'s `a(md)^a` prefactor absorbs.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The pasted line measurement and
its coarse-grainings (`pasteFib`, `lineComb`) are families of elements of
`Matrix (Anc F m) (Anc F m) R` over a player's ordered `⋆`-algebra, and the consistency bound is an
**agreement bound in the expanded model `M.reg (Anc F m)`**: the combined point measurement is the
first player's sandwich `M-hat^Z_b M-hat^X_a M-hat^Z_b` itself, read along `(alpha, beta)`
(`ptComb`), not a dilation of it. That is the form `pairs_of_lines_prod_of_items` now returns, and
it is also what the padded strategy measures, so no compression is needed downstream. The
exchanged player is the same statement for `M.swap`, read back through `hatVec_swapVec_xSqNorm`
and `hatVec_swapVec_bornProb`. Positivity is the model's order: the two coarse-graining lemmas
take nonnegative families, and the name `posSemidef_pasteFib` is kept for a nonnegativity
statement.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

/-! ## Coarse-graining a Born sum -/

section Born

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **Coarse-graining both sides the same way can only increase agreement.** The `POVMIn` version
is `BipartiteModel.sum_bornProb_le_map`; here the families are bare nonnegative families, which is
the shape the pasted line measurement comes in. -/
theorem sum_bornProb_le_fibre {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : BipartiteModel 𝒞 𝒜 ℬ) (P : ι → 𝒜) (Q : ι → ℬ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i) (f : ι → κ) :
    ∑ i, M.bornProb (P i) (Q i)
      ≤ ∑ k : κ, M.bornProb (∑ i ∈ univ.filter fun i => f i = k, P i)
          (∑ i ∈ univ.filter fun i => f i = k, Q i) := by
  classical
  refine le_trans (le_of_eq (sum_fiber f fun _ i => M.bornProb (P i) (Q i)))
    (Finset.sum_le_sum fun k _ => ?_)
  rw [M.bornProb_sum_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Finset.single_le_sum (f := fun j => M.bornProb (P i) (Q j))
    (fun j _ => M.bornProb_nonneg (hP i) (hQ j)) hi

/-- **A Born sum on the diagonal of two POVMs is at most one.** -/
theorem sum_bornProb_diag_le_one {ι : Type*} [Fintype ι] {M : BipartiteModel 𝒞 𝒜 ℬ}
    (hM : ‖M.ψ‖ = 1) (P : ι → 𝒜) (Q : ι → ℬ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hPs : ∑ i, P i = 1) (hQs : ∑ i, Q i = 1) :
    ∑ i, M.bornProb (P i) (Q i) ≤ 1 := by
  classical
  refine le_trans ?_ (le_of_eq (M.bornProb_one_one hM))
  rw [← hPs, ← hQs, M.bornProb_sum_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => M.bornProb (P i) (Q j))
    (fun j _ => M.bornProb_nonneg (hP i) (hQ j)) (mem_univ i)

end Born

/-! ## The two coarse-grained families -/

section Comb

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {hm : m ∣ Fintype.card F}

/-- The pasted line measurement's own outcome map: each side's polynomial read at the parameter of
its own subline. -/
def pasteEval (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (cX cZ : Content F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) : F × F :=
  (LinePoly.eval q.1 (PX.param cX), LinePoly.eval q.2 (PZ.param cZ))

/-- **The combined point measurement along the linear form `(a, b)`**: the paper's
`Q-hat^{x,z,alpha,beta}`, as the coarse-graining of a family indexed by pairs, in any additive
monoid. -/
def ptComb {N : Type*} [AddCommMonoid N] (Q : F × F → N) (a b : F) (v : F) : N :=
  ∑ r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v, Q r

section Ops

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- The pasted line measurement coarse-grained by that map --- the family the product form of
`lem:qld-pairs-of-lines` bounds. -/
def pasteFib (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (cX cZ : Content F m) (r : F × F) :
    Matrix (Anc F m) (Anc F m) R :=
  ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
      LinePoly.eval q.1 (PX.param cX) = r.1 ∧ LinePoly.eval q.2 (PZ.param cZ) = r.2,
    pasteLine PX PZ d S cX cZ q

theorem pasteFib_eq (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (cX cZ : Content F m) (r : F × F) :
    pasteFib PX PZ d S cX cZ r
      = ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
          pasteEval PX PZ cX cZ q = r, pasteLine PX PZ d S cX cZ q := by
  classical
  refine Finset.sum_congr (Finset.filter_congr fun q _ => ?_) fun _ _ => rfl
  rw [pasteEval, Prod.ext_iff]

/-- Each element of the coarse-grained pasted family is nonnegative. -/
theorem posSemidef_pasteFib {S : Question F m → POVMIn (Answer F m d) R}
    (hS : ∀ q, IsPVMIn (S q).op) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (cX cZ : Content F m) (r : F × F) :
    0 ≤ pasteFib PX PZ d S cX cZ r :=
  Finset.sum_nonneg fun q _ => posSemidef_pasteLine hS PX PZ cX cZ q

theorem sum_pasteFib {S : Question F m → POVMIn (Answer F m d) R}
    (hS : ∀ q, IsPVMIn (S q).op) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (cX cZ : Content F m) :
    ∑ r : F × F, pasteFib PX PZ d S cX cZ r = 1 := by
  classical
  rw [Finset.sum_congr rfl fun r (_ : r ∈ (univ : Finset (F × F))) =>
    pasteFib_eq PX PZ d S cX cZ r,
    ← sum_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) => pasteEval PX PZ cX cZ q)
      fun _ q => pasteLine PX PZ d S cX cZ q]
  exact sum_pasteLine hS PX PZ cX cZ

/-- **The pasted line measurement coarse-grained by the combining map at `(a, b)`.** Averaged over
the fresh randomness this is `padLineMats` read at the sampled point; see
`sum_filter_padLineMats`. -/
def lineComb (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (cX cZ : Content F m) (a b : F) (v : F) :
    Matrix (Anc F m) (Anc F m) R :=
  ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
      a * LinePoly.eval q.1 (PX.param cX) + b * LinePoly.eval q.2 (PZ.param cZ) = v,
    pasteLine PX PZ d S cX cZ q

/-- **The line side is a coarse-graining of the fibre family**, along the same linear form. This is
what lets the two be compared by `sum_bornProb_le_fibre`. -/
theorem lineComb_eq_sum_pasteFib (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (cX cZ : Content F m) (a b : F) (v : F) :
    lineComb PX PZ d S cX cZ a b v
      = ∑ r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v,
        pasteFib PX PZ d S cX cZ r := by
  classical
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v) =>
    pasteFib_eq PX PZ d S cX cZ r,
    sum_filter_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) => pasteEval PX PZ cX cZ q)
      (fun r : F × F => a * r.1 + b * r.2 = v) fun q => pasteLine PX PZ d S cX cZ q]
  rfl

end Ops

end Comb

/-! ## The axis-parallel degree bound

The degree computation of `lem:qld-axis-degree`: on an axis-parallel line the expansion adds a
polynomial of degree at most **one**, because the restriction of a multilinear polynomial to
`u_0 + t e_j` is affine in `t` (`natDegree_lineRestrict_single_le`), so an outcome built from a legal
axis answer has degree at most `d` as soon as `d >= 1`.

What this does *not* give is the support claim of `lem:qld-axis-degree`. The strategy's line
measurement is indexed by *all* answers, and a `dpoly` answer to an axis-parallel question --- which
the decider rejects, but for which the measurement still has an element --- produces an outcome of
degree up to `md`. Turning the computation below into the lemma means modifying the measurement to
send those answers to a default outcome and paying the format-failure probability, which is not done
here; that is why `lem:qld-padded-lines` states its degree-`d` clause conditionally on
`lem:qld-axis-degree`. -/

section AxisDegree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

theorem DegLE.add {n k : ℕ} {f g : LinePoly F n} (hf : DegLE f k) (hg : DegLE g k) :
    DegLE (f + g) k := fun i hi => by
  show f i + g i = 0
  rw [hf i hi, hg i hi, add_zero]

theorem degLE_zero {n k : ℕ} : DegLE (0 : LinePoly F n) k := fun _ _ => rfl

theorem degLE_padLine {k n : ℕ} (f : LinePoly F k) : DegLE (padLine n f) k := fun i hi => by
  show (if h : (i : ℕ) < k + 1 then f ⟨i, h⟩ else 0) = 0
  rw [dif_neg (by omega)]

/-- A line outcome read off an answer that is not a diagonal-line answer has degree at most `d`. -/
theorem degLE_rdLine {n : ℕ} (a : Answer F m d)
    (hne : ∀ g : LinePoly F (m * d), a ≠ .dpoly g) : DegLE (rdLine n a) d := by
  cases a with
  | val x => exact degLE_zero
  | apoly f => exact degLE_padLine f
  | dpoly g => exact absurd rfl (hne g)
  | pauliAns h => exact degLE_zero
  | bit b => exact degLE_zero
  | bitPair beta => exact degLE_zero
  | bitTriple alpha => exact degLE_zero

/-- **The expansion adds degree at most one on an axis-parallel line.** -/
theorem degLE_lineCoeffs_aline {n : ℕ} (u₀ : Point F m) (j : Fin m) (h : Anc F m) :
    DegLE (lineCoeffs n u₀ (Pi.single j 1 : Point F m) (MIPRE.LowDegree.ldEnc h)) 1 :=
  fun i hi => by
  show (MIPRE.LowDegree.lineRestrict u₀ (Pi.single j 1 : Point F m)
    (MIPRE.LowDegree.ldEnc h)).coeff (i : ℕ) = 0
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hi)
  exact le_trans (MIPRE.LowDegree.natDegree_lineRestrict_single_le u₀ j _)
    (MIPRE.LowDegree.degreeOf_ldEnc_le h j)

/-- **The degree computation of `lem:qld-axis-degree`**: a legal axis answer convolved with the
expansion's line outcome has degree at most `d`, for `d >= 1`. -/
theorem degLE_hatLine_outcome {n : ℕ} (hd : 1 ≤ d) (u₀ : Point F m) (j : Fin m) (hh : Anc F m)
    (a : Answer F m d) (hne : ∀ g : LinePoly F (m * d), a ≠ .dpoly g) :
    DegLE (rdLine n a
      + lineCoeffs n u₀ (Pi.single j 1 : Point F m) (MIPRE.LowDegree.ldEnc hh)) d :=
  DegLE.add (degLE_rdLine a hne) ((degLE_lineCoeffs_aline u₀ j hh).mono hd)

end AxisDegree

/-! ## The support half of `lem:qld-axis-degree`

The degree computation above says what an outcome built from a *legal* axis answer looks like. The
support claim is that the expanded axis-line measurement has no element anywhere else, and that is
false for an arbitrary strategy: a `dpoly` answer to an axis question is rejected by the decider but
still has a measurement element, whose outcome has degree up to `m d`. For a strategy with
`LegalSupport` --- which `legalizeStrat` provides at no cost --- it is true and exact: every element
of the strategy's factor sits on a legal `apoly` answer, of degree at most `d`, and every element of
the ancilla's factor sits on a restriction of the multilinear encoding, of degree at most `1`. The
padded line measurement inherits it through `degLE_padCombine_aline`. -/

section AxisSupport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {hm : m ∣ Fintype.card F}

/-- **The strategy's axis-line reading of a legally supported strategy is supported on degree at
most `d`.** -/
theorem lineAnsPOVM_aline_eq_zero_of_not_degLE {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] {n : ℕ} {S : Question F m → POVMIn (Answer F m d) R}
    (hleg : LegalSupport S) (W : Bas) (c : Content F m) {f : LinePoly F n} (hf : ¬ DegLE f d) :
    (lineAnsPOVM n hm S (.aline W) c).op f = 0 := by
  rw [lineAnsPOVM, POVMIn.map_op]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hfa : rdLine n a = f := (Finset.mem_filter.mp ha).2
  by_cases hok : (c.question hm (.aline W)).fmtOk a = true
  · exfalso
    apply hf
    obtain ⟨p, rfl⟩ := eq_apoly_of_fmtOk hok
    rw [← hfa]
    exact degLE_padLine p
  · exact hleg _ _ (Bool.eq_false_iff.mpr hok)

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- **The support half of `lem:qld-axis-degree`, at the expanded measurement**: for `d ≥ 1` and a
legally supported strategy, the expanded axis-parallel line measurement has no element off the
polynomials of degree at most `d`. -/
theorem hatLinePOVM_aline_eq_zero_of_not_degLE (hd : 1 ≤ d) {n : ℕ}
    {S : Question F m → POVMIn (Answer F m d) R} (hleg : LegalSupport S) (W : Bas)
    (c : Content F m) {f : LinePoly F n} (hf : ¬ DegLE f d) :
    (hatLinePOVM n hm S W (.aline W) (abaseOf hm W) (dirOf hm) c).op f = 0 := by
  rw [hatLinePOVM, POVMIn.map_op]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpf : p.1 + p.2 = f := (Finset.mem_filter.mp hp).2
  rw [kronIn_op]
  by_cases h1 : DegLE p.1 d
  · have h2 : ¬ DegLE p.2 1 := fun h2 => hf (hpf ▸ DegLE.add h1 (h2.mono hd))
    have hanc : ((synLinePOVM n W (abaseOf hm W c) (dirOf hm c)).mats p.2).val = 0 := by
      rw [synLinePOVM, synOfPOVM_mats, MIPRE.Weyl.synOf]
      refine Finset.sum_eq_zero fun h hh => ?_
      exfalso
      apply h2
      rw [← (Finset.mem_filter.mp hh).2]
      exact degLE_lineCoeffs_aline (abaseOf hm W c) (MIPRE.LIDT.CL.chi hm c.s) h
    rw [hanc, smulKron_zero_right]
  · rw [lineAnsPOVM_aline_eq_zero_of_not_degLE hleg W c h1, smulKron_zero_left]

/-- The same, for the axis-parallel presentation's line measurement. -/
theorem lineMats_aPres_eq_zero_of_not_degLE (hd : 1 ≤ d)
    {S : Question F m → POVMIn (Answer F m d) R} (hleg : LegalSupport S) (W : Bas)
    (c : Content F m) {f : LinePoly F (m * d)} (hf : ¬ DegLE f d) :
    (aPres hm W).lineMats d S c f = 0 :=
  hatLinePOVM_aline_eq_zero_of_not_degLE hd hleg W c hf

/-- **The support half of `lem:qld-axis-degree`, at the padded line measurement**: on an
axis-parallel padded line, the padded line measurement of a legally supported strategy has no
element off the polynomials of degree at most `d`. This is what makes its outcome a legal answer to
an axis-parallel line question of the seeded test at `(q, 4m, d, 1)`. -/
theorem padLineMats_aline_eq_zero_of_not_degLE (hm4 : 4 * m ∣ Fintype.card F) (hd : 1 ≤ d)
    {S : Question F m → POVMIn (Answer F m d) R} (hleg : LegalSupport S) (P : LPData F (4 * m))
    {f : LinePoly F (m * d + 1)} (hf : ¬ DegLE f d) :
    padLineMats hm4 .aline (aPres hm .X) (aPres hm .Z) S P f = 0 := by
  rw [padLineMats]
  refine smul_eq_zero_of_right _
    (Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun q hq => ?_)
  have hqf : padCombine hm4 hm .aline d P e.1 e.2 q = f := (Finset.mem_filter.mp hq).2
  rw [pasteLine]
  by_cases hX : DegLE q.1 d
  · have hZ : ¬ DegLE q.2 d := fun hZ =>
      hf (hqf ▸ degLE_padCombine_aline hm4 hm hd P e.1 e.2 q hX hZ)
    rw [lineMats_aPres_eq_zero_of_not_degLE hd hleg .Z _ hZ, mul_zero, zero_mul]
  · rw [lineMats_aPres_eq_zero_of_not_degLE hd hleg .X _ hX, zero_mul, zero_mul]

end AxisSupport

/-! ## The consistency bound -/

section Main

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ] {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-padded-lines`, the consistency bound.** On the padded line-point law, at every padded
seed and line type, the first player's combined point measurement --- the sandwich of the expanded
point measurements, read along `(alpha, beta)` at the sampled point --- agrees in the expanded
model `M.reg (Anc F m)` with the second player's pasted line measurement coarse-grained by the
combining map, up to `m^2 * delta_P`.

The proof is the coarse-graining step and then the two domination lemmas: agreement only increases
under a common coarse-graining, the padded law is at most `m^2` times the product law
(`avgSub_le_mul_avgAll`), and `(alpha, beta)` is uniform and independent of both sublines
(`avgSubAB_le_of_forall`). The paper's Claims 17-1 to 17-3 are not used; see
`reports/padded-lines-product-law.md`. -/
theorem padded_lines_consistency (hm4 : 4 * m ∣ Fintype.card F) (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op)
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hX1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        (M.reg (Anc F m)).xSqNorm (PX.lineMats d PA c f) (PX.lineMats d PB c f) ≤ 172 * ε)
    (hX2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA .X (c.pt .X) a) (PX.lineEvalMats d PB c a)
          ≤ 172 * ε)
    (hZ2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA .Z (c.pt .Z) b) (PZ.lineEvalMats d PB c b)
          ≤ 172 * ε)
    {εc : ℝ} (hcoll : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      collProb PX d c ≤ εc) (ty : CL.Ty) (s : F) :
    1 - avgSubAB hm4 hm ty s (fun a b cX cZ =>
          ∑ v : F, (M.reg (Anc F m)).bornProb
            (ptComb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt)) a b v)
            (lineComb PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
      ≤ (m : ℝ) * (m : ℝ) * deltaPairs ε εc := by
  classical
  set N := M.reg (Anc F m) with hN
  have hbound := pairs_of_lines_prod_of_items hM hfail hPA hPB PX PZ hfacX hfacZ hX1 hX2 hZ2 hcoll
  have hunit : ‖N.ψ‖ = 1 := hatVec_unit hM
  -- the first player's sandwich is a POVM
  have hQnn : ∀ (p : LPData F m × LPData F m) (r : F × F),
      0 ≤ sand (hatMats PA .X p.1.pt) (hatMats PA .Z p.2.pt) r := fun p r => by
    rw [(isPVM_hatMats hPA .X p.1.pt).sand_eq_gram (isPVM_hatMats hPA .Z p.2.pt)]
    exact star_mul_self_nonneg _
  have hQsum : ∀ p : LPData F m × LPData F m,
      ∑ r : F × F, sand (hatMats PA .X p.1.pt) (hatMats PA .Z p.2.pt) r = 1 := fun p =>
    (isPVM_hatMats hPA .X p.1.pt).sum_sand (isPVM_hatMats hPA .Z p.2.pt)
  -- the product-law bound on the fine agreement, `pasteFib` being the filter sum by definition
  have hfineb : 1 - avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        ∑ r : F × F, N.bornProb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt) r)
          (pasteFib PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
      ≤ deltaPairs ε εc := by
    rw [avgAll_prod_eq_uniform]
    exact hbound
  -- every fine agreement is at most one
  have hfine1 : ∀ p : LPData F m × LPData F m,
      (∑ r : F × F, N.bornProb (sand (hatMats PA .X p.1.pt) (hatMats PA .Z p.2.pt) r)
        (pasteFib PX PZ d PB (pairCX p) (pairCZ p) r)) ≤ 1 := fun p =>
    sum_bornProb_diag_le_one (ι := F × F) hunit _ _ (hQnn p)
      (fun r => posSemidef_pasteFib hPB PX PZ (pairCX p) (pairCZ p) r) (hQsum p)
      (sum_pasteFib hPB PX PZ (pairCX p) (pairCZ p))
  -- coarse-graining only increases agreement
  have hcoarse : ∀ (a b : F) (p : LPData F m × LPData F m),
      (∑ r : F × F, N.bornProb (sand (hatMats PA .X p.1.pt) (hatMats PA .Z p.2.pt) r)
          (pasteFib PX PZ d PB (pairCX p) (pairCZ p) r))
        ≤ ∑ v : F, N.bornProb (ptComb (sand (hatMats PA .X p.1.pt) (hatMats PA .Z p.2.pt)) a b v)
            (lineComb PX PZ d PB (pairCX p) (pairCZ p) a b v) := by
    intro a b p
    refine le_trans (sum_bornProb_le_fibre (ι := F × F) (κ := F) N _
      (pasteFib PX PZ d PB (pairCX p) (pairCZ p)) (hQnn p)
      (fun r => posSemidef_pasteFib hPB PX PZ _ _ r)
      (fun r : F × F => a * r.1 + b * r.2)) (le_of_eq (Finset.sum_congr rfl fun v _ => ?_))
    rw [ptComb, lineComb_eq_sum_pasteFib]
  -- the deficit of the fine agreement, on the product law
  have hinner : ∀ cX : LPData F m,
      avgAll (fun cZ : LPData F m => 1 - ∑ r : F × F,
          N.bornProb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt) r)
            (pasteFib PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
        = 1 - avgAll (fun cZ : LPData F m => ∑ r : F × F,
          N.bornProb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt) r)
            (pasteFib PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) := fun cX => by
    rw [avgAll_sub (fun _ : LPData F m => (1 : ℝ)), avgAll_one]
  have houter : avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        1 - ∑ r : F × F, N.bornProb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt) r)
          (pasteFib PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
      = 1 - avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        ∑ r : F × F, N.bornProb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt) r)
          (pasteFib PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) := by
    rw [congrArg avgAll (funext hinner), avgAll_sub (fun _ : LPData F m => (1 : ℝ)), avgAll_one]
  -- the padded law, at each fixed `(alpha, beta)`
  have hstep : ∀ a b : F, avgSub hm4 hm ty s (fun cX cZ =>
        1 - ∑ v : F, N.bornProb (ptComb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt)) a b v)
          (lineComb PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
      ≤ (m : ℝ) * (m : ℝ) * deltaPairs ε εc := by
    intro a b
    refine le_trans (avgSub_mono hm4 hm ty s (g' := fun cX cZ =>
      1 - ∑ r : F × F, N.bornProb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt) r)
        (pasteFib PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) fun cX cZ => by
      have h := hcoarse a b (cX, cZ)
      linarith) ?_
    refine le_trans (avgSub_le_mul_avgAll hm4 hm ty s fun cX cZ => by
      have h := hfine1 (cX, cZ)
      linarith) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [houter]
    linarith [hfineb]
  -- and back to the joint law
  have hsub := avgSubAB_sub hm4 hm ty s (fun _ _ _ _ => (1 : ℝ))
    (fun (a b : F) (cX cZ : LPData F m) => ∑ v : F,
      N.bornProb (ptComb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt)) a b v)
        (lineComb PX PZ d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
  rw [avgSubAB_one] at hsub
  have hle := avgSubAB_le_of_forall hm4 hm ty s hstep
  linarith [hsub, hle]

/-! ### The other register version

The paper's `lem:qld-4-13` asserts the relation in both orientations. The second is the first
applied to the exchanged model `M.swap`, with the two strategies exchanged, read back through
`hatVec_swapVec_xSqNorm` and `hatVec_swapVec_bornProb` --- the route `Swap.lean` takes for the
expansion stage's point items. The two mirrored inputs are `lem:qld-expanded-lines`' second item
with the players exchanged. -/

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-padded-lines`, the consistency bound in the other register version**: the first
player's pasted line measurement against the second player's combined point measurement, in the
expanded model. -/
theorem padded_lines_consistency_swap (hm4 : 4 * m ∣ Fintype.card F) (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op)
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hX1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        (M.reg (Anc F m)).xSqNorm (PX.lineMats d PA c f) (PX.lineMats d PB c f) ≤ 172 * ε)
    (hX2' : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm (PX.lineEvalMats d PA c a) (hatMats PB .X (c.pt .X) a)
          ≤ 172 * ε)
    (hZ2' : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
        (M.reg (Anc F m)).xSqNorm (PZ.lineEvalMats d PA c b) (hatMats PB .Z (c.pt .Z) b)
          ≤ 172 * ε)
    {εc : ℝ} (hcoll : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      collProb PX d c ≤ εc) (ty : CL.Ty) (s : F) :
    1 - avgSubAB hm4 hm ty s (fun a b cX cZ =>
          ∑ v : F, (M.reg (Anc F m)).bornProb
            (lineComb PX PZ d PA (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v)
            (ptComb (sand (hatMats PB .X cX.pt) (hatMats PB .Z cZ.pt)) a b v))
      ≤ (m : ℝ) * (m : ℝ) * deltaPairs ε εc := by
  classical
  -- the three inputs, in the exchanged model
  have hX1sw : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
      (M.swap.reg (Anc F m)).xSqNorm (PX.lineMats d PB c f) (PX.lineMats d PA c f)
        ≤ 172 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
        (Finset.sum_congr rfl fun f _ => ?_))) hX1
    exact hatVec_swapVec_xSqNorm M _ _
  have hX2sw : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
      (M.swap.reg (Anc F m)).xSqNorm (hatMats PB .X (c.pt .X) a) (PX.lineEvalMats d PA c a)
        ≤ 172 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
        (Finset.sum_congr rfl fun a _ => ?_))) hX2'
    exact hatVec_swapVec_xSqNorm M _ _
  have hZ2sw : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
      (M.swap.reg (Anc F m)).xSqNorm (hatMats PB .Z (c.pt .Z) b) (PZ.lineEvalMats d PA c b)
        ≤ 172 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
        (Finset.sum_congr rfl fun b _ => ?_))) hZ2'
    exact hatVec_swapVec_xSqNorm M _ _
  have hb := padded_lines_consistency (M := M.swap) (PA := PB) (PB := PA) hm4 (swapVec_unit hM)
    (povmValue_swapped_le hfail) hPB hPA PX PZ hfacX hfacZ hX1sw hX2sw hZ2sw hcoll ty s
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t) ?_)) hb
  refine congrArg (avgSubAB hm4 hm ty s) ?_
  funext a b cX cZ
  refine Finset.sum_congr rfl fun v _ => ?_
  exact (hatVec_swapVec_bornProb M _ _).symm

end Main

end MIPRE.QLD

end
