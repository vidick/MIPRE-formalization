/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import MIPRE.Foundations.BipartiteModel
public import MIPRE.Tactics

@[expose] public section

/-!
# The summed semidefinite form in a commutant with a vector trace

The self-improvement step of the low-individual-degree soundness proof (JNVWY, Lemma 9.2) solves a
semidefinite program in the local algebra: it needs a measurement `T` and an operator `Z` with
`Aᵢ ≤ Z` for every `i` and the complementary slackness `Tᵢ Z = Tᵢ Aᵢ`. The finite-dimensional
proof gets them from strong duality. In a finite pair (`MIPRE/Foundations/FinitePair.lean`) there
is no dimension, but there is a faithful trace given by finitely many vectors, and that is enough:
a maximizer of `T ↦ ∑ᵢ Re τ(Tᵢ Aᵢ)` over the measurements of the algebra satisfies a first-order
condition, and the first-order condition gives `Z := ∑ᵢ Tᵢ Aᵢ` self-adjoint, `Aᵢ ≤ Z` and
`Tᵢ Z = Tᵢ Aᵢ`. This is `reports/c6b-paper-proofs.md`, §5 (Theorem 10 with Lemmas 1–9 and 7′,
and Corollary 11), item M9 of `planning/c6b-plan.md`.

**Setting (S).** `t` is any set of operators on a Hilbert space `H`, and the algebra is its
commutant `StarSubalgebra.centralizer ℂ t` (the operators commuting with `t` and `t⋆`). The vectors
`ξ : ι → H`, finitely many, give the functional `τ(x) = ∑ₖ ⟪ξₖ, x ξₖ⟫` on all of `B(H)`
(`tr`), which is assumed tracial and faithful on the commutant (`IsFaithfulTrace`). No
normalization is needed. The algebras of a finite pair are of this form, `opsA` the commutant of
`opsB` and conversely, with the pair's `VecTrace`.

* `IsSummedSdp A T Z`: the conclusion, over any ordered `⋆`-ring, with the fields of the vendored
  `SdpOptimalPairWithSlackness` (Corollary 11): `T` a measurement, `Z` self-adjoint, `Aᵢ ≤ Z` and
  `Tᵢ Z = Tᵢ Aᵢ`. Its consumers use slackness only through `∑ᵢ Tᵢ Aᵢ = Z`
  (`IsSummedSdp.sum_mul_eq`). `isSummedSdp_coe_iff` moves it between a `⋆`-subalgebra and `B(H)`.
* **The core chain** (Lemmas 1b–3 and 5–9): the trace facts (`re_tr_star`,
  `re_tr_star_mul_self`, `eq_zero_of_re_tr_star_mul_self_nonpos`), positivity of the pairing of
  two positive elements (`re_tr_mul_nonneg`, `mul_eq_zero_of_re_tr_mul_nonpos`), the perturbed
  measurement `perturb` and its exact expansion (`isMeasIn_perturb`, `obj_perturb`), the first
  order condition of a maximizer (`firstOrder_of_isMaxOn`), and from it the domination
  (`le_of_firstOrder`) and slackness (`mul_eq_of_le`).
* `isSummedSdp_of_firstOrder` and `isSummedSdp_of_isMaxOn`: Theorem 10, given a maximizer; and
  `isSummedSdp_of_le`, the converse of Corollary 11: self-adjointness and domination give
  slackness.

That a maximizer exists (Lemma 4) is weak-operator compactness of the unit ball, which the
repository has only in the vendored orthonormalization tree, so it and the assembled theorem are
`MIPRE/Background/Orthonormalization/SdpMaximizer.lean`.
-/

namespace MIPRE.SummedSdp

open scoped InnerProductSpace ComplexConjugate

/-! ## The conclusion -/

section Conclusion

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] {G : Type*} [Fintype G]

/-- **The summed semidefinite form** (`reports/c6b-paper-proofs.md`, §5, Corollary 11): `T` is a
measurement (`Tᵢ ≥ 0`, `∑ᵢ Tᵢ = 1`), `Z` is self-adjoint and dominates every `Aᵢ`, and
`Tᵢ Z = Tᵢ Aᵢ` for every `i`. The last three fields are those of the vendored
`SdpOptimalPairWithSlackness` (`primalTotalOperator`, `dualFeasible`, `complementarySlackness`). -/
structure IsSummedSdp (A T : G → R) (Z : R) : Prop where
  /-- Each outcome is positive. -/
  nonneg : ∀ i, 0 ≤ T i
  /-- The outcomes sum to one. -/
  total : ∑ i, T i = 1
  /-- The dual operator is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint Z
  /-- Dual feasibility: the dual operator dominates every `Aᵢ`. -/
  dualFeasible : ∀ i, A i ≤ Z
  /-- Complementary slackness: `Tᵢ Z = Tᵢ Aᵢ`. -/
  complementarySlackness : ∀ i, T i * Z = T i * A i

/-- **The composite rewrite the consumers use**: in the summed form, `∑ᵢ Tᵢ Aᵢ = Z`. -/
theorem IsSummedSdp.sum_mul_eq {A T : G → R} {Z : R} (h : IsSummedSdp A T Z) :
    ∑ i, T i * A i = Z := by
  simp_rw [← h.complementarySlackness, ← Finset.sum_mul, h.total, one_mul]

/-- **The summed form under an order embedding**: a `⋆`-ring homomorphism that preserves and
reflects the order carries the summed form both ways. -/
theorem isSummedSdp_map_iff {S : Type*} [Ring S] [StarRing S] [PartialOrder S] (f : R →+* S)
    (hf : Function.Injective f) (hstar : ∀ x, f (star x) = star (f x))
    (hle : ∀ x y, f x ≤ f y ↔ x ≤ y) {A T : G → R} {Z : R} :
    IsSummedSdp (fun i => f (A i)) (fun i => f (T i)) (f Z) ↔ IsSummedSdp A T Z := by
  have hsa : ∀ x, IsSelfAdjoint (f x) ↔ IsSelfAdjoint x := fun x => by
    simp only [IsSelfAdjoint, ← hstar, hf.eq_iff]
  constructor
  · intro h
    exact ⟨fun i => (hle 0 _).1 (by simpa using h.nonneg i),
      hf (by simpa [map_sum] using h.total), (hsa Z).1 h.isSelfAdjoint,
      fun i => (hle _ _).1 (h.dualFeasible i),
      fun i => hf (by simpa [map_mul] using h.complementarySlackness i)⟩
  · intro h
    exact ⟨fun i => by simpa using (hle 0 _).2 (h.nonneg i),
      by simpa [map_sum] using congrArg f h.total, (hsa Z).2 h.isSelfAdjoint,
      fun i => (hle _ _).2 (h.dualFeasible i),
      fun i => by simpa [map_mul] using congrArg f (h.complementarySlackness i)⟩

end Conclusion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] {G : Type*} [Fintype G]

/-- **The summed form in a `⋆`-subalgebra of `B(H)` is the summed form of the operators**: the
subalgebra carries the order of `B(H)`. -/
theorem isSummedSdp_coe_iff {S : StarSubalgebra ℂ (H →L[ℂ] H)} {A T : G → S} {Z : S} :
    IsSummedSdp (fun i => (A i : H →L[ℂ] H)) (fun i => (T i : H →L[ℂ] H)) (Z : H →L[ℂ] H) ↔
      IsSummedSdp A T Z :=
  isSummedSdp_map_iff (S.subtype : S →+* (H →L[ℂ] H)) Subtype.val_injective (fun _ => rfl)
    fun _ _ => Iff.rfl

/-! ## The vector functional (Lemma 2) -/

/-- **The vector functional** `τ(x) = ∑ₖ ⟪ξₖ, x ξₖ⟫` of finitely many vectors, on all of
`B(H)`. -/
noncomputable def tr (ξ : ι → H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun x := ∑ k, ⟪ξ k, x (ξ k)⟫_ℂ
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.mul_sum]

omit [CompleteSpace H] in
theorem tr_apply (ξ : ι → H) (x : H →L[ℂ] H) : tr ξ x = ∑ k, ⟪ξ k, x (ξ k)⟫_ℂ := rfl

/-- `τ(x⋆) = conj τ(x)`. -/
theorem tr_star (ξ : ι → H) (x : H →L[ℂ] H) : tr ξ (star x) = conj (tr ξ x) := by
  simp only [tr_apply, ContinuousLinearMap.star_eq_adjoint, map_sum,
    ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

/-- `Re τ(x⋆) = Re τ(x)` (Lemma 2). -/
theorem re_tr_star (ξ : ι → H) (x : H →L[ℂ] H) : (tr ξ (star x)).re = (tr ξ x).re := by
  rw [tr_star, Complex.conj_re]

/-- `Re τ(x⋆ x) = ∑ₖ ‖x ξₖ‖²` (Lemma 2). -/
theorem re_tr_star_mul_self (ξ : ι → H) (x : H →L[ℂ] H) :
    (tr ξ (star x * x)).re = ∑ k, ‖x (ξ k)‖ ^ 2 := by
  rw [tr_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint,
    show (ContinuousLinearMap.adjoint x * x) (ξ k) = ContinuousLinearMap.adjoint x (x (ξ k)) from
      rfl, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `Re τ(x⋆ x) ≥ 0` (Lemma 2). -/
theorem re_tr_star_mul_self_nonneg (ξ : ι → H) (x : H →L[ℂ] H) :
    0 ≤ (tr ξ (star x * x)).re := by
  rw [re_tr_star_mul_self]
  positivity

/-- **Setting (S)**: the vectors `ξ` give a tracial functional on the commutant of `t`, and they
separate it, so that the functional is faithful there. -/
structure IsFaithfulTrace (t : Set (H →L[ℂ] H)) (ξ : ι → H) : Prop where
  /-- (Tr): `τ(xy) = τ(yx)` on the commutant. -/
  trace_mul_comm : ∀ x ∈ StarSubalgebra.centralizer ℂ t, ∀ y ∈ StarSubalgebra.centralizer ℂ t,
    tr ξ (x * y) = tr ξ (y * x)
  /-- (F): an element of the commutant vanishing at every `ξₖ` vanishes. -/
  separating : ∀ x ∈ StarSubalgebra.centralizer ℂ t, (∀ k, x (ξ k) = 0) → x = 0

variable {t : Set (H →L[ℂ] H)} {ξ : ι → H}

/-- **Faithfulness** (Lemma 2): an element `x` of the commutant with `Re τ(x⋆ x) ≤ 0` is zero. -/
theorem IsFaithfulTrace.eq_zero_of_re_tr_star_mul_self_nonpos (hS : IsFaithfulTrace t ξ)
    {x : H →L[ℂ] H} (hx : x ∈ StarSubalgebra.centralizer ℂ t)
    (h : (tr ξ (star x * x)).re ≤ 0) : x = 0 := by
  rw [re_tr_star_mul_self] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by positivity).1
    (le_antisymm h (by positivity))
  exact hS.separating x hx fun k => by simpa using h0 k (Finset.mem_univ k)

/-! ## The commutant is closed under the functional calculus (Lemma 1b) -/

/-- **The commutant is closed under the real functional calculus** (Lemma 1b). -/
theorem cfcₙ_mem_centralizer {x : H →L[ℂ] H} (hx : x ∈ StarSubalgebra.centralizer ℂ t)
    (f : ℝ → ℝ) : cfcₙ f x ∈ StarSubalgebra.centralizer ℂ t := by
  rw [StarSubalgebra.mem_centralizer_iff] at hx ⊢
  intro y hy
  exact ⟨(Commute.cfcₙ_real (hx y hy).1.symm f).eq.symm,
    (Commute.cfcₙ_real (hx y hy).2.symm f).eq.symm⟩

/-- **The commutant contains the square roots of its elements** (Lemma 1b). -/
theorem sqrt_mem_centralizer {x : H →L[ℂ] H} (hx : x ∈ StarSubalgebra.centralizer ℂ t) :
    CFC.sqrt x ∈ StarSubalgebra.centralizer ℂ t := by
  rw [StarSubalgebra.mem_centralizer_iff] at hx ⊢
  intro y hy
  exact ⟨(Commute.cfcₙ_nnreal (hx y hy).1.symm _).eq.symm,
    (Commute.cfcₙ_nnreal (hx y hy).2.symm _).eq.symm⟩

/-- **The commutant contains the negative parts of its elements** (Lemma 1b). -/
theorem negPart_mem_centralizer {x : H →L[ℂ] H} (hx : x ∈ StarSubalgebra.centralizer ℂ t) :
    x⁻ ∈ StarSubalgebra.centralizer ℂ t := by
  rw [CFC.negPart_def]
  exact cfcₙ_mem_centralizer hx _

/-- A real multiple of an element of the commutant is in the commutant. -/
theorem real_smul_mem_centralizer {x : H →L[ℂ] H} (hx : x ∈ StarSubalgebra.centralizer ℂ t)
    (r : ℝ) : r • x ∈ StarSubalgebra.centralizer ℂ t := by
  rw [← Complex.coe_smul]
  exact SMulMemClass.smul_mem _ hx

/-! ## Positivity of the pairing (Lemma 3) -/

/-- The pairing of two positive elements of the commutant is `Re τ((r s)⋆ (r s))` with `s`, `r`
their square roots. -/
private theorem tr_mul_eq_star_mul_self (hS : IsFaithfulTrace t ξ) {T D : H →L[ℂ] H}
    (hT : T ∈ StarSubalgebra.centralizer ℂ t) (hD : D ∈ StarSubalgebra.centralizer ℂ t)
    (hT0 : 0 ≤ T) (hD0 : 0 ≤ D) :
    tr ξ (T * D) = tr ξ (star (CFC.sqrt D * CFC.sqrt T) * (CFC.sqrt D * CFC.sqrt T)) := by
  set s := CFC.sqrt T
  set r := CFC.sqrt D
  have hs : star s = s := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  have hr : star r = r := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  have hsm := sqrt_mem_centralizer hT
  have hrm := sqrt_mem_centralizer hD
  rw [star_mul, hs, hr, ← CFC.sqrt_mul_sqrt_self T hT0, ← CFC.sqrt_mul_sqrt_self D hD0]
  calc tr ξ (s * s * (r * r)) = tr ξ (s * (s * r * r)) := by simp only [mul_assoc]
    _ = tr ξ (s * r * r * s) := by
        rw [hS.trace_mul_comm _ hsm _ (mul_mem (mul_mem hsm hrm) hrm)]
    _ = tr ξ (s * r * (r * s)) := by simp only [mul_assoc]

/-- **The pairing of two positive elements is positive** (Lemma 3): `Re τ(T D) ≥ 0`. -/
theorem re_tr_mul_nonneg (hS : IsFaithfulTrace t ξ) {T D : H →L[ℂ] H}
    (hT : T ∈ StarSubalgebra.centralizer ℂ t) (hD : D ∈ StarSubalgebra.centralizer ℂ t)
    (hT0 : 0 ≤ T) (hD0 : 0 ≤ D) : 0 ≤ (tr ξ (T * D)).re := by
  rw [tr_mul_eq_star_mul_self hS hT hD hT0 hD0]
  exact re_tr_star_mul_self_nonneg ξ _

/-- **The equality case of Lemma 3**: if two positive elements of the commutant have
`Re τ(T D) ≤ 0`, then `D T = 0`. -/
theorem mul_eq_zero_of_re_tr_mul_nonpos (hS : IsFaithfulTrace t ξ) {T D : H →L[ℂ] H}
    (hT : T ∈ StarSubalgebra.centralizer ℂ t) (hD : D ∈ StarSubalgebra.centralizer ℂ t)
    (hT0 : 0 ≤ T) (hD0 : 0 ≤ D) (h : (tr ξ (T * D)).re ≤ 0) : D * T = 0 := by
  rw [tr_mul_eq_star_mul_self hS hT hD hT0 hD0] at h
  have h0 := hS.eq_zero_of_re_tr_star_mul_self_nonpos
    (mul_mem (sqrt_mem_centralizer hD) (sqrt_mem_centralizer hT)) h
  rw [← CFC.sqrt_mul_sqrt_self T hT0, ← CFC.sqrt_mul_sqrt_self D hD0,
    show CFC.sqrt D * CFC.sqrt D * (CFC.sqrt T * CFC.sqrt T) =
      CFC.sqrt D * (CFC.sqrt D * CFC.sqrt T) * CFC.sqrt T by simp only [mul_assoc], h0,
    mul_zero, zero_mul]

/-! ## Measurements, the objective, and the perturbation (Lemmas 5 and 6) -/

/-- **A measurement in the commutant**: positive elements of the commutant summing to one. -/
structure IsMeasIn (t : Set (H →L[ℂ] H)) (T : G → H →L[ℂ] H) : Prop where
  /-- Each outcome is in the commutant. -/
  mem : ∀ i, T i ∈ StarSubalgebra.centralizer ℂ t
  /-- Each outcome is positive. -/
  nonneg : ∀ i, 0 ≤ T i
  /-- The outcomes sum to one. -/
  sum_eq_one : ∑ i, T i = 1

/-- **The outcomes of a measurement are contractions**: `0 ≤ Tᵢ ≤ ∑ⱼ Tⱼ = 1`. -/
theorem IsMeasIn.norm_le_one {T : G → H →L[ℂ] H} (hT : IsMeasIn t T) (i : G) : ‖T i‖ ≤ 1 := by
  refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hT.nonneg i)).2 ?_
  rw [← hT.sum_eq_one]
  exact Finset.single_le_sum (fun j _ => hT.nonneg j) (Finset.mem_univ i)

/-- **The objective** `f(T) = ∑ᵢ Re τ(Tᵢ Aᵢ)`. -/
noncomputable def obj (ξ : ι → H) (A T : G → H →L[ℂ] H) : ℝ := ∑ i, (tr ξ (T i * A i)).re

/-- **The first-order condition** `FO(T, A)`: `Re τ(P Aₕ) ≤ Re τ(P Z)` for every `h` and every
`P` of the commutant with `0 ≤ P ≤ 1`, where `Z = ∑ᵢ Tᵢ Aᵢ`. -/
def FirstOrder (t : Set (H →L[ℂ] H)) (ξ : ι → H) (A T : G → H →L[ℂ] H) : Prop :=
  ∀ h, ∀ P ∈ StarSubalgebra.centralizer ℂ t, 0 ≤ P → P ≤ 1 →
    (tr ξ (P * A h)).re ≤ (tr ξ (P * ∑ i, T i * A i)).re

/-- **The perturbed measurement** of Lemma 5: `T'ᵢ = K Tᵢ K + δᵢₕ (1 - K²)`. -/
noncomputable def perturb [DecidableEq G] (T : G → H →L[ℂ] H) (h : G) (K : H →L[ℂ] H) :
    G → H →L[ℂ] H :=
  fun i => K * T i * K + if i = h then 1 - K * K else 0

/-- **The perturbed measurement is a measurement** (Lemma 5): for `P` in the commutant with
`0 ≤ P ≤ 1` and `0 ≤ ε ≤ 1`, with `K = 1 - εP`. -/
theorem isMeasIn_perturb [DecidableEq G] {T : G → H →L[ℂ] H} (hT : IsMeasIn t T) (h : G)
    {P : H →L[ℂ] H} (hP : P ∈ StarSubalgebra.centralizer ℂ t) (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : IsMeasIn t (perturb T h (1 - ε • P)) := by
  set K : H →L[ℂ] H := 1 - ε • P
  have hK : K ∈ StarSubalgebra.centralizer ℂ t :=
    sub_mem (one_mem _) (real_smul_mem_centralizer hP ε)
  have hKsa : star K = K := by
    rw [star_sub, star_one, star_smul, star_trivial, (IsSelfAdjoint.of_nonneg hP0).star_eq]
  -- `1 - K = εP` and `1 + K = (2 - ε) + ε (1 - P)` are commuting positive operators
  have h1 : 0 ≤ 1 - K := by
    rw [show 1 - K = ε • P by simp only [K, sub_sub_cancel]]
    exact smul_nonneg hε0 hP0
  have h2 : 0 ≤ 1 + K := by
    rw [show 1 + K = (2 - ε) • (1 : H →L[ℂ] H) + ε • (1 - P) by
      simp only [K, smul_sub, sub_smul, two_smul]; abel]
    exact add_nonneg (smul_nonneg (by linarith) zero_le_one) (smul_nonneg hε0 (sub_nonneg.2 hP1))
  have hc : Commute (1 - K) (1 + K) :=
    (Commute.one_left _).sub_left ((Commute.one_right _).add_right (Commute.refl _))
  have hKK : 0 ≤ 1 - K * K := by
    have := hc.mul_nonneg h1 h2
    rwa [show (1 - K) * (1 + K) = 1 - K * K by noncomm_ring] at this
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · refine add_mem (mul_mem (mul_mem hK (hT.mem i)) hK) ?_
    split_ifs
    · exact sub_mem (one_mem _) (mul_mem hK hK)
    · exact zero_mem _
  · refine add_nonneg ?_ ?_
    · have := star_left_conjugate_nonneg (hT.nonneg i) K
      rwa [hKsa] at this
    · split_ifs
      · exact hKK
      · exact le_rfl
  · simp only [perturb, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_mul, ← Finset.mul_sum, hT.sum_eq_one, mul_one, add_sub_cancel]

omit [CompleteSpace H] in
/-- `Re τ(r • x) = r Re τ(x)` for real `r`. -/
theorem re_tr_smul (ξ : ι → H) (r : ℝ) (x : H →L[ℂ] H) : (tr ξ (r • x)).re = r * (tr ξ x).re := by
  rw [LinearMap.map_smul_of_tower, Complex.smul_re, smul_eq_mul]

/-- **The swap of Lemma 6**: for self-adjoint `T`, `P`, `A` of the commutant,
`Re τ(T P A) = Re τ(P T A)`. -/
theorem re_tr_swap (hS : IsFaithfulTrace t ξ) {T P A : H →L[ℂ] H}
    (hT : T ∈ StarSubalgebra.centralizer ℂ t) (hP : P ∈ StarSubalgebra.centralizer ℂ t)
    (hA : A ∈ StarSubalgebra.centralizer ℂ t) (hTsa : IsSelfAdjoint T) (hPsa : IsSelfAdjoint P)
    (hAsa : IsSelfAdjoint A) : (tr ξ (T * P * A)).re = (tr ξ (P * T * A)).re := by
  rw [← re_tr_star, star_mul, star_mul, hTsa.star_eq, hPsa.star_eq, hAsa.star_eq, mul_assoc,
    hS.trace_mul_comm _ hA _ (mul_mem hP hT), mul_assoc]

/-- **The exact expansion** (Lemma 6): with `K = 1 - εP` and `Z = ∑ᵢ Tᵢ Aᵢ`,
`f(T') = f(T) + 2ε (Re τ(P Aₕ) - Re τ(P Z)) + ε² c` with
`c = ∑ᵢ Re τ(P Tᵢ P Aᵢ) - Re τ(P² Aₕ)`. -/
theorem obj_perturb [DecidableEq G] (hS : IsFaithfulTrace t ξ) {T A : G → H →L[ℂ] H}
    (hT : IsMeasIn t T) (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t)
    (hAsa : ∀ i, IsSelfAdjoint (A i)) (h : G) {P : H →L[ℂ] H}
    (hP : P ∈ StarSubalgebra.centralizer ℂ t) (hPsa : IsSelfAdjoint P) (ε : ℝ) :
    obj ξ A (perturb T h (1 - ε • P)) = obj ξ A T +
      2 * ε * ((tr ξ (P * A h)).re - (tr ξ (P * ∑ i, T i * A i)).re) +
      ε ^ 2 * (∑ i, (tr ξ (P * T i * P * A i)).re - (tr ξ (P * P * A h)).re) := by
  have hexp : ∀ i, (1 - ε • P) * T i * (1 - ε • P) * A i =
      T i * A i - ε • (P * T i * A i) - ε • (T i * P * A i) + (ε ^ 2) • (P * T i * P * A i) := by
    intro i
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul, pow_two, mul_assoc]
    abel
  have hexp' : (1 - (1 - ε • P) * (1 - ε • P)) * A h =
      (2 * ε) • (P * A h) - (ε ^ 2) • (P * P * A h) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul, pow_two, mul_assoc, two_mul, add_smul]
    abel
  have hswap : ∀ i, (tr ξ (T i * P * A i)).re = (tr ξ (P * T i * A i)).re := fun i =>
    re_tr_swap hS (hT.mem i) hP (hA i) (IsSelfAdjoint.of_nonneg (hT.nonneg i)) hPsa (hAsa i)
  have hsplit : obj ξ A (perturb T h (1 - ε • P)) =
      ∑ i, (tr ξ ((1 - ε • P) * T i * (1 - ε • P) * A i)).re +
        (tr ξ ((1 - (1 - ε • P) * (1 - ε • P)) * A h)).re := by
    simp only [obj, perturb, add_mul, map_add, Complex.add_re, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single h (fun i _ hi => by simp [hi]) (by simp)]
    simp
  have hPZ : (tr ξ (P * ∑ i, T i * A i)).re = ∑ i, (tr ξ (P * T i * A i)).re := by
    simp only [Finset.mul_sum, map_sum, Complex.re_sum, mul_assoc]
  rw [hsplit, hPZ]
  simp only [hexp, hexp', map_add, map_sub, Complex.add_re, Complex.sub_re, re_tr_smul, hswap,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, obj]
  ring

/-! ## The first-order condition (Lemmas 7 and 7′) -/

/-- **A quadratic first-order lemma** (Lemma 7): if `2εa + ε²c ≤ 0` for every `ε ∈ [0, 1]`, then
`a ≤ 0`. -/
theorem nonpos_of_quadratic {a c : ℝ} (h : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → 2 * ε * a + ε ^ 2 * c ≤ 0) :
    a ≤ 0 := by
  by_contra ha
  push Not at ha
  set ε := min 1 (a / (|c| + 1))
  have hc1 : 0 < |c| + 1 := by positivity
  have hε0 : 0 < ε := lt_min one_pos (div_pos ha hc1)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεc : ε * (|c| + 1) ≤ a := (le_div_iff₀ hc1).1 (min_le_right _ _)
  have := h ε hε0.le hε1
  nlinarith [neg_abs_le c, abs_nonneg c, mul_pos hε0 hε0]

/-- **A maximizer satisfies the first-order condition** (Lemma 7′). -/
theorem firstOrder_of_isMaxOn (hS : IsFaithfulTrace t ξ) {T A : G → H →L[ℂ] H}
    (hT : IsMeasIn t T) (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t)
    (hAsa : ∀ i, IsSelfAdjoint (A i)) (hmax : IsMaxOn (obj ξ A) {T | IsMeasIn t T} T) :
    FirstOrder t ξ A T := by
  classical
  intro h P hP hP0 hP1
  rw [← sub_nonpos]
  refine nonpos_of_quadratic (c := ∑ i, (tr ξ (P * T i * P * A i)).re - (tr ξ (P * P * A h)).re)
    fun ε hε0 hε1 => ?_
  have hle := isMaxOn_iff.1 hmax _ (isMeasIn_perturb hT h hP hP0 hP1 hε0 hε1)
  rw [obj_perturb hS hT hA hAsa h hP (IsSelfAdjoint.of_nonneg hP0)] at hle
  linarith

/-! ## Domination and slackness (Lemmas 8 and 9) -/

/-- **The pairing with `Z⋆`** (Lemma 8, step 1): for a self-adjoint `P` and `Z` in the commutant,
`Re τ(P Z⋆) = Re τ(P Z)`. -/
theorem re_tr_mul_star (hS : IsFaithfulTrace t ξ) {P Z : H →L[ℂ] H}
    (hP : P ∈ StarSubalgebra.centralizer ℂ t) (hZ : Z ∈ StarSubalgebra.centralizer ℂ t)
    (hPsa : IsSelfAdjoint P) : (tr ξ (P * star Z)).re = (tr ξ (P * Z)).re := by
  rw [← re_tr_star, star_mul, star_star, hPsa.star_eq, hS.trace_mul_comm _ hZ _ hP]

/-- `Z = ∑ᵢ Tᵢ Aᵢ` is in the commutant. -/
theorem sum_mul_mem {T A : G → H →L[ℂ] H} (hT : ∀ i, T i ∈ StarSubalgebra.centralizer ℂ t)
    (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t) :
    ∑ i, T i * A i ∈ StarSubalgebra.centralizer ℂ t :=
  sum_mem fun i _ => mul_mem (hT i) (hA i)

/-- **Domination by the real part** (Lemma 8): under the first-order condition,
`W = (Z + Z⋆)/2` dominates every `Aₕ`. -/
theorem le_of_firstOrder (hS : IsFaithfulTrace t ξ) {T A : G → H →L[ℂ] H} (hT : IsMeasIn t T)
    (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t) (hAsa : ∀ i, IsSelfAdjoint (A i))
    (hFO : FirstOrder t ξ A T) (h : G) :
    A h ≤ (2⁻¹ : ℝ) • (∑ i, T i * A i + star (∑ i, T i * A i)) := by
  set Z := ∑ i, T i * A i
  set W := (2⁻¹ : ℝ) • (Z + star Z)
  have hZ : Z ∈ StarSubalgebra.centralizer ℂ t := sum_mul_mem hT.mem hA
  have hW : W ∈ StarSubalgebra.centralizer ℂ t :=
    real_smul_mem_centralizer (add_mem hZ (star_mem hZ)) _
  have hWsa : IsSelfAdjoint W := by
    simp only [W, IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm]
  set Y := W - A h
  have hY : Y ∈ StarSubalgebra.centralizer ℂ t := sub_mem hW (hA h)
  have hYsa : IsSelfAdjoint Y := hWsa.sub (hAsa h)
  set N := Y⁻
  have hN : N ∈ StarSubalgebra.centralizer ℂ t := negPart_mem_centralizer hY
  have hN0 : 0 ≤ N := CFC.negPart_nonneg Y
  have hNsa : IsSelfAdjoint N := IsSelfAdjoint.of_nonneg hN0
  set c : ℝ := (1 + ‖N‖)⁻¹
  have hc : 0 < c := by positivity
  -- the test element `P = N / (1 + ‖N‖)`, between `0` and `1`
  have hP0 : 0 ≤ c • N := smul_nonneg hc.le hN0
  have hP1 : c • N ≤ 1 := by
    refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ hP0).1 ?_
    rw [norm_smul, Real.norm_of_nonneg hc.le, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hFOh := hFO h _ (real_smul_mem_centralizer hN c) hP0 hP1
  -- `Re τ(P W) = Re τ(P Z)`
  have hPW : (tr ξ (c • N * W)).re = (tr ξ (c • N * Z)).re := by
    have hPm := real_smul_mem_centralizer hN c
    have hPsa : IsSelfAdjoint (c • N) := by
      simp only [IsSelfAdjoint, star_smul, star_trivial, hNsa.star_eq]
    rw [mul_smul_comm, re_tr_smul, mul_add, map_add, Complex.add_re,
      re_tr_mul_star hS hPm hZ hPsa]
    ring
  -- `N Y = -N²`
  have hNY : N * Y = -(star N * N) := by
    conv_lhs => rw [← CFC.posPart_sub_negPart Y hYsa]
    rw [mul_sub, CFC.negPart_mul_posPart, zero_sub, hNsa.star_eq]
  have hle : (tr ξ (star N * N)).re ≤ 0 := by
    have h1 : 0 ≤ (tr ξ (c • N * Y)).re := by
      rw [show c • N * Y = c • N * W - c • N * A h by rw [mul_sub], map_sub, Complex.sub_re, hPW]
      linarith
    rw [smul_mul_assoc, re_tr_smul, hNY, map_neg, Complex.neg_re] at h1
    nlinarith
  have hN00 : N = 0 := hS.eq_zero_of_re_tr_star_mul_self_nonpos hN hle
  rw [← sub_nonneg]
  change 0 ≤ Y
  rw [← CFC.posPart_sub_negPart Y hYsa]
  change 0 ≤ Y⁺ - N
  rw [hN00, sub_zero]
  exact CFC.posPart_nonneg Y

/-- **Slackness** (Lemma 9, steps 1–3): if a self-adjoint `W` of the commutant dominates every
`Aᵢ` and `Re τ(W) ≤ Re τ(Z)` with `Z = ∑ᵢ Tᵢ Aᵢ`, then `W Tᵢ = Aᵢ Tᵢ` for every `i`. -/
theorem mul_eq_of_le (hS : IsFaithfulTrace t ξ) {T A : G → H →L[ℂ] H} (hT : IsMeasIn t T)
    (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t) {W : H →L[ℂ] H}
    (hW : W ∈ StarSubalgebra.centralizer ℂ t) (hle : ∀ i, A i ≤ W)
    (htr : (tr ξ W).re ≤ (tr ξ (∑ i, T i * A i)).re) (i : G) : W * T i = A i * T i := by
  have hD : ∀ i, W - A i ∈ StarSubalgebra.centralizer ℂ t := fun i => sub_mem hW (hA i)
  have hD0 : ∀ i, 0 ≤ W - A i := fun i => sub_nonneg.2 (hle i)
  have hpos : ∀ i, 0 ≤ (tr ξ (T i * (W - A i))).re := fun i =>
    re_tr_mul_nonneg hS (hT.mem i) (hD i) (hT.nonneg i) (hD0 i)
  have hsum : ∑ i, (tr ξ (T i * (W - A i))).re ≤ 0 := by
    simp only [mul_sub, map_sub, Complex.sub_re, Finset.sum_sub_distrib]
    rw [← Complex.re_sum, ← map_sum, ← Finset.sum_mul, hT.sum_eq_one, one_mul,
      ← Complex.re_sum, ← map_sum]
    linarith
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hpos i).1
    (le_antisymm hsum (Finset.sum_nonneg fun i _ => hpos i)) i (Finset.mem_univ i)
  have := mul_eq_zero_of_re_tr_mul_nonpos hS (hT.mem i) (hD i) (hT.nonneg i) (hD0 i) h0.le
  rwa [sub_mul, sub_eq_zero] at this

/-- **`W = Z⋆`** (Lemma 9, step 4): if `W Tᵢ = Aᵢ Tᵢ` for every `i`, with the `Aᵢ` self-adjoint
and `T` a measurement, then `W = (∑ᵢ Tᵢ Aᵢ)⋆`. -/
theorem eq_star_of_mul_eq {T A : G → H →L[ℂ] H} (hT : IsMeasIn t T)
    (hAsa : ∀ i, IsSelfAdjoint (A i)) {W : H →L[ℂ] H} (hWT : ∀ i, W * T i = A i * T i) :
    W = star (∑ i, T i * A i) := by
  rw [star_sum]
  calc W = W * ∑ i, T i := by rw [hT.sum_eq_one, mul_one]
    _ = ∑ i, star (T i * A i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hWT, star_mul, (hAsa i).star_eq, (IsSelfAdjoint.of_nonneg (hT.nonneg i)).star_eq]

/-! ## Theorem 10 and Corollary 11 -/

/-- **The summed semidefinite form from the first-order condition** (`reports/c6b-paper-proofs.md`,
§5, Theorem 10 via Lemmas 8 and 9): if a measurement `T` of the commutant satisfies `FO(T, A)`
for self-adjoint `Aᵢ` of the commutant, then `Z = ∑ᵢ Tᵢ Aᵢ` is self-adjoint, dominates every
`Aᵢ`, and `Tᵢ Z = Tᵢ Aᵢ`. -/
theorem isSummedSdp_of_firstOrder (hS : IsFaithfulTrace t ξ) {T A : G → H →L[ℂ] H}
    (hT : IsMeasIn t T) (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t)
    (hAsa : ∀ i, IsSelfAdjoint (A i)) (hFO : FirstOrder t ξ A T) :
    IsSummedSdp A T (∑ i, T i * A i) := by
  set Z := ∑ i, T i * A i
  set W := (2⁻¹ : ℝ) • (Z + star Z)
  have hZ : Z ∈ StarSubalgebra.centralizer ℂ t := sum_mul_mem hT.mem hA
  have hW : W ∈ StarSubalgebra.centralizer ℂ t :=
    real_smul_mem_centralizer (add_mem hZ (star_mem hZ)) _
  have hWsa : IsSelfAdjoint W := by
    simp only [W, IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm]
  have hle : ∀ i, A i ≤ W := le_of_firstOrder hS hT hA hAsa hFO
  have htr : (tr ξ W).re ≤ (tr ξ Z).re := by
    rw [re_tr_smul, map_add, Complex.add_re, re_tr_star]
    linarith
  have hWZ : W = star Z := eq_star_of_mul_eq hT hAsa (mul_eq_of_le hS hT hA hW hle htr)
  have hZW : Z = W := by rw [← star_star Z, ← hWZ, hWsa.star_eq]
  refine ⟨hT.nonneg, hT.sum_eq_one, hZW ▸ hWsa, fun i => hZW ▸ hle i, fun i => ?_⟩
  have := congrArg star (mul_eq_of_le hS hT hA hW hle htr i)
  rwa [star_mul, star_mul, hWsa.star_eq, (hAsa i).star_eq,
    (IsSelfAdjoint.of_nonneg (hT.nonneg i)).star_eq, ← hZW] at this

/-- **Theorem 10, given a maximizer** (`reports/c6b-paper-proofs.md`, §5): a maximizer of
`T ↦ ∑ᵢ Re τ(Tᵢ Aᵢ)` over the measurements of the commutant gives the summed semidefinite form,
with `Z = ∑ᵢ Tᵢ Aᵢ`. -/
theorem isSummedSdp_of_isMaxOn (hS : IsFaithfulTrace t ξ) {T A : G → H →L[ℂ] H}
    (hT : IsMeasIn t T) (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t)
    (hAsa : ∀ i, IsSelfAdjoint (A i)) (hmax : IsMaxOn (obj ξ A) {T | IsMeasIn t T} T) :
    IsSummedSdp A T (∑ i, T i * A i) :=
  isSummedSdp_of_firstOrder hS hT hA hAsa (firstOrder_of_isMaxOn hS hT hA hAsa hmax)

/-- **The converse of Corollary 11**: if `Z = ∑ᵢ Tᵢ Aᵢ` is self-adjoint and dominates every `Aᵢ`,
for a measurement `T` of the commutant, then complementary slackness holds. -/
theorem isSummedSdp_of_le (hS : IsFaithfulTrace t ξ) {T A : G → H →L[ℂ] H} (hT : IsMeasIn t T)
    (hA : ∀ i, A i ∈ StarSubalgebra.centralizer ℂ t) (hAsa : ∀ i, IsSelfAdjoint (A i))
    (hZsa : IsSelfAdjoint (∑ i, T i * A i)) (hle : ∀ i, A i ≤ ∑ i, T i * A i) :
    IsSummedSdp A T (∑ i, T i * A i) := by
  refine ⟨hT.nonneg, hT.sum_eq_one, hZsa, hle, fun i => ?_⟩
  have := congrArg star (mul_eq_of_le hS hT hA (sum_mul_mem hT.mem hA) hle le_rfl i)
  rwa [star_mul, star_mul, hZsa.star_eq, (hAsa i).star_eq,
    (IsSelfAdjoint.of_nonneg (hT.nonneg i)).star_eq] at this

end MIPRE.SummedSdp

end
