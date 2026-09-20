/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Pcp
import MIPRE.Foundations.SAT.PcpAlgebra
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# The five disjoint answer blocks of the classical PCP

The answer polynomials have `m` variables; the formula and certificates have
`5*m + 5 + s` variables. This file transports the former into the latter without
losing the individual-degree bound. In particular, the honest constraint has
degree at most seven, rather than the soundness proof's coarse bound of 41.
-/

noncomputable section

namespace MIPRE.SAT

open Finset MvPolynomial LowDegree

namespace PcpParams

/-- The coordinate of an answer bit within the complete PCP point. -/
def blockIndex (P : PcpParams) (i : Fin 5) (j : Fin P.m) : Fin P.m' :=
  ⟨i * P.m + j, by
    have hi := Nat.mul_le_mul_right P.m (Nat.lt_succ_iff.mp i.isLt)
    have hj := j.isLt
    simp only [m']
    omega⟩

/-- The sign coordinates immediately follow the five answer blocks. -/
def signIndex (P : PcpParams) (i : Fin 5) : Fin P.m' :=
  ⟨5 * P.m + i, by have := i.isLt; simp only [m']; omega⟩

theorem blockIndex_injective (P : PcpParams) (i : Fin 5) :
    Function.Injective (P.blockIndex i) := by
  intro j k h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [blockIndex] at this
  omega

theorem blockIndex_eq_imp (P : PcpParams) (i t : Fin 5) (j k : Fin P.m)
    (h : P.blockIndex i j = P.blockIndex t k) : i = t := by
  have hj : j.val < P.m := j.isLt
  have hk : k.val < P.m := k.isLt
  have hv := congrArg Fin.val h
  simp only [blockIndex] at hv
  have hm : j.val = k.val := by
    have := congrArg (fun n => n % P.m) hv
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] using this
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < P.m) (by omega)

theorem signIndex_injective (P : PcpParams) : Function.Injective P.signIndex := by
  intro i t h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [signIndex] at this
  omega

theorem blockIndex_ne_signIndex (P : PcpParams) (i t : Fin 5) (j : Fin P.m) :
    P.blockIndex i j ≠ P.signIndex t := by
  intro h
  have hi := Nat.mul_le_mul_right P.m (Nat.lt_succ_iff.mp i.isLt)
  have hj := j.isLt
  have := congrArg Fin.val h
  simp only [blockIndex, signIndex] at this
  omega

end PcpParams

namespace PcpAlgebra

variable {P : PcpParams} {F : Type*} [Field F]

/-- An answer polynomial, viewed as a polynomial on the complete PCP point. -/
def liftAnswer (i : Fin 5) (g : MvPolynomial (Fin P.m) F) :
    MvPolynomial (Fin P.m') F := rename (P.blockIndex i) g

@[simp] theorem eval_liftAnswer (i : Fin 5) (g : MvPolynomial (Fin P.m) F)
    (z : Fin P.m' → F) : eval z (liftAnswer i g) = eval (P.block i z) g := by
  simp only [liftAnswer, eval_rename]
  rfl

theorem degreeOf_liftAnswer_le (i : Fin 5) (g : MvPolynomial (Fin P.m) F)
    {d : ℕ} (hg : ∀ j, g.degreeOf j ≤ d) (j : Fin P.m') :
    (liftAnswer i g).degreeOf j ≤ d := by
  by_cases h : ∃ k, P.blockIndex i k = j
  · obtain ⟨k, rfl⟩ := h
    rw [liftAnswer, degreeOf_rename_of_injective (P.blockIndex_injective i)]
    exact hg k
  · have hz : (liftAnswer i g).degreeOf j = 0 := by
      by_contra hn
      obtain ⟨k, _, hk⟩ := mem_vars_rename _ g (mem_vars_iff_degreeOf_ne_zero.mpr hn)
      exact h ⟨k, hk⟩
    rw [hz]
    exact Nat.zero_le _

private theorem factor_degree_pos (i : Fin 5) (g : MvPolynomial (Fin P.m) F)
    (j : Fin P.m') (h : 0 < (liftAnswer i g - X (P.signIndex i)).degreeOf j) :
    (∃ k, P.blockIndex i k = j) ∨ P.signIndex i = j := by
  by_contra hn
  push Not at hn
  have hz : (liftAnswer i g).degreeOf j = 0 := by
    by_contra hp
    obtain ⟨k, _, hk⟩ := mem_vars_rename _ g (mem_vars_iff_degreeOf_ne_zero.mpr hp)
    exact hn.1 k hk
  have hx : (X (P.signIndex i) : MvPolynomial (Fin P.m') F).degreeOf j = 0 :=
    degreeOf_X_of_ne (Ne.symm hn.2)
  have hb := degreeOf_sub_le j (liftAnswer i g) (X (P.signIndex i))
  rw [hz, hx] at hb
  omega

/-- A coordinate belongs to at most one of the five literal factors. -/
theorem literal_product_degree_le (g : Fin 5 → MvPolynomial (Fin P.m) F)
    (hg : ∀ i j, (g i).degreeOf j ≤ 1) (j : Fin P.m') :
    (∏ i, (liftAnswer i (g i) - X (P.signIndex i))).degreeOf j ≤ 1 := by
  let f : Fin 5 → MvPolynomial (Fin P.m') F := fun i =>
    liftAnswer i (g i) - X (P.signIndex i)
  have hbound (i : Fin 5) : (f i).degreeOf j ≤ 1 := by
    apply (degreeOf_sub_le j _ _).trans
    apply max_le (degreeOf_liftAnswer_le i (g i) (hg i) j)
    by_cases h : j = P.signIndex i
    · simp [h]
    · simp [degreeOf_X_of_ne h]
  have hunique (i t : Fin 5) (hi : 0 < (f i).degreeOf j)
      (ht : 0 < (f t).degreeOf j) : i = t := by
    rcases factor_degree_pos i (g i) j hi with ⟨a, ha⟩ | ha
    · rcases factor_degree_pos t (g t) j ht with ⟨b, hb⟩ | hb
      · exact P.blockIndex_eq_imp i t a b (ha.trans hb.symm)
      · exact (P.blockIndex_ne_signIndex i t a (ha.trans hb.symm)).elim
    · rcases factor_degree_pos t (g t) j ht with ⟨b, hb⟩ | hb
      · exact (P.blockIndex_ne_signIndex t i b (hb.trans ha.symm)).elim
      · exact P.signIndex_injective (ha.trans hb.symm)
  apply (degreeOf_prod_le j univ f).trans
  by_cases h : ∃ i, 0 < (f i).degreeOf j
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · exact hbound i
    · intro t _ hti
      by_contra ht
      exact hti (hunique t i (Nat.pos_of_ne_zero ht) hi)
    · simp
  · push Not at h
    simp only [Nat.le_zero] at h
    simp [h]

/-- The honest constraint has individual degree at most seven. -/
theorem honest_constraint_degree_le (φ : MvPolynomial (Fin P.m') F)
    (g : Fin 5 → MvPolynomial (Fin P.m) F)
    (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ 1)
    (j : Fin P.m') :
    (constraint φ (fun i => liftAnswer i (g i)) P.signIndex).degreeOf j ≤ 7 :=
  (degreeOf_mul_le j _ _).trans (Nat.add_le_add (hφ j) (literal_product_degree_le g hg j))

/-- The two tests on the point and its claimed field-valued evaluations. -/
def TypedAccepts (φ : MvPolynomial (Fin P.m') F) (z : Fin P.m' → F)
    (ev : (Fin 5 → F) × (Fin (P.m' + 1) → F)) : Prop :=
  ev.2 0 = eval z φ * ∏ i, (ev.1 i - z (P.signIndex i)) ∧
    ev.2 0 = ∑ j, ev.2 j.succ * (z j * (1 - z j))

/-- The typed tests on a proof's evaluations are exactly the polynomial tests. -/
theorem typedAccepts_ev_iff (φ : MvPolynomial (Fin P.m') F) (pf : PcpProof P F)
    (z : Fin P.m' → F) :
    TypedAccepts φ z (pf.ev z) ↔
      Accepts φ (fun i => liftAnswer i (pf.g i)) P.signIndex (pf.c 0)
        (fun j => pf.c j.succ) z := by
  simp [TypedAccepts, Accepts, constraint, zeroCombination, cubeZero, PcpProof.ev]

/-- The honest low-degree PCP, including its degree-seven certificates and its
five prescribed answer polynomials, exists for every satisfying Boolean assignment. -/
theorem exists_proof_of_satisfying_assignment
    (φ : MvPolynomial (Fin P.m') F) (hφdeg : ∀ j, φ.degreeOf j ≤ 6)
    (hφbool : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 0 ∨ eval (pt y) φ = 1)
    (a : Fin 5 → (Fin P.m → Bool) → Bool)
    (hsat : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 1 →
      ∃ i : Fin 5, a i (P.block i y) = y (P.signIndex i)) :
    ∃ pf : PcpProof P F,
      (∀ i, pf.g i = ldEnc (fun x => ofBool (a i x))) ∧
      ∀ z, TypedAccepts φ z (pf.ev z) := by
  let g : Fin 5 → MvPolynomial (Fin P.m) F := fun i => ldEnc (fun x => ofBool (a i x))
  have hg : ∀ i j, (g i).degreeOf j ≤ 1 := fun i => degreeOf_ldEnc_le _
  let c₀ := constraint φ (fun i => liftAnswer i (g i)) P.signIndex
  have hc₀ : ∀ j, c₀.degreeOf j ≤ 7 := honest_constraint_degree_le φ g hφdeg hg
  have hz : ∀ y : Fin P.m' → Bool, eval (pt y) c₀ = 0 := by
    intro y
    simp only [c₀, constraint, map_mul, map_prod, map_sub, eval_X, eval_liftAnswer]
    rcases hφbool y with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul]
      obtain ⟨i, hi⟩ := hsat y h
      apply Finset.prod_eq_zero (mem_univ i)
      have he : P.block i (pt y : Fin P.m' → F) = pt (P.block i y) := rfl
      simp [he, g, hi, pt]
  obtain ⟨c, hc, hd⟩ := exists_zero_basis c₀ hc₀ hz
  let pf : PcpProof P F :=
    { g := g
      c := Fin.cases c₀ c
      degreeOf_g := fun i j => (hg i j).trans (by decide)
      degreeOf_c := by
        intro i
        refine Fin.cases hc₀ (fun j => hd j) i }
  refine ⟨pf, fun _ => rfl, fun z => (typedAccepts_ev_iff φ pf z).mpr ?_⟩
  refine ⟨rfl, ?_⟩
  exact congrArg (eval z) hc

/-- Majority acceptance of any low-degree proof yields a satisfying decoded
five-tuple for every Boolean clause described by the arithmetized formula. -/
theorem decoded_clause_of_majority [Fintype F] [DecidableEq F]
    (φ : MvPolynomial (Fin P.m') F) (hφ : ∀ j, φ.degreeOf j ≤ 6)
    (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
    (S : Finset (Fin P.m' → F)) (hS : ∀ z ∈ S, TypedAccepts φ z (pf.ev z))
    (hmajority : Fintype.card F ^ P.m' < 2 * S.card)
    (y : Fin P.m' → Bool) (hy : eval (pt y) φ = 1) :
    ∃ i : Fin 5, coded (pf.g i) (P.block i y) = ofBool (y (P.signIndex i)) := by
  obtain ⟨h₀, h₁⟩ := identities_of_majority φ (fun i => liftAnswer i (pf.g i))
    P.signIndex (pf.c 0) (fun j => pf.c j.succ) hφ
    (fun i => degreeOf_liftAnswer_le i (pf.g i) (pf.degreeOf_g i))
    (pf.degreeOf_c 0) (fun j => pf.degreeOf_c j.succ)
    (by change 2 * (P.m' * 41) ≤ Fintype.card F; omega)
    S (fun z hz => (typedAccepts_ev_iff φ pf z).mp (hS z hz)) hmajority
  obtain ⟨i, hi⟩ := clause_satisfied_of_identities φ (fun i => liftAnswer i (pf.g i))
    P.signIndex (fun j => pf.c j.succ) (h₀.symm.trans h₁) y hy
  refine ⟨i, coded_eq_of_eval_eq_ofBool _ _ _ ?_⟩
  have he : P.block i (pt y : Fin P.m' → F) = pt (P.block i y) := rfl
  rw [eval_liftAnswer, he] at hi
  exact hi

end PcpAlgebra

end MIPRE.SAT

end
