/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.SignedPerm
public import MIPRE.Foundations.Measurement
public import MIPRE.Tactics

@[expose] public section

/-!
# The three forms of a projective measurement with outcomes in `F₂^k`

Paper II, §2.1 (II:972–1006) and §3.4 (II:2887–2982). A projective measurement with outcomes in
`F₂^k` can be given in three forms that carry the same data (II:988):

* the *projective form*, projections `P_a` summing to one, for `a ∈ F₂^k`;
* the *observable form*, `k` commuting involutions `U i`;
* the *representation form*, the homomorphism `α ↦ U^α = ∏_i (U i)^{α_i}` on `F₂^k`.

The passage from the observable form to the projective form is the Fourier transform
`P_a = ∏_i (1 + (-1)^{a_i} U i) / 2` (`MIPRE.Tailored.fourierProj`, defined with the tailored
games in `MIPRE.Tailored.Game`). This file proves, in any complex `⋆`-algebra:

* `isPVMIn_fourierProj`: the Fourier transform of commuting self-adjoint involutions is a
  projective measurement, by induction on `k` from the case of one involution
  (`isPVMIn_fourierFactor`) and products of commuting measurements (`IsPVMIn.prod_of_commute`);
* `mul_fourierProj`, `obsChar_mul_fourierProj`: `P_a` lies in the `(-1)^{a_i}`-eigenspace of
  `U i`, and in the `(-1)^{⟨α, a⟩}`-eigenspace of `U^α`;
* `pvmObs_fourierProj_bit`, `pvmObs_fourierProj_dotBit`: the inverse transforms,
  `U i = ∑_a (-1)^{a_i} P_a` and `U^α = ∑_a (-1)^{⟨α, a⟩} P_a` (II:982);
* `Commute.fourierProj_right`: whatever commutes with the observables commutes with the
  projections, so a strategy commuting along edges in observable form does so in projective
  form (II:1124);
* `isDiag_fourierProj`: diagonal observables have diagonal projections (II:996);
* `pvmObs_coarse_affine`: *affine data processing* (Claim II:2918) — the observable of the
  coarse-graining along `a ↦ c + ⟨α, a⟩` is `(-1)^c U^α`; with `IsPVMIn.coarse`, the diagonal
  data processing of Claim II:2902 is `isDiag_coarse`.
-/

namespace MIPRE.Tailored

open Finset

/-! ## `⟨α, a⟩` over `F₂` -/

/-- The inner product `⟨α, a⟩ = ∑_i α_i a_i` over `F₂`. -/
def dotBit {k : ℕ} (α a : Fin k → Bool) : Bool :=
  (List.finRange k).foldr (fun i acc => xor (α i && a i) acc) false

@[simp] theorem dotBit_zero (α a : Fin 0 → Bool) : dotBit α a = false := by
  simp [dotBit]

theorem dotBit_succ {k : ℕ} (α a : Fin (k + 1) → Bool) :
    dotBit α a = xor (α 0 && a 0) (dotBit (fun i => α i.succ) fun i => a i.succ) := by
  simp only [dotBit, List.finRange_succ, List.foldr_cons, List.foldr_map]

section Ring

variable {R : Type*} [Ring R] {k : ℕ}

/-- The representation form `U^α = ∏_i (U i)^{α_i}` of a family of commuting involutions. -/
def obsChar (U : Fin k → R) (α : Fin k → Bool) : R :=
  ((List.finRange k).map fun i => if α i then U i else 1).prod

@[simp] theorem obsChar_zero (U : Fin 0 → R) (α : Fin 0 → Bool) : obsChar U α = 1 := by
  simp [obsChar]

theorem obsChar_succ (U : Fin (k + 1) → R) (α : Fin (k + 1) → Bool) :
    obsChar U α = (if α 0 then U 0 else 1) * obsChar (fun i => U i.succ) fun i => α i.succ := by
  simp only [obsChar, List.finRange_succ, List.map_cons, List.map_map, List.prod_cons]
  rfl

theorem _root_.Commute.obsChar_right {x : R} {U : Fin k → R} (h : ∀ i, Commute x (U i))
    (α : Fin k → Bool) : Commute x (obsChar U α) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  split_ifs
  · exact h i
  · exact Commute.one_right x

variable [StarRing R]

/-- **Products of commuting projective measurements**: if every element of `P` commutes with
every element of `Q`, then `(a, b) ↦ P a * Q b` is a projective measurement. -/
theorem _root_.MIPRE.IsPVMIn.prod_of_commute {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ'] {P : Λ → R}
    {Q : Λ' → R} (hP : IsPVMIn P) (hQ : IsPVMIn Q) (hc : ∀ a b, Commute (P a) (Q b)) :
    IsPVMIn fun p : Λ × Λ' => P p.1 * Q p.2 where
  star_eq p := by rw [star_mul, hP.star_eq, hQ.star_eq, (hc p.1 p.2).eq]
  idem p := by
    rw [(hc p.1 p.2).symm.mul_mul_mul_comm, hP.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hQ.sum_eq_one, mul_one]
    exact hP.sum_eq_one
  orthogonal {p q} hpq := by
    rw [(hc q.1 p.2).symm.mul_mul_mul_comm]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      rw [hQ.orthogonal h2, mul_zero]
    · rw [hP.orthogonal h1, zero_mul]

end Ring

section Algebra

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-! ## One involution -/

theorem fourierFactor_def (u : R) (b : Bool) :
    fourierFactor u b = (1 / 2 : ℂ) • (1 + bitSign b • u) := rfl

theorem fourierFactor_false_add_true (u : R) :
    fourierFactor u false + fourierFactor u true = 1 := by
  simp only [fourierFactor, bitSign_false, bitSign_true]
  module

theorem fourierFactor_mul_self {u : R} (hu : u * u = 1) (b : Bool) :
    fourierFactor u b * fourierFactor u b = fourierFactor u b := by
  simp only [fourierFactor, smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hu]
  cases b <;> simp only [bitSign_false, bitSign_true] <;> module

theorem fourierFactor_mul_of_ne {u : R} (hu : u * u = 1) {b c : Bool} (h : b ≠ c) :
    fourierFactor u b * fourierFactor u c = 0 := by
  simp only [fourierFactor, smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hu]
  cases b <;> cases c
  · exact absurd rfl h
  · simp only [bitSign_false, bitSign_true]; module
  · simp only [bitSign_false, bitSign_true]; module
  · exact absurd rfl h

/-- `u` acts on the range of `(1 + (-1)^b u)/2` as `(-1)^b`. -/
theorem mul_fourierFactor {u : R} (hu : u * u = 1) (b : Bool) :
    u * fourierFactor u b = bitSign b • fourierFactor u b := by
  simp only [fourierFactor, mul_smul_comm, mul_add, mul_one, hu]
  cases b <;> simp only [bitSign_false, bitSign_true] <;> module

theorem _root_.Commute.fourierFactor_right {x u : R} (h : Commute x u) (b : Bool) :
    Commute x (fourierFactor u b) :=
  ((Commute.one_right x).add_right (h.smul_right _)).smul_right _

section Star

variable [StarRing R] [StarModule ℂ R]

theorem star_fourierFactor {u : R} (hu : star u = u) (b : Bool) :
    star (fourierFactor u b) = fourierFactor u b := by
  simp [fourierFactor, hu]

/-- **One involution is a projective measurement with two outcomes.** -/
theorem isPVMIn_fourierFactor {u : R} (hu : u * u = 1) (hsa : star u = u) :
    IsPVMIn (fourierFactor u) where
  star_eq b := star_fourierFactor hsa b
  idem b := fourierFactor_mul_self hu b
  sum_eq_one := by
    rw [Fintype.sum_bool, add_comm]
    exact fourierFactor_false_add_true u
  orthogonal h := fourierFactor_mul_of_ne hu h

end Star

/-! ## The Fourier transform -/

@[simp] theorem fourierProj_zero (U : Fin 0 → R) (a : Fin 0 → Bool) : fourierProj U a = 1 := by
  simp [fourierProj]

theorem fourierProj_succ {k : ℕ} (U : Fin (k + 1) → R) (a : Fin (k + 1) → Bool) :
    fourierProj U a =
      fourierFactor (U 0) (a 0) * fourierProj (fun i => U i.succ) fun i => a i.succ := by
  simp only [fourierProj, List.finRange_succ, List.map_cons, List.map_map, List.prod_cons]
  rfl

variable {k : ℕ}

/-- **Whatever commutes with the observables commutes with the projections.** -/
theorem _root_.Commute.fourierProj_right {x : R} {U : Fin k → R} (h : ∀ i, Commute x (U i))
    (a : Fin k → Bool) : Commute x (fourierProj U a) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  exact (h i).fourierFactor_right _

/-- **Observables commuting across two families give projections commuting across them**: a
strategy commuting along an edge in observable form does so in projective form (II:1124). -/
theorem _root_.Commute.fourierProj_fourierProj {k' : ℕ} {U : Fin k → R} {V : Fin k' → R}
    (h : ∀ i j, Commute (U i) (V j)) (a : Fin k → Bool) (b : Fin k' → Bool) :
    Commute (fourierProj U a) (fourierProj V b) :=
  Commute.fourierProj_right (fun j => (Commute.fourierProj_right (fun i => (h i j).symm) a).symm) b

/-- **`P_a` lies in the `(-1)^{a_i}`-eigenspace of `U i`.** -/
theorem mul_fourierProj {U : Fin k → R} (hinv : ∀ i, U i * U i = 1)
    (hcomm : ∀ i j, Commute (U i) (U j)) (i : Fin k) (a : Fin k → Bool) :
    U i * fourierProj U a = bitSign (a i) • fourierProj U a := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [fourierProj_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← mul_assoc, mul_fourierFactor (hinv 0), smul_mul_assoc]
    · have h' := ih (fun i => hinv i.succ) (fun i j => hcomm i.succ j.succ) j fun i => a i.succ
      rw [← mul_assoc, ((hcomm j.succ 0).fourierFactor_right (a 0)).eq, mul_assoc, h',
        mul_smul_comm]

/-- **`P_a` lies in the `(-1)^{⟨α, a⟩}`-eigenspace of `U^α`.** -/
theorem obsChar_mul_fourierProj {U : Fin k → R} (hinv : ∀ i, U i * U i = 1)
    (hcomm : ∀ i j, Commute (U i) (U j)) (α a : Fin k → Bool) :
    obsChar U α * fourierProj U a = bitSign (dotBit α a) • fourierProj U a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h' := ih (fun i => hinv i.succ) (fun i j => hcomm i.succ j.succ) (fun i => α i.succ)
      fun i => a i.succ
    have hc : Commute (obsChar (fun i => U i.succ) fun i => α i.succ)
        (fourierFactor (U 0) (a 0)) :=
      (Commute.obsChar_right (fun i => ((hcomm i.succ 0).fourierFactor_right (a 0)).symm) _).symm
    rw [obsChar_succ, fourierProj_succ, dotBit_succ, bitSign_xor, mul_assoc,
      ← mul_assoc (obsChar _ _), hc.eq, mul_assoc, h', mul_smul_comm, mul_smul_comm,
      ← mul_assoc]
    by_cases hα : α 0 = true
    · rw [ite_eq_left hα, mul_fourierFactor (hinv 0), hα, Bool.true_and, smul_mul_assoc, smul_smul,
        mul_comm]
    · rw [ite_eq_right hα, one_mul]
      rw [Bool.not_eq_true] at hα
      rw [hα, Bool.false_and, bitSign_false, one_mul]

/-! ## The Fourier transform is a projective measurement -/

section Star

variable [StarRing R] [StarModule ℂ R]

/-- **The Fourier transform of commuting self-adjoint involutions is a projective
measurement** (II:974): the projective form of the measurement whose observable form is
`U`. -/
theorem isPVMIn_fourierProj {U : Fin k → R} (hinv : ∀ i, U i * U i = 1)
    (hsa : ∀ i, star (U i) = U i) (hcomm : ∀ i j, Commute (U i) (U j)) :
    IsPVMIn (fourierProj U) := by
  induction k with
  | zero =>
    refine ⟨fun a => by simp, fun a => by simp, ?_, fun {a b} h => absurd (Subsingleton.elim a b) h⟩
    simp
  | succ k ih =>
    have hP := isPVMIn_fourierFactor (hinv 0) (hsa 0)
    have hQ := ih (fun i => hinv i.succ) (fun i => hsa i.succ) fun i j => hcomm i.succ j.succ
    have hPQ := hP.prod_of_commute hQ fun b a =>
      Commute.fourierProj_right (fun i => ((hcomm i.succ 0).fourierFactor_right b).symm) a
    -- reindex along `F₂^{k+1} ≃ F₂ × F₂^k`
    let e := (Fin.consEquiv fun _ : Fin (k + 1) => Bool).symm
    have hre : IsPVMIn fun a : Fin (k + 1) → Bool =>
        fourierFactor (U 0) (e a).1 * fourierProj (fun i => U i.succ) (e a).2 :=
      { star_eq := fun a => hPQ.star_eq (e a)
        idem := fun a => hPQ.idem (e a)
        sum_eq_one := by
          rw [← hPQ.sum_eq_one]
          exact e.sum_comp fun p => fourierFactor (U 0) p.1 * fourierProj (fun i => U i.succ) p.2
        orthogonal := fun h => hPQ.orthogonal fun h' => h (e.injective h') }
    convert hre using 1
    funext a
    rw [fourierProj_succ]
    rfl

/-- **The inverse Fourier transform, in observable form**: `U i = ∑_a (-1)^{a_i} P_a`
(II:982). -/
theorem pvmObs_fourierProj_bit {U : Fin k → R} (hinv : ∀ i, U i * U i = 1)
    (hsa : ∀ i, star (U i) = U i) (hcomm : ∀ i j, Commute (U i) (U j)) (i : Fin k) :
    pvmObs (fourierProj U) (fun a => bitSign (a i)) = U i := by
  unfold pvmObs
  simp_rw [← mul_fourierProj hinv hcomm i]
  rw [← Finset.mul_sum, (isPVMIn_fourierProj hinv hsa hcomm).sum_eq_one, mul_one]

/-- **The inverse Fourier transform, in representation form**: `U^α = ∑_a (-1)^{⟨α, a⟩} P_a`
(II:982). -/
theorem pvmObs_fourierProj_dotBit {U : Fin k → R} (hinv : ∀ i, U i * U i = 1)
    (hsa : ∀ i, star (U i) = U i) (hcomm : ∀ i j, Commute (U i) (U j)) (α : Fin k → Bool) :
    pvmObs (fourierProj U) (fun a => bitSign (dotBit α a)) = obsChar U α := by
  unfold pvmObs
  simp_rw [← obsChar_mul_fourierProj hinv hcomm α]
  rw [← Finset.mul_sum, (isPVMIn_fourierProj hinv hsa hcomm).sum_eq_one, mul_one]

/-- **Affine data processing** (Claim II:2918): coarse-graining the Fourier transform of `U`
along the affine map `a ↦ c + ⟨α, a⟩` gives the measurement whose observable is
`(-1)^c U^α`. -/
theorem pvmObs_coarse_affine {U : Fin k → R} (hinv : ∀ i, U i * U i = 1)
    (hsa : ∀ i, star (U i) = U i) (hcomm : ∀ i j, Commute (U i) (U j)) (α : Fin k → Bool)
    (c : Bool) :
    pvmObs (fun b : Bool => ∑ a ∈ univ.filter fun a => xor c (dotBit α a) = b, fourierProj U a)
      bitSign = bitSign c • obsChar U α := by
  rw [← pvmObs_fourierProj_dotBit hinv hsa hcomm α]
  unfold pvmObs
  simp_rw [Finset.smul_sum]
  have hfib : ∀ b : Bool,
      (∑ a ∈ univ.filter fun a => xor c (dotBit α a) = b, bitSign b • fourierProj U a) =
        ∑ a ∈ univ.filter fun a => xor c (dotBit α a) = b,
          bitSign (xor c (dotBit α a)) • fourierProj U a :=
    fun b => Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]
  rw [Finset.sum_congr rfl fun b _ => hfib b,
    Finset.sum_fiberwise univ (fun a => xor c (dotBit α a))
      fun a => bitSign (xor c (dotBit α a)) • fourierProj U a]
  simp only [bitSign_xor, mul_smul]

end Star

end Algebra

/-! ## Diagonal measurements -/

section Diagonal

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}

/-- A product of diagonal matrices is diagonal. -/
theorem isDiag_mul {A B : Matrix n n ℂ} (hA : A.IsDiag) (hB : B.IsDiag) : (A * B).IsDiag := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, Matrix.diagonal_mul_diagonal]
  exact Matrix.isDiag_diagonal _

/-- **Diagonal observables have diagonal projections** (II:996). -/
theorem isDiag_fourierProj {U : Fin k → Matrix n n ℂ} (h : ∀ i, (U i).IsDiag)
    (a : Fin k → Bool) : (fourierProj U a).IsDiag := by
  unfold fourierProj
  induction (List.finRange k) with
  | nil => exact Matrix.isDiag_one
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons]
    exact isDiag_mul ((Matrix.isDiag_one.add ((h i).smul _)).smul _) ih

omit [Fintype n] [DecidableEq n] in
/-- **Diagonal data processing** (Claim II:2902): coarse-graining a diagonal measurement gives a
diagonal measurement. -/
theorem isDiag_coarse {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ'] {P : Λ → Matrix n n ℂ}
    (h : ∀ a, (P a).IsDiag) (f : Λ → Λ') (b : Λ') :
    (∑ a ∈ univ.filter fun a => f a = b, P a).IsDiag := by
  classical
  induction (univ.filter fun a => f a = b) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a).add ih

end Diagonal

end MIPRE.Tailored

end
