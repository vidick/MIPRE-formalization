/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Fourier

@[expose] public section

/-!
# The bit observables of an encoded measurement

A projective measurement `P` with outcomes in a finite set `Λ`, together with an encoding
`enc : Λ → F₂^k`, gives `k` observables, one per bit of the encoding:
`encObs P enc i = ∑_λ (-1)^{enc(λ)_i} P_λ` (`encObs`). These are the observables a
permutation strategy must supply at a question whose answers are the encoded outcomes of `P`.
This file proves that they have every property of `MIPRE.Tailored.PermStrategy` but the
signed-permutation one, which depends on `P`:

* `encObs_mul_self`, `star_encObs`, `commute_encObs`: they are commuting self-adjoint
  involutions;
* `fourierProj_encObs`: their Fourier transform is the push-forward of `P` along `enc`,
  `P'_a = ∑_{enc(λ) = a} P_λ`; so the permutation strategy built from them measures exactly
  the encoded outcomes of `P`;
* `commute_encObs_encObs`: they commute with the bit observables of any measurement commuting
  with `P`.
-/

namespace MIPRE.Tailored

open Finset

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
variable {Λ : Type*} [Fintype Λ] {k : ℕ}

/-- The observable of the `i`-th bit of the encoded outcome. -/
noncomputable def encObs (P : Λ → R) (enc : Λ → Fin k → Bool) (i : Fin k) : R :=
  pvmObs P fun l => bitSign (enc l i)

section

variable {P : Λ → R} (hP : IsPVMIn P) (enc : Λ → Fin k → Bool)
include hP

theorem encObs_mul_self (i : Fin k) : encObs P enc i * encObs P enc i = 1 :=
  hP.pvmObs_mul_self fun _ => bitSign_mul_self _

theorem commute_encObs (i j : Fin k) : Commute (encObs P enc i) (encObs P enc j) :=
  hP.pvmObs_comm _ _

theorem star_encObs [StarModule ℂ R] (i : Fin k) : star (encObs P enc i) = encObs P enc i :=
  hP.pvmObs_star_eq fun l => by cases enc l i <;> simp [bitSign]

omit [StarRing R] hP in
/-- A coarse-graining of `P`, as the observable of an indicator weighting. -/
theorem sum_filter_eq_pvmObs (p : Λ → Prop) [DecidablePred p] :
    ∑ l ∈ univ.filter p, P l = pvmObs P fun l => if p l then 1 else 0 := by
  rw [pvmObs, Finset.sum_filter]
  exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp

omit hP in
/-- `(1 + (-1)^b (-1)^c) / 2` is the indicator of `b = c`. -/
theorem half_one_add_bitSign_mul (b c : Bool) :
    (1 / 2 : ℂ) * (1 + bitSign b * bitSign c) = if c = b then 1 else 0 := by
  cases b <;> cases c <;> norm_num [bitSign]

/-- **The Fourier factor of one bit observable** is the coarse-graining of `P` onto that bit. -/
theorem fourierFactor_encObs (i : Fin k) (b : Bool) :
    fourierFactor (encObs P enc i) b = ∑ l ∈ univ.filter fun l => enc l i = b, P l := by
  rw [sum_filter_eq_pvmObs, fourierFactor_def, encObs, ← hP.pvmObs_one, pvmObs, pvmObs,
    pvmObs, Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.one_apply, smul_smul, ← add_smul, smul_smul, half_one_add_bitSign_mul]

/-- **The Fourier transform of the bit observables is the push-forward of `P` along `enc`.** -/
theorem fourierProj_encObs (a : Fin k → Bool) :
    fourierProj (encObs P enc) a = ∑ l ∈ univ.filter fun l => enc l = a, P l := by
  induction k with
  | zero =>
    rw [fourierProj_zero, Finset.filter_true_of_mem fun l _ => funext fun i => i.elim0]
    exact hP.sum_eq_one.symm
  | succ k ih =>
    rw [fourierProj_succ]
    have h := ih (fun l i => enc l i.succ) (fun i => a i.succ)
    simp only [encObs] at h ⊢
    rw [show (fun i : Fin k => pvmObs P fun l => bitSign (enc l i.succ)) =
      encObs P (fun l i => enc l i.succ) from rfl, h]
    change fourierFactor (encObs P enc 0) (a 0) * _ = _
    rw [fourierFactor_encObs hP, sum_filter_eq_pvmObs, sum_filter_eq_pvmObs,
      sum_filter_eq_pvmObs, hP.pvmObs_mul]
    congr 1
    funext l
    simp only [Pi.mul_apply]
    have key : enc l = a ↔
        enc l 0 = a 0 ∧ (fun i : Fin k => enc l i.succ) = fun i => a i.succ := by
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨h0, ht⟩
        funext i
        exact Fin.cases h0 (fun j => congrFun ht j) i
    by_cases h0 : enc l 0 = a 0 <;>
      by_cases ht : (fun i : Fin k => enc l i.succ) = fun i => a i.succ <;> simp [h0, ht, key]

end

omit [StarRing R] in
/-- **Bit observables of commuting measurements commute.** -/
theorem commute_encObs_encObs {Λ' : Type*} [Fintype Λ'] {k' : ℕ} {P : Λ → R} {Q : Λ' → R}
    (h : ∀ l l', Commute (P l) (Q l')) (enc : Λ → Fin k → Bool) (enc' : Λ' → Fin k' → Bool)
    (i : Fin k) (j : Fin k') : Commute (encObs P enc i) (encObs Q enc' j) :=
  Commute.sum_left _ _ _ fun l _ => Commute.sum_right _ _ _ fun l' _ =>
    ((h l l').smul_left _).smul_right _

end MIPRE.Tailored

end
