/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotient
import MIPRE.Foundations.LowDegree.IdempotentSplit
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Extracting polynomial factors from primitive quotient components

An idempotent represented by `E` corresponds to the factor `gcd(f,E-1)`.
Its multiples are exactly the polynomials annihilated by that component.
Primitive-component inverses therefore prove irreducibility without a Chinese
remainder construction or an enumeration of the quotient ring.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Polynomial

/-- The factor supported by the component represented by `E`. -/
def componentFactor (f E : Polynomial (ZMod 2)) : Polynomial (ZMod 2) :=
  gcd f (E - 1)

/-- An idempotent's supported factor describes its polynomial annihilator. -/
theorem componentFactor_dvd_iff (f E H : Polynomial (ZMod 2))
    (he : AdjoinRoot.mk f E * AdjoinRoot.mk f E = AdjoinRoot.mk f E) :
    componentFactor f E ∣ H ↔ AdjoinRoot.mk f E * AdjoinRoot.mk f H = 0 := by
  have hid : f ∣ E * (E - 1) := by
    apply AdjoinRoot.mk_eq_zero.mp
    rw [map_mul, map_sub, map_one, mul_sub, mul_one, he, sub_self]
  constructor
  · intro h
    rw [← map_mul]
    apply AdjoinRoot.mk_eq_zero.mpr
    exact (dvd_mul_gcd_of_dvd_mul hid).trans (mul_dvd_mul_left E h)
  · intro h
    have hprod : f ∣ E * H := AdjoinRoot.mk_eq_zero.mp (by simpa only [map_mul] using h)
    have h₁ : componentFactor f E ∣ E * H := (gcd_dvd_left f (E - 1)).trans hprod
    have h₂ : componentFactor f E ∣ (E - 1) * H :=
      dvd_mul_of_dvd_left (gcd_dvd_right f (E - 1)) H
    have hd := dvd_sub h₁ h₂
    convert hd using 1
    ring

/-- A primitive component of a quotient with bijective squaring yields a prime factor. -/
theorem componentFactor_prime (f E : Polynomial (ZMod 2)) (hf : f ≠ 0)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (he : PrimitiveBinaryComponent (AdjoinRoot.mk f E)) :
    Prime (componentFactor f E) := by
  have hne : componentFactor f E ≠ 0 :=
    ne_zero_of_dvd_ne_zero hf (gcd_dvd_left f (E - 1))
  have hunit : ¬ IsUnit (componentFactor f E) := by
    intro hu
    have hz := (componentFactor_dvd_iff f E 1 he.2.1).mp (isUnit_iff_dvd_one.mp hu)
    exact he.1 (by simpa only [map_one, mul_one] using hz)
  refine ⟨hne, hunit, ?_⟩
  intro U V huv
  by_cases hu : componentFactor f E ∣ U
  · exact Or.inl hu
  · right
    have hU : AdjoinRoot.mk f E * AdjoinRoot.mk f U ≠ 0 := by
      intro h
      exact hu ((componentFactor_dvd_iff f E U he.2.1).mpr h)
    have hEU : AdjoinRoot.mk f E * (AdjoinRoot.mk f E * AdjoinRoot.mk f U) =
        AdjoinRoot.mk f E * AdjoinRoot.mk f U := by rw [← mul_assoc, he.2.1]
    obtain ⟨z, hz⟩ := he.exists_mul_eq hsq _ hU hEU
    have hUV := (componentFactor_dvd_iff f E (U * V) he.2.1).mp huv
    rw [map_mul] at hUV
    apply (componentFactor_dvd_iff f E V he.2.1).mpr
    calc
      AdjoinRoot.mk f E * AdjoinRoot.mk f V =
          (AdjoinRoot.mk f E * AdjoinRoot.mk f U * z) * AdjoinRoot.mk f V := by rw [hz]
      _ = z * (AdjoinRoot.mk f E * (AdjoinRoot.mk f U * AdjoinRoot.mk f V)) := by ring
      _ = 0 := by rw [hUV, mul_zero]

/-- Irreducibility follows from the primitive-component primality criterion. -/
theorem componentFactor_irreducible (f E : Polynomial (ZMod 2)) (hf : f ≠ 0)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (he : PrimitiveBinaryComponent (AdjoinRoot.mk f E)) :
    Irreducible (componentFactor f E) :=
  (componentFactor_prime f E hf hsq he).irreducible

/-- Every nonzero quotient modulus has a monic supported gcd factor. -/
theorem componentFactor_monic (f E : Polynomial (ZMod 2)) (hf : f ≠ 0) :
    (componentFactor f E).Monic := by
  have hne : componentFactor f E ≠ 0 :=
    ne_zero_of_dvd_ne_zero hf (gcd_dvd_left f (E - 1))
  simpa only [componentFactor, normalize_gcd] using (Polynomial.monic_normalize hne)

/-- Orthogonal components cannot share a nonunit supported factor. -/
theorem componentFactor_isCoprime (f E H : Polynomial (ZMod 2))
    (he : Irreducible (componentFactor f E))
    (heh : AdjoinRoot.mk f E * AdjoinRoot.mk f H = 0) :
    IsCoprime (componentFactor f E) (componentFactor f H) := by
  apply he.coprime_iff_not_dvd.mpr
  intro hd
  have hprod : f ∣ E * H := AdjoinRoot.mk_eq_zero.mp (by simpa only [map_mul] using heh)
  have h₁ : componentFactor f E ∣ E * H := (gcd_dvd_left f (E - 1)).trans hprod
  have h₂ : componentFactor f E ∣ (E - 1) * H :=
    dvd_mul_of_dvd_left (gcd_dvd_right f (E - 1)) H
  have h₃ : componentFactor f E ∣ H - 1 := hd.trans (gcd_dvd_right f (H - 1))
  have hcomb := dvd_sub (dvd_sub h₁ h₂) h₃
  have hone : componentFactor f E ∣ 1 := by
    convert hcomb using 1
    ring
  exact he.not_isUnit (isUnit_iff_dvd_one.mpr hone)

/-- A complete orthogonal primitive family reconstructs its monic quotient modulus. -/
theorem componentFactors_prod (f : Polynomial (ZMod 2)) (hf : f.Monic)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    {n : ℕ} (E : Fin n → Polynomial (ZMod 2))
    (he : ∀ i, PrimitiveBinaryComponent (AdjoinRoot.mk f (E i)))
    (horth : Pairwise (fun i j => AdjoinRoot.mk f (E i) * AdjoinRoot.mk f (E j) = 0))
    (hsum : ∑ i, AdjoinRoot.mk f (E i) = 1) :
    ∏ i, componentFactor f (E i) = f := by
  have hirr (i : Fin n) : Irreducible (componentFactor f (E i)) :=
    componentFactor_irreducible f (E i) hf.ne_zero hsq (he i)
  have hcop : Pairwise (fun i j => IsCoprime (componentFactor f (E i))
      (componentFactor f (E j))) := by
    intro i j hij
    exact componentFactor_isCoprime f (E i) (E j) (hirr i) (horth hij)
  have hdiv : (∏ i, componentFactor f (E i)) ∣ f :=
    Fintype.prod_dvd_of_coprime hcop (fun i => gcd_dvd_left f (E i - 1))
  have hzero (i : Fin n) : AdjoinRoot.mk f (E i) *
      AdjoinRoot.mk f (∏ j, componentFactor f (E j)) = 0 := by
    apply (componentFactor_dvd_iff f (E i) _ (he i).2.1).mp
    exact Finset.dvd_prod_of_mem (fun j => componentFactor f (E j)) (Finset.mem_univ i)
  have hz : (∑ i, AdjoinRoot.mk f (E i)) *
      AdjoinRoot.mk f (∏ j, componentFactor f (E j)) = 0 := by
    rw [Finset.sum_mul]
    simp only [hzero, Finset.sum_const_zero]
  rw [hsum, one_mul] at hz
  have hrev : f ∣ ∏ i, componentFactor f (E i) := AdjoinRoot.mk_eq_zero.mp hz
  have hmonic : (∏ i, componentFactor f (E i)).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => componentFactor_monic f (E i) hf.ne_zero)
  exact dvd_antisymm_of_normalize_eq hmonic.normalize_eq_self hf.normalize_eq_self hdiv hrev

/-- The reconstruction theorem in the list representation used by the programs. -/
theorem componentFactors_list_prod (f : Polynomial (ZMod 2)) (hf : f.Monic)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (l : List (Polynomial (ZMod 2)))
    (hl : ComponentFamily (l.map (AdjoinRoot.mk f)))
    (he : ∀ E ∈ l, PrimitiveBinaryComponent (AdjoinRoot.mk f E)) :
    (l.map (componentFactor f)).prod = f := by
  have hpair : l.Pairwise (fun E H => AdjoinRoot.mk f E * AdjoinRoot.mk f H = 0) :=
    List.pairwise_map.mp hl.orthogonal
  have horth : Pairwise (fun i j : Fin l.length =>
      AdjoinRoot.mk f (l.get i) * AdjoinRoot.mk f (l.get j) = 0) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpair.rel_get_of_lt h
    · rw [mul_comm]
      exact hpair.rel_get_of_lt h
  have hsum : (∑ i : Fin l.length, AdjoinRoot.mk f (l.get i)) = 1 := by
    simpa only [List.get_eq_getElem, Fin.sum_univ_fun_getElem] using hl.sum_eq_one
  have hp := componentFactors_prod f hf hsq (fun i : Fin l.length => l.get i)
    (fun i => he _ (List.get_mem l i)) horth hsum
  simpa only [List.get_eq_getElem, Fin.prod_univ_fun_getElem] using hp

/-- The quotient map reads coefficient bits by evaluation at its canonical root. -/
theorem mk_polyOfBits (f : Polynomial (ZMod 2)) (a : Cost.BitStr) :
    AdjoinRoot.mk f (polyOfBits a) = BinaryPolynomial.evalBits (AdjoinRoot.root f) a := by
  rw [← AdjoinRoot.aeval_eq]
  exact BinaryPolynomial.eval₂_polyOfBits (algebraMap (ZMod 2) (AdjoinRoot f)) _ a

/-- Canonical coordinate bits give a polynomial representative of the quotient element. -/
@[simp] theorem mk_polyOfBits_toBits (f : Polynomial (ZMod 2)) (hf : f.Monic)
    (x : AdjoinRoot f) :
    AdjoinRoot.mk f (polyOfBits (toBits f hf x)) = x := by
  rw [mk_polyOfBits, evalBits_toBits]

/-- Canonical representatives of a primitive component family yield the complete factorization. -/
theorem componentFactors_toBits_prod (f : Polynomial (ZMod 2)) (hf : f.Monic)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (l : List (AdjoinRoot f)) (hl : ComponentFamily l)
    (he : ∀ e ∈ l, PrimitiveBinaryComponent e) :
    (l.map (fun e => componentFactor f (polyOfBits (toBits f hf e)))).prod = f := by
  have hrep : (l.map (fun e => polyOfBits (toBits f hf e))).map (AdjoinRoot.mk f) = l := by
    simp only [List.map_map, Function.comp_def, mk_polyOfBits_toBits]
    exact List.map_id l
  have hfam : ComponentFamily
      ((l.map (fun e => polyOfBits (toBits f hf e))).map (AdjoinRoot.mk f)) := hrep.symm ▸ hl
  have hp := componentFactors_list_prod f hf hsq
    (l.map (fun e => polyOfBits (toBits f hf e))) hfam (by
      intro E hE
      obtain ⟨e, he', rfl⟩ := List.mem_map.mp hE
      simpa only [mk_polyOfBits_toBits] using he e he')
  simpa only [List.map_map, Function.comp_def] using hp

end MIPRE.LowDegree.BinaryQuotient

end
