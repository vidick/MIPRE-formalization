/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.StateDistance
import MIPRE.Foundations.Weyl

/-!
# Parseval for the character transform

The combining stage of the Pauli appendix moves between two descriptions of the same data: an
`F_q`-valued measurement `{P_a}` and its **binary observables**
`O^r = sum_a (-1)^{tr(ar)} P_a`, one for each `r in F_q`. The two are Fourier transforms of each
other, and what the estimates need is that the transform is an **isometry**: a bound on the
observables, averaged over `r`, is a bound on the measurement elements, summed over `a`, and
conversely.

This file is that dictionary, for vectors and for families of matrices applied to a state:

* `fourierVec` is the transform of a family of vectors indexed by `V = F_q^n`, against the
  characters of the trace form, and `sum_norm_fourierVec_sq` is Parseval --- an identity, not an
  estimate;
* `trObs` is the observable of an `F_q`-indexed family at a parameter `r`, `trObs_fourier` inverts
  it, and `sum_stateSqNorm_eq_avg_trObs` is Parseval in the form the appendix uses: the sum over
  outcomes of the squared state-norms of the elements is the average over `r` of the squared
  state-norms of the observables.

The one-field character orthogonality it all rests on is `MIPRE.Weyl.sum_sgn_trMul`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix MIPRE.Weyl
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]

set_option linter.unusedSectionVars false

/-! ## The transform of a family of vectors -/

/-- **The character transform** of a family of vectors indexed by `V = F_q^n`. -/
def fourierVec (T : (n → F) → (N → ℂ)) (e : n → F) : N → ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • T a

/-- The unnormalized transform: the same sum without the `1/|V|`. -/
def fourierVecRaw (T : (n → F) → (N → ℂ)) (e : n → F) : N → ℂ :=
  ∑ a : n → F, sgn (trDot a e) • T a

theorem fourierVec_eq_smul (T : (n → F) → (N → ℂ)) (e : n → F) :
    fourierVec T e = (Fintype.card (n → F) : ℂ)⁻¹ • fourierVecRaw T e := rfl

/-- **The character sum, on the sesquilinear form.** Only the diagonal survives. -/
theorem sum_dotProduct_fourierVecRaw (T : (n → F) → (N → ℂ)) :
    ∑ e : n → F, star (fourierVecRaw T e) ⬝ᵥ fourierVecRaw T e
      = (Fintype.card (n → F) : ℂ) * ∑ a : n → F, star (T a) ⬝ᵥ T a := by
  classical
  have hterm : ∀ e : n → F, star (fourierVecRaw T e) ⬝ᵥ fourierVecRaw T e
      = ∑ a : n → F, ∑ b : n → F, sgn (trDot (a + b) e) * (star (T a) ⬝ᵥ T b) := by
    intro e
    rw [fourierVecRaw, star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_smul, star_sgn, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, trDot_add_left, sgn_add, mul_assoc]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => hterm e]
  rw [show (∑ e : n → F, ∑ a : n → F, ∑ b : n → F,
        sgn (trDot (a + b) e) * (star (T a) ⬝ᵥ T b))
      = ∑ a : n → F, ∑ b : n → F,
          (∑ e : n → F, sgn (trDot (a + b) e)) * (star (T a) ⬝ᵥ T b) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]]
  have hinner : ∀ a : n → F, (∑ b : n → F, (∑ e : n → F, sgn (trDot (a + b) e))
        * (star (T a) ⬝ᵥ T b))
      = (Fintype.card (n → F) : ℂ) * (star (T a) ⬝ᵥ T a) := by
    intro a
    refine (Finset.sum_eq_single_of_mem a (mem_univ a) fun b _ hb => ?_).trans ?_
    · have hne : a + b ≠ 0 := fun h => hb ((add_eq_zero_iff_vec a b).mp h).symm
      rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_comm],
        sum_sgn_trDot hne, zero_mul]
    · congr 1
      rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
          rw [add_self_vec, trDot_zero_left, sgn_zero],
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hinner a, ← Finset.mul_sum]

/-- The sesquilinear form of a vector with itself is its squared norm, as a complex number. -/
theorem dotProduct_star_self (v : N → ℂ) : star v ⬝ᵥ v = ((‖evec v‖ ^ 2 : ℝ) : ℂ) := by
  have hentry : ∀ i : N, star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  have hsq : ‖evec v‖ ^ 2 = ∑ i : N, ‖v i‖ ^ 2 := by
    rw [norm_evec_sq, dotProduct, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hentry i, Complex.ofReal_re]
  rw [dotProduct, hsq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => hentry i

/-- **Parseval for the character transform.** The transform is an isometry up to the
normalization: the sum of the squared norms of the transform is the *average* of the squared
norms of the family. No hypothesis on the family at all. -/
theorem sum_norm_fourierVec_sq (T : (n → F) → (N → ℂ)) :
    ∑ e : n → F, ‖evec (fourierVec T e)‖ ^ 2
      = (Fintype.card (n → F) : ℝ)⁻¹ * ∑ a : n → F, ‖evec (T a)‖ ^ 2 := by
  classical
  have hNR : (Fintype.card (n → F) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos (α := n → F)).ne'
  have hraw : ∑ e : n → F, ‖evec (fourierVecRaw T e)‖ ^ 2
      = (Fintype.card (n → F) : ℝ) * ∑ a : n → F, ‖evec (T a)‖ ^ 2 := by
    have h1 : (∑ e : n → F, star (fourierVecRaw T e) ⬝ᵥ fourierVecRaw T e)
        = ((∑ e : n → F, ‖evec (fourierVecRaw T e)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun e _ => dotProduct_star_self _
    have h2 : (∑ a : n → F, star (T a) ⬝ᵥ T a)
        = ((∑ a : n → F, ‖evec (T a)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun a _ => dotProduct_star_self _
    have h3 := sum_dotProduct_fourierVecRaw T
    rw [h1, h2] at h3
    exact_mod_cast h3
  have hscale : ∀ e : n → F, ‖evec (fourierVec T e)‖ ^ 2
      = ((Fintype.card (n → F) : ℝ)⁻¹ * (Fintype.card (n → F) : ℝ)⁻¹)
        * ‖evec (fourierVecRaw T e)‖ ^ 2 := by
    intro e
    rw [fourierVec_eq_smul, show evec ((Fintype.card (n → F) : ℂ)⁻¹ • fourierVecRaw T e)
        = (Fintype.card (n → F) : ℂ)⁻¹ • evec (fourierVecRaw T e) from rfl,
      norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
    ring
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => hscale e, ← Finset.mul_sum, hraw]
  field_simp

/-! ## The one-field transform, and its inverse

The appendix's other direction: an `F_q`-valued family `P` has binary observables
`O^r = sum_a (-1)^{tr(ar)} P_a`, and `P` is recovered from `O` by the same transform, averaged.
-/

/-- The binary observable of an `F_q`-indexed family of operators at the probe `r`. -/
def trObs (P : F → Matrix N N ℂ) (r : F) : Matrix N N ℂ :=
  ∑ a : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • P a

/-- The transform back: the `a`-th element recovered from the observables. -/
def trFourier (A : F → Matrix N N ℂ) (a : F) : Matrix N N ℂ :=
  (Fintype.card F : ℂ)⁻¹ • ∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • A r

/-- **Fourier inversion over one copy of the field.** -/
theorem trFourier_trObs (P : F → Matrix N N ℂ) (a : F) : trFourier (trObs P) a = P a := by
  classical
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this.ne'
  have hswap : (∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • trObs P r)
      = ∑ b : F, (∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * (a + b)))) • P b := by
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by
        rw [trObs, Finset.smul_sum,
          Finset.sum_congr rfl fun b (_ : b ∈ univ) => by
            rw [smul_smul, ← sgn_add, ← map_add, ← add_mul, mul_comm (a + b) r]],
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_smul]
  rw [trFourier, hswap, Finset.sum_eq_single_of_mem a (mem_univ a) fun b _ hb => ?_]
  · rw [add_self, sum_sgn_trMul_zero, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · rw [sum_sgn_trMul (x := a + b) fun h => hb ((add_eq_zero_iff a b).mp h).symm, zero_smul]

/-! ## Coarse-grainings and the transform

A measurement is usually presented as a POVM whose outcomes are then *read* by a function; the
transform has to see through that reading. Both lemmas below are the same regrouping of a sum
along the fibres of the reading. -/

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

/-- **The one-field transform sees through a coarse-graining.** -/
theorem trObs_map (P : POVM A dA) (f : A → F) (r : F) :
    trObs (fun a : F => (((P.map f).mats a).val)) r
      = ∑ x : A, sgn (Algebra.trace (ZMod 2) F (f x * r)) • ((P.mats x).val) := by
  classical
  have hsplit : ∀ a : F, (((P.map f).mats a).val)
      = ∑ x ∈ univ.filter fun x => f x = a, ((P.mats x).val) := fun a =>
    AddSubmonoidClass.coe_finsetSum _ _
  rw [trObs, ← Finset.sum_fiberwise (univ : Finset A) f
    fun x => sgn (Algebra.trace (ZMod 2) F (f x * r)) • ((P.mats x).val)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hsplit, Finset.smul_sum]
  exact Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]

/-! ## The two-field transform of a product

The combined measurement is indexed by a *pair* `(a, b)`, and the family it transforms is a
product of one operator depending on `r` and one depending on `s`. The transform factorizes,
which is why the combined measurement is the product of the two marginals whenever the two
commute. -/

/-- The pair `(r, s)` as a vector of `F_q^2`. -/
def pairVec (r s : F) : Fin 2 → F := fun i => if i = 0 then r else s

@[simp] theorem pairVec_zero (r s : F) : pairVec r s 0 = r := if_pos rfl

@[simp] theorem pairVec_one (r s : F) : pairVec r s 1 = s := by
  rw [pairVec, if_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem trDot_pairVec (r s a b : F) :
    trDot (pairVec r s) (pairVec a b) = Algebra.trace (ZMod 2) F (a * r)
      + Algebra.trace (ZMod 2) F (b * s) := by
  rw [trDot, show (∑ l : Fin 2, pairVec r s l * pairVec a b l) = r * a + s * b from by
      rw [Fin.sum_univ_two, pairVec_zero, pairVec_zero, pairVec_one, pairVec_one],
    map_add, mul_comm r a, mul_comm s b]

theorem sum_pairVec {M : Type*} [AddCommMonoid M] (f : (Fin 2 → F) → M) :
    ∑ v : Fin 2 → F, f v = ∑ r : F, ∑ s : F, f (pairVec r s) := by
  classical
  have hv : ∀ v : Fin 2 → F, v = pairVec (v 0) (v 1) := by
    intro v
    funext i
    fin_cases i <;> simp [pairVec]
  rw [show (∑ r : F, ∑ s : F, f (pairVec r s)) = ∑ p : F × F, f (pairVec p.1 p.2) from
    (Fintype.sum_prod_type (fun p : F × F => f (pairVec p.1 p.2))).symm]
  exact Fintype.sum_equiv (piFinTwoEquiv fun _ => F) _ _ fun v => congrArg f (hv v)

/-- A sum over pairs is a sum over `F_q^2`. -/
theorem sum_prod_eq_sum_pairVec {M : Type*} [AddCommMonoid M] (f : F → F → M) :
    ∑ p : F × F, f p.1 p.2 = ∑ v : Fin 2 → F, f (v 0) (v 1) := by
  classical
  rw [Fintype.sum_prod_type (fun p : F × F => f p.1 p.2),
    sum_pairVec (fun v : Fin 2 → F => f (v 0) (v 1))]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by
    rw [pairVec_zero, pairVec_one]

end MIPRE

end
