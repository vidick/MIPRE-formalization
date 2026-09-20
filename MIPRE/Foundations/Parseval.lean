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
theorem sum_norm_fourierVecRaw_sq (T : (n → F) → (N → ℂ)) :
    ∑ e : n → F, ‖evec (fourierVecRaw T e)‖ ^ 2
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

theorem sum_norm_fourierVec_sq (T : (n → F) → (N → ℂ)) :
    ∑ e : n → F, ‖evec (fourierVec T e)‖ ^ 2
      = (Fintype.card (n → F) : ℝ)⁻¹ * ∑ a : n → F, ‖evec (T a)‖ ^ 2 := by
  classical
  have hNR : (Fintype.card (n → F) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos (α := n → F)).ne'
  have hraw := sum_norm_fourierVecRaw_sq T
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

/-! ## Parseval over one copy of the field, and over two

The combining stage coarse-grains an `F_q x F_q`-valued measurement by the linear form
`(a, b) |-> alpha a + beta b`, and the fibres have `q` elements -- so a per-fibre triangle
inequality would cost a factor `q`. Parseval is what avoids that, and it is needed in three
shapes: over `F_q` (to turn the sum over fibres into an average over one probe), over
`F_q x F_q` (to turn that average back into a sum over outcome pairs), and the cancellation of
the zero probe.
-/

/-- The unnormalized character transform of a family of vectors indexed by `F_q` itself. -/
def trVecRaw (T : F → (N → ℂ)) (r : F) : N → ℂ :=
  ∑ c : F, sgn (Algebra.trace (ZMod 2) F (c * r)) • T c

theorem sum_dotProduct_trVecRaw (T : F → (N → ℂ)) :
    ∑ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r
      = (Fintype.card F : ℂ) * ∑ c : F, star (T c) ⬝ᵥ T c := by
  classical
  have hterm : ∀ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r
      = ∑ a : F, ∑ b : F,
          sgn (Algebra.trace (ZMod 2) F ((a + b) * r)) * (star (T a) ⬝ᵥ T b) := by
    intro r
    rw [trVecRaw, star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_smul, star_sgn, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      add_mul, map_add, sgn_add, mul_assoc]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => hterm r]
  rw [show (∑ r : F, ∑ a : F, ∑ b : F,
        sgn (Algebra.trace (ZMod 2) F ((a + b) * r)) * (star (T a) ⬝ᵥ T b))
      = ∑ a : F, ∑ b : F,
          (∑ r : F, sgn (Algebra.trace (ZMod 2) F ((a + b) * r))) * (star (T a) ⬝ᵥ T b) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]]
  have hchar : ∀ a b : F, a ≠ b →
      (∑ r : F, sgn (Algebra.trace (ZMod 2) F ((a + b) * r))) = 0 := by
    intro a b hab
    have hne : a + b ≠ 0 := by
      intro h
      exact hab (by
        have h2 : b + b = 0 := by
          rw [← two_mul, MIPRE.Weyl.two_eq_zero, zero_mul]
        calc a = a + (b + b) := by rw [h2, add_zero]
          _ = (a + b) + b := by ring
          _ = b := by rw [h, zero_add])
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [mul_comm (a + b) r]]
    exact MIPRE.Weyl.sum_sgn_trMul hne
  have hinner : ∀ a : F, (∑ b : F, (∑ r : F, sgn (Algebra.trace (ZMod 2) F ((a + b) * r)))
        * (star (T a) ⬝ᵥ T b))
      = (Fintype.card F : ℂ) * (star (T a) ⬝ᵥ T a) := by
    intro a
    refine (Finset.sum_eq_single_of_mem a (mem_univ a) fun b _ hb => ?_).trans ?_
    · rw [hchar a b (Ne.symm hb), zero_mul]
    · congr 1
      have h2 : a + a = 0 := by rw [← two_mul, MIPRE.Weyl.two_eq_zero, zero_mul]
      rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by
          rw [h2, zero_mul, map_zero, sgn_zero],
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hinner a, ← Finset.mul_sum]

/-- **Parseval over one copy of the field.** -/
theorem sum_norm_trVecRaw_sq (T : F → (N → ℂ)) :
    ∑ r : F, ‖evec (trVecRaw T r)‖ ^ 2 = (Fintype.card F : ℝ) * ∑ c : F, ‖evec (T c)‖ ^ 2 := by
  have h1 : (∑ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r)
      = ((∑ r : F, ‖evec (trVecRaw T r)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun r _ => dotProduct_star_self _
  have h2 : (∑ c : F, star (T c) ⬝ᵥ T c) = ((∑ c : F, ‖evec (T c)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun c _ => dotProduct_star_self _
  have h3 := sum_dotProduct_trVecRaw T
  rw [h1, h2] at h3
  exact_mod_cast h3

/-- **Parseval over two copies of the field**, in the product-indexed shape the combining stage
uses. -/
theorem sum_norm_char_two_sq (T : F × F → (N → ℂ)) :
    ∑ q : F × F, ‖evec (∑ p : F × F,
        sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
          + Algebra.trace (ZMod 2) F (q.2 * p.2)) • T p)‖ ^ 2
      = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)) * ∑ p : F × F, ‖evec (T p)‖ ^ 2 := by
  classical
  have hcard : (Fintype.card (Fin 2 → F) : ℝ) = (Fintype.card F : ℝ) * (Fintype.card F : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hraw := sum_norm_fourierVecRaw_sq (T := fun v : Fin 2 → F => T (v 0, v 1))
  rw [hcard] at hraw
  have hrhs : (∑ p : F × F, ‖evec (T p)‖ ^ 2) = ∑ a : Fin 2 → F, ‖evec (T (a 0, a 1))‖ ^ 2 :=
    sum_prod_eq_sum_pairVec fun a b => ‖evec (T (a, b))‖ ^ 2
  have hlhs : (∑ q : F × F, ‖evec (∑ p : F × F,
        sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
          + Algebra.trace (ZMod 2) F (q.2 * p.2)) • T p)‖ ^ 2)
      = ∑ e : Fin 2 → F, ‖evec (fourierVecRaw (fun v : Fin 2 → F => T (v 0, v 1)) e)‖ ^ 2 := by
    refine (sum_prod_eq_sum_pairVec fun a b => ‖evec (∑ p : F × F,
        sgn (Algebra.trace (ZMod 2) F (a * p.1)
          + Algebra.trace (ZMod 2) F (b * p.2)) • T p)‖ ^ 2).trans ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine congrArg (fun w : N → ℂ => ‖evec w‖ ^ 2) ?_
    show (∑ p : F × F, sgn (Algebra.trace (ZMod 2) F (e 0 * p.1)
        + Algebra.trace (ZMod 2) F (e 1 * p.2)) • T p)
      = ∑ a : Fin 2 → F, sgn (trDot a e) • T (a 0, a 1)
    refine (sum_prod_eq_sum_pairVec fun a b =>
      sgn (Algebra.trace (ZMod 2) F (e 0 * a)
        + Algebra.trace (ZMod 2) F (e 1 * b)) • T (a, b)).trans ?_
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    rw [show trDot v e = Algebra.trace (ZMod 2) F (e 0 * v 0)
        + Algebra.trace (ZMod 2) F (e 1 * v 1) from by
      rw [show v = pairVec (v 0) (v 1) from by funext i; fin_cases i <;> simp [pairVec],
        show e = pairVec (e 0) (e 1) from by funext i; fin_cases i <;> simp [pairVec],
        trDot_pairVec, pairVec_zero, pairVec_one, pairVec_zero, pairVec_one]]
  rw [hlhs, hrhs, hraw]

/-! ## Coarse-graining by a linear form -/

/-- **Parseval for a coarse-graining by a linear form.** A family of vectors indexed by
`F_q x F_q` that *sums to zero* has, on average over `(alpha, beta)` uniform, fibre sums under
`(a, b) |-> alpha a + beta b` whose total squared norm is `1 - 1/q` times the family's own. In
particular it is at most the family's: the fibres have `q` elements, and a per-fibre triangle
inequality would cost exactly that factor, which this avoids.

The zero-sum hypothesis is what kills the `r = 0` character; without it the statement is false
(take `U` supported on one point). -/
theorem sum_avg_norm_fibre_sq (U : F × F → (N → ℂ)) (hU : ∑ p : F × F, U p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, ‖evec (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p)‖ ^ 2
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖evec (U p)‖ ^ 2 := by
  classical
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set G : F × F → (N → ℂ) := fun st => ∑ p : F × F,
    sgn (Algebra.trace (ZMod 2) F (st.1 * p.1)
      + Algebra.trace (ZMod 2) F (st.2 * p.2)) • U p with hG
  -- the family's own total, which every term reduces to
  set S : ℝ := ∑ p : F × F, ‖evec (U p)‖ ^ 2 with hS
  -- **step 1**: the fibre sums are a character average, for each fixed `(alpha, beta)`
  have hstep1 : ∀ ab : F × F,
      (∑ c : F, ‖evec (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p)‖ ^ 2)
        = (Fintype.card F : ℝ)⁻¹ * ∑ r : F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2 := by
    intro ab
    have hraw : ∀ r : F,
        trVecRaw (fun c : F => ∑ p ∈ univ.filter fun p : F × F =>
            ab.1 * p.1 + ab.2 * p.2 = c, U p) r
          = G (r * ab.1, r * ab.2) := by
      intro r
      rw [trVecRaw, hG]
      refine (Finset.sum_congr rfl fun c (_ : c ∈ univ) => ?_).trans
        (Finset.sum_fiberwise (univ : Finset (F × F))
          (fun p : F × F => ab.1 * p.1 + ab.2 * p.2)
          (fun p : F × F => sgn (Algebra.trace (ZMod 2) F ((r * ab.1) * p.1)
            + Algebra.trace (ZMod 2) F ((r * ab.2) * p.2)) • U p))
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Finset.mem_filter.mp hp).2,
        show Algebra.trace (ZMod 2) F ((r * ab.1) * p.1)
            + Algebra.trace (ZMod 2) F ((r * ab.2) * p.2)
          = Algebra.trace (ZMod 2) F ((ab.1 * p.1 + ab.2 * p.2) * r) from by
          rw [← map_add]
          congr 1
          ring]
    have hT := sum_norm_trVecRaw_sq
      (T := fun c : F => ∑ p ∈ univ.filter fun p : F × F =>
        ab.1 * p.1 + ab.2 * p.2 = c, U p)
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [hraw r]] at hT
    rw [hT]
    field_simp
  rw [Finset.sum_congr rfl fun ab (_ : ab ∈ univ) => by rw [hstep1 ab]]
  -- **step 2**: swap the two averages
  have hswap : (∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ((Fintype.card F : ℝ)⁻¹ * ∑ r : F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2))
      = ∑ r : F, (Fintype.card F : ℝ)⁻¹ *
          (((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
            ∑ ab : F × F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun ab _ => by ring
  rw [hswap]
  -- **step 3**: each nonzero character contributes the family's total; the zero one nothing
  have hterm : ∀ r : F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
      (∑ ab : F × F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2) = if r = 0 then 0 else S := by
    intro r
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl]
      have hzero : ∀ ab : F × F, G ((0 : F) * ab.1, (0 : F) * ab.2) = 0 := by
        intro ab
        rw [hG]
        show (∑ p : F × F, sgn (Algebra.trace (ZMod 2) F ((0 : F) * ab.1 * p.1)
          + Algebra.trace (ZMod 2) F ((0 : F) * ab.2 * p.2)) • U p) = 0
        rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => by
          rw [zero_mul, zero_mul, zero_mul, zero_mul, map_zero, add_zero, sgn_zero, one_smul]]
        exact hU
      rw [Finset.sum_congr rfl fun ab (_ : ab ∈ univ) => by rw [hzero ab], evec_zero]
      simp
    · rw [if_neg hr]
      have hbij : (∑ ab : F × F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2)
          = ∑ st : F × F, ‖evec (G (st.1, st.2))‖ ^ 2 := by
        refine Fintype.sum_equiv
          ((Equiv.mulLeft₀ r hr).prodCongr (Equiv.mulLeft₀ r hr)) _ _ fun ab => ?_
        rfl
      rw [hbij, hG]
      rw [show (∑ st : F × F, ‖evec ((fun st : F × F => ∑ p : F × F,
            sgn (Algebra.trace (ZMod 2) F (st.1 * p.1)
              + Algebra.trace (ZMod 2) F (st.2 * p.2)) • U p) (st.1, st.2))‖ ^ 2)
          = ∑ q : F × F, ‖evec (∑ p : F × F,
              sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
                + Algebra.trace (ZMod 2) F (q.2 * p.2)) • U p)‖ ^ 2 from rfl,
        sum_norm_char_two_sq, hS]
      field_simp
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [hterm r], ← Finset.mul_sum]
  have h1 : (∑ _r : F, if _r = 0 then (0 : ℝ) else S) = (Fintype.card F : ℝ) * S - S := by
    have h2 : ∀ r : F, (if r = 0 then (0 : ℝ) else S) = S - (if r = 0 then S else 0) := by
      intro r
      by_cases h : r = 0 <;> simp [h]
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => h2 r, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
  rw [h1]
  field_simp

end MIPRE

end
