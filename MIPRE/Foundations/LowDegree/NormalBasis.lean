/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.LowDegree.SelfDual
import MIPRE.Foundations.LowDegree.SelfDualize
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Finite.Trace

/-!
# A self-dual normal basis exists in characteristic two and odd degree

This is the existence half of blueprint `lem:self-dual-basis`: over a finite field of
characteristic two, an extension of odd degree admits a basis that is simultaneously normal
(a Frobenius orbit) and self-dual for the trace form.

The argument is the short one. Fix the normal element `α` Mathlib's normal basis theorem
supplies and let `c ∈ F[G]`, `G = Gal(K/F)`, be its Gram element, with `c_g = tr(α · gα)`.
Writing `ofAlg a` for the element with normal-basis coordinates `a`, the Gram element
transforms as
`gramPair (ofAlg a) (ofAlg a) = a · τa · c`,
where `τ` is the involution induced by `g ↦ g⁻¹` (`gramPair_ofAlg`). Nondegeneracy of the
trace form makes `c` a unit (`isUnit_gram`), and `c` is `τ`-fixed, hence so is `c⁻¹`. Since
`|G| = [K : F]` is odd and the characteristic is two, squaring is bijective on `F[G]`
(`mul_self_bijective'`), so `exists_mul_involute_eq` of
`MIPRE.Foundations.LowDegree.SelfDualize` produces `a` with `a · τa = c⁻¹`. Then
`β = ofAlg a` has Gram element `1`, i.e. its Frobenius orbit is orthonormal.

What is *not* here is the `poly(k)` algorithm that produces such a basis; the blueprint's
`lem:self-dual-basis` still waits on that half.
-/

namespace MIPRE.LowDegree

open Finset

/-! ## Squaring on a group algebra, multiplicatively -/

section MulSelfDualize

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
variable {F : Type*} [Field F] [Fintype F]

omit [DecidableEq G] in
/-- In a finite abelian group of odd order, squaring is injective. -/
theorem mul_self_injective (hG : Odd (Fintype.card G)) :
    Function.Injective fun g : G => g * g := by
  intro a b hab
  simp only at hab
  have h2 : (a / b) * (a / b) = 1 := by
    have e : (a / b) * (a / b) = (a * a) / (b * b) := div_mul_div_comm a b a b
    rw [e, hab, div_self']
  have hord : orderOf (a / b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have hcard : orderOf (a / b) ∣ Fintype.card G := orderOf_dvd_card
  have hcop : Nat.Coprime 2 (Fintype.card G) := Nat.coprime_two_left.mpr hG
  have hdvd : orderOf (a / b) ∣ 1 := hcop ▸ Nat.dvd_gcd hord hcard
  exact div_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

omit [Fintype G] [DecidableEq G] [Fintype F] in
private theorem two_eq_zero' (hF : CharP F 2) : (2 : MonoidAlgebra F G) = 0 := by
  have h : ((2 : ℕ) : F) = 0 := by
    have := hF
    exact CharP.cast_eq_zero F 2
  rw [show (2 : MonoidAlgebra F G) = MonoidAlgebra.single 1 (2 : F) from rfl,
    show (2 : F) = ((2 : ℕ) : F) from by norm_num, h, MonoidAlgebra.single_zero]

omit [Fintype F] in
/-- The coefficient of a square, at a squared index. -/
theorem coeff_mul_self' (hF : CharP F 2) (hG : Odd (Fintype.card G))
    (z : MonoidAlgebra F G) (g : G) :
    (z * z).coeff (g * g) = z.coeff g * z.coeff g := by
  have h2 : (2 : F) = 0 := by
    have := hF
    have h := CharP.cast_eq_zero F 2
    rwa [show ((2 : ℕ) : F) = (2 : F) from by norm_num] at h
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [add_mul_self_char_two (two_eq_zero' (G := G) hF), MonoidAlgebra.coeff_add,
        Finsupp.add_apply, hx, hy, MonoidAlgebra.coeff_add, Finsupp.add_apply]
      rw [add_mul_self_char_two h2]
  | single m r =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single,
        MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : m = g
      · simp [h]
      · rw [if_neg h, if_neg (fun he => h (mul_self_injective hG he)), mul_zero]

/-- **Squaring is bijective on `F[G]`**, multiplicatively. -/
theorem mul_self_bijective' (hF : CharP F 2) (hG : Odd (Fintype.card G)) :
    Function.Bijective fun x : MonoidAlgebra F G => x * x := by
  have : Finite (MonoidAlgebra F G) :=
    Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  refine Finite.injective_iff_bijective.mp fun x y hxy => ?_
  have hz : (x - y) * (x - y) = 0 := by
    have e : (x - y) * (x - y) = x * x - y * y - 2 * (x * y) + 2 * (y * y) := by ring
    rw [e, hxy, sub_self, two_eq_zero' (G := G) hF, zero_mul, zero_mul, zero_sub, neg_zero,
      add_zero]
  refine sub_eq_zero.mp (MonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_))
  have h := coeff_mul_self' hF hG (x - y) g
  rw [hz] at h
  simpa using (mul_self_eq_zero.mp h.symm)

end MulSelfDualize

/-! ## The Gram element of a Frobenius orbit -/

section Existence

attribute [local instance] IsCyclic.commGroup

variable (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K] [Finite K]
  [FiniteDimensional F K] [IsGalois F K]

/-- The normal element Mathlib's normal basis theorem supplies. -/
noncomputable def normalElt : K := IsGalois.normalBasis F K 1

/-- The involution of the group algebra induced by `g ↦ g⁻¹`. -/
noncomputable def galStar :
    MonoidAlgebra F (K ≃ₐ[F] K) ≃+* MonoidAlgebra F (K ≃ₐ[F] K) :=
  (MonoidAlgebra.domCongr F F (MulEquiv.inv (K ≃ₐ[F] K))).toRingEquiv

/-- The Gram element of a pair: its coefficient at `g` is `tr(x · g y)`. For `x = y` the
Gram matrix of the Frobenius orbit of `x` is the circulant this determines. -/
noncomputable def gramPair (x y : K) : MonoidAlgebra F (K ≃ₐ[F] K) :=
  .ofCoeff (Finsupp.equivFunOnFinite.symm fun g => Algebra.trace F K (x * g y))

/-- The element of `K` with normal-basis coordinates `a`. -/
noncomputable def ofAlg (a : MonoidAlgebra F (K ≃ₐ[F] K)) : K :=
  (IsGalois.normalBasis F K).repr.symm a.coeff

variable {F K}

omit [Fintype F] [Finite K] [IsGalois F K] in
@[simp] theorem coeff_gramPair (x y : K) (g : K ≃ₐ[F] K) :
    (gramPair F K x y).coeff g = Algebra.trace F K (x * g y) := rfl

omit [Fintype F] [FiniteDimensional F K] [IsGalois F K] in
@[simp] theorem coeff_galStar (a : MonoidAlgebra F (K ≃ₐ[F] K)) (g : K ≃ₐ[F] K) :
    (galStar F K a).coeff g = a.coeff g⁻¹ := by
  simp [galStar]

omit [Fintype F] in
theorem normalBasis_eq (g : K ≃ₐ[F] K) :
    IsGalois.normalBasis F K g = g (normalElt F K) :=
  IsGalois.normalBasis_apply g

omit [Fintype F] [Finite K] in
/-- The trace is invariant under the Galois action. -/
theorem trace_algEquiv (σ : K ≃ₐ[F] K) (x : K) :
    Algebra.trace F K (σ x) = Algebra.trace F K x := by
  apply FaithfulSMul.algebraMap_injective F K
  rw [_root_.trace_eq_sum_automorphisms (K := F) (σ x),
    _root_.trace_eq_sum_automorphisms (K := F) x]
  exact Fintype.sum_equiv (Equiv.mulRight σ) _ _ fun ρ => rfl

omit [Fintype F] in
/-- The trace pairing of two members of one Frobenius orbit depends only on their ratio. -/
theorem trace_orbit (σ τ : K ≃ₐ[F] K) (x : K) :
    Algebra.trace F K (σ x * τ x) = Algebra.trace F K (x * (σ⁻¹ * τ) x) := by
  have h : σ (x * (σ⁻¹ * τ) x) = σ x * τ x := by
    rw [map_mul, ← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← h, trace_algEquiv]

omit [Fintype F] in
theorem ofAlg_eq (a : MonoidAlgebra F (K ≃ₐ[F] K)) :
    ofAlg F K a = ∑ g, a.coeff g • g (normalElt F K) := by
  rw [ofAlg, Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype]
  · exact Finset.sum_congr rfl fun g _ => by rw [normalBasis_eq]
  · intro i
    exact zero_smul _ _

omit [Fintype F] in
/-- **The Gram element transforms by `a ↦ a · τa · c`.** This is the identity the whole
self-dualization rests on: the Gram matrix of the orbit of `ofAlg a` is the circulant of
`a · τ a · c`, where `c` is the Gram element of the normal element itself. -/
theorem gramPair_ofAlg (a b : MonoidAlgebra F (K ≃ₐ[F] K)) :
    gramPair F K (ofAlg F K a) (ofAlg F K b)
      = a * galStar F K b * gramPair F K (normalElt F K) (normalElt F K) := by
  set c := gramPair F K (normalElt F K) (normalElt F K) with hc
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  have hL : (gramPair F K (ofAlg F K a) (ofAlg F K b)).coeff g
      = ∑ σ, ∑ ρ, a.coeff σ * b.coeff ρ * c.coeff (σ⁻¹ * (g * ρ)) := by
    rw [coeff_gramPair, ofAlg_eq, ofAlg_eq, map_sum, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [map_smul, smul_mul_smul_comm, smul_eq_mul, ← mul_assoc]
    congr 1
    rw [hc, coeff_gramPair, ← AlgEquiv.mul_apply, trace_orbit, mul_assoc σ⁻¹ g ρ]
  have hR : (a * galStar F K b * c).coeff g
      = ∑ σ, ∑ ρ, a.coeff σ * b.coeff ρ * c.coeff (σ⁻¹ * (g * ρ)) := by
    have hab : ∀ u : K ≃ₐ[F] K, (a * galStar F K b).coeff u
        = ∑ σ, a.coeff σ * b.coeff (u⁻¹ * σ) := by
      intro u
      rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [coeff_galStar]
      congr 2
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
    rw [Finset.sum_congr rfl fun u (_ : u ∈ Finset.univ) => by rw [hab u, Finset.sum_mul],
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    refine (Fintype.sum_equiv ((Equiv.inv (K ≃ₐ[F] K)).trans (Equiv.mulLeft σ)) _ _
      fun ρ => ?_).symm
    show a.coeff σ * b.coeff ρ * c.coeff (σ⁻¹ * (g * ρ))
      = a.coeff σ * b.coeff ((σ * ρ⁻¹)⁻¹ * σ) * c.coeff ((σ * ρ⁻¹)⁻¹ * g)
    have e1 : (σ * ρ⁻¹)⁻¹ * σ = ρ := by
      rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    have e2 : (σ * ρ⁻¹)⁻¹ * g = σ⁻¹ * (g * ρ) := by
      rw [mul_inv_rev, inv_inv]
      simp [mul_comm, mul_assoc]
    rw [e1, e2]
  rw [hL, hR]

/-! ## The Gram element is a unit -/

omit [Fintype F] [FiniteDimensional F K] [IsGalois F K] in
theorem galStar_galStar (a : MonoidAlgebra F (K ≃ₐ[F] K)) :
    galStar F K (galStar F K a) = a := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  simp

omit [Fintype F] in
/-- The Gram element of an orbit is fixed by the involution: the Gram matrix is symmetric. -/
theorem galStar_gramPair_self (x : K) :
    galStar F K (gramPair F K x x) = gramPair F K x x := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  rw [coeff_galStar, coeff_gramPair, coeff_gramPair, ← trace_algEquiv g (x * g⁻¹ x), map_mul,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, mul_comm]

omit [Fintype F] [Finite K] in
theorem ofAlg_bijective : Function.Bijective (ofAlg F K) := by
  constructor
  · intro a b h
    exact MonoidAlgebra.coeff_injective ((IsGalois.normalBasis F K).repr.symm.injective h)
  · intro x
    exact ⟨.ofCoeff ((IsGalois.normalBasis F K).repr x), by simp [ofAlg]⟩

/-- **The Gram element of a normal element is a unit**: the Gram matrix of a basis under the
nondegenerate trace form is invertible. -/
theorem isUnit_gram : IsUnit (gramPair F K (normalElt F K) (normalElt F K)) := by
  have hfs : Finite ((K ≃ₐ[F] K) →₀ F) :=
    Finite.of_injective (fun f => (f : (K ≃ₐ[F] K) → F)) DFunLike.coe_injective
  have hfin : Finite (MonoidAlgebra F (K ≃ₐ[F] K)) :=
    Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  have hinj : Function.Injective
      fun z => gramPair F K (normalElt F K) (normalElt F K) * z := by
    intro z w h
    simp only at h
    have hz : gramPair F K (normalElt F K) (normalElt F K) * (z - w) = 0 := by
      rw [mul_sub, h, sub_self]
    refine sub_eq_zero.mp ?_
    have hall : ∀ x : K,
        Algebra.trace F K (ofAlg F K (galStar F K (z - w)) * x) = 0 := by
      intro x
      obtain ⟨a, rfl⟩ := (ofAlg_bijective (F := F) (K := K)).surjective x
      have key := gramPair_ofAlg a (galStar F K (z - w))
      rw [galStar_galStar] at key
      have h1 := congrArg (fun u : MonoidAlgebra F (K ≃ₐ[F] K) => u.coeff 1) key
      simp only [coeff_gramPair, AlgEquiv.one_apply] at h1
      rw [mul_comm (ofAlg F K (galStar F K (z - w))), h1, mul_assoc,
        mul_comm (z - w) (gramPair F K (normalElt F K) (normalElt F K)), hz, mul_zero]
      simp
    have hy0 : ofAlg F K (galStar F K (z - w)) = 0 :=
      (_root_.traceForm_nondegenerate F K).1 _ fun x => by
        rw [Algebra.traceForm_apply]
        exact hall x
    have hz0 : galStar F K (z - w) = 0 :=
      (ofAlg_bijective (F := F) (K := K)).injective
        (by rw [hy0, show ofAlg F K 0 = 0 from by simp [ofAlg]])
    have h2 := congrArg (galStar F K) hz0
    rwa [galStar_galStar, map_zero] at h2
  obtain ⟨z, hz⟩ := (Finite.injective_iff_bijective.mp hinj).surjective 1
  exact ⟨⟨_, z, hz, by rw [mul_comm]; exact hz⟩, rfl⟩

/-! ## A self-dual normal element, and the basis -/

variable (F K)

/-- **A self-dual normal element.** In characteristic two and odd degree there is a `β` whose
Frobenius orbit is orthonormal for the trace form. This is `exists_mul_involute_eq` applied to
the inverse of the Gram element, which is fixed by the involution because the Gram element is
and inverses are unique. -/
theorem exists_gramPair_eq_one (hF : CharP F 2) (hodd : Odd (Module.finrank F K)) :
    ∃ β : K, gramPair F K β β = 1 := by
  classical
  have hcard : Odd (Fintype.card (K ≃ₐ[F] K)) := by
    convert hodd using 2
    exact Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank F K)
  obtain ⟨cu, hcu⟩ := isUnit_gram (F := F) (K := K)
  have hgc : galStar F K (gramPair F K (normalElt F K) (normalElt F K))
      = gramPair F K (normalElt F K) (normalElt F K) := galStar_gramPair_self _
  have hinv : (↑cu⁻¹ : MonoidAlgebra F (K ≃ₐ[F] K)) *
      gramPair F K (normalElt F K) (normalElt F K) = 1 := by
    rw [← hcu]
    exact cu.inv_mul
  have h1 : galStar F K (↑cu⁻¹ : MonoidAlgebra F (K ≃ₐ[F] K)) *
      gramPair F K (normalElt F K) (normalElt F K) = 1 := by
    conv_lhs => rw [← hgc]
    rw [← map_mul, hinv, map_one]
  have hstar : galStar F K (↑cu⁻¹ : MonoidAlgebra F (K ≃ₐ[F] K)) = ↑cu⁻¹ := by
    calc galStar F K (↑cu⁻¹ : MonoidAlgebra F (K ≃ₐ[F] K))
        = galStar F K (↑cu⁻¹) *
            (gramPair F K (normalElt F K) (normalElt F K) * ↑cu⁻¹) := by
          rw [mul_comm (gramPair F K (normalElt F K) (normalElt F K)), hinv, mul_one]
      _ = galStar F K (↑cu⁻¹) * gramPair F K (normalElt F K) (normalElt F K) * ↑cu⁻¹ := by
          ring
      _ = ↑cu⁻¹ := by rw [h1, one_mul]
  obtain ⟨a, ha⟩ := exists_mul_involute_eq (galStar F K)
    (fun x y h => (mul_self_bijective' hF hcard).injective h)
    (fun y => (mul_self_bijective' hF hcard).surjective y) hstar
  exact ⟨ofAlg F K a, by rw [gramPair_ofAlg, ha, hinv]⟩

variable {F K}

private theorem trace_frobOrbit_eq (β : K) (i j : ℕ) :
    Algebra.trace F K (β ^ (Fintype.card F ^ i) * β ^ (Fintype.card F ^ j))
      = (gramPair F K β β).coeff
          (((FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ i)⁻¹ *
            (FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ j) := by
  have hpow : ∀ n : ℕ, (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ n) β
      = β ^ (Fintype.card F ^ n) := fun n => by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [← hpow i, ← hpow j, trace_orbit, ← coeff_gramPair]

/-- The Frobenius orbit of a self-dual normal element is orthonormal: the diagonal. -/
theorem trace_frobOrbit_self {β : K} (hβ : gramPair F K β β = 1) {i j : ℕ}
    (h : (FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ i
      = (FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ j) :
    Algebra.trace F K (β ^ (Fintype.card F ^ i) * β ^ (Fintype.card F ^ j)) = 1 := by
  rw [trace_frobOrbit_eq, hβ,
    show (1 : MonoidAlgebra F (K ≃ₐ[F] K)) = MonoidAlgebra.single 1 1 from rfl,
    MonoidAlgebra.coeff_single, h, inv_mul_cancel, Finsupp.single_eq_same]

/-- The Frobenius orbit of a self-dual normal element is orthonormal: off the diagonal. -/
theorem trace_frobOrbit_ne {β : K} (hβ : gramPair F K β β = 1) {i j : ℕ}
    (h : (FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ i
      ≠ (FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ j) :
    Algebra.trace F K (β ^ (Fintype.card F ^ i) * β ^ (Fintype.card F ^ j)) = 0 := by
  have hne : (1 : K ≃ₐ[F] K) ≠ ((FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ i)⁻¹ *
      (FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ j := by
    intro he
    refine h ?_
    have h2 := congrArg (fun u => (FiniteField.frobeniusAlgEquivOfAlgebraic F K) ^ i * u) he
    simpa [mul_inv_cancel_left] using h2
  rw [trace_frobOrbit_eq, hβ,
    show (1 : MonoidAlgebra F (K ≃ₐ[F] K)) = MonoidAlgebra.single 1 1 from rfl,
    MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne' hne]

variable (F K)

/-- **A self-dual normal basis exists** when the characteristic is two and the degree is odd
(the existence half of blueprint `lem:self-dual-basis`). -/
theorem exists_isSelfDualBasis_isNormalBasis (hF : CharP F 2)
    (hodd : Odd (Module.finrank F K)) :
    ∃ b : Module.Basis (Fin (Module.finrank F K)) F K, IsSelfDualBasis b ∧ IsNormalBasis b := by
  classical
  obtain ⟨β, hβ⟩ := exists_gramPair_eq_one F K hF hodd
  have horth : ∀ i j : Fin (Module.finrank F K),
      Algebra.trace F K (β ^ (Fintype.card F ^ (i : ℕ)) * β ^ (Fintype.card F ^ (j : ℕ)))
        = if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · rw [if_pos h]
      exact trace_frobOrbit_self hβ (by rw [h])
    · rw [if_neg h]
      exact trace_frobOrbit_ne hβ fun he =>
        h ((FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).injective he)
  have hli : LinearIndependent F
      (fun i : Fin (Module.finrank F K) => β ^ (Fintype.card F ^ (i : ℕ))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h2 := congrArg (fun x => Algebra.trace F K (x * β ^ (Fintype.card F ^ (j : ℕ)))) hg
    simp only [zero_mul, map_zero, Finset.sum_mul, map_sum] at h2
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [smul_mul_assoc, map_smul, horth i j, smul_eq_mul]] at h2
    simpa using h2
  have : Nonempty (Fin (Module.finrank F K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), ?_, ?_⟩
  · intro i j
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact horth i j
  · exact ⟨β, fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩

/-- **A self-dual normal basis of `𝔽_{2^k}` over `𝔽₂` exists for every odd `k`** --- the
existence half of blueprint `lem:self-dual-basis`, on Mathlib's normal basis theorem and the
self-dualization of `lem:group-algebra-selfdualization`. -/
theorem exists_selfDualNormalBasis_two (k : ℕ) (hk : Odd k) :
    ∃ b : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k),
      IsSelfDualBasis b ∧ IsNormalBasis b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hfr : Module.finrank (ZMod 2) (GaloisField 2 k) = k := GaloisField.finrank 2 hk0
  obtain ⟨b, hsd, hnb⟩ := exists_isSelfDualBasis_isNormalBasis (ZMod 2) (GaloisField 2 k)
    (ZMod.charP 2) (by rw [hfr]; exact hk)
  refine ⟨b.reindex (finCongr hfr), fun i j => ?_, ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hsd]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg fun he => h ((finCongr hfr).symm.injective he)]
  · obtain ⟨α, hα⟩ := hnb
    refine ⟨α, fun i => ?_⟩
    rw [Module.Basis.reindex_apply, hα]
    simp

end Existence

end MIPRE.LowDegree
