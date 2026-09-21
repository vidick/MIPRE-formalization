/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryFiniteFieldDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod

/-!
# The characteristic-two Artin–Schreier tower step

The polynomial `X² + X + a` has no root exactly when its quadratic quotient is
an extension field. In that extension, multiplication of `a` by the canonical
root supplies the next no-root parameter. These are algebraic correctness
lemmas for the explicit binary tower constructor; they do not choose a root
by searching through the field.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryArtinSchreier

open Polynomial Module

variable {K : Type*} [Field K]

/-- The monic quadratic used by the characteristic-two tower. -/
def quadratic (a : K) : K[X] := X ^ 2 + X + C a

@[simp] theorem quadratic_natDegree (a : K) : (quadratic a).natDegree = 2 := by
  simpa [quadratic] using (natDegree_quadratic (a := (1 : K)) (b := 1) (c := a) one_ne_zero)

theorem quadratic_monic (a : K) : (quadratic a).Monic := by
  simpa [quadratic, Monic] using
    (leadingCoeff_quadratic (a := (1 : K)) (b := 1) (c := a) one_ne_zero)

@[simp] theorem quadratic_eval (a x : K) : (quadratic a).eval x = x ^ 2 + x + a := by
  simp [quadratic]

/-- Degree two reduces irreducibility to the explicit no-root property. -/
theorem quadratic_irreducible_iff (a : K) :
    Irreducible (quadratic a) ↔ ∀ x : K, x ^ 2 + x + a ≠ 0 := by
  constructor
  · intro h x
    simpa only [IsRoot, quadratic_eval] using
      (h.not_isRoot_of_natDegree_ne_one (by simp) (x := x))
  · intro h
    apply irreducible_of_degree_le_three_of_not_isRoot (by simp)
    simpa only [IsRoot, quadratic_eval] using h

/-- The specified basis of every monic quadratic quotient, indexed by `Fin 2`. -/
def quadraticBasis (a : K) : Basis (Fin 2) K (AdjoinRoot (quadratic a)) :=
  (AdjoinRoot.powerBasis' (quadratic_monic a)).basis.reindex
    (finCongr (quadratic_natDegree a))

@[simp] theorem quadraticBasis_apply (a : K) (i : Fin 2) :
    quadraticBasis a i = AdjoinRoot.root (quadratic a) ^ (i : ℕ) := by
  rw [quadraticBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- Each element has its two coefficients in the specified quadratic power basis. -/
theorem exists_coordinates (a : K) (x : AdjoinRoot (quadratic a)) :
    ∃ u v : K, x = algebraMap K _ u + algebraMap K _ v * AdjoinRoot.root (quadratic a) := by
  refine ⟨(quadraticBasis a).repr x 0, (quadraticBasis a).repr x 1, ?_⟩
  have h := (quadraticBasis a).sum_repr x
  simpa only [Fin.sum_univ_two, quadraticBasis_apply, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, Algebra.smul_def, mul_one] using h.symm

/-- The coefficient of the root in a zero linear combination is zero. -/
theorem linear_coeff_eq_zero (a u v : K)
    (h : algebraMap K (AdjoinRoot (quadratic a)) u +
      algebraMap K _ v * AdjoinRoot.root (quadratic a) = 0) : v = 0 := by
  have h' : u • quadraticBasis a 0 + v • quadraticBasis a 1 = 0 := by
    simpa only [quadraticBasis_apply, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      Algebra.smul_def, mul_one] using h
  have hc := congrArg (fun x => (quadraticBasis a).repr x 1) h'
  simpa only [map_add, map_smul, Basis.repr_self, map_zero, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Fin.zero_ne_one,
    if_false, if_true, mul_zero, zero_add, mul_one, Finsupp.zero_apply] using hc

/-- The root of the quadratic satisfies its defining Artin–Schreier equation. -/
theorem root_relation (a : K) :
    AdjoinRoot.root (quadratic a) ^ 2 + AdjoinRoot.root (quadratic a) +
      algebraMap K (AdjoinRoot (quadratic a)) a = 0 := by
  have h := AdjoinRoot.eval₂_root (quadratic a)
  change (X ^ 2 + X + C a : K[X]).eval₂ _ _ = 0 at h
  rw [eval₂_add, eval₂_add, eval₂_pow, eval₂_X, eval₂_C] at h
  exact h

variable [CharP K 2]

/-- One no-root quadratic gives the next one over its explicitly presented extension. -/
theorem next_quadratic_irreducible (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    Irreducible (quadratic
      (algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a))) := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  apply (quadratic_irreducible_iff _).2
  intro x hx
  obtain ⟨u, v, rfl⟩ := exists_coordinates a x
  have hr := root_relation a
  have hz :
      algebraMap K (AdjoinRoot (quadratic a)) (u ^ 2 + u + v ^ 2 * a) +
        algebraMap K _ (v ^ 2 + v + a) * AdjoinRoot.root (quadratic a) = 0 := by
    simp only [map_add, map_mul, map_pow]
    linear_combination (norm := skip) hx - (algebraMap K (AdjoinRoot (quadratic a)) v) ^ 2 * hr
    ring_nf
    simp [CharTwo.two_eq_zero]
  exact (quadratic_irreducible_iff a).1 ha v (linear_coeff_eq_zero a _ _ hz)

/-- The multiplicative next parameter is the uniform cubic expression in the new root. -/
theorem next_parameter_eq_cubic (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a) =
      AdjoinRoot.root (quadratic a) ^ 3 + AdjoinRoot.root (quadratic a) ^ 2 := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  rw [← CharTwo.add_eq_zero.mp (root_relation a)]
  ring

/-- The source's cubic expression therefore preserves the no-root invariant. -/
theorem cubic_quadratic_irreducible (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    Irreducible (quadratic
      (AdjoinRoot.root (quadratic a) ^ 3 + AdjoinRoot.root (quadratic a) ^ 2)) := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  rw [← next_parameter_eq_cubic a ha]
  exact next_quadratic_irreducible a ha

/-- The initial binary quadratic has no root. -/
theorem binary_initial_irreducible : Irreducible (quadratic (1 : ZMod 2)) := by
  apply (quadratic_irreducible_iff _).2
  decide

omit [CharP K 2] in
/-- The quadratic root cannot already lie in the original field. -/
theorem root_not_mem_range (a : K) (ha : Irreducible (quadratic a)) :
    AdjoinRoot.root (quadratic a) ∉ (algebraMap K (AdjoinRoot (quadratic a))).range := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  rintro ⟨x, hx⟩
  have hr := root_relation a
  rw [← hx, ← map_pow, ← map_add, ← map_add] at hr
  have hz : x ^ 2 + x + a = 0 := (algebraMap K _).injective (hr.trans (map_zero _).symm)
  exact (quadratic_irreducible_iff a).1 ha x hz

/-- A binary annihilating polynomial of the old dimension gives the next
irreducible polynomial by substitution of `X² + X`. The hypothesis on `g`
is supplied by the explicit Frobenius orbit product, after coefficient descent. -/
theorem comp_quadratic_irreducible [Finite K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (t : ℕ)
    (hK : Module.finrank (ZMod 2) K = 2 ^ t)
    (a : K) (ha : Irreducible (quadratic a))
    (g : (ZMod 2)[X]) (hg : g.Monic) (hd : g.natDegree = 2 ^ t)
    (hz : aeval a g = 0) :
    Irreducible (g.comp (quadratic (0 : ZMod 2))) := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  let : Module.Finite K (AdjoinRoot (quadratic a)) := (quadratic_monic a).finite_adjoinRoot
  let : Module.Finite (ZMod 2) (AdjoinRoot (quadratic a)) :=
    Module.Finite.trans K (AdjoinRoot (quadratic a))
  let : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = 2 ^ (2 ^ t) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hK]
  have hdim : Module.finrank K (AdjoinRoot (quadratic a)) = 2 := by
    rw [(AdjoinRoot.powerBasis' (quadratic_monic a)).finrank]
    exact quadratic_natDegree a
  have htotal : Module.finrank (ZMod 2) (AdjoinRoot (quadratic a)) = 2 ^ (t + 1) := by
    rw [← Module.finrank_mul_finrank (ZMod 2) K (AdjoinRoot (quadratic a)), hK, hdim,
      pow_succ]
  have hdeg := BinaryFiniteField.minpoly_natDegree_of_not_mem_range t hcard htotal
    (AdjoinRoot.root (quadratic a)) (root_not_mem_range a ha)
  have hi : IsIntegral (ZMod 2) (AdjoinRoot.root (quadratic a)) :=
    IsIntegral.of_finite (ZMod 2) _
  have hp : aeval (AdjoinRoot.root (quadratic a)) (g.comp (quadratic (0 : ZMod 2))) = 0 := by
    rw [aeval_comp]
    have hroot : aeval (AdjoinRoot.root (quadratic a)) (quadratic (0 : ZMod 2)) =
        algebraMap K (AdjoinRoot (quadratic a)) a := by
      change aeval (AdjoinRoot.root (quadratic a)) (X ^ 2 + X + C (0 : ZMod 2)) = _
      rw [map_add, map_add, map_pow, aeval_X, aeval_C, map_zero, add_zero]
      exact CharTwo.add_eq_zero.mp (root_relation a)
    rw [hroot]
    change aeval ((IsScalarTower.toAlgHom (ZMod 2) K (AdjoinRoot (quadratic a))) a) g = 0
    rw [aeval_algHom_apply, hz, map_zero]
  have heq : g.comp (quadratic (0 : ZMod 2)) =
      minpoly (ZMod 2) (AdjoinRoot.root (quadratic a)) := by
    apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi)
      (hg.comp (quadratic_monic (0 : ZMod 2)) (by simp)) ((minpoly.dvd_iff).2 hp)
    rw [natDegree_comp, hd, quadratic_natDegree, hdeg, pow_succ]
  rw [heq]
  exact minpoly.irreducible hi

/-- Flattening the quadratic extension preserves the cubic no-root invariant.
Only the canonical embedding of the flat quotient is required; no search for
an isomorphism or a field element is part of this argument. -/
theorem comp_quadratic_cubic_irreducible [Finite K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (t : ℕ)
    (hK : Module.finrank (ZMod 2) K = 2 ^ t)
    (a : K) (ha : Irreducible (quadratic a))
    (g : (ZMod 2)[X]) (hg : g.Monic) (hd : g.natDegree = 2 ^ t)
    (hz : aeval a g = 0) :
    let : Fact (Irreducible (g.comp (quadratic (0 : ZMod 2)))) :=
      ⟨comp_quadratic_irreducible t hK a ha g hg hd hz⟩
    Irreducible (quadratic
      (AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 3 +
        AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 2)) := by
  let : Fact (Irreducible (g.comp (quadratic (0 : ZMod 2)))) :=
    ⟨comp_quadratic_irreducible t hK a ha g hg hd hz⟩
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  have hp : aeval (AdjoinRoot.root (quadratic a)) (g.comp (quadratic (0 : ZMod 2))) = 0 := by
    rw [aeval_comp]
    have hroot : aeval (AdjoinRoot.root (quadratic a)) (quadratic (0 : ZMod 2)) =
        algebraMap K (AdjoinRoot (quadratic a)) a := by
      change aeval (AdjoinRoot.root (quadratic a)) (X ^ 2 + X + C (0 : ZMod 2)) = _
      rw [map_add, map_add, map_pow, aeval_X, aeval_C, map_zero, add_zero]
      exact CharTwo.add_eq_zero.mp (root_relation a)
    rw [hroot]
    change aeval ((IsScalarTower.toAlgHom (ZMod 2) K (AdjoinRoot (quadratic a))) a) g = 0
    rw [aeval_algHom_apply, hz, map_zero]
  let φ := AdjoinRoot.liftAlgHom (g.comp (quadratic (0 : ZMod 2)))
    (Algebra.ofId (ZMod 2) (AdjoinRoot (quadratic a))) (AdjoinRoot.root (quadratic a)) hp
  have hφ : φ (AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2)))) =
      AdjoinRoot.root (quadratic a) := AdjoinRoot.liftAlgHom_root _ _ _ _
  apply (quadratic_irreducible_iff _).2
  intro x hx
  have hx' := congrArg φ hx
  simp only [map_add, map_pow, map_zero, hφ] at hx'
  exact (quadratic_irreducible_iff _).1 (cubic_quadratic_irreducible a ha) (φ x) hx'

/-- Transport the canonical-root cubic invariant across equality of binary moduli. -/
theorem cubic_irreducible_congr {f g : (ZMod 2)[X]} (hfg : f = g)
    (hf : Irreducible f) (hg : Irreducible g)
    (hc : let : Fact (Irreducible g) := ⟨hg⟩
      Irreducible (quadratic (AdjoinRoot.root g ^ 3 + AdjoinRoot.root g ^ 2))) :
    let : Fact (Irreducible f) := ⟨hf⟩
    Irreducible (quadratic (AdjoinRoot.root f ^ 3 + AdjoinRoot.root f ^ 2)) := by
  subst g
  exact hc

end MIPRE.LowDegree.BinaryArtinSchreier

end