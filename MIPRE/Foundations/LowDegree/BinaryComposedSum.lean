/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryComposedSumProg
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Correctness of the effective coprime-degree composed-sum construction -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost BinaryPolynomial Polynomial BinaryFiniteField

variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]

include hf in
/-- The canonical root's Frobenius orbit closes at the degree of its modulus. -/
theorem root_frobenius_period : AdjoinRoot.root f ^ (2 ^ f.natDegree) = AdjoinRoot.root f := by
  have hi := AdjoinRoot.isIntegral_root hf.ne_zero
  have hm : minpoly (ZMod 2) (AdjoinRoot.root f) = f := by
    simpa only [hf.leadingCoeff, inv_one, map_one, mul_one] using AdjoinRoot.minpoly_root hf.ne_zero
  apply (minpoly_natDegree_dvd_iff_frobenius _ hi _).mp
  rw [hm]

include hf in
/-- The executable composed-sum output has the specified product interpretation. -/
theorem map_composedSumBits (p g : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic) :
    (polyOfBits (composedSumBits p g)).map (algebraMap (ZMod 2) (AdjoinRoot f)) =
      composedSumPolynomial (polyOfBits g) (AdjoinRoot.root f) f.natDegree := by
  let : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have hp0 : p ≠ [] := by
    intro h
    have hpos := (Fact.out : Irreducible f).natDegree_pos
    simp [h] at hp
    omega
  let bs := orbitBits (unary p.length) p (rootBits p)
  let cs := normProductBits p g bs
  have hb : ∀ a ∈ bs, a.length = p.length := orbitBits_width _ p _ (length_rootBits p)
  have hc : ∀ c ∈ cs, c.length = p.length := by
    apply fold_normStep_width bs p g [oneBits p] hb
    intro c h
    obtain rfl := List.mem_singleton.mp h
    exact length_oneBits p
  have hroot := root_eq f p hpoly
  have he := map_evalBits_orbitBits (AdjoinRoot.root f) (unary p.length) p (rootBits p)
    hroot (length_rootBits p)
  rw [evalBits_rootBits _ p hp0 hroot, length_unary, hp] at he
  have hprod : coeffPolynomial (AdjoinRoot.root f) cs =
      composedSumPolynomial (polyOfBits g) (AdjoinRoot.root f) f.natDegree := by
    dsimp only [cs]
    rw [coeffPolynomial_normProductBits _ p g bs hp0 hroot hb]
    have h := congrArg (fun l : List (AdjoinRoot f) =>
      (l.map (translatedPolynomial (polyOfBits g))).prod) he
    simpa only [List.map_map, List.map_ofFn, Function.comp_def, bs, hp, composedSumPolynomial] using h
  change (polyOfBits (descendBits cs)).map _ = _
  rw [map_polyOfBits_descendBits _ cs ?_, hprod]
  intro c hmem
  apply evalBits_eq_head_of_zero_or_one f hf p c hp ((hc c hmem).trans hp) hp0
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
  have hcoeff : (coeffPolynomial (AdjoinRoot.root f) cs).coeff i = evalBits (AdjoinRoot.root f) c := by
    simp only [coeff_coeffPolynomial, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, he]
  rw [← hcoeff, hprod]
  exact composedSumPolynomial_coeff_zero_or_one _ hg _ _ (root_frobenius_period f hf) i

include hf in
/-- The descended composed sum is monic, of the product degree. -/
theorem composedSumBits_monic_natDegree (p g : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic) :
    (polyOfBits (composedSumBits p g)).Monic ∧
      (polyOfBits (composedSumBits p g)).natDegree = f.natDegree * (polyOfBits g).natDegree := by
  have h := map_composedSumBits f hf p g hp hpoly hg
  constructor
  · have hm := composedSumPolynomial_monic (polyOfBits g) hg (AdjoinRoot.root f) f.natDegree
    rw [← h] at hm
    exact Polynomial.monic_map_iff.mp hm
  · rw [← natDegree_map_eq_of_injective (algebraMap (ZMod 2) (AdjoinRoot f)).injective, h,
      natDegree_composedSumPolynomial _ hg]

include hf in
/-- The uniform composed-sum program combines irreducible polynomials of coprime degrees. -/
theorem composedSumBits_correct (p g : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic)
    (hgi : Irreducible (polyOfBits g)) (hcop : f.natDegree.Coprime (polyOfBits g).natDegree) :
    (polyOfBits (composedSumBits p g)).Monic ∧ Irreducible (polyOfBits (composedSumBits p g)) ∧
      (polyOfBits (composedSumBits p g)).natDegree = f.natDegree * (polyOfBits g).natDegree := by
  let L := AlgebraicClosure (ZMod 2)
  let : CharP L 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) L).injective 2
  have hfi : Irreducible f := Fact.out
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero L f hfi.degree_pos.ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero L (polyOfBits g) hgi.degree_pos.ne'
  let φ : AdjoinRoot f →ₐ[ZMod 2] L := AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) x hx
  have hφ : φ (AdjoinRoot.root f) = x := AdjoinRoot.liftAlgHom_root ..
  have hbase : φ.toRingHom.comp (algebraMap (ZMod 2) (AdjoinRoot f)) = algebraMap (ZMod 2) L := by
    ext z
    exact φ.commutes z
  have hmap := congrArg (Polynomial.map φ.toRingHom) (map_composedSumBits f hf p g hp hpoly hg)
  rw [Polynomial.map_map, hbase, map_composedSumPolynomial, hφ] at hmap
  have hz : aeval (x + y) (polyOfBits (composedSumBits p g)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]
    exact eval_composedSumPolynomial _ x y _ hfi.natDegree_pos hy
  have hmd := composedSumBits_monic_natDegree f hf p g hp hpoly hg
  have hix : IsIntegral (ZMod 2) x := ⟨f, hf, hx⟩
  have hiy : IsIntegral (ZMod 2) y := ⟨_, hg, hy⟩
  have hmx : minpoly (ZMod 2) x = f := (minpoly.eq_of_irreducible_of_monic hfi hx hf).symm
  have hmy : minpoly (ZMod 2) y = polyOfBits g := (minpoly.eq_of_irreducible_of_monic hgi hy hg).symm
  have hdeg : (minpoly (ZMod 2) (x + y)).natDegree = f.natDegree * (polyOfBits g).natDegree := by
    rw [minpoly_natDegree_add_of_coprime x y hix hiy (by simpa only [hmx, hmy] using hcop), hmx, hmy]
  have heq : polyOfBits (composedSumBits p g) = minpoly (ZMod 2) (x + y) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hix.add hiy)) hmd.1
      (minpoly.dvd _ _ hz) (by rw [hmd.2, hdeg])
  refine ⟨hmd.1, ?_, hmd.2⟩
  rw [heq]
  exact minpoly.irreducible (hix.add hiy)

end MIPRE.LowDegree.BinaryQuotient

end
