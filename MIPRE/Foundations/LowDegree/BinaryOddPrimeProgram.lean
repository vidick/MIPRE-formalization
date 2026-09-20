/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryOddPrimeExtension
import MIPRE.Foundations.LowDegree.BinaryTraceBits
import MIPRE.Foundations.LowDegree.BinaryComposedSumProg

/-! # The explicit odd-prime-power construction program -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial BinaryQuotient

/-- The full binary modulus for Shoup's flat auxiliary extension. -/
def oddExtensionBits (q r : Unary) : BitStr :=
  substitutePowerBits (nonresidueLiftBitsProg q) r.tail

/-- The lower coefficients used by quotient arithmetic. -/
def oddExtensionLowerBits (q r : Unary) : BitStr := (oddExtensionBits q r).dropLast

/-- The trace generator in the explicitly represented flat extension. -/
def oddTraceBits (q r : Unary) : BitStr :=
  let p := oddExtensionLowerBits q r
  traceBits (unary (nonresidueLiftBitsProg q).tail.length) r p (BinaryQuotient.rootBits p)

/-- Print the descended orbit polynomial of the trace generator. -/
def oddPrimePowerBits (q r : Unary) : BitStr :=
  normalizeBits (orbitPolynomialBits r (oddExtensionLowerBits q r) (oddTraceBits q r))

/-- One total polynomial-time program takes unary prime and requested prime-power degree. -/
def oddPrimePowerBitsProg : PolyTimeFun (Unary × Unary) BitStr :=
  let aux := nonresidueLiftBitsProg.comp fst
  let r := snd
  let p := dropLastBitsProg.comp (substitutePowerBitsProg.comp
    (aux.pair (PolyTimeFun.tail.comp r)))
  let m := length.comp (PolyTimeFun.tail.comp aux)
  let gamma := traceBitsProg.comp (m.pair (r.pair (p.pair (BinaryQuotient.rootBitsProg.comp p))))
  normalizeBitsProg.comp (orbitPolynomialBitsProg.comp (r.pair (p.pair gamma)))

@[simp] theorem oddPrimePowerBitsProg_apply (q r : Unary) :
    oddPrimePowerBitsProg (q, r) = oddPrimePowerBits q r := by
  simp only [oddPrimePowerBitsProg, comp_apply, pair_apply, fst_apply, snd_apply,
    dropLastBitsProg_apply, substitutePowerBitsProg_apply, tail_apply, length_apply,
    traceBitsProg_apply, BinaryQuotient.rootBitsProg_apply, orbitPolynomialBitsProg_apply, normalizeBitsProg_apply]
  rfl

/-- The flat printed modulus has the exact Kummer composition semantics. -/
theorem polyOfBits_oddExtensionBits (q r : ℕ) (hr : 0 < r) :
    polyOfBits (oddExtensionBits (unary q) (unary r)) =
      (polyOfBits (nonresidueLiftBitsProg (unary q))).comp (X ^ r) := by
  rw [oddExtensionBits, polyOfBits_substitutePowerBits, List.length_tail, length_unary,
    Nat.sub_add_cancel hr]

/-- Every requested odd-prime-power flat modulus is a canonical irreducible polynomial. -/
theorem oddExtensionBits_correct (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let a := oddExtensionBits (unary q) (unary (q ^ e))
    a.getLastD false = true ∧ (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) ∧
      (polyOfBits a).natDegree =
        (polyOfBits (cyclotomicSeedBits (unary q))).natDegree * q ^ e := by
  have haux := nonresidueLiftBitsProg_correct q hq hq2
  dsimp only at haux ⊢
  have he := polyOfBits_oddExtensionBits q (q ^ e) (pow_pos hq.pos e)
  have hm : (polyOfBits (oddExtensionBits (unary q) (unary (q ^ e)))).Monic := by
    rw [he]
    exact haux.2.1.comp (monic_X.pow _) (by simp [hq.ne_zero])
  refine ⟨?_, hm, ?_, ?_⟩
  · rcases normalizeBits_getLast ((nonresidueLiftBitsProg (unary q)).flatMap
      (fun b => b :: List.replicate (unary (q ^ e)).tail.length false)) with hn | hn
    · have hz : oddExtensionBits (unary q) (unary (q ^ e)) = [] := hn
      exact (hm.ne_zero (by rw [hz]; simp [polyOfBits])).elim
    · exact hn
  · rw [he]
    exact irreducible_comp_prime_pow_of_nonresidue _ haux.2.1 haux.2.2.1 q e hq hq2 haux.2.2.2.2
  · rw [he, natDegree_comp, natDegree_X_pow, haux.2.2.2.1]

/-- Every lower extension representation has the correct modulus width and equation. -/
theorem oddExtensionLowerBits_spec (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let a := oddExtensionBits (unary q) (unary (q ^ e))
    let p := oddExtensionLowerBits (unary q) (unary (q ^ e))
    p.length = (polyOfBits a).natDegree ∧ polyOfBits a = polyOfBits (p ++ [true]) ∧ p ≠ [] := by
  let a := oddExtensionBits (unary q) (unary (q ^ e))
  have hc := oddExtensionBits_correct q e hq hq2
  have hl := natDegree_add_one_of_getLast a hc.1
  have hp := hc.2.2.1.natDegree_pos
  change a.dropLast.length = (polyOfBits a).natDegree ∧
    polyOfBits a = polyOfBits (a.dropLast ++ [true]) ∧ a.dropLast ≠ []
  have hlen : a.dropLast.length = (polyOfBits a).natDegree := by
    rw [List.length_dropLast]
    omega
  refine ⟨hlen, ?_, ?_⟩
  · rw [dropLast_append_true a hc.1]
  · intro he
    exact (Nat.ne_of_gt hp) (hlen.symm.trans (congrArg List.length he))

/-- The trace vector has exactly the flat extension width. -/
theorem oddTraceBits_width (q r : Unary) :
    (oddTraceBits q r).length = (oddExtensionLowerBits q r).length :=
  traceBits_width _ _ _ _ (BinaryQuotient.length_rootBits _)

/-- Interpreting the printed trace vector gives Shoup's precise Frobenius-stride sum. -/
theorem evalBits_oddTraceBits_of_root {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hz : z ^ (oddExtensionLowerBits (unary q) (unary (q ^ e))).length =
      evalBits z (oddExtensionLowerBits (unary q) (unary (q ^ e)))) :
    evalBits z (oddTraceBits (unary q) (unary (q ^ e))) =
      ∑ i ∈ Finset.range (polyOfBits (cyclotomicSeedBits (unary q))).natDegree,
        z ^ (2 ^ (q ^ e * i)) := by
  let p := oddExtensionLowerBits (unary q) (unary (q ^ e))
  have hp := oddExtensionLowerBits_spec q e hq hq2
  have ha := nonresidueLiftBitsProg_correct q hq hq2
  have hl := natDegree_add_one_of_getLast _ ha.1
  have hd : (nonresidueLiftBitsProg (unary q)).tail.length =
      (polyOfBits (cyclotomicSeedBits (unary q))).natDegree := by
    rw [List.length_tail, ← hl, ha.2.2.2.1]
    omega
  change evalBits z (traceBits (unary (nonresidueLiftBitsProg (unary q)).tail.length)
    (unary (q ^ e)) p (BinaryQuotient.rootBits p)) = _
  rw [evalBits_traceBits z _ _ p _ hz (BinaryQuotient.length_rootBits p),
    BinaryQuotient.evalBits_rootBits z p hp.2.2 hz, length_unary, length_unary, hd]

end MIPRE.LowDegree.BinaryPolynomial

end
