/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryTrace
import MIPRE.Foundations.SAT.QuotientField

/-! # Frobenius and trace in the effective Shoup field -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryPolynomial

instance shoupBinField_algebra (k : ℕ) (hk : 1 ≤ k) :
    Algebra (ZMod 2) (shoupBinField k hk).carrier := by
  change Algebra (ZMod 2) (AdjoinRoot (polyOfBits (shoupIrreducible (unary k))))
  infer_instance

/-- The effective quotient field has the stated extension degree over the binary field. -/
theorem shoupBinField_finrank (k : ℕ) (hk : 1 ≤ k) :
    Module.finrank (ZMod 2) (shoupBinField k hk).carrier = k := by
  change Module.finrank (ZMod 2) (AdjoinRoot (polyOfBits (shoupIrreducible (unary k)))) = k
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' (shoupIrreducible_monic k hk)),
    Fintype.card_fin, shoupIrreducible_natDegree k hk]

/-- Construct the field and perform a unary-specified number of Frobenius steps. -/
def shoupFrobeniusTraceProg : PolyTimeFun (Unary × BitStr × Unary) (BitStr × BitStr) :=
  frobeniusTraceProg.comp ((shoupLowerCoeffs.comp PolyTimeFun.fst).pair PolyTimeFun.snd)

/-- Canonical coordinates of the Frobenius iterate are computed uniformly. -/
theorem shoupFrobeniusTraceProg_frobenius (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) (u : Unary) :
    (shoupFrobeniusTraceProg (unary k, (shoupBinField k hk).toBits a, u)).1 =
      (shoupBinField k hk).toBits (a ^ (2 ^ u.length)) := by
  have hw : ((shoupBinField k hk).toBits a).length =
      (shoupLowerCoeffs (unary k)).length := by
    rw [(shoupBinField k hk).length_toBits, shoupLowerCoeffs_length k hk]
  apply (shoupRoot_eval_eq_iff k hk _ _
    ((length_frobeniusTrace _ _ u hw).1.trans (shoupLowerCoeffs_length k hk))
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits]
  have h := (evalBits_frobeniusTrace (shoupRoot k hk) _ _ u (shoupRoot_equation k hk) hw).1
  simpa only [shoupRoot_eval_toBits] using h

/-- Computing `k` successive squarings gives the identity on the degree-`k` field. -/
theorem shoupFrobeniusTraceProg_period (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    (shoupFrobeniusTraceProg (unary k, (shoupBinField k hk).toBits a, unary k)).1 =
      (shoupBinField k hk).toBits a := by
  rw [shoupFrobeniusTraceProg_frobenius, length_unary,
    ← (shoupBinField k hk).card_carrier, FiniteField.pow_card]

/-- The trace sum, returned as canonical coordinates in the extension field. -/
def shoupTraceProg : PolyTimeFun (Unary × BitStr) BitStr :=
  PolyTimeFun.snd.comp (shoupFrobeniusTraceProg.comp
    (PolyTimeFun.fst.pair (PolyTimeFun.snd.pair PolyTimeFun.fst)))

theorem shoupTraceProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupTraceProg (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits
        (algebraMap (ZMod 2) (shoupBinField k hk).carrier
          (Algebra.trace (ZMod 2) (shoupBinField k hk).carrier a)) := by
  have hw : ((shoupBinField k hk).toBits a).length =
      (shoupLowerCoeffs (unary k)).length := by
    rw [(shoupBinField k hk).length_toBits, shoupLowerCoeffs_length k hk]
  apply (shoupRoot_eval_eq_iff k hk _ _
    ((length_frobeniusTrace _ _ (unary k) hw).2.trans (shoupLowerCoeffs_length k hk))
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits]
  have h := evalBits_frobeniusTrace_trace (shoupRoot k hk) _ _
    ((shoupBinField_finrank k hk).trans (shoupLowerCoeffs_length k hk).symm)
    (shoupRoot_equation k hk) hw
  rw [shoupLowerCoeffs_length k hk, shoupRoot_eval_toBits] at h
  exact h

/-- Trace computation, including field construction, has polynomial runtime in `k`. -/
theorem shoupTraceProg_time_le : ∃ R : Polynomial ℕ, ∀ k : ℕ, ∀ a : BitStr,
    a.length = k → ∃ t ≤ R.eval k,
      shoupTraceProg.code.Runs (encode (unary k, a))
        (encode (shoupTraceProg (unary k, a))) t := by
  refine ⟨shoupTraceProg.timeBound.comp (6 * Polynomial.X + 3), fun k a ha => ?_⟩
  obtain ⟨t, ht, hr⟩ := shoupTraceProg.computes (unary k, a)
  refine ⟨t, ht.trans ?_, hr⟩
  have hsize : esize (unary k, a) ≤ 6 * k + 3 := by
    have h := esize_bitStr_le a
    simp only [esize_prod, esize_unary]
    rw [ha] at h
    omega
  simpa using polynomial_eval_mono shoupTraceProg.timeBound hsize

end MIPRE.SAT

end
