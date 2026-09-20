/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.FieldVectors
import MIPRE.Foundations.SAT.PcpFieldTests
import MIPRE.Foundations.SAT.PcpBlocks
import Mathlib.Algebra.BigOperators.Fin

/-! # The raw field tests on typed PCP views -/

namespace MIPRE.SAT.PcpViewTests

open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial

def literals (P : PcpParams) (z ev : List BitStr) : List (BitStr × BitStr) :=
  (ev.take 5).zip ((z.drop (5 * P.m)).take 5)

def certificates (z ev : List BitStr) : List (BitStr × BitStr) := (ev.drop 6).zip z

variable {k : ℕ} (E : BinField k) (P : PcpParams)

theorem main_claim (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    (E.vecBits α ++ E.vecBits β).getD 5 [] = E.toBits (β 0) := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), E.length_vecBits, Nat.sub_self]
  exact E.getD_vecBits β 0

theorem tail_claims (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    (E.vecBits α ++ E.vecBits β).drop 6 = E.vecBits (fun i : Fin P.m' => β i.succ) := by
  have ha : (E.vecBits α).drop 6 = [] := List.drop_eq_nil_of_le (by simp)
  have hb : E.vecBits β = E.toBits (β 0) :: E.vecBits (fun i : Fin P.m' => β i.succ) := by
    rw [E.vecBits_eq_ofFn, List.ofFn_succ, E.vecBits_eq_ofFn]
  rw [List.drop_append, ha, List.nil_append, E.length_vecBits]
  simpa only [hb, List.drop_succ_cons, List.drop_zero]

theorem literals_vecBits (z : Fin P.m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    literals P (E.vecBits z) (E.vecBits α ++ E.vecBits β) =
      List.ofFn (fun i => (E.toBits (α i), E.toBits (z (P.signIndex i)))) := by
  rw [literals, List.take_left' (E.length_vecBits α)]
  have hs := E.slice_vecBits z (5 * P.m) 5 (by unfold PcpParams.m'; omega)
  rw [hs]
  exact E.zip_vecBits α (fun i => z (P.signIndex i))

theorem certificates_vecBits (z : Fin P.m' → E.carrier)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    certificates (E.vecBits z) (E.vecBits α ++ E.vecBits β) =
      List.ofFn (fun i : Fin P.m' => (E.toBits (β i.succ), E.toBits (z i))) := by
  rw [certificates, tail_claims E P]
  exact E.zip_vecBits _ _

theorem correctPairs_ofFn (p : BitStr) (hpk : p.length = k) {n : ℕ}
    (a b : Fin n → E.carrier) :
    PcpFieldTests.CorrectPairs p (List.ofFn (fun i => (E.toBits (a i), E.toBits (b i)))) := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact ⟨(E.length_toBits _).trans hpk.symm, (E.length_toBits _).trans hpk.symm⟩

/-- On a typed view with canonical coefficient decoding, the executable tests
are exactly `TypedAccepts`, including the order of all certificate coordinates. -/
theorem checks_typed_iff [CharP E.carrier 2] (root : E.carrier)
    (p : BitStr) (hp : p ≠ []) (hpk : p.length = k)
    (hroot : root ^ p.length = BinaryPolynomial.evalBits root p)
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (faithful : ∀ a b : BitStr, a.length = p.length → b.length = p.length →
      (BinaryPolynomial.evalBits root a = BinaryPolynomial.evalBits root b ↔ a = b))
    (Φ : MvPolynomial (Fin P.m') E.carrier) (z : Fin P.m' → E.carrier)
    (φ : BitStr) (hφ : φ.length = p.length) (hφeval : BinaryPolynomial.evalBits root φ = eval z Φ)
    (α : Fin 5 → E.carrier) (β : Fin (P.m' + 1) → E.carrier) :
    PcpFieldTests.checksProg (p, φ, (E.vecBits α ++ E.vecBits β).getD 5 [],
      literals P (E.vecBits z) (E.vecBits α ++ E.vecBits β),
      certificates (E.vecBits z) (E.vecBits α ++ E.vecBits β)) = true ↔
        PcpAlgebra.TypedAccepts Φ z (α, β) := by
  rw [main_claim E P, literals_vecBits E P, certificates_vecBits E P]
  rw [PcpFieldTests.checksProg_true_iff root p hp hroot faithful φ (E.toBits (β 0)) hφ
    ((E.length_toBits _).trans hpk.symm) _ _
    (correctPairs_ofFn E p hpk _ _) (correctPairs_ofFn E p hpk _ _)]
  simp only [List.map_ofFn, List.prod_ofFn, List.sum_ofFn, Function.comp_apply, hencode, hφeval,
    PcpAlgebra.TypedAccepts]

end MIPRE.SAT.PcpViewTests
