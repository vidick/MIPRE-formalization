/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.PauliCons
public import MIPRE.Background.Introspection.DecisionKernelPauli

@[expose] public section

/-!
# The introspection kernel's Pauli conjunct as controlled linear constraints

`MIPRE.Introspection.DecisionKernel.program_pauli_iff` reads the decision kernel, at a pair of
Pauli labels, as two endpoint-validity checks, the Pauli basis test on the decoded questions and
answers, and the auxiliary conjunct. `program_pauli_iff_cons` replaces the first three by the
answer lengths of the tailored layout (`pauliLen`) and the satisfaction of the controlled linear
constraints `pauliCons` (`MIPRE/Background/Tailored/Intro/PauliCons.lean`), which is the form
the tailored presentation of the introspection verifier consumes.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.PauliCons

open Cost MIPRE.Introspection MIPRE.Introspection.DecisionKernel

/-- **The kernel at a pair of Pauli labels is the tailored check.** The decision kernel accepts
exactly when both answers have their label's length, the constraints of `pauliCons` at the
readable prefixes are satisfied, and the auxiliary conjunct holds. -/
theorem program_pauli_iff_cons (V : Verifier 7) (lam n Q R : ℕ) (W : ClockedUniversalMachine)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (SAT.shoupBinField k hk).carrier) (t u : QLD.Ty)
    (x y a b : BitStr)
    (hx : x.length = (3 * 2 ^ j + 3) * k) (hy : y.length = (3 * 2 ^ j + 3) * k) :
    program W (canonicalInput V lam n Q R (unary k, unary j, unary (2 ^ j)) (.inl t) (.inl u)
        x y a b) = true ↔
      a.length = pauliLen (2 ^ j) k t ∧ b.length = pauliLen (2 ^ j) k u ∧
      (∀ c ∈ pauliCons k hk hodd j hm t u x y (a.take (pauliLenR k (2 ^ j) t))
          (b.take (pauliLenR k (2 ^ j) u)), Tailored.Satisfies c (a ++ b ++ [true])) ∧
      auxiliary W (canonicalInput V lam n Q R (unary k, unary j, unary (2 ^ j)) (.inl t)
        (.inl u) x y a b) = true := by
  have h := program_pauli_iff V lam n Q R x y a b W k hk hodd j hj hm t u hx hy
  dsimp only at h
  rw [h, endpointValid_iff k hk j, endpointValid_iff k hk j]
  constructor
  · rintro ⟨ha, hb, hacc, haux⟩
    exact ⟨ha, hb, (pauliCons_iff k hk hodd j hm t u x y a b ha hb).2 hacc, haux⟩
  · rintro ⟨ha, hb, hcons, haux⟩
    exact ⟨ha, hb, (pauliCons_iff k hk hodd j hm t u x y a b ha hb).1 hcons, haux⟩

end MIPRE.Tailored.Intro.PauliCons

end

end
