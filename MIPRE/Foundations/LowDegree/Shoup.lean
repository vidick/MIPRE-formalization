/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.LowDegree.BinaryIrreducibleConstructor

/-!
# Deterministic irreducible polynomials over the binary field

This file exposes the proved fixed-characteristic construction of Shoup 1990,
Theorem 3.2. The specified program factors squarefree binary polynomials, constructs
odd-prime auxiliary nonresidues and trace generators, builds the characteristic-two
Artin–Schreier tower, and combines coprime prime-power degrees by composed sums.

The input is the unary requested degree. Every arithmetic operation and bounded loop
is compiled into the ambient cost model, including coefficient printing and a fixed
constant output at degree zero. `BinaryPolynomial.irreducibleBitsProg_time_le` gives
the resulting polynomial runtime bound in the degree. The public names below retain
the interfaces used by the quotient-field and self-dual-normal-basis consumers.
-/

noncomputable section

namespace MIPRE.LowDegree

open Cost

/-- The specified deterministic polynomial-time irreducible-polynomial constructor. -/
def shoupIrreducible : PolyTimeFun Unary (List Bool) :=
  BinaryPolynomial.irreducibleBitsProg

/-- Shoup's deterministic irreducible-polynomial construction over `𝔽₂`
(Shoup 1990, Theorem 3.2; ledger node `1.1.6.1.1`), proved by the explicit program. -/
theorem exists_shoup_irreducible :
    ∃ F : PolyTimeFun Unary (List Bool), ∀ k : ℕ, 1 ≤ k →
      (polyOfBits (F (unary k))).Monic ∧
        Irreducible (polyOfBits (F (unary k))) ∧
        (polyOfBits (F (unary k))).natDegree = k :=
  ⟨shoupIrreducible, fun k hk => BinaryPolynomial.irreducibleBits_correct k hk⟩

/-- info: 'MIPRE.LowDegree.shoupIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.shoupIrreducible

/-- The constructed polynomial is monic at every positive degree. -/
theorem shoupIrreducible_monic (k : ℕ) (hk : 1 ≤ k) :
    (polyOfBits (shoupIrreducible (unary k))).Monic :=
  (BinaryPolynomial.irreducibleBits_correct k hk).1

/-- The constructed polynomial is irreducible at every positive degree. -/
theorem shoupIrreducible_irreducible (k : ℕ) (hk : 1 ≤ k) :
    Irreducible (polyOfBits (shoupIrreducible (unary k))) :=
  (BinaryPolynomial.irreducibleBits_correct k hk).2.1

/-- The constructed polynomial has exactly the requested positive degree. -/
theorem shoupIrreducible_natDegree (k : ℕ) (hk : 1 ≤ k) :
    (polyOfBits (shoupIrreducible (unary k))).natDegree = k :=
  (BinaryPolynomial.irreducibleBits_correct k hk).2.2

end MIPRE.LowDegree

end
