/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Fold
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.ZMod.Basic

/-!
# The one imported construction: Shoup's irreducible polynomials over `𝔽₂`

`lem:self-dual-basis` is, as the blueprint says, the whole of what this project assumes beyond
Mathlib, and the assumption is narrower than the lemma: the adversarial-verification campaign
proved the normal-basis construction and the self-dualization over sixteen sub-nodes, and left
exactly one admitted, node `1.1.6.1.1` --- Shoup's deterministic irreducible-polynomial
construction, specialized to characteristic `2`.

That node carries an explicit contract, and this file is that contract as a Lean `axiom`.

**What is asserted.** A *fixed uniform deterministic* algorithm which, given `k ≥ 1`, outputs
a monic irreducible `f ∈ 𝔽₂[T]` of degree `k` in `poly(k)` bit operations. This is the `p = 2`
specialization of Shoup 1990, Theorem 3.2.

**What is not.** No claim of `poly(log k)` output time; no variable-characteristic
`poly(log p, k)` form; no randomized success; no advice tables; no enumeration of all `2^k`
field elements.

The `poly(k)` rather than `poly(log k)` is not a detail, and it is what fixes the shape of the
statement: the input is `Unary k`, whose encoding size is `2k + 1` (`Cost.esize_unary`), so
`PolyTimeFun`'s bound is a polynomial in `k`. Had the input been `k` in binary, `PolyTimeFun`
would assert the `poly(log k)` bound the contract explicitly disclaims.

**Why an `axiom` and not a `sorry`.** `CONTRIBUTING.md` allows a merged `sorry` only for a
blueprint node tracked by an open issue, which is right for work this project intends to do.
This is not that: it is an imported construction that the project does not intend to
formalize, and the blueprint says so ("which is the shape a Lean `axiom` for it should take").
As an axiom it also appears by name in `#print axioms` of everything that rests on it, so the
dependency is visible and machine-checkable rather than a matter of reading docstrings;
`MIPRE/Axioms.lean` records it.
-/

noncomputable section

namespace MIPRE.LowDegree

open Cost

/-- The polynomial over `𝔽₂` whose coefficient of `Tⁱ` is bit `i` of `l`, least significant
first --- the repository's little-endian bit convention (`Cost.bitsVal`, `bitsOfNat`). -/
def polyOfBits (l : List Bool) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range l.length, Polynomial.monomial i (if l.getD i false then 1 else 0)

/-- **Shoup's deterministic irreducible-polynomial construction, `p = 2`** (Shoup 1990,
Theorem 3.2; ledger node `1.1.6.1.1`, the one admitted node under `lem:self-dual-basis`).

The module docstring states the contract in full, including what is deliberately *not*
claimed. In particular the `Unary` input is what makes the time bound `poly(k)` rather than
the `poly(log k)` the contract disclaims. -/
axiom exists_shoup_irreducible :
    ∃ F : PolyTimeFun Unary (List Bool), ∀ k : ℕ, 1 ≤ k →
      (polyOfBits (F (unary k))).Monic ∧
        Irreducible (polyOfBits (F (unary k))) ∧
        (polyOfBits (F (unary k))).natDegree = k

/-- The construction the axiom provides, named so that consumers do not each `choose`. -/
def shoupIrreducible : PolyTimeFun Unary (List Bool) :=
  exists_shoup_irreducible.choose

/- The axiom dependency, pinned. This fails the build if another axiom creeps in, if the
dependency disappears (the axiom having been proved, which is worth noticing), or if the name
changes; `MIPRE/Axioms.lean` records the axiom itself, and `scripts/lean-coverage.py` fails
if it stops doing so. -/
/-- info: 'MIPRE.LowDegree.shoupIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound, exists_shoup_irreducible] -/
#guard_msgs in
#print axioms MIPRE.LowDegree.shoupIrreducible

theorem shoupIrreducible_monic (k : ℕ) (hk : 1 ≤ k) :
    (polyOfBits (shoupIrreducible (unary k))).Monic :=
  (exists_shoup_irreducible.choose_spec k hk).1

theorem shoupIrreducible_irreducible (k : ℕ) (hk : 1 ≤ k) :
    Irreducible (polyOfBits (shoupIrreducible (unary k))) :=
  (exists_shoup_irreducible.choose_spec k hk).2.1

theorem shoupIrreducible_natDegree (k : ℕ) (hk : 1 ≤ k) :
    (polyOfBits (shoupIrreducible (unary k))).natDegree = k :=
  (exists_shoup_irreducible.choose_spec k hk).2.2

end MIPRE.LowDegree

end
