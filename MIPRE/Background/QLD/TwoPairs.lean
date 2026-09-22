/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.MTilde

/-!
# Both entangled pairs, without changing the interface

The paper's expanded state carries two maximally entangled pairs,
`psi-hat = psi_{AB} (x) EPR_{A'A''} (x) EPR_{B'B''}` (`qld-commutation.tex`, `sec:expanding`), and
the six registers are partitioned into two parties in **two** ways: `A A'` against `B A''`, and
`B B'` against `A B''`. Every bipartite relation derived for one holds for the other with the
registers changed. `SimulPair` is the first partition; `lem:qld-pauli-selfcons` and `lem:qld-swap`
compare an object built on the first with one built on the second, so both are needed at once, on
one state, and that is what this file's regroupings supply.

## The second pair is appended, not hidden in the padding

`planning/qld-two-pairs-scope.md` first scoped this as a retyping of `SimulPair.Phi`, and then as
putting the second pair inside `SimulPair`'s arbitrary padding registers `EA` and `EB`. Neither is
right, and the second is wrong for a reason worth stating: the paper's pair measurement `S-hat` is
supported on `A A'` (`lem:qld-4-7`: it acts on `H (x) (C^q)^{(x) n}` for `H` one party's space),
and `M-tilde` is then "an operator acting on registers `A A' A''`". A measurement living inside
`(dA x Anc) x EA` with `B''` buried in `EA` would be free to act on `B''`, which is Bob's --- and
then neither `M-tilde` nor the swap unitary built from it is local, and the self-consistency of
`lem:qld-pauli-selfcons` cannot even be stated, because its two sides would not lie on opposite
sides of any cut.

So the second pair is **appended**: a `SimulPair` is left exactly as stages 4a--4c produce it, on
`(dA x Anc) x EA` against `(dB x Anc) x EB`, and the pair `EPR_{B'B''}` is tensored on afterwards
with `expVec`, one half to each party. A party register is then

```
((X x Anc) x E) x Anc
```

--- the party's own space, its half of the pair the state already carried, its padding, and the
half of the appended pair the cut gives it. Alice's is `((A x A') x Ea) x B''` and Bob's is
`((B x A'') x Eb) x B'`. The point of the ordering is that `mTilde` appends its Pauli register at
the end of the party register it is built on, so `mTildeAnc` built from a `SimulPair` on
`(dA x Anc) x Ea` already lands on `((A x A') x Ea) x A''` --- Alice's **physical** register, with
no `B''` in it and no reindexing to arrange.

## The two regroupings

`pairSwapEquiv` sends each party's far half home: from the first cut to the physical grouping
`A A' Ea A''` against `B B' Eb B''`. `mirrorEquiv` is the change of reading between the paper's two
cuts. They meet on the nose --- `pairSwapVec_mirrorVec` --- so a statement proved on either cut is
a statement about one and the same physical vector.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE
open scoped Kronecker ComplexOrder MatrixOrder

section Swap

variable {A B T1 T2 S1 S2 E E' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T1] [DecidableEq T1] [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1]
  [Fintype S2] [DecidableEq S2] [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']

/-- **The permutation onto the physical grouping.** `T1` and `S1` are the halves of the pair the
`SimulPair`'s own state carries, split across its cut; `T2` and `S2` are the halves of the appended
pair, split the opposite way. This sends each party's far half home, leaving the party's own space,
its padding and both of its pair halves together. -/
def pairSwapEquiv :
    (((A × T1) × E) × T2) × (((B × S1) × E') × S2)
      ≃ (((A × T1) × E) × S1) × (((B × S2) × E') × T2) where
  toFun p := ((p.1.1, p.2.1.1.2), (((p.2.1.1.1, p.2.2), p.2.1.2), p.1.2))
  invFun q := ((q.1.1, q.2.2), (((q.2.1.1.1, q.1.2), q.2.1.2), q.2.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The state, read along it. -/
def pairSwapVec (ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ) :
    (((A × T1) × E) × S1) × (((B × S2) × E') × T2) → ℂ :=
  ψ ∘ (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1) (S2 := S2)
    (E := E) (E' := E')).symm

omit [DecidableEq A] [DecidableEq B] [DecidableEq T1] [DecidableEq T2] [DecidableEq S1]
  [DecidableEq S2] [DecidableEq E] [DecidableEq E'] in
/-- A regrouped unit vector is a unit vector. -/
theorem pairSwapVec_unit
    {ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (pairSwapVec ψ) ⬝ᵥ pairSwapVec ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1)
    (S2 := S2) (E := E) (E' := E')).symm fun p => star ψ p * ψ p

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T1] [DecidableEq T1]
  [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1] [Fintype S2] [DecidableEq S2]
  [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E'] in
/-- **The same operator, grouped the two ways.** A product across all eight factors is carried by
the permutation to the product of the two parties' physical quadruples. -/
theorem reindex_pairSwapEquiv (XA : Matrix A A ℂ) (Y1 : Matrix T1 T1 ℂ) (ZA : Matrix E E ℂ)
    (Y2 : Matrix T2 T2 ℂ) (XB : Matrix B B ℂ) (W1 : Matrix S1 S1 ℂ) (ZB : Matrix E' E' ℂ)
    (W2 : Matrix S2 S2 ℂ) :
    Matrix.reindex (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1) (S2 := S2)
        (E := E) (E' := E'))
        (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1) (S2 := S2)
        (E := E) (E' := E'))
        (((((XA ⊗ₖ Y1) ⊗ₖ ZA) ⊗ₖ Y2)) ⊗ₖ ((((XB ⊗ₖ W1) ⊗ₖ ZB) ⊗ₖ W2)))
      = ((((XA ⊗ₖ Y1) ⊗ₖ ZA) ⊗ₖ W1)) ⊗ₖ ((((XB ⊗ₖ W2) ⊗ₖ ZB) ⊗ₖ Y2)) := by
  ext p q
  obtain ⟨⟨⟨a, t1⟩, ea⟩, s1⟩ := p.1
  obtain ⟨⟨⟨b, s2⟩, eb⟩, t2⟩ := p.2
  obtain ⟨⟨⟨a', t1'⟩, ea'⟩, s1'⟩ := q.1
  obtain ⟨⟨⟨b', s2'⟩, eb'⟩, t2'⟩ := q.2
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, pairSwapEquiv, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply]
  ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq T1] [DecidableEq T2] [DecidableEq S1]
  [DecidableEq S2] [DecidableEq E] [DecidableEq E'] in
/-- **And so is the quadratic form.** -/
theorem qform_pairSwapVec (ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ)
    (XA : Matrix A A ℂ) (Y1 : Matrix T1 T1 ℂ) (ZA : Matrix E E ℂ) (Y2 : Matrix T2 T2 ℂ)
    (XB : Matrix B B ℂ) (W1 : Matrix S1 S1 ℂ) (ZB : Matrix E' E' ℂ) (W2 : Matrix S2 S2 ℂ) :
    qform (pairSwapVec ψ)
        (((((XA ⊗ₖ Y1) ⊗ₖ ZA) ⊗ₖ W1)) ⊗ₖ ((((XB ⊗ₖ W2) ⊗ₖ ZB) ⊗ₖ Y2)))
      = qform ψ (((((XA ⊗ₖ Y1) ⊗ₖ ZA) ⊗ₖ Y2)) ⊗ₖ ((((XB ⊗ₖ W1) ⊗ₖ ZB) ⊗ₖ W2))) := by
  rw [qform, qform, pairSwapVec, ← reindex_pairSwapEquiv, qform_comp_equiv]

/-! ## The mirror of the cut -/

/-- **The change of reading between the paper's two partitions.** `qld-commutation.tex`
(`sec:expanding`) partitions the six registers two ways --- `A A'` against `B A''`, and `B B'`
against `A B''` --- and records that every bipartite relation derived for one holds for the other,
"with the registers appropriately changed". This is that change of registers: the same state, with
the parties exchanged and each party's two pair halves traded, so that what was the far half of one
pair becomes the near half of the other. -/
def mirrorEquiv :
    (((A × T1) × E) × T2) × (((B × S1) × E') × S2)
      ≃ (((B × S2) × E') × S1) × (((A × T2) × E) × T1) where
  toFun p := ((((p.2.1.1.1, p.2.2), p.2.1.2), p.2.1.1.2),
    (((p.1.1.1.1, p.1.2), p.1.1.2), p.1.1.1.2))
  invFun q := ((((q.2.1.1.1, q.2.2), q.2.1.2), q.2.1.1.2),
    (((q.1.1.1.1, q.1.2), q.1.1.2), q.1.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The state, read along the mirrored cut. -/
def mirrorVec (ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ) :
    (((B × S2) × E') × S1) × (((A × T2) × E) × T1) → ℂ :=
  ψ ∘ (mirrorEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1) (S2 := S2)
    (E := E) (E' := E')).symm

omit [DecidableEq A] [DecidableEq B] [DecidableEq T1] [DecidableEq T2] [DecidableEq S1]
  [DecidableEq S2] [DecidableEq E] [DecidableEq E'] in
/-- A mirrored unit vector is a unit vector. -/
theorem mirrorVec_unit
    {ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (mirrorVec ψ) ⬝ᵥ mirrorVec ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (mirrorEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1)
    (S2 := S2) (E := E) (E' := E')).symm fun p => star ψ p * ψ p

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T1] [DecidableEq T1]
  [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1] [Fintype S2] [DecidableEq S2]
  [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E'] in
/-- **The two readings meet on the physical grouping**, and they meet on the nose: pulling each
party's far half home from the mirrored cut lands on the very same vector as doing it from the
original one, with only the two parties written in the other order. This is why the mirror costs
nothing --- every statement proved on one cut is a statement about `pairSwapVec ψ` once it is
pushed to the physical grouping, whichever cut it came from. -/
theorem pairSwapVec_mirrorVec (ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ) :
    pairSwapVec (mirrorVec ψ) = pairSwapVec ψ ∘ Prod.swap := rfl

end Swap

end MIPRE.QLD

end
