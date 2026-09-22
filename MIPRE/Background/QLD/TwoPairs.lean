/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.MTilde

/-!
# Both entangled pairs, without changing the interface

`planning/qld-two-pairs-scope.md` scoped the change that unblocks the two remaining QLD assemblies
as a retyping of `SimulPair.Phi`: the paper's state has two entangled pairs, `A' A''` local to
Alice and `B' B''` local to Bob, and `Phi` looked as though it carried only one.

It does not need retyping. `SimulPair`'s padding registers `EA` and `EB` are **arbitrary types**,
constrained only by `Fintype` and `DecidableEq`, so the second pair can live inside them:
`EA = Anc x EA'` and `EB = Anc x EB'`. The structure, the four merged files that build on it and
every statement about `Phi` are untouched; what is added is the regrouping that makes both parties'
exact Pauli objects readable at once.

## The cut the comparison needs

Read `Phi`'s factors as the paper's registers, with each pair split across the party cut the way
`hatVec` already splits the first:

* Alice's side, `(dA x Anc) x (Anc x EA')`, is `A A'` and `B'' EA'`;
* Bob's side, `(dB x Anc) x (Anc x EB')`, is `B A''` and `B' EB'`.

`Phi_reduced` pins the first `Anc` on each side to be the halves of the pair `hatVec` carries, `A'`
with Alice and `A''` with Bob, and says nothing about the second, which is free to be the other
pair split the other way.

Alice's `M~` wants `A A' A''` and Bob's wants `B B' B''`, so each needs one register from the far
side --- and they are *different* registers, `A''` for Alice and `B''` for Bob. One permutation
therefore serves both: send `A''` to Alice and `B''` to Bob, which is `pairSwapEquiv`. After it
Alice holds `A A' A''` and Bob holds `B B' B''`, the physical grouping, and both exact Pauli
objects are expressible on the same bipartite cut --- which is exactly what
`lem:qld-pauli-selfcons`'s conclusion and `lem:qld-swap` item 1 compare.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE
open scoped Kronecker ComplexOrder MatrixOrder

section Swap

variable {A B T1 T2 S1 S2 E E' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T1] [DecidableEq T1] [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1]
  [Fintype S2] [DecidableEq S2] [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']

/-- **The permutation onto the physical grouping.** `T1` and `S1` are the first pair's halves,
`S2` and `T2` the second's, each split across the party cut the opposite way; this sends each
party's far half home. -/
def pairSwapEquiv :
    ((A × T1) × (T2 × E)) × ((B × S1) × (S2 × E'))
      ≃ (((A × T1) × S1) × E) × (((B × S2) × T2) × E') where
  toFun p := ((((p.1.1.1, p.1.1.2), p.2.1.2), p.1.2.2),
    (((p.2.1.1, p.2.2.1), p.1.2.1), p.2.2.2))
  invFun q := (((q.1.1.1.1, q.1.1.1.2), (q.2.1.2, q.1.2)),
    ((q.2.1.1.1, q.1.1.2), (q.2.1.1.2, q.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The state, read along it. -/
def pairSwapVec (ψ : ((A × T1) × (T2 × E)) × ((B × S1) × (S2 × E')) → ℂ) :
    (((A × T1) × S1) × E) × (((B × S2) × T2) × E') → ℂ :=
  ψ ∘ (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1) (S2 := S2)
    (E := E) (E' := E')).symm

omit [DecidableEq A] [DecidableEq B] [DecidableEq T1] [DecidableEq T2] [DecidableEq S1]
  [DecidableEq S2] [DecidableEq E] [DecidableEq E'] in
/-- A regrouped unit vector is a unit vector. -/
theorem pairSwapVec_unit
    {ψ : ((A × T1) × (T2 × E)) × ((B × S1) × (S2 × E')) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (pairSwapVec ψ) ⬝ᵥ pairSwapVec ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1)
    (S2 := S2) (E := E) (E' := E')).symm fun p => star ψ p * ψ p

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T1] [DecidableEq T1]
  [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1] [Fintype S2] [DecidableEq S2]
  [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E'] in
/-- **The same operator, grouped the two ways.** A product across all eight factors is carried by
the permutation to the product of the two parties' triples. -/
theorem reindex_pairSwapEquiv (XA : Matrix A A ℂ) (Y1 : Matrix T1 T1 ℂ) (Y2 : Matrix T2 T2 ℂ)
    (ZA : Matrix E E ℂ) (XB : Matrix B B ℂ) (W1 : Matrix S1 S1 ℂ) (W2 : Matrix S2 S2 ℂ)
    (ZB : Matrix E' E' ℂ) :
    Matrix.reindex (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1) (S2 := S2)
        (E := E) (E' := E'))
        (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1) (S2 := S2)
        (E := E) (E' := E'))
        (((XA ⊗ₖ Y1) ⊗ₖ (Y2 ⊗ₖ ZA)) ⊗ₖ ((XB ⊗ₖ W1) ⊗ₖ (W2 ⊗ₖ ZB)))
      = (((XA ⊗ₖ Y1) ⊗ₖ W1) ⊗ₖ ZA) ⊗ₖ (((XB ⊗ₖ W2) ⊗ₖ Y2) ⊗ₖ ZB) := by
  ext p q
  obtain ⟨⟨⟨a, t1⟩, s1⟩, e⟩ := p.1
  obtain ⟨⟨⟨b, s2⟩, t2⟩, e'⟩ := p.2
  obtain ⟨⟨⟨a', t1'⟩, s1'⟩, e''⟩ := q.1
  obtain ⟨⟨⟨b', s2'⟩, t2'⟩, e'''⟩ := q.2
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, pairSwapEquiv, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply]
  ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq T1] [DecidableEq T2] [DecidableEq S1]
  [DecidableEq S2] [DecidableEq E] [DecidableEq E'] in
/-- **And so is the quadratic form.** -/
theorem qform_pairSwapVec (ψ : ((A × T1) × (T2 × E)) × ((B × S1) × (S2 × E')) → ℂ)
    (XA : Matrix A A ℂ) (Y1 : Matrix T1 T1 ℂ) (Y2 : Matrix T2 T2 ℂ) (ZA : Matrix E E ℂ)
    (XB : Matrix B B ℂ) (W1 : Matrix S1 S1 ℂ) (W2 : Matrix S2 S2 ℂ) (ZB : Matrix E' E' ℂ) :
    qform (pairSwapVec ψ)
        ((((XA ⊗ₖ Y1) ⊗ₖ W1) ⊗ₖ ZA) ⊗ₖ (((XB ⊗ₖ W2) ⊗ₖ Y2) ⊗ₖ ZB))
      = qform ψ (((XA ⊗ₖ Y1) ⊗ₖ (Y2 ⊗ₖ ZA)) ⊗ₖ ((XB ⊗ₖ W1) ⊗ₖ (W2 ⊗ₖ ZB))) := by
  rw [qform, qform, pairSwapVec, ← reindex_pairSwapEquiv, qform_comp_equiv]

end Swap

end MIPRE.QLD

end
