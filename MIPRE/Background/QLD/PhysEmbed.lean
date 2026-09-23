/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.MirrorExists
import MIPRE.Background.QLD.SwapItemOne
import MIPRE.Foundations.Introspection.IsometricStrategy

/-!
# The physical embedding `phi`, and why the physical state is its image

The last step of `thm:qld` (`qld-isometry.tex`, the proof of `thm:pauli-appendix`) defines one
isometry per player,

```
phi_A : |theta>_A  ↦  V_A (|theta>_A ⊗ |EPR_q>^M_{A'A''}),
```

and says that `phi_A ⊗ phi_B |psi> = V_A ⊗ V_B |psi-hat>` holds exactly, "this is the definition
of `psi-hat`". So item 1 of the swap isometry lemma, which is about `V_A ⊗ V_B |psi-hat>`, is
already item 1 of the theorem, about `phi_A ⊗ phi_B |psi>` --- provided the physical state really is
the image of `psi` under a product of *local* isometries. This file proves that it is, for the
`MirrorSimul` that `mirrorOfGlobalPairs` builds, with the isometry written down.

## The embedding

`physEmb D` maps a party's space `D` to its physical register `((D × A') × E) × A''` of
`Mirror.lean`:

```
|theta>  ↦  |theta>_D ⊗ |EPR_q>^M_{A'A''} ⊗ |0>_E .
```

`E = (F × F) × CL.Answer F (4 m) d 1` is the padding of the projective dilation (`padState`), both
registers pinned at a basis vector; its weight is `padWeight`. The paper absorbs it into "we assume
the state is padded with sufficiently many ancilla qubits"; here it is one more tensor factor, and
it is what the entry formula `physEmb_apply` carries besides the pair.

## Why the physical state is a product image

Because both of its ingredients are explicit. `padState_reindex_apply` computes the first cut's
state pointwise --- the strategy's amplitude, one pair `A'A''` split across the cut, and the padding
--- and `physVec` appends the second pair `B'B''` and pulls each party's far half home. On the
physical cut Alice then holds `A A' Ea A''` and Bob `B B' Eb B''`: **each pair is held by one party
alone**. So the state is `psi` pushed forward by one isometry per party, which is what
`physVec_mirrorOfGlobalPairs` says. The only thing to check is that the appended pair enters with
its halves the other way round, `B''` before `B'`, which is `epr_symm`.

## What else the descent needs

The paper's passage from `V`-conjugation to `phi`-conjugation rests on two identities, and both are
here at the level of the embedding, before the swap unitary is applied:

* `physEmb_conj_aOp`: `phi_0^† (X ⊗ Id) phi_0 = X`, where `X ⊗ Id` is the triple `aOp` by which
  `MirrorSimul.alicePauli` extends a strategy operator to the physical register. It is the
  compression that makes a pairing on the embedded state a pairing on `psi`.
* `physEmb_mul_mul_conjTranspose`: `phi_0 X phi_0^† = (X ⊗ Id) · P` with `P = phi_0 phi_0^†` the
  projection onto `Id ⊗ |EPR><EPR| ⊗ |0><0|`, and `P` commutes with `X ⊗ Id`
  (`aOp_mul_physEmbProj_comm`). Conjugated by `V_A`, this is the paper's
  `phi_A M_h phi_A^† = V_A (M_h ⊗ Id) V_A^† · P`.

Finally `physSwap_mulVec_physVec_mirrorOfGlobalPairs` composes with the two swap unitaries:
`M.physSwap *ᵥ M.physVec` --- the vector item 1 of `lem:qld-swap` is about --- is
`((V_A phi_0) ⊗ (V_B phi_0)) psi`, the paper's `phi_A ⊗ phi_B |psi>`, and `V_A phi_0` is an
isometry by `isometry_mul_of_isometry M.aliceSwap_conjTranspose_mul physEmb_isometry`.

## A note on spelling

`M.Ea` is only *definitionally* the padding type, so a product such as `M.aliceSwap * physEmb dA`
typechecks only while `physEmb`'s implicit arguments are still open when instance search runs:
instance search does not unfold `mirrorOfGlobalPairs`, so with both factors fully spelled it sees
two different index types and finds no multiplication. That is why the statements below leave `physEmb dA` bare where the other
factor is spelled with `M.Ea`, and why the pointwise computation in `physVec_mirrorOfGlobalPairs` is
done on the explicit padding type and only then transported.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

/- The same four-fold physical register as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

section Generic

variable {DA DB RA RB : Type*} [Fintype DA] [Fintype DB] [Fintype RA] [DecidableEq RA]
  [Fintype RB] [DecidableEq RB]

/-- **Two local operators after two local embeddings are two local embeddings.** -/
theorem aOp_mul_bOp_mulVec_kronecker (U : Matrix RA RA ℂ) (V : Matrix RB RB ℂ)
    (EA : Matrix RA DA ℂ) (EB : Matrix RB DB ℂ) (ψ : DA × DB → ℂ) :
    ((aOp U : Matrix (RA × RB) (RA × RB) ℂ) * bOp V) *ᵥ ((EA ⊗ₖ EB) *ᵥ ψ)
      = ((U * EA) ⊗ₖ (V * EB)) *ᵥ ψ := by
  rw [Matrix.mulVec_mulVec, aOp_mul_bOp_eq, ← Matrix.mul_kronecker_mul]

omit [Fintype DA] in
/-- **A unitary after an isometry is an isometry.** With `M.aliceSwap_conjTranspose_mul` and
`physEmb_isometry` it says the paper's `phi_A = V_A phi_0` is an isometry. -/
theorem isometry_mul_of_isometry [DecidableEq DA] {U : Matrix RA RA ℂ} {E : Matrix RA DA ℂ}
    (hU : Uᴴ * U = 1) (hE : Eᴴ * E = 1) : (U * E)ᴴ * (U * E) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul, hE]

end Generic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}

/-- **The physical embedding** `phi_0 : |theta> ↦ |theta> ⊗ |EPR_q>^M_{A'A''} ⊗ |0>_E`, from a
party's space `D` to its physical register `((D × A') × E) × A''`: the entry at `(p, y)` is the pair
amplitude on `A'A''` times the padding weight when `p`'s first register is `y`, and zero otherwise.
The paper's `phi_A` is this followed by the swap unitary `V_A`. -/
def physEmb (D : Type*) [DecidableEq D] :
    Matrix (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) D ℂ :=
  Matrix.of fun p y =>
    if p.1.1.1 = y then epr (F := F) (n := Fin m → Bool) (p.1.1.2, p.2) * padWeight p.1.2 else 0

omit [Fintype F] [Algebra (ZMod 2) F] in
/-- The padding weight is the indicator of the padding registers' basis vector. -/
theorem padWeight_eq_ite (e : (F × F) × CL.Answer F (4 * m) d 1) :
    padWeight e = if e = (((0 : F), (0 : F)), ansZero) then 1 else 0 := by
  obtain ⟨f, c⟩ := e
  rw [padWeight]
  by_cases h1 : f = ((0 : F), (0 : F)) <;> by_cases h2 : c = ansZero <;> simp [h1, h2]

section Embed

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Algebra (ZMod 2) F] [Fintype D] in
theorem physEmb_apply (p : ((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m)
    (y : D) :
    physEmb D p y
      = if p.1.1.1 = y then epr (F := F) (n := Fin m → Bool) (p.1.1.2, p.2) * padWeight p.1.2
        else 0 :=
  rfl

/-- **`phi_0` is an isometry**: the pair is a unit vector (`epr_unit`) and the padding weight is
the indicator of one basis vector. -/
theorem physEmb_isometry :
    (physEmb (F := F) (m := m) (d := d) D)ᴴ * physEmb (F := F) (m := m) (d := d) D = 1 := by
  ext y y'
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [conjTranspose_apply, physEmb_apply]
  rw [Finset.sum_eq_single y (fun x _ hx => by simp [hx]) (fun h => absurd (mem_univ y) h)]
  by_cases hyy : y = y'
  · subst hyy
    simp only [if_true, Matrix.one_apply_eq]
    rw [Finset.sum_comm, Finset.sum_eq_single (((0 : F), (0 : F)), ansZero)
      (fun e _ he => by simp [padWeight_eq_ite, he]) (fun h => absurd (mem_univ _) h)]
    have h := epr_unit (F := F) (n := Fin m → Bool)
    rw [dotProduct, Fintype.sum_prod_type] at h
    rw [padWeight_eq_ite, if_pos rfl]
    simpa only [mul_one, Pi.star_apply] using h
  · simp [hyy]

omit [Algebra (ZMod 2) F] in
/-- **`phi_0` intertwines an operator with its extension by the identity**: acting with `X` and
then embedding is embedding and then acting with `X ⊗ Id`, the triple `aOp` by which
`MirrorSimul.alicePauli` extends a strategy operator to the physical register. -/
theorem aOp_mul_physEmb (X : Matrix D D ℂ) :
    (aOp (aOp (aOp X)) : Matrix (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m)
        (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) ℂ)
        * physEmb (F := F) (m := m) (d := d) D
      = physEmb (F := F) (m := m) (d := d) D * X := by
  ext p y
  obtain ⟨⟨⟨x, a'⟩, e⟩, a''⟩ := p
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [aOp, kroneckerMap_apply, physEmb_apply, Matrix.one_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  ring

omit [Algebra (ZMod 2) F] in
/-- The adjoint form of the intertwining. -/
theorem physEmb_conjTranspose_mul_aOp (X : Matrix D D ℂ) :
    (physEmb (F := F) (m := m) (d := d) D)ᴴ
        * (aOp (aOp (aOp X)) : Matrix (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1))
          × Anc F m) (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) ℂ)
      = X * (physEmb (F := F) (m := m) (d := d) D)ᴴ := by
  have h := congrArg Matrix.conjTranspose (aOp_mul_physEmb (F := F) (m := m) (d := d) Xᴴ)
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    aOp_conjTranspose, aOp_conjTranspose, aOp_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h

/-- **Compressing by `phi_0` undoes the extension by the identity**: `phi_0^† (X ⊗ Id) phi_0 = X`.
A pairing of an extended operator on the embedded state is therefore the same pairing on the
strategy's own state, which is what the descent to the original measurement uses. -/
theorem physEmb_conj_aOp (X : Matrix D D ℂ) :
    (physEmb (F := F) (m := m) (d := d) D)ᴴ
        * (aOp (aOp (aOp X)) : Matrix (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1))
          × Anc F m) (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) ℂ)
        * physEmb (F := F) (m := m) (d := d) D
      = X := by
  rw [Matrix.mul_assoc, aOp_mul_physEmb, ← Matrix.mul_assoc, physEmb_isometry, Matrix.one_mul]

omit [Algebra (ZMod 2) F] in
/-- **Conjugating by `phi_0` is extending and then projecting**: `phi_0 X phi_0^† = (X ⊗ Id) P`
with `P = phi_0 phi_0^†` the projection onto `Id ⊗ |EPR><EPR| ⊗ |0><0|`. Conjugated by the swap
unitary, this is the paper's `phi_A M_h phi_A^† = V_A (M_h ⊗ Id) V_A^† · P`. -/
theorem physEmb_mul_mul_conjTranspose (X : Matrix D D ℂ) :
    physEmb (F := F) (m := m) (d := d) D * X * (physEmb (F := F) (m := m) (d := d) D)ᴴ
      = (aOp (aOp (aOp X)) : Matrix (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1))
          × Anc F m) (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) ℂ)
        * (physEmb (F := F) (m := m) (d := d) D * (physEmb (F := F) (m := m) (d := d) D)ᴴ) := by
  rw [← Matrix.mul_assoc, aOp_mul_physEmb]

omit [Algebra (ZMod 2) F] in
/-- **The projection `P` commutes with every extended operator.** -/
theorem aOp_mul_physEmbProj_comm (X : Matrix D D ℂ) :
    (aOp (aOp (aOp X)) : Matrix (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1))
        × Anc F m) (((D × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) ℂ)
        * (physEmb (F := F) (m := m) (d := d) D * (physEmb (F := F) (m := m) (d := d) D)ᴴ)
      = (physEmb (F := F) (m := m) (d := d) D * (physEmb (F := F) (m := m) (d := d) D)ᴴ)
        * aOp (aOp (aOp X)) := by
  rw [← Matrix.mul_assoc, aOp_mul_physEmb, Matrix.mul_assoc, Matrix.mul_assoc,
    physEmb_conjTranspose_mul_aOp]

/-- **And it is a projection.** -/
theorem physEmbProj_idem :
    (physEmb (F := F) (m := m) (d := d) D * (physEmb (F := F) (m := m) (d := d) D)ᴴ)
        * (physEmb (F := F) (m := m) (d := d) D * (physEmb (F := F) (m := m) (d := d) D)ᴴ)
      = physEmb (F := F) (m := m) (d := d) D * (physEmb (F := F) (m := m) (d := d) D)ᴴ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (physEmb D), physEmb_isometry, Matrix.one_mul]

end Embed

section Kron

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

omit [Algebra (ZMod 2) F] in
/-- **The two parties' embeddings together, pointwise**: each party's pair amplitude and padding
weight, times the strategy's amplitude on the two first registers. -/
theorem physEmb_kron_mulVec_apply (ψ : dA × dB → ℂ)
    (pA : ((dA × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m)
    (pB : ((dB × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) :
    ((physEmb (F := F) (m := m) (d := d) dA ⊗ₖ physEmb (F := F) (m := m) (d := d) dB) *ᵥ ψ)
        (pA, pB)
      = epr (F := F) (n := Fin m → Bool) (pA.1.1.2, pA.2) * padWeight pA.1.2
        * (epr (F := F) (n := Fin m → Bool) (pB.1.1.2, pB.2) * padWeight pB.1.2)
        * ψ (pA.1.1.1, pB.1.1.1) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [kroneckerMap_apply, physEmb_apply, ite_mul, mul_ite, Finset.sum_ite_eq]

/-- **The two parties' embeddings together are an isometry.** -/
theorem physEmb_kron_isometry :
    (physEmb (F := F) (m := m) (d := d) dA ⊗ₖ physEmb (F := F) (m := m) (d := d) dB)ᴴ
        * (physEmb (F := F) (m := m) (d := d) dA ⊗ₖ physEmb (F := F) (m := m) (d := d) dB)
      = 1 :=
  Introspection.isometricTensor_isometry _ _ physEmb_isometry physEmb_isometry

end Kron

section Mirror

open MIPRE.LIDT.Adapter

variable [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB] {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ψ : dA × dB → ℂ} {ε δ : ℝ}
  {hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)}
  {hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)} (hm : m ∣ Fintype.card F)

include hm in
/-- **The physical state is the image of the strategy's state under `phi_0 ⊗ phi_0`.** For the
`MirrorSimul` that `mirrorOfGlobalPairs` builds, the state on the two physical registers
`A A' Ea A''` and `B B' Eb B''` is `psi` with each party's own pair and padding appended locally:
the first cut's state is explicit (`padState_reindex_apply`), the appended pair enters as
`EPR_{B''B'}`, and `epr_symm` turns it round. -/
theorem physVec_mirrorOfGlobalPairs
    (P : GlobalPair ψ hprojA hprojB δ)
    (P' : GlobalPair (ψ ∘ Prod.swap) hprojB hprojA δ)
    (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    (mirrorOfGlobalPairs hm P P' hd hψ hfail hq).physVec
      = (physEmb dA ⊗ₖ physEmb dB) *ᵥ ψ := by
  -- stated on the explicit padding type, since `M.Ea` is only definitionally that type
  have h : ∀ (A : ((dA × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m)
      (B : ((dB × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m),
      reindexVec (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
          (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
          (padState (F := F) (m := m) (d := d) ψ) (A.1, ((B.1.1.1, A.2), B.1.2))
        * epr (F := F) (n := Fin m → Bool) (B.2, B.1.1.2)
      = ((physEmb dA ⊗ₖ physEmb dB) *ᵥ ψ) (A, B) := by
    intro A B
    rw [physEmb_kron_mulVec_apply, padState_reindex_apply, epr_symm B.2 B.1.1.2]
    ring
  funext p
  exact h p.1 p.2

include hm in
/-- **The same, in the vocabulary of isometric strategies**: the physical state is
`isometricState phi_0 phi_0 psi`. -/
theorem physVec_mirrorOfGlobalPairs_eq_isometricState
    (P : GlobalPair ψ hprojA hprojB δ)
    (P' : GlobalPair (ψ ∘ Prod.swap) hprojB hprojA δ)
    (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    (mirrorOfGlobalPairs hm P P' hd hψ hfail hq).physVec
      = Introspection.isometricState (physEmb dA) (physEmb dB) ψ :=
  physVec_mirrorOfGlobalPairs hm P P' hd hψ hfail hq

include hm in
/-- **`phi_A ⊗ phi_B |psi> = V_A ⊗ V_B |psi-hat>`.** The vector item 1 of `lem:qld-swap` is about
--- the physical state after the two swap unitaries --- is `psi` pushed forward by the two local
maps `V_A phi_0` and `V_B phi_0`, which are the paper's `phi_A` and `phi_B`. -/
theorem physSwap_mulVec_physVec_mirrorOfGlobalPairs
    (P : GlobalPair ψ hprojA hprojB δ)
    (P' : GlobalPair (ψ ∘ Prod.swap) hprojB hprojA δ)
    (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    (mirrorOfGlobalPairs hm P P' hd hψ hfail hq).physSwap
        *ᵥ (mirrorOfGlobalPairs hm P P' hd hψ hfail hq).physVec
      = (((mirrorOfGlobalPairs hm P P' hd hψ hfail hq).aliceSwap * physEmb dA)
          ⊗ₖ ((mirrorOfGlobalPairs hm P P' hd hψ hfail hq).bobSwap * physEmb dB)) *ᵥ ψ := by
  rw [MirrorSimul.physSwap, physVec_mirrorOfGlobalPairs]
  exact aOp_mul_bOp_mulVec_kronecker _ _ _ _ _

end Mirror

end MIPRE.QLD

end
