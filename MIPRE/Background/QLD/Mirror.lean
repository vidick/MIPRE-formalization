/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.ChainProbe
import MIPRE.Background.QLD.TwoPairs

/-!
# The second cut, and why it is a second `SimulPair`

`lem:qld-pauli-selfcons` and `lem:qld-swap` both compare *Alice's* exact Pauli object with *Bob's*.
Everything merged so far builds Alice's, from `SimulPair.SA`. This file supplies Bob's.

## Why `SB` is not it

The paper's `lem:qld-4-7` gives a pair measurement `S-hat` on `A A'` **and** one on `B B'`, with

* `(S-hat_{[eval_u = a]})_{A A'} ~ (M-hat^{(Point,W),u}_a)_{B A''}`,
* `(S-hat_{[eval_u = a]})_{B B'} ~ (M-hat^{(Point,W),u}_a)_{A B''}`,

and it is the second that Bob's swap unitary `V_B` conjugates by, because `V_B` acts on `B B' B''`.
`SimulPair.SB` is typed on `(dB x Anc F m) x EB`, and that `Anc F m` is the half of the *first*
pair that `hatVec` gives Bob --- the register the paper calls `A''`. So `SB` sits on `B A''`: it is
the second party of the *first* cut, a legitimate object (it is the symmetric equivalent
`M-hat_{A A'} ~ S-hat_{B A''}` of the first display) but not the one `V_B` is built from.

## What it is instead

`qld-commutation.tex` (`sec:expanding`, "Partitioning the registers, and symmetries") partitions
the six registers two ways --- `A A'` against `B A''`, and `B B'` against `A B''` --- and records
that every bipartite relation derived for one holds for the other with the registers changed. The
second partition is therefore not data of a new kind: it is the same kind as the first, so **the
mirror of a `SimulPair` is a `SimulPair`** --- at the swapped strategy, with the two players'
measurements exchanged, over the other reading of one physical state.

`MirrorSimul` is that pair of readings, and `toFirst` and `toSecond` are the two views. Every lemma
already proved about `SimulPair` --- `mVec`, `mTildeAnc`, `swapA`, `swapU_conj_mTildeAnc`,
`inconsistency_mTilde_pauli_le_of_win` --- then applies to Bob by instantiating it at `toSecond`,
with no mirror lemma to prove. That is the whole point of the shape.

## The state, and where the second pair goes

Each view carries the state its own cut sees: `Phi` on `(dA x Anc) x Ea` against
`(dB x Anc) x Eb`, which is exactly what stages 4a--4c produce and has only the pair `A' A''` in
it, and `Phi'` the same for `B' B''` with the players exchanged. The physical state is either of
them with the *other* pair appended, one half to each party, which is `expVec _ epr`; the field
`hmirror` says the two appendings agree. The appended halves are the outermost factor of each party
register, so a party register reads

```
((X x Anc) x E) x Anc
```

and `mTildeAnc`, which appends its Pauli register at the end of the register its pair measurement
lives on, lands on Alice's **physical** register `A A' Ea A''` with nothing to reindex --- and
`toSecond`'s lands on Bob's, `B B' Eb B''`. `physVec` is the state on those two, so `xSqNorm` of
the two exact Pauli objects against it is well formed. It is not well formed for any two objects
built inside one `SimulPair`, which is the concrete reason both cuts are needed at once.
-/

noncomputable section

universe u

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Appending a state to one party

The physical state is the first cut's state with the second entangled pair tensored on. Read along
the cut `mTilde` needs --- the one that has already moved `A''` to Alice --- **both** halves of
that pair are on Bob's side, so the appending is one-sided, and `expVec`, which puts one register
on each party, does not directly cover it. It does cover it with a trivial register on the first
party, which is all `sndExtVec` is. -/

section SndExt

variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]

/-- **A state with a further state appended to the second party.** -/
def sndExtVec (ψ : R × S → ℂ) (χ : C → ℂ) : R × (S × C) → ℂ :=
  fun p => ψ (p.1, p.2.1) * χ p.2.2

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C] in
/-- It is an `expVec` whose first party's register is trivial. -/
theorem sndExtVec_eq (ψ : R × S → ℂ) (χ : C → ℂ) :
    sndExtVec ψ χ
      = reindexVec (Equiv.prodPUnit R : R × Unit ≃ R) (Equiv.refl (S × C))
          (expVec ψ fun q : Unit × C => χ q.2) :=
  rfl

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C] in
/-- Padding an operator by the trivial register changes nothing. -/
theorem reindex_prodPUnit (X : Matrix R R ℂ) :
    Matrix.reindex (Equiv.prodPUnit R : R × Unit ≃ R) (Equiv.prodPUnit R : R × Unit ≃ R)
        (X ⊗ₖ (1 : Matrix Unit Unit ℂ)) = X := by
  ext r r'
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [DecidableEq C] in
/-- The trivially padded state is a unit vector when the appended one is. -/
theorem expVec_punit_unit {χ : C → ℂ} (hχ : star χ ⬝ᵥ χ = 1) :
    star (fun q : Unit × C => χ q.2) ⬝ᵥ (fun q : Unit × C => χ q.2) = 1 := by
  rw [← hχ, dotProduct, dotProduct, Fintype.sum_prod_type, Fintype.sum_unique]
  rfl

/-- **The appended state contributes its norm and nothing else.** A Born probability whose second
operator is the identity on the appended register is the one the original state gives. -/
theorem bornProb_sndExtVec {χ : C → ℂ} (hχ : star χ ⬝ᵥ χ = 1) (ψ : R × S → ℂ)
    (X : Matrix R R ℂ) (Y : Matrix S S ℂ) :
    bornProb (sndExtVec ψ χ) X (Y ⊗ₖ (1 : Matrix C C ℂ)) = bornProb ψ X Y := by
  have h := bornProb_reindex (Equiv.prodPUnit R : R × Unit ≃ R) (Equiv.refl (S × C))
    (expVec ψ fun q : Unit × C => χ q.2) (X ⊗ₖ (1 : Matrix Unit Unit ℂ))
    (Y ⊗ₖ (1 : Matrix C C ℂ))
  rw [reindex_prodPUnit,
    show Matrix.reindex (Equiv.refl (S × C)) (Equiv.refl (S × C)) (Y ⊗ₖ (1 : Matrix C C ℂ))
      = Y ⊗ₖ (1 : Matrix C C ℂ) from rfl] at h
  rw [sndExtVec_eq, h, bornProb_expVec_kron ψ _ Matrix.PosSemidef.one Matrix.PosSemidef.one,
    bornProb_one_one (expVec_punit_unit hχ), mul_one]

/-- A one-sided appending of a unit vector is a unit vector. -/
theorem sndExtVec_unit {ψ : R × S → ℂ} {χ : C → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hχ : star χ ⬝ᵥ χ = 1) : star (sndExtVec ψ χ) ⬝ᵥ sndExtVec ψ χ = 1 := by
  rw [sndExtVec_eq]
  exact reindexVec_unit (Equiv.prodPUnit R : R × Unit ≃ R) (Equiv.refl (S × C))
    (expVec_unit hψ (expVec_punit_unit hχ))

/-! ## Bob's physical register

Bob's own space and padding, with the appended pair's two halves put where the physical grouping
wants them: the half his own cut gave him beside his space, the half pulled back from Alice
outermost, which is where `mTilde` writes the Weyl operator. -/

variable {T T2 : Type*} [Fintype T] [DecidableEq T] [Fintype T2] [DecidableEq T2]

/-- The regrouping onto it. -/
def sndPairEquiv : ((S × C) × (T × T2)) ≃ (((S × T2) × C) × T) where
  toFun p := (((p.1.1, p.2.2), p.1.2), p.2.1)
  invFun q := ((q.1.1.1, q.1.2), (q.2, q.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
  [Fintype T2] [DecidableEq T2] in
/-- A product of the four factors is carried by it to the product in the physical order. -/
theorem reindex_sndPairEquiv (Y : Matrix S S ℂ) (Z : Matrix C C ℂ) (V : Matrix T T ℂ)
    (V2 : Matrix T2 T2 ℂ) :
    Matrix.reindex (sndPairEquiv (S := S) (C := C) (T := T) (T2 := T2))
        (sndPairEquiv (S := S) (C := C) (T := T) (T2 := T2)) ((Y ⊗ₖ Z) ⊗ₖ (V ⊗ₖ V2))
      = ((Y ⊗ₖ V2) ⊗ₖ Z) ⊗ₖ V := by
  ext p q
  obtain ⟨⟨⟨s1, u1⟩, c1⟩, v1⟩ := p
  obtain ⟨⟨⟨s2, u2⟩, c2⟩, v2⟩ := q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, sndPairEquiv, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply]
  ring

/-- **The one-sided appending, read on the second party's physical register.** -/
theorem bornProb_sndPair {χ : T × T2 → ℂ} (hχ : star χ ⬝ᵥ χ = 1) (ψ : R × (S × C) → ℂ)
    (X : Matrix R R ℂ) (Y : Matrix S S ℂ) (Z : Matrix C C ℂ) :
    bornProb (reindexVec (Equiv.refl R) sndPairEquiv (sndExtVec ψ χ)) X
        (((Y ⊗ₖ (1 : Matrix T2 T2 ℂ)) ⊗ₖ Z) ⊗ₖ (1 : Matrix T T ℂ))
      = bornProb ψ X (Y ⊗ₖ Z) := by
  have h := bornProb_reindex (Equiv.refl R) (sndPairEquiv (S := S) (C := C) (T := T) (T2 := T2))
    (sndExtVec ψ χ) X ((Y ⊗ₖ Z) ⊗ₖ (1 : Matrix (T × T2) (T × T2) ℂ))
  rw [bornProb_sndExtVec hχ] at h
  rw [show Matrix.reindex (Equiv.refl R) (Equiv.refl R) X = X from rfl,
    show (1 : Matrix (T × T2) (T × T2) ℂ)
      = (1 : Matrix T T ℂ) ⊗ₖ (1 : Matrix T2 T2 ℂ) from (Matrix.one_kronecker_one).symm,
    reindex_sndPairEquiv] at h
  exact h

end SndExt

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **One physical state, read along both of the paper's cuts.**

The fields come in two groups of the same shape, one per cut: the state, its reduction to the
expanded state, the two parties' pair measurements and the two consistencies of `lem:qld-4-7` and
their symmetric equivalents. The second group is the first with the players exchanged, which is
what `sec:expanding`'s symmetry paragraph licenses. `hmirror` is the only field that is not one of
those two groups: it says the two cuts read one state. -/
structure MirrorSimul (ψ : dA × dB → ℂ) (MA : Question F m → POVM (Answer F m d) dA)
    (MB : Question F m → POVM (Answer F m d) dB) (δ : ℝ) where
  /-- Alice's padding beyond the expansion. -/
  Ea : Type u
  [instFintypeEa : Fintype Ea]
  [instDecEqEa : DecidableEq Ea]
  /-- Bob's padding beyond the expansion. -/
  Eb : Type u
  [instFintypeEb : Fintype Eb]
  [instDecEqEb : DecidableEq Eb]
  /-- The state along the first cut, `A A' Ea` against `B A'' Eb`. -/
  Φ : ((dA × Anc F m) × Ea) × ((dB × Anc F m) × Eb) → ℂ
  Φ_unit : star Φ ⬝ᵥ Φ = 1
  Φ_reduced : ∀ (X : Matrix (dA × Anc F m) (dA × Anc F m) ℂ)
    (Y : Matrix (dB × Anc F m) (dB × Anc F m) ℂ),
    bornProb Φ (aOp X) (aOp Y) = bornProb (hatVec (F := F) (m := m) ψ) X Y
  /-- Alice's pair measurement, on `A A'`. -/
  SA : POVM (PolyPair F m d) ((dA × Anc F m) × Ea)
  SA_proj : IsPVM fun p => ((SA.mats p).val)
  /-- The first cut's second party's pair measurement, on `B A''`. -/
  SB : POVM (PolyPair F m d) ((dB × Anc F m) × Eb)
  SB_proj : IsPVM fun p => ((SB.mats p).val)
  consA : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ (fun u => evalMarg SA W u)
    (fun u => (hatPtPOVM MB W u).aOp) ≤ δ
  consB : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ (fun u => (hatPtPOVM MA W u).aOp)
    (fun u => evalMarg SB W u) ≤ δ
  /-- The state along the second cut, `B B' Eb` against `A B'' Ea`. -/
  Φ' : ((dB × Anc F m) × Eb) × ((dA × Anc F m) × Ea) → ℂ
  Φ'_unit : star Φ' ⬝ᵥ Φ' = 1
  Φ'_reduced : ∀ (X : Matrix (dB × Anc F m) (dB × Anc F m) ℂ)
    (Y : Matrix (dA × Anc F m) (dA × Anc F m) ℂ),
    bornProb Φ' (aOp X) (aOp Y) = bornProb (hatVec (F := F) (m := m) (ψ ∘ Prod.swap)) X Y
  /-- Bob's pair measurement, on `B B'` --- the one `V_B` is built from. -/
  SA' : POVM (PolyPair F m d) ((dB × Anc F m) × Eb)
  SA'_proj : IsPVM fun p => ((SA'.mats p).val)
  /-- The second cut's second party's pair measurement, on `A B''`. -/
  SB' : POVM (PolyPair F m d) ((dA × Anc F m) × Ea)
  SB'_proj : IsPVM fun p => ((SB'.mats p).val)
  consA' : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ' (fun u => evalMarg SA' W u)
    (fun u => (hatPtPOVM MA W u).aOp) ≤ δ
  consB' : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ' (fun u => (hatPtPOVM MB W u).aOp)
    (fun u => evalMarg SB' W u) ≤ δ
  /-- **The two cuts read one state.** Appending the pair the other cut carries --- one half to
  each party, which is what `expVec _ epr` does --- makes both into the same state on all six
  registers, up to the change of reading `mirrorVec`. -/
  hmirror : expVec Φ' (epr (F := F) (n := Fin m → Bool))
    = mirrorVec (expVec Φ (epr (F := F) (n := Fin m → Bool)))

attribute [instance] MirrorSimul.instFintypeEa MirrorSimul.instDecEqEa
  MirrorSimul.instFintypeEb MirrorSimul.instDecEqEb

namespace MirrorSimul

variable {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

variable (M : MirrorSimul ψ MA MB δ)

/- The same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-- **The first cut**, as a `SimulPair`: exactly the data stages 4a--4c deliver. -/
def toFirst : SimulPair ψ MA MB δ where
  EA := M.Ea
  EB := M.Eb
  Φ := M.Φ
  Φ_unit := M.Φ_unit
  Φ_reduced := M.Φ_reduced
  SA := M.SA
  SA_proj := M.SA_proj
  SB := M.SB
  SB_proj := M.SB_proj
  consA := M.consA
  consB := M.consB

/-- **The second cut**, as a `SimulPair` at the swapped strategy. Its `SA` is Bob's measurement on
`B B'`, so every construction the merged files make from `SimulPair.SA` --- `mTildeAnc` and `swapA`
above all --- is Bob's when instantiated here. -/
def toSecond : SimulPair (ψ ∘ Prod.swap) MB MA δ where
  EA := M.Eb
  EB := M.Ea
  Φ := M.Φ'
  Φ_unit := M.Φ'_unit
  Φ_reduced := M.Φ'_reduced
  SA := M.SA'
  SA_proj := M.SA'_proj
  SB := M.SB'
  SB_proj := M.SB'_proj
  consA := M.consA'
  consB := M.consB'

@[simp] theorem toFirst_Φ : M.toFirst.Φ = M.Φ := rfl

@[simp] theorem toSecond_Φ : M.toSecond.Φ = M.Φ' := rfl

@[simp] theorem toFirst_SA : M.toFirst.SA = M.SA := rfl

@[simp] theorem toSecond_SA : M.toSecond.SA = M.SA' := rfl

/-- **The mirror of a `MirrorSimul` is a `MirrorSimul`**, at the swapped strategy with the two
players' measurements exchanged and the two cuts exchanged. `toFirst` and `toSecond` give Bob's
objects as a `SimulPair`, which is enough for everything stated on one cut's state; this gives
Bob's objects on the *physical* state, which is what the chain's last displays compare. So every
lemma about the six-register cut becomes Bob's by instantiating here, with no mirror lemma to
prove --- the same economy `toSecond` buys one level down. The field saying the two cuts read one
state survives because `mirrorVec` is an involution (`mirrorVec_mirrorVec`). -/
def mirror : MirrorSimul (ψ ∘ Prod.swap) MB MA δ where
  Ea := M.Eb
  Eb := M.Ea
  Φ := M.Φ'
  Φ_unit := M.Φ'_unit
  Φ_reduced := M.Φ'_reduced
  SA := M.SA'
  SA_proj := M.SA'_proj
  SB := M.SB'
  SB_proj := M.SB'_proj
  consA := M.consA'
  consB := M.consB'
  Φ' := M.Φ
  Φ'_unit := M.Φ_unit
  Φ'_reduced := M.Φ_reduced
  SA' := M.SA
  SA'_proj := M.SA_proj
  SB' := M.SB
  SB'_proj := M.SB_proj
  consA' := M.consA
  consB' := M.consB
  hmirror := by rw [M.hmirror, mirrorVec_mirrorVec]

@[simp] theorem mirror_toFirst : M.mirror.toFirst = M.toSecond := rfl

@[simp] theorem mirror_toSecond : M.mirror.toSecond = M.toFirst := rfl

@[simp] theorem mirror_Φ : M.mirror.Φ = M.Φ' := rfl

@[simp] theorem mirror_SA : M.mirror.SA = M.SA' := rfl

/-! ## The physical state -/

/-- **The state on all six registers, grouped as the two parties physically hold them**: Alice's
`A A' Ea A''` against Bob's `B B' Eb B''`. It is the first cut's state with the second pair
appended and each party's far half pulled home. -/
def physVec : ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ :=
  pairSwapVec (expVec M.Φ (epr (F := F) (n := Fin m → Bool)))

theorem physVec_unit : star M.physVec ⬝ᵥ M.physVec = 1 :=
  pairSwapVec_unit (expVec_unit M.Φ_unit (epr_unit (F := F) (n := Fin m → Bool)))

/-- **The second cut lands on the same physical state**, with only the two parties written in the
other order. This is `hmirror` pushed through `pairSwapVec_mirrorVec`, and it is what lets a
statement proved on one cut be combined with one proved on the other. -/
theorem physVec_mirror :
    pairSwapVec (expVec M.Φ' (epr (F := F) (n := Fin m → Bool))) = M.physVec ∘ Prod.swap := by
  rw [M.hmirror]
  exact pairSwapVec_mirrorVec _

/-- **The mirror reads the same physical state**, with only the two parties written in the other
order. This is `physVec_mirror` in the form the instantiations use: whatever is proved about
`physVec` holds for Bob by being proved about `M.mirror.physVec`. -/
theorem mirror_physVec : M.mirror.physVec = M.physVec ∘ Prod.swap := M.physVec_mirror

/-- **A cut-1 expectation is unchanged by appending the other pair.** Operators that are the
identity on the appended halves see the state the `SimulPair` already describes: the pair
contributes its own norm and nothing else. This is `SimulPair.bornProb_padded`'s argument one level
up, and it is the bridge from everything proved about `Φ` to the physical state. -/
theorem bornProb_expPair (X : Matrix ((dA × Anc F m) × M.Ea) ((dA × Anc F m) × M.Ea) ℂ)
    (Y : Matrix ((dB × Anc F m) × M.Eb) ((dB × Anc F m) × M.Eb) ℂ) :
    bornProb (expVec M.Φ (epr (F := F) (n := Fin m → Bool))) (aOp X) (aOp Y)
      = bornProb M.Φ X Y := by
  show bornProb (expVec M.Φ _) (X ⊗ₖ 1) (Y ⊗ₖ 1) = _
  rw [bornProb_expVec_kron M.Φ _ Matrix.PosSemidef.one Matrix.PosSemidef.one,
    bornProb_one_one (epr_unit (F := F) (n := Fin m → Bool)), mul_one]

/-- **The physical state is the first cut's `mVec` with the appended pair, both halves on Bob's
side.** Along the cut `mTilde` needs, `A''` has already moved to Alice, so what the appending adds
is entirely Bob's: `B'` beside his own space and `B''` outermost. -/
theorem physVec_eq_sndPair :
    M.physVec = reindexVec (Equiv.refl _) sndPairEquiv
      (sndExtVec M.toFirst.mVec (epr (F := F) (n := Fin m → Bool))) :=
  rfl

/-- **Everything proved on the first cut's `mVec` reads on the physical state.** Bob's operator is
extended by the identity on both halves of the appended pair, and the pair contributes its own norm
and nothing else; Alice's needs no extension, being already on her physical register. This is the
bridge the assemblies of `lem:qld-pauli-selfcons` and `lem:qld-swap` run through, and its mirror
image --- by `physVec_mirror` --- does the same for Bob's side. -/
theorem bornProb_physVec (X : Matrix (((dA × Anc F m) × M.Ea) × Anc F m)
      (((dA × Anc F m) × M.Ea) × Anc F m) ℂ) (Y : Matrix dB dB ℂ) (Z : Matrix M.Eb M.Eb ℂ) :
    bornProb M.physVec X
        (((Y ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ)) ⊗ₖ Z) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      = bornProb M.toFirst.mVec X (Y ⊗ₖ Z) := by
  rw [M.physVec_eq_sndPair]
  exact bornProb_sndPair (epr_unit (F := F) (n := Fin m → Bool)) _ _ _ _

/-! ## Bob's objects, for free

Nothing below has a proof of its own: each is a merged lemma about `SimulPair` instantiated at
`toSecond`. They are stated because the typing is the point --- each of Bob's objects lands on the
second party of `physVec`, where Alice's lands on the first. -/

section Bob

/-- **Bob's exact Pauli measurement at an arbitrary probe**, on his physical register
`B B' Eb B''`. -/
def bobMTilde (W : Bas) (v : Anc F m) (a : F) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.toSecond.mTildeAnc W v a

/-- It is projective, by the lemma that says Alice's is. -/
theorem isPVM_bobMTilde (W : Bas) (v : Anc F m) : IsPVM (M.bobMTilde W v) :=
  M.toSecond.isPVM_mTildeAnc W v

/-- **Bob's swap unitary** `V_B`, on the same register. -/
def bobSwap : Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.toSecond.swapA

theorem bobSwap_mul_conjTranspose : M.bobSwap * M.bobSwapᴴ = 1 :=
  M.toSecond.swapA_mul_conjTranspose

theorem bobSwap_conjTranspose_mul : M.bobSwapᴴ * M.bobSwap = 1 :=
  M.toSecond.swapA_conjTranspose_mul

/-- **Display `eq:qld-unitary-6` for Bob**: his swap unitary strips the pair measurement off his
exact Pauli measurement, leaving the Weyl syndrome on `B''` alone. The paper says "an entirely
analogous calculation shows"; here it is the same calculation, at the other instance. -/
theorem bobSwap_conj_bobMTilde (W : Bas) (v : Anc F m) (a : F) :
    M.bobSwap * M.bobMTilde W v a * M.bobSwapᴴ = 1 ⊗ₖ syn (weylOf W) v a :=
  M.toSecond.swapU_conj_mTildeAnc W v a

/-- **Alice's exact Pauli measurement at an arbitrary probe**, on her physical register
`A A' Ea A''` --- named here only so that the two sit side by side. -/
def aliceMTilde (W : Bas) (v : Anc F m) (a : F) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.toFirst.mTildeAnc W v a

/-- **The two exact Pauli measurements lie on opposite sides of the physical cut.** The content is
the typing: this expression is well formed, and no expression comparing two objects built inside a
single `SimulPair` is. It is the left-hand side of `lem:qld-pauli-selfcons`. -/
def selfConsGap (W : Bas) (v : Anc F m) (a : F) : ℝ :=
  xSqNorm M.physVec (M.aliceMTilde W v a) (M.bobMTilde W v a)

end Bob

end MirrorSimul

end MIPRE.QLD

end
