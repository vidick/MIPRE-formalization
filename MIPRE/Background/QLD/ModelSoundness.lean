/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Soundness
public import MIPRE.Foundations.BlockOrder
public import MIPRE.Foundations.Introspection.RegisterModel
public import MIPRE.Foundations.POVMDomination
public import MIPRE.Foundations.TensorExpand

@[expose] public section

/-!
# The Pauli basis test in a bipartite model

Phase 4 of `planning/mipco-track.md`. Introspection's soundness uses one fact about the Pauli
basis test, its soundness `thm:qld` (`MIPRE.QLD.qld_soundness`), and uses it only through its
conclusion: local isometries into the EPR register and an ancilla, the state carried near
`|EPR⟩ ⊗ |aux⟩`, and each player's Pauli measurements carried near the honest ones. This file
states that conclusion for a bipartite model, and takes the theorem as a hypothesis on the model
(`QLD.SoundIn ω M`), in the exact shape of `exists_le_qldErr` and at its error `qldErr`:

* **the ancilla** is a bipartite model `N` on a Hilbert space of `Type`, with ordered, proper
  algebras (`QLD.AncillaModel`), in place of the ancilla spaces `H_A`, `H_B` and the state
  `|aux⟩`;
* **the local isometries** are one local isometry of models (`BipartiteModel.LocalIsometry`) from
  `M` into `N` with the EPR register `Anc F m` adjoined (`BipartiteModel.reg`), in place of
  `V_A ⊗ V_B`; the players' operators move by its homomorphisms, as `X ↦ V_A X V_Aᴴ` does;
* **the errors** are the distance of the transported state to the state of the register model,
  and each player's summed squared state norms of the transported Pauli measurements minus the
  honest projectors `smulKron 1 (proj (weylOf W) h)` (`QLD.Extraction`);
* **the value model** `ω` dominates the POVM strategies of the ancilla model
  (`ValueModel.DominatesPOVM`): the strategy introspection extracts lives there, and its value
  has to count in `ω`.

**Its tensor-product instance** (`QLD.soundIn_tensor`) is `exists_le_qldErr`: the ancilla is the
tensor-product model of `|aux⟩`, the local isometry is `V_A ⊗ V_B` followed by the reading of the
flat state `registerState aux = expVec (registerEPR _) aux` as the register model
(`BipartiteModel.tensorUnexpand`), and `val*` dominates the POVM strategies of a tensor-product
model (`ValueModel.tensor_dominatesPOVM`). **Its commuting-operator form** (`QLD.SoundCo`: the
test is sound in the model of every commuting-operator strategy, with `ω_co`) is the hypothesis on
the Pauli basis test of `MIPRE.mipco_eq_core_of_stages`, and Phase 5 of the plan.

The constants of `thm:qld` in closed form (`exists_qldErr_le`) are a fact about the function
`qldErr` alone, so the hypothesis at `qldErr` gives the introspection compiler's constants in any
model.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix Weyl BipartiteModel
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The ancilla -/

/-- **An ancilla model**: a bipartite model on a Hilbert space of `Type`, with ordered, proper
algebras and a unit state, packed with its algebras. -/
structure AncillaModel where
  /-- The algebra represented on the Hilbert space. -/
  𝒞 : Type
  /-- The first player's algebra. -/
  𝒜 : Type
  /-- The second player's algebra. -/
  ℬ : Type
  [instRing𝒞 : Ring 𝒞]
  [instStarRing𝒞 : StarRing 𝒞]
  [instAlgebra𝒞 : Algebra ℂ 𝒞]
  [instRing𝒜 : Ring 𝒜]
  [instStarRing𝒜 : StarRing 𝒜]
  [instAlgebra𝒜 : Algebra ℂ 𝒜]
  [instPartialOrder𝒜 : PartialOrder 𝒜]
  [instStarOrderedRing𝒜 : StarOrderedRing 𝒜]
  [instStarProper𝒜 : StarProper 𝒜]
  [instRingℬ : Ring ℬ]
  [instStarRingℬ : StarRing ℬ]
  [instAlgebraℬ : Algebra ℂ ℬ]
  [instPartialOrderℬ : PartialOrder ℬ]
  [instStarOrderedRingℬ : StarOrderedRing ℬ]
  [instStarProperℬ : StarProper ℬ]
  /-- The model. -/
  N : BipartiteModel.{0} 𝒞 𝒜 ℬ
  /-- Its state is a unit vector. -/
  unit : ‖N.ψ‖ = 1

attribute [instance] AncillaModel.instRing𝒞 AncillaModel.instStarRing𝒞 AncillaModel.instAlgebra𝒞
  AncillaModel.instRing𝒜 AncillaModel.instStarRing𝒜 AncillaModel.instAlgebra𝒜
  AncillaModel.instPartialOrder𝒜 AncillaModel.instStarOrderedRing𝒜 AncillaModel.instStarProper𝒜
  AncillaModel.instRingℬ AncillaModel.instStarRingℬ AncillaModel.instAlgebraℬ
  AncillaModel.instPartialOrderℬ AncillaModel.instStarOrderedRingℬ AncillaModel.instStarProperℬ

/-! ## The conclusion of the Pauli basis test in a model -/

section Extraction

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- **The conclusion of the Pauli basis test** for a projective strategy `S` in the model `M`, at
error `δ`: an ancilla model `N` and a local isometry of `M` into `N` with the EPR register
`Anc F m` adjoined, carrying the state of `M` within `δ` of the state of the register model, and
carrying each player's coarse `(Pauli, W)` measurement within `δ` of the honest projectors on the
player's register, in summed squared state norm. -/
structure Extraction (M : BipartiteModel 𝒞 𝒜 ℬ) (hm : m ∣ Fintype.card F)
    (S : M.ProjStrat (qldGame (d := d) hm)) (δ : ℝ) where
  /-- The ancilla model. -/
  N : AncillaModel
  /-- The local isometry into the ancilla model with the EPR register adjoined. -/
  Φ : LocalIsometry M (N.N.reg (Anc F m))
  /-- The transported state is near `|EPR⟩ ⊗ ψ_N`. -/
  state_error : ‖Φ.W M.ψ - (N.N.reg (Anc F m)).ψ‖ ≤ δ
  /-- The first player's transported Pauli measurements are near the honest ones. -/
  alice_error : ∀ W : Bas, ∑ h : Anc F m, (N.N.reg (Anc F m)).stateSqNorm
    (Φ.ΦA (((S.PA (.pauli W)).map rdPauliVec).op h) - smulKron 1 (proj (weylOf W) h)) ≤ δ
  /-- The second player's transported Pauli measurements are near the honest ones. -/
  bob_error : ∀ W : Bas, ∑ h : Anc F m, (N.N.reg (Anc F m)).swap.stateSqNorm
    (Φ.ΦB (((S.PB (.pauli W)).map rdPauliVec).op h) - smulKron 1 (proj (weylOf W) h)) ≤ δ

/-- Increasing the error bound keeps the extraction. -/
def Extraction.mono {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {S : M.ProjStrat (qldGame (d := d) hm)} {δ δ' : ℝ} (E : Extraction M hm S δ) (h : δ ≤ δ') :
    Extraction M hm S δ' where
  N := E.N
  Φ := E.Φ
  state_error := E.state_error.trans h
  alice_error W := (E.alice_error W).trans h
  bob_error W := (E.bob_error W).trans h

end Extraction

/-! ## Soundness in a model -/

/-- **The Pauli basis test is sound in the bipartite model `M`** (`def:qld-sound-in`), with the
value model `ω`, in the shape of `exists_le_qldErr`: for every admissible `(q, m, d)`, a
projective strategy in `M` failing the test with probability at most `ε` has an extraction at
error `qldErr ε m d q` whose ancilla model `ω` dominates. -/
def SoundIn {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
    [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (ω : ValueModel) (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]
    (hm : m ∣ Fintype.card F), 1 ≤ d →
    ∀ (S : M.ProjStrat (qldGame (d := d) hm)) {ε : ℝ}, 0 ≤ ε → 1 - S.value ≤ ε →
      ∃ E : Extraction M hm S (qldErr ε m d (Fintype.card F)), ω.DominatesPOVM E.N.N

/-! ## The tensor-product instance -/

section Tensor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m] {HA HB : Type} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- The tensor-product model of a unit vector, as an ancilla model. -/
def tensorAncilla (aux : HA × HB → ℂ) (haux : ‖evec aux‖ = 1) : AncillaModel where
  𝒞 := Matrix (HA × HB) (HA × HB) ℂ
  𝒜 := Matrix HA HA ℂ
  ℬ := Matrix HB HB ℂ
  N := BipartiteModel.tensor aux
  unit := haux

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- The local isometry of the tensor-product instance: `V_A ⊗ V_B`, followed by the reading of the
flat register state as the register model. -/
def tensorPhi (ψ : dA × dB → ℂ) (aux : HA × HB → ℂ) (VA : Matrix (Anc F m × HA) dA ℂ)
    (VB : Matrix (Anc F m × HB) dB ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1) :
    LocalIsometry (BipartiteModel.tensor ψ) ((BipartiteModel.tensor aux).reg (Anc F m)) :=
  (tensorUnexpand aux (Introspection.registerEPR (Anc F m))).comp
    (tensorIsometry ψ (Introspection.registerState (Anc F m) aux) VA VB hA hB)

omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
theorem tensorPhi_W_ψ (ψ : dA × dB → ℂ) (aux : HA × HB → ℂ) (VA : Matrix (Anc F m × HA) dA ℂ)
    (VB : Matrix (Anc F m × HB) dB ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1) :
    ‖(tensorPhi ψ aux VA VB hA hB).W (BipartiteModel.tensor ψ).ψ -
        ((BipartiteModel.tensor aux).reg (Anc F m)).ψ‖ =
      ‖evec (Introspection.isometricState VA VB ψ - Introspection.registerState (Anc F m) aux)‖ := by
  rw [← tensorUnexpand_W_ψ aux (Introspection.registerEPR (Anc F m))]
  show ‖(tensorUnexpand aux _).W ((tensorIsometry ψ _ VA VB hA hB).W (BipartiteModel.tensor ψ).ψ) -
    (tensorUnexpand aux _).W (BipartiteModel.tensor (expVec _ aux)).ψ‖ = _
  rw [← map_sub, LinearIsometry.norm_map]
  rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The first player's error of the tensor-product instance is the matrix error. -/
theorem tensorPhi_alice (ψ : dA × dB → ℂ) (aux : HA × HB → ℂ) (VA : Matrix (Anc F m × HA) dA ℂ)
    (VB : Matrix (Anc F m × HB) dB ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1)
    (P : Matrix dA dA ℂ) (Q : Matrix (Anc F m) (Anc F m) ℂ) :
    ((BipartiteModel.tensor aux).reg (Anc F m)).stateSqNorm
        ((tensorPhi ψ aux VA VB hA hB).ΦA P - smulKron 1 Q) =
      snorm (Introspection.registerState (Anc F m) aux)
        (aOp (Introspection.isometricImage VA P - aOp Q)) ^ 2 := by
  have hX : (tensorPhi ψ aux VA VB hA hB).ΦA P - smulKron 1 Q =
      (tensorUnexpand aux (Introspection.registerEPR (Anc F m))).ΦA
        (Introspection.isometricImage VA P - aOp Q) := by
    rw [map_sub, tensorUnexpand_ΦA, tensorUnexpand_ΦA, aOp, compSymmHom_kronecker_one]
    rfl
  rw [hX, LocalIsometry.stateSqNorm_of_W_ψ (tensorUnexpand_W_ψ _ _)]
  rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The second player's error of the tensor-product instance is the matrix error. -/
theorem tensorPhi_bob (ψ : dA × dB → ℂ) (aux : HA × HB → ℂ) (VA : Matrix (Anc F m × HA) dA ℂ)
    (VB : Matrix (Anc F m × HB) dB ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1)
    (P : Matrix dB dB ℂ) (Q : Matrix (Anc F m) (Anc F m) ℂ) :
    ((BipartiteModel.tensor aux).reg (Anc F m)).swap.stateSqNorm
        ((tensorPhi ψ aux VA VB hA hB).ΦB P - smulKron 1 Q) =
      snorm (Introspection.registerState (Anc F m) aux)
        (bOp (Introspection.isometricImage VB P - aOp Q)) ^ 2 := by
  have hY : (tensorPhi ψ aux VA VB hA hB).ΦB P - smulKron 1 Q =
      (tensorUnexpand aux (Introspection.registerEPR (Anc F m))).ΦB
        (Introspection.isometricImage VB P - aOp Q) := by
    rw [map_sub, tensorUnexpand_ΦB, tensorUnexpand_ΦB, aOp, compSymmHom_kronecker_one]
    rfl
  rw [hY, LocalIsometry.swap_stateSqNorm_of_W_ψ (tensorUnexpand_W_ψ _ _)]
  rfl

end Tensor

/-- **The Pauli basis test is sound in the tensor-product model** of every state, with `val*`:
`exists_le_qldErr`, read in the model. -/
theorem soundIn_tensor {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (ψ : dA × dB → ℂ) : SoundIn .tensor (BipartiteModel.tensor ψ) := by
  intro F _ _ _ _ m d _ hm hd S ε hε hS
  have hψ : star ψ ⬝ᵥ ψ = 1 := star_dotProduct_self_eq_one S.ψ_unit
  have hfail : 1 - povmValue (qldGame hm) ψ (fun q => (S.PA q).toPOVM)
      (fun q => (S.PB q).toPOVM) ≤ ε := by
    rw [povmValue_eq_tensor]
    exact hS
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, aux, hA, hB, haux, h1, h2⟩ :=
    exists_le_qldErr hm hd hψ (fun q => (S.PA q).toPOVM) (fun q => (S.PB q).toPOVM) hε hfail
  have hmapA : ∀ q h, ((S.PA q).map rdPauliVec).op h =
      ((((S.PA q).toPOVM).map rdPauliVec).mats h).val := fun q h => by
    rw [← POVM.toIn_op, POVM.toIn_map, POVMIn.toPOVM_toIn]
  have hmapB : ∀ q h, ((S.PB q).map rdPauliVec).op h =
      ((((S.PB q).toPOVM).map rdPauliVec).mats h).val := fun q h => by
    rw [← POVM.toIn_op, POVM.toIn_map, POVMIn.toPOVM_toIn]
  exact ⟨⟨tensorAncilla aux haux, tensorPhi ψ aux VA VB hA hB,
    (tensorPhi_W_ψ ψ aux VA VB hA hB).trans_le h1,
    fun W => le_of_eq_of_le (Finset.sum_congr rfl fun h _ => by
      rw [hmapA]; exact tensorPhi_alice ψ aux VA VB hA hB _ _) (h2 W).1,
    fun W => le_of_eq_of_le (Finset.sum_congr rfl fun h _ => by
      rw [hmapB]; exact tensorPhi_bob ψ aux VA VB hA hB _ _) (h2 W).2⟩,
    ValueModel.tensor_dominatesPOVM aux (star_dotProduct_self_eq_one haux)⟩

/-! ## The commuting-operator model -/

/-- **The Pauli basis test is sound in the commuting-operator model** (`def:qld-sound-co`): in the
model of every commuting-operator strategy, with `ω_co`. This is Phase 5 of
`planning/mipco-track.md`, and the hypothesis on the Pauli basis test of
`MIPRE.mipco_eq_core_of_stages`. -/
def SoundCo : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (S : CommutingOperatorStrategy X Y A B), SoundIn .commuting S.toModel

end MIPRE.QLD

end
