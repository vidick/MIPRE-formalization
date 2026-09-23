/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.SwapItemTwo
import MIPRE.Foundations.Introspection.RegisterEPR
import MIPRE.Foundations.Introspection.IsometricStrategy
import MIPRE.Foundations.Introspection.HidingBaseOperators
import MIPRE.Foundations.Introspection.Readout

/-!
# `thm:qld` in the register-first form its consumer reads

The swap isometry lemma (`MirrorSimul.swap_isometry`) concludes on the *physical* registers: each
party holds `H × Anc`, its half of the maximally entangled pair **last**, and the product state is
`outerUnVec (auxVec aux)`, with value `aux (x, y) * epr (a, b)` at `((x, a), (y, b))`. Its
consumer, the introspection soundness theorem
(`TypedEstimates.quantumValue_ge_of_valid_isometric_images`), reads the same objects with the
register **first**: isometries `VA : Matrix ((ι → F) × H) H₀ ℂ`, the state
`registerState (ι → F) ξ`, with value `registerEPR (a, b) * ξ (x, y)` at `((a, x), (b, y))`, and
the honest measurements as `aOp` of a readout on that register.

The two readings differ by one permutation of basis labels on each side, `Prod.swap`, and nothing
else: `registerEPR (ι → F)` *is* `Weyl.epr` (`registerEPR_eq_weyl`, by `rfl`). So this file does no
estimate. It records that every quantity the consumer asks about is, on the nose, the quantity the
swap lemma's side bounds after that permutation:

* `regFirst` moves the register to the front of an isometry's target, and keeps it an isometry
  (`regFirst_isometry`);
* the pushed-forward state and the product state move together (`isometricState_regFirst`,
  `registerState_eq_outerUnVec`), so the consumer's state distance is the physical one
  (`norm_isometricState_sub_registerState`);
* a conjugated measurement against an honest one on the register, in the state-dependent distance,
  is the physical conjugate against `Id ⊗ tau` (`snorm_registerState_alice`,
  `snorm_registerState_bob`). The honest operator changes spelling --- `aOp τ` in front, `bOp τ`
  behind --- because the register changed sides within the party;
* the product state is a unit vector exactly when `aux` is (`norm_evec_registerState`,
  `norm_evec_auxVec`), which turns item 1's `‖evec (auxVec aux)‖ = 1` into the consumer's
  `star ξ ⬝ᵥ ξ = 1`;
* a symmetric spectral projector moves across the pair on `registerState` too
  (`registerState_move`), the register-first form of `mulVec_auxVec_proj`. This is the step the
  paper's descent runs on: closeness to `tau^W` on one half is agreement with `tau^W` on the
  opposite half, and an agreement is a bilinear pairing, which is what survives a dilation;
* the honest readouts the consumer names are the spectral projectors of the two Weyl families
  (`proj_weylOf_X`, `proj_weylOf_Z`). Their projectivity is already
  `isPVM_proj (isWeylFamily_weylOf W)` (`Chain.lean`, `Expanded.lean`), and needs no new name.

Everything is stated for a general coordinate type `n` of the pair, `(n → F)`; the appendix's
ancilla `Anc F m` is the instance `n = Fin m → Bool`, being an `abbrev`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.Introspection
open scoped Kronecker

/-! ## Moving a register to the front -/

section Reorder

variable {H T D : Type*}

/-- **Put the register first.** An isometry into `H × T`, read as one into `T × H`: the same
matrix with its row labels swapped. -/
def regFirst (φ : Matrix (H × T) D ℂ) : Matrix (T × H) D ℂ := φ.submatrix Prod.swap id

theorem regFirst_apply (φ : Matrix (H × T) D ℂ) (t : T) (h : H) (d : D) :
    regFirst φ (t, h) d = φ (h, t) d := rfl

/-- **It is still an isometry**: the Gram matrix is a sum over the rows, and the rows were only
relabelled. -/
theorem regFirst_isometry [Fintype H] [Fintype T] [DecidableEq D] {φ : Matrix (H × T) D ℂ}
    (hφ : φᴴ * φ = 1) : (regFirst φ)ᴴ * regFirst φ = 1 := by
  rw [regFirst, conjTranspose_submatrix,
    show (Prod.swap : T × H → H × T) = Equiv.prodComm T H from rfl,
    Matrix.submatrix_mul_equiv, hφ, submatrix_id_id]

/-- **Conjugating into the register-first image is conjugating into the other one, relabelled.** -/
theorem isometricImage_regFirst [Fintype D] (φ : Matrix (H × T) D ℂ) (P : Matrix D D ℂ) :
    isometricImage (regFirst φ) P = registerOp (Equiv.prodComm T H) (φ * P * φᴴ) := rfl

/-- **An operator on the register, placed first, is the same operator placed last**, relabelled. -/
theorem aOp_eq_registerOp_bOp [DecidableEq H] (τ : Matrix T T ℂ) :
    (aOp τ : Matrix (T × H) (T × H) ℂ) = registerOp (Equiv.prodComm T H) (bOp τ) := by
  ext ⟨t, h⟩ ⟨t', h'⟩
  simp only [aOp, bOp, registerOp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    kroneckerMap_apply]
  exact mul_comm _ _

/-- **The consumer's local error operator is the physical one, relabelled.** -/
theorem isometricImage_regFirst_sub_aOp [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype D] (φ : Matrix (H × T) D ℂ) (P : Matrix D D ℂ) (τ : Matrix T T ℂ) :
    isometricImage (regFirst φ) P - (aOp τ : Matrix (T × H) (T × H) ℂ)
      = registerOp (Equiv.prodComm T H) (φ * P * φᴴ - bOp τ) := by
  rw [isometricImage_regFirst, aOp_eq_registerOp_bOp, registerOp_sub]

end Reorder

/-! ## The two cuts of the bipartite state -/

section Bipartite

variable {HA HB TA TB dA dB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
  [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB] [Fintype dA] [Fintype dB]

/-- The relabelling of both parties at once, as an equivalence. -/
abbrev regSwap (HA HB TA TB : Type*) : (TA × HA) × (TB × HB) ≃ (HA × TA) × (HB × TB) :=
  (Equiv.prodComm TA HA).prodCongr (Equiv.prodComm TB HB)

omit [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] [Fintype TA] [DecidableEq TA]
  [Fintype TB] [DecidableEq TB] in
/-- **Pushing a state through the register-first isometries** is pushing it through the others and
relabelling. -/
theorem isometricState_regFirst (φA : Matrix (HA × TA) dA ℂ) (φB : Matrix (HB × TB) dB ℂ)
    (ψ : dA × dB → ℂ) :
    isometricState (regFirst φA) (regFirst φB) ψ
      = ((φA ⊗ₖ φB) *ᵥ ψ) ∘ Prod.map Prod.swap Prod.swap := rfl

/-- **A relabelling of basis vectors carries the state-dependent distance**, the operator and the
vector relabelled together. -/
theorem snorm_comp_registerOp {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (v : J → ℂ) (X : Matrix J J ℂ) :
    snorm (v ∘ e) (registerOp e X) = snorm v X := by
  rw [snorm, snorm, registerOp_mulVec, norm_evec_comp_equiv]

/-- Alice's local operator, relabelled on her side, is the bipartite operator relabelled on both. -/
theorem aOp_registerOp_prodCongr {I J K L : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : I ≃ J) (f : K ≃ L) (X : Matrix J J ℂ) :
    (aOp (registerOp e X) : Matrix (I × K) (I × K) ℂ) = registerOp (e.prodCongr f) (aOp X) := by
  rw [aOp, aOp, registerOp_kronecker, registerOp_one]

/-- And Bob's. -/
theorem bOp_registerOp_prodCongr {I J K L : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : I ≃ J) (f : K ≃ L) (Y : Matrix L L ℂ) :
    (bOp (registerOp f Y) : Matrix (I × K) (I × K) ℂ) = registerOp (e.prodCongr f) (bOp Y) := by
  rw [bOp, bOp, registerOp_kronecker, registerOp_one]

/-- **Alice's error, on any state, reads the same on either cut.** -/
theorem snorm_comp_regSwap_alice (v : (HA × TA) × (HB × TB) → ℂ) (φA : Matrix (HA × TA) dA ℂ)
    (P : Matrix dA dA ℂ) (τ : Matrix TA TA ℂ) :
    snorm (v ∘ Prod.map Prod.swap Prod.swap)
        (aOp (isometricImage (regFirst φA) P - aOp τ) :
          Matrix ((TA × HA) × (TB × HB)) ((TA × HA) × (TB × HB)) ℂ)
      = snorm v (aOp (φA * P * φAᴴ - bOp τ)) := by
  rw [isometricImage_regFirst_sub_aOp,
    aOp_registerOp_prodCongr (Equiv.prodComm TA HA) (Equiv.prodComm TB HB)]
  exact snorm_comp_registerOp (regSwap HA HB TA TB) v _

/-- **And Bob's.** -/
theorem snorm_comp_regSwap_bob (v : (HA × TA) × (HB × TB) → ℂ) (φB : Matrix (HB × TB) dB ℂ)
    (Q : Matrix dB dB ℂ) (τ : Matrix TB TB ℂ) :
    snorm (v ∘ Prod.map Prod.swap Prod.swap)
        (bOp (isometricImage (regFirst φB) Q - aOp τ) :
          Matrix ((TA × HA) × (TB × HB)) ((TA × HA) × (TB × HB)) ℂ)
      = snorm v (bOp (φB * Q * φBᴴ - bOp τ)) := by
  rw [isometricImage_regFirst_sub_aOp,
    bOp_registerOp_prodCongr (Equiv.prodComm TA HA) (Equiv.prodComm TB HB)]
  exact snorm_comp_registerOp (regSwap HA HB TA TB) v _

end Bipartite

/-! ## The product state -/

section Product

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : Type*} [Fintype n] [DecidableEq n]
  {HA HB dA dB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
  [Fintype dA] [Fintype dB]

omit [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] in
/-- **The consumer's product state is the swap lemma's, relabelled.** Both are `aux ⊗ EPR`; they
differ only in which end of each party's register the half of the pair sits at. -/
theorem registerState_eq_outerUnVec (aux : HA × HB → ℂ) :
    registerState (n → F) aux
      = outerUnVec (auxVec (F := F) (n := n) aux) ∘ Prod.map Prod.swap Prod.swap := by
  funext p
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  show registerEPR (n → F) (a, b) * aux (x, y) = aux (x, y) * epr (F := F) (n := n) (a, b)
  rw [registerEPR_eq_weyl, mul_comm]

/-- **Item 1's distance, in the consumer's form.** With the register moved to the front of both
isometries, the pushed-forward state's distance to `registerState` is the physical distance to
the product state. -/
theorem norm_isometricState_sub_registerState (φA : Matrix (HA × (n → F)) dA ℂ)
    (φB : Matrix (HB × (n → F)) dB ℂ) (ψ : dA × dB → ℂ) (aux : HA × HB → ℂ) :
    ‖evec (isometricState (regFirst φA) (regFirst φB) ψ - registerState (n → F) aux)‖
      = ‖evec ((φA ⊗ₖ φB) *ᵥ ψ - outerUnVec (auxVec (F := F) (n := n) aux))‖ := by
  rw [isometricState_regFirst, registerState_eq_outerUnVec, ← Pi.sub_comp]
  exact norm_evec_comp_equiv (regSwap HA HB (n → F) (n → F)) _

/-- **Alice's item-2 error, in the consumer's form**: the conjugated measurement against an honest
operator on the register, on `registerState`, is the physical conjugate against `Id ⊗ τ` on the
physical product state. -/
theorem snorm_registerState_alice (φA : Matrix (HA × (n → F)) dA ℂ) (P : Matrix dA dA ℂ)
    (τ : Matrix (n → F) (n → F) ℂ) (aux : HA × HB → ℂ) :
    snorm (registerState (n → F) aux) (aOp (isometricImage (regFirst φA) P - aOp τ))
      = snorm (outerUnVec (auxVec (F := F) (n := n) aux)) (aOp (φA * P * φAᴴ - bOp τ)) := by
  rw [registerState_eq_outerUnVec]
  exact snorm_comp_regSwap_alice _ φA P τ

/-- **Bob's.** -/
theorem snorm_registerState_bob (φB : Matrix (HB × (n → F)) dB ℂ) (Q : Matrix dB dB ℂ)
    (τ : Matrix (n → F) (n → F) ℂ) (aux : HA × HB → ℂ) :
    snorm (registerState (n → F) aux) (bOp (isometricImage (regFirst φB) Q - aOp τ))
      = snorm (outerUnVec (auxVec (F := F) (n := n) aux)) (bOp (φB * Q * φBᴴ - bOp τ)) := by
  rw [registerState_eq_outerUnVec]
  exact snorm_comp_regSwap_bob _ φB Q τ

omit [Algebra (ZMod 2) F] in
/-- **The product state has the norm of its auxiliary factor**, the pair being a unit vector. -/
theorem norm_evec_registerState (aux : HA × HB → ℂ) :
    ‖evec (registerState (n → F) aux)‖ = ‖evec aux‖ := by
  rw [registerState, norm_evec_expVec, registerEPR_norm, one_mul]

/-- **So does the physical one.** -/
theorem norm_evec_outerUnVec_auxVec (aux : HA × HB → ℂ) :
    ‖evec (outerUnVec (auxVec (F := F) (n := n) aux))‖ = ‖evec aux‖ := by
  rw [← norm_evec_registerState (F := F) (n := n) aux, registerState_eq_outerUnVec]
  exact (norm_evec_comp_equiv (regSwap HA HB (n → F) (n → F)) _).symm

/-- **And so does item 1's**, which is how item 1's `‖evec (auxVec aux)‖ = 1` becomes the
consumer's unit hypothesis on `aux`. -/
theorem norm_evec_auxVec (aux : HA × HB → ℂ) :
    ‖evec (auxVec (F := F) (n := n) aux)‖ = ‖evec aux‖ := by
  rw [← norm_evec_outerUnVec, norm_evec_outerUnVec_auxVec]

/-- **Item 1's normalisation, in the consumer's form.** -/
theorem unit_of_norm_evec_auxVec {aux : HA × HB → ℂ}
    (h : ‖evec (auxVec (F := F) (n := n) aux)‖ = 1) : star aux ⬝ᵥ aux = 1 := by
  rw [norm_evec_auxVec] at h
  exact unit_of_norm_evec_eq_one h

/-- **A symmetric spectral projector moves across the pair on the register-first product state**:
`registerState`'s form of `mulVec_auxVec_proj`. On the pair itself this is `stateVec_epr_proj`;
the auxiliary factor is a spectator. -/
theorem registerState_move (aux : HA × HB → ℂ) {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) (e : n → F) :
    (aOp (aOp (proj w e)) :
        Matrix (((n → F) × HA) × ((n → F) × HB)) (((n → F) × HA) × ((n → F) × HB)) ℂ)
        *ᵥ registerState (n → F) aux
      = bOp (aOp (proj w e)) *ᵥ registerState (n → F) aux := by
  have hP : (aOp (proj w e) : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ)
        *ᵥ epr (F := F) (n := n) = bOp (proj w e) *ᵥ epr :=
    congrArg WithLp.ofLp (stateVec_epr_proj hw e)
  rw [registerState, aOp, aOp, bOp, aOp,
    show (1 : Matrix ((n → F) × HB) ((n → F) × HB) ℂ)
      = (1 : Matrix (n → F) (n → F) ℂ) ⊗ₖ (1 : Matrix HB HB ℂ) from one_kronecker_one.symm,
    show (1 : Matrix ((n → F) × HA) ((n → F) × HA) ℂ)
      = (1 : Matrix (n → F) (n → F) ℂ) ⊗ₖ (1 : Matrix HA HA ℂ) from one_kronecker_one.symm,
    mulVec_kron_kron_expVec, mulVec_kron_kron_expVec]
  exact congrArg (expVec · _) hP

end Product

/-! ## The honest readouts -/

section Readouts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}

/-- **The honest `X` readout the consumer names is the `X` family's spectral projector.** -/
theorem proj_weylOf_X (h : Anc F m) :
    proj (weylOf (F := F) (m := m) .X) h = Honest.pauliXReadout (some h) :=
  (Honest.pauliXReadout_some h).symm

/-- **The honest `Z` readout is the `Z` family's**, the computational-basis projector. -/
theorem proj_weylOf_Z (h : Anc F m) :
    proj (weylOf (F := F) (m := m) .Z) h
      = readout (some : Anc F m → Option (Anc F m)) (some h) := by
  rw [show weylOf (F := F) (m := m) .Z = wZ from rfl, proj_wZ, zProj, readout]
  congr 1
  funext i
  simp only [Option.some.injEq]

end Readouts

end MIPRE.QLD

end
