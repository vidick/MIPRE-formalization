/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Soundness
import MIPRE.Foundations.WeylBinary

/-!
# `cor:qld-binary`: `thm:qld` on qubits

`thm:qld` (`qld_soundness`) self-tests the qudit register `(C^q)^{⊗ M}`, `M = 2^m`, indexed by
`Anc F m = F_q^M`: its honest measurements are the generalized Pauli projectors `tau^W_h` over
`F_q`. Introspection does not consume it in that form. The binary introspection game
(`BinaryComplete.game`) samples its questions over `F_2`, its register is
`F_2^{M × t} = ((Fin m → Bool) × Fin t) → ZMod 2` (`BinaryComplete.Seed m t`), and the honest
readouts its soundness theorem names (`TypedEstimates.quantumValue_ge_of_valid_isometric_images`)
are the qubit Pauli readouts over `ZMod 2`: `Honest.pauliXReadout` and the computational-basis
`readout some`. The paper's `cor:pauli-binary` (`ldt.tex`) is the bridge: `thm:pauli` with the
qudit register read as `M log q` qubits through a self-dual basis of `F_q` over `F_2`, with the same
error `delta_qld`. This file is that corollary, `qld_soundness_binary`.

## Why nothing is estimated

The relabelling `Weyl.binEquiv b : F_q^M ≃ F_2^{M × t}` of a basis `b` is a **bijection of basis
labels**, so the paper's isometry `(C^q)^{⊗ M} → (C^2)^{⊗ M t}` is a permutation of the
computational basis and conjugating by it is `Matrix.submatrix` (`lem:pauli-binary`,
`WeylBinary.lean`). Composing the isometries of `thm:qld` with it is therefore a reindexing of
their rows (`binFirst`), and every quantity of the corollary is, on the nose, the corresponding
quantity of `thm:qld`:

* an isometry with its register relabelled is an isometry (`relabelFirst_isometry`);
* the product state `|EPR> ⊗ |aux>` relabels with the register (`registerState_relabel`): the
  maximally entangled state is the normalized diagonal, and a simultaneous relabelling of its two
  halves preserves the diagonal (`registerEPR_equiv`). This is the `EPR` item of
  `lem:pauli-binary` (`epr_binEquiv`) for an arbitrary bijection;
* hence item 1's distance is unchanged (`norm_isometricState_relabelFirst_sub`), and so is each
  item-2 term, the honest operator relabelled with the register
  (`snorm_registerState_relabel_alice`, `_bob`): the state-dependent distance is invariant under
  relabelling vector and operator together (`snorm_comp_registerOp`);
* the qubit readouts *are* the relabelled qudit projectors. For `Z` both are computational-basis
  projectors and any bijection carries one to the other (`readout_some_binEquiv`). For `X` they are
  Fourier projectors, and the relabelling carries the `F_q` characters `(-1)^{tr(x · e)}` to the
  `F_2` ones `(-1)^{s · s'}` exactly when the basis is **self-dual** (`trDot_binEquiv`): this is the
  one place the hypothesis `IsSelfDualBasis b` is used (`pauliXReadout_binEquiv`, through
  `proj_wX_binEquiv`);
* the summed item-2 error over `s ∈ F_2^{M × t}` is the sum over `h ∈ F_q^M` reindexed by
  `h = binEquiv⁻¹ s` (`sum_snorm_sq_binFirst_alice_X` and its three siblings).

So the corollary holds with **the same** constants `a`, `b` as `qld_soundness`, which is what the
paper's one-line proof says.

The transport lemmas are stated for a general relabelling `e : I ≃ J` of the register first
(section `Relabel`) and specialized to `e = (binEquiv b).symm`; the ones about `binFirst` take the
measurement as an arbitrary family `P : Anc F m → Matrix d d ℂ`, so they transport any family of
operators indexed by the qudit register, and not only the coarse Pauli measurement.

## What differs from the paper's statement

* The paper's `sigma^W_u` for `u ∈ F_q^M` is the qubit Pauli at `(kappa(u_i))_i`; here the sum is
  indexed by the qubit label `s = binEquiv b u` itself, with the measurement read at
  `(binEquiv b).symm s`. It is the same sum.
* As in `qld_soundness`, the `(Pauli, W)` measurement is the coarse one, read as cube data through
  `rdPauliVec`: an answer of the wrong format reads as outcome `h = 0`. The introspection consumer
  sums only the valid full-register answers; at `h ≠ 0` the coarse operator is the valid one, at
  `h = 0` it also carries the malformed answers.
* The paper states the corollary for the field sizes it uses; here the basis is a hypothesis
  (`∀ t b, IsSelfDualBasis b → ...`). One exists whenever `[F : F_2]` is odd
  (`exists_binEquiv_pauli_binary`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.Introspection
open scoped Kronecker

/-! ## Relabelling the register -/

section Relabel

variable {I J D : Type*}

/-- **Relabel a party's register** along `e : I ≃ J`, the rest of the party's space a
spectator. -/
abbrev relabelParty (e : I ≃ J) (H : Type*) : I × H ≃ J × H := e.prodCongr (Equiv.refl H)

/-- **An isometry with its register relabelled**: the same matrix, its rows reindexed. -/
def relabelFirst {H : Type*} (e : I ≃ J) (V : Matrix (J × H) D ℂ) : Matrix (I × H) D ℂ :=
  V.submatrix (relabelParty e H) id

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
/-- **It is still an isometry**: the Gram matrix sums over the rows, which were only
relabelled. -/
theorem relabelFirst_isometry {H : Type*} [Fintype H] [DecidableEq D] (e : I ≃ J)
    {V : Matrix (J × H) D ℂ} (hV : Vᴴ * V = 1) : (relabelFirst e V)ᴴ * relabelFirst e V = 1 := by
  rw [relabelFirst, conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV, submatrix_id_id]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **Conjugating into the relabelled image is conjugating into the original one, relabelled.** -/
theorem isometricImage_relabelFirst {H : Type*} [Fintype D] (e : I ≃ J) (V : Matrix (J × H) D ℂ)
    (P : Matrix D D ℂ) :
    isometricImage (relabelFirst e V) P = registerOp (relabelParty e H) (isometricImage V P) :=
  rfl

variable {HA HB dA dB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
  [Fintype dA] [Fintype dB]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype HA] [DecidableEq HA]
  [Fintype HB] [DecidableEq HB] in
/-- **Pushing a state through the relabelled isometries** is pushing it through the original ones
and relabelling. -/
theorem isometricState_relabelFirst (e : I ≃ J) (VA : Matrix (J × HA) dA ℂ)
    (VB : Matrix (J × HB) dB ℂ) (ψ : dA × dB → ℂ) :
    isometricState (relabelFirst e VA) (relabelFirst e VB) ψ
      = isometricState VA VB ψ ∘ (relabelParty e HA).prodCongr (relabelParty e HB) :=
  rfl

omit [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] in
/-- **The register-first product state relabels with its register**: the maximally entangled
state is invariant under a simultaneous relabelling of its two halves (`registerEPR_equiv`), and
the auxiliary factor is a spectator. -/
theorem registerState_relabel (e : I ≃ J) (ξ : HA × HB → ℂ) :
    registerState I ξ
      = registerState J ξ ∘ (relabelParty e HA).prodCongr (relabelParty e HB) := by
  funext p
  show registerEPR I (p.1.1, p.2.1) * ξ (p.1.2, p.2.2)
    = registerEPR J (e p.1.1, e p.2.1) * ξ (p.1.2, p.2.2)
  rw [← congrFun (registerEPR_equiv e) (p.1.1, p.2.1)]
  rfl

/-- **Item 1's distance does not see the relabelling**: both states relabel together, and a
relabelling of basis vectors preserves the norm. -/
theorem norm_isometricState_relabelFirst_sub (e : I ≃ J) (VA : Matrix (J × HA) dA ℂ)
    (VB : Matrix (J × HB) dB ℂ) (ψ : dA × dB → ℂ) (ξ : HA × HB → ℂ) :
    ‖evec (isometricState (relabelFirst e VA) (relabelFirst e VB) ψ - registerState I ξ)‖
      = ‖evec (isometricState VA VB ψ - registerState J ξ)‖ := by
  rw [isometricState_relabelFirst, registerState_relabel e, ← Pi.sub_comp]
  exact norm_evec_comp_equiv _ _

/-- **Alice's item-2 error does not see the relabelling**, the honest operator relabelled with
the register: operator and state are relabelled together (`snorm_comp_registerOp`). -/
theorem snorm_registerState_relabel_alice (e : I ≃ J) (VA : Matrix (J × HA) dA ℂ)
    (P : Matrix dA dA ℂ) (τ : Matrix J J ℂ) (ξ : HA × HB → ℂ) :
    snorm (registerState I ξ)
        (aOp (isometricImage (relabelFirst e VA) P - aOp (registerOp e τ)))
      = snorm (registerState J ξ) (aOp (isometricImage VA P - aOp τ)) := by
  rw [isometricImage_relabelFirst, aOp_registerOp_prodCongr e (Equiv.refl HA), ← registerOp_sub,
    aOp_registerOp_prodCongr (relabelParty e HA) (relabelParty e HB), registerState_relabel e]
  exact snorm_comp_registerOp _ _ _

/-- **And Bob's.** -/
theorem snorm_registerState_relabel_bob (e : I ≃ J) (VB : Matrix (J × HB) dB ℂ)
    (Q : Matrix dB dB ℂ) (τ : Matrix J J ℂ) (ξ : HA × HB → ℂ) :
    snorm (registerState I ξ)
        (bOp (isometricImage (relabelFirst e VB) Q - aOp (registerOp e τ)))
      = snorm (registerState J ξ) (bOp (isometricImage VB Q - aOp τ)) := by
  rw [isometricImage_relabelFirst, aOp_registerOp_prodCongr e (Equiv.refl HB), ← registerOp_sub,
    bOp_registerOp_prodCongr (relabelParty e HA) (relabelParty e HB), registerState_relabel e]
  exact snorm_comp_registerOp _ _ _

end Relabel

/-! ## The qubit register

`F_2^{M × t}`, written out as `((Fin m → Bool) × Fin t) → ZMod 2` so that it is literally the
consumer's register `ι → F` at `ι = (Fin m → Bool) × Fin t`, `F = ZMod 2`. -/

section Binary

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m t : ℕ}
  (b : Module.Basis (Fin t) (ZMod 2) F)

/-- **Put the qubit register first**: an isometry into `F_q^M ⊗ H`, read as one into
`F_2^{M × t} ⊗ H` through the coordinate relabelling `binEquiv b` of the basis `b`. This is the
paper's composite of the `thm:pauli` isometry with the `lem:pauli-binary` one, which is a
permutation of basis vectors, so a reindexing of rows. -/
def binFirst {H D : Type*} (V : Matrix (Anc F m × H) D ℂ) :
    Matrix ((((Fin m → Bool) × Fin t) → ZMod 2) × H) D ℂ :=
  V.submatrix (fun p => ((binEquiv b).symm p.1, p.2)) id

omit [Fintype F] [DecidableEq F] in
theorem binFirst_eq_relabelFirst {H D : Type*} (V : Matrix (Anc F m × H) D ℂ) :
    binFirst b V = relabelFirst (binEquiv b).symm V := rfl

omit [DecidableEq F] in
/-- **It is still an isometry.** -/
theorem binFirst_isometry {H D : Type*} [Fintype H] [DecidableEq D]
    {V : Matrix (Anc F m × H) D ℂ} (hV : Vᴴ * V = 1) : (binFirst b V)ᴴ * binFirst b V = 1 :=
  relabelFirst_isometry _ hV

variable {HA HB dA dB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
  [Fintype dA] [Fintype dB]

omit [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] in
/-- **The product state on the qubit register is the one on the qudit register, relabelled**:
`|EPR_2>^{⊗ M t} ⊗ |aux>` is `|EPR_q>^{⊗ M} ⊗ |aux>` with `binEquiv b` applied to each party's
register. -/
theorem registerState_binEquiv (ξ : HA × HB → ℂ) :
    registerState (((Fin m → Bool) × Fin t) → ZMod 2) ξ
      = registerState (Anc F m) ξ
        ∘ (relabelParty (binEquiv b).symm HA).prodCongr (relabelParty (binEquiv b).symm HB) :=
  registerState_relabel _ ξ

/-- **Item 1's distance is the same on the qubit register.** -/
theorem norm_isometricState_binFirst_sub (VA : Matrix (Anc F m × HA) dA ℂ)
    (VB : Matrix (Anc F m × HB) dB ℂ) (ψ : dA × dB → ℂ) (ξ : HA × HB → ℂ) :
    ‖evec (isometricState (binFirst b VA) (binFirst b VB) ψ
        - registerState (((Fin m → Bool) × Fin t) → ZMod 2) ξ)‖
      = ‖evec (isometricState VA VB ψ - registerState (Anc F m) ξ)‖ :=
  norm_isometricState_relabelFirst_sub _ VA VB ψ ξ

/-- **The honest qubit `X` readout is the qudit `X` projector, relabelled.** This is where the
basis must be self-dual: the two Fourier projectors agree because the relabelling carries the
trace form to the dot product (`proj_wX_binEquiv`). -/
theorem pauliXReadout_binEquiv (hb : LowDegree.IsSelfDualBasis b)
    (s : ((Fin m → Bool) × Fin t) → ZMod 2) :
    Introspection.Honest.pauliXReadout (some s)
      = registerOp (binEquiv b).symm
          (proj (weylOf (F := F) (m := m) .X) ((binEquiv b).symm s)) := by
  rw [Introspection.Honest.pauliXReadout_some, show weylOf (F := F) (m := m) .X = wX from rfl,
    ← proj_wX_binEquiv hb ((binEquiv b).symm s), Equiv.apply_symm_apply]
  exact (registerOp_inv (binEquiv b) _).symm

/-- **The honest qubit `Z` readout is the qudit `Z` projector, relabelled.** Both are
computational-basis projectors (`proj_weylOf_Z`), so this needs no self-duality. -/
theorem readout_some_binEquiv (s : ((Fin m → Bool) × Fin t) → ZMod 2) :
    readout (some : (((Fin m → Bool) × Fin t) → ZMod 2) → Option _) (some s)
      = registerOp (binEquiv b).symm
          (proj (weylOf (F := F) (m := m) .Z) ((binEquiv b).symm s)) := by
  rw [proj_weylOf_Z]
  ext i j
  simp only [registerOp_apply, readout, diagonal_apply, Option.some.injEq,
    (binEquiv b).symm.injective.eq_iff]

/-- **Alice's `X` error is the same on the qubit register**: for any family `P` indexed by the
qudit register, the summed squared distance to the qubit readouts over `s ∈ F_2^{M × t}`, with
`P` read at `binEquiv⁻¹ s`, is the summed squared distance to the qudit projectors over
`h ∈ F_q^M`. -/
theorem sum_snorm_sq_binFirst_alice_X (hb : LowDegree.IsSelfDualBasis b)
    (VA : Matrix (Anc F m × HA) dA ℂ) (P : Anc F m → Matrix dA dA ℂ) (ξ : HA × HB → ℂ) :
    ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
        snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) ξ)
          (aOp (isometricImage (binFirst b VA) (P ((binEquiv b).symm s))
            - aOp (Introspection.Honest.pauliXReadout (some s)))) ^ 2
      = ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
          (aOp (isometricImage VA (P h) - aOp (proj (weylOf .X) h))) ^ 2 :=
  Fintype.sum_equiv (binEquiv b).symm _ _ fun s => by
    rw [pauliXReadout_binEquiv b hb, binFirst_eq_relabelFirst, snorm_registerState_relabel_alice]

/-- **Alice's `Z` error is the same on the qubit register.** -/
theorem sum_snorm_sq_binFirst_alice_Z (VA : Matrix (Anc F m × HA) dA ℂ)
    (P : Anc F m → Matrix dA dA ℂ) (ξ : HA × HB → ℂ) :
    ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
        snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) ξ)
          (aOp (isometricImage (binFirst b VA) (P ((binEquiv b).symm s))
            - aOp (readout (some : (((Fin m → Bool) × Fin t) → ZMod 2) → Option _) (some s)))) ^ 2
      = ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
          (aOp (isometricImage VA (P h) - aOp (proj (weylOf .Z) h))) ^ 2 :=
  Fintype.sum_equiv (binEquiv b).symm _ _ fun s => by
    rw [readout_some_binEquiv b, binFirst_eq_relabelFirst, snorm_registerState_relabel_alice]

/-- **Bob's `X` error is the same on the qubit register.** -/
theorem sum_snorm_sq_binFirst_bob_X (hb : LowDegree.IsSelfDualBasis b)
    (VB : Matrix (Anc F m × HB) dB ℂ) (Q : Anc F m → Matrix dB dB ℂ) (ξ : HA × HB → ℂ) :
    ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
        snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) ξ)
          (bOp (isometricImage (binFirst b VB) (Q ((binEquiv b).symm s))
            - aOp (Introspection.Honest.pauliXReadout (some s)))) ^ 2
      = ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
          (bOp (isometricImage VB (Q h) - aOp (proj (weylOf .X) h))) ^ 2 :=
  Fintype.sum_equiv (binEquiv b).symm _ _ fun s => by
    rw [pauliXReadout_binEquiv b hb, binFirst_eq_relabelFirst, snorm_registerState_relabel_bob]

/-- **Bob's `Z` error is the same on the qubit register.** -/
theorem sum_snorm_sq_binFirst_bob_Z (VB : Matrix (Anc F m × HB) dB ℂ)
    (Q : Anc F m → Matrix dB dB ℂ) (ξ : HA × HB → ℂ) :
    ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
        snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) ξ)
          (bOp (isometricImage (binFirst b VB) (Q ((binEquiv b).symm s))
            - aOp (readout (some : (((Fin m → Bool) × Fin t) → ZMod 2) → Option _) (some s)))) ^ 2
      = ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
          (bOp (isometricImage VB (Q h) - aOp (proj (weylOf .Z) h))) ^ 2 :=
  Fintype.sum_equiv (binEquiv b).symm _ _ fun s => by
    rw [readout_some_binEquiv b, binFirst_eq_relabelFirst, snorm_registerState_relabel_bob]

end Binary

/-! ## `cor:qld-binary` -/

/-- **`cor:qld-binary`: `thm:qld` on qubits** (the paper's `cor:pauli-binary`). With the universal
constants `a ≥ 1`, `0 < b < 1` of `qld_soundness`, for every admissible `(q, m, d)`, **every
self-dual basis** `β` of `F_q` over `F_2` (of size `t`) and every POVM strategy `(ψ, M_A, M_B)` of
the Pauli basis test failing with probability at most `ε`, there are local isometries
`V_A : C^{d_A} → (C^2)^{⊗ M t} ⊗ H_A`, `V_B : C^{d_B} → (C^2)^{⊗ M t} ⊗ H_B` (the qubit register
first) and a unit state `|aux>` on `H_A ⊗ H_B` such that, with
`δ = a (md)^a (ε^b + q^{-b} + 2^{-bmd})`,

1. `‖(V_A ⊗ V_B) |ψ> - |EPR_2>^{⊗ M t} ⊗ |aux>‖ ≤ δ`, and
2. for each basis `W ∈ {X, Z}` and each party, the strategy's own coarse `(Pauli, W)` measurement
   at `binEquiv⁻¹ s`, conjugated by the party's isometry, is `δ`-close to the honest qubit Pauli
   readout at `s` (`Honest.pauliXReadout` for `X`, `readout some` for `Z`) on that party's
   register, in the summed squared state-dependent distance over `s ∈ F_2^{M × t}` relative to
   `|EPR_2>^{⊗ M t} ⊗ |aux>`.

The isometries are `qld_soundness`'s with the register relabelled by `binEquiv β` (`binFirst`),
and the auxiliary state is the same. Every quantity is then equal to the corresponding one of
`qld_soundness` (`norm_isometricState_binFirst_sub`, `sum_snorm_sq_binFirst_alice_X`, ...), so
nothing is lost and the constants do not change. The basis is named `β` because `b` is the
exponent. -/
theorem qld_soundness_binary :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
        [NeZero m] (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ (t : ℕ) (β : Module.Basis (Fin t) (ZMod 2) F), LowDegree.IsSelfDualBasis β →
      ∀ {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
        (ψ : dA × dB → ℂ), star ψ ⬝ᵥ ψ = 1 →
      ∀ (MA : Question F m → POVM (Answer F m d) dA)
        (MB : Question F m → POVM (Answer F m d) dB) {ε : ℝ}, 0 ≤ ε →
        1 - povmValue (qldGame hm) ψ MA MB ≤ ε →
      ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB)
        (_ : DecidableEq HB) (VA : Matrix ((((Fin m → Bool) × Fin t) → ZMod 2) × HA) dA ℂ)
        (VB : Matrix ((((Fin m → Bool) × Fin t) → ZMod 2) × HB) dB ℂ) (aux : HA × HB → ℂ),
        VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ ‖evec aux‖ = 1 ∧
        ‖evec (isometricState VA VB ψ - registerState (((Fin m → Bool) × Fin t) → ZMod 2) aux)‖
          ≤ errShape a b ε m d (Fintype.card F) ∧
        ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
            snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) aux)
              (aOp (isometricImage VA
                  (((MA (.pauli .X)).map rdPauliVec).mats ((binEquiv β).symm s)).val
                - aOp (Introspection.Honest.pauliXReadout (some s)))) ^ 2
          ≤ errShape a b ε m d (Fintype.card F) ∧
        ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
            snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) aux)
              (aOp (isometricImage VA
                  (((MA (.pauli .Z)).map rdPauliVec).mats ((binEquiv β).symm s)).val
                - aOp (readout (some : (((Fin m → Bool) × Fin t) → ZMod 2) → Option _)
                    (some s)))) ^ 2
          ≤ errShape a b ε m d (Fintype.card F) ∧
        ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
            snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) aux)
              (bOp (isometricImage VB
                  (((MB (.pauli .X)).map rdPauliVec).mats ((binEquiv β).symm s)).val
                - aOp (Introspection.Honest.pauliXReadout (some s)))) ^ 2
          ≤ errShape a b ε m d (Fintype.card F) ∧
        ∑ s : ((Fin m → Bool) × Fin t) → ZMod 2,
            snorm (registerState (((Fin m → Bool) × Fin t) → ZMod 2) aux)
              (bOp (isometricImage VB
                  (((MB (.pauli .Z)).map rdPauliVec).mats ((binEquiv β).symm s)).val
                - aOp (readout (some : (((Fin m → Bool) × Fin t) → ZMod 2) → Option _)
                    (some s)))) ^ 2
          ≤ errShape a b ε m d (Fintype.card F) := by
  obtain ⟨a, b, ha, hb0, hb1, hqld⟩ := qld_soundness
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ m d _ hm hd t β hβ dA dB _ _ _ _ ψ hψ MA MB ε hε hfail
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, aux, hA, hB, haux, h1, h2⟩ :=
    hqld hm hd ψ hψ MA MB hε hfail
  refine ⟨HA, HB, i1, i2, i3, i4, binFirst β VA, binFirst β VB, aux, binFirst_isometry β hA,
    binFirst_isometry β hB, haux, ?_, ?_, ?_, ?_, ?_⟩
  · exact (norm_isometricState_binFirst_sub β VA VB ψ aux).trans_le h1
  · exact (sum_snorm_sq_binFirst_alice_X β hβ VA
      (fun h => (((MA (.pauli .X)).map rdPauliVec).mats h).val) aux).trans_le (h2 .X).1
  · exact (sum_snorm_sq_binFirst_alice_Z β VA
      (fun h => (((MA (.pauli .Z)).map rdPauliVec).mats h).val) aux).trans_le (h2 .Z).1
  · exact (sum_snorm_sq_binFirst_bob_X β hβ VB
      (fun h => (((MB (.pauli .X)).map rdPauliVec).mats h).val) aux).trans_le (h2 .X).2
  · exact (sum_snorm_sq_binFirst_bob_Z β VB
      (fun h => (((MB (.pauli .Z)).map rdPauliVec).mats h).val) aux).trans_le (h2 .Z).2

end MIPRE.QLD

end
