/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.SelfCons
import MIPRE.Background.QLD.SwapEndgame

/-!
# Item 1 of `lem:qld-swap`, unconditional

`MIPRE/Background/QLD/SwapState.lean` proves item 1 of the swap isometry lemma *given its
hypothesis*: a unit state nearly invariant under both Weyl twirls on its two ancilla halves is
close to a product of an auxiliary state and a maximally entangled pair
(`exists_auxVec_close`). This file supplies the hypothesis, which is
`lem:qld-pauli-selfcons`.

The blueprint calls this "the missing edge", and says it is one rewriting: the twirl is by
definition the uniform average of the per-probe Weyl operators, so
`qform_bOp_twirl` turns the near-invariance into an average of per-probe expectations, and at
each probe that expectation is the two parties' exact Pauli observables agreeing. Three things
have to be said to make the rewriting go through.

* **The cut.** `endEquiv` regroups a four-fold product whose ancilla halves sit in the middle;
  the physical cut of a `MirrorSimul` puts each party's half of the pair it holds at the *end*,
  so `outerPairEquiv` is the regrouping this needs. It was written when it was clear which one
  the state actually has.
* **The conjugation.** `swapU_conj_wTilde_X` and `_Z` say the swap unitary strips the pair
  measurement off the exact Pauli observable exactly, leaving the honest Weyl operator; read
  backwards (`conj_inv_of_unitary`) that turns an expectation of the Weyl operator on the swapped
  state into an expectation of the two observables on the state itself.
* **The two involutions.** Each party's exact Pauli observable is self-adjoint and squares to
  one, so its cross-party deviation and its joint expectation determine each other exactly:
  `xSqNorm = 2 - 2 bornProb`, with no inequality.

What is *not* here is item 2, the longer half, which threads these steps into a statement about
the conjugated total Pauli measurement `V M^{(Pauli,W)}_h V†`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

section Outer

variable {A B T T' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']

/-- **The regrouping onto item 1's cut, for a four-fold product whose ancilla halves are
outermost.** `endEquiv` does the same for one whose ancilla halves sit in the middle; the
physical cut of a `MirrorSimul` puts each party's half of the pair it holds at the end. -/
def outerPairEquiv : (A × T) × (B × T') ≃ (A × B) × (T × T') where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The state, read along it. -/
def outerVec (χ : (A × T) × (B × T') → ℂ) : (A × B) × (T × T') → ℂ :=
  χ ∘ (outerPairEquiv (A := A) (B := B) (T := T) (T' := T')).symm

omit [DecidableEq A] [DecidableEq B] [DecidableEq T] [DecidableEq T'] in
/-- A regrouped unit vector is a unit vector. -/
theorem outerVec_unit {χ : (A × T) × (B × T') → ℂ} (hχ : star χ ⬝ᵥ χ = 1) :
    star (outerVec χ) ⬝ᵥ outerVec χ = 1 := by
  rw [← hχ]
  exact Equiv.sum_comp (outerPairEquiv (A := A) (B := B) (T := T) (T' := T')).symm
    fun p => star χ p * χ p

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
  [Fintype T'] [DecidableEq T'] in
/-- **The same operator, grouped the two ways.** -/
theorem reindex_outerPairEquiv (XA : Matrix A A ℂ) (XB : Matrix B B ℂ) (YA : Matrix T T ℂ)
    (YB : Matrix T' T' ℂ) :
    Matrix.reindex (outerPairEquiv (A := A) (B := B) (T := T) (T' := T'))
        (outerPairEquiv (A := A) (B := B) (T := T) (T' := T'))
        ((XA ⊗ₖ YA) ⊗ₖ (XB ⊗ₖ YB))
      = (XA ⊗ₖ XB) ⊗ₖ (YA ⊗ₖ YB) := by
  ext p q
  obtain ⟨⟨a, b⟩, t, t'⟩ := p
  obtain ⟨⟨a', b'⟩, s, s'⟩ := q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, outerPairEquiv,
    Equiv.coe_fn_symm_mk, kroneckerMap_apply]
  ring

omit [DecidableEq A] [DecidableEq B] [DecidableEq T] [DecidableEq T'] in
/-- **And so is the quadratic form.** -/
theorem qform_outerVec (χ : (A × T) × (B × T') → ℂ) (XA : Matrix A A ℂ) (XB : Matrix B B ℂ)
    (YA : Matrix T T ℂ) (YB : Matrix T' T' ℂ) :
    qform (outerVec χ) ((XA ⊗ₖ XB) ⊗ₖ (YA ⊗ₖ YB))
      = qform χ ((XA ⊗ₖ YA) ⊗ₖ (XB ⊗ₖ YB)) := by
  rw [qform, qform, outerVec, ← reindex_outerPairEquiv, qform_comp_equiv]

end Outer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

section Probe

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

set_option synthInstance.maxSize 1000

/-- **Display `eq:qld-unitary-6` for the observable, at the interface.** The swap unitary strips
the pair measurement off the exact Pauli observable, leaving the honest Weyl operator on the
party's half of the pair. -/
theorem SimulPair.swapA_conj_wTildeAt (P : SimulPair ψ MA MB δ) (W : Bas) (e : F)
    (v : Anc F m) :
    P.swapA * P.wTildeAt W e v * P.swapAᴴ = 1 ⊗ₖ weylOf W (e • v) := by
  cases W with
  | X => exact swapU_conj_wTilde_X P.SA_proj e v
  | Z => exact swapU_conj_wTilde_Z P.SA_proj e v

/-- The same at the unit scalar, which is the case the twirl reads. -/
theorem SimulPair.swapA_conj_wTildeAt_one (P : SimulPair ψ MA MB δ) (W : Bas) (v : Anc F m) :
    P.swapA * P.wTildeAt W 1 v * P.swapAᴴ = bOp (weylOf W v) := by
  rw [P.swapA_conj_wTildeAt W 1 v, one_smul]
  rfl

end Probe

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- Inverting a conjugation by a unitary. -/
theorem conj_inv_of_unitary {N : Type*} [Fintype N] [DecidableEq N] {V X Y : Matrix N N ℂ}
    (h1 : Vᴴ * V = 1) (h : V * X * Vᴴ = Y) : Vᴴ * (Y * V) = X := by
  rw [← h]
  rw [show Vᴴ * (V * X * Vᴴ * V) = (Vᴴ * V) * X * (Vᴴ * V) from by
    simp only [Matrix.mul_assoc], h1, Matrix.one_mul, Matrix.mul_one]

section Physical

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

set_option synthInstance.maxSize 1000

/-- **The constant `lem:qld-pauli-selfcons` carries**, named so that the swap isometry's
statements fit on a line. -/
def deltaSelfCons (δ ε : ℝ) (m d q : ℕ) : ℝ :=
  72 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε) + (m : ℝ) * d / q)

theorem deltaSelfCons_nonneg {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (m d q : ℕ) :
    0 ≤ deltaSelfCons δ ε m d q := by
  have h1 : (0 : ℝ) ≤ Real.sqrt (172 * ε) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (m : ℝ) * d / q := by positivity
  rw [deltaSelfCons]
  linarith

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **Alice's swap unitary** `V_A`, in her own spelling. -/
def aliceSwap :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.toFirst.swapA

theorem aliceSwap_conjTranspose_mul : M.aliceSwapᴴ * M.aliceSwap = 1 :=
  M.toFirst.swapA_conjTranspose_mul

theorem bobSwap_conjTranspose_mul' : M.bobSwapᴴ * M.bobSwap = 1 :=
  M.toSecond.swapA_conjTranspose_mul

/-- **Display `eq:qld-unitary-6` for Alice's observable**, in her own spelling. -/
theorem aliceSwap_conj_aliceWTilde (W : Bas) (v : Anc F m) :
    M.aliceSwap * M.aliceWTilde W 1 v * M.aliceSwapᴴ = bOp (weylOf W v) :=
  M.toFirst.swapA_conj_wTildeAt_one W v

/-- **And for Bob's.** -/
theorem bobSwap_conj_bobWTilde (W : Bas) (v : Anc F m) :
    M.bobSwap * M.bobWTilde W 1 v * M.bobSwapᴴ = bOp (weylOf W v) :=
  M.toSecond.swapA_conj_wTildeAt_one W v

/-- **The two swap unitaries together**, on the physical cut. -/
def physSwap :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp M.aliceSwap * bOp M.bobSwap

theorem physSwap_conjTranspose_mul : M.physSwapᴴ * M.physSwap = 1 := by
  rw [physSwap, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, M.aliceSwap_conjTranspose_mul,
    M.bobSwap_conjTranspose_mul', aOp_one, bOp_one, Matrix.one_mul]

/-- **The state item 1 concludes about**: the physical state after the two swap unitaries,
regrouped so that the two parties' halves of the pair sit together. -/
def endState :
    ((((dA × Anc F m) × M.Ea) × (((dB × Anc F m) × M.Eb))) × (Anc F m × Anc F m)) → ℂ :=
  outerVec (M.physSwap *ᵥ M.physVec)

theorem endState_unit : star M.endState ⬝ᵥ M.endState = 1 := by
  refine outerVec_unit ?_
  have h := dotProduct_mulVec_conj M.physSwap 1 M.physVec
  rw [Matrix.one_mulVec, Matrix.one_mul, M.physSwap_conjTranspose_mul, Matrix.one_mulVec] at h
  exact h.trans M.physVec_unit

set_option maxHeartbeats 4000000 in
/-- **The Weyl operator on the two halves of the pair, read on that state, is the two parties'
exact Pauli observables read on the physical state.** Conjugation by the swap unitaries carries
the one to the other exactly. -/
theorem qform_endState_weyl (W : Bas) (v : Anc F m) :
    qform M.endState (bOp (weylOf W v ⊗ₖ weylOf W v))
      = bornProb M.physVec (M.aliceWTilde W 1 v) (M.bobWTilde W 1 v) := by
  have hone : (bOp (weylOf W v ⊗ₖ weylOf W v)
        : Matrix ((((dA × Anc F m) × M.Ea) × (((dB × Anc F m) × M.Eb))) × (Anc F m × Anc F m))
          _ ℂ)
      = ((1 : Matrix (((dA × Anc F m) × M.Ea)) _ ℂ)
          ⊗ₖ (1 : Matrix (((dB × Anc F m) × M.Eb)) _ ℂ)) ⊗ₖ (weylOf W v ⊗ₖ weylOf W v) := by
    rw [Matrix.one_kronecker_one]
    rfl
  rw [hone, endState, qform_outerVec, ← aOp_mul_bOp_eq]
  have h := dotProduct_mulVec_conj M.physSwap
    ((aOp (bOp (weylOf W v)) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
        × (((dB × Anc F m) × M.Eb) × Anc F m)) _ ℂ) * bOp (bOp (weylOf W v))) M.physVec
  refine Eq.trans (congrArg Complex.re h) ?_
  show qform M.physVec (M.physSwapᴴ * (((aOp (bOp (weylOf W v))
      : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m)) _ ℂ)
    * bOp (bOp (weylOf W v))) * M.physSwap)) = _
  rw [physSwap, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, aOp_bOp_mul_aOp_bOp,
    conj_inv_of_unitary M.aliceSwap_conjTranspose_mul (M.aliceSwap_conj_aliceWTilde W v),
    conj_inv_of_unitary M.bobSwap_conjTranspose_mul' (M.bobSwap_conj_bobWTilde W v),
    ← bornProb_eq_qform]

/-- `lem:qld-pauli-selfcons`, at that name. -/
theorem snorm_sq_wTilde_le' {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (e : F) (v : Anc F m) :
    snorm M.physVec ((aOp (M.aliceWTilde W e v)
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        - bOp (M.bobWTilde W e v)) ^ 2
      ≤ deltaSelfCons δ ε m d (Fintype.card F) := by
  have h := M.snorm_sq_wTilde_le (hm := hm) hψ hfail hprojA hprojB hd W e v
  rw [deltaSelfCons]
  linarith

theorem aliceWTilde_conjTranspose (W : Bas) (e : F) (v : Anc F m) :
    (M.aliceWTilde W e v)ᴴ = M.aliceWTilde W e v :=
  M.toFirst.wTildeAt_conjTranspose W e v

theorem aliceWTilde_mul_self (W : Bas) (e : F) (v : Anc F m) :
    M.aliceWTilde W e v * M.aliceWTilde W e v = 1 :=
  M.toFirst.wTildeAt_mul_self W e v

theorem bobWTilde_conjTranspose (W : Bas) (e : F) (v : Anc F m) :
    (M.bobWTilde W e v)ᴴ = M.bobWTilde W e v :=
  M.toSecond.wTildeAt_conjTranspose W e v

theorem bobWTilde_mul_self (W : Bas) (e : F) (v : Anc F m) :
    M.bobWTilde W e v * M.bobWTilde W e v = 1 :=
  M.toSecond.wTildeAt_mul_self W e v

set_option maxHeartbeats 1000000 in
/-- **The two observables' agreement, as a Born probability.** Both are self-adjoint involutions,
so their cross-party deviation and their joint expectation determine each other. -/
theorem bornProb_wTilde_ge {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (e : F) (v : Anc F m) :
    1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
      ≤ bornProb M.physVec (M.aliceWTilde W e v) (M.bobWTilde W e v) := by
  have hx : xSqNorm M.physVec (M.aliceWTilde W e v) (M.bobWTilde W e v)
      = 2 - 2 * bornProb M.physVec (M.aliceWTilde W e v) (M.bobWTilde W e v) := by
    rw [xSqNorm_eq_expand M.physVec (M.aliceWTilde_conjTranspose W e v),
      stateSqNorm_eq_bornProb_one, normSq_stateVecB_eq_one_bornProb,
      M.aliceWTilde_conjTranspose W e v, M.bobWTilde_conjTranspose W e v,
      M.aliceWTilde_mul_self W e v, M.bobWTilde_mul_self W e v,
      bornProb_one_one M.physVec_unit]
    ring
  have hle : xSqNorm M.physVec (M.aliceWTilde W e v) (M.bobWTilde W e v)
      ≤ deltaSelfCons δ ε m d (Fintype.card F) := by
    rw [xSqNorm_eq_snorm_sq]
    exact M.snorm_sq_wTilde_le' (hm := hm) hψ hfail hprojA hprojB hd W e v
  linarith

set_option maxHeartbeats 1000000 in
/-- **The near-invariance item 1 asks for.** The twirl is by definition the uniform average of the
per-probe Weyl operators, and at each probe that average is the two parties' exact Pauli
observables agreeing. This is the edge the blueprint's dependency graph was missing. -/
theorem qform_endState_twirl_ge {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (W : Bas) :
    1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
      ≤ qform M.endState (bOp (twirl (weylOf W))) := by
  rw [qform_bOp_twirl]
  have hterm : ∀ v : Anc F m,
      1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
        ≤ qform M.endState (bOp (weylOf W v ⊗ₖ weylOf W v)) := by
    intro v
    rw [M.qform_endState_weyl W v]
    exact M.bornProb_wTilde_ge (hm := hm) hψ hfail hprojA hprojB hd W 1 v
  calc 1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
      = ∑ v : Anc F m, uniform (Anc F m) v
          * (1 - deltaSelfCons δ ε m d (Fintype.card F) / 2) := by
        rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
    _ ≤ ∑ v : Anc F m, uniform (Anc F m) v
          * qform M.endState (bOp (weylOf W v ⊗ₖ weylOf W v)) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hterm v) (uniform_nonneg (Anc F m) v)

set_option maxHeartbeats 1000000 in
/-- **Item 1 of `lem:qld-swap`, unconditional.** After the two swap unitaries the physical state
is close to a product of an auxiliary state on the two parties' non-ancilla registers and a
maximally entangled pair on the two halves of the ancilla. -/
theorem exists_aux_close {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hlt : 2 * Real.sqrt (deltaSelfCons δ ε m d (Fintype.card F))
      + 2 * deltaSelfCons δ ε m d (Fintype.card F) < 1) :
    ∃ aux : (((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb)) → ℂ,
      ‖evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ = 1 ∧
        ‖evec M.endState - evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ ^ 2
          ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt (deltaSelfCons δ ε m d (Fintype.card F))
            + 2 * deltaSelfCons δ ε m d (Fintype.card F))) :=
  exists_auxVec_close M.endState M.endState_unit
    (deltaSelfCons_nonneg hδ hε m d (Fintype.card F)) hlt
    (M.qform_endState_twirl_ge (hm := hm) hψ hfail hprojA hprojB hd .X)
    (M.qform_endState_twirl_ge (hm := hm) hψ hfail hprojA hprojB hd .Z)

end MirrorSimul

end Physical

end MIPRE.QLD
