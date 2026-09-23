/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.SwapItemOne

/-!
# Item 2 of `lem:qld-swap`, and the lemma

`MIPRE/Background/QLD/SwapItemOne.lean` proves item 1 of the swap isometry lemma with nothing
assumed beyond the game (`MirrorSimul.exists_aux_close`): after the two swap unitaries the
physical state is close to a product `|aux> ⊗ |EPR_q>^M`. This file proves item 2 --- conjugation
by a party's swap unitary carries the strategy's total Pauli measurement `M^{(Pauli,W)}_h` to the
honest projector `Id ⊗ tau^W_h` on that party's half of the pair, in the state-dependent distance
relative to that product state --- for both parties, and puts the two items together relative to
**one** auxiliary state: `MirrorSimul.swap_isometry`.

## The chain

No estimate here is new; every display of the paper's argument was already a lemma, and this file
is the threading. For Alice, on a state `Δ` that carries the pair on `A'' B''` and is within `r`
of the swapped physical state:

* `eq:qld-unitary-7`: both families are projective, so the summed deviation is twice the deficit
  of their agreement (`sum_snorm_sq_sub_le_of_agree`); and on the product state `tau^W_h` on `A''`
  acts as `tau^W_h` on `B''` (`mulVec_outerUnVec_auxVec`, from `stateVec_epr_proj`), which makes
  the agreement a bipartite Born probability across the physical cut.
* `eq:qld-unitary-8`: coarse-graining both families along `g_h(u)` raises the agreement by at most
  `md/q` (`sum_uniform_bornProb_fibre_le`).
* `eq:qld-unitary-6`, on **Bob's** side: the coarse-grained honest projector is a syndrome
  projector, which is Bob's exact Pauli measurement conjugated by his swap unitary
  (`bobSwap_conj_bobMTilde`), so the coarse agreement is `eq:qld-unitary-9`'s.
* The transport across item 1 (`sum_bornProb_conj_ge_of_close`): the conjugation moves onto the
  state, where it undoes the swap; the outcome sum is one projection, hence a contraction; and
  `abs_qform_sub_qform_le` costs `2 r`. With `r` the square root of item 1's bound on the squared
  distance, this is where `delta_S^{1/4}` enters.
* `eq:qld-unitary-5`, at the **mirror** instance (`sum_bornProb_physVec_ge`): on the physical state,
  Bob's exact Pauli measurement against Alice's `(Pauli, W)` reading is the second cut's `mTildeAt`
  against the swapped strategy's Pauli reading, and `inconsistency_mTilde_pauli_le_of_win` there,
  with its hypothesis discharged by item 1 of `lem:qld-exact-paulis` at the same instance
  (`inconsistency_mTilde_le`), bounds it.

## Three things that had to be said

* **The encoding as an outcome.** The Schwartz--Zippel packaging reads its index through
  coefficient tables of bounded individual degree. `ancPoly h` is the table of the low-degree
  encoding `ldEnc h`; it is faithful because the encoding is multilinear and `1 ≤ d`
  (`toMv_coeffTable`), and its value at `u` is the pairing `h . ind_m(u)` (`ancPoly_eval`).
* **The cut.** Item 1 concludes on its own cut, the two ancilla halves adjacent; the conjugated
  Pauli measurement lives on Alice's physical register. `outerUnVec` is the inverse of `outerVec`,
  so `physAux aux` is the product state read on the physical cut, and item 1's distance is the same
  number there (`norm_evec_physSwap_sub_physAux`).
* **Bob's half is Alice's at the mirror, relative to the same state.** The mirror's product state
  is this one's with the parties exchanged (`swapVec`), and so is its swapped physical state
  (`mirror_physSwap_mulVec`). The mirror's objects are spelled with `M.mirror.Ea` where Bob's are
  spelled with `M.Eb`; the two are definitionally equal but not reducibly so, so instance search
  cannot mix them. The rule that worked for item 1 works again: the state is named once, in the
  mirror's own spelling, and related to this one's by an equation.

## Constants

`deltaLegs` bounds each leg of `eq:qld-unitary-5`'s triangle, `11 * deltaLegs` the display (the
Lean triangle's `11` for the paper's `9`). Item 2's bound is
`deltaItemTwo = 2 (11 deltaLegs + md/q + 2 sqrt η)` for item 1's bound `η`; at `η = etaItemOne`,
which is `O(sqrt delta_S)`, that is `O(delta_S^{1/4} + md/q)`, the paper's `delta_qld`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

section Encoding

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A polynomial of individual degree at most `d` is the polynomial its coefficient table
denotes. -/
theorem toMv_coeffTable (p : MvPolynomial (Fin m) F)
    (hp : ∀ i, p.degreeOf i ≤ d) :
    LowIndDegPoly.toMv (F := F) (n := m) (d := d)
        (fun e : Fin m → Fin (d + 1) => p.coeff (expFinsupp e)) = p := by
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : ∀ i, s i ≤ d
  · have : s = expFinsupp fun i => (⟨s i, Nat.lt_succ_of_le (hs i)⟩ : Fin (d + 1)) := by
      ext i
      simp
    rw [this, LowIndDegPoly.coeff_toMv]
  · have h0 : (LowIndDegPoly.toMv (F := F) (n := m) (d := d)
        (fun e : Fin m → Fin (d + 1) => p.coeff (expFinsupp e))).coeff s = 0 := by
      simp only [LowIndDegPoly.toMv, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [if_neg]
      intro h
      apply hs
      intro i
      rw [← h, expFinsupp_apply]
      exact Nat.lt_succ_iff.mp (e i).isLt
    rw [h0]
    by_contra h
    push Not at hs
    obtain ⟨i, hi⟩ := hs
    have := MvPolynomial.degreeOf_le_iff.mp (hp i) s
      (MvPolynomial.mem_support_iff.mpr (Ne.symm h))
    omega

/-- **The low-degree encoding `g_h` of cube data `h`**, as a coefficient table of individual
degree at most `d`. It is multilinear, so this is faithful as soon as `1 ≤ d`. -/
def ancPoly (h : Anc F m) : LowIndDegPoly (F := F) (m := m) (d := d) :=
  fun e => (ldEnc h).coeff (expFinsupp e)

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem ancPoly_toMv (hd : 1 ≤ d) (h : Anc F m) : (ancPoly (d := d) h).toMv = ldEnc h :=
  toMv_coeffTable _ fun i => (degreeOf_ldEnc_le h i).trans hd

/-- **Its value at a point is the pairing with the point's indicator vector**: the paper's
`g_h(u) = h . ind_m(u)`. -/
theorem ancPoly_eval (hd : 1 ≤ d) (h : Anc F m) (u : Point F m) :
    (ancPoly (d := d) h).eval u = dotF h (indVec u) := by
  rw [← LowIndDegPoly.eval_toMv, ancPoly_toMv hd, dotF_indVec]

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Distinct cube data have distinct encodings**: the encoding reads the data back on the
cube. -/
theorem ancPoly_toMv_ne (hd : 1 ≤ d) {h h' : Anc F m} (hne : h ≠ h') :
    (ancPoly (d := d) h).toMv ≠ (ancPoly (d := d) h').toMv := by
  rw [ancPoly_toMv hd, ancPoly_toMv hd]
  intro heq
  exact hne (funext fun y => by rw [← eval_ldEnc h y, ← eval_ldEnc h' y, heq])

end Encoding

/-! ## Generic facts the threading uses -/

section Generic

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Conjugating a projective measurement by a unitary gives a projective measurement.** -/
theorem isPVM_conj_unitary {N Λ : Type*} [Fintype N] [DecidableEq N] [Fintype Λ]
    {P : Λ → Matrix N N ℂ} (hP : IsPVM P) {V : Matrix N N ℂ} (h1 : Vᴴ * V = 1)
    (h2 : V * Vᴴ = 1) : IsPVM fun a => V * P a * Vᴴ where
  isSelfAdjoint a := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hP.isSelfAdjoint, Matrix.mul_assoc]
  idem a := by
    rw [show V * P a * Vᴴ * (V * P a * Vᴴ) = V * P a * (Vᴴ * V) * P a * Vᴴ from by
      simp only [Matrix.mul_assoc], h1, Matrix.mul_one, Matrix.mul_assoc V (P a) (P a),
      hP.idem]
  sum_eq_one := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.sum_eq_one, Matrix.mul_one, h2]

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **A projection is a contraction.** -/
theorem bnd_one_of_proj {N : Type*} [Fintype N] [DecidableEq N] {P : Matrix N N ℂ}
    (hsa : Pᴴ = P) (hidem : P * P = P) : Bnd P 1 :=
  bnd_one_of_conjTranspose_mul_self_le (by rw [hsa, hidem]; exact proj_le_one hsa hidem)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **The swap moves an operator on the second party to the first.** -/
theorem mulVec_swapVec_aOp {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (v : dA × dB → ℂ) (Z : Matrix dB dB ℂ) :
    (aOp Z : Matrix (dB × dA) (dB × dA) ℂ) *ᵥ swapVec v
      = swapVec ((bOp Z : Matrix (dA × dB) (dA × dB) ℂ) *ᵥ v) :=
  mulVec_kronecker_swapVec Z 1 v

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem mulVec_swapVec_bOp {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (v : dA × dB → ℂ) (Z : Matrix dA dA ℂ) :
    (bOp Z : Matrix (dB × dA) (dB × dA) ℂ) *ᵥ swapVec v
      = swapVec ((aOp Z : Matrix (dA × dB) (dA × dB) ℂ) *ᵥ v) :=
  mulVec_kronecker_swapVec 1 Z v

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Conjugating the operator is conjugating the state the other way.** -/
theorem qform_conj_eq {N : Type*} [Fintype N] (V O : Matrix N N ℂ) (v : N → ℂ) :
    qform v (V * O * Vᴴ) = qform (Vᴴ *ᵥ v) O := by
  rw [qform, qform, dotProduct_mulVec_conj, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A vector of norm one is a unit vector in the `dotProduct` sense. -/
theorem unit_of_norm_evec_eq_one {N : Type*} [Fintype N] {v : N → ℂ} (h : ‖evec v‖ = 1) :
    star v ⬝ᵥ v = 1 := by
  rw [← inner_evec, inner_self_eq_norm_sq_to_K, h]
  simp

end Generic

/-! ## The product state, read on the physical cut -/

section Outer

variable {A B T T' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']

/-- **A state on item 1's cut, read on the physical one.** The inverse of `outerVec`. -/
def outerUnVec (χ : (A × B) × (T × T') → ℂ) : (A × T) × (B × T') → ℂ :=
  χ ∘ outerPairEquiv (A := A) (B := B) (T := T) (T' := T')

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
  [Fintype T'] [DecidableEq T'] in
theorem outerVec_outerUnVec (χ : (A × B) × (T × T') → ℂ) : outerVec (outerUnVec χ) = χ := by
  funext p
  simp [outerVec, outerUnVec]

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [DecidableEq A] [DecidableEq B] [DecidableEq T] [DecidableEq T'] in
/-- It is a unit vector exactly when the state is. -/
theorem norm_evec_outerUnVec (χ : (A × B) × (T × T') → ℂ) :
    ‖evec (outerUnVec χ)‖ = ‖evec χ‖ := by
  simp only [outerUnVec, evec, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp (outerPairEquiv (A := A) (B := B) (T := T) (T' := T'))
    fun j => ‖χ j‖ ^ 2

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [DecidableEq A] [DecidableEq B] [DecidableEq T] [DecidableEq T'] in
/-- **Distances are the same on both cuts.** -/
theorem norm_evec_sub_outerUnVec (w : (A × T) × (B × T') → ℂ) (χ : (A × B) × (T × T') → ℂ) :
    ‖evec (w - outerUnVec χ)‖ = ‖evec (outerVec w) - evec χ‖ := by
  rw [← evec_sub, ← norm_evec_outerUnVec (outerVec w - χ)]
  congr 2

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Applying an operator on the physical cut is applying its regrouping on item 1's.** -/
theorem mulVec_outerUnVec (χ : (A × B) × (T × T') → ℂ)
    (X : Matrix ((A × T) × (B × T')) ((A × T) × (B × T')) ℂ) :
    X *ᵥ outerUnVec χ
      = (Matrix.reindex (outerPairEquiv (A := A) (B := B) (T := T) (T' := T'))
          (outerPairEquiv (A := A) (B := B) (T := T) (T' := T')) X *ᵥ χ)
        ∘ outerPairEquiv (A := A) (B := B) (T := T) (T' := T') := by
  have h := mulVec_comp_equiv (outerPairEquiv (A := A) (B := B) (T := T) (T' := T'))
    (outerUnVec χ) X
  have hχ : outerUnVec χ ∘ (outerPairEquiv (A := A) (B := B) (T := T) (T' := T')).symm = χ :=
    outerVec_outerUnVec χ
  rw [hχ] at h
  rw [h]
  funext p
  simp

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [NeZero m] in
/-- **On the product state, an operator on Alice's half of the pair moves to Bob's**, read on the
physical cut, whenever it does so on the entangled pair itself. This is the last line of display
`eq:qld-unitary-7` where each party holds its own half of `|EPR_q>^M`. -/
theorem mulVec_outerUnVec_auxVec (aux : A × B → ℂ) {P : Matrix (n → F) (n → F) ℂ}
    (hP : (aOp P : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ) *ᵥ epr (F := F) (n := n)
      = bOp P *ᵥ epr) :
    (aOp (bOp P) : Matrix ((A × (n → F)) × (B × (n → F))) ((A × (n → F)) × (B × (n → F))) ℂ)
        *ᵥ outerUnVec (auxVec (F := F) (n := n) aux)
      = (bOp (bOp P) :
          Matrix ((A × (n → F)) × (B × (n → F))) ((A × (n → F)) × (B × (n → F))) ℂ)
        *ᵥ outerUnVec (auxVec (F := F) (n := n) aux) := by
  have hA : Matrix.reindex (outerPairEquiv (A := A) (B := B) (T := n → F) (T' := n → F))
      (outerPairEquiv (A := A) (B := B) (T := n → F) (T' := n → F))
      (aOp (bOp P) :
        Matrix ((A × (n → F)) × (B × (n → F))) ((A × (n → F)) × (B × (n → F))) ℂ)
      = bOp (aOp P) := by
    rw [show (aOp (bOp P) :
          Matrix ((A × (n → F)) × (B × (n → F))) ((A × (n → F)) × (B × (n → F))) ℂ)
        = ((1 : Matrix A A ℂ) ⊗ₖ P) ⊗ₖ ((1 : Matrix B B ℂ) ⊗ₖ (1 : Matrix (n → F) (n → F) ℂ))
        from by rw [Matrix.one_kronecker_one]; rfl,
      reindex_outerPairEquiv, Matrix.one_kronecker_one]
    rfl
  have hB : Matrix.reindex (outerPairEquiv (A := A) (B := B) (T := n → F) (T' := n → F))
      (outerPairEquiv (A := A) (B := B) (T := n → F) (T' := n → F))
      (bOp (bOp P) :
        Matrix ((A × (n → F)) × (B × (n → F))) ((A × (n → F)) × (B × (n → F))) ℂ)
      = bOp (bOp P) := by
    rw [show (bOp (bOp P) :
          Matrix ((A × (n → F)) × (B × (n → F))) ((A × (n → F)) × (B × (n → F))) ℂ)
        = ((1 : Matrix A A ℂ) ⊗ₖ (1 : Matrix (n → F) (n → F) ℂ)) ⊗ₖ ((1 : Matrix B B ℂ) ⊗ₖ P)
        from by rw [Matrix.one_kronecker_one]; rfl,
      reindex_outerPairEquiv, Matrix.one_kronecker_one]
    rfl
  rw [mulVec_outerUnVec, mulVec_outerUnVec, hA, hB,
    mulVec_auxVec_congr (R := A × B) aux hP]

end Outer

/-! ## The objects item 2 is about -/

section Physical

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

set_option synthInstance.maxSize 1000

/-- **The constant the three legs of `eq:qld-unitary-5` share**: item 1 of
`lem:qld-exact-paulis` (`inconsistency_mTilde_le`) and the game's two consistencies at `86 ε`,
added so that one number bounds all three. -/
def deltaLegs (δ ε : ℝ) (m d q : ℕ) : ℝ :=
  δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / q) + 86 * ε

/-- The constant of item 2: `eq:qld-unitary-5`'s `11 δ'`, Schwartz--Zippel's `md/q`, and the
transport across item 1, which costs twice the square root of item 1's bound. -/
def deltaItemTwo (δ ε : ℝ) (m d q : ℕ) (η : ℝ) : ℝ :=
  2 * (11 * deltaLegs δ ε m d q + (m : ℝ) * d / q + 2 * Real.sqrt η)

/-- **Item 1's bound**, named so that the joint statement fits. -/
def etaItemOne (δ ε : ℝ) (m d q : ℕ) : ℝ :=
  2 - 2 * Real.sqrt (1 - (2 * Real.sqrt (deltaSelfCons δ ε m d q) + 2 * deltaSelfCons δ ε m d q))

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **Alice's total Pauli measurement** `M^{(Pauli,W)}_h`, its outcomes the cube data `h` the
answer reports, extended by the identity to her physical register `A A' Ea A''`. An answer that is
not a well-formed Pauli answer is read as `h = 0` by `rdPauliVec`; the paper assumes well-formed
answers, and this is a relabelling of outcomes, not a restriction. -/
def alicePauli (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  aOp (aOp (aOp ((((MA (.pauli W)).map rdPauliVec).mats h).val)))

/-- **Bob's**, on `B B' Eb B''`. -/
def bobPauli (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  aOp (aOp (aOp ((((MB (.pauli W)).map rdPauliVec).mats h).val)))

/-- **Alice's conjugated Pauli measurement** `V_A M^{(Pauli,W)}_h V_A^dagger`. -/
def aliceConjPauli (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.aliceSwap * M.alicePauli W h * M.aliceSwapᴴ

/-- **Bob's** `V_B M^{(Pauli,W)}_h V_B^dagger`. -/
def bobConjPauli (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.bobSwap * M.bobPauli W h * M.bobSwapᴴ

/-- **The honest Pauli projector `tau^W_h` on Alice's half of the pair**, `Id ⊗ tau^W_h`. -/
def aliceTau (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  bOp (proj (weylOf W) h)

/-- **And on Bob's.** -/
def bobTau (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  bOp (proj (weylOf W) h)

theorem aliceSwap_mul_conjTranspose : M.aliceSwap * M.aliceSwapᴴ = 1 :=
  M.toFirst.swapA_mul_conjTranspose

theorem physSwap_mul_conjTranspose : M.physSwap * M.physSwapᴴ = 1 := by
  rw [physSwap, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, M.aliceSwap_mul_conjTranspose,
    M.bobSwap_mul_conjTranspose, aOp_one, bOp_one, Matrix.one_mul]

theorem isPVM_alicePauli (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)) (W : Bas) :
    IsPVM (M.alicePauli W) :=
  (((isPVM_povm_map _ (hprojA _) rdPauliVec).aOp).aOp).aOp

theorem isPVM_aliceConjPauli (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)) (W : Bas) :
    IsPVM (M.aliceConjPauli W) :=
  isPVM_conj_unitary (M.isPVM_alicePauli hprojA W) M.aliceSwap_conjTranspose_mul
    M.aliceSwap_mul_conjTranspose

theorem isPVM_aliceTau (W : Bas) : IsPVM (M.aliceTau W) :=
  (isPVM_proj (isWeylFamily_weylOf W)).bOp

theorem isPVM_bobTau (W : Bas) : IsPVM (M.bobTau W) :=
  (isPVM_proj (isWeylFamily_weylOf W)).bOp

/-- **Alice's conjugated Pauli measurement, coarse-grained along `g_h(u)`, is the conjugated
`M^{(Pauli,W)}_{[g_h(u) = a]}`.** -/
theorem sum_aliceConjPauli_fibre (hd : 1 ≤ d) (W : Bas) (u : Point F m) (a : F) :
    ∑ h ∈ univ.filter fun h => (ancPoly (d := d) h).eval u = a, M.aliceConjPauli W h
      = M.aliceSwap * aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val))) * M.aliceSwapᴴ := by
  rw [Finset.filter_congr fun h _ => by rw [ancPoly_eval hd]]
  simp only [aliceConjPauli, alicePauli]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← aOp_sum, ← aOp_sum, ← aOp_sum]
  have hY : ((MA (.pauli W)).map rdPauliVec).map (fun k => dotF k (indVec u))
      = pauliAtPOVM MA W u := by
    rw [POVM.map_map, pauliAtPOVM, show (fun a => dotF (rdPauliVec a) (indVec u)) = rdPauli u
      from funext fun a => (rdPauli_eq_dotF u a).symm]
  rw [← hY, POVM.map_mats]

/-- **The honest projectors, coarse-grained along `g_h(u)`, are the syndrome projector, which is
Bob's exact Pauli measurement conjugated by his swap unitary** (`eq:qld-unitary-6`). -/
theorem sum_bobTau_fibre (hd : 1 ≤ d) (W : Bas) (u : Point F m) (a : F) :
    ∑ h ∈ univ.filter fun h => (ancPoly (d := d) h).eval u = a, M.bobTau W h
      = M.bobSwap * M.bobMTilde W (indVec u) a * M.bobSwapᴴ := by
  rw [Finset.filter_congr fun h _ => by rw [ancPoly_eval hd], M.bobSwap_conj_bobMTilde]
  simp only [bobTau]
  rw [← bOp_sum]
  rfl

/-- **Alice's `(Pauli, W)` measurement read at `u`, against Bob's exact Pauli measurement, on the
physical state, is the same pair on the mirror's cut** --- where Bob's `M~` is the first party's
`mTildeAt` and Alice's reading is the second party's, which is the orientation
`eq:qld-unitary-5` is proved in. -/
theorem bornProb_physVec_pauli_bobMTilde (W : Bas) (u : Point F m) (a : F) :
    bornProb M.physVec (aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val))))
        (M.bobMTilde W (indVec u) a)
      = bornProb M.toSecond.mVec (M.toSecond.mTildeAt W u a)
          (aOp (((pauliAtPOVM MA W u).mats a).val)) := by
  rw [← bornProb_swapVec]
  have h := M.mirror.bornProb_physVec (M.bobMTilde W (indVec u) a)
    (((pauliAtPOVM MA W u).mats a).val) 1
  rw [M.mirror_physVec] at h
  exact h

/-- **`eq:qld-unitary-5`, on the physical state.** Alice's `(Pauli, W)` measurement read at the
sampled point agrees with Bob's exact Pauli measurement at that point's encoding, to within
`11 δ'`: this is `inconsistency_mTilde_pauli_le_of_win` at the mirror instance, whose hypothesis is
item 1 of `lem:qld-exact-paulis` there. -/
theorem sum_bornProb_physVec_ge {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (W : Bas) :
    1 - 11 * deltaLegs δ ε m d (Fintype.card F)
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F, bornProb M.physVec
          (aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val)))) (M.bobMTilde W (indVec u) a) := by
  have hψ' : star (ψ ∘ Prod.swap) ⬝ᵥ (ψ ∘ Prod.swap) = 1 := swapVec_unit hψ
  have hfail' : 1 - povmValue (qldGame hm) (ψ ∘ Prod.swap) MB MA ≤ ε :=
    povmValue_swapped_le hfail
  have hmt := M.toSecond.inconsistency_mTilde_le (hm := hm) hψ' hfail' hprojA hd W
  have hsq : 0 ≤ Real.sqrt (688 * ε) := Real.sqrt_nonneg _
  have hmd : (0 : ℝ) ≤ (m : ℝ) * d / Fintype.card F := by positivity
  have hle : δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F)
      ≤ deltaLegs δ ε m d (Fintype.card F) := by
    rw [deltaLegs]
    linarith
  have h86 : 86 * ε ≤ deltaLegs δ ε m d (Fintype.card F) := by
    rw [deltaLegs]
    nlinarith
  have hinc := M.toSecond.inconsistency_mTilde_pauli_le_of_win (hm := hm) hψ' hfail' hprojB hprojA
    W h86 (le_trans hmt hle)
  have hdiag := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) M.toSecond.mVec_unit
    (fun u => (M.toSecond.isPVM_mTildeAt W u).toPOVM)
    (fun u => (pauliAtPOVM MA W u).aOp)
  simp only [IsPVM.toPOVM_mats, POVM.aOp_mats] at hdiag
  simp only [M.bornProb_physVec_pauli_bobMTilde]
  linarith

/-- **A fibred agreement, carried from the physical state to a nearby one.** On a state `Δ`
within `r` of the swapped physical state, a pair of projective families conjugated by the two swap
unitaries reads what the bare pair reads on the physical state, up to `2 r`: the conjugation moves
onto the state, where it undoes the swap, and the outcome sum is one projection, so a
contraction (`abs_qform_sub_qform_le`). -/
theorem sum_bornProb_conj_ge_of_close {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {Y : Λ → Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ}
    {Z : Λ → Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ}
    (hY : IsPVM Y) (hZ : IsPVM Z)
    (Δ : ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ)
    (hΔ : ‖evec Δ‖ = 1) {r : ℝ} (hr : ‖evec (M.physSwap *ᵥ M.physVec - Δ)‖ ≤ r) :
    (∑ a, bornProb M.physVec (Y a) (Z a)) - 2 * r
      ≤ ∑ a, bornProb Δ (M.aliceSwap * Y a * M.aliceSwapᴴ) (M.bobSwap * Z a * M.bobSwapᴴ) := by
  -- the outcome sum, as one operator on the physical cut
  obtain ⟨O, hOdef⟩ : ∃ O : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
      × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ,
      O = ∑ a, (aOp (Y a) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
        × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        * bOp (Z a) := ⟨_, rfl⟩
  have hphys : ∑ a, bornProb M.physVec (Y a) (Z a) = qform M.physVec O := by
    rw [hOdef, qform_sum]
    exact Finset.sum_congr rfl fun a _ => bornProb_eq_qform _ _ _
  have hconj : ∑ a, bornProb Δ (M.aliceSwap * Y a * M.aliceSwapᴴ)
      (M.bobSwap * Z a * M.bobSwapᴴ) = qform (M.physSwapᴴ *ᵥ Δ) O := by
    rw [← qform_conj_eq, hOdef, Finset.mul_sum, Finset.sum_mul, qform_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [bornProb_eq_qform, physSwap, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp,
      aOp_bOp_mul_aOp_bOp]
  -- the operator is a contraction
  obtain ⟨hsa, hid⟩ := isProj_diag (dA := (((dA × Anc F m) × M.Ea) × Anc F m))
    (dB := (((dB × Anc F m) × M.Eb) × Anc F m)) hY hZ
  have hbnd : Bnd O 1 := by
    rw [hOdef]
    exact bnd_one_of_proj hsa hid
  -- and the two states are close
  have hiso : (M.physSwapᴴ)ᴴ * M.physSwapᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose, M.physSwap_mul_conjTranspose]
  have hnorm : ‖evec (M.physSwapᴴ *ᵥ Δ)‖ = 1 := by
    rw [norm_evec_mulVec_of_isometry hiso, hΔ]
  have hdist : ‖evec (M.physSwapᴴ *ᵥ Δ - M.physVec)‖ ≤ r := by
    have heq : M.physSwapᴴ *ᵥ Δ - M.physVec = M.physSwapᴴ *ᵥ (Δ - M.physSwap *ᵥ M.physVec) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, M.physSwap_conjTranspose_mul,
        Matrix.one_mulVec]
    rw [heq, norm_evec_mulVec_of_isometry hiso, evec_sub, norm_sub_rev, ← evec_sub]
    exact hr
  have htr := abs_qform_sub_qform_le (M.physSwapᴴ *ᵥ Δ) M.physVec zero_le_one hbnd hnorm.le
    (norm_evec_eq_one_of_unit M.physVec_unit).le
  rw [hphys, hconj]
  have := (abs_le.mp htr).1
  linarith

/-- **Display `eq:qld-unitary-9` and the calculation after it**: on a state `Δ` within `r` of
the swapped physical state, the conjugated Pauli measurement read at the sampled point agrees with
Bob's conjugated exact Pauli measurement to within `11 δ' + 2 r`, on average over the point. The
`11 δ'` is `eq:qld-unitary-5`; the `2 r` is the transport across item 1. -/
theorem sum_bornProb_fibre_ge {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (Δ : ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ)
    (hΔ : ‖evec Δ‖ = 1) {r : ℝ} (hr : ‖evec (M.physSwap *ᵥ M.physVec - Δ)‖ ≤ r) (W : Bas) :
    1 - 11 * deltaLegs δ ε m d (Fintype.card F) - 2 * r
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F, bornProb Δ
          (M.aliceSwap * aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val))) * M.aliceSwapᴴ)
          (M.bobSwap * M.bobMTilde W (indVec u) a * M.bobSwapᴴ) := by
  have hphys := M.sum_bornProb_physVec_ge (hm := hm) hψ hfail hprojA hprojB hd hδ hε W
  have hterm : ∀ u : Point F m,
      uniform (Point F m) u * ((∑ a : F, bornProb M.physVec
          (aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val)))) (M.bobMTilde W (indVec u) a))
        - 2 * r)
      ≤ uniform (Point F m) u * ∑ a : F, bornProb Δ
          (M.aliceSwap * aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val))) * M.aliceSwapᴴ)
          (M.bobSwap * M.bobMTilde W (indVec u) a * M.bobSwapᴴ) := fun u =>
    mul_le_mul_of_nonneg_left
      (M.sum_bornProb_conj_ge_of_close
        ((((isPVM_povm_map _ (hprojA _) _).aOp).aOp).aOp)
        (M.isPVM_bobMTilde W (indVec u)) Δ hΔ hr)
      (uniform_nonneg (Point F m) u)
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) => hterm u
  have hsplit : ∑ u : Point F m, uniform (Point F m) u * ((∑ a : F, bornProb M.physVec
          (aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val)))) (M.bobMTilde W (indVec u) a))
        - 2 * r)
      = (∑ u : Point F m, uniform (Point F m) u * ∑ a : F, bornProb M.physVec
          (aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val)))) (M.bobMTilde W (indVec u) a))
        - 2 * r := by
    rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => mul_sub (uniform (Point F m) u) _ _,
      Finset.sum_sub_distrib, ← Finset.sum_mul, sum_uniform_eq_one, one_mul]
  rw [hsplit] at hsum
  linarith

/-- **Item 2 of `lem:qld-swap` for Alice, relative to any state that carries `|EPR_q>^M` on the
two halves of the pair and is close to the swapped physical state.** The summed state-dependent
distance between `V_A M^{(Pauli,W)}_h V_A^dagger` and `Id ⊗ tau^W_h` on `A''` is at most
`2 (11 δ' + md/q + 2 r)`.

The chain is the paper's. Both families are projective, so the deviation is twice the deficit of
their agreement (`eq:qld-unitary-7`); `hmove` carries `tau^W_h` from `A''` to `B''`, making the
agreement a bipartite Born probability; coarse-graining along `g_h(u)` costs `md/q`
(`eq:qld-unitary-8`), and the coarse-grained honest projector is Bob's conjugated exact Pauli
measurement (`eq:qld-unitary-6`, `eq:qld-unitary-9`); the rest is `sum_bornProb_fibre_ge`. -/
theorem sum_snorm_sq_aliceConjPauli_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (Δ : ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ)
    (hΔ : ‖evec Δ‖ = 1)
    (hmove : ∀ (W : Bas) (h : Anc F m),
      (aOp (M.aliceTau W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ) *ᵥ Δ
        = bOp (M.bobTau W h) *ᵥ Δ)
    {r : ℝ} (hr : ‖evec (M.physSwap *ᵥ M.physVec - Δ)‖ ≤ r) (W : Bas) :
    ∑ h : Anc F m, snorm Δ ((aOp (M.aliceConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea)
          × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        - aOp (M.aliceTau W h)) ^ 2
      ≤ 2 * (11 * deltaLegs δ ε m d (Fintype.card F) + (m : ℝ) * d / Fintype.card F + 2 * r) := by
  refine sum_snorm_sq_sub_le_of_agree hΔ (M.isPVM_aliceConjPauli hprojA W).aOp
    (M.isPVM_aliceTau W).aOp ?_
  have hswap : ∀ h : Anc F m,
      qform Δ ((aOp (M.aliceConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        * aOp (M.aliceTau W h))
        = bornProb Δ (M.aliceConjPauli W h) (M.bobTau W h) := by
    intro h
    rw [bornProb_eq_qform, qform, qform, ← Matrix.mulVec_mulVec, hmove W h,
      Matrix.mulVec_mulVec]
  have hfib := sum_uniform_bornProb_fibre_le (unit_of_norm_evec_eq_one hΔ)
    (M.isPVM_aliceConjPauli hprojA W) (M.isPVM_bobTau W) (enc := ancPoly (d := d))
    (fun h h' hne => ancPoly_toMv_ne hd hne)
  simp only [M.sum_aliceConjPauli_fibre hd, M.sum_bobTau_fibre hd] at hfib
  have hagree := M.sum_bornProb_fibre_ge (hm := hm) hψ hfail hprojA hprojB hd hδ hε Δ hΔ hr W
  rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) => hswap h]
  linarith

/-! ### The product state of item 1 -/

/-- **The product state `|aux> ⊗ |EPR_q>^M` of item 1, read on the physical cut**: each party's
half of the pair back at the end of its own register. -/
def physAux (aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ) :
    ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ :=
  outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux)

theorem norm_evec_physAux (aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ) :
    ‖evec (M.physAux aux)‖ = ‖evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ :=
  norm_evec_outerUnVec _

/-- **Item 1's distance, read on the physical cut.** -/
theorem norm_evec_physSwap_sub_physAux
    (aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ) :
    ‖evec (M.physSwap *ᵥ M.physVec - M.physAux aux)‖
      = ‖evec M.endState - evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ :=
  norm_evec_sub_outerUnVec _ _

/-- **On the product state, `tau^W_h` on `A''` is `tau^W_h` on `B''`**: the last line of
`eq:qld-unitary-7`. The Weyl families are symmetric matrices, so their spectral projectors move
across the entangled pair. -/
theorem aliceTau_mulVec_physAux
    (aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ) (W : Bas) (h : Anc F m) :
    (aOp (M.aliceTau W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
        × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        *ᵥ M.physAux aux
      = bOp (M.bobTau W h) *ᵥ M.physAux aux :=
  mulVec_outerUnVec_auxVec aux
    (congrArg WithLp.ofLp (stateVec_epr_proj (weylOf_transpose W) h))

/-- **Item 2 of `lem:qld-swap`, Alice's half**, relative to any auxiliary state for which item 1
holds with bound `η`: conjugation by `V_A` carries the strategy's total Pauli measurement
`M^{(Pauli,W)}_h` to `Id ⊗ tau^W_h` on `A''`, within `deltaItemTwo` in the state-dependent
distance relative to `|aux> ⊗ |EPR_q>^M`. -/
theorem sum_snorm_sq_alice_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ)
    (haux : ‖evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ = 1) {η : ℝ}
    (hη : ‖evec M.endState - evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ ^ 2 ≤ η)
    (W : Bas) :
    ∑ h : Anc F m, snorm (M.physAux aux)
        ((aOp (M.aliceConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
          - aOp (M.aliceTau W h)) ^ 2
      ≤ deltaItemTwo δ ε m d (Fintype.card F) η := by
  have hr : ‖evec (M.physSwap *ᵥ M.physVec - M.physAux aux)‖ ≤ Real.sqrt η := by
    rw [M.norm_evec_physSwap_sub_physAux]
    exact Real.le_sqrt_of_sq_le hη
  exact M.sum_snorm_sq_aliceConjPauli_le (hm := hm) hψ hfail hprojA hprojB hd hδ hε
    (M.physAux aux) (by rw [M.norm_evec_physAux, haux]) (M.aliceTau_mulVec_physAux aux) hr W

/-! ### Bob's half, through the mirror -/

/-- **The mirror's swapped physical state is the swapped physical state, swapped.** The mirror's
swap unitaries are Bob's and Alice's in the other order, and its physical state is the physical
state read with the parties exchanged. -/
theorem mirror_physSwap_mulVec :
    M.mirror.physSwap *ᵥ M.mirror.physVec = swapVec (M.physSwap *ᵥ M.physVec) := by
  have h := mulVec_kronecker_swapVec M.bobSwap M.aliceSwap M.physVec
  rw [← aOp_mul_bOp_eq, ← aOp_mul_bOp_eq] at h
  rw [M.mirror_physVec]
  exact h

/-- **Item 2 of `lem:qld-swap`, Bob's half, relative to the same auxiliary state.** Alice's half
at the mirror, whose first party is Bob, read on the physical state with the parties exchanged:
the mirror's swapped physical state is this one's, swapped (`mirror_physSwap_mulVec`), and the
exchange carries `tau^W_h`'s move across the pair to the mirror's. So the one product state serves
both halves, which is what the paper's item 2 asks. -/
theorem sum_snorm_sq_bob_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ)
    (haux : ‖evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ = 1) {η : ℝ}
    (hη : ‖evec M.endState - evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ ^ 2 ≤ η)
    (W : Bas) :
    ∑ h : Anc F m, snorm (M.physAux aux)
        ((bOp (M.bobConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
          - bOp (M.bobTau W h)) ^ 2
      ≤ deltaItemTwo δ ε m d (Fintype.card F) η := by
  have hr : ‖evec (M.physSwap *ᵥ M.physVec - M.physAux aux)‖ ≤ Real.sqrt η := by
    rw [M.norm_evec_physSwap_sub_physAux]
    exact Real.le_sqrt_of_sq_le hη
  have hΔ : ‖evec (M.physAux aux)‖ = 1 := by rw [M.norm_evec_physAux, haux]
  -- the product state, in the mirror's own spelling
  obtain ⟨Δ', hΔ'⟩ : ∃ Δ' : ((((dB × Anc F m) × M.mirror.Ea) × Anc F m))
      × ((((dA × Anc F m) × M.mirror.Eb) × Anc F m)) → ℂ,
      Δ' = swapVec (M.physAux aux) := ⟨_, rfl⟩
  have hΔn : ‖evec Δ'‖ = 1 := by
    rw [hΔ']
    exact (norm_swapVec _).trans hΔ
  have hr' : ‖evec (M.mirror.physSwap *ᵥ M.mirror.physVec - Δ')‖ ≤ Real.sqrt η := by
    have h1 : M.mirror.physSwap *ᵥ M.mirror.physVec - Δ'
        = swapVec (M.physSwap *ᵥ M.physVec - M.physAux aux) := by
      rw [hΔ', M.mirror_physSwap_mulVec]
      rfl
    rw [h1]
    exact (norm_swapVec _).trans_le hr
  have hmove : ∀ (W : Bas) (h : Anc F m),
      (aOp (M.mirror.aliceTau W h) : Matrix ((((dB × Anc F m) × M.mirror.Ea) × Anc F m)
          × (((dA × Anc F m) × M.mirror.Eb) × Anc F m))
        ((((dB × Anc F m) × M.mirror.Ea) × Anc F m)
          × (((dA × Anc F m) × M.mirror.Eb) × Anc F m)) ℂ) *ᵥ Δ'
        = bOp (M.mirror.bobTau W h) *ᵥ Δ' := by
    intro W h
    rw [hΔ']
    exact (mulVec_swapVec_aOp (M.physAux aux) (M.bobTau W h)).trans
      ((congrArg swapVec (M.aliceTau_mulVec_physAux aux W h)).symm.trans
        (mulVec_swapVec_bOp (M.physAux aux) (M.aliceTau W h)).symm)
  have hcore := M.mirror.sum_snorm_sq_aliceConjPauli_le (hm := hm) (swapVec_unit hψ)
    (povmValue_swapped_le hfail) hprojB hprojA hd hδ hε Δ' hΔn hmove hr' W
  subst hΔ'
  have hterm : ∀ h : Anc F m, snorm (M.physAux aux)
        ((bOp (M.bobConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
          - bOp (M.bobTau W h)) ^ 2
      = snorm (swapVec (M.physAux aux))
        ((aOp (M.bobConjPauli W h) : Matrix ((((dB × Anc F m) × M.Eb) × Anc F m)
            × (((dA × Anc F m) × M.Ea) × Anc F m))
          ((((dB × Anc F m) × M.Eb) × Anc F m) × (((dA × Anc F m) × M.Ea) × Anc F m)) ℂ)
          - aOp (M.bobTau W h)) ^ 2 := by
    intro h
    rw [← aOp_sub, snorm_swapVec_aOp, norm_stateVecB_eq_snorm, bOp_sub]
  refine Eq.trans_le (Finset.sum_congr rfl fun h _ => (hterm h).trans ?_) hcore
  rfl

/-! ### The joint lemma -/

/-- **`lem:qld-swap`: the swap isometry.** There is an auxiliary state `|aux>` on the two parties'
non-ancilla registers such that

1. after the two swap unitaries the physical state is within `etaItemOne` of
   `|aux> ⊗ |EPR_q>^M`, in squared norm; and
2. for each basis `W`, conjugation by `V_A`, resp. `V_B`, carries the strategy's total Pauli
   measurement `M^{(Pauli,W)}_h` to `Id ⊗ tau^W_h` on `A''`, resp. `B''`, within
   `deltaItemTwo … etaItemOne` in the state-dependent distance relative to that **same** product
   state.

Item 1 is `exists_aux_close`; item 2 is `sum_snorm_sq_alice_le` and `sum_snorm_sq_bob_le` at the
auxiliary state it produces. -/
theorem swap_isometry {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hlt : 2 * Real.sqrt (deltaSelfCons δ ε m d (Fintype.card F))
      + 2 * deltaSelfCons δ ε m d (Fintype.card F) < 1) :
    ∃ aux : (((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb)) → ℂ,
      ‖evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ = 1 ∧
      ‖evec M.endState - evec (auxVec (F := F) (n := Fin m → Bool) aux)‖ ^ 2
        ≤ etaItemOne δ ε m d (Fintype.card F) ∧
      ∀ W : Bas,
        ∑ h : Anc F m, snorm (M.physAux aux)
            ((aOp (M.aliceConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
                × (((dB × Anc F m) × M.Eb) × Anc F m))
              ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
              - aOp (M.aliceTau W h)) ^ 2
          ≤ deltaItemTwo δ ε m d (Fintype.card F) (etaItemOne δ ε m d (Fintype.card F)) ∧
        ∑ h : Anc F m, snorm (M.physAux aux)
            ((bOp (M.bobConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
                × (((dB × Anc F m) × M.Eb) × Anc F m))
              ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
              - bOp (M.bobTau W h)) ^ 2
          ≤ deltaItemTwo δ ε m d (Fintype.card F) (etaItemOne δ ε m d (Fintype.card F)) := by
  obtain ⟨aux, haux, hclose⟩ := M.exists_aux_close (hm := hm) hψ hfail hprojA hprojB hd hδ hε hlt
  exact ⟨aux, haux, hclose, fun W =>
    ⟨M.sum_snorm_sq_alice_le (hm := hm) hψ hfail hprojA hprojB hd hδ hε aux haux hclose W,
      M.sum_snorm_sq_bob_le (hm := hm) hψ hfail hprojA hprojB hd hδ hε aux haux hclose W⟩⟩

end MirrorSimul

end Physical

end MIPRE.QLD

end
