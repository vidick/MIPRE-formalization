/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.SwapItemOne

@[expose] public section

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
  acts as `tau^W_h` on `B''` (`aliceTau_mulVec_physAux`, from the mirror identity `reg_mirror` of
  the register model of item 1's cut), which makes the agreement a bipartite Born probability
  across the physical cut.
* `eq:qld-unitary-8`: coarse-graining both families along `g_h(u)` raises the agreement by at most
  `md/q` (`sum_uniform_bornProb_fibre_le`).
* `eq:qld-unitary-6`, on **Bob's** side: the coarse-grained honest projector is a syndrome
  projector, which is Bob's exact Pauli measurement conjugated by his swap unitary
  (`bobSwap_conj_bobMTilde`), so the coarse agreement is `eq:qld-unitary-9`'s.
* The transport across item 1 (`sum_bornProb_conj_ge_of_close`): the conjugation moves onto the
  state, where it undoes the swap; the outcome sum is one projection, hence a contraction; and
  `StateModel.abs_qform_withState_sub_qform_le` costs `2 r`. With `r` the square root of item 1's
  bound on the squared distance, this is where `delta_S^{1/4}` enters.
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
* **The cut.** Item 1 concludes on its own cut, the register model `tgt` with the two far halves
  outside; the conjugated Pauli measurement lives on Alice's physical registers. The associativity
  of item 1's cut carries the product state to the physical model (`physAux`), its inverse
  `unassoc` carries it back (`unassoc_W_physAux`), and item 1's distance is the same number on
  both (`norm_evec_physSwap_sub_physAux`).
* **Bob's half is Alice's at the mirror, relative to the same state.** The mirror's physical model
  is the physical model of the exchanged players, and the exchange of the blocks of registers
  (`blockSwapIso`) carries the product state, the swapped physical state
  (`mirror_physSwap_mulVec`), `tau^W_h`'s move across the pair and the state norms to the
  mirror's. So the one product state serves both halves.

## Constants

`deltaLegs` bounds each leg of `eq:qld-unitary-5`'s triangle, `11 * deltaLegs` the display (the
Lean triangle's `11` for the paper's `9`). Item 2's bound is
`deltaItemTwo = 2 (11 deltaLegs + md/q + 2 sqrt η)` for item 1's bound `η`; at `η = etaItemOne`,
which is `O(sqrt delta_S)`, that is `O(delta_S^{1/4} + md/q)`, the paper's `delta_qld`.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). Everything is read in the
physical model `phys (Anc F m) F m d M Mi.K` of a `MirrorSimul`: the strategy's Pauli measurement
with the registers inert (`alicePauli`), conjugated by the swap unitary of the player's physical
algebra (`aliceConjPauli`), against the honest projector on the player's far half (`aliceTau`), on
the product state of item 1 carried to the physical model by the associativity of item 1's cut
(`physAux`). The matrix route regrouped the product state with an explicit equivalence of index sets
(`outerUnVec`) and moved Bob's half by the exchange of the parties on the vector (`swapVec`); here
the regroupings are the local isometries `M.assoc … (physE …)` and `unassoc`, and Bob's half is
carried by `blockSwapIso`. The swap isometry is stated in the vocabulary of `QLD.Extraction`
(`MIPRE/Background/QLD/ModelSoundness.lean`): `swapPhi aux`, a local isometry of `M` into the
register model over the extension of `M` by the padded registers in the auxiliary vector, is the
model into its physical model with the registers inert, the conjugation by the two swap unitaries
(`adV`) and `unassoc`; item 1 is the distance of the transported state to the register model's
state, and item 2 the summed squared state norms of the transported Pauli measurements minus the
honest projectors `smulKron 1 (proj (weylOf W) h)`. The constants are the matrix ones.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl OperatorMatrix
open scoped Kronecker ComplexOrder MatrixOrder InnerProductSpace

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
theorem isPVM_conj_unitary {R Λ : Type*} [Ring R] [StarRing R] [Fintype Λ] {P : Λ → R}
    (hP : IsPVMIn P) {V : R} (h1 : star V * V = 1) (h2 : V * star V = 1) :
    IsPVMIn fun a => V * P a * star V where
  star_eq a := by rw [star_mul, star_mul, star_star, hP.star_eq, ← mul_assoc]
  idem a := by
    rw [show V * P a * star V * (V * P a * star V) = V * P a * (star V * V) * P a * star V by
      simp only [mul_assoc], h1, mul_one, mul_assoc V (P a) (P a), hP.idem]
  sum_eq_one := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.sum_eq_one, mul_one, h2]
  orthogonal {a b} hab := by
    rw [show V * P a * star V * (V * P b * star V) = V * (P a * (star V * V) * P b) * star V by
      simp only [mul_assoc], h1, mul_one, hP.orthogonal hab, mul_zero, zero_mul]

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A vector of norm one is a unit vector in the `dotProduct` sense. -/
theorem unit_of_norm_evec_eq_one {N : Type*} [Fintype N] {v : N → ℂ} (h : ‖evec v‖ = 1) :
    star v ⬝ᵥ v = 1 := by
  rw [← inner_evec, inner_self_eq_norm_sq_to_K, h]
  simp

/-- **A local isometry carries Born probabilities on any vector**: on the image of the vector,
the images of the two operators have the Born probability the operators have on the vector. -/
theorem bornProb_withState_W {𝒞' 𝒜' ℬ' 𝒞'' 𝒜'' ℬ'' : Type*} [Ring 𝒞'] [StarRing 𝒞']
    [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
    [Ring 𝒞''] [StarRing 𝒞''] [Algebra ℂ 𝒞''] [Ring 𝒜''] [StarRing 𝒜''] [Algebra ℂ 𝒜'']
    [Ring ℬ''] [StarRing ℬ''] [Algebra ℂ ℬ''] {N : BipartiteModel 𝒞' 𝒜' ℬ'}
    {N' : BipartiteModel 𝒞'' 𝒜'' ℬ''} (Φ : BipartiteModel.LocalIsometry N N') (v : N.H)
    (a : 𝒜') (b : ℬ') :
    (N'.withState (Φ.W v)).bornProb (Φ.ΦA a) (Φ.ΦB b) = (N.withState v).bornProb a b := by
  show (⟪Φ.W v, N'.π (N'.πA (Φ.ΦA a) * N'.πB (Φ.ΦB b)) (Φ.W v)⟫_ℂ).re
    = (⟪v, N.π (N.πA a * N.πB b) v⟫_ℂ).re
  rw [Φ.intertwine, LinearIsometry.inner_map_map]

end Generic

/-! ## The objects item 2 is about -/

section Physical

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ}

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

variable (Mi : MirrorSimul M S δ)

/-- **Alice's total Pauli measurement** `M^{(Pauli,W)}_h`, its outcomes the cube data `h` the
answer reports, on her physical registers with the registers inert. An answer that is not a
well-formed Pauli answer is read as `h = 0` by `rdPauliVec`; the paper assumes well-formed
answers, and this is a relabelling of outcomes, not a restriction. -/
def alicePauli (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  (physInert (Anc F m) F m d M Mi.K).ΦA (((S.PA (.pauli W)).map rdPauliVec).op h)

/-- **Bob's**, on his. -/
def bobPauli (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  (physInert (Anc F m) F m d M Mi.K).ΦB (((S.PB (.pauli W)).map rdPauliVec).op h)

/-- **Alice's conjugated Pauli measurement** `V_A M^{(Pauli,W)}_h V_A^dagger`. -/
def aliceConjPauli (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  Mi.aliceSwap * Mi.alicePauli W h * star Mi.aliceSwap

/-- **Bob's** `V_B M^{(Pauli,W)}_h V_B^dagger`. -/
def bobConjPauli (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  Mi.bobSwap * Mi.bobPauli W h * star Mi.bobSwap

/-- **The honest Pauli projector `tau^W_h` on the far half `A''` of Alice's pair**. -/
def aliceTau (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  compHom (smulKron 1 (proj (weylOf W) h))

/-- **And on the far half `B''` of Bob's.** -/
def bobTau (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  compHom (smulKron 1 (proj (weylOf W) h))

theorem isPVM_alicePauli (W : Bas) : IsPVMIn (Mi.alicePauli W) :=
  (POVMIn.isPVMIn_map (S.projA _) rdPauliVec).pushforward
    (physInert (Anc F m) F m d M Mi.K).ΦA_one

theorem isPVM_bobPauli (W : Bas) : IsPVMIn (Mi.bobPauli W) :=
  (POVMIn.isPVMIn_map (S.projB _) rdPauliVec).pushforward
    (physInert (Anc F m) F m d M Mi.K).ΦB_one

theorem isPVM_aliceConjPauli (W : Bas) : IsPVMIn (Mi.aliceConjPauli W) :=
  isPVM_conj_unitary (Mi.isPVM_alicePauli W) Mi.aliceSwap_conjTranspose_mul
    Mi.aliceSwap_mul_conjTranspose

theorem isPVM_bobConjPauli (W : Bas) : IsPVMIn (Mi.bobConjPauli W) :=
  isPVM_conj_unitary (Mi.isPVM_bobPauli W) Mi.bobSwap_conjTranspose_mul
    Mi.bobSwap_mul_conjTranspose

theorem isPVM_aliceTau (W : Bas) : IsPVMIn (Mi.aliceTau W) :=
  (IsPVMIn.smulKron_one (R := Matrix (PadAnc F m d Mi.K × Anc F m)
    (PadAnc F m d Mi.K × Anc F m) 𝒜) (isPVM_proj (isWeylFamily_weylOf W)).toIn).pushforward
    compHom_one

theorem isPVM_bobTau (W : Bas) : IsPVMIn (Mi.bobTau W) :=
  (IsPVMIn.smulKron_one (R := Matrix (PadAnc F m d Mi.K × Anc F m)
    (PadAnc F m d Mi.K × Anc F m) ℬ) (isPVM_proj (isWeylFamily_weylOf W)).toIn).pushforward
    compHom_one

/-- **Alice's conjugated Pauli measurement, coarse-grained along `g_h(u)`, is the conjugated
`M^{(Pauli,W)}_{[g_h(u) = a]}`.** -/
theorem sum_aliceConjPauli_fibre (hd : 1 ≤ d) (W : Bas) (u : Point F m) (a : F) :
    ∑ h ∈ univ.filter fun h => (ancPoly (d := d) h).eval u = a, Mi.aliceConjPauli W h
      = Mi.aliceSwap * (physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a)
        * star Mi.aliceSwap := by
  rw [Finset.filter_congr fun h _ => by rw [ancPoly_eval hd]]
  simp only [aliceConjPauli, alicePauli]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum]
  have hY : ((S.PA (.pauli W)).map rdPauliVec).map (fun k => dotF k (indVec u))
      = pauliAtPOVM S.PA W u := by
    rw [POVMIn.map_map, pauliAtPOVM, show (fun a => dotF (rdPauliVec a) (indVec u)) = rdPauli u
      from funext fun a => (rdPauli_eq_dotF u a).symm]
  rw [← hY, POVMIn.map_op]

/-- **The honest projectors, coarse-grained along `g_h(u)`, are the syndrome projector, which is
Bob's exact Pauli measurement conjugated by his swap unitary** (`eq:qld-unitary-6`). -/
theorem sum_bobTau_fibre (hd : 1 ≤ d) (W : Bas) (u : Point F m) (a : F) :
    ∑ h ∈ univ.filter fun h => (ancPoly (d := d) h).eval u = a, Mi.bobTau W h
      = Mi.bobSwap * Mi.bobMTilde W (indVec u) a * star Mi.bobSwap := by
  rw [Finset.filter_congr fun h _ => by rw [ancPoly_eval hd], Mi.bobSwap_conj_bobMTilde]
  simp only [bobTau]
  rw [← map_sum, ← smulKron_sum_right]
  rfl

/-- **Alice's `(Pauli, W)` measurement read at `u`, against Bob's exact Pauli measurement, on the
physical model, is the same pair on the physical model of the exchanged players** --- where Bob's
`M~` is the first player's `mTildeAt` of the second cut and Alice's reading is the second player's,
which is the orientation `eq:qld-unitary-5` is proved in. -/
theorem bornProb_physVec_pauli_bobMTilde (W : Bas) (u : Point F m) (a : F) :
    (phys (Anc F m) F m d M Mi.K).bornProb
        ((physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a))
        (Mi.bobMTilde W (indVec u) a)
      = (phys (Anc F m) F m d M.swap Mi.K).bornProb (compHom (Mi.second.mTildeAt W u a))
          ((physInert (Anc F m) F m d M.swap Mi.K).ΦB ((pauliAtPOVM S.PA W u).op a)) :=
  (phys_swap_bornProb _ _).symm

set_option maxHeartbeats 1000000 in
/-- **`eq:qld-unitary-5`, on the physical state.** Alice's `(Pauli, W)` measurement read at the
sampled point agrees with Bob's exact Pauli measurement at that point's encoding, to within
`11 δ'`: this is `inconsistency_mTilde_pauli_le_of_win` at the second cut, whose hypothesis is
item 1 of `lem:qld-exact-paulis` there. -/
theorem sum_bornProb_physVec_ge {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (W : Bas) :
    1 - 11 * deltaLegs δ ε m d (Fintype.card F)
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M Mi.K).bornProb
          ((physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a))
          (Mi.bobMTilde W (indVec u) a) := by
  have hfail' : 1 - (S.swap (qldGame (d := d) hm)).value ≤ ε := povmValue_swapped_le hfail
  have hmt := Mi.second.inconsistency_mTilde_le hfail' hd W
  have hsq : 0 ≤ Real.sqrt (688 * ε) := Real.sqrt_nonneg _
  have hmd : (0 : ℝ) ≤ (m : ℝ) * d / Fintype.card F := by positivity
  have hle : δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F)
      ≤ deltaLegs δ ε m d (Fintype.card F) := by
    rw [deltaLegs]
    linarith
  have h86 : 86 * ε ≤ deltaLegs δ ε m d (Fintype.card F) := by
    rw [deltaLegs]
    linarith
  have hinc := Mi.second.inconsistency_mTilde_pauli_le_of_win hfail' W h86 (le_trans hmt hle)
  have hdiag := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) Mi.second.mVec_unit
    (fun u => Mi.second.mTildePOVM W u)
    (fun u => (pauliAtPOVM (S.swap (qldGame (d := d) hm)).PB W u).pushforward
      (physInert (Anc F m) F m d M.swap Mi.K).ΦB (physInert (Anc F m) F m d M.swap Mi.K).ΦB_one)
  have hsum : (∑ u, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M.swap Mi.K).bornProb
        ((Mi.second.mTildePOVM W u).op a)
        (((pauliAtPOVM (S.swap (qldGame (d := d) hm)).PB W u).pushforward
          (physInert (Anc F m) F m d M.swap Mi.K).ΦB
          (physInert (Anc F m) F m d M.swap Mi.K).ΦB_one).op a))
      = ∑ u, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M Mi.K).bornProb
          ((physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a))
          (Mi.bobMTilde W (indVec u) a) :=
    Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ =>
      (Mi.bornProb_physVec_pauli_bobMTilde W u a).symm)
  rw [hsum] at hdiag
  linarith

set_option maxHeartbeats 1000000 in
/-- **A fibred agreement, carried from the physical state to a nearby one.** On a state `Δ`
within `r` of the swapped physical state, a pair of projective families conjugated by the two swap
unitaries reads what the bare pair reads on the physical state, up to `2 r`: the conjugation moves
onto the state, where it undoes the swap, and the outcome sum is one projection, so a
contraction (`StateModel.abs_qform_withState_sub_qform_le`). -/
theorem sum_bornProb_conj_ge_of_close {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {Y : Λ → Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜}
    {Z : Λ → Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ}
    (hY : IsPVMIn Y) (hZ : IsPVMIn Z) (Δ : (phys (Anc F m) F m d M Mi.K).H) (hΔ : ‖Δ‖ = 1)
    {r : ℝ} (hr : ‖(phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ
      - Δ‖ ≤ r) :
    (∑ a, (phys (Anc F m) F m d M Mi.K).bornProb (Y a) (Z a)) - 2 * r
      ≤ ∑ a, ((phys (Anc F m) F m d M Mi.K).withState Δ).bornProb
          (Mi.aliceSwap * Y a * star Mi.aliceSwap) (Mi.bobSwap * Z a * star Mi.bobSwap) := by
  -- the state, with the swap undone
  obtain ⟨Δ', hΔ'def⟩ : ∃ Δ' : (phys (Anc F m) F m d M Mi.K).H,
      Δ' = (phys (Anc F m) F m d M Mi.K).π (star Mi.physSwap) Δ := ⟨_, rfl⟩
  have hiso : star (star Mi.physSwap) * star Mi.physSwap = 1 := by
    rw [star_star, Mi.physSwap_mul_conjTranspose]
  have hWΔ' : Mi.adV.W Δ' = Δ := by
    rw [adV_W, hΔ'def, ← π_mul_apply (phys (Anc F m) F m d M Mi.K).toStateModel,
      Mi.physSwap_mul_conjTranspose, map_one, one_apply_eq_self]
  -- the outcome sum, as one operator, a projection
  obtain ⟨O, hOdef⟩ : ∃ O, O = ∑ a, (phys (Anc F m) F m d M Mi.K).πA (Y a)
      * (phys (Anc F m) F m d M Mi.K).πB (Z a) := ⟨_, rfl⟩
  have hphys : ∑ a, (phys (Anc F m) F m d M Mi.K).bornProb (Y a) (Z a)
      = (phys (Anc F m) F m d M Mi.K).qform O := by
    rw [hOdef, StateModel.qform_sum]
    rfl
  have hconj : ∑ a, ((phys (Anc F m) F m d M Mi.K).withState Δ).bornProb
        (Mi.aliceSwap * Y a * star Mi.aliceSwap) (Mi.bobSwap * Z a * star Mi.bobSwap)
      = ((phys (Anc F m) F m d M Mi.K).withState Δ').qform O := by
    rw [hOdef, StateModel.qform_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hWΔ', ← adV_ΦA, ← adV_ΦB, bornProb_withState_W]
    rfl
  have hbnd : (phys (Anc F m) F m d M Mi.K).Bnd O 1 := by
    rw [hOdef]
    exact StateModel.bnd_one_of_isStarProjection _
      ((phys (Anc F m) F m d M Mi.K).isStarProjection_diag hY hZ)
  -- and the two states are close
  have hnorm : ‖Δ'‖ = 1 := by
    rw [hΔ'def, Op.norm_apply_of_isometry
      ((phys (Anc F m) F m d M Mi.K).star_π_mul_self hiso), hΔ]
  have hdist : ‖Δ' - (phys (Anc F m) F m d M Mi.K).ψ‖ ≤ r := by
    have heq : Δ' - (phys (Anc F m) F m d M Mi.K).ψ
        = (phys (Anc F m) F m d M Mi.K).π (star Mi.physSwap)
          (Δ - (phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ) := by
      rw [map_sub, hΔ'def, ← π_mul_apply (phys (Anc F m) F m d M Mi.K).toStateModel,
        Mi.physSwap_conjTranspose_mul, map_one, one_apply_eq_self]
    rw [heq, Op.norm_apply_of_isometry ((phys (Anc F m) F m d M Mi.K).star_π_mul_self hiso),
      norm_sub_rev]
    exact hr
  have htr : |((phys (Anc F m) F m d M Mi.K).withState Δ').qform O
      - (phys (Anc F m) F m d M Mi.K).qform O|
        ≤ 2 * 1 * ‖Δ' - (phys (Anc F m) F m d M Mi.K).ψ‖ :=
    (phys (Anc F m) F m d M Mi.K).abs_qform_withState_sub_qform_le Δ' zero_le_one hbnd
      hnorm.le Mi.physVec_unit.le
  rw [hphys, hconj]
  have := (abs_le.mp htr).1
  linarith

/-- **Display `eq:qld-unitary-9` and the calculation after it**: on a state `Δ` within `r` of
the swapped physical state, the conjugated Pauli measurement read at the sampled point agrees with
Bob's conjugated exact Pauli measurement to within `11 δ' + 2 r`, on average over the point. The
`11 δ'` is `eq:qld-unitary-5`; the `2 r` is the transport across item 1. -/
theorem sum_bornProb_fibre_ge {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (Δ : (phys (Anc F m) F m d M Mi.K).H) (hΔ : ‖Δ‖ = 1) {r : ℝ}
    (hr : ‖(phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ - Δ‖ ≤ r)
    (W : Bas) :
    1 - 11 * deltaLegs δ ε m d (Fintype.card F) - 2 * r
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F, ((phys (Anc F m) F m d M Mi.K).withState Δ).bornProb
          (Mi.aliceSwap * (physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a)
            * star Mi.aliceSwap)
          (Mi.bobSwap * Mi.bobMTilde W (indVec u) a * star Mi.bobSwap) := by
  have hphys := Mi.sum_bornProb_physVec_ge hfail hd hδ hε W
  have hterm : ∀ u : Point F m,
      uniform (Point F m) u * ((∑ a : F, (phys (Anc F m) F m d M Mi.K).bornProb
          ((physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a))
          (Mi.bobMTilde W (indVec u) a)) - 2 * r)
      ≤ uniform (Point F m) u * ∑ a : F, ((phys (Anc F m) F m d M Mi.K).withState Δ).bornProb
          (Mi.aliceSwap * (physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a)
            * star Mi.aliceSwap)
          (Mi.bobSwap * Mi.bobMTilde W (indVec u) a * star Mi.bobSwap) := fun u =>
    mul_le_mul_of_nonneg_left
      (Mi.sum_bornProb_conj_ge_of_close
        ((POVMIn.isPVMIn_map (S.projA _) _).pushforward (physInert (Anc F m) F m d M Mi.K).ΦA_one)
        (Mi.isPVM_bobMTilde W (indVec u)) Δ hΔ hr)
      (uniform_nonneg (Point F m) u)
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) => hterm u
  have hsplit : ∑ u : Point F m, uniform (Point F m) u * ((∑ a : F,
        (phys (Anc F m) F m d M Mi.K).bornProb
          ((physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a))
          (Mi.bobMTilde W (indVec u) a)) - 2 * r)
      = (∑ u : Point F m, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M Mi.K).bornProb
          ((physInert (Anc F m) F m d M Mi.K).ΦA ((pauliAtPOVM S.PA W u).op a))
          (Mi.bobMTilde W (indVec u) a)) - 2 * r := by
    rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => mul_sub (uniform (Point F m) u) _ _,
      Finset.sum_sub_distrib, ← Finset.sum_mul, sum_uniform_eq_one, one_mul]
  rw [hsplit] at hsum
  linarith

set_option maxHeartbeats 1000000 in
/-- **Item 2 of `lem:qld-swap` for Alice, relative to any state that carries `|EPR_q>^M` on the
two halves of the pair and is close to the swapped physical state.** The summed state-dependent
distance between `V_A M^{(Pauli,W)}_h V_A^dagger` and `Id ⊗ tau^W_h` on `A''` is at most
`2 (11 δ' + md/q + 2 r)`.

The chain is the paper's. Both families are projective, so the deviation is twice the deficit of
their agreement (`eq:qld-unitary-7`); `hmove` carries `tau^W_h` from `A''` to `B''`, making the
agreement a bipartite Born probability; coarse-graining along `g_h(u)` costs `md/q`
(`eq:qld-unitary-8`), and the coarse-grained honest projector is Bob's conjugated exact Pauli
measurement (`eq:qld-unitary-6`, `eq:qld-unitary-9`); the rest is `sum_bornProb_fibre_ge`. -/
theorem sum_snorm_sq_aliceConjPauli_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (Δ : (phys (Anc F m) F m d M Mi.K).H) (hΔ : ‖Δ‖ = 1)
    (hmove : ∀ (W : Bas) (h : Anc F m),
      (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceTau W h)) Δ
        = (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πB (Mi.bobTau W h)) Δ)
    {r : ℝ}
    (hr : ‖(phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ - Δ‖ ≤ r)
    (W : Bas) :
    ∑ h : Anc F m, ((phys (Anc F m) F m d M Mi.K).withState Δ).snorm
        ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceConjPauli W h)
          - (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceTau W h)) ^ 2
      ≤ 2 * (11 * deltaLegs δ ε m d (Fintype.card F) + (m : ℝ) * d / Fintype.card F
        + 2 * r) := by
  refine sum_snorm_sq_sub_le_of_agree (M := ((phys (Anc F m) F m d M Mi.K).withState Δ).toStateModel)
    hΔ ((Mi.isPVM_aliceConjPauli W).map (phys (Anc F m) F m d M Mi.K).πA)
    ((Mi.isPVM_aliceTau W).map (phys (Anc F m) F m d M Mi.K).πA) ?_
  have hswap : ∀ h : Anc F m,
      ((phys (Anc F m) F m d M Mi.K).withState Δ).qform
          ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceConjPauli W h)
            * (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceTau W h))
        = ((phys (Anc F m) F m d M Mi.K).withState Δ).bornProb (Mi.aliceConjPauli W h)
          (Mi.bobTau W h) := by
    intro h
    show (⟪Δ, (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πA
          (Mi.aliceConjPauli W h) * (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceTau W h)) Δ⟫_ℂ).re
      = (⟪Δ, (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πA
          (Mi.aliceConjPauli W h) * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobTau W h)) Δ⟫_ℂ).re
    rw [π_mul_apply (phys (Anc F m) F m d M Mi.K).toStateModel,
      π_mul_apply (phys (Anc F m) F m d M Mi.K).toStateModel, hmove W h]
  have hfib := sum_uniform_bornProb_fibre_le (M := (phys (Anc F m) F m d M Mi.K).withState Δ) hΔ
    (Mi.isPVM_aliceConjPauli W) (Mi.isPVM_bobTau W) (enc := ancPoly (d := d))
    (fun h h' hne => ancPoly_toMv_ne hd hne)
  simp only [Mi.sum_aliceConjPauli_fibre hd, Mi.sum_bobTau_fibre hd] at hfib
  have hagree := Mi.sum_bornProb_fibre_ge hfail hd hδ hε Δ hΔ hr W
  rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) => hswap h]
  linarith

/-! ### The product state of item 1 -/

/-- **The product state `|aux> ⊗ |EPR_q>^M` of item 1, read on the physical model**: the
associativity of item 1's cut, with each party's far half back among its physical registers. -/
def physAux (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) : (phys (Anc F m) F m d M Mi.K).H :=
  (M.assoc (padE (Anc F m) F m d Mi.K) (Introspection.registerEPR (Anc F m))
    (physE (Anc F m) F m d Mi.K)).W (Mi.tgtState aux)

/-- **`unassoc` undoes the associativity**, so it carries the product state back to item 1's
cut. -/
theorem unassoc_W_physAux (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    (unassoc (Anc F m) F m d M Mi.K).W (Mi.physAux aux) = Mi.tgtState aux :=
  (M.expand (padE (Anc F m) F m d Mi.K)).expand_ext (Introspection.registerEPR (Anc F m))
    fun _ => M.expand_ext (padE (Anc F m) F m d Mi.K) fun _ => rfl

theorem norm_evec_physAux (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    ‖Mi.physAux aux‖ = ‖aux‖ := by
  rw [physAux, LinearIsometry.norm_map,
    ← LinearIsometryEquiv.norm_map ((M.expand (padE (Anc F m) F m d Mi.K)).ampl
      (Introspection.registerEPR (Anc F m))), Mi.ampl_tgtState, norm_auxVec]

/-- **Item 1's distance, read on the physical model.** -/
theorem norm_evec_physSwap_sub_physAux (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    ‖(phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ
        - Mi.physAux aux‖
      = ‖Mi.endState - Mi.tgtState aux‖ := by
  have h : (phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ
      = (M.assoc (padE (Anc F m) F m d Mi.K) (Introspection.registerEPR (Anc F m))
          (physE (Anc F m) F m d Mi.K)).W Mi.endState :=
    (assoc_W_unassocIsometry _).symm
  rw [h, physAux, ← map_sub, LinearIsometry.norm_map]

/-- **On the product state, `tau^W_h` on `A''` is `tau^W_h` on `B''`**: the last line of
`eq:qld-unitary-7`. The register model of item 1's cut carries the maximally entangled pair on
`(A'', B'')`, the Weyl families are symmetric matrices, so their spectral projectors move across
the pair (`reg_mirror`), and the associativity carries the move to the physical model. -/
theorem aliceTau_mulVec_physAux (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) (W : Bas)
    (h : Anc F m) :
    (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceTau W h))
        (Mi.physAux aux)
      = (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πB (Mi.bobTau W h))
        (Mi.physAux aux) := by
  have hA := (M.assoc (padE (Anc F m) F m d Mi.K) (Introspection.registerEPR (Anc F m))
    (physE (Anc F m) F m d Mi.K)).intertwineA (smulKron 1 (proj (weylOf W) h)) (Mi.tgtState aux)
  have hB := (M.assoc (padE (Anc F m) F m d Mi.K) (Introspection.registerEPR (Anc F m))
    (physE (Anc F m) F m d Mi.K)).intertwineB (smulKron 1 (proj (weylOf W) h)) (Mi.tgtState aux)
  have hmir := ((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg_mirror
    (I := Anc F m) (proj (weylOf W) h)
  rw [proj_weylOf_transpose] at hmir
  have hmir' : (tgt (Anc F m) F m d M Mi.K).π ((tgt (Anc F m) F m d M Mi.K).πA
        (smulKron 1 (proj (weylOf W) h))) (Mi.tgtState aux)
      = (tgt (Anc F m) F m d M Mi.K).π ((tgt (Anc F m) F m d M Mi.K).πB
        (smulKron 1 (proj (weylOf W) h))) (Mi.tgtState aux) := hmir
  exact hA.trans ((congrArg _ hmir').trans hB.symm)

set_option maxHeartbeats 1000000 in
/-- **Item 2 of `lem:qld-swap`, Alice's half**, relative to any auxiliary state for which item 1
holds with bound `η`: conjugation by `V_A` carries the strategy's total Pauli measurement
`M^{(Pauli,W)}_h` to `Id ⊗ tau^W_h` on `A''`, within `deltaItemTwo` in the state-dependent
distance relative to `|aux> ⊗ |EPR_q>^M`. -/
theorem sum_snorm_sq_alice_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) (haux : ‖aux‖ = 1) {η : ℝ}
    (hη : ‖Mi.endState - Mi.tgtState aux‖ ^ 2 ≤ η) (W : Bas) :
    ∑ h : Anc F m, ((phys (Anc F m) F m d M Mi.K).withState (Mi.physAux aux)).snorm
        ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceConjPauli W h)
          - (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceTau W h)) ^ 2
      ≤ deltaItemTwo δ ε m d (Fintype.card F) η := by
  have hr : ‖(phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ
      - Mi.physAux aux‖ ≤ Real.sqrt η := by
    rw [Mi.norm_evec_physSwap_sub_physAux]
    exact Real.le_sqrt_of_sq_le hη
  exact Mi.sum_snorm_sq_aliceConjPauli_le hfail hd hδ hε (Mi.physAux aux)
    (by rw [Mi.norm_evec_physAux, haux]) (Mi.aliceTau_mulVec_physAux aux) hr W

/-! ### Bob's half, through the mirror -/

/-- **The mirror's swapped physical state is the swapped physical state**, carried by the
exchange of the blocks of registers: the mirror's swap unitaries are Bob's and Alice's in the
other order. -/
theorem mirror_physSwap_mulVec :
    (blockSwapIso (Anc F m) F m d M Mi.K).W
        ((phys (Anc F m) F m d M.swap Mi.K).π
          ((phys (Anc F m) F m d M.swap Mi.K).πA Mi.bobSwap
            * (phys (Anc F m) F m d M.swap Mi.K).πB Mi.aliceSwap)
          (phys (Anc F m) F m d M.swap Mi.K).ψ)
      = (phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ := by
  have h := (blockSwapIso (Anc F m) F m d M Mi.K).toLocalIsometry.intertwine Mi.bobSwap
    Mi.aliceSwap (phys (Anc F m) F m d M.swap Mi.K).ψ
  rw [BipartiteModel.Iso.toLocalIsometry_W, BipartiteModel.Iso.toLocalIsometry_W,
    (blockSwapIso (Anc F m) F m d M Mi.K).W_ψ] at h
  rw [← h]
  show (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πB Mi.bobSwap
      * (phys (Anc F m) F m d M Mi.K).πA Mi.aliceSwap) (phys (Anc F m) F m d M Mi.K).ψ
    = (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πA Mi.aliceSwap
      * (phys (Anc F m) F m d M Mi.K).πB Mi.bobSwap) (phys (Anc F m) F m d M Mi.K).ψ
  exact congrArg (fun T => (phys (Anc F m) F m d M Mi.K).π T (phys (Anc F m) F m d M Mi.K).ψ)
    ((phys (Anc F m) F m d M Mi.K).commute Mi.aliceSwap Mi.bobSwap).eq.symm

/-- A state norm of the first player of the physical model of the exchanged players, on any
vector, is the second player's on the physical model, on the exchanged vector. -/
theorem snorm_withState_blockSwap (w : (phys (Anc F m) F m d M.swap Mi.K).H)
    (X : Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ) :
    ((phys (Anc F m) F m d M.swap Mi.K).withState w).snorm
        ((phys (Anc F m) F m d M.swap Mi.K).πA X)
      = ((phys (Anc F m) F m d M Mi.K).withState ((blockSwapIso (Anc F m) F m d M Mi.K).W w)).snorm
        ((phys (Anc F m) F m d M Mi.K).πB X) := by
  show ‖(phys (Anc F m) F m d M.swap Mi.K).π ((phys (Anc F m) F m d M.swap Mi.K).πA X) w‖
    = ‖((phys (Anc F m) F m d M Mi.K).swap).π (((phys (Anc F m) F m d M Mi.K).swap).πA
        ((blockSwapIso (Anc F m) F m d M Mi.K).ΦA X)) ((blockSwapIso (Anc F m) F m d M Mi.K).W w)‖
  rw [(blockSwapIso (Anc F m) F m d M Mi.K).intertwineA, LinearIsometryEquiv.norm_map]

set_option maxHeartbeats 4000000 in
/-- **Item 2 of `lem:qld-swap`, Bob's half, relative to the same auxiliary state.** Alice's half
at the mirror, whose first party is Bob, read on the physical model of the exchanged players at
the product state carried there by the exchange of the blocks of registers: the mirror's swapped
physical state is this one's (`mirror_physSwap_mulVec`), and the exchange carries `tau^W_h`'s move
across the pair to the mirror's. So the one product state serves both halves, which is what the
paper's item 2 asks. -/
theorem sum_snorm_sq_bob_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) (haux : ‖aux‖ = 1) {η : ℝ}
    (hη : ‖Mi.endState - Mi.tgtState aux‖ ^ 2 ≤ η) (W : Bas) :
    ∑ h : Anc F m, ((phys (Anc F m) F m d M Mi.K).withState (Mi.physAux aux)).snorm
        ((phys (Anc F m) F m d M Mi.K).πB (Mi.bobConjPauli W h)
          - (phys (Anc F m) F m d M Mi.K).πB (Mi.bobTau W h)) ^ 2
      ≤ deltaItemTwo δ ε m d (Fintype.card F) η := by
  have hr : ‖(phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ
      - Mi.physAux aux‖ ≤ Real.sqrt η := by
    rw [Mi.norm_evec_physSwap_sub_physAux]
    exact Real.le_sqrt_of_sq_le hη
  -- the product state, on the physical model of the exchanged players
  obtain ⟨Δ', hΔ'⟩ : ∃ Δ' : (phys (Anc F m) F m d M.swap Mi.K).H,
      (blockSwapIso (Anc F m) F m d M Mi.K).W Δ' = Mi.physAux aux :=
    ⟨(blockSwapIso (Anc F m) F m d M Mi.K).W.symm (Mi.physAux aux),
      LinearIsometryEquiv.apply_symm_apply _ _⟩
  have hΔn : ‖Δ'‖ = 1 :=
    calc ‖Δ'‖ = ‖(blockSwapIso (Anc F m) F m d M Mi.K).W Δ'‖ :=
          ((blockSwapIso (Anc F m) F m d M Mi.K).W.norm_map Δ').symm
      _ = ‖Mi.physAux aux‖ := congrArg (fun x => ‖x‖) hΔ'
      _ = 1 := by rw [Mi.norm_evec_physAux, haux]
  have hr' : ‖(phys (Anc F m) F m d M.swap Mi.K).π
        ((phys (Anc F m) F m d M.swap Mi.K).πA Mi.bobSwap
          * (phys (Anc F m) F m d M.swap Mi.K).πB Mi.aliceSwap)
        (phys (Anc F m) F m d M.swap Mi.K).ψ - Δ'‖ ≤ Real.sqrt η := by
    have e : (blockSwapIso (Anc F m) F m d M Mi.K).W ((phys (Anc F m) F m d M.swap Mi.K).π
          ((phys (Anc F m) F m d M.swap Mi.K).πA Mi.bobSwap
            * (phys (Anc F m) F m d M.swap Mi.K).πB Mi.aliceSwap)
          (phys (Anc F m) F m d M.swap Mi.K).ψ - Δ')
        = (phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ
          - Mi.physAux aux := by
      rw [LinearIsometryEquiv.map_sub, Mi.mirror_physSwap_mulVec, hΔ']
      rfl
    calc _ = ‖(blockSwapIso (Anc F m) F m d M Mi.K).W ((phys (Anc F m) F m d M.swap Mi.K).π
            ((phys (Anc F m) F m d M.swap Mi.K).πA Mi.bobSwap
              * (phys (Anc F m) F m d M.swap Mi.K).πB Mi.aliceSwap)
            (phys (Anc F m) F m d M.swap Mi.K).ψ - Δ')‖ :=
          ((blockSwapIso (Anc F m) F m d M Mi.K).W.norm_map _).symm
      _ = ‖(phys (Anc F m) F m d M Mi.K).π Mi.physSwap (phys (Anc F m) F m d M Mi.K).ψ
            - Mi.physAux aux‖ := congrArg (fun x => ‖x‖) e
      _ ≤ Real.sqrt η := hr
  have hmove : ∀ (W : Bas) (h : Anc F m),
      (phys (Anc F m) F m d M.swap Mi.K).π
          ((phys (Anc F m) F m d M.swap Mi.K).πA (Mi.bobTau W h)) Δ'
        = (phys (Anc F m) F m d M.swap Mi.K).π
          ((phys (Anc F m) F m d M.swap Mi.K).πB (Mi.aliceTau W h)) Δ' := by
    intro W h
    apply (blockSwapIso (Anc F m) F m d M Mi.K).W.injective
    rw [← (blockSwapIso (Anc F m) F m d M Mi.K).intertwineA,
      ← (blockSwapIso (Anc F m) F m d M Mi.K).intertwineB, hΔ']
    exact (Mi.aliceTau_mulVec_physAux aux W h).symm
  have hcore := Mi.mirror.sum_snorm_sq_aliceConjPauli_le (povmValue_swapped_le hfail) hd hδ hε
    Δ' hΔn hmove hr' W
  have hcore' : ∑ h : Anc F m, ((phys (Anc F m) F m d M.swap Mi.K).withState Δ').snorm
        ((phys (Anc F m) F m d M.swap Mi.K).πA (Mi.bobConjPauli W h - Mi.bobTau W h)) ^ 2
      ≤ deltaItemTwo δ ε m d (Fintype.card F) η := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun h _ => ?_)) hcore
    rw [map_sub]
    rfl
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun h _ => ?_)) hcore'
  rw [Mi.snorm_withState_blockSwap, hΔ', map_sub]

/-! ### The swap isometry -/

/-- **The swap isometry** of `lem:qld-swap`, in the vocabulary of `QLD.Extraction`: the model into
its physical model with the registers inert, the conjugation by the two swap unitaries (`adV`), and
the regrouping into item 1's cut (`unassoc`), landing in the register model over the extension of
`M` by the padded registers in the auxiliary vector `aux`. The players' operators move as
`X ↦ V X V†` on the physical registers, read as block matrices over the far half of the pair. -/
def swapPhi (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    BipartiteModel.LocalIsometry M
      (((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)) :=
  ((unassoc (Anc F m) F m d M Mi.K).comp
    (Mi.adV.comp (M.inert (physE (Anc F m) F m d Mi.K) norm_physE))).toWithState (Mi.tgtState aux)

/-- The swap isometry carries the state to the state item 1 is about. -/
theorem swapPhi_W_ψ (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    (Mi.swapPhi aux).W M.ψ = Mi.endState := rfl

@[simp] theorem swapPhi_ΦA (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) (X : 𝒜) :
    (Mi.swapPhi aux).ΦA X
      = uncompHom (Mi.aliceSwap * (physInert (Anc F m) F m d M Mi.K).ΦA X * star Mi.aliceSwap) :=
  rfl

@[simp] theorem swapPhi_ΦB (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) (Y : ℬ) :
    (Mi.swapPhi aux).ΦB Y
      = uncompHom (Mi.bobSwap * (physInert (Anc F m) F m d M Mi.K).ΦB Y * star Mi.bobSwap) :=
  rfl

/-- **The first player's error of the swap isometry, read on the physical model**: the summand
of item 2 for Alice. -/
theorem stateSqNorm_swapPhi_alice (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) (W : Bas)
    (h : Anc F m) :
    (((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).stateSqNorm
        ((Mi.swapPhi aux).ΦA (((S.PA (.pauli W)).map rdPauliVec).op h)
          - smulKron 1 (proj (weylOf W) h))
      = ((phys (Anc F m) F m d M Mi.K).withState (Mi.physAux aux)).snorm
          ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceConjPauli W h)
            - (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceTau W h)) ^ 2 := by
  have hX : (Mi.swapPhi aux).ΦA (((S.PA (.pauli W)).map rdPauliVec).op h)
        - smulKron 1 (proj (weylOf W) h)
      = (unassoc (Anc F m) F m d M Mi.K).ΦA (Mi.aliceConjPauli W h - Mi.aliceTau W h) := by
    rw [map_sub, unassoc_ΦA, unassoc_ΦA, aliceTau, uncompHom_compHom, swapPhi_ΦA]
    rfl
  rw [hX, ← map_sub (phys (Anc F m) F m d M Mi.K).πA]
  show ‖(tgt (Anc F m) F m d M Mi.K).π ((tgt (Anc F m) F m d M Mi.K).πA
        ((unassoc (Anc F m) F m d M Mi.K).ΦA (Mi.aliceConjPauli W h - Mi.aliceTau W h)))
        (Mi.tgtState aux)‖ ^ 2
    = ‖(phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πA
        (Mi.aliceConjPauli W h - Mi.aliceTau W h)) (Mi.physAux aux)‖ ^ 2
  rw [← Mi.unassoc_W_physAux aux, (unassoc (Anc F m) F m d M Mi.K).intertwineA,
    LinearIsometry.norm_map]

/-- **The second player's error of the swap isometry, read on the physical model.** -/
theorem stateSqNorm_swapPhi_bob (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) (W : Bas)
    (h : Anc F m) :
    (((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).swap.stateSqNorm
        ((Mi.swapPhi aux).ΦB (((S.PB (.pauli W)).map rdPauliVec).op h)
          - smulKron 1 (proj (weylOf W) h))
      = ((phys (Anc F m) F m d M Mi.K).withState (Mi.physAux aux)).snorm
          ((phys (Anc F m) F m d M Mi.K).πB (Mi.bobConjPauli W h)
            - (phys (Anc F m) F m d M Mi.K).πB (Mi.bobTau W h)) ^ 2 := by
  have hX : (Mi.swapPhi aux).ΦB (((S.PB (.pauli W)).map rdPauliVec).op h)
        - smulKron 1 (proj (weylOf W) h)
      = (unassoc (Anc F m) F m d M Mi.K).ΦB (Mi.bobConjPauli W h - Mi.bobTau W h) := by
    rw [map_sub, unassoc_ΦB, unassoc_ΦB, bobTau, uncompHom_compHom, swapPhi_ΦB]
    rfl
  rw [hX, ← map_sub (phys (Anc F m) F m d M Mi.K).πB]
  show ‖(tgt (Anc F m) F m d M Mi.K).π ((tgt (Anc F m) F m d M Mi.K).πB
        ((unassoc (Anc F m) F m d M Mi.K).ΦB (Mi.bobConjPauli W h - Mi.bobTau W h)))
        (Mi.tgtState aux)‖ ^ 2
    = ‖(phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πB
        (Mi.bobConjPauli W h - Mi.bobTau W h)) (Mi.physAux aux)‖ ^ 2
  rw [← Mi.unassoc_W_physAux aux, (unassoc (Anc F m) F m d M Mi.K).intertwineB,
    LinearIsometry.norm_map]

set_option maxHeartbeats 1000000 in
/-- **`lem:qld-swap`: the swap isometry**, in the vocabulary of `QLD.Extraction`. There is an
auxiliary unit vector `aux` of the extension of `M` by the padded registers such that, for the
local isometry `swapPhi aux` of `M` into the register model over that extension in `aux`,

1. the transported state is within `etaItemOne` of the register model's state
   `|EPR_q>^M ⊗ |aux>`, in squared norm; and
2. for each basis `W`, the transported total Pauli measurements `M^{(Pauli,W)}_h` of Alice, resp.
   Bob, are within `deltaItemTwo … etaItemOne` of the honest projectors `Id ⊗ tau^W_h` on that
   player's register, in summed squared state norm on the register model's state --- the **same**
   product state for both players.

Item 1 is `exists_aux_close`; item 2 is `sum_snorm_sq_alice_le` and `sum_snorm_sq_bob_le` at the
auxiliary state it produces, read through `unassoc`. The constants are the matrix ones. -/
theorem swap_isometry {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hlt : 2 * Real.sqrt (deltaSelfCons δ ε m d (Fintype.card F))
      + 2 * deltaSelfCons δ ε m d (Fintype.card F) < 1) :
    ∃ aux : (M.expand (padE (Anc F m) F m d Mi.K)).H, ‖aux‖ = 1 ∧
      ‖(Mi.swapPhi aux).W M.ψ
          - (((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).ψ‖ ^ 2
        ≤ etaItemOne δ ε m d (Fintype.card F) ∧
      ∀ W : Bas,
        (∑ h : Anc F m,
            (((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).stateSqNorm
              ((Mi.swapPhi aux).ΦA (((S.PA (.pauli W)).map rdPauliVec).op h)
                - smulKron 1 (proj (weylOf W) h))
          ≤ deltaItemTwo δ ε m d (Fintype.card F) (etaItemOne δ ε m d (Fintype.card F))) ∧
        (∑ h : Anc F m,
            (((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).swap.stateSqNorm
              ((Mi.swapPhi aux).ΦB (((S.PB (.pauli W)).map rdPauliVec).op h)
                - smulKron 1 (proj (weylOf W) h))
          ≤ deltaItemTwo δ ε m d (Fintype.card F) (etaItemOne δ ε m d (Fintype.card F))) := by
  obtain ⟨aux, haux, hclose⟩ := Mi.exists_aux_close hfail hd hδ hε hlt
  refine ⟨aux, haux, hclose, fun W => ⟨?_, ?_⟩⟩
  · rw [Finset.sum_congr rfl fun h _ => Mi.stateSqNorm_swapPhi_alice aux W h]
    exact Mi.sum_snorm_sq_alice_le hfail hd hδ hε aux haux hclose W
  · rw [Finset.sum_congr rfl fun h _ => Mi.stateSqNorm_swapPhi_bob aux W h]
    exact Mi.sum_snorm_sq_bob_le hfail hd hδ hε aux haux hclose W

end MirrorSimul

end Physical

end MIPRE.QLD

end

end
