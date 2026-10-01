/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.SelfCons
public import MIPRE.Background.QLD.SwapEndgame

@[expose] public section

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

* **The cut.** Item 1 reads the state with the two far halves `(A'', B'')` together as one
  register and everything else as one space: item 1's cut `tgt`, into which `unassoc` regroups the
  physical registers (`MIPRE/Background/QLD/PhysModel.lean`).
* **The conjugation.** `swapU_conj_wTilde_X` and `_Z` say the swap unitary strips the pair
  measurement off the exact Pauli observable exactly, leaving the honest Weyl operator; the two
  swap unitaries together are a local isometry of the physical model (`adV`, conjugation by a
  unitary of each player), and it carries an expectation on the physical state to the conjugated
  expectation on the swapped state (`LocalIsometry.bornProb_withState`).
* **The two involutions.** Each party's exact Pauli observable is self-adjoint and squares to
  one, so its cross-party deviation and its joint expectation determine each other exactly:
  `xSqNorm = 2 - 2 bornProb`, with no inequality.

What is *not* here is item 2, the longer half, which threads these steps into a statement about
the conjugated total Pauli measurement `V M^{(Pauli,W)}_h V†`.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The swap unitaries are unitary
elements of the two players' algebras of the physical model `phys (Anc F m) F m d M Mi.K` (the two
cuts' `swapA`, flattened by `compHom`), and their product acts on the physical state as the local
isometry `adV` (`LocalIsometry.ofUnitary`). The state item 1 is about is the image of the physical
state under `adV`, regrouped into item 1's cut by `unassoc`: `endState`, a vector of the register
model `tgt` over the extension of `M` by the padded registers. The matrix route regrouped the
vector along an explicit equivalence of index sets (`outerPairEquiv`, `outerVec`); here the
regrouping is the local isometry `unassoc`, read through `qform_endVec`, and the product state of
the conclusion is the state of the register model over the extension in the auxiliary vector,
`((M.expand (padE …)).withState aux).reg (Anc F m)`. The constants are the matrix ones.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl OperatorMatrix
open scoped Kronecker ComplexOrder MatrixOrder InnerProductSpace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

section Probe

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

set_option synthInstance.maxSize 1000

/-- **Display `eq:qld-unitary-6` for the observable, at the interface.** The swap unitary strips
the pair measurement off the exact Pauli observable, leaving the honest Weyl operator on the
party's half of the pair. -/
theorem SimulPair.swapA_conj_wTildeAt [StarModule ℂ 𝒜'] (P : SimulPair M S K ι δ) (W : Bas)
    (e : F) (v : Anc F m) :
    P.swapA * P.wTildeAt W e v * star P.swapA = smulKron 1 (weylOf W (e • v)) := by
  cases W with
  | X => exact swapU_conj_wTilde_X P.SA_proj e v
  | Z => exact swapU_conj_wTilde_Z P.SA_proj e v

/-- The same at the unit scalar, which is the case the twirl reads. -/
theorem SimulPair.swapA_conj_wTildeAt_one [StarModule ℂ 𝒜'] (P : SimulPair M S K ι δ)
    (W : Bas) (v : Anc F m) :
    P.swapA * P.wTildeAt W 1 v * star P.swapA = smulKron 1 (weylOf W v) := by
  rw [P.swapA_conj_wTildeAt W 1 v, one_smul]

end Probe

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- Inverting a conjugation by a unitary. -/
theorem conj_inv_of_unitary {R : Type*} [Monoid R] [Star R] {V X Y : R}
    (h1 : star V * V = 1) (h : V * X * star V = Y) : star V * (Y * V) = X := by
  rw [← h, show star V * (V * X * star V * V) = (star V * V) * X * (star V * V) by
    simp only [mul_assoc], h1, one_mul, mul_one]

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

section Physical

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ}

set_option synthInstance.maxSize 1000

namespace MirrorSimul

variable (Mi : MirrorSimul M S δ)

/-- **Alice's swap unitary** `V_A`, on her physical registers `(A'', (Ea, A'))`: the first cut's
`swapA`, flattened. -/
def aliceSwap : Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  compHom Mi.first.swapA

theorem aliceSwap_conjTranspose_mul : star Mi.aliceSwap * Mi.aliceSwap = 1 := by
  rw [aliceSwap, ← map_star, ← map_mul, Mi.first.swapA_conjTranspose_mul, compHom_one]

theorem aliceSwap_mul_conjTranspose : Mi.aliceSwap * star Mi.aliceSwap = 1 := by
  rw [aliceSwap, ← map_star, ← map_mul, Mi.first.swapA_mul_conjTranspose, compHom_one]

/-- At the mirror, Alice's swap unitary is Bob's. -/
@[simp] theorem mirror_aliceSwap : Mi.mirror.aliceSwap = Mi.bobSwap := rfl

/-- **Display `eq:qld-unitary-6` for Alice's observable**: on her physical registers, the honest
Weyl operator on the far half `A''` of her pair. -/
theorem aliceSwap_conj_aliceWTilde (W : Bas) (v : Anc F m) :
    Mi.aliceSwap * Mi.aliceWTilde W 1 v * star Mi.aliceSwap
      = compHom (smulKron 1 (weylOf W v)) := by
  rw [aliceSwap, aliceWTilde, ← map_star, ← map_mul, ← map_mul,
    Mi.first.swapA_conj_wTildeAt_one]

/-- **And for Bob's**, on the far half `B''` of his. -/
theorem bobSwap_conj_bobWTilde (W : Bas) (v : Anc F m) :
    Mi.bobSwap * Mi.bobWTilde W 1 v * star Mi.bobSwap
      = compHom (smulKron 1 (weylOf W v)) := by
  rw [bobSwap, bobWTilde, ← map_star, ← map_mul, ← map_mul,
    Mi.second.swapA_conj_wTildeAt_one]

/-- **The two swap unitaries together**, an element of the physical model's algebra. -/
def physSwap :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  (phys (Anc F m) F m d M Mi.K).πA Mi.aliceSwap * (phys (Anc F m) F m d M Mi.K).πB Mi.bobSwap

theorem physSwap_conjTranspose_mul : star Mi.physSwap * Mi.physSwap = 1 :=
  (phys (Anc F m) F m d M Mi.K).star_πA_mul_πB_mul_self Mi.aliceSwap_conjTranspose_mul
    Mi.bobSwap_conjTranspose_mul

theorem physSwap_mul_conjTranspose : Mi.physSwap * star Mi.physSwap = 1 := by
  rw [physSwap, star_mul, ← map_star, ← map_star, mul_assoc,
    ← mul_assoc ((phys (Anc F m) F m d M Mi.K).πB Mi.bobSwap), ← map_mul,
    Mi.bobSwap_mul_conjTranspose, map_one, one_mul, ← map_mul, Mi.aliceSwap_mul_conjTranspose,
    map_one]

/-- **Conjugation by the two swap unitaries**, a local isometry of the physical model
(`LocalIsometry.ofUnitary`): the isometry is the representation of `physSwap`, and each player's
operators are conjugated by the player's swap unitary. It does not fix the physical state; the
state it produces is the one item 1 is about. -/
def adV : BipartiteModel.LocalIsometry (phys (Anc F m) F m d M Mi.K)
    (phys (Anc F m) F m d M Mi.K) :=
  BipartiteModel.LocalIsometry.ofUnitary (phys (Anc F m) F m d M Mi.K) Mi.aliceSwap Mi.bobSwap
    Mi.aliceSwap_conjTranspose_mul Mi.aliceSwap_mul_conjTranspose Mi.bobSwap_conjTranspose_mul
    Mi.bobSwap_mul_conjTranspose

@[simp] theorem adV_W (w : (phys (Anc F m) F m d M Mi.K).H) :
    Mi.adV.W w = (phys (Anc F m) F m d M Mi.K).π Mi.physSwap w := rfl

@[simp] theorem adV_ΦA (X : Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜) :
    Mi.adV.ΦA X = Mi.aliceSwap * X * star Mi.aliceSwap := rfl

@[simp] theorem adV_ΦB (Y : Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ) :
    Mi.adV.ΦB Y = Mi.bobSwap * Y * star Mi.bobSwap := rfl

/-- **The state item 1 concludes about**: the physical state after the two swap unitaries,
regrouped as item 1's cut, the two far halves `(A'', B'')` together outside. -/
def endState : (tgt (Anc F m) F m d M Mi.K).H :=
  (unassoc (Anc F m) F m d M Mi.K).W (Mi.adV.W (phys (Anc F m) F m d M Mi.K).ψ)

theorem endState_unit : ‖Mi.endState‖ = 1 :=
  endVec_unit (by rw [LinearIsometry.norm_map]; exact Mi.physVec_unit)

/-- **The product state of item 1**, as a vector of item 1's cut: the state of the register model
over the extension of `M` by the padded registers in an auxiliary vector `aux` --- the maximally
entangled pair on the two far halves `(A'', B'')`, tensored with `aux`. -/
def tgtState (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    (tgt (Anc F m) F m d M Mi.K).H :=
  (((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).ψ

/-- It is the product vector of `SwapState.lean`. -/
theorem ampl_tgtState (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    (M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m))
        (Mi.tgtState aux)
      = auxVec (F := F) (n := Fin m → Bool) aux := rfl

set_option maxHeartbeats 4000000 in
/-- **The Weyl operator on the two halves of the pair, read on that state, is the two parties'
exact Pauli observables read on the physical state.** Conjugation by the swap unitaries carries
the one to the other exactly. -/
theorem qform_endState_weyl (W : Bas) (v : Anc F m) :
    ((tgt (Anc F m) F m d M Mi.K).withState Mi.endState).bornProb
        (smulKron 1 (weylOf W v)) (smulKron 1 (weylOf W v))
      = (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceWTilde W 1 v) (Mi.bobWTilde W 1 v) := by
  rw [endState, qform_endVec, ← Mi.aliceSwap_conj_aliceWTilde W v,
    ← Mi.bobSwap_conj_bobWTilde W v]
  have h := Mi.adV.bornProb_withState (Mi.aliceWTilde W 1 v) (Mi.bobWTilde W 1 v)
  rwa [adV_ΦA, adV_ΦB] at h

/-- **A product of matrices of scalars on the two far halves, against that state**, is a Born
probability of item 1's cut. -/
theorem qform_endState_regAct (P Q : Matrix (Anc F m) (Anc F m) ℂ) :
    Op.qform ((M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m)) Mi.endState)
        (regAct (P ⊗ₖ Q))
      = ((tgt (Anc F m) F m d M Mi.K).withState Mi.endState).bornProb (smulKron 1 P)
          (smulKron 1 Q) := by
  rw [← BipartiteModel.expand_π_smulKron_one_mul (M.expand (padE (Anc F m) F m d Mi.K))
    (Introspection.registerEPR (Anc F m)) P Q]
  rfl

/-- `lem:qld-pauli-selfcons`, at that name. -/
theorem snorm_sq_wTilde_le' {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (e : F) (v : Anc F m) :
    (phys (Anc F m) F m d M Mi.K).snorm
        ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceWTilde W e v)
          - (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWTilde W e v)) ^ 2
      ≤ deltaSelfCons δ ε m d (Fintype.card F) := by
  have h := Mi.snorm_sq_wTilde_le hfail hd W e v
  rw [deltaSelfCons]
  linarith

theorem aliceWTilde_conjTranspose (W : Bas) (e : F) (v : Anc F m) :
    star (Mi.aliceWTilde W e v) = Mi.aliceWTilde W e v := by
  rw [aliceWTilde, ← map_star, Mi.first.wTildeAt_conjTranspose]

theorem aliceWTilde_mul_self (W : Bas) (e : F) (v : Anc F m) :
    Mi.aliceWTilde W e v * Mi.aliceWTilde W e v = 1 := by
  rw [aliceWTilde, ← map_mul, Mi.first.wTildeAt_mul_self, compHom_one]

theorem bobWTilde_conjTranspose (W : Bas) (e : F) (v : Anc F m) :
    star (Mi.bobWTilde W e v) = Mi.bobWTilde W e v := by
  rw [bobWTilde, ← map_star, Mi.second.wTildeAt_conjTranspose]

theorem bobWTilde_mul_self (W : Bas) (e : F) (v : Anc F m) :
    Mi.bobWTilde W e v * Mi.bobWTilde W e v = 1 := by
  rw [bobWTilde, ← map_mul, Mi.second.wTildeAt_mul_self, compHom_one]

set_option maxHeartbeats 1000000 in
/-- **The two observables' agreement, as a Born probability.** Both are self-adjoint involutions,
so their cross-party deviation and their joint expectation determine each other. -/
theorem bornProb_wTilde_ge {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (e : F) (v : Anc F m) :
    1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
      ≤ (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceWTilde W e v) (Mi.bobWTilde W e v) := by
  have hx : (phys (Anc F m) F m d M Mi.K).xSqNorm (Mi.aliceWTilde W e v) (Mi.bobWTilde W e v)
      = 2 - 2 * (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceWTilde W e v)
          (Mi.bobWTilde W e v) := by
    rw [(phys (Anc F m) F m d M Mi.K).xSqNorm_eq (Mi.aliceWTilde_conjTranspose W e v),
      BipartiteModel.stateSqNorm_eq_bornProb_one, BipartiteModel.stateSqNorm_eq_bornProb_one,
      BipartiteModel.bornProb_swap, Mi.aliceWTilde_conjTranspose W e v,
      Mi.bobWTilde_conjTranspose W e v, Mi.aliceWTilde_mul_self W e v,
      Mi.bobWTilde_mul_self W e v, (phys (Anc F m) F m d M Mi.K).bornProb_one_one Mi.physVec_unit]
    ring
  have hle : (phys (Anc F m) F m d M Mi.K).xSqNorm (Mi.aliceWTilde W e v) (Mi.bobWTilde W e v)
      ≤ deltaSelfCons δ ε m d (Fintype.card F) :=
    Mi.snorm_sq_wTilde_le' hfail hd W e v
  linarith

set_option maxHeartbeats 1000000 in
/-- **The near-invariance item 1 asks for.** The twirl is by definition the uniform average of the
per-probe Weyl operators, and at each probe that average is the two parties' exact Pauli
observables agreeing. This is the edge the blueprint's dependency graph was missing. -/
theorem qform_endState_twirl_ge {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (W : Bas) :
    1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
      ≤ (⟪(M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m)) Mi.endState,
          regAct (twirl (weylOf W))
            ((M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m))
              Mi.endState)⟫_ℂ).re := by
  have hθ := qform_bOp_twirl
    ((M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m)) Mi.endState)
    (weylOf W)
  have hterm : ∀ v : Anc F m,
      1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
        ≤ Op.qform ((M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m))
            Mi.endState) (regAct (weylOf W v ⊗ₖ weylOf W v)) := by
    intro v
    rw [Mi.qform_endState_regAct, Mi.qform_endState_weyl W v]
    exact Mi.bornProb_wTilde_ge hfail hd W 1 v
  show 1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
    ≤ Op.qform ((M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m)) Mi.endState)
        (regAct (twirl (weylOf W)))
  rw [hθ]
  calc 1 - deltaSelfCons δ ε m d (Fintype.card F) / 2
      = ∑ v : Anc F m, uniform (Anc F m) v
          * (1 - deltaSelfCons δ ε m d (Fintype.card F) / 2) := by
        rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hterm v) (uniform_nonneg (Anc F m) v)

set_option maxHeartbeats 1000000 in
/-- **Item 1 of `lem:qld-swap`, unconditional.** After the two swap unitaries the physical state,
read on item 1's cut, is close to the state of the register model over the extension of `M` by
the padded registers in an auxiliary unit vector `aux`: the maximally entangled pair on the two
far halves, tensored with `aux`. -/
theorem exists_aux_close {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε)
    (hlt : 2 * Real.sqrt (deltaSelfCons δ ε m d (Fintype.card F))
      + 2 * deltaSelfCons δ ε m d (Fintype.card F) < 1) :
    ∃ aux : (M.expand (padE (Anc F m) F m d Mi.K)).H, ‖aux‖ = 1 ∧
      ‖Mi.endState - Mi.tgtState aux‖ ^ 2
        ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt (deltaSelfCons δ ε m d (Fintype.card F))
          + 2 * deltaSelfCons δ ε m d (Fintype.card F))) := by
  obtain ⟨aux, haux, hclose⟩ := exists_auxVec_close (F := F) (n := Fin m → Bool)
    ((M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m)) Mi.endState)
    (by rw [LinearIsometryEquiv.norm_map]; exact Mi.endState_unit)
    (deltaSelfCons_nonneg hδ hε m d (Fintype.card F)) hlt
    (Mi.qform_endState_twirl_ge hfail hd .X) (Mi.qform_endState_twirl_ge hfail hd .Z)
  refine ⟨aux, haux, ?_⟩
  rw [← LinearIsometryEquiv.norm_map
    ((M.expand (padE (Anc F m) F m d Mi.K)).ampl (Introspection.registerEPR (Anc F m))), map_sub]
  exact hclose

end MirrorSimul

end Physical

end MIPRE.QLD

end
