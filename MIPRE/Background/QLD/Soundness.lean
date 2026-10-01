/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.ModelSoundness
public import MIPRE.Background.QLD.MirrorExists
public import MIPRE.Background.QLD.Regime
public import MIPRE.Background.LIDT.ModelTransport
public import MIPRE.Background.LIDT.CoExpand
public import MIPRE.Foundations.POVMReduction

@[expose] public section

/-!
# `thm:qld`: soundness of the Pauli basis test, in a bipartite model

Phase 5 of `planning/mipco-track.md`. This file proves `thm:qld` for the projective strategies of
a bipartite model, in the form `QLD.SoundIn ω M` in which introspection takes it
(`MIPRE/Background/QLD/ModelSoundness.lean`), from two hypotheses on the model:

* **the seeded low individual degree test is sound** (`LIDT.Simul.SoundIn`) in every extension
  `M.expand e` of the model by a unit vector: stage 4 runs the seeded test on the padded strategy,
  which lives in such an extension (`exists_globalPair`);
* **the value model dominates** the POVM strategies of every model obtained from such an extension
  by replacing its state with a unit vector: the ancilla model the theorem produces is one, the
  extension by the padding registers in the auxiliary state of the swap isometry lemma.

The headline is `soundIn_of_lidt`. Its two instances are the two models the project needs.

* **`soundIn_tensor`**: in the tensor-product model of every state, with `val*`. An extension of
  a tensor-product model is the tensor-product model of the expanded vector
  (`BipartiteModel.tensorExpandIso`), in which the seeded test is sound
  (`LIDT.Simul.soundIn_expand_tensor`) and which `val*` dominates
  (`ValueModel.tensor_dominatesPOVM`). The main theorem uses it, through introspection
  (`approxSoundIn_tensor`).
* **`soundCo_of_lidt`**: in the model of every commuting-operator strategy, with `ω_co`, as soon as
  the seeded test is sound in the commuting-operator model (`LIDT.Simul.SoundCo`): an extension of
  a commuting-operator model is again one (`LIDT.Simul.SoundCo.expand`), and `ω_co` dominates
  every model in a unit state (`ValueModel.commuting_dominatesPOVM`). So the Pauli basis test adds
  no hypothesis to `MIP^co = coRE` (`MIPRE.mipco_eq_core_of_lidt`).

## The route

Inside the regime --- `48 m d ≤ q`, where the chain runs, and `qldHlt < 1`, where the swap
isometry lemma applies --- three steps (`exists_extraction_of_regime`).

1. **Legalize** (`legalStrat`). Sending each answer of the wrong format to the question's default
   makes the strategy legally supported, which stage 4 needs. It keeps the strategy projective,
   does not raise its failure probability (`one_sub_povmValue_legalizeStrat_le`), and does not
   change the cube data a Pauli answer carries (`rdPauliVec_legalize_pauli`), which is all the
   conclusion is about (`legalStrat_pauli_A`, `legalStrat_pauli_B`).
2. **Both cuts on one state** (`exists_mirrorSimul`): `lem:qld-global-pvm` at the strategy and at
   the strategy with the players exchanged, at one padding size.
3. **The swap isometry** (`MirrorSimul.swap_isometry`): a local isometry `swapPhi aux` of the
   model into the register model over the padded extension in an auxiliary unit state `aux`, with
   item 1 on the squared distance and item 2 for both players.

The extraction is that local isometry, with the padded extension in the state `aux` as its ancilla
model. Item 1 of `thm:qld` is the distance itself, at most `√qldEta`, and item 2 is the swap
lemma's: both are at most `qldBound`, and both are at most the trivial bound `4`
(`sum_stateSqNorm_alice_le_four`, `sum_stateSqNorm_bob_le_four`), so at most `qldErr`
(`le_qldErr`). Outside the regime `qldErr = 4`, and the model itself with the EPR register adjoined
inertly is an extraction at the trivial bound (`Extraction.trivial`).

## What changed from the matrix statement

The matrix `thm:qld` this replaces (`qld_soundness`, removed in Phase 5) was about an arbitrary
POVM strategy on finite-dimensional spaces. It dilated the strategy to a projective one, ran the
chain on the dilation, and carried item 2 back down to the original POVM through the agreement
with `τ^W` on the other half of the pair, at a cost of `8 √η`. Introspection, its one consumer,
applies it to projective strategies only, so the descent is gone, and with it the explicit
embedding of the original space and the register-first reading of the isometries. The error is
the same function `qldErr`, of the closed form `a (md)^a (ε^b + q^{-b} + 2^{-bmd})`
(`exists_qldErr_le`).

## What differs from the paper's statement

* The strategy is projective, in a bipartite model satisfying the two hypotheses, rather than a
  POVM strategy on a tensor product of finite-dimensional spaces.
* The regime is `48 m d ≤ q`, not `16 m d ≤ q`: `48` is where `lem:qld-global-separate` is
  formalized. The error absorbs the difference, as the paper's own `a ≥ 64` does.
* `m ≥ 1` is the instance `[NeZero m]`, which `qldGame` needs to be stated at all.
* The `(Pauli, W)` measurement is read as cube data through `rdPauliVec`, which reads an answer of
  the wrong format as `h = 0`. The paper assumes well-formatted answers; this is a relabelling of
  outcomes, not a restriction.
-/

noncomputable section

namespace MIPRE.BipartiteModel.LocalIsometry

variable {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
  [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  {M : BipartiteModel 𝒞 𝒜 ℬ} {M' : BipartiteModel 𝒞' 𝒜' ℬ'}

/-- **A local isometry between the two models with their states replaced**: the same isometry and
homomorphisms, the states playing no part in a local isometry (`toWithState` replaces the target's
alone). -/
def withStates (Φ : LocalIsometry M M') (v : M.H) (w : M'.H) :
    LocalIsometry (M.withState v) (M'.withState w) where
  W := Φ.W
  ΦA := Φ.ΦA
  ΦB := Φ.ΦB
  intertwineA := Φ.intertwineA
  intertwineB := Φ.intertwineB

end MIPRE.BipartiteModel.LocalIsometry

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.Weyl MIPRE.Introspection BipartiteModel
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Legalizing the strategy -/

section Legal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- **Legalizing a `(Pauli, W)` answer does not change the cube data it reports**: an answer of
the wrong format reads as `0`, and so does the default. -/
theorem rdPauliVec_legalize_pauli (W : Bas) (a : Answer F m d) :
    rdPauliVec (legalize (.pauli W) a) = rdPauliVec a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdPauliVec]

variable [Algebra (ZMod 2) F] [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}

/-- **The legalized strategy**: each measurement relabelled along `legalize`, which sends an
answer of the wrong format for the question to the question's default (`legalizeStrat`). A
coarse-graining of a projective strategy is projective. -/
def legalStrat (S : M.ProjStrat (qldGame (d := d) hm)) : M.ProjStrat (qldGame (d := d) hm) :=
  S.adapt (qldGame hm) id id legalize legalize

theorem legalStrat_PA (S : M.ProjStrat (qldGame (d := d) hm)) (q : Question F m) :
    (legalStrat S).PA q = legalizeStrat S.PA q := rfl

theorem legalStrat_PB (S : M.ProjStrat (qldGame (d := d) hm)) (q : Question F m) :
    (legalStrat S).PB q = legalizeStrat S.PB q := rfl

/-- **Legalizing does not raise the failure probability** (`one_sub_povmValue_legalizeStrat_le`). -/
theorem one_sub_value_legalStrat_le (S : M.ProjStrat (qldGame (d := d) hm)) {ε : ℝ}
    (hfail : 1 - S.value ≤ ε) : 1 - (legalStrat S).value ≤ ε :=
  one_sub_povmValue_legalizeStrat_le hm M S.PA S.PB hfail

theorem legalSupport_legalStrat_A (S : M.ProjStrat (qldGame (d := d) hm)) :
    LegalSupport (legalStrat S).PA :=
  legalSupport_legalizeStrat S.PA

theorem legalSupport_legalStrat_B (S : M.ProjStrat (qldGame (d := d) hm)) :
    LegalSupport (legalStrat S).PB :=
  legalSupport_legalizeStrat S.PB

/-- **The first player's coarse `(Pauli, W)` measurement is unchanged by legalizing.** -/
theorem legalStrat_pauli_A (S : M.ProjStrat (qldGame (d := d) hm)) (W : Bas) :
    ((legalStrat S).PA (.pauli W)).map rdPauliVec = (S.PA (.pauli W)).map rdPauliVec :=
  legalizeStrat_map S.PA _ rdPauliVec (rdPauliVec_legalize_pauli W)

/-- **The second player's coarse `(Pauli, W)` measurement is unchanged by legalizing.** -/
theorem legalStrat_pauli_B (S : M.ProjStrat (qldGame (d := d) hm)) (W : Bas) :
    ((legalStrat S).PB (.pauli W)).map rdPauliVec = (S.PB (.pauli W)).map rdPauliVec :=
  legalizeStrat_map S.PB _ rdPauliVec (rdPauliVec_legalize_pauli W)

end Legal

/-! ## The trivial bound -/

section Trivial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

omit [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **The first player's error of an extraction is at most `4`**, for a local isometry into the
register model of an ancilla model whose first homomorphism preserves the unit: the transported
Pauli measurement and the honest one are projective, on a unit vector
(`BipartiteModel.sum_stateSqNorm_sub_le_four`). -/
theorem sum_stateSqNorm_alice_le_four (N : AncillaModel) (Φ : LocalIsometry M (N.N.reg (Anc F m)))
    (hΦ : Φ.ΦA 1 = 1) {P : POVMIn (Anc F m) 𝒜} (hP : IsPVMIn P.op) (W : Bas) :
    ∑ h : Anc F m, (N.N.reg (Anc F m)).stateSqNorm
      (Φ.ΦA (P.op h) - smulKron 1 (proj (weylOf W) h)) ≤ 4 :=
  (N.N.reg (Anc F m)).sum_stateSqNorm_sub_le_four ((norm_reg_ψ N.N).trans N.unit)
    (hP.pushforward hΦ) (IsPVMIn.smulKron_one (isPVM_proj (isWeylFamily_weylOf W)).toIn)

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **The second player's error of an extraction is at most `4`.** -/
theorem sum_stateSqNorm_bob_le_four (N : AncillaModel) (Φ : LocalIsometry M (N.N.reg (Anc F m)))
    (hΦ : Φ.ΦB 1 = 1) {P : POVMIn (Anc F m) ℬ} (hP : IsPVMIn P.op) (W : Bas) :
    ∑ h : Anc F m, (N.N.reg (Anc F m)).swap.stateSqNorm
      (Φ.ΦB (P.op h) - smulKron 1 (proj (weylOf W) h)) ≤ 4 :=
  (N.N.reg (Anc F m)).swap.sum_stateSqNorm_sub_le_four ((norm_reg_ψ N.N).trans N.unit)
    (hP.pushforward hΦ) (IsPVMIn.smulKron_one (isPVM_proj (isWeylFamily_weylOf W)).toIn)

variable {𝒞 𝒜 ℬ : Type} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ] {M : BipartiteModel.{0} 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}

omit [Algebra (ZMod 2) F] [NeZero m] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
/-- The inert EPR register carries the state exactly to the state of the register model. -/
theorem norm_inert_reg_sub_le_four :
    ‖(M.inert (registerEPR (Anc F m)) registerEPR_norm).W M.ψ - (M.reg (Anc F m)).ψ‖ ≤ 4 := by
  rw [inert_W_ψ, sub_self, norm_zero]
  norm_num

omit [Algebra (ZMod 2) F] [NeZero m] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
theorem inert_reg_ΦA_one : (M.inert (registerEPR (Anc F m)) registerEPR_norm).ΦA 1 = 1 := by
  rw [inert_ΦA, diagonal_one]

omit [Algebra (ZMod 2) F] [NeZero m] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
theorem inert_reg_ΦB_one : (M.inert (registerEPR (Anc F m)) registerEPR_norm).ΦB 1 = 1 := by
  rw [inert_ΦB, diagonal_one]

/-- **The trivial extraction**, at the trivial bound `4`: the model itself is the ancilla model,
and the local isometry adjoins the EPR register inertly, carrying the state exactly to the
register model's. -/
def Extraction.trivial (S : M.ProjStrat (qldGame (d := d) hm)) : Extraction M hm S 4 where
  N := AncillaModel.of M S.ψ_unit
  Φ := M.inert (registerEPR (Anc F m)) registerEPR_norm
  state_error := norm_inert_reg_sub_le_four
  alice_error W := sum_stateSqNorm_alice_le_four (AncillaModel.of M S.ψ_unit)
    (M.inert (registerEPR (Anc F m)) registerEPR_norm) inert_reg_ΦA_one
    (POVMIn.isPVMIn_map (S.projA _) _) W
  bob_error W := sum_stateSqNorm_bob_le_four (AncillaModel.of M S.ψ_unit)
    (M.inert (registerEPR (Anc F m)) registerEPR_norm) inert_reg_ΦB_one
    (POVMIn.isPVMIn_map (S.projB _) _) W

/-- The one-point unit vector. -/
theorem norm_evec_unitPoint : ‖evec (fun _ : Unit × Unit => (1 : ℂ))‖ = 1 :=
  norm_evec_eq_one (by simp [dotProduct])

omit [StarModule ℂ 𝒜] [StarModule ℂ ℬ] in
/-- **A value model dominating the extensions of a model in unit states dominates the model**, in
a unit state: the model reduces to its extension by one-point registers, which is itself in its
own state. -/
theorem dominatesPOVM_of_expand {ω : ValueModel}
    (hω : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → ∀ v : (M.expand e).H, ‖v‖ = 1 →
        ω.DominatesPOVM ((M.expand e).withState v))
    (hψ : ‖M.ψ‖ = 1) : ω.DominatesPOVM M :=
  ValueModel.DominatesPOVM.of_povmReduces
    (((M.inert _ norm_evec_unitPoint).toWithState
      (M.expand fun _ : Unit × Unit => (1 : ℂ)).ψ).povmReduces rfl (by simp) (by simp))
    (hω _ norm_evec_unitPoint _
      (by rw [norm_expand_state, norm_evec_unitPoint, one_mul, hψ]))

end Trivial

/-! ## Inside the regime -/

section Regime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {hm : m ∣ Fintype.card F}
variable {𝒞 𝒜 ℬ : Type} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ] {M : BipartiteModel.{0} 𝒞 𝒜 ℬ}

namespace MirrorSimul

variable {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ} (Mi : MirrorSimul M S δ)

/-- The swap isometry preserves the first player's unit. -/
theorem swapPhi_ΦA_one (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    (Mi.swapPhi aux).ΦA 1 = 1 := by
  rw [swapPhi_ΦA, physInert_ΦA, diagonal_one, mul_one, Mi.aliceSwap_mul_conjTranspose,
    uncompHom_one]

/-- The swap isometry preserves the second player's unit. -/
theorem swapPhi_ΦB_one (aux : (M.expand (padE (Anc F m) F m d Mi.K)).H) :
    (Mi.swapPhi aux).ΦB 1 = 1 := by
  rw [swapPhi_ΦB, physInert_ΦB, diagonal_one, mul_one, Mi.bobSwap_mul_conjTranspose,
    uncompHom_one]

end MirrorSimul

variable {ω : ValueModel}

/-- **`thm:qld` inside the regime.** For a projective strategy failing with probability at most
`ε`, when `48 m d ≤ q` and `qldHlt < 1`: the swap isometry of the legalized strategy
(`MirrorSimul.swap_isometry`, at the `MirrorSimul` of `exists_mirrorSimul`), with the extension by
the padding registers in the swap lemma's auxiliary state as the ancilla model, is an extraction at
error `qldErr`. Item 1 is the swap lemma's at the cost of a square root, and item 2 is the swap
lemma's on the nose, the legalized strategy having the strategy's Pauli measurements. -/
theorem exists_extraction_of_regime
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (hω : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → ∀ v : (M.expand e).H, ‖v‖ = 1 →
        ω.DominatesPOVM ((M.expand e).withState v))
    (hd : 1 ≤ d) (S : M.ProjStrat (qldGame (d := d) hm)) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - S.value ≤ ε) (hq : 48 * m * d ≤ Fintype.card F)
    (hlt : qldHlt ε m d (Fintype.card F) < 1) :
    ∃ E : Extraction M hm S (qldErr ε m d (Fintype.card F)), ω.DominatesPOVM E.N.N := by
  have hfail' := one_sub_value_legalStrat_le S hfail
  obtain ⟨Mi⟩ := exists_mirrorSimul hL (legalStrat S) hε hfail' (legalSupport_legalStrat_A S)
    (legalSupport_legalStrat_B S) hd hq
  obtain ⟨aux, haux, h1, h2⟩ := Mi.swap_isometry hfail' hd (qldDelta_nonneg hε m d _) hε hlt
  have hR : ‖(((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).ψ‖ = 1 :=
    (norm_reg_ψ _).trans haux
  refine ⟨⟨AncillaModel.of ((M.expand (padE (Anc F m) F m d Mi.K)).withState aux) haux,
    Mi.swapPhi aux, ?_, fun W => ?_, fun W => ?_⟩, hω _ norm_padE aux haux⟩
  · refine le_qldErr ?_ fun _ _ => ?_
    · calc _ ≤ ‖(Mi.swapPhi aux).W M.ψ‖
            + ‖(((M.expand (padE (Anc F m) F m d Mi.K)).withState aux).reg (Anc F m)).ψ‖ :=
          norm_sub_le _ _
        _ = 2 := by rw [LinearIsometry.norm_map, S.ψ_unit, hR]; norm_num
        _ ≤ 4 := by norm_num
    · exact (Real.le_sqrt_of_sq_le h1).trans (sqrt_qldEta_le_qldBound hε _ _ _)
  · refine le_qldErr (sum_stateSqNorm_alice_le_four _ _ (Mi.swapPhi_ΦA_one aux)
      (POVMIn.isPVMIn_map (S.projA _) _) W) fun _ _ => ?_
    have h := (h2 W).1
    rw [legalStrat_pauli_A] at h
    exact h.trans (itemTwo_le_qldBound _ _ _ _)
  · refine le_qldErr (sum_stateSqNorm_bob_le_four _ _ (Mi.swapPhi_ΦB_one aux)
      (POVMIn.isPVMIn_map (S.projB _) _) W) fun _ _ => ?_
    have h := (h2 W).2
    rw [legalStrat_pauli_B] at h
    exact h.trans (itemTwo_le_qldBound _ _ _ _)

end Regime

/-! ## `thm:qld` -/

section Theorem

variable {𝒞 𝒜 ℬ : Type} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ] {M : BipartiteModel.{0} 𝒞 𝒜 ℬ} {ω : ValueModel}

/-- **`thm:qld`: the Pauli basis test is sound in a bipartite model** (the paper's
`thm:pauli-appendix`), with the value model `ω`, when the seeded low individual degree test is
sound in every extension of the model by a unit vector and `ω` dominates every such extension in
every unit state. For every admissible `(q, m, d)` and every projective strategy in the model that
fails with probability at most `ε`, there are an ancilla model, which `ω` dominates, and a local
isometry of the model into it with the EPR register `|EPR_q>^{⊗M}` adjoined, such that

1. the transported state is within `qldErr ε m d q` of `|EPR_q>^{⊗M} ⊗ |aux>`, the state of the
   register model; and
2. for each basis `W ∈ {X, Z}`, each player's own `(Pauli, W)` measurement, read as cube data and
   transported, is within `qldErr ε m d q` of the honest Pauli basis measurement `τ^W_h` on that
   player's register, in summed squared state norm on that state.

`qldErr` is of the closed form `a (md)^a (ε^b + q^{-b} + 2^{-bmd})` (`exists_qldErr_le`). Inside
the regime this is `exists_extraction_of_regime`; outside it, `Extraction.trivial`. -/
theorem soundIn_of_lidt
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (hω : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → ∀ v : (M.expand e).H, ‖v‖ = 1 →
        ω.DominatesPOVM ((M.expand e).withState v)) :
    SoundIn ω M := by
  intro F _ _ _ _ m d _ hm hd S ε hε hfail
  by_cases hreg : 48 * m * d ≤ Fintype.card F ∧ qldHlt ε m d (Fintype.card F) < 1
  · exact exists_extraction_of_regime hL hω hd S hε hfail hreg.1 hreg.2
  · exact ⟨(Extraction.trivial S).mono (qldErr_of_not hreg).ge,
      dominatesPOVM_of_expand hω S.ψ_unit⟩

end Theorem

/-! ## The tensor-product instance -/

section Tensor

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The Pauli basis test is sound in the tensor-product model** of every state, with `val*`.
An extension of a tensor-product model by a unit vector is the tensor-product model of the
expanded vector (`BipartiteModel.tensorExpandIso`), in which the seeded test is sound
(`LIDT.Simul.soundIn_expand_tensor`), and which `val*` dominates in every unit state
(`ValueModel.tensor_dominatesPOVM`). -/
theorem soundIn_tensor (ψ : dA × dB → ℂ) : SoundIn .tensor (BipartiteModel.tensor ψ) := by
  refine soundIn_of_lidt (fun e _ => LIDT.Simul.soundIn_expand_tensor ψ e) ?_
  intro α β _ _ _ _ e _ v hv
  have hw : ‖(BipartiteModel.tensorExpandIso ψ e).W v‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, hv]
  have hR : (((BipartiteModel.tensor ψ).expand e).withState v).POVMReduces
      ((BipartiteModel.tensor (expVec e ψ)).withState ((BipartiteModel.tensorExpandIso ψ e).W v)) :=
    (LocalIsometry.withStates (BipartiteModel.tensorExpandIso ψ e).toLocalIsometry v
      ((BipartiteModel.tensorExpandIso ψ e).W v)).povmReduces rfl
      (Iso.toLocalIsometry_ΦA_one (BipartiteModel.tensorExpandIso ψ e))
      (Iso.toLocalIsometry_ΦB_one (BipartiteModel.tensorExpandIso ψ e))
  have hD : ValueModel.tensor.DominatesPOVM
      ((BipartiteModel.tensor (expVec e ψ)).withState ((BipartiteModel.tensorExpandIso ψ e).W v)) :=
    ValueModel.tensor_dominatesPOVM (dA := α × dA) (dB := β × dB)
      (WithLp.ofLp ((BipartiteModel.tensorExpandIso ψ e).W v)) (star_dotProduct_self_eq_one hw)
  intro X Y A B _ _ _ _ G PA PB
  obtain ⟨QA, QB, hQ⟩ := hR G PA PB
  exact hQ.trans (hD G QA QB)

end Tensor

/-- **`val*` is approached in tensor-product models**, where the test is sound
(`soundIn_tensor`): a tensor-product strategy near the supremum is a projective strategy of its
model, of the same value. -/
theorem approxSoundIn_tensor : ApproxSoundIn .tensor := fun G t ht h => by
  rw [ValueModel.tensor_val, quantumValue] at h
  rcases isEmpty_or_nonempty (TensorProductStrategy G) with hG | hG
  · rw [Real.iSup_of_isEmpty] at h
    exact absurd ht (not_le.mpr h)
  obtain ⟨T, hT⟩ := exists_lt_of_lt_ciSup h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, BipartiteModel.tensor T.ψ,
    soundIn_tensor T.ψ, T.toModel, by rwa [T.value_toModel]⟩

/-! ## The commuting-operator instance -/

/-- **The Pauli basis test is sound in the commuting-operator model** as soon as the seeded low
individual degree test is: an extension of the model of a commuting-operator strategy by a unit
vector is the model of a commuting-operator strategy (`LIDT.Simul.SoundCo.expand`), and `ω_co`
dominates every model in a unit state (`ValueModel.commuting_dominatesPOVM`). -/
theorem soundCo_of_lidt (h : LIDT.Simul.SoundCo) : SoundCo := fun S =>
  soundIn_of_lidt (fun e he => h.expand S e he) fun _ _ _ hv =>
    ValueModel.commuting_dominatesPOVM _ hv

end MIPRE.QLD

end

end
