/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.PauliRestriction
import MIPRE.Background.Introspection.BinaryGame
import MIPRE.Background.Introspection.CompleteGame
import MIPRE.Foundations.Introspection.ValidPauliSoundness
import MIPRE.Background.QLD.ValidAnswers
import MIPRE.Background.QLD.BinaryForm

/-! # Actual Pauli extraction for introspection (`lem:intro-pauli-strat`)

`TypedEstimates.quantumValue_ge_of_valid_isometric_images` proves introspection soundness from
five supplied facts about a projective strategy of the parsed introspection game:
* local isometries onto the register `ι → F`, tensored with auxiliary spaces;
* a unit auxiliary state `ξ`;
* an unsquared state distance to `|EPR> ⊗ |ξ>`;
* a failure bound;
* Alice's `X` and Bob's `Z` errors, summed over the valid full-register Pauli answers only.

It does not prove that such isometries exist. That is the Pauli basis test's soundness,
`thm:qld`, applied to the strategy's Pauli block, as in the paper's proof of
`lem:intro-pauli-strat`. This file supplies those facts and composes the result with the consumer.

## The route

1. **Restriction** (`PauliRestriction`). A strategy `S` of the full parsed game
   `PauliRestriction.fullGame` is turned into a strategy of the actual Pauli basis game
   `qldGame`, on the same state (`strategy_state`). Malformed outer answers are completed at the
   scalar answer `.val 0`. Its failure is at most `N ε`, where `N` is the ordered-edge count of
   the typed graph (`strategy_failure_le`). This is the paper's conditioning on the Pauli block,
   which has probability `Θ(1/ℓ)`. At a valid answer `.pauliAns h`, its Pauli operator is exactly
   `S`'s (`strategy_pauliAns_A`, `_B`).
2. **`thm:qld` on the valid answers** (`qld_soundness_valid`). This gives the isometries, the
   auxiliary state and item 1 at error `errShape a b (N ε)`. It also gives item 2 on the valid
   answers `.pauliAns h`, at `2 errShape + 8/q`. The coarse measurement of `qld_soundness`
   charges the malformed answers to outcome `0`; the valid-answer form pays `8/q` to drop them.
   The strategy's measurements are projective, which is what that step needs.
   Result: `exists_valid_extraction`, for any projection and any original CL functions.
3. **The qubit register** (`BinaryForm`, the paper's `cor:pauli-binary`). The actual binary game
   `BinaryComplete.game` is `fullGame` at the projection `BinaryComplete.project`, definitionally
   (`binaryGame_eq_fullGame`). Its register is `F_2^{M × t}`, and its honest readouts are the
   qubit Paulis. Relabelling the register by `binEquiv` changes no quantity (`binFirst`). For `X`
   the relabelled readouts agree only because the basis is **self-dual**. The consumer's valid
   answer at the qubit label `x` is `.pauliAns (binEquiv⁻¹ x)`, whose projection is `x`.
   Result: `exists_binary_extraction`, with one error `T = ε + 2 errShape a b (N ε) m d q + 8/q`
   that dominates every hypothesis. As in the paper, it holds for both players and both bases:
   four Pauli estimates, of which Alice's `X` and Bob's `Z` are the consumer's `hX`, `hZ`.
4. **Soundness** (`exists_quantumValue_ge_of_binary`). The consumer applied to step 3 bounds
   `val*(G)`, for the original game `G` behind the CL functions.

Steps 3–4 have field-register analogues for `Complete.game`, whose register is `F_q^M` itself.
There no basis relabelling is needed (`proj_weylOf_X`, `proj_weylOf_Z`):
`exists_field_extraction`, `exists_quantumValue_ge_of_field`.

## Constants

The constants `a ≥ 1`, `0 < b < 1` come first and are those of `qld_soundness`. They do not
depend on `ℓ`, `q`, `m`, `d`, the answer alphabet or the strategy. Every dependence on `ℓ` is
explicit, through the edge count `N` inside `errShape` and through `validSoundnessCoefficient`
and `iteratedRoot` in the consumer. The paper's constants "depending only on `ℓ`" absorb exactly
these.

## Differences from the paper

* The paper states `lem:intro-pauli-strat` with an exact state and exact Pauli operators,
  after replacing the strategy by a nearby one. Here the estimates are kept as distances, which
  is the form the consumer's error accounting takes.
* The Pauli answers are indexed by the qubit label `x ∈ F_2^{M × t}` and read at
  `binEquiv⁻¹ x`, rather than by `u ∈ F_q^M`. It is the same sum.
* Only the valid full-register answers are estimated. Malformed answers need no bound: the
  consumer accounts for them.
* The state bound is stated at `T`, not at the sharper `errShape a b (N ε) m d q` that is
  actually proved, so that one error serves every hypothesis of the consumer. The sharper
  bound is in `exists_valid_extraction`.

## What remains between this and an arbitrary original game

The soundness theorems inherit the consumer's hypothesis `∀ w, (L w).ExactlyOn univ`: the
original game's CL functions must be exactly on the **whole** register, of `M · t = M log q`
coordinates. The paper's original questions have length `s(N) ≤ Q`, so reaching an arbitrary
original game still needs a padding step from `s(N)` to `Q` coordinates. `BinaryGame` makes no
such claim, and neither does this file.
-/

noncomputable section
namespace MIPRE.Introspection.PauliExtraction
open Matrix Finset MIPRE.QLD MIPRE.Weyl

/-! ## Step 1–2: the qudit extraction for any full parsed game -/

/-- **Pauli extraction from the full parsed introspection game**, on the qudit register
`F_q^M`. The constants `a ≥ 1`, `0 < b < 1` are those of `thm:qld` and come first. Fix a
strategy `S` of `PauliRestriction.fullGame`, for any original CL functions `L`, projection
`project` and decider `D`, failing with probability at most `ε`. Let `N` be the ordered-edge
count of the typed graph. Then there are register-first isometries `V_A`, `V_B` and a unit
auxiliary state `ξ` with:
* `‖(V_A ⊗ V_B) ψ - |EPR> ⊗ ξ‖ ≤ errShape a b (N ε) m d q`;
* for each `W ∈ {X, Z}` and each party, the squared distance to the honest projector
  `proj (weylOf W) h`, summed over the **valid** answers `.pauli (.pauliAns h)` of `S`'s own
  `(Pauli, W)` measurement, is at most `2 errShape a b (N ε) m d q + 8 / q`.

Proof: restrict `S` to the actual Pauli basis game (`PauliRestriction.strategy`) and apply
`qld_soundness_valid`. The restriction keeps the state, multiplies the failure by at most `N`,
and does not change the operators at valid answers. -/
theorem exists_valid_extraction :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
        {F₀ ι A : Type*} [Field F₀] [Fintype F₀] [DecidableEq F₀] [Fintype ι] [DecidableEq ι]
        [Fintype A] {m t d ℓ : ℕ} [NeZero m] (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ (bas : Module.Basis (Fin t) (ZMod 2) F) (L : Bool → CL.CLFun F₀ ι ℓ)
        (project : QLD.Answer F m d → ι → F₀) (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
        (S : TensorProductStrategy (PauliRestriction.fullGame hm bas L project D)) {ε : ℝ},
        0 ≤ ε → 1 - S.value ≤ ε →
      ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB)
        (_ : DecidableEq HB) (VA : Matrix (Anc F m × HA) (Fin S.dA) ℂ)
        (VB : Matrix (Anc F m × HB) (Fin S.dB) ℂ) (ξ : HA × HB → ℂ),
        VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ ‖evec ξ‖ = 1 ∧
        ‖evec (isometricState VA VB S.ψ - registerState (Anc F m) ξ)‖
          ≤ errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε) m d
              (Fintype.card F) ∧
        ∀ W : Bas,
          ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
              (aOp (isometricImage VA
                ((S.PA.toPOVM (QuestionType.pauli (.pauli W), 0)).mats (.pauli (.pauliAns h))).val
                - aOp (proj (weylOf W) h))) ^ 2
            ≤ 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
                m d (Fintype.card F) + 8 / Fintype.card F ∧
          ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
              (bOp (isometricImage VB
                ((S.PB.toPOVM (QuestionType.pauli (.pauli W), 0)).mats (.pauli (.pauliAns h))).val
                - aOp (proj (weylOf W) h))) ^ 2
            ≤ 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
                m d (Fintype.card F) + 8 / Fintype.card F := by
  obtain ⟨a, b, ha, hb0, hb1, H⟩ := qld_soundness_valid
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ F₀ ι A _ _ _ _ _ _ m t d ℓ _ hm hd bas L project D S ε hε hS
  let Q := PauliRestriction.strategy hm bas L project D S (.val 0) (.val 0)
  have hQ : 1 - povmValue (qldGame hm) S.ψ (fun q => Q.PA.toPOVM q) (fun q => Q.PB.toPOVM q)
      ≤ (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε := by
    have hv := PauliRestriction.strategy_failure_le hm bas L project D S (.val 0) (.val 0) hS
    rw [TensorProductStrategy.value_eq_povmValue] at hv
    exact hv
  have hpA : ∀ W : Bas, IsPVM fun a => ((Q.PA.toPOVM (.pauli W)).mats a).val := fun W =>
    ⟨fun a => by rw [← Matrix.star_eq_conjTranspose]; exact Q.PA.selfAdjoint _ a,
      fun a => Q.PA.projective _ a, Q.PA.normalized _⟩
  have hpB : ∀ W : Bas, IsPVM fun a => ((Q.PB.toPOVM (.pauli W)).mats a).val := fun W =>
    ⟨fun a => by rw [← Matrix.star_eq_conjTranspose]; exact Q.PB.selfAdjoint _ a,
      fun a => Q.PB.projective _ a, Q.PB.normalized _⟩
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, ξ, hA, hB, hξ, h1, h2⟩ :=
    H hm hd S.ψ S.ψ_unit (fun q => Q.PA.toPOVM q) (fun q => Q.PB.toPOVM q) hpA hpB
      (mul_nonneg (Nat.cast_nonneg _) hε) hQ
  refine ⟨HA, HB, i1, i2, i3, i4, VA, VB, ξ, hA, hB, hξ, h1, fun W => ⟨?_, ?_⟩⟩
  · have e : ∀ h : Anc F m,
        ((S.PA.toPOVM (QuestionType.pauli (.pauli W), 0)).mats (.pauli (.pauliAns h))).val
          = ((Q.PA.toPOVM (.pauli W)).mats (.pauliAns h)).val := fun h =>
      (PauliRestriction.strategy_pauliAns_A hm bas L project D S W h).symm
    simp only [e]
    exact (h2 W).1
  · have e : ∀ h : Anc F m,
        ((S.PB.toPOVM (QuestionType.pauli (.pauli W), 0)).mats (.pauli (.pauliAns h))).val
          = ((Q.PB.toPOVM (.pauli W)).mats (.pauliAns h)).val := fun h =>
      (PauliRestriction.strategy_pauliAns_B hm bas L project D S W h).symm
    simp only [e]
    exact (h2 W).2

/-! ## The two concrete games are full parsed games -/

section Games

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {A : Type*} [Fintype A] {m t d ℓ : ℕ} [NeZero m]
  {hm : m ∣ Fintype.card F} {bas : Module.Basis (Fin t) (ZMod 2) F}

/-- **The binary introspection game is the full parsed game** at the binary projection
`BinaryComplete.project`. The two games' Pauli deciders are the same expression, so the games
agree by definition. -/
theorem binaryGame_eq_fullGame (hm : m ∣ Fintype.card F)
    (bas : Module.Basis (Fin t) (ZMod 2) F)
    (L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ)
    (D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool) :
    BinaryComplete.game (d := d) L D hm bas
      = PauliRestriction.fullGame hm bas L (BinaryComplete.project (d := d) bas) D := rfl

/-- A strategy of the binary game, read as a strategy of the full parsed game: the same
dimensions, state and measurements. -/
def binaryToFull {L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ}
    {D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool}
    (S : TensorProductStrategy (BinaryComplete.game (d := d) L D hm bas)) :
    TensorProductStrategy
      (PauliRestriction.fullGame hm bas L (BinaryComplete.project (d := d) bas) D) :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA, S.PB⟩

/-- Reading a binary strategy as a full one keeps its value. -/
theorem binaryToFull_value {L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ}
    {D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool}
    (S : TensorProductStrategy (BinaryComplete.game (d := d) L D hm bas)) :
    (binaryToFull S).value = S.value := rfl

/-- **The field introspection game is the full parsed game** at the field projection
`Complete.project`, by definition. -/
theorem fieldGame_eq_fullGame (hm : m ∣ Fintype.card F)
    (bas : Module.Basis (Fin t) (ZMod 2) F) (L : Bool → CL.CLFun F (Fin m → Bool) ℓ)
    (D : Complete.Seed F m → Complete.Seed F m → A → A → Bool) :
    Complete.game (d := d) L D hm bas
      = PauliRestriction.fullGame hm bas L (Complete.project (d := d)) D := rfl

/-- A strategy of the field game, read as a strategy of the full parsed game. -/
def fieldToFull {L : Bool → CL.CLFun F (Fin m → Bool) ℓ}
    {D : Complete.Seed F m → Complete.Seed F m → A → A → Bool}
    (S : TensorProductStrategy (Complete.game (d := d) L D hm bas)) :
    TensorProductStrategy (PauliRestriction.fullGame hm bas L (Complete.project (d := d)) D) :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA, S.PB⟩

/-- Reading a field strategy as a full one keeps its value. -/
theorem fieldToFull_value {L : Bool → CL.CLFun F (Fin m → Bool) ℓ}
    {D : Complete.Seed F m → Complete.Seed F m → A → A → Bool}
    (S : TensorProductStrategy (Complete.game (d := d) L D hm bas)) :
    (fieldToFull S).value = S.value := rfl

end Games

/-! ## Step 3–4: the binary introspection game -/

/-- **Pauli extraction for the binary introspection game (`lem:intro-pauli-strat`), in the
consumer's hypothesis form.** The constants `a ≥ 1`, `0 < b < 1` are those of `thm:qld`. Fix a
self-dual basis `bas` of `F_q` over `F_2` and a strategy `S` of `BinaryComplete.game` failing
with probability at most `ε`. There are isometries `V_A`, `V_B` onto the qubit register
`F_2^{M × t}` (`BinaryComplete.Seed m t`) and a unit auxiliary state `ξ` such that each of the
following is at most `T = ε + 2 errShape a b (N ε) m d q + 8 / q`:
* the unsquared state distance `‖(V_A ⊗ V_B) ψ - |EPR_2> ⊗ ξ‖`;
* for each player and each `W ∈ {X, Z}`, the summed squared error of that player's `(Pauli, W)`
  measurement over the valid answers `.pauliAns (binEquiv⁻¹ x)`, against the honest qubit
  readout: `Honest.pauliXReadout (some x)` for `X`, `readout some (some z)` for `Z`. In order:
  Alice `X`, Alice `Z`, Bob `X`, Bob `Z`.

The state distance and Alice's `X`, Bob's `Z` estimates are
`quantumValue_ge_of_valid_isometric_images`'s `hstate`, `hX`, `hZ`, and `S`'s failure is at most
`ε ≤ T` (`hfail`). The other two estimates are not used by the consumer; they are kept because
the paper's lemma states all four. The isometries are those of `exists_valid_extraction` with
the register relabelled by `binEquiv bas` (`binFirst`). Relabelling changes no quantity, and for
`X` that needs self-duality (`sum_snorm_sq_binFirst_alice_X`, `sum_snorm_sq_binFirst_bob_X`). -/
theorem exists_binary_extraction :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
        {A : Type*} [Fintype A] {m t d ℓ : ℕ} [NeZero m]
        (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ (bas : Module.Basis (Fin t) (ZMod 2) F), LowDegree.IsSelfDualBasis bas →
      ∀ (L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ)
        (D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool)
        (S : TensorProductStrategy (BinaryComplete.game (d := d) L D hm bas)) {ε : ℝ},
        0 ≤ ε → 1 - S.value ≤ ε →
      ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB)
        (_ : DecidableEq HB) (VA : Matrix (BinaryComplete.Seed m t × HA) (Fin S.dA) ℂ)
        (VB : Matrix (BinaryComplete.Seed m t × HB) (Fin S.dB) ℂ) (ξ : HA × HB → ℂ),
        VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ star ξ ⬝ᵥ ξ = 1 ∧
        ‖evec (isometricState VA VB S.ψ - registerState (BinaryComplete.Seed m t) ξ)‖
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ x, snorm (registerState (BinaryComplete.Seed m t) ξ) (aOp
          (isometricImage VA ((S.PA.toPOVM (QuestionType.pauli (.pauli .X), 0)).mats
              (.pauli (.pauliAns ((binEquiv bas).symm x)))).val -
            (aOp (Honest.pauliXReadout (some x)) :
              Matrix (BinaryComplete.Seed m t × HA) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ z, snorm (registerState (BinaryComplete.Seed m t) ξ) (aOp
          (isometricImage VA ((S.PA.toPOVM (QuestionType.pauli (.pauli .Z), 0)).mats
              (.pauli (.pauliAns ((binEquiv bas).symm z)))).val -
            (aOp (readout (some : BinaryComplete.Seed m t → Option (BinaryComplete.Seed m t))
              (some z)) : Matrix (BinaryComplete.Seed m t × HA) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ x, snorm (registerState (BinaryComplete.Seed m t) ξ) (bOp
          (isometricImage VB ((S.PB.toPOVM (QuestionType.pauli (.pauli .X), 0)).mats
              (.pauli (.pauliAns ((binEquiv bas).symm x)))).val -
            (aOp (Honest.pauliXReadout (some x)) :
              Matrix (BinaryComplete.Seed m t × HB) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ z, snorm (registerState (BinaryComplete.Seed m t) ξ) (bOp
          (isometricImage VB ((S.PB.toPOVM (QuestionType.pauli (.pauli .Z), 0)).mats
              (.pauli (.pauliAns ((binEquiv bas).symm z)))).val -
            (aOp (readout (some : BinaryComplete.Seed m t → Option (BinaryComplete.Seed m t))
              (some z)) : Matrix (BinaryComplete.Seed m t × HB) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F := by
  obtain ⟨a, b, ha, hb0, hb1, H⟩ := exists_valid_extraction
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ A _ m t d ℓ _ hm hd bas hbas L D S ε hε hS
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, ξ, hA, hB, hξ, h1, h2⟩ :=
    H hm hd bas L (BinaryComplete.project bas) D (binaryToFull S) hε
      ((binaryToFull_value S).symm ▸ hS)
  have he : 0 ≤ errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
      m d (Fintype.card F) :=
    errShape_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg _) hε)
  have hq : (0 : ℝ) ≤ 8 / Fintype.card F := by positivity
  refine ⟨HA, HB, i1, i2, i3, i4, binFirst bas VA, binFirst bas VB, ξ, binFirst_isometry bas hA,
    binFirst_isometry bas hB, unit_of_norm_evec_eq_one hξ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (norm_isometricState_binFirst_sub bas VA VB S.ψ ξ).trans_le (h1.trans (by linarith))
  · exact (sum_snorm_sq_binFirst_alice_X bas hbas VA
      (fun h => ((S.PA.toPOVM (QuestionType.pauli (.pauli .X), 0)).mats
        (.pauli (.pauliAns h))).val) ξ).trans_le ((h2 .X).1.trans (by linarith))
  · exact (sum_snorm_sq_binFirst_alice_Z bas VA
      (fun h => ((S.PA.toPOVM (QuestionType.pauli (.pauli .Z), 0)).mats
        (.pauli (.pauliAns h))).val) ξ).trans_le ((h2 .Z).1.trans (by linarith))
  · exact (sum_snorm_sq_binFirst_bob_X bas hbas VB
      (fun h => ((S.PB.toPOVM (QuestionType.pauli (.pauli .X), 0)).mats
        (.pauli (.pauliAns h))).val) ξ).trans_le ((h2 .X).2.trans (by linarith))
  · exact (sum_snorm_sq_binFirst_bob_Z bas VB
      (fun h => ((S.PB.toPOVM (QuestionType.pauli (.pauli .Z), 0)).mats
        (.pauli (.pauliAns h))).val) ξ).trans_le ((h2 .Z).2.trans (by linarith))

/-- **Introspection soundness for the binary game, with the Pauli extraction supplied.** The
constants `a ≥ 1`, `0 < b < 1` are those of `thm:qld`. Let `G` be a game on the qubit register
whose question distribution is the CL distribution of `L` and whose decider is `D`, with `L`
exactly on the whole register. If a strategy `S` of the binary introspection game
`BinaryComplete.game L D hm bas` fails with probability at most `ε`, and the basis is self-dual,
then
`val*(G) ≥ 1 - validSoundnessCoefficient ℓ N · iteratedRoot (6ℓ + 2) T`,
with `N` the ordered-edge count and `T = ε + 2 errShape a b (N ε) m d q + 8 / q`.

This is `TypedEstimates.quantumValue_ge_of_valid_isometric_images` with its extraction
hypotheses discharged by `exists_binary_extraction`. The valid Pauli answer at `x` is
`.pauliAns (binEquiv⁻¹ x)`, and the Pauli questions' seeds are `0`
(`binaryPresentation_pauli_eval`). -/
theorem exists_quantumValue_ge_of_binary :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
        {A : Type} [Fintype A] [Nonempty A] {m t d ℓ : ℕ} [NeZero m]
        (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ (bas : Module.Basis (Fin t) (ZMod 2) F), LowDegree.IsSelfDualBasis bas →
      ∀ (L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ),
        (∀ w, (L w).ExactlyOn univ) →
      ∀ (D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool)
        (G : Game (BinaryComplete.Seed m t) (BinaryComplete.Seed m t) A A),
        (∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y) → G.D = D →
      ∀ (S : TensorProductStrategy (BinaryComplete.game (d := d) L D hm bas)) {ε : ℝ},
        0 ≤ ε → 1 - S.value ≤ ε →
        1 - validSoundnessCoefficient ℓ (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card *
            iteratedRoot (6 * ℓ + 2) (ε + 2 * errShape a b
              ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε) m d (Fintype.card F)
              + 8 / Fintype.card F)
          ≤ quantumValue G := by
  obtain ⟨a, b, ha, hb0, hb1, H⟩ := exists_binary_extraction
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ A _ _ m t d ℓ _ hm hd bas hbas L hL D G hμ hD S ε hε hS
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, ξ, hA, hB, hξ, h1, hX, -, -, hZ⟩ :=
    H hm hd bas hbas L D S hε hS
  have he : 0 ≤ errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
      m d (Fintype.card F) :=
    errShape_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg _) hε)
  have hq : (0 : ℝ) ≤ 8 / Fintype.card F := by positivity
  have hfail : 1 - povmValue (BinaryComplete.game (d := d) L D hm bas) S.ψ
      (fun q => S.PA.toPOVM q) (fun q => S.PB.toPOVM q)
      ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
          m d (Fintype.card F) + 8 / Fintype.card F := by
    rw [← TensorProductStrategy.value_eq_povmValue]
    linarith
  exact TypedEstimates.quantumValue_ge_of_valid_isometric_images QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm bas) L hL (BinaryComplete.project bas)
    (fun x => .pauliAns ((binEquiv bas).symm x))
    (fun x => (binEquiv bas).apply_symm_apply x)
    D (BinaryComplete.pauliCheck hm bas) G hμ hD ξ hξ S.ψ (norm_evec_eq_one_of_unit S.ψ_unit)
    VA VB hA hB (fun q => S.PA.toPOVM q) (fun q => S.PB.toPOVM q)
    (fun q => ⟨fun a => by rw [← Matrix.star_eq_conjTranspose]; exact S.PA.selfAdjoint q a,
      fun a => S.PA.projective q a, S.PA.normalized q⟩)
    (fun q => ⟨fun a => by rw [← Matrix.star_eq_conjTranspose]; exact S.PB.selfAdjoint q a,
      fun a => S.PB.projective q a, S.PB.normalized q⟩)
    0 0 (QLD.PauliCL.binaryPresentation_pauli_eval hm bas .X)
    (QLD.PauliCL.binaryPresentation_pauli_eval hm bas .Z) (by positivity) h1 hfail hX hZ

/-! ## The field introspection game -/

/-- **Pauli extraction for the field introspection game, in the consumer's hypothesis form.**
This is `exists_binary_extraction` for `Complete.game`, whose register is `F_q^M`
(`Complete.Seed F m = Anc F m`) and whose valid Pauli answer at `x` is `.pauliAns x` itself. No
relabelling is needed and no basis property is used. The honest qudit projectors of `thm:qld`
are the consumer's readouts: `proj_weylOf_X` for `X`, `proj_weylOf_Z` for `Z`. As there, all four
Pauli estimates are stated, in the order Alice `X`, Alice `Z`, Bob `X`, Bob `Z`. -/
theorem exists_field_extraction :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
        {A : Type*} [Fintype A] {m t d ℓ : ℕ} [NeZero m]
        (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ (bas : Module.Basis (Fin t) (ZMod 2) F) (L : Bool → CL.CLFun F (Fin m → Bool) ℓ)
        (D : Complete.Seed F m → Complete.Seed F m → A → A → Bool)
        (S : TensorProductStrategy (Complete.game (d := d) L D hm bas)) {ε : ℝ},
        0 ≤ ε → 1 - S.value ≤ ε →
      ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB)
        (_ : DecidableEq HB) (VA : Matrix (Complete.Seed F m × HA) (Fin S.dA) ℂ)
        (VB : Matrix (Complete.Seed F m × HB) (Fin S.dB) ℂ) (ξ : HA × HB → ℂ),
        VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ star ξ ⬝ᵥ ξ = 1 ∧
        ‖evec (isometricState VA VB S.ψ - registerState (Complete.Seed F m) ξ)‖
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ x, snorm (registerState (Complete.Seed F m) ξ) (aOp
          (isometricImage VA ((S.PA.toPOVM (QuestionType.pauli (.pauli .X), 0)).mats
              (.pauli (.pauliAns x))).val -
            (aOp (Honest.pauliXReadout (some x)) : Matrix (Complete.Seed F m × HA) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ z, snorm (registerState (Complete.Seed F m) ξ) (aOp
          (isometricImage VA ((S.PA.toPOVM (QuestionType.pauli (.pauli .Z), 0)).mats
              (.pauli (.pauliAns z))).val -
            (aOp (readout (some : Complete.Seed F m → Option (Complete.Seed F m)) (some z)) :
              Matrix (Complete.Seed F m × HA) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ x, snorm (registerState (Complete.Seed F m) ξ) (bOp
          (isometricImage VB ((S.PB.toPOVM (QuestionType.pauli (.pauli .X), 0)).mats
              (.pauli (.pauliAns x))).val -
            (aOp (Honest.pauliXReadout (some x)) : Matrix (Complete.Seed F m × HB) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F ∧
        ∑ z, snorm (registerState (Complete.Seed F m) ξ) (bOp
          (isometricImage VB ((S.PB.toPOVM (QuestionType.pauli (.pauli .Z), 0)).mats
              (.pauli (.pauliAns z))).val -
            (aOp (readout (some : Complete.Seed F m → Option (Complete.Seed F m)) (some z)) :
              Matrix (Complete.Seed F m × HB) _ ℂ))) ^ 2
          ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
              m d (Fintype.card F) + 8 / Fintype.card F := by
  obtain ⟨a, b, ha, hb0, hb1, H⟩ := exists_valid_extraction
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ A _ m t d ℓ _ hm hd bas L D S ε hε hS
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, ξ, hA, hB, hξ, h1, h2⟩ :=
    H hm hd bas L (Complete.project (d := d)) D (fieldToFull S) hε
      ((fieldToFull_value S).symm ▸ hS)
  have he : 0 ≤ errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
      m d (Fintype.card F) :=
    errShape_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg _) hε)
  have hq : (0 : ℝ) ≤ 8 / Fintype.card F := by positivity
  refine ⟨HA, HB, i1, i2, i3, i4, VA, VB, ξ, hA, hB, unit_of_norm_evec_eq_one hξ,
    h1.trans (by linarith), ?_, ?_, ?_, ?_⟩
  · have hX := (h2 .X).1
    simp only [proj_weylOf_X] at hX
    exact hX.trans (by linarith)
  · have hZ := (h2 .Z).1
    simp only [proj_weylOf_Z] at hZ
    exact hZ.trans (by linarith)
  · have hX := (h2 .X).2
    simp only [proj_weylOf_X] at hX
    exact hX.trans (by linarith)
  · have hZ := (h2 .Z).2
    simp only [proj_weylOf_Z] at hZ
    exact hZ.trans (by linarith)

/-- **Introspection soundness for the field game, with the Pauli extraction supplied.** This is
`exists_quantumValue_ge_of_binary` for `Complete.game`: the original game `G` lives on the field
register `F_q^M`, its CL functions are over `F_q`, and no basis property is needed. -/
theorem exists_quantumValue_ge_of_field :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
        {A : Type} [Fintype A] [Nonempty A] {m t d ℓ : ℕ} [NeZero m]
        (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ (bas : Module.Basis (Fin t) (ZMod 2) F) (L : Bool → CL.CLFun F (Fin m → Bool) ℓ),
        (∀ w, (L w).ExactlyOn univ) →
      ∀ (D : Complete.Seed F m → Complete.Seed F m → A → A → Bool)
        (G : Game (Complete.Seed F m) (Complete.Seed F m) A A),
        (∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y) → G.D = D →
      ∀ (S : TensorProductStrategy (Complete.game (d := d) L D hm bas)) {ε : ℝ},
        0 ≤ ε → 1 - S.value ≤ ε →
        1 - validSoundnessCoefficient ℓ (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card *
            iteratedRoot (6 * ℓ + 2) (ε + 2 * errShape a b
              ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε) m d (Fintype.card F)
              + 8 / Fintype.card F)
          ≤ quantumValue G := by
  obtain ⟨a, b, ha, hb0, hb1, H⟩ := exists_field_extraction
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ A _ _ m t d ℓ _ hm hd bas L hL D G hμ hD S ε hε hS
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, ξ, hA, hB, hξ, h1, hX, -, -, hZ⟩ :=
    H hm hd bas L D S hε hS
  have he : 0 ≤ errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
      m d (Fintype.card F) :=
    errShape_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg _) hε)
  have hq : (0 : ℝ) ≤ 8 / Fintype.card F := by positivity
  have hfail : 1 - povmValue (Complete.game (d := d) L D hm bas) S.ψ
      (fun q => S.PA.toPOVM q) (fun q => S.PB.toPOVM q)
      ≤ ε + 2 * errShape a b ((TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε)
          m d (Fintype.card F) + 8 / Fintype.card F := by
    rw [← TensorProductStrategy.value_eq_povmValue]
    linarith
  exact TypedEstimates.quantumValue_ge_of_valid_isometric_images QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm bas) L hL (Complete.project (d := d))
    (fun x => .pauliAns x) (fun _ => rfl)
    D (Complete.pauliCheck hm bas) G hμ hD ξ hξ S.ψ (norm_evec_eq_one_of_unit S.ψ_unit)
    VA VB hA hB (fun q => S.PA.toPOVM q) (fun q => S.PB.toPOVM q)
    (fun q => ⟨fun a => by rw [← Matrix.star_eq_conjTranspose]; exact S.PA.selfAdjoint q a,
      fun a => S.PA.projective q a, S.PA.normalized q⟩)
    (fun q => ⟨fun a => by rw [← Matrix.star_eq_conjTranspose]; exact S.PB.selfAdjoint q a,
      fun a => S.PB.projective q a, S.PB.normalized q⟩)
    0 0 (QLD.PauliCL.binaryPresentation_pauli_eval hm bas .X)
    (QLD.PauliCL.binaryPresentation_pauli_eval hm bas .Z) (by positivity) h1 hfail hX hZ

end MIPRE.Introspection.PauliExtraction
end
