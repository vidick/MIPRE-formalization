/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.PauliRestriction
public import MIPRE.Background.Introspection.BinaryMeasurements
public import MIPRE.Foundations.Introspection.ValidPauliSoundness
public import MIPRE.Background.QLD.ModelSoundness

@[expose] public section

/-! # Source-game soundness from the restricted QLD strategy

The extraction inputs refer to the actual restricted QLD strategy, with scalar
completion of malformed answers. The full-register answers retain their original
operators, so the checked finite-game soundness theorem applies without a
malformed-mass hypothesis.

The isometry codomains and ideal projectors here use binary coordinates under
`Weyl.binEquiv b`. Thus the witness interface explicitly records the coordinate
convention expected after the field-to-binary Pauli equivalence.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the strategy is a projective
strategy of any model `M`, and the extraction is the conclusion of the Pauli basis test in a model
(`QLD.Extraction`) read at the genuine full-register answers in binary coordinates: an ancilla
model `N` and a local isometry of `M` into `N` with the binary register adjoined. The value is that
of any value model dominating the POVM strategies of `N`.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete
set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d ℓ : ℕ} [NeZero m]
  {A : Type} [Fintype A] [Nonempty A]

/-- Interpret a full binary register answer as the genuine QLD Pauli answer. -/
def validAnswer (b : Module.Basis (Fin t) (ZMod 2) F) (x : Seed m t) : QLD.Answer F m d :=
  .pauliAns ((Weyl.binEquiv b).symm x)

theorem project_validAnswer (b : Module.Basis (Fin t) (ZMod 2) F) (x : Seed m t) :
    BinaryComplete.project b (validAnswer (d := d) b x) = x :=
  (Weyl.binEquiv b).apply_symm_apply x

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **The conclusion of the Pauli basis test for an actual QLD strategy, in binary
coordinates**: an ancilla model and a local isometry into it with the binary register adjoined,
the state within `δ` of the register state, and the valid-answer X and Z effects within `δ` of the
honest readouts in summed squared state norm. -/
structure Extraction (M : BipartiteModel 𝒞 𝒜 ℬ) (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (R : M.ProjStrat (QLD.qldGame (d := d) hm))
    (δ : ℝ) where
  /-- The ancilla model. -/
  N : QLD.AncillaModel
  /-- The local isometry into the ancilla model with the binary register adjoined. -/
  Φ : BipartiteModel.LocalIsometry M (N.N.reg (Seed m t))
  state_error : ‖Φ.W M.ψ - (N.N.reg (Seed m t)).ψ‖ ≤ δ
  X_error : ∑ x : Seed m t, (N.N.reg (Seed m t)).stateSqNorm
    (Φ.ΦA ((R.PA (.pauli .X)).op (validAnswer b x)) -
      smulKron 1 (Honest.pauliXReadout (some x))) ≤ δ
  Z_error : ∑ z : Seed m t, (N.N.reg (Seed m t)).swap.stateSqNorm
    (Φ.ΦB ((R.PB (.pauli .Z)).op (validAnswer b z)) -
      smulKron 1 (readout (some : Seed m t → Option (Seed m t)) (some z))) ≤ δ

variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool) {M : BipartiteModel 𝒞 𝒜 ℬ}
  (S : M.ProjStrat
    (PauliRestriction.fullGame hm b L (BinaryComplete.project (d := d) b) D))

/-- The extraction theorem is applied to this precise QLD strategy. -/
abbrev restriction := PauliRestriction.strategy hm b L (BinaryComplete.project b) D S
  (.val 0) (.val 0)

/-- Concrete valid-answer extraction estimates imply source-game soundness, in every value model
dominating the ancilla model. The common error is the maximum of full-game failure and extraction
error. -/
theorem quantumValue_ge_of_extraction (hL : ∀ w, (L w).ExactlyOn univ) (ω : ValueModel)
    {ε δ : ℝ} (hδ : 0 ≤ δ) (hfail : 1 - S.value ≤ ε)
    (E : Extraction M hm b (restriction hm b L D S) δ) (hω : ω.DominatesPOVM E.N.N) :
    1 - validSoundnessCoefficient ℓ
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card *
      iteratedRoot (6 * ℓ + 2) (max ε δ) ≤ ω.val (Honest.sourceGame L D) := by
  apply TypedEstimates.quantumValue_ge_of_valid_isometric_images
    QLD.adj (.pauli .X) (.pauli .Z) (QLD.PauliCL.binaryPresentation hm b) L hL
    (BinaryComplete.project b) (validAnswer b) (project_validAnswer b)
    D (PauliRestriction.pauliCheck hm b) ω (Honest.sourceGame L D)
    (by
      intro x y
      change SampledGame.dist _ _ x y = _
      rw [SampledGame.dist_eq_card]
      unfold CL.clDist
      congr 2
      apply congrArg Finset.card
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) rfl E.N.N E.N.unit hω
    M S.ψ_unit E.Φ S.PA S.PB S.projA S.projB 0 0
    (QLD.PauliCL.binaryPresentation_pauli_eval hm b .X)
    (QLD.PauliCL.binaryPresentation_pauli_eval hm b .Z)
    (hδ.trans (le_max_right ε δ)) (E.state_error.trans (le_max_right ε δ))
  · exact hfail.trans (le_max_left ε δ)
  · have hh := E.X_error.trans (le_max_right ε δ)
    simpa only [restriction, validAnswer, PauliRestriction.strategy_pauliAns_A] using hh
  · have hh := E.Z_error.trans (le_max_right ε δ)
    simpa only [restriction, validAnswer, PauliRestriction.strategy_pauliAns_B] using hh

end MIPRE.Introspection.RestrictedSoundness
end

end
