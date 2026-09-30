/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.SamplingRigidity
public import MIPRE.Foundations.Introspection.HidingInduction
public import MIPRE.Foundations.Introspection.HidingBaseOperators

@[expose] public section

/-! # Actual sampling tests imply coarse Z commutation

The common joint measurement is the actual Sample measurement: one marginal
records its evaluated question and original answer, while the other records
an arbitrary function of its seed. Both marginal estimates are obtained from
the parsed game and the extracted Pauli-Z estimate before applying the joint
commutation theorem. Malformed answers retain a dummy outcome throughout.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the EPR seed beside an
arbitrary auxiliary state is the register model `Ξ.reg (ι → F)` of a normalized model `Ξ`, the
strategy is a pair of POVM families of matrices over `ι → F` with entries in `Ξ`'s algebras, and
the honest computational readouts, complex register matrices, act as `smulKron 1 _` for either
player; the readout of a seed function is a projective measurement of the model
(`IsPVMIn.toPOVMIn`). Coarse-graining a POVM is `POVMIn.map`, and coarse-graining an embedded
register family is `fibSumIn` (`fibSumIn_smulKron_one`). The exact mirror of a readout is the
vector identity `π (πA _) ψ = π (πB _) ψ` of `BipartiteModel.reg_mirror`, and Bob's commutator is
Alice's in the exchanged model `(Ξ.reg (ι → F)).swap`.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A C : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The complete question/answer pair reported at Introspect. -/
def introspectPair : ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .pair y a => some (y, a)
  | _ => none

/-- The full Introspect outcome predicted by an actual Sample answer. -/
def evaluatedSamplePair (P : CL.CLFun F ι ℓ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .pair z a => some (P.eval z, a)
  | _ => none

/-- Any selected seed readout, with a dummy malformed outcome. -/
def sampledCoarseZ (g : (ι → F) → C) (a : ParsedAnswer (ι → F) A PauliAnswer) :
    Option C := (sampleSeed a).map g

/-- A single Sample measurement jointly predicts the full Introspect answer
and the selected computational readout. -/
def sampleJointZ (P : CL.CLFun F ι ℓ) (g : (ι → F) → C)
    (a : ParsedAnswer (ι → F) A PauliAnswer) : Option ((ι → F) × A) × Option C :=
  (evaluatedSamplePair P a, sampledCoarseZ g a)

theorem check_sample_introspect_pair
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.sample w) (QuestionType.introspect w) a b = true) :
    evaluatedSamplePair (L w) a = introspectPair b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i z a y b
  have hd := TypedPredicate.check_directed_reversed L X Z projectPauli D DP h
  simp only [TypedPredicate.directed, ↓reduceIte] at hd
  have he : y = (L w).eval z ∧ b = a :=
    @of_decide_eq_true _ (Classical.propDecidable _) hd
  simp only [evaluatedSamplePair, introspectPair, he.1, he.2]

variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype C] [DecidableEq C]

/-- The first marginal of the joint Sample measurement, for a POVM in any ordered `⋆`-ring. -/
theorem sampleJointZ_left (P : CL.CLFun F ι ℓ) (g : (ι → F) → C)
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (y : Option ((ι → F) × A)) :
    (∑ c, (M.map (sampleJointZ P g)).op (y, c)) = (M.map (evaluatedSamplePair P)).op y :=
  POVMIn.sum_op_map_prod M (evaluatedSamplePair P) (sampledCoarseZ g) y

/-- The second marginal of the joint Sample measurement, for a POVM in any ordered `⋆`-ring. -/
theorem sampleJointZ_right (P : CL.CLFun F ι ℓ) (g : (ι → F) → C)
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (c : Option C) :
    (∑ y, (M.map (sampleJointZ P g)).op (y, c)) = (M.map (sampledCoarseZ g)).op c :=
  POVMIn.sum_op_map_prod' M (evaluatedSamplePair P) (sampledCoarseZ g) c

/-- Processing the actual sampled seed produces the selected seed readout, for a POVM in any
ordered `⋆`-ring. -/
theorem sampledCoarseZ_mapped (g : (ι → F) → C)
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (c : Option C) :
    fibSumIn (M.map sampleSeed).op (Option.map g) c = (M.map (sampledCoarseZ g)).op c := by
  rw [fibSumIn, ← POVMIn.map_op, POVMIn.map_map]
  rfl

/-- Ideal Z followed by any classical seed processing is the corresponding
computational readout on the same register. Both are honest register operators, embedded as
`smulKron 1` in the matrices over any algebra. -/
theorem idealZ_coarse_fibSum {R : Type*} [Ring R] [Algebra ℂ R] (g : (ι → F) → C)
    (c : Option C) :
    fibSumIn (fun z => smulKron (1 : R) (readout (some : (ι → F) → Option (ι → F)) z))
      (Option.map g) c = smulKron 1 (readout (fun z => some (g z)) c) := by
  rw [fibSumIn_smulKron_one, ← fibSum_eq_fibSumIn, fibSum_readout]
  rfl

variable [Fintype PauliType] [DecidableEq PauliType] [Fintype κ] [DecidableEq κ]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The actual Introspect operators almost commute with every chosen coarse
Z readout. Its joint witness and both marginal bounds come from actual Sample
measurements and tested game edges; no commutator or marginal estimate is an
extra hypothesis. -/
theorem introspect_coarseZ_commutator_bob [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    {ε η : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q) (w : Bool)
    (hS : IsPVMIn (MA (QuestionType.sample w, 0)).op)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ η)
    (g : (ι → F) → C) :
    (∑ a, ∑ c, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.introspect w, 0)).map introspectPair).op a *
        smulKron 1 (readout (fun z => some (g z)) c) -
       smulKron 1 (readout (fun z => some (g z)) c) *
        ((MB (QuestionType.introspect w, 0)).map introspectPair).op a)) ^ 2) ≤
      32 * η + 96 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hψ : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hsample := aux_pauli_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .sample w Z q hq
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_pauliZ_sample E X Z w))
    sampleSeed (pauliProjection projectPauli)
    (fun a b hab => check_sample_pauliZ_seed L X Z projectPauli D
      (fun p s => DP p s 0 q) w hab)
  have hseed := sampling_replace_bob (Ξ.reg (ι → F))
    (fun z => ((MA (QuestionType.sample w, 0)).map sampleSeed).op z)
    (fun z => ((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z)
    (fun z => smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z)) hsample hZ
  have hcoarse := (Ξ.reg (ι → F)).sum_xSqNorm_fibSum_le hψ
    (POVMIn.isPVMIn_map hS sampleSeed)
    (readout_isPVM (some : (ι → F) → Option (ι → F))).toIn.smulKron_one (Option.map g)
  simp only [sampledCoarseZ_mapped, idealZ_coarse_fibSum] at hcoarse
  have hright := hcoarse.trans hseed
  have hleft := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .sample .introspect w w (TypeGraph.adj_sample_introspect E X Z w)
    (evaluatedSamplePair (L w)) introspectPair
    (fun a b hab => check_sample_introspect_pair L X Z projectPauli D
      (fun p s => DP p s 0 0) w hab)
  let N : POVMIn (Option C) (Matrix (ι → F) (ι → F) ℬ) :=
    (readout_isPVM (fun z : ι → F => some (g z))).toIn.smulKron_one.toPOVMIn
  have ht := coarse_joint_commutator_bound (Ξ.reg (ι → F)).swap
    ((MB (QuestionType.introspect w, 0)).map introspectPair) N
    (MA (QuestionType.sample w, 0)) hS (sampleJointZ (L w) g)
  simp only [coarseJointLeftError, coarseJointRightError, sampleJointZ_left,
    sampleJointZ_right, N, IsPVMIn.toPOVMIn_op, BipartiteModel.xSqNorm_swap,
    BipartiteModel.stateSqNorm, BipartiteModel.stateNorm, BipartiteModel.swap_toStateModel,
    BipartiteModel.swap_πA] at ht
  linarith only [ht, hleft, hright]

/-- Every computational seed readout has an exact mirror on the register model of any bipartite
auxiliary model. -/
theorem coarseZ_registerState_mirror (g : (ι → F) → C) (c : C) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) :
    (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πA (smulKron 1 (readout g c))) (Ξ.reg (ι → F)).ψ =
      (Ξ.reg (ι → F)).π ((Ξ.reg (ι → F)).πB (smulKron 1 (readout g c))) (Ξ.reg (ι → F)).ψ := by
  have he := Ξ.reg_mirror (readout g c)
  rwa [show (readout g c)ᵀ = readout g c from Matrix.diagonal_transpose _] at he

/-- Alice's coarse Z commutator from the same primitive Bob-Z guarantee.
The actual Sample consistency loop transfers the fine seed estimate before
any coarse-graining. There is no additional Alice extraction hypothesis. -/
theorem introspect_coarseZ_commutator_alice [StarModule ℂ 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    {ε η : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q) (w : Bool)
    (hS : IsPVMIn (MB (QuestionType.sample w, 0)).op)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ η)
    (g : (ι → F) → C) :
    (∑ a, ∑ c, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.introspect w, 0)).map introspectPair).op a *
        smulKron 1 (readout (fun z => some (g z)) c) -
       smulKron 1 (readout (fun z => some (g z)) c) *
        ((MA (QuestionType.introspect w, 0)).map introspectPair).op a)) ≤
      64 * η + 224 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hψ : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hsample := aux_pauli_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .sample w Z q hq
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_pauliZ_sample E X Z w))
    sampleSeed (pauliProjection projectPauli)
    (fun a b hab => check_sample_pauliZ_seed L X Z projectPauli D
      (fun p s => DP p s 0 q) w hab)
  have hseed := sampling_replace_bob (Ξ.reg (ι → F))
    (fun z => ((MA (QuestionType.sample w, 0)).map sampleSeed).op z)
    (fun z => ((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z)
    (fun z => smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z)) hsample hZ
  have hdist := hseed
  simp only [xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
    (coarseZ_registerState_mirror (some : (ι → F) → Option (ι → F)) _ Ξ)] at hdist
  have hloop := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .sample .sample w w (TypeGraph.adj_self E X Z (QuestionType.sample w))
    sampleSeed sampleSeed (fun a b hab => congrArg sampleSeed
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have hseedB := (Ξ.reg (ι → F)).sum_xSqNorm_le_of_two_step
    (fun z => smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))
    (fun z => ((MA (QuestionType.sample w, 0)).map sampleSeed).op z)
    (fun z => ((MB (QuestionType.sample w, 0)).map sampleSeed).op z) hdist hloop
  have hcoarse := (Ξ.reg (ι → F)).sum_xSqNorm_fibSum_le hψ
    (readout_isPVM (some : (ι → F) → Option (ι → F))).toIn.smulKron_one
    (POVMIn.isPVMIn_map hS sampleSeed) (Option.map g)
  simp only [sampledCoarseZ_mapped, idealZ_coarse_fibSum] at hcoarse
  have hright := hcoarse.trans hseedB
  have hleft := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (Ξ.reg (ι → F)) hψ MA MB hfail
    .introspect .sample w w
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_sample_introspect E X Z w))
    introspectPair (evaluatedSamplePair (L w)) (fun a b hab => by
      have hf := TypedPredicate.check_formats L X Z projectPauli D (fun p s => DP p s 0 0) hab
      cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
      rename_i y a z b
      have he := TypedPredicate.check_sampling L X Z projectPauli D
        (fun p s => DP p s 0 0) w hab
      exact congrArg some (Prod.ext he.1 he.2))
  let N : POVMIn (Option C) (Matrix (ι → F) (ι → F) 𝒜) :=
    (readout_isPVM (fun z : ι → F => some (g z))).toIn.smulKron_one.toPOVMIn
  have ht := coarse_joint_commutator_bound (Ξ.reg (ι → F))
    ((MA (QuestionType.introspect w, 0)).map introspectPair) N
    (MB (QuestionType.sample w, 0)) hS (sampleJointZ (L w) g)
  simp only [coarseJointLeftError, coarseJointRightError, sampleJointZ_left,
    sampleJointZ_right, N, IsPVMIn.toPOVMIn_op] at ht
  linarith only [ht, hleft, hright]

end MIPRE.Introspection.TypedEstimates

end

end
