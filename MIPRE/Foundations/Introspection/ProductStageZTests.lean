/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SamplingRigidity
import MIPRE.Foundations.Introspection.HidingInduction
import MIPRE.Foundations.Introspection.HidingBaseOperators

/-! # Actual sampling tests imply coarse Z commutation

The common joint measurement is the actual Sample measurement: one marginal
records its evaluated question and original answer, while the other records
an arbitrary function of its seed. Both marginal estimates are obtained from
the parsed game and the extracted Pauli-Z estimate before applying the joint
commutation theorem. Malformed answers retain a dummy outcome throughout.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K C : Type*}
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
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C]

theorem sampleJointZ_left (P : CL.CLFun F ι ℓ) (g : (ι → F) → C)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (y : Option ((ι → F) × A)) :
    (∑ c, ((M.map (sampleJointZ P g)).mats (y, c)).val) =
      ((M.map (evaluatedSamplePair P)).mats y).val := by
  have hm := POVM.sum_mats_map_prod M (evaluatedSamplePair P) (sampledCoarseZ g) y
  convert hm using 1
  apply Finset.sum_congr rfl
  intro c _
  unfold sampleJointZ
  simp only [POVM.map_mats, Finset.sum_filter]

theorem sampleJointZ_right (P : CL.CLFun F ι ℓ) (g : (ι → F) → C)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (c : Option C) :
    (∑ y, ((M.map (sampleJointZ P g)).mats (y, c)).val) =
      ((M.map (sampledCoarseZ g)).mats c).val := by
  have hm := POVM.sum_mats_map_prod' M (evaluatedSamplePair P) (sampledCoarseZ g) c
  convert hm using 1
  apply Finset.sum_congr rfl
  intro y _
  unfold sampleJointZ
  simp only [POVM.map_mats, Finset.sum_filter]

theorem sampledCoarseZ_mapped (g : (ι → F) → C)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (c : Option C) :
    fibSum (fun z => ((M.map sampleSeed).mats z).val) (Option.map g) c =
      ((M.map (sampledCoarseZ g)).mats c).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
  rfl

/-- Ideal Z followed by any classical seed processing is the corresponding
computational readout on the same register. -/
theorem idealZ_coarse_fibSum (g : (ι → F) → C) (c : Option C) :
    fibSum (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) (Option.map g) c =
      aOp (readout (fun z => some (g z)) c) := by
  rw [fibSum_aOp, fibSum_readout]
  rfl

variable [Fintype PauliType] [DecidableEq PauliType] [Fintype κ] [DecidableEq κ]

set_option backward.isDefEq.respectTransparency false in
/-- The actual Introspect operators almost commute with every chosen coarse
Z readout. Its joint witness and both marginal bounds come from actual Sample
measurements and tested game edges; no commutator or marginal estimate is an
extra hypothesis. -/
theorem introspect_coarseZ_commutator_bob
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q) (w : Bool)
    (hS : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
    (g : (ι → F) → C) :
    (∑ a, ∑ c, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.introspect w, 0)).map introspectPair).mats a).val *
        (aOp (readout (fun z => some (g z)) c) : Matrix ((ι → F) × K) _ ℂ) -
       (aOp (readout (fun z => some (g z)) c) : Matrix ((ι → F) × K) _ ℂ) *
        (((MB (QuestionType.introspect w, 0)).map introspectPair).mats a).val)) ^ 2) ≤
      32 * η + 96 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hψ : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hsample := aux_pauli_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample w Z q hq
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_pauliZ_sample E X Z w))
    sampleSeed (pauliProjection projectPauli)
    (fun a b hab => check_sample_pauliZ_seed L X Z projectPauli D
      (fun p s => DP p s 0 q) w hab)
  have hseed := sampling_replace_bob (registerState (ι → F) ξ)
    (fun z => (((MA (QuestionType.sample w, 0)).map sampleSeed).mats z).val)
    (fun z => (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val)
    (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) hsample hZ
  have hcoarse := sum_xSqNorm_fibSum_le (norm_evec_eq_one_of_unit hψ)
    (isPVM_povm_map (MA (QuestionType.sample w, 0)) hS sampleSeed)
    (readout_isPVM (some : (ι → F) → Option (ι → F))).aOp (Option.map g)
  simp only [sampledCoarseZ_mapped, idealZ_coarse_fibSum] at hcoarse
  have hright := hcoarse.trans hseed
  have hleft := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample .introspect w w (TypeGraph.adj_sample_introspect E X Z w)
    (evaluatedSamplePair (L w)) introspectPair
    (fun a b hab => check_sample_introspect_pair L X Z projectPauli D
      (fun p s => DP p s 0 0) w hab)
  let N : POVM (Option C) ((ι → F) × K) :=
    (IsPVM.aOp (dB := K) (readout_isPVM (fun z : ι → F => some (g z)))).toPOVM
  have ht := coarse_joint_commutator_bound (swapVec (registerState (ι → F) ξ))
    ((MB (QuestionType.introspect w, 0)).map introspectPair) N
    (MA (QuestionType.sample w, 0)) hS (sampleJointZ (L w) g)
  simp only [coarseJointLeftError, coarseJointRightError, sampleJointZ_left,
    sampleJointZ_right, N, IsPVM.toPOVM_mats,
    xSqNorm_eq_snorm_sq, snorm_swapVec_aOp_sub_bOp,
    stateSqNorm, ← norm_stateVecB, norm_stateVecB_eq_snorm] at ht
  simp only [← xSqNorm_eq_sq] at ht
  linarith only [ht, hleft, hright]

variable [Algebra (ZMod 2) F]

/-- Every computational seed readout has an exact mirror on the extracted
EPR register, including with arbitrary auxiliary state. -/
theorem coarseZ_registerState_mirror (g : (ι → F) → C) (c : C) (ξ : H × K → ℂ) :
    aOp (aOp (readout g c) : Matrix ((ι → F) × H) _ ℂ) *ᵥ registerState (ι → F) ξ =
      bOp (aOp (readout g c) : Matrix ((ι → F) × K) _ ℂ) *ᵥ registerState (ι → F) ξ := by
  have he := Weyl.stateVec_epr (readout g c)
  have ht : (readout g c)ᵀ = readout g c := Matrix.diagonal_transpose _
  rw [ht, ← registerEPR_eq_weyl] at he
  exact congrArg WithLp.ofLp (mirror_expVec (registerEPR (ι → F)) ξ _ _ he)

set_option backward.isDefEq.respectTransparency false in
/-- Alice's coarse Z commutator from the same primitive Bob-Z guarantee.
The actual Sample consistency loop transfers the fine seed estimate before
any coarse-graining. There is no additional Alice extraction hypothesis. -/
theorem introspect_coarseZ_commutator_alice
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q) (w : Bool)
    (hS : IsPVM (fun a => ((MB (QuestionType.sample w, 0)).mats a).val))
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
    (g : (ι → F) → C) :
    (∑ a, ∑ c, stateSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val *
        (aOp (readout (fun z => some (g z)) c) : Matrix ((ι → F) × H) _ ℂ) -
       (aOp (readout (fun z => some (g z)) c) : Matrix ((ι → F) × H) _ ℂ) *
        (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val)) ≤
      64 * η + 224 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hψ : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hsample := aux_pauli_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample w Z q hq
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_pauliZ_sample E X Z w))
    sampleSeed (pauliProjection projectPauli)
    (fun a b hab => check_sample_pauliZ_seed L X Z projectPauli D
      (fun p s => DP p s 0 q) w hab)
  have hseed := sampling_replace_bob (registerState (ι → F) ξ)
    (fun z => (((MA (QuestionType.sample w, 0)).map sampleSeed).mats z).val)
    (fun z => (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val)
    (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) hsample hZ
  have hdist := hseed
  simp only [xSqNorm_eq_stateSqNorm_of_mirror _ _ _ _
    (coarseZ_registerState_mirror (some : (ι → F) → Option (ι → F)) _ ξ)] at hdist
  have hloop := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .sample .sample w w (TypeGraph.adj_self E X Z (QuestionType.sample w))
    sampleSeed sampleSeed (fun a b hab => congrArg sampleSeed
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have hseedB := sum_xSqNorm_le_of_two_step
    (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × H) _ ℂ))
    (fun z => (((MA (QuestionType.sample w, 0)).map sampleSeed).mats z).val)
    (fun z => (((MB (QuestionType.sample w, 0)).map sampleSeed).mats z).val) hdist hloop
  have hcoarse := sum_xSqNorm_fibSum_le (norm_evec_eq_one_of_unit hψ)
    (readout_isPVM (some : (ι → F) → Option (ι → F))).aOp
    (isPVM_povm_map (MB (QuestionType.sample w, 0)) hS sampleSeed) (Option.map g)
  simp only [sampledCoarseZ_mapped, idealZ_coarse_fibSum] at hcoarse
  have hright := hcoarse.trans hseedB
  have hleft := aux_agreement_estimate E X Z P
    (questionCheck L X Z projectPauli D DP) (registerState (ι → F) ξ) hψ MA MB hfail
    .introspect .sample w w
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_sample_introspect E X Z w))
    introspectPair (evaluatedSamplePair (L w)) (fun a b hab => by
      have hf := TypedPredicate.check_formats L X Z projectPauli D (fun p s => DP p s 0 0) hab
      cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
      rename_i y a z b
      have he := TypedPredicate.check_sampling L X Z projectPauli D
        (fun p s => DP p s 0 0) w hab
      exact congrArg some (Prod.ext he.1 he.2))
  let N : POVM (Option C) ((ι → F) × H) :=
    (IsPVM.aOp (dB := H) (readout_isPVM (fun z : ι → F => some (g z)))).toPOVM
  have ht := coarse_joint_commutator_bound (registerState (ι → F) ξ)
    ((MA (QuestionType.introspect w, 0)).map introspectPair) N
    (MB (QuestionType.sample w, 0)) hS (sampleJointZ (L w) g)
  simp only [coarseJointLeftError, coarseJointRightError, sampleJointZ_left,
    sampleJointZ_right, N, IsPVM.toPOVM_mats] at ht
  linarith only [ht, hleft, hright]

end MIPRE.Introspection.TypedEstimates

end
