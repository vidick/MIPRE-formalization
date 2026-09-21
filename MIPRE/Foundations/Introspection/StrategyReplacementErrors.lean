/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RegisteredExtensionErrors
import MIPRE.Foundations.Introspection.ReadRigidityGame

/-! # The errors at unchanged questions survive adaptive replacement exactly

The replacement at the selected question is arbitrary. Every other question
is the concrete identity extension in the original register ordering.
Consequently the primitive Pauli estimates and the hiding and Read estimates
can be reused at the next induction stage without an additional error.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

section Generic
variable {X I H K T A B : Type*}
  [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T] [Fintype A] [Fintype B] [DecidableEq B]

theorem registeredReplacement_other_eq (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) :
    registeredReplacement MA q R x = registeredExtendPOVM (MA x) :=
  registeredReplacement_other MA q x R hx

/-- Outcome maps, including their malformed outcome, are transported exactly. -/
theorem registeredReplacement_other_map (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) (f : A → B) :
    (registeredReplacement MA q R x).map f = registeredExtendPOVM ((MA x).map f) := by
  rw [registeredReplacement_other_eq MA q x R hx, registeredExtendPOVM_map]

/-- Projectivity at an unchanged question does not depend on projectivity
of the selected replacement. -/
theorem registeredReplacement_other_isPVM (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q)
    (hM : IsPVM (fun a => ((MA x).mats a).val)) :
    IsPVM (fun a => ((registeredReplacement MA q R x).mats a).val) := by
  rw [registeredReplacement_other_eq MA q x R hx]
  exact registeredExtendPOVM_isPVM (MA x) hM

theorem registeredReplacement_samePartyError_other
    (ξ : H × K → ℂ) (a₀ : T) (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) (f : A → B)
    (J : B → Matrix I I ℂ) :
    (∑ b, stateSqNorm (registerState I (extVecA ξ a₀))
      ((((registeredReplacement MA q R x).map f).mats b).val - aOp (J b))) =
      ∑ b, stateSqNorm (registerState I ξ) ((((MA x).map f).mats b).val - aOp (J b)) := by
  rw [registeredReplacement_other_map MA q x R hx f]
  apply Finset.sum_congr rfl
  intro b _
  rw [registeredExtendPOVM_mats, ← registeredExtendOp_aOp,
    ← registeredExtendOp_sub, stateSqNorm_registeredExtendOp]

theorem registeredReplacement_crossError_other
    (ξ : H × K → ℂ) (a₀ : T) (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) (f : A → B)
    (N : B → Matrix (I × K) (I × K) ℂ) :
    (∑ b, xSqNorm (registerState I (extVecA ξ a₀))
      ((((registeredReplacement MA q R x).map f).mats b).val) (N b)) =
      ∑ b, xSqNorm (registerState I ξ) ((((MA x).map f).mats b).val) (N b) := by
  rw [registeredReplacement_other_map MA q x R hx f]
  simp only [registeredExtendPOVM_mats, xSqNorm_registeredExtendOp]

theorem registeredExtension_bobCrossError
    (ξ : H × K → ℂ) (a₀ : T) (J : B → Matrix I I ℂ)
    (N : B → Matrix (I × K) (I × K) ℂ) :
    (∑ b, xSqNorm (registerState I (extVecA ξ a₀)) (aOp (J b)) (N b)) =
      ∑ b, xSqNorm (registerState I ξ) (aOp (J b)) (N b) := by
  apply Finset.sum_congr rfl
  intro b _
  rw [← registeredExtendOp_aOp, xSqNorm_registeredExtendOp]

theorem registeredExtension_bobSamePartyError
    (ξ : H × K → ℂ) (a₀ : T) (N : B → Matrix (I × K) (I × K) ℂ) :
    (∑ b, snorm (registerState I (extVecA ξ a₀)) (bOp (N b)) ^ 2) =
      ∑ b, snorm (registerState I ξ) (bOp (N b)) ^ 2 := by
  simp only [snorm_bOp_registered_extVecA]

/-- Any unchanged pair of questions has exactly its old outcome law. -/
theorem registeredReplacement_bornProb_other
    (ξ : H × K → ℂ) (a₀ : T) (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) (a : A)
    (N : Matrix (I × K) (I × K) ℂ) :
    bornProb (registerState I (extVecA ξ a₀))
      ((registeredReplacement MA q R x).mats a).val N =
      bornProb (registerState I ξ) ((MA x).mats a).val N := by
  rw [registeredReplacement_other_eq MA q x R hx, registeredExtendPOVM_mats,
    bornProb_registeredExtendOp]

/-- An arbitrary weighted consistency test supported away from the replaced
question is preserved, without assumptions on the replacement measurement. -/
theorem inconsistency_registeredReplacement_away [DecidableEq A]
    (μ : X → ℝ) (ξ : H × K → ℂ) (a₀ : T)
    (MA : X → POVM A (I × H)) (MB : X → POVM A (I × K)) (q : X)
    (R : POVM A ((I × H) × T)) (hq : μ q = 0) :
    inconsistency μ (registerState I (extVecA ξ a₀)) (registeredReplacement MA q R) MB =
      inconsistency μ (registerState I ξ) MA MB := by
  unfold inconsistency
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = q
  · subst x
    simp only [hq, zero_mul]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · simp only [hab, if_pos]
    · simp only [if_neg hab]
      exact registeredReplacement_bornProb_other ξ a₀ MA q x R hx a ((MB x).mats b).val

theorem xPovmDist_registeredReplacement_away [DecidableEq A]
    (μ : X → ℝ) (ξ : H × K → ℂ) (a₀ : T)
    (MA : X → POVM A (I × H)) (MB : X → POVM A (I × K)) (q : X)
    (R : POVM A ((I × H) × T)) (hq : μ q = 0) :
    xPovmDist μ (registerState I (extVecA ξ a₀)) (registeredReplacement MA q R) MB =
      xPovmDist μ (registerState I ξ) MA MB := by
  unfold xPovmDist
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = q
  · subst x
    simp only [hq, zero_mul]
  · rw [registeredReplacement_other_eq MA q x R hx]
    simp only [registeredExtendPOVM_mats, xSqNorm_registeredExtendOp]

end Generic

namespace TypedEstimates
variable {PauliType PauliAnswer F ι κ A H K T : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T] {ℓ : ℕ}

theorem hidingAliceError_registeredReplacement
    (L : Bool → CL.CLFun F ι ℓ) (w v : Bool) (hL : (L w).SupportedOn univ)
    (ξ : H × K → ℂ) (a₀ : T)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (R : POVM (ParsedAnswer (ι → F) A PauliAnswer) (((ι → F) × H) × T)) (j : Fin ℓ) :
    hidingAliceError L w hL (extVecA ξ a₀)
      (registeredReplacement MA (QuestionType.introspect v, 0) R) j =
      hidingAliceError L w hL ξ MA j := by
  exact registeredReplacement_crossError_other ξ a₀ MA _ _ R (by simp)
    (hidingCoarse (L w) j.val) (fun i => aOp (Honest.hideCoarseOp (L w) j.val hL i))

theorem hidingBobError_registeredExtension
    (L : Bool → CL.CLFun F ι ℓ) (w : Bool) (hL : (L w).SupportedOn univ)
    (ξ : H × K → ℂ) (a₀ : T)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) :
    hidingBobError L w hL (extVecA ξ a₀) MB j = hidingBobError L w hL ξ MB j :=
  registeredExtension_bobCrossError ξ a₀ (Honest.hideCoarseOp (L w) j.val hL)
    (fun i => (((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)

theorem readAliceError_registeredReplacement
    (L : Bool → CL.CLFun F ι ℓ) (w v : Bool) (hL : (L w).SupportedOn univ)
    (ξ : H × K → ℂ) (a₀ : T)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (R : POVM (ParsedAnswer (ι → F) A PauliAnswer) (((ι → F) × H) × T)) (j : Fin ℓ) :
    readAliceError L w hL (extVecA ξ a₀)
      (registeredReplacement MA (QuestionType.introspect v, 0) R) j =
      readAliceError L w hL ξ MA j := by
  exact registeredReplacement_crossError_other ξ a₀ MA _ _ R (by simp)
    (reportedDual (L w) j.val .read) (fun i => aOp (Honest.readDualOp (L w) j.val hL i))

theorem readBobError_registeredExtension
    (L : Bool → CL.CLFun F ι ℓ) (w : Bool) (hL : (L w).SupportedOn univ)
    (ξ : H × K → ℂ) (a₀ : T)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) :
    readBobError L w hL (extVecA ξ a₀) MB j = readBobError L w hL ξ MB j :=
  registeredExtension_bobCrossError ξ a₀ (Honest.readDualOp (L w) j.val hL)
    (fun i => (((MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).mats i).val)

/-- The primitive Alice Pauli estimate, for any fixed register ideal, is
unchanged when an Introspect question is replaced. -/
theorem pauliAliceError_registeredReplacement
    (ξ : H × K → ℂ) (a₀ : T) (projectPauli : PauliAnswer → ι → F)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (R : POVM (ParsedAnswer (ι → F) A PauliAnswer) (((ι → F) × H) × T))
    (v : Bool) (p : PauliType) (q : κ → ZMod 2)
    (J : Option (ι → F) → Matrix (ι → F) (ι → F) ℂ) :
    (∑ z, stateSqNorm (registerState (ι → F) (extVecA ξ a₀))
      (((((registeredReplacement MA (QuestionType.introspect v, 0) R)
        (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).mats z).val - aOp (J z))) =
    ∑ z, stateSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).mats z).val - aOp (J z)) := by
  exact registeredReplacement_samePartyError_other ξ a₀ MA _ _ R (by simp)
    (pauliProjection projectPauli) J

/-- The primitive Bob Pauli estimate is unchanged on the newly extended
state; Bob's actual family is literally retained. -/
theorem pauliBobError_registeredExtension
    (ξ : H × K → ℂ) (a₀ : T) (projectPauli : PauliAnswer → ι → F)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (p : PauliType) (q : κ → ZMod 2)
    (J : Option (ι → F) → Matrix (ι → F) (ι → F) ℂ) :
    (∑ z, snorm (registerState (ι → F) (extVecA ξ a₀)) (bOp
      ((((MB (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (J z) : Matrix ((ι → F) × K) _ ℂ))) ^ 2) =
    ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (J z) : Matrix ((ι → F) × K) _ ℂ))) ^ 2 := by
  exact registeredExtension_bobSamePartyError ξ a₀ _

end TypedEstimates
end MIPRE.Introspection
end
