/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.RegisteredExtensionErrors
public import MIPRE.Foundations.Introspection.ReadRigidityGame

@[expose] public section

/-! # The errors at unchanged questions survive adaptive replacement exactly

The replacement at the selected question is arbitrary. Every other question
is the concrete identity extension in the original register ordering.
Consequently the primitive Pauli estimates and the hiding and Read estimates
can be reused at the next induction stage without an additional error.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the old register state is the
register model `Ξ.reg I`, the new one the register model `(Ξ.expandA t₀).reg I` of the auxiliary
model extended by a first-player ancilla in the fixed state `t₀`. At an unchanged question the
registered replacement is the old measurement carried along the registered extension
`registeredExtend Ξ t₀` (`registeredExtendPOVM`), a local isometry taking the state to the state,
so every error is transported exactly. An honest register operator enters as `smulKron 1 J` and
is fixed by the extension (`registeredExtendOp_aOp`); the second player's operators are unchanged.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

section Generic
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜]
variable {X I T A B : Type*}
  [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype A] [Fintype B] [DecidableEq B]

theorem registeredReplacement_other_eq (MA : X → POVMIn A (Matrix I I 𝒜)) (q x : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) (hx : x ≠ q) :
    registeredReplacement MA q R x = registeredExtendPOVM (MA x) :=
  registeredReplacement_other MA q x R hx

/-- Outcome maps, including their malformed outcome, are transported exactly. -/
theorem registeredReplacement_other_map (MA : X → POVMIn A (Matrix I I 𝒜)) (q x : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) (hx : x ≠ q) (f : A → B) :
    (registeredReplacement MA q R x).map f = registeredExtendPOVM ((MA x).map f) := by
  rw [registeredReplacement_other_eq MA q x R hx, registeredExtendPOVM_map]

theorem registeredReplacement_samePartyError_other
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) (MA : X → POVMIn A (Matrix I I 𝒜)) (q x : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) (hx : x ≠ q) (f : A → B)
    (J : B → Matrix I I ℂ) :
    (∑ b, ((Ξ.expandA t₀).reg I).stateSqNorm
      (((registeredReplacement MA q R x).map f).op b - smulKron 1 (J b))) =
      ∑ b, (Ξ.reg I).stateSqNorm (((MA x).map f).op b - smulKron 1 (J b)) := by
  rw [registeredReplacement_other_map MA q x R hx f]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [registeredExtendPOVM_mats, ← registeredExtendOp_aOp, ← registeredExtendOp_sub,
    stateSqNorm_registeredExtendOp]

theorem registeredReplacement_crossError_other
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) (MA : X → POVMIn A (Matrix I I 𝒜)) (q x : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) (hx : x ≠ q) (f : A → B)
    (N : B → Matrix I I ℬ) :
    (∑ b, ((Ξ.expandA t₀).reg I).xSqNorm
      (((registeredReplacement MA q R x).map f).op b) (N b)) =
      ∑ b, (Ξ.reg I).xSqNorm (((MA x).map f).op b) (N b) := by
  rw [registeredReplacement_other_map MA q x R hx f]
  simp only [registeredExtendPOVM_mats, xSqNorm_registeredExtendOp]

omit [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] in
theorem registeredExtension_bobCrossError
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) (J : B → Matrix I I ℂ)
    (N : B → Matrix I I ℬ) :
    (∑ b, ((Ξ.expandA t₀).reg I).xSqNorm (smulKron 1 (J b)) (N b)) =
      ∑ b, (Ξ.reg I).xSqNorm (smulKron 1 (J b)) (N b) := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← registeredExtendOp_aOp, xSqNorm_registeredExtendOp]

omit [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] in
theorem registeredExtension_bobSamePartyError
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) (N : B → Matrix I I ℬ) :
    (∑ b, ((Ξ.expandA t₀).reg I).snorm (((Ξ.expandA t₀).reg I).πB (N b)) ^ 2) =
      ∑ b, (Ξ.reg I).snorm ((Ξ.reg I).πB (N b)) ^ 2 := by
  simp only [snorm_bOp_registered_extVecA]

end Generic

namespace TypedEstimates
variable {PauliType PauliAnswer F ι κ A T : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype T] [DecidableEq T] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-! ### The first player's errors at the unchanged questions -/

section Alice
variable [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

theorem hidingAliceError_registeredReplacement
    (L : Bool → CL.CLFun F ι ℓ) (w v : Bool) (hL : (L w).SupportedOn univ)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (R : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix T T (Matrix (ι → F) (ι → F) 𝒜)))
    (j : Fin ℓ) :
    hidingAliceError L w hL (Ξ.expandA t₀)
      (registeredReplacement MA (QuestionType.introspect v, 0) R) j =
      hidingAliceError L w hL Ξ MA j := by
  exact registeredReplacement_crossError_other Ξ t₀ MA _ _ R (by simp)
    (hidingCoarse (L w) j.val) (fun i => smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i))

theorem readAliceError_registeredReplacement
    (L : Bool → CL.CLFun F ι ℓ) (w v : Bool) (hL : (L w).SupportedOn univ)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (R : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix T T (Matrix (ι → F) (ι → F) 𝒜)))
    (j : Fin ℓ) :
    readAliceError L w hL (Ξ.expandA t₀)
      (registeredReplacement MA (QuestionType.introspect v, 0) R) j =
      readAliceError L w hL Ξ MA j := by
  exact registeredReplacement_crossError_other Ξ t₀ MA _ _ R (by simp)
    (reportedDual (L w) j.val .read) (fun i => smulKron 1 (Honest.readDualOp (L w) j.val hL i))

/-- The primitive Alice Pauli estimate, for any fixed register ideal, is
unchanged when an Introspect question is replaced. -/
theorem pauliAliceError_registeredReplacement
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) (projectPauli : PauliAnswer → ι → F)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (R : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix T T (Matrix (ι → F) (ι → F) 𝒜)))
    (v : Bool) (p : PauliType) (q : κ → ZMod 2)
    (J : Option (ι → F) → Matrix (ι → F) (ι → F) ℂ) :
    (∑ z, ((Ξ.expandA t₀).reg (ι → F)).stateSqNorm
      (((registeredReplacement MA (QuestionType.introspect v, 0) R
        (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).op z - smulKron 1 (J z))) =
    ∑ z, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (J z)) := by
  exact registeredReplacement_samePartyError_other Ξ t₀ MA _ _ R (by simp)
    (pauliProjection projectPauli) J

end Alice

/-! ### The second player's errors on the extended state -/

section Bob
variable [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]

theorem hidingBobError_registeredExtension
    (L : Bool → CL.CLFun F ι ℓ) (w : Bool) (hL : (L w).SupportedOn univ)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) (j : Fin ℓ) :
    hidingBobError L w hL (Ξ.expandA t₀) MB j = hidingBobError L w hL Ξ MB j :=
  registeredExtension_bobCrossError Ξ t₀ (Honest.hideCoarseOp (L w) j.val hL)
    (fun i => ((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)

theorem readBobError_registeredExtension
    (L : Bool → CL.CLFun F ι ℓ) (w : Bool) (hL : (L w).SupportedOn univ)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) (j : Fin ℓ) :
    readBobError L w hL (Ξ.expandA t₀) MB j = readBobError L w hL Ξ MB j :=
  registeredExtension_bobCrossError Ξ t₀ (Honest.readDualOp (L w) j.val hL)
    (fun i => ((MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).op i)

/-- The primitive Bob Pauli estimate is unchanged on the newly extended
state; Bob's actual family is literally retained. -/
theorem pauliBobError_registeredExtension
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) (projectPauli : PauliAnswer → ι → F)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (p : PauliType) (q : κ → ZMod 2)
    (J : Option (ι → F) → Matrix (ι → F) (ι → F) ℂ) :
    (∑ z, ((Ξ.expandA t₀).reg (ι → F)).snorm (((Ξ.expandA t₀).reg (ι → F)).πB
      (((MB (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (J z))) ^ 2) =
    ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli p, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (J z))) ^ 2 :=
  registeredExtension_bobSamePartyError Ξ t₀ _

end Bob

end TypedEstimates
end MIPRE.Introspection
end

end
