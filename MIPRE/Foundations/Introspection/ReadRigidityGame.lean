/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.HidingRigidityGame
public import MIPRE.Foundations.Introspection.ReadRigidity

@[expose] public section

/-! # Full Read rigidity from game success and primitive Pauli estimates

The complete hiding theorem supplies the input of the actual hiding-to-Read
chain. The resulting estimates hold for every dual prefix and both players,
with one explicit bound independent of the question and answer alphabets.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, the measurements are POVMs
in its algebras, and the honest readouts enter as `smulKron 1 _`.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

def readAliceError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (j : Fin ℓ) : ℝ :=
  ∑ z, (Ξ.reg (ι → F)).xSqNorm
    (((MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).op z)
    (smulKron 1 (readDualOp (L w) j.val hL z))

def readBobError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) (j : Fin ℓ) : ℝ :=
  ∑ z, (Ξ.reg (ι → F)).xSqNorm
    (smulKron 1 (readDualOp (L w) j.val hL z))
    (((MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).op z)

/-- Both actual Read families are rigid at every dual prefix. The inputs are
game success and the extracted X/Z estimates, without a Read or hiding
rigidity premise. No projectivity of either Read measurement is needed. -/
theorem read_register_rigidity_of_pauli
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
    {ε δX ηZ : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    (hPX : IsPVMIn (MA (QuestionType.pauli X, qX)).op)
    (hX : ∑ x, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x -
        smulKron 1 (pauliXReadout x)) ≤ δX)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ ηZ)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVMIn (MA (QuestionType.sample w, 0)).op)
    (hMA : ∀ j : Fin ℓ, IsPVMIn (MA (QuestionType.hide w j, 0)).op)
    (hMB : ∀ j : Fin ℓ, IsPVMIn (MB (QuestionType.hide w j, 0)).op)
    (j : Fin ℓ) :
    readAliceError L w hL Ξ MA j ≤
      (16*(ℓ:ℝ)^2+8)*((TypeGraph.edges E X Z ℓ).card*ε) +
        4*hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ ∧
    readBobError L w hL Ξ MB j ≤
      (32*(ℓ:ℝ)^2+20)*((TypeGraph.edges E X Z ℓ).card*ε) +
        8*hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ := by
  have hh := hiding_register_rigidity_of_pauli E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail qX qZ hqX hqZ hPX hX hZ w hL hS hMA hMB j
  have ha := read_register_rigidity_alice E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail w hL j (hMA j) hh.2
  have hb := read_register_rigidity_bob E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail w hL j (hMA j) hh.2
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hε : 0 ≤ ε := by
    apply le_trans ?_ hfail
    rw [(Ξ.reg (ι → F)).one_sub_povmValue_eq]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg ((parsedGame E X Z P L projectPauli D DP).μ_nonneg x y)
        ((Ξ.reg (ι → F)).condFail_nonneg hunit x y)
  have he : 0 ≤ ((TypeGraph.edges E X Z ℓ).card:ℝ)*ε :=
    mul_nonneg (Nat.cast_nonneg _) hε
  have hn : ((ℓ-j.val:ℕ):ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast Nat.sub_le ℓ j.val
  have hsq : ((ℓ-j.val:ℕ):ℝ)^2 ≤ (ℓ:ℝ)^2 := by
    have hz : (0:ℝ) ≤ ((ℓ-j.val:ℕ):ℝ) := Nat.cast_nonneg _
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hsq he
  change readAliceError L w hL Ξ MA j ≤ _ at ha
  change readBobError L w hL Ξ MB j ≤ _ at hb
  constructor <;> nlinarith

end MIPRE.Introspection.TypedEstimates

end

end
