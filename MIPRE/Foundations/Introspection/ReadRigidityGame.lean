/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingRigidityGame
import MIPRE.Foundations.Introspection.ReadRigidity

/-! # Full Read rigidity from game success and primitive Pauli estimates

The complete hiding theorem supplies the input of the actual hiding-to-Read
chain. The resulting estimates hold for every dual prefix and both players,
with one explicit bound independent of the question and answer alphabets.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

def readAliceError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (j : Fin ℓ) : ℝ :=
  ∑ z, xSqNorm (registerState (ι → F) ξ)
    ((((MA (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).mats z).val)
    (aOp (readDualOp (L w) j.val hL z) : Matrix ((ι → F) × K) _ ℂ)

def readBobError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) : ℝ :=
  ∑ z, xSqNorm (registerState (ι → F) ξ)
    (aOp (readDualOp (L w) j.val hL z) : Matrix ((ι → F) × H) _ ℂ)
    ((((MB (QuestionType.read w, 0)).map (reportedDual (L w) j.val .read)).mats z).val)

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
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε δX ηZ : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    (hPX : IsPVM (fun a => ((MA (QuestionType.pauli X, qX)).mats a).val))
    (hX : ∑ x, stateSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val -
        (aOp (pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ δX)
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ)))^2 ≤ ηZ)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
    (hMA : ∀ j : Fin ℓ, IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val))
    (hMB : ∀ j : Fin ℓ, IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
    (j : Fin ℓ) :
    readAliceError L w hL ξ MA j ≤
      (16*(ℓ:ℝ)^2+8)*((TypeGraph.edges E X Z ℓ).card*ε) +
        4*hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ ∧
    readBobError L w hL ξ MB j ≤
      (32*(ℓ:ℝ)^2+20)*((TypeGraph.edges E X Z ℓ).card*ε) +
        8*hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ := by
  have hh := hiding_register_rigidity_of_pauli E X Z P L projectPauli D DP
    ξ hξ MA MB hfail qX qZ hqX hqZ hPX hX hZ w hL hS hMA hMB j
  have ha := read_register_rigidity_alice E X Z P L projectPauli D DP
    ξ hξ MA MB hfail w hL j (hMA j) hh.2
  have hb := read_register_rigidity_bob E X Z P L projectPauli D DP
    ξ hξ MA MB hfail w hL j (hMA j) hh.2
  have hunit : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hε : 0 ≤ ε := by
    apply le_trans ?_ hfail
    rw [one_sub_povmValue_eq]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg ((parsedGame E X Z P L projectPauli D DP).μ_nonneg x y)
        (condFail_nonneg hunit x y)
  have he : 0 ≤ ((TypeGraph.edges E X Z ℓ).card:ℝ)*ε :=
    mul_nonneg (Nat.cast_nonneg _) hε
  have hn : ((ℓ-j.val:ℕ):ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast Nat.sub_le ℓ j.val
  have hsq : ((ℓ-j.val:ℕ):ℝ)^2 ≤ (ℓ:ℝ)^2 := by
    have hz : (0:ℝ) ≤ ((ℓ-j.val:ℕ):ℝ) := Nat.cast_nonneg _
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hsq he
  change readAliceError L w hL ξ MA j ≤ _ at ha
  change readBobError L w hL ξ MB j ≤ _ at hb
  constructor <;> nlinarith

end MIPRE.Introspection.TypedEstimates

end
