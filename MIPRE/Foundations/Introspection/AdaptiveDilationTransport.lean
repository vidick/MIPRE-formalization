/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.StrategyReplacementRegister

/-! # Conditional Naimark projectors in adaptive register coordinates

A residual dilation is pulled back through the actual coordinate split.
Compression and reassociation are exact, and the next linear-map readout is
retained as an explicit tensor factor of the new projective measurement.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {V I R H K Y A : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]

/-- Ancilla compression commutes with a relabelling of the old register. -/
theorem ancilla_compress_registerOp (e : V ≃ I) (a₀ : A)
    (M : Matrix (I × A) (I × A) ℂ) :
    (ancillaEmbed V a₀)ᴴ *
      (registerOp (e.prodCongr (Equiv.refl A)) M * ancillaEmbed V a₀) =
      registerOp e ((ancillaEmbed I a₀)ᴴ * (M * ancillaEmbed I a₀)) := by
  ext i j
  simp only [ancilla_compress_apply, registerOp_apply]
  rfl

/-- The conditional joint PVM on the original remaining register plus one
fixed ancilla. -/
def transportedConditionalDilation (e : V ≃ I × R) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ) (p : Y × A) :
    Matrix ((V × H) × A) ((V × H) × A) ℂ :=
  registerOp ((registerParty e H).prodCongr (Equiv.refl A)) (conditionalDilationOp Z P p)

theorem transportedConditionalDilation_isPVM (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ)
    (hP : ∀ y, IsPVM (P y)) : IsPVM (transportedConditionalDilation e Z P) :=
  registerOp_isPVM _ (conditionalDilationOp_isPVM Z hZ P hP)

theorem transportedConditionalDilation_compress (e : V ≃ I × R) (a₀ : A)
    (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ)
    (Q : Y → POVM A (R × H))
    (hk : ∀ y a, (ancillaEmbed (R × H) a₀)ᴴ * (P y a * ancillaEmbed (R × H) a₀) =
      ((Q y).mats a).val) (p : Y × A) :
    (ancillaEmbed (V × H) a₀)ᴴ *
      (transportedConditionalDilation e Z P p * ancillaEmbed (V × H) a₀) =
      registerOp (registerParty e H) (Z p.1 ⊗ₖ ((Q p.1).mats p.2).val) := by
  rw [transportedConditionalDilation, ancilla_compress_registerOp,
    conditionalDilationOp_compress a₀ Z P (fun y a => ((Q y).mats a).val) hk]

/-- The same PVM with the fresh ancilla absorbed into the auxiliary register. -/
def reassociatedConditionalDilation (e : V ≃ I × R) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ) (p : Y × A) :
    Matrix (V × (H × A)) (V × (H × A)) ℂ :=
  registerOp (Equiv.prodAssoc V H A).symm (transportedConditionalDilation e Z P p)

theorem reassociatedConditionalDilation_isPVM (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ)
    (hP : ∀ y, IsPVM (P y)) : IsPVM (reassociatedConditionalDilation e Z P) :=
  registerOp_isPVM _ (transportedConditionalDilation_isPVM e Z hZ P hP)

/-- The new readout remains an exact tensor factor. The second factor is
the dilated residual operator on precisely the remaining coordinates. -/
theorem reassociatedConditionalDilation_factor (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ) (p : Y × A) :
    reassociatedConditionalDilation e Z P p =
      registerOp (registerParty e (H × A))
        (Z p.1 ⊗ₖ registerOp (Equiv.prodAssoc R H A).symm (P p.1 p.2)) := by
  ext i j
  rfl

/-- Reassociation transports the squared error exactly to the new register
state, with no state replacement or dimension factor. -/
theorem stateSqNorm_reassociated_extVecA (ξ : H × K → ℂ) (a₀ : A)
    (M : Matrix ((V × H) × A) ((V × H) × A) ℂ) :
    stateSqNorm (registerState V (extVecA ξ a₀))
      (registerOp (Equiv.prodAssoc V H A).symm M) =
      stateSqNorm (extVecA (registerState V ξ) a₀) M := by
  have hs : (extVecA (registerState V ξ) a₀) ∘
      ((Equiv.prodAssoc V H A).symm.prodCongr (Equiv.refl (V × K))) =
        registerState V (extVecA ξ a₀) :=
    reindex_extVecA_registerState ξ a₀
  rw [← hs, stateSqNorm_registerOp]

end MIPRE.Introspection
end
