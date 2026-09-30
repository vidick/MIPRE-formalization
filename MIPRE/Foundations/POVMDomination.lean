/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.CommutingModel
public import MIPRE.Foundations.ModelStrategy
public import MIPRE.Foundations.RegisterReindex
public import MIPRE.Foundations.StrategyDilation

@[expose] public section

/-!
# Value models dominating the POVM strategies of a bipartite model

`ValueModel.Dominates ω M` (`MIPRE/Foundations/ModelStrategy.lean`) bounds the projective
strategies of `M` by the value `ω`. A strategy extracted by a rigidity argument need not be
projective: it can be a compression of a projective strategy on an ancilla. So this file bounds
the POVM strategies (`ValueModel.DominatesPOVM`), for the two values:

* **`val*` dominates the POVM strategies of the tensor-product model** of a unit vector on any
  finite registers (`ValueModel.tensor_dominatesPOVM`): the Naimark dilation of each party's
  measurements (`exists_projective_dilation_povm`) makes the strategy projective on the registers
  extended by the answer sets, at the same value (`povmValue_extVec2`), and the reindexing of the
  registers (`TensorProductStrategy.ofProjective`) makes it a `TensorProductStrategy`;
* **`ω_co` dominates the POVM strategies of every model on a Hilbert space** with a unit state
  (`ValueModel.commuting_dominatesPOVM`): such a strategy is a commuting-operator strategy
  (`BipartiteModel.povmValue_le_commutingOperatorValue`).
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder

section Tensor

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The value of a POVM strategy on a unit vector is at most `val*`.** -/
theorem povmValue_le_quantumValue (G : Game X Y A B) (ψ : dA × dB → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : X → POVM A dA) (MB : Y → POVM B dB) : povmValue G ψ MA MB ≤ quantumValue G := by
  classical
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
  · have h0 : povmValue G ψ MA MB = 0 := by
      simp only [povmValue, condWin, Finset.univ_eq_empty, Finset.sum_empty, mul_zero,
        Finset.sum_const_zero]
    rw [h0]
    exact quantumValue_nonneg G
  rcases isEmpty_or_nonempty B with hB | ⟨⟨b₀⟩⟩
  · have h0 : povmValue G ψ MA MB = 0 := by
      simp only [povmValue, condWin, Finset.univ_eq_empty, Finset.sum_empty, mul_zero,
        Finset.sum_const_zero]
    rw [h0]
    exact quantumValue_nonneg G
  obtain ⟨PA, hPA⟩ := exists_projective_dilation_povm MA a₀
  obtain ⟨PB, hPB⟩ := exists_projective_dilation_povm MB b₀
  have hv : povmValue G (extVec2 ψ a₀ b₀) (fun x => PA.toPOVM x) (fun y => PB.toPOVM y) =
      povmValue G ψ MA MB := by
    rw [povmValue_extVec2]
    simp only [hPA, hPB]
  rw [← hv, ← TensorProductStrategy.value_ofProjective G _ (extVec2_unit hψ a₀ b₀) PA PB]
  exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) _

end Tensor

namespace ValueModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **The value model dominates the POVM strategies of a bipartite model**: each has value at
most the value of its game. -/
def DominatesPOVM (ω : ValueModel) (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G : Game X Y A B)
    (PA : X → POVMIn A 𝒜) (PB : Y → POVMIn B ℬ), M.povmValue G PA PB ≤ ω.val G

/-- Dominating the POVM strategies dominates the projective ones. -/
theorem DominatesPOVM.dominates {ω : ValueModel} {M : BipartiteModel 𝒞 𝒜 ℬ}
    (h : ω.DominatesPOVM M) : ω.Dominates M :=
  fun G S => h G S.PA S.PB

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **`val*` dominates the POVM strategies of the tensor-product model** of a unit vector, on any
finite registers. -/
theorem tensor_dominatesPOVM {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : dA × dB → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    tensor.DominatesPOVM (BipartiteModel.tensor ψ) := fun G PA PB => by
  rw [tensor_val]
  have h := povmValue_le_quantumValue G ψ hψ (fun x => (PA x).toPOVM) (fun y => (PB y).toPOVM)
  rw [povmValue_eq_tensor] at h
  exact h

/-- **`ω_co` dominates the POVM strategies of every bipartite model on a Hilbert space** with a
unit state. -/
theorem commuting_dominatesPOVM (M : BipartiteModel.{0} 𝒞 𝒜 ℬ) (hψ : ‖M.ψ‖ = 1) :
    commuting.DominatesPOVM M := fun G PA PB => by
  rw [commuting_val]
  exact M.povmValue_le_commutingOperatorValue hψ PA PB G

end ValueModel

end MIPRE

end
