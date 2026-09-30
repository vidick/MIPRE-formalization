/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.StrategyReplacementRegister

@[expose] public section

/-! # Conditional residual POVMs produce an actual replacement strategy

Naimark's construction uses the same fixed ancilla for every prefix. The
resulting residual PVMs are assembled with the unchanged prefix projectors,
inserted at the chosen question, and packaged as a legal strategy. The value
loss is `2 sqrt(2 sqrt(delta))`, independent of every outcome cardinality.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the strategy is a projective
strategy (`BipartiteModel.ProjStrat`) of the register model `(Ξ.expandA t₀).reg I` of the first
player's one-sided extension, in place of a tensor-product strategy. The fixed ancilla state is
the basis vector `t₀ = inl (a₀, 0)` of `DilationAncilla C K`, the number `K` of Kraus terms
depending on the residual POVMs (`exists_conditional_projective_dilation`), and the compression of
a residual PVM to that state is its `(t₀, t₀)` entry.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ ℬ]
  [StarProper ℬ]
  (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y A B C J I : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I] [Nonempty I]

/-- Conditional projectivization followed by actual strategy reassembly.
Neither the projectors nor the strategy are hypotheses: both are constructed
from the residual POVMs `Q`, and every prefix shares the fixed state `inl (a₀, 0)`. -/
theorem exists_conditional_replacement_strategy
    (G : Game X Y A B) (hΞ : ‖Ξ.ψ‖ = 1) (a₀ : C)
    (MA : X → POVMIn A (Matrix I I 𝒜)) (MB : Y → POVMIn B (Matrix I I ℬ)) (q : X)
    (M : POVMIn (J × C) (Matrix I I 𝒜)) (f : J × C → A)
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op)
    (hselected : MA q = M.map f) (hM : IsPVMIn M.op)
    (Z : J → Matrix I I ℂ) (hZ : IsPVM Z) (Q : J → POVMIn C 𝒜) {δ : ℝ}
    (hd : ∑ p : J × C, (Ξ.reg I).stateSqNorm
      (M.op p - smulKron ((Q p.1).op p.2) (Z p.1)) ≤ δ) :
    ∃ K : ℕ, ∃ (P : J → C → Matrix (DilationAncilla C K) (DilationAncilla C K) 𝒜)
      (hP : ∀ j, IsPVMIn (P j)),
      (∀ j c, P j c (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) = (Q j).op c) ∧
      |(Ξ.reg I).povmValue G MA MB -
        (registeredReplacementStrategy Ξ G hΞ (Sum.inl (a₀, 0) : DilationAncilla C K) MA MB q
          ((conditionalDilationOp_isPVM Z hZ P hP).toPOVMIn.map f) hMA hMB
          (POVMIn.isPVMIn_map (M := (conditionalDilationOp_isPVM Z hZ P hP).toPOVMIn)
            (conditionalDilationOp_isPVM Z hZ P hP) f)).value| ≤
        2*Real.sqrt (2*Real.sqrt δ) := by
  obtain ⟨K, P, hP, hk, hjoint, _, hdist⟩ :=
    exists_conditional_projective_dilation (J := Unit) (Ξ.reg I)
      (by rw [BipartiteModel.norm_reg_ψ, hΞ]) a₀
      (fun _ => 1) (fun _ => zero_le_one) (by simp)
      (fun _ => Z) (fun _ => hZ) (fun _ => Q)
      (fun _ p => M.op p) (fun _ => hM) (δ := δ) (by simpa using hd)
  refine ⟨K, P (), hP (), hk (), ?_⟩
  apply registeredReplacementStrategy_value_loss Ξ G hΞ _ MA MB q M
    (conditionalDilationOp_isPVM Z hZ (P ()) (hP ())).toPOVMIn f hMA hMB
    hselected hM (hjoint ())
  simpa only [Fintype.sum_unique, one_mul, IsPVMIn.toPOVMIn_op] using hdist

end MIPRE.Introspection
end

end
