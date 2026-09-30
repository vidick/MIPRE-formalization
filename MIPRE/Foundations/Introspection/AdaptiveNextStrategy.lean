/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveNextInvariant
public import MIPRE.Foundations.Introspection.AdaptivePrefixStrategy

@[expose] public section

/-! # A returned strategy with its constructed next-prefix invariant

The selected measurement is identified with the next-prefix residual PVM,
including its actual coordinate carrier and the one shared new ancilla.
Any answer decoder may then be applied to the pair of next prefix and
retained answer. This composes the exact invariant closure with the existing
dimension-independent game-value estimate.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the next joint PVM and the
decoded next residual PVMs are measurements of block matrices over the register whose entries are
block matrices over the ancilla `T` with entries in any algebra `𝒜`
(`POVMIn _ (Matrix (ι → F) (ι → F) (Matrix T T 𝒜))`), which is the first player's algebra of the
register model `(Ξ.expandA t₀).reg (ι → F)` of the returned strategy. The reassociation
`Equiv.prodAssoc` of the replacement measurement becomes its push-forward along the exchange of
the two layers, `BipartiteModel.layerSwap`, which commutes with coarse-graining
(`POVMIn.map_pushforward`). The returned strategy is a projective strategy of that model, so its
selected measurement is the decoded next joint PVM itself, with no basis equivalence
(`adaptiveReplacementStrategy_next_at`); the one shared ancilla is `DilationAncilla A K`, in its
fixed state `inl (a₀, 0)`, with the `K` returned by the dilation.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

/-- Coarse-graining a POVM commutes with pushing it forward along a unital `⋆`-homomorphism. -/
theorem POVMIn.map_pushforward {R S X Y : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    [PartialOrder R] [StarOrderedRing R] [Ring S] [StarRing S] [Algebra ℂ S] [PartialOrder S]
    [StarOrderedRing S] [Fintype X] [Fintype Y] [DecidableEq Y] (φ : R →⋆ₙₐ[ℂ] S)
    (hφ : φ 1 = 1) (f : X → Y) (M : POVMIn X R) :
    (M.map f).pushforward φ hφ = (M.pushforward φ hφ).map f :=
  POVMIn.ext' fun y => by
    rw [POVMIn.pushforward_op, POVMIn.map_op, POVMIn.map_op, map_sum]
    rfl

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
  [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {T : Type*} [Fintype T] [DecidableEq T]

def nextPrefixJointPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k 𝒜 T A)
    (hD : ∀ y z, IsPVMIn (D y z)) :
    POVMIn ((ι → F) × A) (Matrix (ι → F) (ι → F) (Matrix T T 𝒜)) :=
  (nextPrefixJoint_isPVM P hP k a₀ D hD).toPOVMIn

/-- After exchanging the ancilla and register layers, the actual replacement
measurement is exactly the constructed next-prefix PVM with its answer retained. -/
theorem adaptiveReplacementPOVM_next (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k 𝒜 T A)
    (hD : ∀ y z, IsPVMIn (D y z)) :
    ((adaptiveReplacementPOVM P hP k D hD).pushforward BipartiteModel.layerSwap
        BipartiteModel.layerSwap_one).map (advanceStageAnswer P k) =
      nextPrefixJointPOVM P hP k a₀ D hD := by
  rw [adaptiveReplacementPOVM_reindex]
  refine POVMIn.ext' fun p => ?_
  rw [POVMIn.map_op]
  exact adaptiveReplacementJointOp_next_reassembly P hP k a₀ D p.1 p.2

variable {X Y Ans B : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Ans] [DecidableEq Ans] [Fintype B] [DecidableEq B]

/-- The next residual measurement on the common decoded answer alphabet. -/
def nextPrefixDecodedPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k 𝒜 T A)
    (hD : ∀ y z, IsPVMIn (D y z)) (g : (ι → F) × A → Ans) (v : ι → F) :
    POVMIn Ans (Matrix (stageRemaining P (k + 1) v → F) (stageRemaining P (k + 1) v → F)
      (Matrix T T 𝒜)) :=
  ((nextPrefixResidual_isPVM P hP k a₀ D hD v).toPOVMIn).map (fun a => g (v, a))

theorem nextPrefixDecodedPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k 𝒜 T A)
    (hD : ∀ y z, IsPVMIn (D y z)) (g : (ι → F) × A → Ans) (v : ι → F) :
    IsPVMIn (nextPrefixDecodedPOVM P hP k a₀ D hD g v).op :=
  POVMIn.isPVMIn_map (M := (nextPrefixResidual_isPVM P hP k a₀ D hD v).toPOVMIn)
    (nextPrefixResidual_isPVM P hP k a₀ D hD v) _

/-- Decoding the actual joint measurement gives exactly the sum of the
decoded residual measurements behind the next-prefix projectors. -/
theorem nextPrefixJointPOVM_map_mats (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k 𝒜 T A)
    (hD : ∀ y z, IsPVMIn (D y z)) (g : (ι → F) × A → Ans) (b : Ans) :
    ((nextPrefixJointPOVM P hP k a₀ D hD).map g).op b =
      ∑ v, prefixResidualOp P (k + 1) v ((nextPrefixDecodedPOVM P hP k a₀ D hD g v).op b) := by
  simp only [nextPrefixJointPOVM, nextPrefixDecodedPOVM, POVMIn.map_op,
    IsPVMIn.toPOVMIn_op, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [prefixResidualOp_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : g (v, a) = b
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, prefixResidualOp, smulKron_zero_left, map_zero]

/-- Decoding the retained answer commutes with advancing the concrete
replacement into its next-prefix residual form. -/
theorem adaptiveReplacementPOVM_next_decode (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z))
    (g : (ι → F) × A → Ans) :
    ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))).pushforward BipartiteModel.layerSwap
        BipartiteModel.layerSwap_one =
      (nextPrefixJointPOVM P hP k a₀ D hD).map g := by
  rw [POVMIn.map_pushforward, ← POVMIn.map_map _ (advanceStageAnswer P k) g,
    adaptiveReplacementPOVM_next]

/-- The actual question-indexed strategy family has the constructed next
form at the selected question; the other questions are still supplied by
the existing registered replacement constructor. -/
theorem registeredReplacement_next_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z))
    (MA : X → POVMIn Ans (Matrix (ι → F) (ι → F) 𝒜)) (q : X) (g : (ι → F) × A → Ans) :
    registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))) q =
        (nextPrefixJointPOVM P hP k a₀ D hD).map g := by
  rw [registeredReplacement_at, adaptiveReplacementPOVM_next_decode]

/-- The selected measurement's entries satisfy the next induction invariant
with the constructed decoded residual PVM, on the actual remaining register. -/
theorem registeredReplacement_next_mats (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z))
    (MA : X → POVMIn Ans (Matrix (ι → F) (ι → F) 𝒜)) (q : X) (g : (ι → F) × A → Ans)
    (b : Ans) :
    (registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))) q).op b =
      ∑ v, prefixResidualOp P (k + 1) v ((nextPrefixDecodedPOVM P hP k a₀ D hD g v).op b) := by
  rw [registeredReplacement_next_at P hP k a₀ D hD MA q g, nextPrefixJointPOVM_map_mats]

variable [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ ℬ] [StarProper ℬ]
  (Ξ : BipartiteModel 𝒞 𝒜 ℬ)

/-- The same selected-measurement identity for the actual projective strategy of the register
model extended by the ancilla, for any ancilla state. -/
theorem adaptiveReplacementStrategy_next_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (hΞ : ‖Ξ.ψ‖ = 1) (a₀ : A) (t₀ : T)
    (MA : X → POVMIn Ans (Matrix (ι → F) (ι → F) 𝒜))
    (MB : Y → POVMIn B (Matrix (ι → F) (ι → F) ℬ)) (q : X)
    (g : (ι → F) × A → Ans)
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op)
    (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z)) :
    (adaptiveReplacementStrategy Ξ P hP k G hΞ t₀ MA MB q
      (fun p => g (advanceStageAnswer P k p)) hMA hMB D hD).PA q =
      (nextPrefixJointPOVM P hP k a₀ D hD).map g :=
  registeredReplacement_next_at P hP k a₀ D hD MA q g

/-- One quantitative adaptive step returns the next-prefix residual PVMs
and a legal strategy whose selected measurement has exactly that form.
The only structural input concerns the old selected measurement. -/
theorem exists_adaptive_next_strategy (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (hΞ : ‖Ξ.ψ‖ = 1) (a₀ : A)
    (MA : X → POVMIn Ans (Matrix (ι → F) (ι → F) 𝒜))
    (MB : Y → POVMIn B (Matrix (ι → F) (ι → F) ℬ)) (q : X)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (hM : ∀ y, IsPVMIn (M y).op)
    (g : (ι → F) × A → Ans)
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op)
    (hselected : MA q = (adaptiveOldJointPOVM P hP k M).map
      (fun p => g (advanceStageAnswer P k p)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k Ξ (fun y => (M y).op) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ (K : ℕ) (D : AdaptiveDilationFamily P k 𝒜 (DilationAncilla A K) A)
      (hD : ∀ y z, IsPVMIn (D y z)),
      (∀ v, IsPVMIn (nextPrefixResidual P hP k a₀ D v)) ∧
      (adaptiveReplacementStrategy Ξ P hP k G hΞ (Sum.inl (a₀, 0)) MA MB q
        (fun p => g (advanceStageAnswer P k p)) hMA hMB D hD).PA q =
        (nextPrefixJointPOVM P hP k a₀ D hD).map g ∧
      |(Ξ.reg (ι → F)).povmValue G MA MB -
        (adaptiveReplacementStrategy Ξ P hP k G hΞ (Sum.inl (a₀, 0)) MA MB q
          (fun p => g (advanceStageAnswer P k p)) hMA hMB D hD).value| ≤
        2 * Real.sqrt (2 * Real.sqrt (56 * Real.sqrt ε)) := by
  obtain ⟨K, D, hD, _, hv⟩ := exists_adaptive_replacement_strategy Ξ P hP k G hΞ a₀
    MA MB q M hM (fun p => g (advanceStageAnswer P k p)) hMA hMB hselected
    hε0 hε1 hmarg hZ hX
  exact ⟨K, D, hD, nextPrefixResidual_isPVM P hP k a₀ D hD,
    adaptiveReplacementStrategy_next_at Ξ P hP k G hΞ a₀ _ MA MB q g hMA hMB D hD, hv⟩

end MIPRE.Introspection
end

end
