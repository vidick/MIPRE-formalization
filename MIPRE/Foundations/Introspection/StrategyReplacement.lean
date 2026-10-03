/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.StrategyReplacementValue
public import MIPRE.Foundations.Introspection.HidingInductionDilation
public import MIPRE.Foundations.StrategyDilation
public import MIPRE.Foundations.RegisterReindex
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

/-! # Replacing one measurement on a common ancillary extension

The new family is a function of the actual question. The selected question
uses the supplied projective dilation; every other measurement is the old
measurement tensored with identity. The state extension is independent of
the question and the opposite player is unchanged.

In a bipartite model (Phase 4 of `planning/mipco-track.md`) the common extension is the first
player's one-sided ancilla `Ψ.expandA t₀`, and an old measurement tensored with the identity is
pushed forward along `a ↦ a ⊗ 1` (`MIPRE.diagHom`).
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y A B C T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

/-- An old measurement tensored with the identity of the fresh ancilla. -/
def POVMIn.ampA (M : POVMIn A 𝒜) : POVMIn A (Matrix T T 𝒜) :=
  M.pushforward diagHom diagHom_one

@[simp]
theorem POVMIn.ampA_op (M : POVMIn A 𝒜) (a : A) :
    (POVMIn.ampA (T := T) M).op a = diagonal fun _ => M.op a := rfl

theorem POVMIn.isPVMIn_ampA {M : POVMIn A 𝒜} (hM : IsPVMIn M.op) :
    IsPVMIn (POVMIn.ampA (T := T) M).op :=
  POVMIn.isPVMIn_pushforward _ _ hM

theorem POVMIn.map_ampA (M : POVMIn C 𝒜) (f : C → A) :
    (POVMIn.ampA (T := T) M).map f = POVMIn.ampA (M.map f) := by
  refine POVMIn.ext' fun a => ?_
  rw [POVMIn.ampA_op, POVMIn.map_op, POVMIn.map_op]
  simp only [POVMIn.ampA_op]
  ext t t'
  by_cases h : t = t'
  · subst h
    simp only [Matrix.sum_apply, diagonal_apply_eq]
  · simp only [Matrix.sum_apply, diagonal_apply_ne _ h, Finset.sum_const_zero]

/-- Actual replacement on one common enlarged register. -/
def replaceExtended (MA : X → POVMIn A 𝒜) (q : X) (R : POVMIn A (Matrix T T 𝒜)) :
    X → POVMIn A (Matrix T T 𝒜) := fun x => if x = q then R else POVMIn.ampA (MA x)

@[simp] theorem replaceExtended_at (MA : X → POVMIn A 𝒜) (q : X)
    (R : POVMIn A (Matrix T T 𝒜)) : replaceExtended MA q R q = R := by simp [replaceExtended]

theorem replaceExtended_other (MA : X → POVMIn A 𝒜) (q x : X) (R : POVMIn A (Matrix T T 𝒜))
    (hx : x ≠ q) : replaceExtended MA q R x = POVMIn.ampA (MA x) := by
  simp [replaceExtended, hx]

theorem replaceExtended_isPVM (MA : X → POVMIn A 𝒜) (q : X) (R : POVMIn A (Matrix T T 𝒜))
    (hMA : ∀ x, IsPVMIn (MA x).op) (hR : IsPVMIn R.op) (x : X) :
    IsPVMIn (replaceExtended MA q R x).op := by
  by_cases hx : x = q
  · simpa only [hx, replaceExtended_at] using hR
  · rw [replaceExtended_other MA q x R hx]
    exact POVMIn.isPVMIn_ampA (hMA x)

/-- Adding an inert Alice ancilla preserves the whole game's value exactly. -/
theorem povmValue_expandA (G : Game X Y A B) (t₀ : T) (MA : X → POVMIn A 𝒜)
    (MB : Y → POVMIn B ℬ) :
    (Ψ.expandA t₀).povmValue G (fun x => POVMIn.ampA (MA x)) MB = Ψ.povmValue G MA MB := by
  unfold BipartiteModel.povmValue BipartiteModel.condWin
  simp only [POVMIn.ampA_op, BipartiteModel.bornProb_expandA, diagonal_apply_eq]

/-- Quantitative value preservation for the actual replacement family.
The fine outcomes may be relabelled by any function, including a constructor
in the common parsed-answer alphabet. -/
theorem replaceExtended_value (G : Game X Y A B) (hΨ : ‖Ψ.ψ‖ = 1) (t₀ : T)
    (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    (q : X) (M : POVMIn C 𝒜) (R : POVMIn C (Matrix T T 𝒜)) (f : C → A)
    (hMA : MA q = M.map f) (hM : IsPVMIn M.op) (hR : IsPVMIn R.op)
    (hMB : ∀ y, IsPVMIn (MB y).op) {δ : ℝ}
    (hd : ∑ c, (Ψ.expandA t₀).stateSqNorm ((diagonal fun _ => M.op c) - R.op c) ≤ δ) :
    |Ψ.povmValue G MA MB -
      (Ψ.expandA t₀).povmValue G (replaceExtended MA q (R.map f)) MB| ≤ 2*Real.sqrt δ := by
  rw [← povmValue_expandA Ψ G t₀ MA MB]
  apply povmValue_stability_at (Ψ.expandA t₀) G (by rw [BipartiteModel.norm_expandA_ψ, hΨ])
    (fun x => POVMIn.ampA (MA x)) (replaceExtended MA q (R.map f)) MB q (POVMIn.ampA M) R f
  · rw [hMA, POVMIn.map_ampA]
  · exact replaceExtended_at MA q (R.map f)
  · intro x hx
    exact (replaceExtended_other MA q x (R.map f) hx).symm
  · exact POVMIn.isPVMIn_ampA hM
  · exact hR
  · exact hMB
  · exact hd

end MIPRE.Introspection
end

end
