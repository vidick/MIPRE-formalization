/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveInductionInvariant
public import MIPRE.Foundations.Introspection.FinalExtraction

@[expose] public section

/-! # Terminal adaptive invariants are conditional readouts

An exact CL presentation has no remaining coordinates at its final level.
The terminal residual measurements therefore act on the auxiliary register
alone. Valid answers have exactly the claimed question readout; the
malformed outcome remains an explicit sum of conditional auxiliary effects.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): a terminal residual operator
is a block matrix over the empty remaining register with entries in the first player's algebra
`𝒜` of the auxiliary model, so it is its single entry, at the unique (zero) vector. That
identification is a unital `⋆`-algebra isomorphism onto `𝒜` (`terminalResidualEquiv`), which
replaces the basis reindexing inserting the unique empty-register vector; the auxiliary
measurement `terminalAuxPOVM` is a POVM in `𝒜`, pushed forward along it; and the question readout
tensored with an auxiliary effect `X` is `smulKron X (readout P.eval y)`, the `conditionalReadout`
of `FinalExtraction.lean`, whose `extractedStrategy` takes such auxiliary families in `𝒜`.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]

theorem stageRemaining_terminal {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F) : stageRemaining P ℓ y = ∅ := by
  simp only [stageRemaining, CLChecks.prefixRegister_full hP, Finset.compl_univ]

/-- Every vector on the empty remaining register is its zero vector. -/
theorem terminalRemaining_eq_zero {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F) (u : stageRemaining P ℓ y → F) : u = 0 := by
  funext i
  have hi : i.val ∈ (∅ : Finset ι) := by
    simpa only [stageRemaining_terminal hP] using i.property
  simp at hi

/-- The terminal residual algebra is the auxiliary algebra: a block matrix over the empty
remaining register is its entry at the unique empty-register vector. -/
def terminalResidualEquiv {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F) :
    Matrix (stageRemaining P ℓ y → F) (stageRemaining P ℓ y → F) 𝒜 ≃⋆ₐ[ℂ] 𝒜 where
  toFun M := M 0 0
  invFun X := Matrix.of fun _ _ => X
  left_inv M := by
    ext u u'
    rw [terminalRemaining_eq_zero hP y u, terminalRemaining_eq_zero hP y u']
    rfl
  right_inv _ := rfl
  map_mul' M M' := by
    change (M * M') 0 0 = M 0 0 * M' 0 0
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_single 0 (fun u _ hu => absurd (terminalRemaining_eq_zero hP y u) hu)
      fun h => absurd (mem_univ _) h
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem terminalResidualEquiv_apply {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F)
    (M : Matrix (stageRemaining P ℓ y → F) (stageRemaining P ℓ y → F) 𝒜) :
    terminalResidualEquiv hP y M = M 0 0 := rfl

/-- Reassembling a terminal residual operator is exactly a question readout
tensored with its single entry, an operator of the auxiliary algebra. -/
theorem prefixResidualOp_terminal {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F)
    (M : Matrix (stageRemaining P ℓ y → F) (stageRemaining P ℓ y → F) 𝒜) :
    prefixResidualOp P ℓ y M = smulKron (terminalResidualEquiv hP y M) (readout P.eval y) := by
  have he (x x' : ι → F) :
      (∀ i ∈ CLChecks.prefixRegister P ℓ y, x i = x' i) ↔ x = x' := by
    rw [CLChecks.prefixRegister_full hP y]
    exact ⟨fun h => funext fun i => h i (mem_univ i), fun h i _ => h ▸ rfl⟩
  ext x x'
  rw [prefixResidualOp_apply P hP.supportedOn, smulKron_apply, terminalResidualEquiv_apply,
    terminalRemaining_eq_zero hP y (fun i => x i), terminalRemaining_eq_zero hP y (fun i => x' i)]
  simp only [readout, Matrix.diagonal_apply, he, CL.CLFun.truncate_self]
  by_cases hx : x = x' <;> by_cases hy : P.eval x = y <;> simp [hx, hy]

/-- Forget only the question component of a valid answer. Malformed answers
remain malformed. -/
def terminalAnswerMap : Option ((ι → F) × A) → Option A := Option.map Prod.snd

section Measurement

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
variable {P : CL.CLFun F ι ℓ}
  {N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜)}

theorem IntroPrefixInvariant.terminal_residual_some_zero
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ)
    (y x : ι → F) (a : A) (hxy : x ≠ y) :
    (I.residual y).op (some (x, a)) = 0 :=
  I.support y x a (by simpa only [hP.outputPrefix_univ x] using hxy)

/-- Coarsening a terminal branch loses no valid-answer effect: its question
component was already fixed by the structural support invariant. -/
theorem IntroPrefixInvariant.terminal_map_some
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ)
    (y : ι → F) (a : A) :
    ((I.residual y).map terminalAnswerMap).op (some a) = (I.residual y).op (some (y, a)) := by
  rw [POVMIn.map_op]
  apply Finset.sum_eq_single (some (y, a))
  · intro b hb hba
    have he : terminalAnswerMap b = some a := (mem_filter.mp hb).2
    cases b with
    | none => cases he
    | some b =>
      have hsecond : b.2 = a := Option.some.inj he
      have hfirst : b.1 ≠ y := by
        intro h
        exact hba (congrArg some (Prod.ext h hsecond))
      exact I.terminal_residual_some_zero hP y b.1 b.2 hfirst
  · intro h
    exact False.elim (h (by simp [terminalAnswerMap]))

theorem IntroPrefixInvariant.terminal_map_none
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) :
    ((I.residual y).map terminalAnswerMap).op none = (I.residual y).op none := by
  rw [POVMIn.map_op]
  apply Finset.sum_eq_single none
  · intro b hb hbnone
    have he : terminalAnswerMap b = none := (mem_filter.mp hb).2
    cases b with
    | none => exact False.elim (hbnone rfl)
    | some b => cases he
  · intro h
    exact False.elim (h (by simp [terminalAnswerMap]))

/-- The actual auxiliary measurement extracted from the terminal invariant, in the first player's
algebra of the auxiliary model. It is normalized on `Option A`, including the malformed outcome. -/
def terminalAuxPOVM (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) : POVMIn (Option A) 𝒜 :=
  ((I.residual y).map terminalAnswerMap).pushforward
    (terminalResidualEquiv (𝒜 := 𝒜) hP y).toNonUnitalStarAlgHom
    (((terminalResidualEquiv (𝒜 := 𝒜) hP y).toNonUnitalStarAlgHom_apply 1).trans (map_one _))

theorem terminalAuxPOVM_isPVM (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) :
    IsPVMIn (terminalAuxPOVM hP I y).op :=
  POVMIn.isPVMIn_pushforward _ _ (POVMIn.isPVMIn_map (I.projective y) terminalAnswerMap)

theorem terminalAuxPOVM_some (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) (a : A) :
    (terminalAuxPOVM hP I y).op (some a) =
      terminalResidualEquiv hP y ((I.residual y).op (some (y, a))) := by
  rw [terminalAuxPOVM, POVMIn.pushforward_op, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    I.terminal_map_some hP]

theorem terminalAuxPOVM_none (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) :
    (terminalAuxPOVM hP I y).op none = terminalResidualEquiv hP y ((I.residual y).op none) := by
  rw [terminalAuxPOVM, POVMIn.pushforward_op, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    I.terminal_map_none]

/-- Every valid terminal answer is an exact conditional readout of the
question, with the concrete auxiliary PVM constructed above. -/
theorem IntroPrefixInvariant.terminal_some
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ)
    (y : ι → F) (a : A) :
    N.op (some (y, a)) = smulKron ((terminalAuxPOVM hP I y).op (some a)) (readout P.eval y) := by
  rw [I.form]
  have hs : (∑ x, prefixResidualOp P ℓ x ((I.residual x).op (some (y, a)))) =
      prefixResidualOp P ℓ y ((I.residual y).op (some (y, a))) := by
    apply Finset.sum_eq_single y
    · intro x _ hxy
      rw [I.terminal_residual_some_zero hP x y a (Ne.symm hxy), prefixResidualOp,
        smulKron_zero_left, map_zero]
    · intro h
      exact False.elim (h (mem_univ y))
  rw [hs, prefixResidualOp_terminal hP, terminalAuxPOVM_some]

/-- Malformed answers are retained as the sum of their conditional
auxiliary effects. No zero-malformed-mass assumption is used. -/
theorem IntroPrefixInvariant.terminal_none
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ) :
    N.op none = ∑ y, smulKron ((terminalAuxPOVM hP I y).op none) (readout P.eval y) := by
  rw [I.form]
  apply Finset.sum_congr rfl
  intro y _
  rw [prefixResidualOp_terminal hP, terminalAuxPOVM_none]

end Measurement

end MIPRE.Introspection
end

end
