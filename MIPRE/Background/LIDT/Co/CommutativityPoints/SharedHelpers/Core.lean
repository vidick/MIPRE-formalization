/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
CommutativityPoints/SharedHelpers/Core.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Approximation

@[expose] public section

/-!
# Section 10 commutativity points: shared helpers core

Shared reindexing and tensor-placement helpers used by the Section 10
commutativity-of-points argument: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/SharedHelpers/Core.lean` in the port of
`planning/c6b-plan.md` (milestone M1, section "Port conventions").

The distance lemmas use only the state vector, so they take a vector state `V : VecState K`
(the vendored `ψ`) as an explicit argument and are stated on joint operators `K →L[ℂ] K`. The
placement lemmas take the symmetric model `S : SymModel 𝔓 K` as an explicit first argument (the
vendored ones are fixed by their carrier `ι × ι`); each is a placement identity of the model,
`S.L` and `S.R` being `⋆`-homomorphisms and `S.opTensor A B` being `S.L A * S.R B`, so the
vendored unfolding steps are definitional. `subMeas_sum_adjoint_mul_le_one` is about a local
submeasurement, in the C*-algebra `𝔓`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`

In this repository: `lem:co-commutativity-points` in `blueprint/src/content/08_downstream.tex`.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.CommutativityPoints

open MIPStarRE.LDT (Distribution avgOver avgOver_congr)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Shared reindexing and tensor-placement helpers -/

/-- `SDDOpRel` of a vector state is symmetric in its two operator families. -/
theorem sddOpRel_symm
    {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    V.SDDOpRel 𝒟 A B δ →
      V.SDDOpRel 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [VecState.sddErrorOp, MIPRE.LIDT.Co.Preliminaries.qSDDOp_symm] using h

/-- Reindexing the outcome type of both operator families preserves `qSDDOp`. -/
theorem qSDDOp_reindex
    {Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (V : VecState K)
    (A B : OpFamily Outcome (K →L[ℂ] K)) :
    V.qSDDOp A B =
      V.qSDDOp
        ({ outcome := fun a' => A.outcome (e.symm a')
           total := A.total } : OpFamily Outcome' (K →L[ℂ] K))
        ({ outcome := fun a' => B.outcome (e.symm a')
           total := B.total } : OpFamily Outcome' (K →L[ℂ] K)) := by
  unfold VecState.qSDDOp VecState.qSDDCore
  exact Fintype.sum_equiv e
    (fun a => V.ev (star (A.outcome a - B.outcome a) * (A.outcome a - B.outcome a)))
    (fun a' =>
      V.ev
        (star (A.outcome (e.symm a') - B.outcome (e.symm a')) *
          (A.outcome (e.symm a') - B.outcome (e.symm a'))))
    (by
      intro a
      simp)

/-- Reindexing the outcome type of both indexed families preserves `SDDOpRel`. -/
theorem sddOpRel_reindex
    {Question Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    V.SDDOpRel 𝒟 A B δ →
      V.SDDOpRel 𝒟
        (fun q =>
          ({ outcome := fun a' => (A q).outcome (e.symm a')
             total := (A q).total } : OpFamily Outcome' (K →L[ℂ] K)))
        (fun q =>
          ({ outcome := fun a' => (B q).outcome (e.symm a')
             total := (B q).total } : OpFamily Outcome' (K →L[ℂ] K)))
        δ := by
  intro ⟨h⟩
  constructor
  unfold VecState.sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          V.qSDDOp
            ({ outcome := fun a' => (A q).outcome (e.symm a')
               total := (A q).total } : OpFamily Outcome' (K →L[ℂ] K))
            ({ outcome := fun a' => (B q).outcome (e.symm a')
               total := (B q).total } : OpFamily Outcome' (K →L[ℂ] K)))
      = avgOver 𝒟 (fun q => V.qSDDOp (A q) (B q)) := by
          apply avgOver_congr
          intro q
          rw [qSDDOp_reindex e V (A q) (B q)]
    _ ≤ δ := h

/-- Pointwise equality of outcomes preserves `SDDOpRel`. -/
theorem sddOpRel_congr_outcome
    {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B A' B' : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ : ℝ)
    (hA : ∀ q a, (A q).outcome a = (A' q).outcome a)
    (hB : ∀ q a, (B q).outcome a = (B' q).outcome a) :
    V.SDDOpRel 𝒟 A B δ →
      V.SDDOpRel 𝒟 A' B' δ := by
  intro ⟨h⟩
  constructor
  unfold VecState.sddErrorOp at *
  calc
    avgOver 𝒟 (fun q => V.qSDDOp (A' q) (B' q))
      = avgOver 𝒟 (fun q => V.qSDDOp (A q) (B q)) := by
          apply avgOver_congr
          intro q
          unfold VecState.qSDDOp VecState.qSDDCore
          apply Finset.sum_congr rfl
          intro a _
          rw [hA q a, hB q a]
    _ ≤ δ := h

/-- For a submeasurement `A` in the C*-algebra `𝔓`, `∑ a, star (A a) * A a ≤ 1`. -/
theorem subMeas_sum_adjoint_mul_le_one
    {Outcome : Type*}
    [Fintype Outcome]
    (A : SubMeas Outcome 𝔓) :
    ∑ a : Outcome, star (A.outcome a) * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, star (A.outcome a) * A.outcome a
      = ∑ a : Outcome, A.outcome a * A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [SubMeas.outcome_hermitian]
    _ ≤ ∑ a : Outcome, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact MIPRE.LIDT.Co.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

/-- Multiplying a left lift with a left-placed family stays on the left tensor factor. -/
theorem liftLeft_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓)
    (a : α) (b : β) :
    (A.liftLeft S).outcome a * (OpFamily.leftPlacedOpFamily S B.toOpFamily).outcome b =
      S.L (A.outcome a * B.outcome b) :=
  S.leftTensor_mul_leftTensor (A.outcome a) (B.outcome b)

/-- Multiplying a left lift with a right-placed family gives the tensor product. -/
theorem liftLeft_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓)
    (a : α) (b : β) :
    (A.liftLeft S).outcome a * (OpFamily.rightPlacedOpFamily S B.toOpFamily).outcome b =
      S.opTensor (A.outcome a) (B.outcome b) :=
  S.leftTensor_mul_rightTensor_eq_opTensor (A.outcome a) (B.outcome b)

/-- Multiplying a right lift with a left-placed family gives the tensor product. -/
theorem liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓)
    (a : α) (b : β) :
    (A.liftRight S).outcome a * (OpFamily.leftPlacedOpFamily S B.toOpFamily).outcome b =
      S.opTensor (B.outcome b) (A.outcome a) :=
  S.rightTensor_mul_leftTensor_eq_opTensor (B.outcome b) (A.outcome a)

/-- Multiplying a right lift with a right-placed family stays on the right tensor factor. -/
theorem liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓)
    (a : α) (b : β) :
    (A.liftRight S).outcome a * (OpFamily.rightPlacedOpFamily S B.toOpFamily).outcome b =
      S.R (A.outcome a * B.outcome b) :=
  S.rightTensor_mul_rightTensor (A.outcome a) (B.outcome b)

end MIPRE.LIDT.Co.CommutativityPoints

end
