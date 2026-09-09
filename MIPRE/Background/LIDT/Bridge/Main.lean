/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Bridge.Value
import MIPRE.Background.LIDT.Bridge.Consistency
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.MainTheorem.MainFormal

/-!
# Bridge, part 8: the soundness theorem in our vocabulary

The main theorem `MIPStarRE.LDT.Test.mainFormal`, applied to the induced strategy
`toProjStrat S`, produces two MIPStarRE projective measurements with outcomes in the
polynomials of individual degree at most `d`; `ofProjMeas` reads them as our projective
measurements with outcomes in `LowIndDegPoly`, and the three consistency conclusions are
transferred with `inconsistency_eq_bipartiteConsError`.
-/

open MIPStarRE.LDT (ProjMeas SubMeas IdxSubMeas ev opTensor)
open scoped MatrixOrder

noncomputable section

namespace MIPRE.LIDT.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- A MIPStarRE projective measurement with polynomial outcomes, as one of our projective
measurements (over the one-element question alphabet) with outcomes in `LowIndDegPoly`. -/
def ofProjMeas {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjMeas (MIPStarRE.LDT.Polynomial (lidtParams F m d)) n) :
    ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d)) (Matrix n n ℂ) where
  M _ c := G.outcome (lowIndDegEquiv c)
  selfAdjoint _ c := by
    have := G.outcome_hermitian (lowIndDegEquiv c)
    simpa [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using this
  projective _ c := G.proj _
  normalized _ := by
    rw [lowIndDegEquiv.sum_comp (fun g => G.outcome g), G.sum_eq_total, G.total_eq_one]

@[simp] theorem ofProjMeas_M {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjMeas (MIPStarRE.LDT.Polynomial (lidtParams F m d)) n) (c : LowIndDegPoly) :
    (ofProjMeas G).M () c = G.outcome (lowIndDegEquiv c) := rfl

omit [DecidableEq F] in
/-- The error bounds of the two developments agree. -/
theorem mainFormalError_eq (k : ℕ) (ε : ℝ) :
    MIPStarRE.LDT.Test.mainFormalError (lidtParams F m d) k ε =
      lidtError m d (Fintype.card F) k ε := by
  unfold MIPStarRE.LDT.Test.mainFormalError lidtError
  rw [neg_div]
  try rfl

/-- The point POVMs of player A, as outcomes of the induced strategy's point measurements. -/
theorem pointPOVMA_val (S : TensorProductStrategy (lidtGame F m d)) (u : Point F m) (a : F) :
    ((pointPOVMA S u).mats a).val =
      ((toProjStrat S).pointMeasurementA (encP u)).toSubMeas.outcome (enc a) := by
  classical
  rw [pointMeasA_eq, MIPStarRE.LDT.SubMeas.postprocess_outcome]
  simp only [pointPOVMA, POVM.map, ProjectiveMeasurement.toPOVM, AddSubmonoidClass.coe_finsetSum,
    decP_encP, toProjMeas_outcome]
  refine Finset.sum_congr (Finset.filter_congr fun ans _ => ?_) fun _ _ => rfl
  exact enc_injective.eq_iff.symm

/-- The point POVMs of player B, as outcomes of the induced strategy's point measurements. -/
theorem pointPOVMB_val (S : TensorProductStrategy (lidtGame F m d)) (u : Point F m) (a : F) :
    ((pointPOVMB S u).mats a).val =
      ((toProjStrat S).pointMeasurementB (encP u)).toSubMeas.outcome (enc a) := by
  classical
  rw [pointMeasB_eq, MIPStarRE.LDT.SubMeas.postprocess_outcome]
  simp only [pointPOVMB, POVM.map, ProjectiveMeasurement.toPOVM, AddSubmonoidClass.coe_finsetSum,
    decP_encP, toProjMeas_outcome]
  refine Finset.sum_congr (Finset.filter_congr fun ans _ => ?_) fun _ _ => rfl
  exact enc_injective.eq_iff.symm

/-- Evaluation of a converted global measurement, as MIPStarRE's evaluation family. -/
theorem evalPOVM_val {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjMeas (MIPStarRE.LDT.Polynomial (lidtParams F m d)) n) (u : Point F m) (a : F) :
    ((evalPOVM (ofProjMeas G) u).mats a).val =
      (MIPStarRE.LDT.polynomialEvaluationFamily (lidtParams F m d) G.toSubMeas (encP u)).outcome
        (enc a) := by
  classical
  show _ = (MIPStarRE.LDT.postprocess G.toSubMeas fun g => g (encP u)).outcome (enc a)
  rw [MIPStarRE.LDT.SubMeas.postprocess_outcome]
  simp only [evalPOVM, POVM.map, ProjectiveMeasurement.toPOVM, AddSubmonoidClass.coe_finsetSum,
    ofProjMeas_M]
  refine Finset.sum_equiv lowIndDegEquiv (fun c => ?_) fun c _ => rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lowIndDegEquiv_apply_encP]
  exact enc_injective.eq_iff.symm

/-- The soundness theorem, assembled from the MIPStarRE main theorem. -/
theorem soundness (S : TensorProductStrategy (lidtGame F m d)) (ε : ℝ) (hS : 1 - ε ≤ S.value)
    (k : ℕ) (hk : 400 * m * d ≤ k) (hk0 : 0 < k) :
    ∃ GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dA) (Fin S.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dB) (Fin S.dB) ℂ),
      inconsistency (uniform (Point F m)) S.ψ (pointPOVMA S) (evalPOVM GB) ≤
          lidtError m d (Fintype.card F) k ε ∧
        inconsistency (uniform (Point F m)) S.ψ (evalPOVM GA) (pointPOVMB S) ≤
          lidtError m d (Fintype.card F) k ε ∧
        inconsistency (uniform Unit) S.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) ≤
          lidtError m d (Fintype.card F) k ε := by
  have hpass : (toProjStrat S).lowIndividualDegreeFailureProbability ≤ ε :=
    (failure_le S).trans (by linarith)
  obtain ⟨GA, GB, h1, h2, h3⟩ := MIPStarRE.LDT.Test.mainFormal (lidtParams F m d)
    (toProjStrat S) ε hpass k hk hk0
  rw [mainFormalError_eq] at h1 h2 h3
  refine ⟨ofProjMeas GA, ofProjMeas GB, ?_, ?_, ?_⟩
  · rw [inconsistency_eq_bipartiteConsError S pointEquiv scalarEquiv (pointPOVMA S)
      (evalPOVM (ofProjMeas GB))
      (MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas (toProjStrat S).pointMeasurementA)
      (MIPStarRE.LDT.polynomialEvaluationFamily (lidtParams F m d) GB.toSubMeas)
      (fun _ => rfl) (fun _ => GB.total_eq_one) (pointPOVMA_val S) (evalPOVM_val GB)]
    exact h1.offDiagonalBound
  · rw [inconsistency_eq_bipartiteConsError S pointEquiv scalarEquiv (evalPOVM (ofProjMeas GA))
      (pointPOVMB S)
      (MIPStarRE.LDT.polynomialEvaluationFamily (lidtParams F m d) GA.toSubMeas)
      (MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas (toProjStrat S).pointMeasurementB)
      (fun _ => GA.total_eq_one) (fun _ => rfl) (evalPOVM_val GA) (pointPOVMB_val S)]
    exact h2.offDiagonalBound
  · rw [inconsistency_eq_bipartiteConsError S (Equiv.refl Unit) lowIndDegEquiv
      (fun _ => (ofProjMeas GA).toPOVM ()) (fun _ => (ofProjMeas GB).toPOVM ())
      (MIPStarRE.LDT.constSubMeasFamily GA.toSubMeas)
      (MIPStarRE.LDT.constSubMeasFamily GB.toSubMeas)
      (fun _ => GA.total_eq_one) (fun _ => GB.total_eq_one) (fun _ _ => rfl) (fun _ _ => rfl)]
    exact h3.offDiagonalBound

end MIPRE.LIDT.Bridge

end
