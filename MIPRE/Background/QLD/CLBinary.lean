/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.CLPresentation
import MIPRE.Foundations.CL.Downsize

/-! # Binary coordinates for the concrete Pauli CL family

A supplied basis of the actual finite field converts the twenty-six concrete
presentations into three-level binary presentations on `(3m+3)t` numbered
coordinates. The theorems identify both the exact question map and the
existing Pauli game's joint question law. No executable or uniform runtime
claim is part of this coordinate conversion.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]

private def basisIndex : Bas ≃ Fin 2 where
  toFun | .X => 0 | .Z => 1
  invFun i := if i = 0 then .X else .Z
  left_inv W := by cases W <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def unitIndex : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := by fin_cases i; rfl

/-- Field coordinates in the fixed order: `uX`, `uZ`, seed, direction,
`rX`, `rZ`. The numbering contains no arbitrary finite-type enumeration. -/
def coordNumbering (m : ℕ) : Coord m ≃ Fin (3 * m + 3) :=
  let points : Bas × Fin m ≃ Fin (2 * m) :=
    (Equiv.prodCongr basisIndex (Equiv.refl _)).trans finProdFinEquiv
  let tail : Unit ⊕ (Fin m ⊕ Bas) ≃ Fin (1 + (m + 2)) :=
    (Equiv.sumCongr unitIndex
      ((Equiv.sumCongr (Equiv.refl _) basisIndex).trans finSumFinEquiv)).trans finSumFinEquiv
  ((coordEquiv m).trans ((Equiv.sumCongr points tail).trans finSumFinEquiv)).trans
    (finCongr (by omega))

@[simp] theorem coordNumbering_point_X (m : ℕ) (i : Fin m) :
    (coordNumbering m (.point .X i)).val = i.val := by
  simp [coordNumbering, coordEquiv, basisIndex, finProdFinEquiv, finSumFinEquiv]

@[simp] theorem coordNumbering_point_Z (m : ℕ) (i : Fin m) :
    (coordNumbering m (.point .Z i)).val = m + i.val := by
  simp [coordNumbering, coordEquiv, basisIndex, finProdFinEquiv, finSumFinEquiv]
  omega

@[simp] theorem coordNumbering_seed (m : ℕ) :
    (coordNumbering m .seed).val = 2 * m := by
  simp [coordNumbering, coordEquiv, unitIndex, finSumFinEquiv]

@[simp] theorem coordNumbering_direction (m : ℕ) (i : Fin m) :
    (coordNumbering m (.direction i)).val = 2 * m + 1 + i.val := by
  simp [coordNumbering, coordEquiv, finSumFinEquiv]
  omega

@[simp] theorem coordNumbering_scalar_X (m : ℕ) :
    (coordNumbering m (.scalar .X)).val = 3 * m + 1 := by
  simp [coordNumbering, coordEquiv, basisIndex, finSumFinEquiv]
  omega

@[simp] theorem coordNumbering_scalar_Z (m : ℕ) :
    (coordNumbering m (.scalar .Z)).val = 3 * m + 2 := by
  simp [coordNumbering, coordEquiv, basisIndex, finSumFinEquiv]
  omega

/-- Each field coordinate is followed by its `t` bits in basis order. -/
def binaryCoordEquiv (m t : ℕ) : Coord m × Fin t ≃ Fin ((3 * m + 3) * t) :=
  (Equiv.prodCongr (coordNumbering m) (Equiv.refl _)).trans finProdFinEquiv

theorem binaryCoordEquiv_val (m t : ℕ) (c : Coord m) (j : Fin t) :
    (binaryCoordEquiv m t (c, j)).val = (coordNumbering m c).val * t + j.val := by
  simp [binaryCoordEquiv, finProdFinEquiv, mul_comm, add_comm]

def binaryVectorEquiv (b : Module.Basis (Fin t) (ZMod 2) F) :
    (Coord m → F) ≃ₗ[ZMod 2] (Fin ((3 * m + 3) * t) → ZMod 2) :=
  (CL.downsizeEquiv b).trans (CL.reindexEquiv (binaryCoordEquiv m t))

theorem binaryVectorEquiv_apply (b : Module.Basis (Fin t) (ZMod 2) F)
    (x : Coord m → F) (c : Coord m) (j : Fin t) :
    binaryVectorEquiv b x (binaryCoordEquiv m t (c, j)) = b.repr (x c) j := by
  simp only [binaryVectorEquiv, LinearEquiv.trans_apply, CL.reindexEquiv_apply,
    Equiv.symm_apply_apply, CL.downsizeEquiv_apply]

def binaryPresentation (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) :
    CL.CLFun (ZMod 2) (Fin ((3 * m + 3) * t)) 3 :=
  ((presentation hm T).downsize b).reindex (binaryCoordEquiv m t)

theorem binaryPresentation_exactlyOn (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) :
    (binaryPresentation hm b T).ExactlyOn univ := by
  have h := ((presentation_exactlyOn hm T).downsize b).reindex (binaryCoordEquiv m t)
  simpa only [binaryPresentation, Finset.univ_product_univ, Finset.map_univ_equiv] using h

/-- Evaluation agrees with the actual field presentation under the binary
coordinate equivalence. -/
theorem binaryPresentation_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Coord m → F) :
    (binaryPresentation hm b T).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((presentation hm T).eval x) := by
  change (((presentation hm T).downsize b).reindex (binaryCoordEquiv m t)).eval
    (CL.reindexEquiv (binaryCoordEquiv m t) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.eval_reindex, CL.CLFun.eval_downsize]
  rfl

theorem binaryPresentation_pauli_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : Bas)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) :
    (binaryPresentation hm b (.pauli W)).eval x = 0 := by
  obtain ⟨z, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective x
  rw [binaryPresentation_eval, presentation_pauli_eval, map_zero]

/-- Decode the binary content of a question of the given type. -/
def binaryQuestion (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) : Question F m :=
  questionOfVector T ((binaryVectorEquiv b).symm x)

theorem binaryQuestion_presentation (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (c : Content F m) :
    binaryQuestion b T ((binaryPresentation hm b T).eval
      (binaryVectorEquiv b (contentVector c))) = c.question hm T := by
  rw [binaryPresentation_eval]
  unfold binaryQuestion
  rw [LinearEquiv.symm_apply_apply, questionOfVector_presentation]

def binarySampleEquiv (b : Module.Basis (Fin t) (ZMod 2) F) :
    Sample F m ≃ (TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2)) :=
  Equiv.prodCongr (Equiv.refl _) (contentEquiv.trans (binaryVectorEquiv b).toEquiv)

/-- The existing Pauli game is exactly the decoded binary CL sampler law,
including its uniform ordered-edge choice. -/
theorem qldGame_mu_binaryPresentation {d : ℕ} (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y =
      SampledGame.dist
        (fun p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2) =>
          binaryQuestion b p.1.val.1 ((binaryPresentation hm b p.1.val.1).eval p.2))
        (fun p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2) =>
          binaryQuestion b p.1.val.2 ((binaryPresentation hm b p.1.val.2).eval p.2))
        x y := by
  change (∑ p : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
    if (p.2.question hm p.1.val.1, p.2.question hm p.1.val.2) = (x, y)
      then 1 else 0) = _
  unfold SampledGame.dist
  rw [← Finset.mul_sum, Fintype.card_congr (binarySampleEquiv (m := m) b)]
  congr 1
  refine Fintype.sum_equiv (binarySampleEquiv b) _ _ fun p => ?_
  simp only [binarySampleEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    Equiv.trans_apply, contentEquiv, Equiv.coe_fn_mk,
    LinearEquiv.coe_toEquiv, binaryQuestion_presentation]

end MIPRE.QLD.PauliCL
end
