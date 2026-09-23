/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliStageProg
import MIPRE.Foundations.SAT.TraceGram

/-! # Extracting arithmetic inputs from Pauli questions

Basis index zero selects X and one selects Z. Axis directions are constructed
from the explicit binary seed selector; diagonal directions are already
present in the question's direction field.
-/

noncomputable section
namespace MIPRE.Introspection.FieldQuestionProgram
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial
  PauliStageProgram SeedProgram

def selectedPoint : PolyTimeFun (ℕ × Fields) (List BitStr) :=
  ite (ArrayProg.eqNat.comp (fst.pair (const 1)))
    (pointZ.comp snd) (pointX.comp snd)

def selectedScalar : PolyTimeFun (ℕ × Fields) BitStr :=
  ite (ArrayProg.eqNat.comp (fst.pair (const 1)))
    (scalarZ.comp snd) (scalarX.comp snd)

@[simp] theorem selectedPoint_zero (fields : Fields) : selectedPoint (0, fields) = fields.1 := rfl
@[simp] theorem selectedPoint_one (fields : Fields) : selectedPoint (1, fields) = fields.2.1 := rfl
@[simp] theorem selectedScalar_zero (fields : Fields) :
    selectedScalar (0, fields) = fields.2.2.2.2.1 := rfl
@[simp] theorem selectedScalar_one (fields : Fields) :
    selectedScalar (1, fields) = fields.2.2.2.2.2 := rfl

private def unitEntryProg : PolyTimeFun (ℕ × Unary × ℕ) BitStr :=
  let zero := shoupZeroProg.comp (fst.comp snd)
  ite (ArrayProg.eqNat.comp (fst.pair (snd.comp snd))) (oneBitsProg.comp zero) zero

theorem unitEntryProg_correct (k : ℕ) (hk : 1 ≤ k) (i j : ℕ) :
    unitEntryProg (i, unary k, j) =
      (shoupBinField k hk).toBits (if i = j then 1 else 0) := by
  simp only [unitEntryProg, PolyTimeFun.ite_apply, comp_apply, pair_apply, fst_apply,
    snd_apply, ArrayProg.eqNat_apply, decide_eq_true_eq, oneBitsProg_apply,
    shoupZeroProg_correct k hk, shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits 0)]
  split <;> rfl

/-- Width, dimension, and selected axis index. -/
def unitDirectionProg : PolyTimeFun (Unary × Unary × ℕ) (List BitStr) :=
  (mapWith unitEntryProg).comp
    ((range'P.comp ((const 0).pair (fst.comp snd))).pair (fst.pair (snd.comp snd)))

theorem unitDirectionProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ} (i : Fin m) :
    unitDirectionProg (unary k, unary m, i.val) =
      (shoupBinField k hk).vecBits (Pi.single i 1) := by
  have hr : List.range' 0 m = List.ofFn (fun j : Fin m => j.val) := by
    apply List.ext_getElem <;> simp
  simp only [unitDirectionProg, comp_apply, pair_apply, fst_apply, snd_apply,
    range'P_apply, const_apply, length_unary, hr, mapWith_apply, List.map_ofFn,
    Function.comp_def, unitEntryProg_correct k hk, BinField.vecBits]
  apply congrArg List.ofFn
  funext j
  congr 1
  simp [Pi.single_apply, Fin.ext_iff, eq_comm]

/-- Field width, selector width, dimension, followed by the canonical seed. -/
def axisDirectionProg : PolyTimeFun ((Unary × Unary × Unary) × BitStr) (List BitStr) :=
  let width := fst.comp fst
  let selectorWidth := fst.comp (snd.comp fst)
  let dimension := snd.comp (snd.comp fst)
  let axis := selectorProg.comp (width.pair (selectorWidth.pair snd))
  unitDirectionProg.comp (width.pair (dimension.pair axis))

theorem axisDirectionProg_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (seed : (shoupBinField k hk).carrier) :
    axisDirectionProg ((unary k, unary j, unary (2 ^ j)), (shoupBinField k hk).toBits seed) =
      (shoupBinField k hk).vecBits (Pi.single (selector (shoupBinField k hk) j hj seed) 1) := by
  simp only [axisDirectionProg, comp_apply, pair_apply, fst_apply, snd_apply,
    selectorProg_correct (shoupBinField k hk) j hj, unitDirectionProg_correct k hk]

theorem axisDirectionProg_runs (input : (Unary × Unary × Unary) × BitStr) :
    ∃ t ≤ axisDirectionProg.timeBound.eval (esize input),
      axisDirectionProg.code.Runs (encode input) (encode (axisDirectionProg input)) t :=
  axisDirectionProg.computes input

end MIPRE.Introspection.FieldQuestionProgram
end
