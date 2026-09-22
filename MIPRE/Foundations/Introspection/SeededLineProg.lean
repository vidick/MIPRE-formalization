/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SeedSelectorProg
import MIPRE.Foundations.Introspection.LineRepresentativeProg
import MIPRE.Foundations.Cost.BinaryCompare
import MIPRE.Foundations.SAT.ArrayProg

/-! # Uniform programs for the seeded axis and diagonal stages

The field width, selector width, seed and vector data are all inputs of fixed
programs. Indices stay binary. The bounded vector scan masks the selected
direction or axis coordinate, and the diagonal stage invokes the actual Shoup
line-representative program. Malformed inputs still halt in polynomial time.
-/

noncomputable section
namespace MIPRE.Introspection.SeededLineProgram
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram

private def indexedRows : PolyTimeFun (List BitStr) (List (ℕ × BitStr)) :=
  zip.comp ((range'P.comp ((const 0).pair length)).pair (PolyTimeFun.id _))

private theorem indexedRows_apply (l : List BitStr) :
    indexedRows l = (List.range' 0 l.length).zip l := by
  simp [indexedRows]

private def maskBeforeStep : PolyTimeFun ((ℕ × BitStr) × (Unary × ℕ)) BitStr :=
  ite (leNat.comp ((snd.comp snd).pair (fst.comp fst)))
    (snd.comp fst) (shoupZeroProg.comp (fst.comp snd))

/-- Zero all coordinates strictly before the supplied binary index. -/
def maskBeforeProg : PolyTimeFun (Unary × ℕ × List BitStr) (List BitStr) :=
  (mapWith maskBeforeStep).comp
    ((indexedRows.comp (snd.comp snd)).pair (fst.pair (fst.comp snd)))

theorem maskBeforeProg_apply (k : Unary) (i : ℕ) (v : List BitStr) :
    maskBeforeProg (k, i, v) = ((List.range' 0 v.length).zip v).map
      (fun p => if i ≤ p.1 then p.2 else shoupZeroProg k) := by
  simp [maskBeforeProg, maskBeforeStep, indexedRows_apply]

theorem maskBeforeProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (i : ℕ)
    (v : Fin n → (shoupBinField k hk).carrier) :
    maskBeforeProg (unary k, i, (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (fun j => if j.val < i then 0 else v j) := by
  rw [maskBeforeProg_apply, shoupZeroProg_correct k hk]
  apply List.ext_getElem
  · simp [BinField.vecBits]
  · intro j hj hj'
    simp only [BinField.vecBits, List.length_map, List.length_ofFn,
      List.getElem_map, List.getElem_zip, List.getElem_range', zero_add,
      List.getElem_ofFn]
    by_cases h : i ≤ j
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]

private def zeroCoordinateStep : PolyTimeFun ((ℕ × BitStr) × (Unary × ℕ)) BitStr :=
  ite (ArrayProg.eqNat.comp ((snd.comp snd).pair (fst.comp fst)))
    (shoupZeroProg.comp (fst.comp snd)) (snd.comp fst)

/-- Zero only the selected axis coordinate. -/
def zeroCoordinateProg : PolyTimeFun (Unary × ℕ × List BitStr) (List BitStr) :=
  (mapWith zeroCoordinateStep).comp
    ((indexedRows.comp (snd.comp snd)).pair (fst.pair (fst.comp snd)))

theorem zeroCoordinateProg_apply (k : Unary) (i : ℕ) (v : List BitStr) :
    zeroCoordinateProg (k, i, v) = ((List.range' 0 v.length).zip v).map
      (fun p => if i = p.1 then shoupZeroProg k else p.2) := by
  simp [zeroCoordinateProg, zeroCoordinateStep, indexedRows_apply]

theorem zeroCoordinateProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (i : Fin n)
    (v : Fin n → (shoupBinField k hk).carrier) :
    zeroCoordinateProg (unary k, i.val, (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (fun j => if j = i then 0 else v j) := by
  rw [zeroCoordinateProg_apply, shoupZeroProg_correct k hk]
  apply List.ext_getElem
  · simp [BinField.vecBits]
  · intro j hj hj'
    simp only [BinField.vecBits, List.length_map, List.length_ofFn,
      List.getElem_map, List.getElem_zip, List.getElem_range', zero_add,
      List.getElem_ofFn]
    by_cases h : i.val = j
    · simp [h, Fin.ext_iff, eq_comm]
    · simp [h, Fin.ext_iff, eq_comm]

/-- Raw input contains the unary field and selector widths, followed by the
canonical seed and the point vector. -/
def axisRepresentativeProg :
    PolyTimeFun ((Unary × Unary × BitStr) × List BitStr) (List BitStr) :=
  zeroCoordinateProg.comp ((fst.comp fst).pair ((selectorProg.comp fst).pair snd))

theorem axisRepresentativeProg_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    axisRepresentativeProg ((unary k, unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u) =
      (shoupBinField k hk).vecBits
        (fun i => if i = selector (shoupBinField k hk) j hj s then 0 else u i) := by
  change zeroCoordinateProg (unary k, selectorProg (unary k, unary j,
    (shoupBinField k hk).toBits s), (shoupBinField k hk).vecBits u) = _
  rw [selectorProg_correct _ j hj, zeroCoordinateProg_correct]

def selectedDirectionProg :
    PolyTimeFun ((Unary × Unary × BitStr) × List BitStr) (List BitStr) :=
  maskBeforeProg.comp ((fst.comp fst).pair ((selectorProg.comp fst).pair snd))

theorem selectedDirectionProg_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (v : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    selectedDirectionProg ((unary k, unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits
        (fun i => if i < selector (shoupBinField k hk) j hj s then 0 else v i) := by
  change maskBeforeProg (unary k, selectorProg (unary k, unary j,
    (shoupBinField k hk).toBits s), (shoupBinField k hk).vecBits v) = _
  rw [selectorProg_correct _ j hj, maskBeforeProg_correct]
  simp only [Fin.lt_def]

/-- The actual diagonal stage returns the canonical point and selected
direction, preserving the seed in the caller's first-stage register. -/
def diagonalRepresentativeProg :
    PolyTimeFun ((Unary × Unary × BitStr) × List BitStr × List BitStr)
      (List BitStr × List BitStr) :=
  let v := selectedDirectionProg.comp (fst.pair (snd.comp snd))
  (lineRepresentativeProg.comp ((fst.comp fst).pair ((fst.comp snd).pair v))).pair v

theorem diagonalRepresentativeProg_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u v : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    let v' := fun i => if i < selector (shoupBinField k hk) j hj s then 0 else v i
    diagonalRepresentativeProg ((unary k, unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u, (shoupBinField k hk).vecBits v) =
      ((shoupBinField k hk).vecBits (representative u v'), (shoupBinField k hk).vecBits v') := by
  dsimp only
  change (lineRepresentativeProg (unary k, (shoupBinField k hk).vecBits u,
    selectedDirectionProg ((unary k, unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits v)),
    selectedDirectionProg ((unary k, unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits v)) = _
  rw [selectedDirectionProg_correct _ hk j hj, lineRepresentativeProg_correct]

theorem axisRepresentativeProg_runs (x : (Unary × Unary × BitStr) × List BitStr) :
    ∃ r ≤ axisRepresentativeProg.timeBound.eval (esize x),
      axisRepresentativeProg.code.Runs (encode x) (encode (axisRepresentativeProg x)) r :=
  axisRepresentativeProg.computes x

theorem diagonalRepresentativeProg_runs
    (x : (Unary × Unary × BitStr) × List BitStr × List BitStr) :
    ∃ r ≤ diagonalRepresentativeProg.timeBound.eval (esize x),
      diagonalRepresentativeProg.code.Runs (encode x) (encode (diagonalRepresentativeProg x)) r :=
  diagonalRepresentativeProg.computes x

end MIPRE.Introspection.SeededLineProgram
end
