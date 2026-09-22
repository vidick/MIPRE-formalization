/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.SeededLinePrograms
import MIPRE.Foundations.Introspection.PauliStageProg

/-! # Correctness of every executable Pauli stage

These identities cover all twenty-six types and arbitrary prefix vectors.
The executable diagonal stage consumes the prefix direction itself, as
required by `mapOfPrefix`, rather than applying the selector a second time.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram

def programTag : Ty → Tag
  | .point W => (0, W == .Z)
  | .aline W => (1, W == .Z)
  | .dline W => (2, W == .Z)
  | .pauli W => (3, W == .Z)
  | _ => (4, false)

def fieldEncoding {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) : Fields :=
  (E.vecBits (fun i => x (.point .X i)), E.vecBits (fun i => x (.point .Z i)),
    E.toBits (x .seed), E.vecBits (fun i => x (.direction i)),
    E.toBits (x (.scalar .X)), E.toBits (x (.scalar .Z)))

def stageInput (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) : Input :=
  ((unary k, unary j, unary (2 ^ j)), programTag T,
    fieldEncoding (shoupBinField k hk) u, fieldEncoding (shoupBinField k hk) x)

theorem stageOne_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    stageOne (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk) (seedMap T x) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp only [fieldEncoding, seedMap, CL.RegLinear.id_apply, CL.RegLinear.zero_apply]
  all_goals
    simp [stageOne, pack, isKind, kind, zeroPoint, zeroField, dimension, fieldWidth,
      seed, vector, stageInput, programTag, fieldEncoding, shoupZeroProg_correct k hk,
      CL.proj_apply, seedSet, BinField.vecBits, Function.comp_def]

theorem stageTwo_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    stageTwo (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        (ExplicitSeed.secondMap (selector (shoupBinField k hk) j hj) T (u .seed) x) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp only [fieldEncoding, ExplicitSeed.secondMap, directionMap_apply, CL.RegLinear.zero_apply]
  all_goals
    simp [stageTwo, pack, isKind, kind, zeroPoint, zeroField, dimension, fieldWidth,
      seed, vector, prefixData, direction, selectorWidth, stageInput, programTag,
      fieldEncoding, shoupZeroProg_correct k hk, selectedDirectionProg_correct k hk j hj]
  all_goals simp [BinField.vecBits]

theorem stageThree_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    stageThree (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        (ExplicitSeed.finalMap (selector (shoupBinField k hk) j hj) T
          (u .seed) (fun i => u (.direction i)) x) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp only [fieldEncoding, ExplicitSeed.finalMap, pointMap_apply,
      CL.RegLinear.id_apply, CL.RegLinear.zero_apply]
  all_goals
    simp [stageThree, pointFields, fullFields, zeros, pack, isKind, kind, zeroPoint,
      zeroField, dimension, fieldWidth, seed, vector, prefixData, direction, selectorWidth,
      basis, finalPoint, selectedPoint, pointX, pointZ, scalarX, scalarZ,
      stageInput, programTag, fieldEncoding, shoupZeroProg_correct k hk,
      axisRepresentativeProg_canonLin k hk j hj, lineRepresentativeProg_correct k hk,
      representative_eq_canonLin]
  all_goals simp [finalSet, seedSet, directionSet, BinField.vecBits,
    Function.comp_def]

section StageMaps
variable {F : Type*} [Field F] {m : ℕ}

theorem presentation_mapOfPrefix_one (χ : F → Fin m) (T : Ty) (u x : Coord m → F) :
    (ExplicitSeed.presentation χ T).mapOfPrefix 0 u x = seedMap T x := rfl

theorem presentation_mapOfPrefix_two (χ : F → Fin m) (T : Ty) (u x : Coord m → F) :
    (ExplicitSeed.presentation χ T).mapOfPrefix 1 u x =
      ExplicitSeed.secondMap χ T (u .seed) x := by
  change ExplicitSeed.secondMap χ T (CL.proj (seedSet m) u .seed) x = _
  have hs : CL.proj (seedSet m) u .seed = u .seed := by simp [CL.proj_apply, seedSet]
  rw [hs]

theorem presentation_mapOfPrefix_three (χ : F → Fin m) (T : Ty) (u x : Coord m → F) :
    (ExplicitSeed.presentation χ T).mapOfPrefix 2 u x =
      ExplicitSeed.finalMap χ T (u .seed) (fun i => u (.direction i)) x := by
  change ExplicitSeed.finalMap χ T (CL.proj (seedSet m) u .seed)
    (fun i => CL.proj (directionSet m) (CL.proj (seedSet m)ᶜ u) (.direction i)) x = _
  have hs : CL.proj (seedSet m) u .seed = u .seed := by simp [CL.proj_apply, seedSet]
  have hd : (fun i => CL.proj (directionSet m) (CL.proj (seedSet m)ᶜ u) (.direction i)) =
      (fun i => u (.direction i)) := by
    funext i
    simp [CL.proj_apply, seedSet, directionSet]
  rw [hs, hd]
end StageMaps

/-- The linear-query compiler is correct on every prefix, including prefixes
that are not attained by the preceding stages. -/
theorem linear_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    linear (r, stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        ((ExplicitSeed.presentation (selector (shoupBinField k hk) j hj) T).mapOfPrefix
          (r - 1) u x) := by
  interval_cases r
  · rw [linear_one, show 1 - 1 = 0 by rfl, presentation_mapOfPrefix_one]
    exact stageOne_correct k hk j T u x
  · rw [linear_two, show 2 - 1 = 1 by rfl, presentation_mapOfPrefix_two]
    exact stageTwo_correct k hk j hj T u x
  · rw [linear_three, show 3 - 1 = 2 by rfl, presentation_mapOfPrefix_three]
    exact stageThree_correct k hk j hj T u x

theorem zeros_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    zeros (stageInput k hk j T u x) = fieldEncoding (m := 2 ^ j) (shoupBinField k hk) 0 := by
  simp [zeros, pack, zeroPoint, zeroField, dimension, fieldWidth, stageInput,
    fieldEncoding, shoupZeroProg_correct k hk, BinField.vecBits]

theorem withPrefix_fieldEncoding (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (T : Ty)
    (u v x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    withPrefix (stageInput k hk j T u x, fieldEncoding (shoupBinField k hk) v) =
      stageInput k hk j T v x := rfl

section MarginalAssembly
variable {k m : ℕ} (E : BinField k) (χ : E.carrier → Fin m) (T : Ty)
  (x : Coord m → E.carrier)

theorem presentation_truncate_one :
    ((ExplicitSeed.presentation χ T).truncate 1).eval x = seedMap T x := by
  simp [ExplicitSeed.presentation, CL.CLFun.truncate, CL.CLFun.eval]

/-- The first two registers are assembled in their actual ambient positions. -/
theorem assemble_firstTwo :
    assemble (fieldEncoding E (seedMap T x),
      fieldEncoding E (ExplicitSeed.secondMap χ T (seedMap T x .seed) x),
      fieldEncoding (m := m) E 0) =
      fieldEncoding E (((ExplicitSeed.presentation χ T).truncate 2).eval x) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp only [ExplicitSeed.presentation, CL.CLFun.truncate, CL.CLFun.eval,
      fieldEncoding, seedMap, ExplicitSeed.secondMap, CL.RegLinear.zero_apply,
      CL.RegLinear.id_apply, directionMap_apply, Pi.add_apply, Pi.zero_apply]
  all_goals simp [assemble, pack, pointX, pointZ, seed, direction, scalarX, scalarZ,
    CL.proj_apply, seedSet, BinField.vecBits, Function.comp_def]

/-- The last stage uses both fields of the actual first-two-stage prefix. -/
theorem assemble_allThree :
    let p := ((ExplicitSeed.presentation χ T).truncate 2).eval x
    assemble (fieldEncoding E p, fieldEncoding E p,
      fieldEncoding E (ExplicitSeed.finalMap χ T (p .seed) (fun i => p (.direction i)) x)) =
      fieldEncoding E ((ExplicitSeed.presentation χ T).eval x) := by
  dsimp only
  cases T <;> (try cases ‹Bas›) <;>
    simp only [ExplicitSeed.presentation, CL.CLFun.truncate, CL.CLFun.eval,
      fieldEncoding, seedMap, ExplicitSeed.secondMap, ExplicitSeed.finalMap,
      CL.RegLinear.zero_apply, CL.RegLinear.id_apply, directionMap_apply, pointMap_apply,
      Pi.add_apply, Pi.zero_apply]
  all_goals simp [assemble, pack, pointX, pointZ, seed, direction, scalarX, scalarZ,
    CL.proj_apply, seedSet, directionSet, finalSet, BinField.vecBits, Function.comp_def]
end MarginalAssembly

theorem firstTwo_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    firstTwo (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        (((ExplicitSeed.presentation (selector (shoupBinField k hk) j hj) T).truncate 2).eval x) := by
  change assemble (stageOne (stageInput k hk j T u x),
    stageTwo (withPrefix (stageInput k hk j T u x, stageOne (stageInput k hk j T u x))),
    zeros (stageInput k hk j T u x)) = _
  rw [stageOne_correct, withPrefix_fieldEncoding, stageTwo_correct k hk j hj,
    zeros_correct]
  exact assemble_firstTwo _ _ _ _

theorem allThree_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    allThree (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        ((ExplicitSeed.presentation (selector (shoupBinField k hk) j hj) T).eval x) := by
  change assemble (firstTwo (stageInput k hk j T u x), firstTwo (stageInput k hk j T u x),
    stageThree (withPrefix (stageInput k hk j T u x, firstTwo (stageInput k hk j T u x)))) = _
  rw [firstTwo_correct k hk j hj, withPrefix_fieldEncoding, stageThree_correct k hk j hj]
  exact assemble_allThree _ _ _ _

/-- Every legal marginal query is computed by the fixed executable router. -/
theorem marginal_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    marginal (r, stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        (((ExplicitSeed.presentation (selector (shoupBinField k hk) j hj) T).truncate r).eval x) := by
  interval_cases r
  · rw [marginal_one, presentation_truncate_one]
    exact stageOne_correct k hk j T u x
  · rw [marginal_two]
    exact firstTwo_correct k hk j hj T u x
  · rw [marginal_three, CL.CLFun.truncate_self]
    exact allThree_correct k hk j hj T u x

end MIPRE.QLD.PauliCL
end
