/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliStagePrograms
import MIPRE.Background.QLD.BinaryBlocks
import MIPRE.Foundations.Introspection.PauliRowsProg
import Mathlib.Data.List.GetD

/-! # Exact row and binary encodings for the executable Pauli queries -/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Cost SAT Introspection.PauliStageProgram

theorem packRows_fieldEncoding_getD {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) (c : Coord m) :
    (packRows (fieldEncoding E x)).getD (coordNumbering m c).val [] = E.toBits (x c) := by
  have hlen (v : Fin m → E.carrier) : (E.vecBits v).length = m := by simp [BinField.vecBits]
  have hget (v : Fin m → E.carrier) (i : Fin m) :
      (E.vecBits v).getD i.val [] = E.toBits (v i) := by
    simp [BinField.vecBits, List.getD_eq_getElem?_getD, i.isLt]
  cases c with
  | point W i =>
    cases W with
    | X =>
      simp only [fieldEncoding, packRows_apply, coordNumbering_point_X]
      rw [List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
    | Z =>
      simp only [fieldEncoding, packRows_apply, coordNumbering_point_Z]
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
        Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
  | seed =>
    simp only [fieldEncoding, packRows_apply, coordNumbering_seed]
    rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
      List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    simp [show 2 * m - m - m = 0 by omega]
  | direction i =>
    simp only [fieldEncoding, packRows_apply, coordNumbering_direction]
    rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
      List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    rw [show 2 * m + 1 + i.val - m - m = i.val + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
  | scalar W =>
    cases W <;> simp only [fieldEncoding, packRows_apply,
      coordNumbering_scalar_X, coordNumbering_scalar_Z]
    all_goals
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
        List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    · rw [show 3 * m + 1 - m - m = m + 1 by omega]
      simp only [List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp [hlen]), hlen]
      simp
    · rw [show 3 * m + 2 - m - m = (m + 1) + 1 by omega]
      simp only [List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
      simp

theorem packRows_fieldEncoding {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) : packRows (fieldEncoding E x) = numberedRows E x := by
  have hlen : (packRows (fieldEncoding E x)).length = 3 * m + 3 := by
    simp [packRows, fieldEncoding, pointX, pointZ, seed, direction, scalarX, scalarZ,
      BinField.vecBits]
    omega
  apply List.ext_getElem
  · rw [hlen, numberedRows_length]
  · intro i hi hi'
    have hil : i < 3 * m + 3 := by simpa only [hlen] using hi
    let c := (coordNumbering m).symm ⟨i, hil⟩
    have hc : (coordNumbering m c).val = i := by simp [c]
    have he := (packRows_fieldEncoding_getD E x c).trans (numberedRows_getD E x c).symm
    simpa only [hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi', Option.getD_some] using he

theorem unpackRows_numberedRows {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) : unpackRows (unary m, numberedRows E x) = fieldEncoding E x := by
  rw [← packRows_fieldEncoding]
  exact unpackRows_packRows m _ _ _ _ _ _ (by simp [BinField.vecBits])
    (by simp [BinField.vecBits]) (by simp [BinField.vecBits])

theorem rowInput_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (T : Ty) (r : ℕ)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    rowInput ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      numberedRows (shoupBinField k hk) u, numberedRows (shoupBinField k hk) x) =
      stageInput k hk j T u x := by
  simp only [rowInput, PolyTimeFun.pair_apply, PolyTimeFun.comp_apply,
    PolyTimeFun.ap₂_apply, PolyTimeFun.fst_apply, PolyTimeFun.snd_apply,
    unpackRows_numberedRows, stageInput]

theorem linearRows_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (T : Ty) (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    linearRows ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      numberedRows (shoupBinField k hk) u, numberedRows (shoupBinField k hk) x) =
      numberedRows (shoupBinField k hk)
        ((ExplicitSeed.presentation (Introspection.SeedProgram.selector
          (shoupBinField k hk) j hj) T).mapOfPrefix (r - 1) u x) := by
  change packRows (linear (r, rowInput _)) = _
  rw [rowInput_correct, linear_correct k hk j hj T r hr1 hr3, packRows_fieldEncoding]

theorem binaryInput_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (T : Ty) (r : ℕ)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    binaryInput ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) u),
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      ((unary k, unary j, unary (2 ^ j)), programTag T, r,
        numberedRows (shoupBinField k hk) u, numberedRows (shoupBinField k hk) x) := by
  have hc (m : ℕ) : unary m ++ (unary m ++ (unary m ++ unary 3)) = unary (3 * m + 3) := by
    simp only [unary, ← List.replicate_add]
    congr 1
    omega
  simp only [binaryInput, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply,
    PolyTimeFun.ap₂_apply, PolyTimeFun.append_apply, PolyTimeFun.fst_apply,
    PolyTimeFun.snd_apply, PolyTimeFun.const_apply, hc, decodeBlocksProg_binaryVector k hk hodd]

theorem binaryPresentation_mapOfPrefix {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (χ : F → Fin m) (b : Module.Basis (Fin k) (ZMod 2) F) (T : Ty)
    (r : ℕ) (u x : Coord m → F) :
    (ExplicitSeed.binaryPresentation χ b T).mapOfPrefix r
      (binaryVectorEquiv b u) (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((ExplicitSeed.presentation χ T).mapOfPrefix r u x) := by
  change (((ExplicitSeed.presentation χ T).downsize b).reindex (binaryCoordEquiv m k)).mapOfPrefix r
    (CL.reindexEquiv (binaryCoordEquiv m k) (CL.downsizeEquiv b u))
    (CL.reindexEquiv (binaryCoordEquiv m k) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.mapOfPrefix_reindex, CL.CLFun.mapOfPrefix_downsize]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.restrictScalars_apply]
  rfl

theorem linearBits_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (hj : j ≤ k) (T : Ty) (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    linearBits ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) u),
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      CL.toBits ((ExplicitSeed.binaryPresentation
        (Introspection.SeedProgram.selector (shoupBinField k hk) j hj)
        (shoupSelfDualNormalBasis k hk hodd) T).mapOfPrefix (r - 1)
        (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) u)
        (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) := by
  change Introspection.BinaryBlock.encodeBlocksProg (unary k, linearRows (binaryInput _)) = _
  rw [binaryInput_correct k hk hodd, linearRows_correct k hk j hj T r hr1 hr3,
    encodeBlocksProg_numberedRows k hk hodd, binaryPresentation_mapOfPrefix]

theorem marginalRows_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (T : Ty) (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    marginalRows ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      numberedRows (shoupBinField k hk) u, numberedRows (shoupBinField k hk) x) =
      numberedRows (shoupBinField k hk)
        (((ExplicitSeed.presentation (Introspection.SeedProgram.selector
          (shoupBinField k hk) j hj) T).truncate r).eval x) := by
  change packRows (marginal (r, rowInput _)) = _
  rw [rowInput_correct, marginal_correct k hk j hj T r hr1 hr3, packRows_fieldEncoding]

theorem binaryPresentation_truncate {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (χ : F → Fin m) (b : Module.Basis (Fin k) (ZMod 2) F) (T : Ty)
    (r : ℕ) (x : Coord m → F) :
    ((ExplicitSeed.binaryPresentation χ b T).truncate r).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b (((ExplicitSeed.presentation χ T).truncate r).eval x) := by
  change ((((ExplicitSeed.presentation χ T).downsize b).reindex (binaryCoordEquiv m k)).truncate r).eval
    (CL.reindexEquiv (binaryCoordEquiv m k) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.truncate_reindex, CL.CLFun.eval_reindex, CL.CLFun.eval_truncate_downsize]
  rfl

theorem marginalBits_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (hj : j ≤ k) (T : Ty) (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    marginalBits ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) u),
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      CL.toBits (((ExplicitSeed.binaryPresentation
        (Introspection.SeedProgram.selector (shoupBinField k hk) j hj)
        (shoupSelfDualNormalBasis k hk hodd) T).truncate r).eval
        (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) := by
  change Introspection.BinaryBlock.encodeBlocksProg (unary k, marginalRows (binaryInput _)) = _
  rw [binaryInput_correct k hk hodd, marginalRows_correct k hk j hj T r hr1 hr3,
    encodeBlocksProg_numberedRows k hk hodd, binaryPresentation_truncate]

end MIPRE.QLD.PauliCL
end
