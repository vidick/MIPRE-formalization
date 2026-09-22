/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.CLExplicitSeed
import MIPRE.Foundations.Introspection.PauliFactorProg
import MIPRE.Foundations.Repeat.Bits

/-! # Exact factor masks for the binary Pauli sampler

The factor program is independent of the field basis and the question type.
Its masks are the actual downsized, numbered factors on every binary prefix.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Cost Introspection.PauliStageProgram

def factorFlag {m : ℕ} (r : ℕ) : Coord m → Bool
  | .point _ _ | .scalar _ => decide (r = 3)
  | .seed => decide (r = 1)
  | .direction _ => decide (r = 2)

private theorem bits_getD_append (a b : BitStr) (i : ℕ) :
    (a ++ b).getD i false = if i < a.length then a.getD i false else b.getD (i - a.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs <;> rfl

private theorem bits_getD_replicate (n : ℕ) (b : Bool) (i : ℕ) :
    (List.replicate n b).getD i false = if i < n then b else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem factorFlags_getD (m r : ℕ) (c : Coord m) :
    (factorFlags m r).getD (coordNumbering m c).val false = factorFlag r c := by
  cases c with
  | point W i =>
    cases W <;>
      simp only [factorFlags, factorFlag, coordNumbering_point_X, coordNumbering_point_Z,
        bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
    all_goals split_ifs <;> simp_all <;> omega
  | seed =>
    simp only [factorFlags, factorFlag, coordNumbering_seed,
      bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    split_ifs <;> simp_all <;> omega
  | direction i =>
    simp only [factorFlags, factorFlag, coordNumbering_direction,
      bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    split_ifs <;> simp_all <;> omega
  | scalar W =>
    cases W <;>
      simp only [factorFlags, factorFlag, coordNumbering_scalar_X, coordNumbering_scalar_Z,
        bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
    all_goals split_ifs <;> simp_all <;> try omega
    all_goals simp [show m + m + 1 + m = 3 * m + 1 by omega]

theorem factorFlags_ofFn (m r : ℕ) :
    factorFlags m r = List.ofFn (fun i => factorFlag r ((coordNumbering m).symm i)) := by
  apply List.ext_getElem
  · simp [factorFlags_length]
  · intro i hi hj
    have hin : i < 3 * m + 3 := by simpa only [factorFlags_length] using hi
    have he := factorFlags_getD m r ((coordNumbering m).symm ⟨i, hin⟩)
    simpa only [Equiv.apply_symm_apply, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn] using he

theorem indicatorBits_binaryRegister {m k : ℕ} (S : Finset (Coord m)) :
    CL.indicatorBits ((S ×ˢ (Finset.univ : Finset (Fin k))).map
      (binaryCoordEquiv m k).toEmbedding) =
      (List.ofFn (fun i : Fin (3 * m + 3) =>
        List.replicate k (decide ((coordNumbering m).symm i ∈ S)))).flatten := by
  unfold CL.indicatorBits
  rw [CL.ofFn_eq_flatten_blocks]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [← List.ofFn_const]
  apply congrArg List.ofFn
  funext j
  have he : binaryCoordEquiv m k ((coordNumbering m).symm i, j) = finProdFinEquiv (i, j) := by
    simp [binaryCoordEquiv]
  rw [← he]
  simp

section FieldFactors
variable {F : Type*} [Field F] {m : ℕ}

theorem presentation_factor_one (χ : F → Fin m) (T : Ty) (u : Coord m → F) :
    (ExplicitSeed.presentation χ T).factorOfPrefix 0 u = seedSet m := rfl

theorem presentation_factor_two (χ : F → Fin m) (T : Ty) (u : Coord m → F) :
    (ExplicitSeed.presentation χ T).factorOfPrefix 1 u = directionSet m := rfl

theorem presentation_factor_three (χ : F → Fin m) (T : Ty) (u : Coord m → F) :
    (ExplicitSeed.presentation χ T).factorOfPrefix 2 u = finalSet m := rfl

theorem factorFlag_mem (χ : F → Fin m) (T : Ty) (u : Coord m → F)
    (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (c : Coord m) :
    factorFlag r c = decide (c ∈ (ExplicitSeed.presentation χ T).factorOfPrefix (r - 1) u) := by
  interval_cases r <;> cases c <;>
    simp [factorFlag, presentation_factor_one, presentation_factor_two,
      presentation_factor_three, seedSet, directionSet, finalSet]
end FieldFactors

theorem binaryPresentation_factor {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (χ : F → Fin m) (b : Module.Basis (Fin k) (ZMod 2) F) (T : Ty)
    (r : ℕ) (u : Coord m → F) :
    (ExplicitSeed.binaryPresentation χ b T).factorOfPrefix r (binaryVectorEquiv b u) =
      (((ExplicitSeed.presentation χ T).factorOfPrefix r u) ×ˢ (Finset.univ : Finset (Fin k))).map
        (binaryCoordEquiv m k).toEmbedding := by
  change (((ExplicitSeed.presentation χ T).downsize b).reindex (binaryCoordEquiv m k)).factorOfPrefix r
    (CL.reindexEquiv (binaryCoordEquiv m k) (CL.downsizeEquiv b u)) = _
  rw [CL.CLFun.factorOfPrefix_reindex, CL.CLFun.factorOfPrefix_downsize]

/-- Exact correctness for every type, every legal stage, every binary prefix,
and any chosen field basis. No prefix validity assumption is needed. -/
theorem factorBits_correct {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (χ : F → Fin m) (b : Module.Basis (Fin k) (ZMod 2) F) (T : Ty)
    (j r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u : Fin ((3 * m + 3) * k) → ZMod 2) :
    factorBits ((unary k, unary j, unary m), r) =
      CL.indicatorBits ((ExplicitSeed.binaryPresentation χ b T).factorOfPrefix (r - 1) u) := by
  obtain ⟨v, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective u
  rw [factorBits_apply, length_unary, length_unary, factorFlags_ofFn,
    binaryPresentation_factor, indicatorBits_binaryRegister, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [factorFlag_mem χ T v r hr1 hr3]

end MIPRE.QLD.PauliCL
end
