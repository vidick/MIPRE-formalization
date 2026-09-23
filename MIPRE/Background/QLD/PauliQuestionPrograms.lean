/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliStagePrograms
import MIPRE.Background.QLD.PauliBranchPrograms
import MIPRE.Background.QLD.PauliArithmeticPrograms
import MIPRE.Foundations.Introspection.FieldQuestionProg

/-! # Faithful extraction of the Pauli question's arithmetic fields

The basis metadata from finite routing selects the corresponding point and
scalar. The explicit axis direction agrees with the original game after the
same seed permutation used by the sampled-game transport.
-/

noncomputable section
namespace MIPRE.QLD.PauliQuestionProgram
open Cost SAT Introspection.FieldQuestionProgram Introspection.SeedProgram
  PauliCL PauliBranchProgram

theorem selectedPoint_fieldEncoding {k m : ℕ} (E : BinField k) (W : Bas)
    (x : Coord m → E.carrier) :
    selectedPoint (basisIndex W, fieldEncoding E x) =
      E.vecBits (fun i => x (.point W i)) := by
  cases W <;> rfl

theorem selectedScalar_fieldEncoding {k m : ℕ} (E : BinField k) (W : Bas)
    (x : Coord m → E.carrier) :
    selectedScalar (basisIndex W, fieldEncoding E x) = E.toBits (x (.scalar W)) := by
  cases W <;> rfl

/-- The line program uses precisely the legacy game's selected axis under its
proved seed change, rather than assuming a finite enumeration is computable. -/
theorem axisDirectionProg_legacy (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (s : (shoupBinField k hk).carrier) :
    axisDirectionProg ((unary k, unary j, unary (2 ^ j)), (shoupBinField k hk).toBits s) =
      (shoupBinField k hk).vecBits
        (Pi.single (LIDT.CL.chi hm (ExplicitSeed.seedPermutation (shoupBinField k hk) s)) 1) := by
  rw [ExplicitSeed.chi_seedPermutation (shoupBinField k hk) j hj hm s]
  exact axisDirectionProg_correct k hk j hj s

theorem gammaProg_fieldEncoding (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Coord m → (shoupBinField k hk).carrier) :
    Introspection.FieldGammaProgram.gammaProg (unary k,
      (Introspection.PauliStageProgram.pointX (fieldEncoding (shoupBinField k hk) x)).zip
        (Introspection.PauliStageProgram.pointZ (fieldEncoding (shoupBinField k hk) x)),
      Introspection.PauliStageProgram.scalarX (fieldEncoding (shoupBinField k hk) x),
      Introspection.PauliStageProgram.scalarZ (fieldEncoding (shoupBinField k hk) x)) =
      LowDegree.BinaryLinear.bit (gam (vectorContent x).omega) := by
  have hz : ((shoupBinField k hk).vecBits (fun i => x (.point .X i))).zip
      ((shoupBinField k hk).vecBits (fun i => x (.point .Z i))) =
      List.ofFn (fun i => ((shoupBinField k hk).toBits (x (.point .X i)),
        (shoupBinField k hk).toBits (x (.point .Z i)))) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  change Introspection.FieldGammaProgram.gammaProg (unary k, _,
    (shoupBinField k hk).toBits (x (.scalar .X)),
    (shoupBinField k hk).toBits (x (.scalar .Z))) = _
  simp only [Introspection.PauliStageProgram.pointX, Introspection.PauliStageProgram.pointZ,
    Cost.PolyTimeFun.fst_apply, Cost.PolyTimeFun.snd_apply, Cost.PolyTimeFun.comp_apply,
    fieldEncoding, hz]
  exact PauliArithmeticProgram.gammaProg_eq_gam k hk (vectorContent x).omega

end MIPRE.QLD.PauliQuestionProgram
end
