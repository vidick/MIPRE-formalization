/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.CLExplicitSeed

/-! # Equivalences between explicit and legacy Pauli question contents

Only line questions carry the seed. Permuting that coordinate on their raw
contents gives a genuine equivalence, including contents outside the support
of the sampler. The same permutation of the shared random seed intertwines
all twenty-six sampled question maps simultaneously.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL.ExplicitSeed
open Finset Classical
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- Change the field seed coordinate and leave every other coordinate intact. -/
def vectorPermutation (π : F ≃ F) : (Coord m → F) ≃ (Coord m → F) :=
  contentEquiv.symm.trans ((contentPermutation π).trans contentEquiv)

theorem vectorPermutation_content (π : F ≃ F) (c : Content F m) :
    vectorPermutation π (contentVector c) = contentVector (contentPermutation π c) := by
  change contentEquiv (contentPermutation π (contentEquiv.symm (contentEquiv c))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Raw output-question equivalence; only the two line families retain a seed. -/
def outputPermutation (π : F ≃ F) : Ty → ((Coord m → F) ≃ (Coord m → F))
  | .aline _ | .dline _ => vectorPermutation π
  | _ => Equiv.refl _

theorem questionOfVector_outputPermutation (π : F ≃ F) (T : Ty) (x : Coord m → F) :
    questionOfVector T (outputPermutation π T x) = decode π T x := by
  cases T <;> (try cases ‹Bas›) <;> rfl

variable [NeZero m]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem outputPermutation_presentation (hm : m ∣ Fintype.card F)
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (T : Ty) (c : Content F m) :
    outputPermutation π T ((presentation χ T).eval (contentVector c)) =
      (PauliCL.presentation hm T).eval (contentVector (contentPermutation π c)) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp +instances only [outputPermutation, vectorPermutation, contentEquiv, contentPermutation,
      presentation, PauliCL.presentation, seedMap, secondMap, PauliCL.secondMap,
      finalMap, PauliCL.finalMap, CL.CLFun.eval, CL.RegLinear.zero_apply,
      CL.RegLinear.id_apply, pointMap_apply, directionMap_apply, Pi.add_apply, Pi.zero_apply,
      Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_fn_mk, vectorContent]
  all_goals
    funext i
    cases i <;> (try cases ‹Bas›) <;>
      simp +instances only [CL.RegLinear.instFunLikeForall, contentVector, vectorContent,
        pointMap, directionMap, Pi.add_apply, Pi.zero_apply, LinearMap.id_apply] <;>
      simp +instances [CL.proj_apply, seedSet, directionSet, finalSet, contentVector, vectorContent,
        pointMap, directionMap, hχ]

section Binary
variable [Algebra (ZMod 2) F] {t : ℕ}

/-- Raw binary output-question equivalence, in the supplied basis. -/
def binaryOutputPermutation (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (T : Ty) : (Fin ((3*m+3)*t) → ZMod 2) ≃ (Fin ((3*m+3)*t) → ZMod 2) :=
  (binaryVectorEquiv b).toEquiv.symm.trans
    ((outputPermutation π T).trans (binaryVectorEquiv b).toEquiv)

/-- The corresponding permutation of the common binary random content. -/
def binarySeedPermutation (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    (Fin ((3*m+3)*t) → ZMod 2) ≃ (Fin ((3*m+3)*t) → ZMod 2) :=
  (binaryVectorEquiv b).toEquiv.symm.trans
    ((vectorPermutation π).trans (binaryVectorEquiv b).toEquiv)

theorem binaryQuestion_outputPermutation (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Fin ((3*m+3)*t) → ZMod 2) :
    binaryQuestion b T (binaryOutputPermutation π b T x) = binaryDecode π b T x := by
  change questionOfVector T ((binaryVectorEquiv b).symm
    (binaryVectorEquiv b (outputPermutation π T ((binaryVectorEquiv b).symm x)))) = _
  rw [LinearEquiv.symm_apply_apply, questionOfVector_outputPermutation]
  rfl

theorem binaryOutputPermutation_presentation (hm : m ∣ Fintype.card F)
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    binaryOutputPermutation π b T ((binaryPresentation χ b T).eval x) =
      (PauliCL.binaryPresentation hm b T).eval (binarySeedPermutation π b x) := by
  obtain ⟨v, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective x
  obtain ⟨c, rfl⟩ := (contentEquiv (F := F) (m := m)).surjective v
  rw [binaryPresentation_eval]
  change binaryVectorEquiv b (outputPermutation π T
    ((binaryVectorEquiv b).symm (binaryVectorEquiv b
      ((presentation χ T).eval (contentVector c))))) =
    (PauliCL.binaryPresentation hm b T).eval
      (binaryVectorEquiv b (vectorPermutation π
        ((binaryVectorEquiv b).symm (binaryVectorEquiv b (contentVector c)))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    vectorPermutation_content, PauliCL.binaryPresentation_eval,
    outputPermutation_presentation hm χ π hχ]

@[simp] theorem binaryOutputPermutation_pauli (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : Bas)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    binaryOutputPermutation π b (.pauli W) x = x :=
  (binaryVectorEquiv b).apply_symm_apply x

end Binary
end MIPRE.QLD.PauliCL.ExplicitSeed
