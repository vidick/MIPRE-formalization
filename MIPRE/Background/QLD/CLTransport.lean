/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.CLBinary

/-! # Exact strategy transport between the Pauli game and its binary CL form

Question content has a canonical ambient encoding, with unused registers set
to zero. This encoding inverts the decoder on every attained CL output.
Consequently arbitrary strategies for the binary typed game pull back to the
existing Pauli game with exactly the same state, dimensions, and value.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

def pointContent (W : Bas) (u : Fin m → F) (s : F) (v : Fin m → F) : Content F m :=
  match W with
  | .X => ⟨u, 0, s, v, 0, 0⟩
  | .Z => ⟨0, u, s, v, 0, 0⟩

def omegaContent (ω : Omega F m) : Content F m := ⟨ω.uX, ω.uZ, 0, 0, ω.rX, ω.rZ⟩

/-- The canonical ambient encoding of question content. -/
def canonicalVector (q : Question F m) : Coord m → F :=
  contentVector (match q with
    | .point W u => pointContent W u 0 0
    | .aline W u s => pointContent W u s 0
    | .dline W u s v => pointContent W u s v
    | .pauli _ => ⟨0, 0, 0, 0, 0, 0⟩
    | .pairB _ ω | .pair ω | .con _ ω | .var _ ω => omegaContent ω)

theorem canonicalVector_pauli (W : Bas) :
    canonicalVector (F := F) (m := m) (.pauli W) = 0 := by
  funext i
  cases i with
  | point W i => cases W <;> rfl
  | scalar W => cases W <;> rfl
  | seed => rfl
  | direction i => rfl

theorem questionOfVector_canonical [NeZero m] (q : Question F m) :
    questionOfVector q.ty (canonicalVector q) = q := by
  cases q <;> (try cases ‹Bas›) <;>
    simp [questionOfVector, canonicalVector, pointContent, omegaContent,
      vectorContent, contentVector, Question.ty, Content.pt, Content.omega]

/-- No information is lost by decoding an attained field CL output. -/
theorem canonicalVector_question [NeZero m] (hm : m ∣ Fintype.card F)
    (T : Ty) (c : Content F m) :
    canonicalVector (c.question hm T) = (presentation hm T).eval (contentVector c) := by
  cases T <;> (try cases ‹Bas›) <;> funext i
  all_goals cases i
  all_goals (try cases ‹Bas›)
  all_goals
    simp only [canonicalVector, pointContent, omegaContent, presentation,
      seedMap, secondMap, finalMap, CL.CLFun.eval, CL.RegLinear.zero_apply,
      CL.RegLinear.id_apply, pointMap_apply, directionMap_apply,
      Pi.add_apply, Pi.zero_apply, Content.question, Content.pt, Content.omega,
      contentVector, LIDT.CL.rep]
    simp [CL.proj_apply, seedSet, directionSet, finalSet, contentVector]
  all_goals rfl

variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}

abbrev BinaryQuestion (m t : ℕ) := Ty × (Fin ((3 * m + 3) * t) → ZMod 2)

def encodeQuestion (b : Module.Basis (Fin t) (ZMod 2) F) (q : Question F m) :
    BinaryQuestion m t := (q.ty, binaryVectorEquiv b (canonicalVector q))

def decodeQuestion (b : Module.Basis (Fin t) (ZMod 2) F) (q : BinaryQuestion m t) :
    Question F m := binaryQuestion b q.1 q.2

theorem decode_encode (b : Module.Basis (Fin t) (ZMod 2) F) (q : Question F m) :
    decodeQuestion b (encodeQuestion b q) = q := by
  simp only [decodeQuestion, encodeQuestion, binaryQuestion,
    LinearEquiv.symm_apply_apply, questionOfVector_canonical]

theorem encodeQuestion_seed (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (c : Content F m) :
    encodeQuestion b (c.question hm T) =
      (T, (binaryPresentation hm b T).eval (binaryVectorEquiv b (contentVector c))) := by
  simp only [encodeQuestion, Content.question_ty, canonicalVector_question,
    binaryPresentation_eval]

/-- The inverse law is restricted to actual CL outputs, as required. -/
theorem encode_decode_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) :
    encodeQuestion b (decodeQuestion b (T, (binaryPresentation hm b T).eval x)) =
      (T, (binaryPresentation hm b T).eval x) := by
  obtain ⟨z, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective x
  obtain ⟨c, rfl⟩ := (contentEquiv (F := F) (m := m)).surjective z
  change encodeQuestion b (binaryQuestion b T
    ((binaryPresentation hm b T).eval (binaryVectorEquiv b (contentVector c)))) = _
  rw [binaryQuestion_presentation, encodeQuestion_seed]
  rfl

def binaryQuery (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (w : Bool) (p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2)) : BinaryQuestion m t :=
  let T := if w then p.1.val.2 else p.1.val.1
  (T, (binaryPresentation hm b T).eval p.2)

/-- The actual typed binary CL game, with the existing Pauli acceptance rule
applied to decoded questions. -/
def binaryGame (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    Game (BinaryQuestion m t) (BinaryQuestion m t) (Answer F m d) (Answer F m d) := by
  letI : Nonempty TyEdge := ⟨⟨(.pair, .pair), by decide⟩⟩
  exact SampledGame.game (binaryQuery hm b false) (binaryQuery hm b true)
    (fun x y a b' => accepts hm (decodeQuestion b x) (decodeQuestion b y) a b')

/-- Play the binary game's measurements at the canonical encoding of each
Pauli question. The shared state is unchanged. -/
def pullbackStrategy (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) :
    TensorProductStrategy (qldGame (d := d) hm) where
  dA := S.dA
  dB := S.dB
  ψ := S.ψ
  ψ_unit := S.ψ_unit
  PA := S.PA.reindex (encodeQuestion b) (Equiv.refl _)
  PB := S.PB.reindex (encodeQuestion b) (Equiv.refl _)

theorem pullbackStrategy_value (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) :
    (pullbackStrategy hm b S).value = S.value := by
  rw [TensorProductStrategy.value_eq_sum_succAt, TensorProductStrategy.value_eq_sum_succAt]
  simp_rw [qldGame_mu_binaryPresentation hm b]
  rw [SampledGame.sum_dist_mul]
  change _ = ∑ x, ∑ y, SampledGame.dist (binaryQuery hm b false)
    (binaryQuery hm b true) x y * S.succAt x y
  rw [SampledGame.sum_dist_mul]
  apply congrArg (fun r : ℝ => r /
    (Fintype.card (TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2)) : ℝ))
  refine Finset.sum_congr rfl fun p _ => ?_
  have hA := encode_decode_eval hm b p.1.val.1 p.2
  have hB := encode_decode_eval hm b p.1.val.2 p.2
  simp only [decodeQuestion] at hA hB
  unfold TensorProductStrategy.succAt TensorProductStrategy.born
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    binaryGame, SampledGame.game, binaryQuery, Bool.false_eq_true, ↓reduceIte,
    decodeQuestion, hA, hB, qldGame_D]
  rfl

theorem pullbackStrategy_pauli_A (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) (W : Bas) (a : Answer F m d) :
    (pullbackStrategy hm b S).PA.M (.pauli W) a = S.PA.M (.pauli W, 0) a := by
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    encodeQuestion, Question.ty, canonicalVector_pauli, map_zero]

theorem pullbackStrategy_pauli_B (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) (W : Bas) (a : Answer F m d) :
    (pullbackStrategy hm b S).PB.M (.pauli W) a = S.PB.M (.pauli W, 0) a := by
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    encodeQuestion, Question.ty, canonicalVector_pauli, map_zero]

end MIPRE.QLD.PauliCL
end
