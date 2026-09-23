/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelCanonical

/-! # Pauli semantics of the actual prepared decision kernel -/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun AuxiliaryProgram SAT
set_option backward.isDefEq.respectTransparency false

variable (V : Verifier 7) (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters)
  (T U : Label) (x y a b : BitStr)

theorem canonical_canonicalInput :
    canonical (canonicalInput V lam n Q R p T U x y a b) = true :=
  canonical_encode _ _ _ _ _ _ _ _ _ _ _ _ _

theorem questionLengths_canonicalInput :
    questionLengths (canonicalInput V lam n Q R p T U x y a b) = true ↔
      x.length = (3 * p.2.2.length + 3) * p.1.length ∧
      y.length = (3 * p.2.2.length + 3) * p.1.length := by
  rw [questionLengths, andCheck_iff]
  simp only [equal_iff, comp_apply, CL.Detyping.DeciderProgram.lengthNat_apply,
    questionDimension_apply, parameters, resourceTail, canonicalInput, fst_apply,
    snd_apply, leftQuestion, rightQuestion, raw, leftQuestionField_encode,
    rightQuestionField_encode]

theorem leftPauliFormat_canonicalInput (t : QLD.Ty) :
    leftPauliFormat (canonicalInput V lam n Q R p (.inl t) U x y a b) =
      QLD.PauliBinaryProgram.endpointValid (p,t,x,a) := by
  simp only [leftPauliFormat, PolyTimeFun.ite_apply, leftIsPauli, comp_apply,
    finiteFunction_apply, leftType, raw, canonicalInput, fst_apply, leftLabelField_encode,
    isPauli, ↓reduceIte, pair_apply, leftPauliPayload, pauliLabel, leftQuestion,
    leftQuestionField_encode, leftBits, leftAnswerField_encode,
    parameters, resourceTail, snd_apply]

theorem rightPauliFormat_canonicalInput (u : QLD.Ty) :
    rightPauliFormat (canonicalInput V lam n Q R p T (.inl u) x y a b) =
      QLD.PauliBinaryProgram.endpointValid (p,u,y,b) := by
  simp only [rightPauliFormat, PolyTimeFun.ite_apply, rightIsPauli, comp_apply,
    finiteFunction_apply, rightType, raw, canonicalInput, fst_apply, rightLabelField_encode,
    isPauli, ↓reduceIte, pair_apply, rightPauliPayload, pauliLabel, rightQuestion,
    rightQuestionField_encode, rightBits, rightAnswerField_encode,
    parameters, resourceTail, snd_apply]

theorem pauli_canonicalInput (t u : QLD.Ty) :
    pauli (canonicalInput V lam n Q R p (.inl t) (.inl u) x y a b) =
      QLD.PauliBinaryProgram.program (p,(t,x,a),(u,y,b)) := by
  rw [pauli_apply]
  simp only [andCheck, PolyTimeFun.ite_apply, leftIsPauli, rightIsPauli, comp_apply,
    finiteFunction_apply, leftType, rightType, raw, canonicalInput, fst_apply,
    leftLabelField_encode, rightLabelField_encode, isPauli, ↓reduceIte,
    leftPauliPayload, rightPauliPayload, pair_apply, pauliLabel, leftQuestion,
    rightQuestion, leftQuestionField_encode, rightQuestionField_encode, leftBits,
    rightBits, leftAnswerField_encode, rightAnswerField_encode, parameters, resourceTail,
    snd_apply]

omit p T U in
/-- Every actual Pauli-pair computation agrees with QLD on the decoded raw bytes. -/
theorem program_pauli_iff (W : ClockedUniversalMachine)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (t u : QLD.Ty)
    (hx : x.length = (3 * 2 ^ j + 3) * k)
    (hy : y.length = (3 * 2 ^ j + 3) * k) :
    let p : PauliSamplerParameters.Parameters := (unary k,unary j,unary (2 ^ j))
    program W (canonicalInput V lam n Q R p (.inl t) (.inl u) x y a b) = true ↔
      QLD.PauliBinaryProgram.endpointValid (p,t,x,a) = true ∧
      QLD.PauliBinaryProgram.endpointValid (p,u,y,b) = true ∧
      QLD.accepts hm (QLD.PauliBinaryProgram.questionOfBits k hk hodd j t x)
        (QLD.PauliBinaryProgram.questionOfBits k hk hodd j u y)
        (QLD.PauliAnswerProgram.decodeBits (shoupBinField k hk) (2 ^ j) 1 t a)
        (QLD.PauliAnswerProgram.decodeBits (shoupBinField k hk) (2 ^ j) 1 u b) = true ∧
      auxiliary W (canonicalInput V lam n Q R p (.inl t) (.inl u) x y a b) = true := by
  dsimp only
  rw [program_iff, canonical_canonicalInput, questionLengths_canonicalInput,
    leftPauliFormat_canonicalInput, rightPauliFormat_canonicalInput, pauli_canonicalInput,
    QLD.PauliBinaryProgram.program_ofBits_iff k hk hodd j hj hm t u x y a b hx hy]
  simp only [length_unary, hx, hy, true_and]
  tauto

omit p T U x y in
/-- The callback uses the same explicit full-register numbering as the semantic Pauli outcome. -/
theorem project_canonicalInput (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) (W : QLD.Bas) (u : Label)
    (ha : (QLD.PauliAnswerProgram.parser (.pauli W,unary m,unary k,unary 1,a)).1 = true) :
    project (AuxiliaryDecision.canonical V lam n Q R (unary k,unary j,unary m)
      (.inl (.pauli W)) u a b) =
      CL.toBits (QLD.PauliFullAnswerProgram.registerVector (shoupSelfDualNormalBasis k hk hodd)
        (QLD.PauliFullAnswerProgram.decodedOutcome (shoupBinField k hk) m W a)) := by
  change (QLD.PauliBinaryProgram.fullAnswer ((unary k,unary j,unary m),a)).2 = _
  rw [QLD.PauliBinaryProgram.fullAnswer_apply,
    QLD.PauliFullAnswerProgram.program_raw k hk hodd m W a ha]

end MIPRE.Introspection.DecisionKernel
end
