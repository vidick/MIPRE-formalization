/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernel
import MIPRE.Foundations.Introspection.AuxiliaryDecisionCorrect

/-! # The decision kernel on canonical verifier inputs

The resource tuple supplied by preparation is identified with the canonical
bounded-source context used in the auxiliary correctness proofs.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun SourcePadding.Program
set_option backward.isDefEq.respectTransparency false

/-- Canonical prepared input with explicit register parameters. -/
def canonicalInput (V : Verifier 7) (lam n Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr) : Input :=
  (encode (n,T,x,U,y,a,b),((V.sampler.prog,V.decider.prog),lam),
    unary (ansBound 5 lam n),2 ^ n,p,Q,R)

theorem canonicalInput_fields (V : Verifier 7) (lam n Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr) :
    leftType (canonicalInput V lam n Q R p T U x y a b) = T ∧
      rightType (canonicalInput V lam n Q R p T U x y a b) = U ∧
      leftBits (canonicalInput V lam n Q R p T U x y a b) = a ∧
      rightBits (canonicalInput V lam n Q R p T U x y a b) = b := by
  simp only [canonicalInput, leftType, rightType, leftBits, rightBits, raw, comp_apply,
    fst_apply, leftLabelField_encode, rightLabelField_encode,
    leftAnswerField_encode, rightAnswerField_encode, and_self]

theorem sourceContext_canonical (V : Verifier 7) (lam n Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr)
    (hab : Q ≤ a.length + b.length) :
    sourceContext (canonicalInput V lam n Q R p T U x y a b) =
      queryContext V lam n false 0 (0 : Fin Q → CL.𝔽₂) := by
  have hz := zeroPrefix_of_length (canonicalInput V lam n Q R p T U x y a b)
    (by simpa only [canonicalInput_fields, registerWidth, resourceTail, canonicalInput,
      comp_apply, fst_apply, snd_apply, leftBits, rightBits, raw,
      leftAnswerField_encode, rightAnswerField_encode] using hab)
  rw [sourceContext_apply,hz]
  simp only [budget, sourceSampler, sourceIndex, resourceTail, metadata, registerWidth,
    canonicalInput, comp_apply, fst_apply, snd_apply, queryContext,
    CL.Detyping.toBits_zero, Nat.zero_add]

theorem auxiliaryInput_canonical (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) (Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr)
    (hab : Q ≤ a.length + b.length) :
    auxiliaryInput W (canonicalInput V lam n Q R p T U x y a b) =
      AuxiliaryDecision.canonical V lam n Q R p T U a b := by
  have hc := sourceContext_canonical V lam n Q R p T U x y a b hab
  have hd : sourceDimension W (canonicalInput V lam n Q R p T U x y a b) =
      V.sampler.dim (2 ^ n) := by
    rw [sourceDimension, comp_apply, hc]
    exact queryContext_dimension W V hV hn false 0 0
  rw [auxiliaryInput_apply,hc,hd]
  simp only [AuxiliaryDecision.canonical, registerWidth, originalCutoff, sourceDecider,
    metadata, parameters, resourceTail, canonicalInput, leftType, rightType, leftBits,
    rightBits, raw, comp_apply, fst_apply, snd_apply, leftLabelField_encode,
    rightLabelField_encode, leftAnswerField_encode, rightAnswerField_encode]

end MIPRE.Introspection.DecisionKernel
end
