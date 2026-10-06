/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.HonestChain
public import MIPRE.Background.Tailored.Intro.HonestPauli
public import MIPRE.Tailored.Intro.HonestAux
public import MIPRE.Tailored.Intro.LayoutBits

@[expose] public section

/-!
# The measurement of the honest strategy at a typed question

The honest strategy of the guarded game (`HonestChain.canonical`) measures, at a typed question
`(w, (p, z))`, the honest binary operator of the label `p` (`BinaryComplete.op`), relabelled to
the binary Weyl coordinates of the answers (`AuxiliaryQuotient.answerEquiv`) and conjugated by
the numbering of its space (`canonical_M`). This file reduces a bit of its outcome to a bit of
the honest Pauli measurement (`QLD.Honest.answerOp`, at a Pauli label) or of the honest auxiliary
measurement (`Honest.auxOp`, at an auxiliary label), whose bits
`MIPRE.Tailored.Intro.HonestPauli` and `MIPRE.Tailored.Intro.HonestAux` compute.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.HonestChain

open Cost MIPRE.CL MIPRE.Introspection MIPRE.Introspection.CanonicalGame
open MIPRE.Introspection.DecisionCompiler MIPRE.Introspection.SourceCompiler
open MIPRE.Introspection.PauliSamplerParameters
open scoped Kronecker

attribute [local instance] power_neZero

variable {c : ℕ} (W : Verifier 7) {lam n : ℕ}
  (RW : SyncStrategy (W.game (2 ^ n) ((2 ^ n) ^ lam)).doubled)
  (hc1 : 1 ≤ c) (he : Even c) (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n)

/-- **The honest measurement at a typed question.** -/
theorem canonical_M (w : Bool) (p : QuestionType QLD.Ty 7)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (a : CanonicalComplete.Answer c lam n) :
    (canonical W RW hc1 he hs).P.M (w, (p, z)) a =
      (BinaryComplete.op (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
        (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
        (ExplicitGame.questionEquiv (permutation c lam n) (basis c he lam n) (p, z))
        (AuxiliaryQuotient.answerEquiv (numbering c lam n) a)).submatrix
        (Fintype.equivFin (BinaryComplete.Space (family W hs) (decider W hs)
          (reindexed W RW hs))).symm
        (Fintype.equivFin (BinaryComplete.Space (family W hs) (decider W hs)
          (reindexed W RW hs))).symm := rfl

/-- **A bit of the honest measurement at a typed question is a bit of the binary operator**, read
through the relabelling of the answers. -/
theorem isXBit_canonical (w : Bool) (p : QuestionType QLD.Ty 7)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (g : CanonicalComplete.Answer c lam n → Bool)
    (h : IsXBit (BinaryComplete.op (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
        (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
        (ExplicitGame.questionEquiv (permutation c lam n) (basis c he lam n) (p, z)))
      (g ∘ (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm)) :
    IsXBit ((canonical W RW hc1 he hs).P.M (w, (p, z))) g := by
  rw [show (canonical W RW hc1 he hs).P.M (w, (p, z)) = _ from
    funext (canonical_M W RW hc1 he hs w p z)]
  refine IsXBit.submatrix_equiv ?_ _
  unfold IsXBit at h ⊢
  exact (congrArg IsSignedPerm (bitObs_comp_equiv' _ _ _)).mpr h

theorem isZBit_canonical (w : Bool) (p : QuestionType QLD.Ty 7)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (g : CanonicalComplete.Answer c lam n → Bool)
    (h : IsZBit (BinaryComplete.op (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
        (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
        (ExplicitGame.questionEquiv (permutation c lam n) (basis c he lam n) (p, z)))
      (g ∘ (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm)) :
    IsZBit ((canonical W RW hc1 he hs).P.M (w, (p, z))) g := by
  rw [show (canonical W RW hc1 he hs).P.M (w, (p, z)) = _ from
    funext (canonical_M W RW hc1 he hs w p z)]
  refine IsZBit.submatrix_equiv ?_ _
  unfold IsZBit at h ⊢
  exact ⟨(congrArg IsSignedPerm (bitObs_comp_equiv' _ _ _)).mpr h.1,
    (congrArg Matrix.IsDiag (bitObs_comp_equiv' _ _ _)).mpr h.2⟩

/-! ## Pauli labels -/

theorem pauli_injective {V A PA : Type*} :
    Function.Injective (ParsedAnswer.pauli : PA → ParsedAnswer V A PA) :=
  fun x y h => by cases h; rfl

theorem parsedPauliOp_eq_extend {I V A PA : Type*} [Fintype I] [DecidableEq I]
    (M : PA → Matrix I I ℂ) :
    Honest.parsedPauliOp (V := V) (A := A) M = Function.extend ParsedAnswer.pauli M 0 := by
  funext a
  cases a with
  | pauli a =>
    exact (pauli_injective.extend_apply M 0 a).symm
  | _ =>
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
    rfl

/-- The `i`-th bit of the tailored encoding of an answer of the guarded game. -/
def fbit (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (p : QuestionType QLD.Ty 7) (i : ℕ) (a : CanonicalComplete.Answer c lam n) : Bool :=
  (enc (registerBits c lam n) R splitR p (CanonicalComplete.encodeAnswer c hc lam n a).1).getD
    i false

theorem fbit_pauli (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (T : QLD.Ty) (i : ℕ) (a : QLD.Answer (field c lam n).carrier (registerPower c lam n) 1) :
    fbit (lam := lam) (n := n) hc R splitR (.inl T) i (.pauli a) =
      answerBit (fieldBits_pos c lam n) i a := rfl

/-- **At a Pauli label every bit is a signed permutation.** -/
theorem isXBit_canonical_pauli (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (w : Bool) (T : QLD.Ty) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (i : ℕ) :
    IsXBit ((canonical W RW hc1 he hs).P.M (w, (.inl T, z))) (fbit hc R splitR (.inl T) i) := by
  apply isXBit_canonical
  unfold IsXBit
  change IsSignedPerm (bitObs (Honest.parsedPauliOp _) _)
  rw [parsedPauliOp_eq_extend, bitObs_extend _ pauli_injective]
  exact ((isXBit_answerOp (fieldBits_pos c lam n) (divides c hc1 lam n) _ i).kronecker_one
    (Ω' := Fin (reindexed W RW hs).d)).submatrix_equiv _

/-- **At the `(Pauli, Z)` label every bit is a `±1` diagonal.** -/
theorem isZBit_canonical_pauliZ (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (w : Bool) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (i : ℕ) :
    IsZBit ((canonical W RW hc1 he hs).P.M (w, (.inl (.pauli .Z), z)))
      (fbit hc R splitR (.inl (.pauli .Z)) i) := by
  apply isZBit_canonical
  unfold IsZBit
  change IsSignedPerm (bitObs (Honest.parsedPauliOp _) _) ∧ (bitObs (Honest.parsedPauliOp _) _).IsDiag
  rw [parsedPauliOp_eq_extend, bitObs_extend _ pauli_injective]
  exact ((isZBit_answerOp_pauliZ (fieldBits_pos c lam n) (divides c hc1 lam n) i).kronecker_one
    (Ω' := Fin (reindexed W RW hs).d)).submatrix_equiv _

end MIPRE.Tailored.Intro.HonestChain

end
