/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelPauli
import MIPRE.Foundations.Introspection.BoundedAnswerCoding

/-! # The finite answer decoder for the actual decision kernel -/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost SAT
set_option backward.isDefEq.respectTransparency false

namespace Answer

def pauliDecode {k : ℕ} (E : BinField k) (m : ℕ) (t : Label) (bs : BitStr) :
    QLD.Answer E.carrier m 1 := QLD.PauliAnswerProgram.decodeBits E m 1 (pauliLabel t) bs

/-- The codomain is finite: both the source answer and the Pauli answer have
their actual bounded semantic alphabets. -/
def decode {k : ℕ} (E : BinField k) (m Q R : ℕ) (t : Label) (bs : BitStr) :
    ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1) :=
  ParsedAnswer.mapPauli (pauliDecode E m) t
    (ParsedAnswer.mapAnswer (AuxiliaryAnswer.bounded R) (AuxiliaryAnswer.decode Q t bs))

@[simp] theorem decode_pauli {k : ℕ} (E : BinField k) (m Q R : ℕ)
    (T : QLD.Ty) (bs : BitStr) :
    decode E m Q R (.inl T) bs = .pauli (QLD.PauliAnswerProgram.decodeBits E m 1 T bs) := rfl

/-- In particular every raw full-Pauli outcome lands in the legal full-table constructor. -/
theorem decode_pauli_full {k : ℕ} (E : BinField k) (m Q R : ℕ)
    (W : QLD.Bas) (bs : BitStr) :
    decode E m Q R (.inl (.pauli W)) bs =
      .pauli (.pauliAns (QLD.PauliFullAnswerProgram.decodedOutcome E m W bs)) := rfl

theorem decode_fits {k : ℕ} (E : BinField k) (m Q R : ℕ) (t : Label) (bs : BitStr) :
    TypedPredicate.fits t (decode E m Q R t bs) = true := by
  simp only [decode, ParsedAnswer.fits_mapPauli, ParsedAnswer.fits_mapAnswer,
    AuxiliaryAnswer.decode_fits]

theorem questionOfBits_ty (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (T : QLD.Ty) (q : BitStr) :
    (QLD.PauliBinaryProgram.questionOfBits k hk hodd j T q).ty = T := by
  cases T <;> rfl

/-- Every decoded Pauli outcome is legal even when its raw input was malformed. -/
theorem pauliDecode_format (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (T : QLD.Ty) (q a : BitStr) :
    (QLD.PauliBinaryProgram.questionOfBits k hk hodd j T q).fmtOk
      (pauliDecode (shoupBinField k hk) (2 ^ j) (.inl T) a) = true := by
  have h := QLD.PauliAnswerProgram.decodeBits_format (d := 1) (shoupBinField k hk)
    (QLD.PauliBinaryProgram.questionOfBits k hk hodd j T q) a
  rw [questionOfBits_ty] at h
  exact h

def pauliProject {F : Type*} [Field F] [Algebra (ZMod 2) F] {m k : ℕ}
    (basis : Module.Basis (Fin k) (ZMod 2) F) : QLD.Answer F m 1 → Fin (2 ^ m * k) → CL.𝔽₂
  | .pauliAns h => QLD.PauliFullAnswerProgram.registerVector basis h
  | _ => 0

theorem pauliProject_numbering {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) F)
    (h : (Fin m → Bool) → F) :
    pauliProject basis (.pauliAns h) =
      fun i => Weyl.binEquiv basis h ((QLD.PauliFullAnswerProgram.registerNumbering m k).symm i) := rfl

/-- Read the executable projection at a fixed finite register size. -/
def rawProject (p : PauliSamplerParameters.Parameters) (Q : ℕ) (bs : BitStr) : Fin Q → CL.𝔽₂ :=
  CL.ofBits Q (QLD.PauliBinaryProgram.fullAnswer (p,bs)).2

theorem rawProject_pauliDecode (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) (W : QLD.Bas) (a : BitStr)
    (ha : (QLD.PauliAnswerProgram.parser (.pauli W,unary m,unary k,unary 1,a)).1 = true) :
    rawProject (unary k,unary j,unary m) (2 ^ m * k) a =
      pauliProject (shoupSelfDualNormalBasis k hk hodd)
        (pauliDecode (shoupBinField k hk) m (.inl (.pauli W)) a) := by
  rw [rawProject, QLD.PauliBinaryProgram.fullAnswer_apply,
    QLD.PauliFullAnswerProgram.program_raw k hk hodd m W a ha]
  simp only [CL.ofBits_toBits, pauliDecode, pauliLabel,
    QLD.PauliFullAnswerProgram.decodeBits_pauli, pauliProject]

end Answer

theorem program_leftPauli_valid (W : ClockedUniversalMachine) (V : Verifier 7)
    (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters) (T : QLD.Ty) (U : Label)
    (x y a b : BitStr)
    (h : program W (canonicalInput V lam n Q R p (.inl T) U x y a b) = true) :
    QLD.PauliBinaryProgram.endpointValid (p,T,x,a) = true := by
  have hf := ((program_iff W _).mp h).2.2.1
  rwa [leftPauliFormat_canonicalInput] at hf

theorem program_rightPauli_valid (W : ClockedUniversalMachine) (V : Verifier 7)
    (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters) (T : Label) (U : QLD.Ty)
    (x y a b : BitStr)
    (h : program W (canonicalInput V lam n Q R p T (.inl U) x y a b) = true) :
    QLD.PauliBinaryProgram.endpointValid (p,U,y,b) = true := by
  have hf := ((program_iff W _).mp h).2.2.2.1
  rwa [rightPauliFormat_canonicalInput] at hf

end MIPRE.Introspection.DecisionKernel
end
