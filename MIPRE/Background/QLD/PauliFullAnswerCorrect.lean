/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliFullAnswerPrograms
import MIPRE.Background.QLD.PauliAnswerRoundtrip

/-! # Full-register projection of every valid raw Pauli answer -/

noncomputable section
namespace MIPRE.QLD.PauliFullAnswerProgram
open Cost SAT PauliAnswerProgram Introspection.FieldTableProgram

def decodedOutcome {k : ℕ} (E : BinField k) (m : ℕ) (W : Bas) (bs : BitStr) :
    (Fin m → Bool) → E.carrier :=
  fun y => E.ofBits ((parser (.pauli W, unary m, unary k, unary 1, bs)).2.getD
    (cubeEnumeration m y).val [])

theorem decodeBits_pauli {k : ℕ} (E : BinField k) (m : ℕ) (W : Bas) (bs : BitStr) :
    decodeBits E m 1 (.pauli W) bs = .pauliAns (decodedOutcome E m W bs) := rfl

theorem program_raw (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (m : ℕ) (W : Bas) (bs : BitStr)
    (hvalid : (parser (.pauli W, unary m, unary k, unary 1, bs)).1 = true) :
    program (unary m, unary k, bs) =
      (true, CL.toBits (registerVector (shoupSelfDualNormalBasis k hk hodd)
        (decodedOutcome (shoupBinField k hk) m W bs))) := by
  have he := program_answerBits k hk hodd m 1 (decodedOutcome (shoupBinField k hk) m W bs)
  rw [← decodeBits_pauli, answerBits_decodeBits k hk m 1 (.pauli W) bs hvalid] at he
  exact he

theorem program_output_length (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (m : ℕ) (W : Bas) (bs : BitStr)
    (hvalid : (parser (.pauli W, unary m, unary k, unary 1, bs)).1 = true) :
    (program (unary m, unary k, bs)).2.length = 2 ^ m * k := by
  rw [program_raw k hk hodd m W bs hvalid]
  exact List.length_ofFn

end MIPRE.QLD.PauliFullAnswerProgram
end
