/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.PauliAnswerPrograms

@[expose] public section

/-!
# The Pauli labels of the tailored question reduction

The Pauli basis test's answers keep their byte encodings in the tailored layout
(`MIPRE.Tailored.Intro.enc`): a label `T` has `count T m 1` blocks of `width T k` bits
(`QLD.PauliAnswerProgram`), all readable at the `Z`-basis Pauli label and all linear otherwise.
-/

namespace MIPRE.Tailored.Intro

open MIPRE.QLD

/-- The number of answer bits of a Pauli label, for registers of `2^m` field elements of `k`
bits, at degree `1`. -/
def pauliLen (m k : ℕ) (T : Ty) : ℕ := PauliAnswerProgram.count T m 1 * PauliAnswerProgram.width T k

/-- The readable Pauli label: the `Z`-basis Pauli answer. -/
def pauliRead : Ty → Bool
  | .pauli .Z => true
  | _ => false

theorem pauliLen_pauli (m k : ℕ) (W : Bas) : pauliLen m k (.pauli W) = 2 ^ m * k := rfl

end MIPRE.Tailored.Intro

end
