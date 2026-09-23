/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliBooleanDispatch
import MIPRE.Background.QLD.PauliAnswerRoundtrip

/-! # Exact raw-answer semantics of the executable Pauli predicate -/

noncomputable section
namespace MIPRE.QLD.PauliBooleanProgram
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram

/-- Acceptance forces the exact answer format at both original endpoints,
regardless of which orientation the arithmetic router uses. -/
theorem program_formats (input : Input) (h : program input = true) :
    (parser (input.2.1.1, input.1.2.2, input.1.1, unary 1, input.2.1.2.2)).1 = true ∧
    (parser (input.2.2.1, input.1.2.2, input.1.1, unary 1, input.2.2.2.2)).1 = true := by
  rw [program_apply, Bool.and_eq_true, Bool.and_eq_true] at h
  have hp := h.1
  cases ho : (route input).2.1 <;>
    simp only [leftParser, rightParser, left, right, oriented,
      leftBits, rightBits, dim, width, params, endpoints,
      comp_apply, pair_apply, fst_apply, snd_apply, const_apply,
      ho] at hp
  · exact hp
  · exact hp.symm

set_option backward.isDefEq.respectTransparency false in
theorem program_raw_correct_valid (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (T U : Ty)
    (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier) (a b : BitStr)
    (ha : (parser (T, unary (2 ^ j), unary k, unary 1, a)).1 = true)
    (hb : (parser (U, unary (2 ^ j), unary k, unary 1, b)).1 = true) :
    program ((unary k, unary j, unary (2 ^ j)),
      (T, fieldEncoding (shoupBinField k hk) x, a),
      (U, fieldEncoding (shoupBinField k hk) y, b)) =
      accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x)
        (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) := by
  have hfa := decodeBits_format (d := 1) (shoupBinField k hk)
    (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x) a
  have hfb := decodeBits_format (d := 1) (shoupBinField k hk)
    (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y) b
  simp only [explicitDecode_ty] at hfa hfb
  have he := program_correct_formatted k hk j hj hm T U x y
    (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
    (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) hfa hfb
  simpa only [encodedInput, answerBits_decodeBits k hk _ _ T a ha,
    answerBits_decodeBits k hk _ _ U b hb] using he

/-- The whole raw predicate: exact parsing followed by the QLD predicate on
the uniquely decoded semantic answers. Malformed payloads are rejected. -/
theorem program_raw_iff (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (T U : Ty)
    (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier) (a b : BitStr) :
    program ((unary k, unary j, unary (2 ^ j)),
      (T, fieldEncoding (shoupBinField k hk) x, a),
      (U, fieldEncoding (shoupBinField k hk) y, b)) = true ↔
      (parser (T, unary (2 ^ j), unary k, unary 1, a)).1 = true ∧
      (parser (U, unary (2 ^ j), unary k, unary 1, b)).1 = true ∧
      accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x)
        (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) = true := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := program_formats _ h
    exact ⟨ha, hb, (program_raw_correct_valid k hk j hj hm T U x y a b ha hb).symm.trans h⟩
  · rintro ⟨ha, hb, h⟩
    exact (program_raw_correct_valid k hk j hj hm T U x y a b ha hb).trans h

end MIPRE.QLD.PauliBooleanProgram
end
