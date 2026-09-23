/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliBinaryPrograms
import MIPRE.Background.QLD.PauliBooleanRaw
import MIPRE.Background.QLD.PauliFullAnswerCorrect

/-! # Raw Pauli programs for the final introspection compiler -/

noncomputable section
namespace MIPRE.QLD.PauliBinaryProgram
open Cost Cost.PolyTimeFun SAT PauliCL PauliAnswerProgram
  Introspection.PauliStageProgram

/-- Exact answer format at one raw typed endpoint. -/
def endpointValid : PolyTimeFun (Parameters × Payload) Bool :=
  fst.comp (parser.comp ((fst.comp snd).pair
    ((snd.comp (snd.comp fst)).pair ((fst.comp fst).pair
      ((const (unary 1)).pair (snd.comp (snd.comp snd)))))))

theorem endpointValid_apply (k j m : Unary) (T : Ty) (q a : BitStr) :
    endpointValid ((k, j, m), T, q, a) = (parser (T, m, k, unary 1, a)).1 := rfl

/-- Full X/Z outcomes use exactly the same parameters as the query compiler. -/
def fullAnswer : PolyTimeFun (Parameters × BitStr) (Bool × BitStr) :=
  PauliFullAnswerProgram.program.comp
    ((snd.comp (snd.comp fst)).pair ((fst.comp fst).pair snd))

theorem fullAnswer_apply (k j m : Unary) (a : BitStr) :
    fullAnswer ((k, j, m), a) = PauliFullAnswerProgram.program (m, k, a) := rfl

def questionOfBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (T : Ty) (q : BitStr) : Question (shoupBinField k hk).carrier (2 ^ j) :=
  ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T
    ((binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
      (CL.ofBits ((3 * 2 ^ j + 3) * k) q))

/-- On every full-length question payload, the actual raw program is exactly
the QLD acceptance relation after the proved basis and answer decoders. -/
theorem program_ofBits_iff (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (hj : j ≤ k) (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (T U : Ty) (q r a b : BitStr)
    (hq : q.length = (3 * 2 ^ j + 3) * k)
    (hr : r.length = (3 * 2 ^ j + 3) * k) :
    program ((unary k, unary j, unary (2 ^ j)), (T, q, a), (U, r, b)) = true ↔
      endpointValid ((unary k, unary j, unary (2 ^ j)), T, q, a) = true ∧
      endpointValid ((unary k, unary j, unary (2 ^ j)), U, r, b) = true ∧
      accepts hm (questionOfBits k hk hodd j T q) (questionOfBits k hk hodd j U r)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 U b) = true := by
  simp only [program, comp_apply, booleanInput, endpointProg, pair_apply,
    fst_apply, snd_apply, fieldsProg_ofBits k hk hodd _ _ q hq,
    fieldsProg_ofBits k hk hodd _ _ r hr, endpointValid_apply, questionOfBits]
  exact PauliBooleanProgram.program_raw_iff k hk j hj hm T U _ _ a b

theorem program_canonical (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (hj : j ≤ k) (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (T U : Ty) (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier)
    (a b : Answer (shoupBinField k hk).carrier (2 ^ j) 1)
    (ha : (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y).fmtOk b = true) :
    program ((unary k, unary j, unary (2 ^ j)),
      (T, CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x),
        answerBits (shoupBinField k hk) a),
      (U, CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) y),
        answerBits (shoupBinField k hk) b)) =
      accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x)
        (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y) a b := by
  rw [program, comp_apply, booleanInput_correct k hk hodd]
  exact PauliBooleanProgram.program_correct_formatted k hk j hj hm T U x y a b ha hb

end MIPRE.QLD.PauliBinaryProgram
end
