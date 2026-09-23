/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliAnswerCoding
import MIPRE.Background.QLD.BinaryBlocks
import MIPRE.Foundations.WeylBinary

/-! # Executable full Pauli answers in the self-dual register coordinates

Full field tables are enumerated by the same little-endian cube enumeration
as the Pauli evaluator. Each entry is then expanded in the proved self-dual
basis. This fixes the full-register numbering explicitly.
-/

noncomputable section
namespace MIPRE.QLD.PauliFullAnswerProgram
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear
  Introspection.FieldTableProgram Introspection.FieldAnswerParser Introspection.BinaryBlock

def registerNumbering (m k : ℕ) : ((Fin m → Bool) × Fin k) ≃ Fin (2 ^ m * k) :=
  (Equiv.prodCongr (cubeEnumeration m) (Equiv.refl (Fin k))).trans finProdFinEquiv

def registerVector {F : Type*} [Field F] [Algebra (ZMod 2) F] {m k : ℕ}
    (b : Module.Basis (Fin k) (ZMod 2) F) (h : (Fin m → Bool) → F) :
    Fin (2 ^ m * k) → ZMod 2 :=
  fun i => b.equivFun (h ((registerNumbering m k).symm i).1)
    ((registerNumbering m k).symm i).2

theorem registerVector_apply {F : Type*} [Field F] [Algebra (ZMod 2) F] {m k : ℕ}
    (b : Module.Basis (Fin k) (ZMod 2) F) (h : (Fin m → Bool) → F)
    (i : Fin (2 ^ m)) (j : Fin k) :
    registerVector b h (finProdFinEquiv (i, j)) =
      b.equivFun (h ((cubeEnumeration m).symm i)) j := by
  simp [registerVector, registerNumbering]

theorem registerVector_bits {F : Type*} [Field F] [Algebra (ZMod 2) F] {m k : ℕ}
    (b : Module.Basis (Fin k) (ZMod 2) F) (h : (Fin m → Bool) → F) :
    CL.toBits (registerVector b h) =
      (List.ofFn fun i : Fin (2 ^ m) =>
        vectorBits (b.equivFun (h ((cubeEnumeration m).symm i)))).flatten := by
  unfold CL.toBits vectorBits
  rw [CL.ofFn_eq_flatten_blocks]
  simp only [registerVector_apply]
  rfl

/-- This is precisely the coordinate projection used by binary Pauli measurements. -/
theorem registerVector_binEquiv {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} (b : Module.Basis (Fin k) (ZMod 2) F)
    (h : (Fin m → Bool) → F) :
    registerVector b h = fun i => Weyl.binEquiv b h ((registerNumbering m k).symm i) := rfl

abbrev Input := Unary × Unary × BitStr

/-- The validity flag and the full-register bits, in one polynomial-time program. -/
def program : PolyTimeFun Input (Bool × BitStr) :=
  (fst.comp fullPauliParserProg).pair
    (encodeBlocksProg.comp ((fst.comp snd).pair (snd.comp fullPauliParserProg)))

theorem program_answerBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (m d : ℕ) (h : (Fin m → Bool) → (shoupBinField k hk).carrier) :
    program (unary m, unary k,
      PauliAnswerProgram.answerBits (shoupBinField k hk) (.pauliAns (d := d) h)) =
      (true, CL.toBits (registerVector (shoupSelfDualNormalBasis k hk hodd) h)) := by
  simp only [program, pair_apply, comp_apply, fst_apply, snd_apply,
    PauliAnswerProgram.answerBits, PauliAnswerProgram.answerRows,
    fullPauliParserProg_vecBits _ hk, encodeBlocksProg_correct k hk hodd,
    registerVector_bits]

theorem program_valid (m k : Unary) (bs : BitStr) :
    (program (m, k, bs)).1 = true ↔ 0 < k.length ∧ bs.length = 2 ^ m.length * k.length :=
  fullPauliParserProg_valid m k bs

theorem program_runs (input : Input) :
    ∃ t ≤ program.timeBound.eval (esize input),
      program.code.Runs (encode input) (encode (program input)) t := program.computes input

end MIPRE.QLD.PauliFullAnswerProgram
end
