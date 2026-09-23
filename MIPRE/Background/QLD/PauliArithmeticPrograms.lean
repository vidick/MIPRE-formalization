/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.Game
import MIPRE.Foundations.Introspection.FieldLineCheckProg
import MIPRE.Foundations.Introspection.FieldTableProg
import MIPRE.Foundations.Introspection.FieldGammaProg

/-! # Exact arithmetic programs for the Pauli decision rules

These bridges identify the uniform field programs with the existing game
predicates. In particular the line test retains geometric membership, the
full-answer test evaluates at arbitrary field points, and the commutation
bit uses the entire tuple of the endpoint prescribed by the rule.
-/

noncomputable section
namespace MIPRE.QLD.PauliArithmeticProgram
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear
  Introspection.FieldLineCheck Introspection.FieldTableProgram
  Introspection.FieldGammaProgram

theorem parameter_eq_lineParam {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} (origin direction point : Fin m → F) :
    parameter origin direction point = LIDT.CL.lineParam origin direction point :=
  parameter_eq origin direction point

/-- The executable coefficient/membership check is exactly the Pauli line rule. -/
theorem lineCheckProg_eq_lowDeg (k : ℕ) (hk : 1 ≤ k) {m n : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier)
    (f : LIDT.LinePoly (shoupBinField k hk).carrier n)
    (a : (shoupBinField k hk).carrier) :
    lineCheckProg ((unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point),
      (shoupBinField k hk).vecBits f, (shoupBinField k hk).toBits a) =
      lowDeg origin direction point f a := by
  apply Bool.eq_iff_iff.mpr
  rw [lineCheckProg_correct]
  simp only [lowDeg, LIDT.CL.lineVsPoint, decide_eq_true_eq,
    LIDT.LinePoly.eval, parameter_eq_lineParam]
  simp

/-- Canonical full Pauli rows follow the repository's binary cube order. -/
def answerRows {k m : ℕ} (E : BinField k) (h : (Fin m → Bool) → E.carrier) : List BitStr :=
  E.vecBits (fun i : Fin (2 ^ m) => h ((cubeEnumeration m).symm i))

/-- Width, queried point, full answer rows, and claimed point value. -/
def fullAnswerCheckProg : PolyTimeFun
    ((Unary × List BitStr × List BitStr) × BitStr) Bool :=
  ArrayProg.eqBits.comp ((tableProg.comp fst).pair snd)

theorem fullAnswerCheckProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (point : Fin m → (shoupBinField k hk).carrier)
    (h : (Fin m → Bool) → (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    fullAnswerCheckProg ((unary k, (shoupBinField k hk).vecBits point,
      answerRows (shoupBinField k hk) h), (shoupBinField k hk).toBits a) =
      decide (MvPolynomial.eval point (LowDegree.ldEnc h) = a) := by
  have hi : Function.Injective (shoupBinField k hk).toBits := by
    intro x y he
    simpa only [(shoupBinField k hk).ofBits_toBits] using
      congrArg (shoupBinField k hk).ofBits he
  simp only [fullAnswerCheckProg, comp_apply, pair_apply, fst_apply, snd_apply,
    answerRows, BinField.vecBits, List.map_ofFn, Function.comp_def,
    tableProg_correct, ArrayProg.eqBits_apply, hi.eq_iff]

/-- The trace probe used by rules five and seven. -/
theorem probeProg_eq_prb (k : ℕ) (hk : 1 ≤ k)
    (a r : (shoupBinField k hk).carrier) :
    probeProg (unary k, (shoupBinField k hk).toBits a, (shoupBinField k hk).toBits r) =
      bit (prb a r) := probeProg_correct k hk a r

/-- The trace commutation bit used by rules four through seven. -/
theorem gammaProg_eq_gam (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (ω : Omega (shoupBinField k hk).carrier m) :
    gammaProg (unary k,
      List.ofFn (fun i => ((shoupBinField k hk).toBits (ω.uX i),
        (shoupBinField k hk).toBits (ω.uZ i))),
      (shoupBinField k hk).toBits ω.rX, (shoupBinField k hk).toBits ω.rZ) =
      bit (gam ω) := gammaProg_correct k hk ω.uX ω.uZ ω.rX ω.rZ

end MIPRE.QLD.PauliArithmeticProgram
end
