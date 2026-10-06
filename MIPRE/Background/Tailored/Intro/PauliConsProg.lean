/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Typed

@[expose] public section

/-!
# Programs for the Pauli clauses of the tailored introspection verifier

The `Z`-basis guard of `Typed.pauliDir` compares the kernel's projection of the readable `Z`
answer with a register of the Sample answer. `zGuardProg` decides it in polynomial time from
the kernel's parameter triple, the readable answer and the register: it runs the kernel's full
answer program (`QLD.PauliBinaryProgram.fullAnswer`), whose second output is the projection's
bits, and compares them with the register cut or padded to the same length.
`zGuardProg_eq` is its correctness at answers of the label's length.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.PauliConsProg

open Cost Cost.PolyTimeFun MIPRE.SAT MIPRE.Introspection MIPRE.QLD

/-- A bit string cut or padded with zeros to the length of a reference string. -/
def fitTo : PolyTimeFun (BitStr × BitStr) BitStr :=
  Cost.PolyTimeFun.take.comp ((append.comp (snd.pair (replicate.comp
    ((length.comp fst).pair (const false))))).pair (length.comp fst))

theorem fitTo_apply (r z : BitStr) :
    fitTo (r, z) = (z ++ List.replicate r.length false).take r.length := by
  simp [fitTo]

theorem toBits_ofBits_eq_fit (s : ℕ) (z : BitStr) :
    CL.toBits (CL.ofBits s z) = (z ++ List.replicate s false).take s := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [CL.toBits, CL.ofBits, List.getElem_ofFn, List.getElem_take,
    List.getD_eq_getElem?_getD]
  by_cases hi : i < z.length
  · simp only [List.getElem?_eq_getElem hi, List.getElem_append_left hi, Option.getD_some]
    cases z[i] <;> decide
  · simp [List.getElem?_eq_none (show z.length ≤ i by omega),
      List.getElem_append_right (show z.length ≤ i by omega)]

/-- **The `Z`-basis guard**: the projection of the readable `Z` answer is the register. -/
def zGuardProg : PolyTimeFun (PauliSamplerParameters.Parameters × BitStr × BitStr) Bool :=
  ap₂ ArrayProg.eqBits (snd.comp (PauliBinaryProgram.fullAnswer.comp (fst.pair (fst.comp snd))))
    (fitTo.comp ((snd.comp (PauliBinaryProgram.fullAnswer.comp (fst.pair (fst.comp snd)))).pair
      (snd.comp snd)))

/-- **The `Z`-basis guard is decided by `zGuardProg`**, at readable answers of the label's
length. -/
theorem zGuardProg_eq (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (aR z : BitStr)
    (ha : aR.length = pauliLen (2 ^ j) k (.pauli .Z)) :
    zGuardProg ((unary k, unary j, unary (2 ^ j)), aR, z) =
      decide (Typed.proj k hk hodd j (Typed.pDec k hk j (.pauli .Z) aR) =
        CL.ofBits (Typed.Q k j) z) := by
  have hv := (PauliCons.parser_iff_length k hk (.pauli .Z) (2 ^ j) aR).2 ha
  have hraw := DecisionKernel.Answer.rawProject_pauliDecode k hk hodd j (2 ^ j) .Z aR hv
  have hfa := PauliBinaryProgram.fullAnswer_apply (unary k) (unary j) (unary (2 ^ j)) aR
  rw [PauliFullAnswerProgram.program_raw k hk hodd (2 ^ j) .Z aR hv] at hfa
  rw [DecisionKernel.Answer.rawProject, hfa, CL.ofBits_toBits] at hraw
  simp only [zGuardProg, ap₂_apply, comp_apply, pair_apply, fst_apply, snd_apply, hfa,
    fitTo_apply, ArrayProg.eqBits_apply, CL.length_toBits]
  rw [← toBits_ofBits_eq_fit, Typed.proj, Typed.pDec, ← hraw]
  apply decide_eq_decide.2
  constructor
  · intro h
    have := congrArg (CL.ofBits (2 ^ 2 ^ j * k)) h
    simpa only [CL.ofBits_toBits] using this
  · intro h
    rw [h]

end MIPRE.Tailored.Intro.PauliConsProg

end

end
