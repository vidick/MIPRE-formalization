/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryCyclotomicSeed
import MIPRE.Foundations.LowDegree.BinarySubstitution
import MIPRE.Foundations.LowDegree.BinaryExactDivision

/-!
# Bounded auxiliary root lifting

This is the specified program for the odd-prime auxiliary stage. It repeatedly
factors `f(X^q)`, retaining the current `f` once factorization returns at most one
factor. Nonterminal choices are clipped to the initial seed width, ensuring a
global runtime bound even on malformed inputs. The statements here establish
execution and size bounds; the nonresidue and termination correctness theorems
are separate algebraic obligations.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Exponent minus one in unary, coefficient cap, done flag, and current polynomial. -/
abbrev NonresidueState := Unary × Unary × Bool × BitStr

/-- Factor the positive-power substitution in the current candidate. -/
noncomputable def liftCandidates (s : NonresidueState) : List BitStr :=
  BinaryQuotient.factorBitsProg ((substitutePowerBits s.2.2.2 s.1).dropLast)

/-- One bounded root-lifting step, retaining the old polynomial at the stopping test. -/
noncomputable def nonresidueStep (s : NonresidueState) (_ : Bool) : NonresidueState :=
  if s.2.2.1 then s else
    if (liftCandidates s).tail.isEmpty then (s.1, s.2.1, true, s.2.2.2)
    else (s.1, s.2.1, false, ((liftCandidates s).headD []).take s.2.1.length)

/-- Stopping is absorbing, so padding the iteration budget is harmless. -/
theorem nonresidueStep_done (s : NonresidueState) (b : Bool) (hs : s.2.2.1 = true) :
    nonresidueStep s b = s := by simp [nonresidueStep, hs]

/-- Each step retains both external parameters and respects the original width cap. -/
theorem nonresidueStep_width (s : NonresidueState) (b : Bool) :
    (nonresidueStep s b).1 = s.1 ∧ (nonresidueStep s b).2.1 = s.2.1 ∧
    (nonresidueStep s b).2.2.2.length ≤ max s.2.2.2.length s.2.1.length := by
  unfold nonresidueStep
  split
  · exact ⟨rfl, rfl, le_max_left _ _⟩
  · split
    · exact ⟨rfl, rfl, le_max_left _ _⟩
    · exact ⟨rfl, rfl, (List.length_take_le _ _).trans (le_max_right _ _)⟩

/-- The complete loop retains metadata and never exceeds the initial maximum width. -/
theorem fold_nonresidueStep_width (l : BitStr) (s : NonresidueState) :
    (l.foldl nonresidueStep s).1 = s.1 ∧ (l.foldl nonresidueStep s).2.1 = s.2.1 ∧
    (l.foldl nonresidueStep s).2.2.2.length ≤ max s.2.2.2.length s.2.1.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl, le_max_left _ _⟩
  | cons b l ih =>
    obtain ⟨hq, hc, hf⟩ := nonresidueStep_width s b
    obtain ⟨hqi, hci, hfi⟩ := ih (nonresidueStep s b)
    refine ⟨hqi.trans hq, hci.trans hc, ?_⟩
    rw [hc] at hfi
    exact hfi.trans (max_le hf (le_max_right _ _))

private noncomputable def isEmptyProg : PolyTimeFun (List BitStr) Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

private noncomputable def liftCandidatesProg : PolyTimeFun NonresidueState (List BitStr) :=
  congr (BinaryQuotient.factorBitsProg.comp (dropLastBitsProg.comp
    (substitutePowerBitsProg.comp ((snd.comp (snd.comp snd)).pair fst))))
    liftCandidates (by intro s; rfl)

set_option maxHeartbeats 2000000 in
private noncomputable def nonresidueStepProg : PolyTimeFun (NonresidueState × Bool) NonresidueState :=
  let q := fst.comp fst
  let cap := fst.comp (snd.comp fst)
  let done := fst.comp (snd.comp (snd.comp fst))
  let f := snd.comp (snd.comp (snd.comp fst))
  let candidates := liftCandidatesProg.comp fst
  congr (ite done fst (ite (isEmptyProg.comp (PolyTimeFun.tail.comp candidates))
    (q.pair (cap.pair ((const true).pair f)))
    (q.pair (cap.pair ((const false).pair
      (take.comp (((PolyTimeFun.headD []).comp candidates).pair cap)))))))
    (fun s => nonresidueStep s.1 s.2) (by intro s; rfl)

private theorem nonresidueStepProg_apply (s : NonresidueState) (b : Bool) :
    nonresidueStepProg (s, b) = nonresidueStep s b := rfl

private theorem nonresidueStep_bounded : FoldBounded nonresidueStepProg (10 * X + 10) := by
  intro l s pre post _
  change esize (pre.foldl nonresidueStep s) ≤ _
  obtain ⟨hq, hc, hf⟩ := fold_nonresidueStep_width pre s
  have hsz := esize_bitStr_le (pre.foldl nonresidueStep s).2.2.2
  have hinit := length_le_esize_list s.2.2.2
  have hcap := length_le_esize_list s.2.1
  have hflag : esize (pre.foldl nonresidueStep s).2.2.1 ≤ 3 := by
    cases (pre.foldl nonresidueStep s).2.2.1 <;> decide
  have hs : esize s = esize s.1 + (esize s.2.1 +
    (esize s.2.2.1 + esize s.2.2.2 + 1) + 1) + 1 := rfl
  change esize (pre.foldl nonresidueStep s).1 + (esize (pre.foldl nonresidueStep s).2.1 +
    (esize (pre.foldl nonresidueStep s).2.2.1 + esize (pre.foldl nonresidueStep s).2.2.2 + 1) + 1) + 1 ≤ _
  rw [hq, hc]
  simp only [esize_prod, hs, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- Run the bounded lifting loop with explicitly supplied fuel and metadata. -/
noncomputable def nonresidueLoopProg : PolyTimeFun (BitStr × NonresidueState) NonresidueState :=
  foldl nonresidueStepProg (10 * X + 10) nonresidueStep_bounded

@[simp] theorem nonresidueLoopProg_apply (l : BitStr) (s : NonresidueState) :
    nonresidueLoopProg (l, s) = l.foldl nonresidueStep s := rfl

/-- The auxiliary root-lifting program initialized from the deterministic cyclotomic seed.
The initial seed degree supplies the iteration budget, and its full width supplies the cap. -/
noncomputable def nonresidueLiftStateProg : PolyTimeFun Unary NonresidueState :=
  let seed := cyclotomicSeedBitsProg
  nonresidueLoopProg.comp ((PolyTimeFun.tail.comp seed).pair
    (PolyTimeFun.tail.pair ((length.comp seed).pair ((const false).pair seed))))

/-- The retained binary polynomial from the bounded auxiliary construction. -/
noncomputable def nonresidueLiftBitsProg : PolyTimeFun Unary BitStr :=
  (snd.comp (snd.comp snd)).comp nonresidueLiftStateProg

end MIPRE.LowDegree.BinaryPolynomial
