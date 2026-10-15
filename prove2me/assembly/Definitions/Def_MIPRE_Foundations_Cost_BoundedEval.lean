/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BoundedEval.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_count
import Theorems.Thm_MIPRE_Cost_Machine_stepData_toData

/-!
# Running a program under a cost budget, computably

`Machine.evalData` runs a program to completion and is only *partial* recursive; and
`Cost.evalWithin`, which reads off the result of a run within a budget, is `noncomputable` —
it picks a witness out of an existential with `Classical.choice`. Neither can be used to
*compute* anything, and the tabulation of a verifier's game (blueprint
`rem:compression-abstract`, item 3) has to compute: it runs the decider on every answer tuple
under the decider's own time bound and fills in an acceptance table.

`Machine.runForD p x k` is the computable version: iterate the machine's step function
`3 k` times from the initial configuration and read off the result if the configuration
reached is final. Three facts make it right:

* a derivation of cost `t` is a machine run of at most `3 t` steps
  (`Machine.eval_steps_count` — the free steps, entering a loop and returning to a `cons` or
  `let` frame, are each matched with a paid one), so the budget `3 k` is enough for every run
  of cost at most `k`;
* final configurations are fixed by the step function (`Machine.step_final`), so iterating
  past the end is harmless and no exact step count is needed;
* the step function is primitive recursive on the encoded configurations
  (`Machine.primrec_stepData`), so the whole is (`Machine.primrec_runForD`).

`runForD_eq_some` and `runs_of_runForD` are the two directions of its correctness, and
`runForD_isSome_iff` the decision procedure they add up to: **for a program that halts within
the budget on the input, whether it returns a given value is decidable**, which is what
boundedness buys the tabulation.
-/

namespace MIPRE.Cost

namespace Machine

/-- Finality of a configuration as a `Bool`, so that the budgeted run is a plain branch. -/
def isFinalB (d : Data) : Bool := decide (IsFinalD d)

@[simp] theorem isFinalB_iff (d : Data) : isFinalB d = true ↔ IsFinalD d := by
  simp [isFinalB]

theorem primrec_isFinalB : Primrec isFinalB := by
  obtain ⟨inst, h⟩ := primrec_isFinalD
  exact h.of_eq fun d => Bool.eq_iff_iff.2 (by simp [isFinalB])

/-- **Running `p` on `x` under a cost budget `k`**: iterate the step function `3 k` times and
read off the result if the configuration reached is final. Total and computable. -/
def runForD (pd x : Data) (k : ℕ) : Option Data :=
  let d := stepData^[3 * k] (initData pd x)
  if isFinalB d then some (resultD d) else none

theorem stepData_iterate (c : Cfg) (n : ℕ) : stepData^[n] c.toData = (step^[n] c).toData := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepData_toData, ih]

/-- **Completeness.** A run of cost at most the budget is found. -/
theorem runForD_eq_some {p : Prog} {x r : Data} {t k : ℕ} (h : p.Runs x r t) (hk : t ≤ k) :
    runForD (encode p) x k = some r := by
  obtain ⟨N, e, hs, hN⟩ := eval_steps_count h []
  obtain ⟨m, hm⟩ : ∃ m, 3 * k = m + N := ⟨3 * k - N, by omega⟩
  have hiter : step^[3 * k] (⟨.ev p, [x], []⟩ : Cfg) = ⟨.ret r, e, []⟩ := by
    rw [hm, Function.iterate_add_apply, hs.1, step_final]
  show (if isFinalB (stepData^[3 * k] (initData (encode p) x)) then _ else _) = _
  rw [show initData (encode p) x = (⟨.ev p, [x], []⟩ : Cfg).toData from initData_eq p x,
    stepData_iterate, hiter,
    if_pos ((isFinalB_iff _).2 ((isFinalD_toData _).2 ⟨r, e, rfl⟩)), resultD_toData]

/-! ## Computability -/

theorem primrec_runForD : Primrec fun q : (Data × Data) × ℕ => runForD q.1.1 q.1.2 q.2 := by
  have hinit : Primrec fun q : (Data × Data) × ℕ => initData q.1.1 q.1.2 :=
    primrec_initData.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hiter : Primrec fun q : (Data × Data) × ℕ =>
      stepData^[3 * q.2] (initData q.1.1 q.1.2) :=
    Primrec.nat_iterate (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd) hinit
      (primrec_stepData.comp Primrec.snd).to₂
  have hfin : PrimrecPred fun q : (Data × Data) × ℕ =>
      isFinalB (stepData^[3 * q.2] (initData q.1.1 q.1.2)) = true :=
    ⟨inferInstance, (primrec_isFinalB.comp hiter).of_eq fun q => Bool.eq_iff_iff.2 (by simp)⟩
  exact Primrec.ite hfin (Primrec.option_some.comp (primrec_resultD.comp hiter))
    (Primrec.const none)

end Machine

end MIPRE.Cost
