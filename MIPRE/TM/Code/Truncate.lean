/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Code.Evaluator
import MIPRE.TM.MultiInput.Truncate

/-!
# Budgeted evaluation reads only a prefix of the inputs

A coded machine run for `T` steps reads no input cell beyond position `T`, so its budgeted
evaluation is unchanged when the inputs are altered past length `L ≥ T`
(`Code.evalWithin_congr_take`), in particular when they are truncated to that length
(`Code.evalWithin_take`). A universal machine whose time bound is independent of the inputs'
length relies on this to read them only up to a pad (`planning/universal-machine.md`, M2).
-/

namespace Turing.Code

variable {i : ℕ}

theorem bitInputs_take_eq (c : Code i) {x x' : Fin i → List Bool} {L : ℕ}
    (h : ∀ j, (x j).take L = (x' j).take L) (j : Fin i) :
    (c.bitInputs x j).take L = (c.bitInputs x' j).take L := by
  simp only [bitInputs, ← List.map_take, h j]

/-- **Budgeted evaluation is unchanged by altering the inputs past the budget.** -/
theorem evalWithin_congr_take (c : Code i) {x x' : Fin i → List Bool} {L T : ℕ}
    (h : ∀ j, (x j).take L = (x' j).take L) (hT : T ≤ L) :
    c.evalWithin x T = c.evalWithin x' T := by
  obtain ⟨hc, ho⟩ := MultiInputTM.configs_agree_of_take_eq (tm := c.toTM) L
    (c.bitInputs_take_eq h) hT
  unfold evalWithin runFor outputFor
  rw [hc.state, ho]

/-- **Budgeted evaluation on inputs truncated past the budget.** -/
theorem evalWithin_take (c : Code i) (x : Fin i → List Bool) {L T : ℕ} (hT : T ≤ L) :
    c.evalWithin (fun j => (x j).take L) T = c.evalWithin x T :=
  c.evalWithin_congr_take (fun j => List.take_take ▸ by simp) hT

end Turing.Code
