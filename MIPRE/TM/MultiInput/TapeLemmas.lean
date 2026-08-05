/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.MultiInput.Deterministic

/-!
# Tape head visitation and space-usage lemmas for multi-input machines

This file collects lemmas about the set of positions visited by a work-tape head
(`MultiInputTM.visitedByTapeHead`) and the resulting space-usage measures
(`MultiInputTM.spaceUsedByTape`, `MultiInputTM.spaceUsed`) and how the tape head positions
influence the cells that are modified on a tape.

It is the multi-input counterpart, lemma for lemma, of the vendored CSLib file
`MIPRE.Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas`.
-/

namespace Turing.MultiInputTM

variable {i w : ℕ}
variable {State Symbol : Type*}
variable {input : Fin i → List Symbol}
variable {tm : MultiInputTM i w Symbol State}
variable {cfg : Cfg i w Symbol State input}

/-- If the head of work tape `d` is not at position `z`, then the tape does not change
there. -/
lemma step_workTapes_eq_of_ne
    (cfg : Cfg i w Symbol State input)
    (d : Fin w)
    (z : ℤ)
    (hz : z ≠ cfg.workTapePos d) :
    (tm.step cfg).workTapes d z = cfg.workTapes d z := by
  unfold step
  cases hst : cfg.state with
  | none => simp_all
  | some q =>
    rcases hw : ((tm.tr q cfg.inputSymbols cfg.workTapeSymbols).workActions d).1 <;>
      simp_all

lemma mem_visitedByTapeHead {t : ℕ} {d : Fin w} {z : ℤ} :
    z ∈ tm.visitedByTapeHead cfg t d ↔
      ∃ t' < t + 1, (tm.configs cfg t').workTapePos d = z := by
  simp [visitedByTapeHead]

lemma mem_visitedByTapeHead_self (cfg : Cfg i w Symbol State input) (t : ℕ) (d : Fin w) :
    (tm.configs cfg t).workTapePos d ∈ tm.visitedByTapeHead cfg t d :=
  tm.mem_visitedByTapeHead.mpr ⟨t, by omega, rfl⟩

/-- The set of positions visited by a tape head is monotone in the number of steps. -/
lemma visitedByTapeHead_mono (cfg : Cfg i w Symbol State input) (d : Fin w) {t t' : ℕ}
    (h : t ≤ t') :
    tm.visitedByTapeHead cfg t d ⊆ tm.visitedByTapeHead cfg t' d := by
  apply Finset.image_subset_image
  grind

/-- Starting from configuration `cfg`, every position between the initial head position of
tape `d` and the one after `t` steps is part of the "visited set" at step `t`. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead
    (cfg : Cfg i w Symbol State input) (d : Fin w) (t : ℕ) :
    Finset.uIcc (cfg.workTapePos d) ((tm.configs cfg t).workTapePos d)
      ⊆ tm.visitedByTapeHead cfg t d := by
  induction t with
  | zero => simpa [configs] using tm.mem_visitedByTapeHead_self cfg 0 d
  | succ t ih =>
    intro z hz
    have hstep :
        |(tm.configs cfg (t + 1)).workTapePos d - (tm.configs cfg t).workTapePos d| ≤ 1 :=
      configs_succ_eq_step' (tm := tm) ▸ tm.workTapePos_step_le _ d
    have hmono := tm.visitedByTapeHead_mono cfg d (Nat.le_succ t)
    have hself := tm.mem_visitedByTapeHead_self cfg (t + 1) d
    grind [Finset.mem_uIcc]

/-- If a work tape cell is changed after `t` steps, it must have been visited by the tape
head. -/
lemma mem_visitedByTapeHead_of_workTapes_ne
    (d : Fin w)
    (t : ℕ)
    (z : ℤ)
    (h : (tm.configs cfg t).workTapes d z ≠ cfg.workTapes d z) :
    z ∈ tm.visitedByTapeHead cfg t d := by
  induction t with
  | zero => exact absurd (by simp [configs]) h
  | succ t ih =>
    rw [configs_succ_eq_step'] at h
    by_cases hz : z = (tm.configs cfg t).workTapePos d
    · exact hz ▸ tm.visitedByTapeHead_mono cfg d (Nat.le_succ t)
        (tm.mem_visitedByTapeHead_self cfg t d)
    · rw [tm.step_workTapes_eq_of_ne _ d z hz] at h
      exact tm.visitedByTapeHead_mono cfg d (Nat.le_succ t) (ih h)

/-- Every position visited by the head of tape `d` lies within `spaceUsedByTape … d` of
the head's starting position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited
    {d : Fin w}
    {z : ℤ}
    {t : ℕ}
    (hz : z ∈ tm.visitedByTapeHead cfg t d) :
    (z - cfg.workTapePos d).natAbs ≤ tm.spaceUsedByTape cfg t d := by
  obtain ⟨t', ht', rfl⟩ := tm.mem_visitedByTapeHead.mp hz
  have h1 := Finset.card_le_card
    ((tm.uIcc_workTapePos_subset_visitedByTapeHead cfg d t').trans
      (tm.visitedByTapeHead_mono cfg d (show t' ≤ t by omega)))
  rw [Int.card_uIcc] at h1
  unfold spaceUsedByTape
  omega

/-- Every non-blank cell on work tape `d` lies within `spaceUsedByTape … d t` of the
origin. -/
lemma content_natAbs_le_spaceUsedByTape
    {d : Fin w}
    (t : ℕ)
    (z : ℤ)
    (h : (tm.configs (tm.initCfg input) t).workTapes d z ≠ none) :
    z.natAbs ≤ tm.spaceUsedByTape (tm.initCfg input) t d := by
  -- The work tapes start out blank, so any non-blank cell has been visited by the head;
  -- the initial head position is `0`, so the displacement bound is a bound on the
  -- position itself.
  simpa using tm.natAbs_le_spaceUsedByTape_of_mem_visited
    (tm.mem_visitedByTapeHead_of_workTapes_ne d t z h)

/-- The number of cells touched by a single work tape grows by at most one each step. -/
lemma spaceUsedByTape_le (cfg : Cfg i w Symbol State input) (t : ℕ) (d : Fin w) :
    tm.spaceUsedByTape cfg t d ≤ t + 1 := by
  calc
    tm.spaceUsedByTape cfg t d
    _ ≤ (Finset.range (t + 1)).card := Finset.card_image_le
    _ = t + 1 := Finset.card_range _

/-- The space used by a computation is bounded linearly by the number of steps. -/
lemma spaceUsed_linear (cfg : Cfg i w Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t ≤ w * t + w := by
  calc tm.spaceUsed cfg t
      = ∑ d, (tm.spaceUsedByTape cfg t d) := by rfl
    _ ≤ ∑ _d : Fin w, (t + 1) := Finset.sum_le_sum (fun d _ => tm.spaceUsedByTape_le cfg t d)
    _ = w * t + w := by simp [Nat.mul_succ]

/-- The space used by a single tape is monotone in the number of steps. -/
lemma spaceUsedByTape_mono
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input)
    (d : Fin w) :
    Monotone (tm.spaceUsedByTape cfg · d) := by
  intro t t' h
  exact Finset.card_le_card (tm.visitedByTapeHead_mono cfg d h)

/-- The total space used is monotone in the number of steps. -/
lemma spaceUsed_mono (tm : MultiInputTM i w Symbol State) (cfg : Cfg i w Symbol State input) :
    Monotone (tm.spaceUsed cfg ·) := by
  intro t t' h
  exact Finset.sum_le_sum (fun d _ => spaceUsedByTape_mono tm cfg d h)

end Turing.MultiInputTM
