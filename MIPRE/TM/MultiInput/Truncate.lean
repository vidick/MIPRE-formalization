/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.MultiInput.Complexity

/-!
# A run does not see past its own length on the input tapes

An input head starts at position `1` and moves by at most one cell per step, so in its first
`t` steps a machine reads no input cell beyond position `t`. Hence two input tuples that agree
up to length `L` give runs that agree for `L` steps: the same states, work tapes, head
positions and emitted symbols (`MultiInputTM.configs_agree_of_take_eq`). The consequence used
by the universal machines (`planning/universal-machine.md`, milestone M2) is that a machine run
for `T ≤ L` steps computes the same on the inputs truncated to length `L`
(`MultiInputTM.computesInTimeAndSpace_take_iff`): this is what lets a universal machine with a
time bound independent of the inputs' length read them only up to a pad.
-/

namespace Turing.MultiInputTM

open MultiTapeTM (moveInputPos)

variable {i w : ℕ} {Symbol State : Type*} {tm : MultiInputTM i w Symbol State}
  {input input' : Fin i → List Symbol}

/-- The symbol under an input head, as an optional list lookup. -/
theorem Cfg.inputSymbol_eq_getElem? (cfg : Cfg i w Symbol State input) (j : Fin i) :
    cfg.inputSymbol j =
      if (cfg.inputPos j).val = 0 then none else (input j)[(cfg.inputPos j).val - 1]? := by
  unfold Cfg.inputSymbol
  by_cases h₁ : cfg.inputPos j = 0
  · simp [h₁]
  · have h₁' : (cfg.inputPos j).val ≠ 0 := fun h => h₁ (Fin.ext h)
    rw [dif_neg h₁, if_neg h₁']
    by_cases h₂ : (cfg.inputPos j).val = (input j).length + 1
    · rw [dif_pos h₂, h₂]
      simp
    · have hlt := (cfg.inputPos j).isLt
      rw [dif_neg h₂, List.getElem?_eq_getElem (by omega)]

theorem toNat_add_cast_le (p : ℕ) (m : SignType) : ((p : ℤ) + (m.cast : ℤ)).toNat ≤ p + 1 := by
  rcases m with _ | _ | _ <;> simp [SignType.cast]

/-- An input head moves by at most one cell. -/
theorem moveInputPos_val_le {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    (moveInputPos pos m).val ≤ pos.val + 1 := by
  have := toNat_add_cast_le pos.val m
  simp only [moveInputPos]
  split
  · exact this
  · simp only
    omega

/-- Head movement does not depend on the tape length, away from the right end. -/
theorem moveInputPos_val_eq {n n' : ℕ} (pos : Fin (n + 2)) (pos' : Fin (n' + 2))
    (h : pos.val = pos'.val) (hlen : n = n' ∨ (pos.val ≤ n ∧ pos'.val ≤ n')) (m : SignType) :
    (moveInputPos pos m).val = (moveInputPos pos' m).val := by
  rcases hlen with rfl | ⟨hn, hn'⟩
  · rw [Fin.ext h]
  · have h1 := toNat_add_cast_le pos.val m
    have h2 := toNat_add_cast_le pos'.val m
    simp only [moveInputPos]
    rw [dif_pos (by omega), dif_pos (by omega)]
    simp [h]

/-- Two configurations over different inputs agree: same state, work tapes, work heads, and
input heads at the same positions. -/
structure Agree (c : Cfg i w Symbol State input) (c' : Cfg i w Symbol State input') : Prop where
  state : c.state = c'.state
  workTapes : c.workTapes = c'.workTapes
  workTapePos : c.workTapePos = c'.workTapePos
  inputPos : ∀ j, (c.inputPos j).val = (c'.inputPos j).val

variable (L : ℕ) (hL : ∀ j, (input j).take L = (input' j).take L)
include hL

omit hL in
theorem getElem?_eq_of_take_eq {l l' : List Symbol} (h : l.take L = l'.take L) {k : ℕ}
    (hk : k < L) : l[k]? = l'[k]? := by
  rw [← List.getElem?_take_of_lt hk, h, List.getElem?_take_of_lt hk]

theorem inputSymbols_eq_of_agree {c : Cfg i w Symbol State input}
    {c' : Cfg i w Symbol State input'} (hc : Agree c c') (hpos : ∀ j, (c.inputPos j).val ≤ L) :
    c.inputSymbols = c'.inputSymbols := by
  funext j
  simp only [Cfg.inputSymbols_apply, Cfg.inputSymbol_eq_getElem?, ← hc.inputPos j]
  split_ifs with h
  · rfl
  · exact getElem?_eq_of_take_eq L (hL j) (by have := hpos j; omega)

theorem length_eq_or_le_of_take_eq (j : Fin i) :
    (input j).length = (input' j).length ∨ (L ≤ (input j).length ∧ L ≤ (input' j).length) := by
  have h := congrArg List.length (hL j)
  simp only [List.length_take] at h
  omega

/-- **One step preserves agreement**, while the input heads stay within the common prefix. -/
theorem agree_step {c : Cfg i w Symbol State input} {c' : Cfg i w Symbol State input'}
    (hc : Agree c c') (hpos : ∀ j, (c.inputPos j).val ≤ L) :
    Agree (tm.step c) (tm.step c') ∧ tm.outputSymbol c = tm.outputSymbol c' := by
  have hsym := inputSymbols_eq_of_agree L hL hc hpos
  have hws : c.workTapeSymbols = c'.workTapeSymbols := by
    funext d
    simp [Cfg.workTapeSymbols, hc.workTapes, hc.workTapePos]
  cases hs : c.state with
  | none =>
    have hs' : c'.state = none := hc.state ▸ hs
    rw [step_of_halt hs, step_of_halt hs', outputSymbol, outputSymbol, hs, hs']
    exact ⟨hc, rfl⟩
  | some q =>
    have hs' : c'.state = some q := hc.state ▸ hs
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [step, hs, hs', hsym, hws]
    · funext d
      simp [step, hs, hs', hsym, hws, hc.workTapes, hc.workTapePos]
    · funext d
      simp [step, hs, hs', hsym, hws, hc.workTapePos]
    · intro j
      simp only [step, hs, hs', hsym, hws]
      have hp := hc.inputPos j
      have hb := hpos j
      refine moveInputPos_val_eq _ _ hp ?_ _
      rcases length_eq_or_le_of_take_eq L hL j with hlen | ⟨hl, hl'⟩
      · exact Or.inl hlen
      · exact Or.inr ⟨by omega, by omega⟩
    · simp [outputSymbol, hs, hs', hsym, hws]

omit hL in
theorem initCfg_agree : Agree (tm.initCfg input) (tm.initCfg input') :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

omit hL in
theorem inputPos_step_le (c : Cfg i w Symbol State input) (j : Fin i) :
    ((tm.step c).inputPos j).val ≤ (c.inputPos j).val + 1 := by
  unfold step
  split
  · omega
  · exact moveInputPos_val_le _ _

omit hL in
theorem inputPos_configs_le (t : ℕ) (j : Fin i) :
    ((tm.configs (tm.initCfg input) t).inputPos j).val ≤ t + 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [configs_succ_eq_step']
    exact (inputPos_step_le _ j).trans (by omega)

/-- **Runs on inputs agreeing up to length `L` agree for `L` steps.** -/
theorem configs_agree_of_take_eq {t : ℕ} (ht : t ≤ L) :
    Agree (tm.configs (tm.initCfg input) t) (tm.configs (tm.initCfg input') t) ∧
      tm.outputString (tm.initCfg input) t = tm.outputString (tm.initCfg input') t := by
  induction t with
  | zero => exact ⟨initCfg_agree, by simp [outputString]⟩
  | succ t ih =>
    obtain ⟨hc, ho⟩ := ih (by omega)
    have hpos : ∀ j, ((tm.configs (tm.initCfg input) t).inputPos j).val ≤ L :=
      fun j => by have := inputPos_configs_le (tm := tm) (input := input) t j; omega
    obtain ⟨hc', hout⟩ := agree_step L hL hc hpos
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', configs_succ_eq_step']
      exact hc'
    · rw [outputString_succ, outputString_succ, ho, hout]

theorem spaceUsed_eq_of_take_eq {t : ℕ} (ht : t ≤ L) :
    tm.spaceUsed (tm.initCfg input) t = tm.spaceUsed (tm.initCfg input') t := by
  unfold spaceUsed spaceUsedByTape visitedByTapeHead
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  refine Finset.image_congr fun t' ht' => ?_
  have ht'' : t' ≤ L := by simp only [Finset.coe_range, Set.mem_Iio] at ht'; omega
  simp only [(configs_agree_of_take_eq L hL (tm := tm) ht'').1.workTapePos]

/-- **A computation of length at most `L` is unchanged by altering the inputs past `L`.** -/
theorem computesInTimeAndSpace_take_iff (output : List Symbol) {t s : ℕ} (ht : t ≤ L) :
    tm.ComputesInTimeAndSpace input output t s ↔
      tm.ComputesInTimeAndSpace input' output t s := by
  obtain ⟨hc, ho⟩ := configs_agree_of_take_eq L hL (tm := tm) ht
  unfold ComputesInTimeAndSpace
  rw [hc.state, ho, spaceUsed_eq_of_take_eq L hL ht]

end Turing.MultiInputTM
