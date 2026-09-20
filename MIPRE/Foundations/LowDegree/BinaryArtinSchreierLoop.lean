/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryArtinSchreierTower
import MIPRE.Foundations.LowDegree.BinaryGCD

/-!
# The bounded power-of-two constructor

The input is the requested degree in unary. The loop caps all intermediate
moduli by this input degree, including on malformed states. The unbounded
mathematical stage sequence below is used only to state the induction proof.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryArtinSchreier

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- The mathematical sequence used to prove the bounded loop correct. -/
def stage : ℕ → BitStr
  | 0 => [true, true]
  | t + 1 => (towerStepBits (stage t)).dropLast

theorem stage_invariant (t : ℕ) : TowerInvariant (stage t) t := by
  induction t with
  | zero => exact initial_invariant
  | succ t ih => exact towerStep_invariant _ _ ih

/-- Target degree in unary and the current lower coefficients. -/
abbrev TowerState := Unary × BitStr

/-- Grow only below the target, and cap every replacement by the target width. -/
def cappedStep (s : TowerState) : TowerState :=
  if (s.1.drop s.2.length).isEmpty then s
  else (s.1, (towerStepBits s.2).dropLast.take s.1.length)

private def isEmptyUnaryProg : PolyTimeFun Unary Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

/-- One uniform capped step, including its unary stopping test. -/
def cappedStepProg : PolyTimeFun TowerState TowerState :=
  congr (ite (isEmptyUnaryProg.comp (drop.comp (fst.pair (length.comp snd)))) (PolyTimeFun.id _)
    (fst.pair (take.comp ((dropLastBitsProg.comp (towerStepBitsProg.comp snd)).pair fst))))
    cappedStep (by
      intro s
      change (if (s.1.drop (unary s.2.length).length).isEmpty then s else
        (s.1, (towerStepBits s.2).dropLast.take s.1.length)) = _
      rw [length_unary]
      rfl)

@[simp] theorem cappedStepProg_apply (s : TowerState) : cappedStepProg s = cappedStep s := rfl

private theorem cappedStep_width (s : TowerState) :
    (cappedStep s).1 = s.1 ∧ (cappedStep s).2.length ≤ max s.2.length s.1.length := by
  unfold cappedStep
  split
  · exact ⟨rfl, le_max_left _ _⟩
  · exact ⟨rfl, (List.length_take_le _ _).trans (le_max_right _ _)⟩

private theorem fold_cappedStep_width (u : Unary) (s : TowerState) :
    (u.foldl (fun s _ => cappedStep s) s).1 = s.1 ∧
      (u.foldl (fun s _ => cappedStep s) s).2.length ≤ max s.2.length s.1.length := by
  induction u generalizing s with
  | nil => exact ⟨rfl, le_max_left _ _⟩
  | cons x u ih =>
    obtain ⟨hc, hw⟩ := cappedStep_width s
    obtain ⟨hci, hwi⟩ := ih (cappedStep s)
    refine ⟨hci.trans hc, ?_⟩
    rw [hc] at hwi
    exact hwi.trans (max_le hw (le_max_right _ _))

private theorem cappedStep_bounded : FoldBounded (cappedStepProg.comp (fst : PolyTimeFun (TowerState × Unit) TowerState)) (6 * X + 6) := by
  intro u s pre post _
  change esize (pre.foldl (fun s _ => cappedStep s) s) ≤ _
  obtain ⟨hc, hw⟩ := fold_cappedStep_width pre s
  have he := esize_bitStr_le (pre.foldl (fun s _ => cappedStep s) s).2
  have hp := length_le_esize_bitStr s.2
  have hu := length_le_esize_list s.1
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hc]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- Run a polynomially bounded number of capped tower steps. -/
def towerLoopProg : PolyTimeFun (Unary × TowerState) TowerState :=
  foldl (cappedStepProg.comp fst) (6 * X + 6) cappedStep_bounded

@[simp] theorem towerLoopProg_apply (u : Unary) (s : TowerState) :
    towerLoopProg (u, s) = u.foldl (fun s _ => cappedStep s) s := rfl

private theorem fold_cappedStep (u : Unary) (s : TowerState) :
    u.foldl (fun s _ => cappedStep s) s = cappedStep^[u.length] s := by
  induction u generalizing s with
  | nil => rfl
  | cons x u ih =>
    rw [List.foldl_cons, ih, List.length_cons, Function.iterate_succ_apply]

/-- Return the degree-one polynomial for unary zero or one, otherwise run the capped tower. -/
def powerTwoBits (u : Unary) : BitStr :=
  if u.tail.isEmpty then [false, true]
  else (u.foldl (fun s _ => cappedStep s) (u, [true, true])).2 ++ [true]

/-- A fixed ambient polynomial-time program on the requested degree, not its logarithm. -/
def powerTwoBitsProg : PolyTimeFun Unary BitStr :=
  ite (isEmptyUnaryProg.comp tail) (const [false, true])
    (append.comp ((snd.comp (towerLoopProg.comp
      ((PolyTimeFun.id _).pair ((PolyTimeFun.id _).pair (const [true, true]))))).pair (const [true])))

@[simp] theorem powerTwoBitsProg_apply (u : Unary) : powerTwoBitsProg u = powerTwoBits u := rfl

private theorem cappedStep_stage (u : Unary) (t : ℕ) (h : 2 ^ (t + 1 + 1) ≤ u.length) :
    cappedStep (u, stage t) = (u, stage (t + 1)) := by
  have hw := (stage_invariant t).width
  have hn := Nat.two_pow_pos (t + 1)
  have hg : (stage t).length < u.length := by
    rw [pow_succ] at h
    omega
  have hb : (u.drop (stage t).length).isEmpty = false := by
    cases he : u.drop (stage t).length with
    | nil =>
      have hh := congrArg List.length he
      simp only [List.length_drop, List.length_nil] at hh
      omega
    | cons x xs => rfl
  simp only [cappedStep, hb, Bool.false_eq_true, ↓reduceIte]
  change (u, (stage (t + 1)).take u.length) = (u, stage (t + 1))
  rw [List.take_of_length_le (by rw [(stage_invariant (t + 1)).width]; exact h)]

private theorem iterate_cappedStep_stage (u : Unary) (t : ℕ)
    (h : 2 ^ (t + 1) ≤ u.length) :
    cappedStep^[t] (u, [true, true]) = (u, stage t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp : 2 ^ (t + 1) ≤ u.length := by
      rw [pow_succ] at h
      omega
    rw [Function.iterate_succ_apply', ih hp]
    exact cappedStep_stage u t h

private theorem cappedStep_stage_fixed (u : Unary) (t : ℕ) (h : u.length = 2 ^ (t + 1)) :
    cappedStep (u, stage t) = (u, stage t) := by
  simp [cappedStep, (stage_invariant t).width, ← h]

private theorem iterate_cappedStep_finished (u : Unary) (t : ℕ) (h : u.length = 2 ^ (t + 1)) :
    cappedStep^[u.length] (u, [true, true]) = (u, stage t) := by
  have ht : t ≤ u.length := by
    rw [h]
    have hn := (t + 1).lt_two_pow_self
    omega
  have hinit := iterate_cappedStep_stage u t h.ge
  have hfixed := cappedStep_stage_fixed u t h
  have hrepeat (k : ℕ) : cappedStep^[k] (u, stage t) = (u, stage t) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hfixed, ih]
  rw [show u.length = (u.length - t) + t by omega, Function.iterate_add_apply, hinit]
  exact hrepeat _

/-- The complete constructor returns the chosen stage on every positive tower level. -/
theorem powerTwoBits_succ (t : ℕ) :
    powerTwoBits (unary (2 ^ (t + 1))) = stage t ++ [true] := by
  let u := unary (2 ^ (t + 1))
  have hu : u.length = 2 ^ (t + 1) := length_unary _
  have hpos : 1 < u.length := by rw [hu]; exact Nat.one_lt_pow (by omega) (by decide)
  have hb : u.tail.isEmpty = false := by
    cases he : u.tail with
    | nil =>
      have hh := congrArg List.length he
      simp only [List.length_tail, List.length_nil] at hh
      omega
    | cons x xs => rfl
  change (if u.tail.isEmpty then _ else _) = _
  rw [hb]
  change (u.foldl (fun s _ => cappedStep s) (u, [true, true])).2 ++ [true] = _
  rw [fold_cappedStep, iterate_cappedStep_finished u t hu]

/-- Every output is in canonical nonzero coefficient form. -/
theorem powerTwoBits_getLast (u : Unary) : (powerTwoBits u).getLastD false = true := by
  unfold powerTwoBits
  split <;> simp

/-- The globally polynomial-time program constructs a monic irreducible binary
polynomial of every requested power-of-two degree, including degree one. -/
theorem powerTwoBits_correct (e : ℕ) :
    (polyOfBits (powerTwoBits (unary (2 ^ e)))).Monic ∧
      Irreducible (polyOfBits (powerTwoBits (unary (2 ^ e)))) ∧
      (polyOfBits (powerTwoBits (unary (2 ^ e)))).natDegree = 2 ^ e := by
  cases e with
  | zero =>
    have hp : polyOfBits (powerTwoBits (unary (2 ^ 0))) = (X : (ZMod 2)[X]) := by
      change polyOfBits [false, true] = X
      simp only [polyOfBits_cons, show polyOfBits [] = 0 from rfl, ofBool,
        Bool.false_eq_true, ↓reduceIte, C_0, C_1, mul_zero, add_zero, mul_one, zero_add]
    rw [hp]
    exact ⟨monic_X, irreducible_X, by simp⟩
  | succ t =>
    rw [powerTwoBits_succ]
    exact ⟨monic_polyOfBits_append_true _, (stage_invariant t).irreducible,
      (natDegree_polyOfBits_append_true _).trans (stage_invariant t).width⟩

/-- The printed canonical coefficient list has the expected size. -/
theorem powerTwoBits_length (e : ℕ) :
    (powerTwoBits (unary (2 ^ e))).length = 2 ^ e + 1 := by
  rw [← natDegree_add_one_of_getLast _ (powerTwoBits_getLast _), (powerTwoBits_correct e).2.2]

end MIPRE.LowDegree.BinaryArtinSchreier

end