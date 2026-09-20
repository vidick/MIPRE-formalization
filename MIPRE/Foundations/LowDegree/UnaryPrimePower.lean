/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.UnaryPrimality

/-! # A capped unary program for maximal prime-power divisors -/

noncomputable section

namespace MIPRE.LowDegree.DegreeArithmetic

open Cost Cost.PolyTimeFun Polynomial

/-- Target integer, candidate prime, and current prime power, all unary. -/
abbrev PrimePowerState := Unary × Unary × Unary

/-- Advance a dividing prime power, capping every replacement by the target input. -/
def primePowerStep (s : PrimePowerState) : PrimePowerState :=
  let candidate := unary (s.2.1.length * s.2.2.length)
  if candidate.length ∣ s.1.length then (s.1, s.2.1, candidate.take s.1.length) else s

private def primePowerStepProg : PolyTimeFun (PrimePowerState × Unit) PrimePowerState :=
  let n := fst.comp fst
  let q := fst.comp (snd.comp fst)
  let r := snd.comp (snd.comp fst)
  let candidate := mulUnaryProg.comp (q.pair r)
  congr (ite (dvdUnaryProg.comp (candidate.pair n))
    (n.pair (q.pair (take.comp (candidate.pair n)))) fst)
    (fun s => primePowerStep s.1) (by
      rintro ⟨⟨n, q, r⟩, x⟩
      change (if decide ((unary (q.length * r.length)).length ∣ n.length)
        then (n, q, (unary (q.length * r.length)).take n.length) else (n, q, r)) = _
      simp only [decide_eq_true_eq, primePowerStep])

private theorem primePowerStep_shape (s : PrimePowerState) :
    (primePowerStep s).1 = s.1 ∧ (primePowerStep s).2.1 = s.2.1 ∧
      (primePowerStep s).2.2.length ≤ max s.2.2.length s.1.length := by
  dsimp only [primePowerStep]
  split
  · exact ⟨rfl, rfl, (List.length_take_le _ _).trans (le_max_right _ _)⟩
  · exact ⟨rfl, rfl, le_max_left _ _⟩

private theorem fold_primePowerStep_shape (u : Unary) (s : PrimePowerState) :
    (u.foldl (fun s _ => primePowerStep s) s).1 = s.1 ∧
      (u.foldl (fun s _ => primePowerStep s) s).2.1 = s.2.1 ∧
      (u.foldl (fun s _ => primePowerStep s) s).2.2.length ≤ max s.2.2.length s.1.length := by
  induction u generalizing s with
  | nil => exact ⟨rfl, rfl, le_max_left _ _⟩
  | cons x u ih =>
    obtain ⟨hn, hq, hr⟩ := primePowerStep_shape s
    obtain ⟨hn', hq', hr'⟩ := ih (primePowerStep s)
    refine ⟨hn'.trans hn, hq'.trans hq, ?_⟩
    rw [hn] at hr'
    exact hr'.trans (max_le hr (le_max_right _ _))

private theorem primePowerStep_bounded : FoldBounded primePowerStepProg (6 * X + 6) := by
  intro u s pre post _
  change esize (pre.foldl (fun s _ => primePowerStep s) s) ≤ _
  obtain ⟨hn, hq, hr⟩ := fold_primePowerStep_shape pre s
  have he := esize_unary_list (pre.foldl (fun s _ => primePowerStep s) s).2.2
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  have hsn := length_le_esize_list s.1
  have hsr := length_le_esize_list s.2.2
  rw [esize_prod, esize_prod, hn, hq, he]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- The capped maximum-power search. -/
def rawPrimePower (n q : Unary) : Unary :=
  (n.foldl (fun s _ => primePowerStep s) (n, q, [()])).2.2

/-- Uniform polynomial-time implementation of the capped maximum-power search. -/
def rawPrimePowerProg : PolyTimeFun (Unary × Unary) Unary :=
  (snd.comp snd).comp ((foldl primePowerStepProg (6 * X + 6) primePowerStep_bounded).comp
    (fst.pair (fst.pair (snd.pair (const [()])))))

@[simp] theorem rawPrimePowerProg_apply (n q : Unary) : rawPrimePowerProg (n, q) = rawPrimePower n q := rfl

private theorem primePowerStep_progress (n q j : ℕ) (hn : 0 < n) (hq : q.Prime)
    (hj : j < n.factorization q) :
    primePowerStep (unary n, unary q, unary (q ^ j)) =
      (unary n, unary q, unary (q ^ (j + 1))) := by
  have hd : q ^ (j + 1) ∣ n := (hq.pow_dvd_iff_le_factorization hn.ne').mpr (by omega)
  have hle : q ^ (j + 1) ≤ n := Nat.le_of_dvd hn hd
  simp only [primePowerStep, length_unary, ← pow_succ', hd, ↓reduceIte]
  rw [List.take_of_length_le (by simpa using hle)]

private theorem primePowerStep_fixed (n q : ℕ) (hn : 0 < n) (hq : q.Prime) :
    primePowerStep (unary n, unary q, unary (q ^ n.factorization q)) =
      (unary n, unary q, unary (q ^ n.factorization q)) := by
  have hd := Nat.pow_succ_factorization_not_dvd hn.ne' hq
  simp only [primePowerStep, length_unary, ← pow_succ', hd, ↓reduceIte]

private theorem iterate_primePowerStep (n q t : ℕ) (hn : 0 < n) (hq : q.Prime) :
    primePowerStep^[t] (unary n, unary q, [()]) =
      (unary n, unary q, unary (q ^ min t (n.factorization q))) := by
  induction t with
  | zero => simp [unary]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases ht : t < n.factorization q
    · rw [min_eq_left ht.le, primePowerStep_progress n q t hn hq ht,
        min_eq_left (by omega : t + 1 ≤ n.factorization q)]
    · rw [min_eq_right (by omega : n.factorization q ≤ t), primePowerStep_fixed n q hn hq,
        min_eq_right (by omega : n.factorization q ≤ t + 1)]

private theorem fold_primePowerStep (u : Unary) (s : PrimePowerState) :
    u.foldl (fun s _ => primePowerStep s) s = primePowerStep^[u.length] s := by
  induction u generalizing s with
  | nil => rfl
  | cons x u ih => rw [List.foldl_cons, ih, List.length_cons, Function.iterate_succ_apply]

/-- Unary input length supplies enough iterations to reach the maximal prime-power divisor. -/
theorem rawPrimePower_correct (n q : ℕ) (hq : q.Prime) :
    rawPrimePower (unary n) (unary q) = unary (q ^ n.factorization q) := by
  by_cases hn : n = 0
  · subst n
    simp [rawPrimePower, unary]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hd : q ^ n.factorization q ∣ n := (hq.pow_dvd_iff_le_factorization hn).mpr le_rfl
    have hpow := Nat.le_of_dvd hpos hd
    have htwo := Nat.pow_le_pow_left hq.two_le (n.factorization q)
    have hexp : n.factorization q < 2 ^ (n.factorization q) := Nat.lt_two_pow_self
    have hb : n.factorization q ≤ n := by omega
    rw [rawPrimePower, fold_primePowerStep, length_unary, iterate_primePowerStep n q n hpos hq,
      min_eq_right hb]

/-- Nonprime candidates contribute the neutral degree one. -/
def primePowerUnary (n q : Unary) : Unary :=
  if q.length.Prime then rawPrimePower n q else [()]

/-- One total polynomial-time program for each prime's contribution to a unary degree. -/
def primePowerUnaryProg : PolyTimeFun (Unary × Unary) Unary :=
  congr (ite (primeUnaryProg.comp snd) rawPrimePowerProg (const [()]))
    (fun s => primePowerUnary s.1 s.2) (by
      rintro ⟨n, q⟩
      change (if decide q.length.Prime then rawPrimePower n q else [()]) = _
      simp only [decide_eq_true_eq, primePowerUnary])

@[simp] theorem primePowerUnaryProg_apply (n q : Unary) :
    primePowerUnaryProg (n, q) = primePowerUnary n q := rfl

/-- The output is exactly the canonical prime-power component of the target degree. -/
theorem primePowerUnary_correct (n q : ℕ) :
    primePowerUnary (unary n) (unary q) = unary (q ^ n.factorization q) := by
  by_cases hq : q.Prime
  · simp only [primePowerUnary, length_unary, hq, ↓reduceIte]
    exact rawPrimePower_correct n q hq
  · simp [primePowerUnary, hq, Nat.factorization_eq_zero_of_not_prime n hq, unary]

end MIPRE.LowDegree.DegreeArithmetic

end
