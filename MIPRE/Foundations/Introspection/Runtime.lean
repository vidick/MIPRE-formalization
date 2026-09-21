/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Pipeline.Introspection
import MIPRE.Foundations.Halting.PolyBounded
import MIPRE.Foundations.Cost.Toolkit

/-! # Absolute simulation bounds on the original legal answer cut

Ambient boundedness controls input-size degree as well as a time coefficient.
On four bit strings of length at most `(2^n)^λ`, the resulting absolute cost has
a quadratic exponent in `λ`. The polynomial-exponent introspection budget
absorbs this cost without enlarging the original game's answer alphabet.

These lemmas concern actual source and universal-simulator runs. They do not
yet construct the introspective decider's format checks or other subtests.
-/

namespace MIPRE.Introspection

open Cost

/-- Exact linear size bound for the four fields of a legal decider query. -/
theorem legal_query_size_le (R : ℕ) (x y a b : BitStr)
    (hx : x.length ≤ R) (hy : y.length ≤ R)
    (ha : a.length ≤ R) (hb : b.length ≤ R) :
    esize (x, y, a, b) + 1 ≤ 16 * R + 8 := by
  have h1 := esize_bitStr_le x
  have h2 := esize_bitStr_le y
  have h3 := esize_bitStr_le a
  have h4 := esize_bitStr_le b
  simp only [esize_prod]
  omega

/-- Legal-input ambient costs fit the repaired budget with exponent five. -/
theorem legal_query_cost_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (x y a b : BitStr)
    (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
    (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
    (2 ^ n) ^ lam * (esize (x, y, a, b) + 1) ^ lam ≤ ansBound 5 lam n := by
  let u := lam * n
  have hlu : lam ≤ u := by dsimp [u]; nlinarith
  have hu : 1 ≤ u := hl.trans hlu
  have hR : (2 ^ n) ^ lam = 2 ^ u := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have hR1 : 1 ≤ 2 ^ u := Nat.one_le_pow _ _ (by decide)
  have hs : esize (x, y, a, b) + 1 ≤ 2 ^ (5 + u) := by
    calc esize (x, y, a, b) + 1 ≤ 16 * (2 ^ n) ^ lam + 8 :=
          legal_query_size_le _ x y a b hx hy ha hb
      _ ≤ 32 * 2 ^ u := by rw [hR]; omega
      _ = 2 ^ (5 + u) := by rw [pow_add]; norm_num
  have he : u + (5 + u) * lam ≤ (u + 1) ^ 5 := by
    have hc : 8 ≤ (u + 1) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc u + (5 + u) * lam ≤ u + (5 + u) * u := by gcongr
      _ ≤ 8 * (u + 1) ^ 2 := by nlinarith
      _ ≤ (u + 1) ^ 3 * (u + 1) ^ 2 := Nat.mul_le_mul_right _ hc
      _ = (u + 1) ^ 5 := by ring
  calc (2 ^ n) ^ lam * (esize (x, y, a, b) + 1) ^ lam
      ≤ 2 ^ u * (2 ^ (5 + u)) ^ lam := by rw [hR]; gcongr
    _ = 2 ^ (u + (5 + u) * lam) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((u + 1) ^ 5) := Nat.pow_le_pow_right (by decide) he

/-- An actual bounded decider halts within an absolute polynomial-exponent
budget on every input from the original answer cut. -/
theorem original_decider_haltsWithin {ℓ lam n : ℕ} (V : Verifier ℓ)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (x y a b : BitStr)
    (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
    (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
    HaltsWithin V.decider.prog (encode (2 ^ n, x, y, a, b)) (ansBound 5 lam n) := by
  have htime := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).2.2
  obtain ⟨r, t, ht, hrun⟩ := htime (encode (x, y, a, b))
  exact ⟨r, t, ht.trans (legal_query_cost_le (by have := hV.two_le; omega) hn
    x y a b hx hy ha hb), hrun⟩

/-- Any fixed polynomial overhead is absorbed by another polynomial exponent. -/
theorem polynomial_ansBound (P : Polynomial ℕ) (k : ℕ) :
    ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      P.eval (ansBound k lam n) ≤ ansBound C lam n := by
  obtain ⟨d, hd⟩ := (PolyBounded.eval P PolyBounded.id).exists_le_pow
  refine ⟨k + d, fun lam n hl hn => ?_⟩
  have hz : 2 ≤ lam * n + 1 := by nlinarith
  have hb : 2 ≤ ansBound k lam n := by
    change 2 ^ 1 ≤ 2 ^ ((lam * n + 1) ^ k)
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.one_le_pow _ _ (by omega)
  have hc : d ≤ (lam * n + 1) ^ d :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hz d)
  calc P.eval (ansBound k lam n) ≤ (ansBound k lam n) ^ d := hd _ hb
    _ = 2 ^ ((lam * n + 1) ^ k * d) := by rw [ansBound, ← pow_mul]
    _ ≤ 2 ^ ((lam * n + 1) ^ k * (lam * n + 1) ^ d) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hc)
    _ = ansBound (k + d) lam n := by rw [← pow_add]

/-- Uniform absolute time for the actual universal simulation, on the original
legal question and answer cut. The exponent depends only on the universal machine. -/
theorem original_simulation_haltsWithin (U : UniversalMachine) :
    ∃ C, ∀ {ℓ lam n : ℕ} (V : Verifier ℓ), V.IsBounded lam → 1 ≤ n →
      ∀ x y a b : BitStr,
      x.length ≤ (2 ^ n) ^ lam → y.length ≤ (2 ^ n) ^ lam →
      a.length ≤ (2 ^ n) ^ lam → b.length ≤ (2 ^ n) ^ lam →
      HaltsWithin U.univ (.cons (encode V.decider.prog) (encode (2 ^ n, x, y, a, b)))
        (ansBound C lam n) := by
  obtain ⟨C, hC⟩ := polynomial_ansBound (U.bound.comp (Polynomial.C 64 * Polynomial.X)) 5
  refine ⟨C, fun {ℓ lam n} V hV hn x y a b hx hy ha hb => ?_⟩
  have hl : 1 ≤ lam := by have := hV.two_le; omega
  let R := (2 ^ n) ^ lam
  have hR1 : 1 ≤ R := Nat.one_le_pow _ _ (by positivity)
  have hnR : n ≤ R := by
    calc n ≤ 2 ^ n := Nat.lt_two_pow_self.le
      _ = (2 ^ n) ^ 1 := (pow_one _).symm
      _ ≤ R := Nat.pow_le_pow_right (by positivity) hl
  have hlR : lam ≤ R := by
    calc lam ≤ 2 ^ lam := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (n * lam) := Nat.pow_le_pow_right (by decide) (by nlinarith)
      _ = R := pow_mul _ _ _
  have hRB : R ≤ ansBound 5 lam n := by
    rw [show R = 2 ^ (lam * n) by dsimp [R]; rw [← pow_mul, Nat.mul_comm]]
    apply Nat.pow_le_pow_right (by decide)
    calc lam * n ≤ lam * n + 1 := by omega
      _ = (lam * n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (lam * n + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hcode : esize V.decider.prog ≤ lam :=
    (le_max_right V.sampler.size V.decider.size).trans hV.2
  have hdata : esize (2 ^ n, x, y, a, b) ≤ 33 * R := by
    have hs := legal_query_size_le R x y a b hx hy ha hb
    have hi := esize_nat_le (2 ^ n)
    rw [Nat.size_pow] at hi
    rw [esize_prod]
    omega
  obtain ⟨r, t, ht, hr⟩ := original_decider_haltsWithin V hV hn x y a b hx hy ha hb
  obtain ⟨t', ht', hr'⟩ := U.time_le _ _ _ _ hr
  refine ⟨r, t', ht'.trans ?_, hr'⟩
  calc U.bound.eval (esize V.decider.prog + (encode (2 ^ n, x, y, a, b)).size + t)
      ≤ U.bound.eval (64 * ansBound 5 lam n) := polynomial_eval_mono _ (by
          change esize V.decider.prog + esize (2 ^ n, x, y, a, b) + t ≤ _
          omega)
    _ ≤ ansBound C lam n := by
      simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X] using hC lam n hl hn

end MIPRE.Introspection
