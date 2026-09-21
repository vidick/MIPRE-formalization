/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Halting.Arith
import MIPRE.Foundations.Introspection.Runtime
import MIPRE.Foundations.CL.DetypingClock

/-! # Executable arithmetic for the introspection clock

One fixed program, for each constant exponent, reads binary `λ` and `n` and
writes the unary budget `2^((λ*n+1)^k)`. The large output is constructed by
proved unary arithmetic programs; it is never embedded in the program text.
-/

noncomputable section

namespace MIPRE.Introspection.ClockArithmetic

open Cost Cost.Prog Polynomial

def unaryCost (n : ℕ) : ℕ :=
  (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90)

def bothUnary : Prog :=
  .elim 0 .nil (.let_ (callVar 0 toUnaryProg)
    (.let_ (callVar 2 toUnaryProg) (.cons (.var 1) (.var 0))))

theorem bothUnary_closed : bothUnary.WellScoped 1 := by
  refine ⟨by omega, trivial, ?_⟩
  exact ⟨callVar_wellScoped (by omega) toUnaryProg_wellScoped,
    callVar_wellScoped (by omega) toUnaryProg_wellScoped, by simp [WellScoped]⟩

theorem bothUnary_runs (a b : ℕ) :
    ∃ time ≤ unaryCost a + unaryCost b + esize a + esize b + 2 * a + 2 * b + 20,
      bothUnary.Runs (encode (a, b)) (.cons (.ofNat a) (.ofNat b)) time := by
  obtain ⟨ta, hta, ha⟩ := toUnaryProg_runs a
  obtain ⟨tb, htb, hb⟩ := toUnaryProg_runs b
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode a) (b := encode b) (by rfl)
    (Eval.let_ (callVar_eval (i := 0) toUnaryProg_wellScoped (by simp) ha)
      (Eval.let_ (callVar_eval (i := 2) toUnaryProg_wellScoped (by simp) hb)
        (Eval.cons (Eval.var_of_get (i := 1) (by simp)) (Eval.var_of_get (i := 0) (by simp)))))⟩
  simp only [Data.size_ofNat]
  change ta ≤ unaryCost a at hta
  change tb ≤ unaryCost b at htb
  have hae : (encode a).size = esize a := rfl
  have hbe : (encode b).size = esize b := rfl
  omega

def powerCoeffs (k : ℕ) : List ℕ := List.replicate k 0 ++ [1]

theorem powerCoeffs_eval (k m : ℕ) : Data.polyEval (powerCoeffs k) m = m ^ k := by
  induction k with
  | zero => simp [powerCoeffs, Data.polyEval]
  | succ k ih =>
    simpa only [powerCoeffs, List.replicate_succ, List.cons_append, Data.polyEval,
      Nat.zero_add, pow_succ, Nat.mul_comm] using congrArg (m * ·) ih

def powerBound (k : ℕ) : Polynomial ℕ := (polyProg_runs (powerCoeffs k)).choose

theorem power_runs (k m : ℕ) : ∃ time ≤ (powerBound k).eval m,
    (polyProg (powerCoeffs k)).Runs (.ofNat m) (.ofNat (m ^ k)) time := by
  simpa only [powerCoeffs_eval, powerBound, Prog.Runs] using
    (polyProg_runs (powerCoeffs k)).choose_spec m []

def mulCost (a b : ℕ) : ℕ :=
  (b + 1) * ((a + 1) * (4 * a + 2 * (a * b) + 15) + 4 * a + 4 * (a * b) + 2 * b + 41) +
    2 * b + 10

def uniformProg (k : ℕ) : Prog :=
  .let_ bothUnary (.let_ mulProg (.let_ (.cons .nil (.var 0))
    (.let_ (polyProg (powerCoeffs k)) (.let_ expBitsProg toUnaryProg))))

theorem uniformProg_closed (k : ℕ) : (uniformProg k).WellScoped 1 := by
  exact ⟨bothUnary_closed, mulProg_wellScoped.mono (by omega) _,
    ⟨trivial, by simp [WellScoped]⟩, (polyProg_wellScoped _).mono (by omega) _,
    expBitsProg_wellScoped.mono (by omega) _, toUnaryProg_wellScoped.mono (by omega) _⟩

def uniformCost (k lam n : ℕ) : ℕ :=
  let m := lam * n + 1
  let q := m ^ k
  unaryCost lam + unaryCost n + esize lam + esize n + 2 * lam + 2 * n + 20 +
    mulCost lam n + 2 * (lam * n) + 4 + (powerBound k).eval m +
    (q + 2) * (4 * q + 20) + unaryCost (ansBound k lam n) + 5

theorem uniformProg_runs (k lam n : ℕ) :
    ∃ time ≤ uniformCost k lam n,
      (uniformProg k).Runs (encode (lam, n)) (.ofNat (ansBound k lam n)) time := by
  obtain ⟨t₁, ht₁, h₁⟩ := bothUnary_runs lam n
  obtain ⟨t₂, ht₂, h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃, ht₃, h₃⟩ := power_runs k (lam * n + 1)
  obtain ⟨t₄, ht₄, h₄⟩ := expBitsProg_runs ((lam * n + 1) ^ k)
  obtain ⟨t₅, ht₅, h₅⟩ := toUnaryProg_runs (ansBound k lam n)
  have hs : (Prog.cons .nil (.var 0)).Runs (.ofNat (lam * n))
      (.ofNat (lam * n + 1)) (2 * (lam * n) + 4) := by
    have h := Eval.cons (Eval.nil [Data.ofNat (lam * n)])
        (Eval.var_of_get (env := [Data.ofNat (lam * n)]) (i := 0)
          (v := .ofNat (lam * n)) (by simp))
    exact h.cast_cost (by simp only [Data.size_ofNat]; omega)
  refine ⟨_, ?_, Eval.let_ h₁ (Eval.append_of_wellScoped
    (Eval.let_ h₂ (Eval.append_of_wellScoped
      (Eval.let_ hs (Eval.append_of_wellScoped
        (Eval.let_ h₃ (Eval.append_of_wellScoped
          (Eval.let_ h₄ (Eval.append_of_wellScoped h₅ toUnaryProg_wellScoped _))
          ⟨expBitsProg_wellScoped, toUnaryProg_wellScoped.mono (by omega) _⟩ _))
        ⟨polyProg_wellScoped _, expBitsProg_wellScoped.mono (by omega) _,
          toUnaryProg_wellScoped.mono (by omega) _⟩ _))
      ⟨⟨trivial, by simp [WellScoped]⟩, (polyProg_wellScoped _).mono (by omega) _,
        expBitsProg_wellScoped.mono (by omega) _, toUnaryProg_wellScoped.mono (by omega) _⟩ _))
    ⟨mulProg_wellScoped, ⟨trivial, by simp [WellScoped]⟩,
      (polyProg_wellScoped _).mono (by omega) _, expBitsProg_wellScoped.mono (by omega) _,
      toUnaryProg_wellScoped.mono (by omega) _⟩ _)⟩
  change t₂ ≤ mulCost lam n at ht₂
  change t₄ ≤ ((lam * n + 1) ^ k + 2) * (4 * (lam * n + 1) ^ k + 20) at ht₄
  change t₅ ≤ unaryCost (ansBound k lam n) at ht₅
  dsimp only [uniformCost]
  omega

end MIPRE.Introspection.ClockArithmetic
