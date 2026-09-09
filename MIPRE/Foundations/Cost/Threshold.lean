/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Unary
import Mathlib.Tactic.Linarith

/-!
# The threshold function of the compression argument

`threshold K : PolyTimeFun Prog ℕ` computes `e ↦ 2 ^ (K + 1 + esize e)`: the size of the
program in unary (`sizeProg`), plus the constant `K + 1` (`addConstProg`), then the bit
string of the power of two (`expBitsProg`). In the recursive compression argument
(`planning/compression-track.md`, K3 step 4) the constant `K` is chosen, once and for all,
from the overhead polynomials of the toolkit so that `n ≥ 2 ^ (K + 1 + |e|)` makes every
polynomial in `|e| + log n` at most `n`.
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- `k ↦ K + k` on unary numerals. -/
def addConstProg (K : ℕ) : Prog := .let_ (.cons (.const (.ofNat K)) (.var 0)) addProg

theorem addConstProg_wellScoped (K : ℕ) : (addConstProg K).WellScoped 1 :=
  ⟨⟨trivial, Nat.zero_lt_one⟩, addProg_wellScoped.mono (by omega) _⟩

theorem addConstProg_runs (K k : ℕ) :
    ∃ t ≤ (K + 1) * (4 * K + 2 * k + 15) + 2 * K + 2 * k + 5,
      (addConstProg K).Runs (.ofNat k) (.ofNat (K + k)) t := by
  obtain ⟨t, ht, hrun⟩ := addProg_runs K k [Data.ofNat k]
  refine ⟨2 * K + 1 + (2 * k + 1 + 1) + 1 + t + 1, by omega, ?_⟩
  have hpre : Eval [Data.ofNat k] (.cons (.const (.ofNat K)) (.var 0))
      (.cons (.ofNat K) (.ofNat k)) (2 * K + 1 + (2 * k + 1 + 1) + 1) := by
    have := Eval.cons (Eval.const [Data.ofNat k] (.ofNat K))
      (Eval.var_of_get (env := [Data.ofNat k]) (i := 0) (v := .ofNat k) (by simp))
    simpa using this
  exact Eval.let_ hpre hrun

/-- The threshold program: `d ↦ encode (2 ^ (K + 1 + d.size))`. -/
def thresholdProg (K : ℕ) : Prog :=
  .let_ sizeProg (.let_ (callVar 0 (addConstProg (K + 1))) (callVar 0 expBitsProg))

theorem thresholdProg_wellScoped (K : ℕ) : (thresholdProg K).WellScoped 1 :=
  ⟨sizeProg_wellScoped,
    ⟨callVar_wellScoped (by decide) (addConstProg_wellScoped _),
      callVar_wellScoped (by decide) expBitsProg_wellScoped⟩⟩

theorem thresholdProg_runs (K : ℕ) (d : Data) :
    ∃ t ≤ 40 * (d.size + (K + 4)) ^ 2,
      (thresholdProg K).Runs d (encode (2 ^ (K + 1 + d.size))) t := by
  set N := d.size with hN
  obtain ⟨t₁, ht₁, h₁⟩ := sizeProg_runs d
  obtain ⟨t₂, ht₂, h₂⟩ := addConstProg_runs (K + 1) N
  obtain ⟨t₃, ht₃, h₃⟩ := expBitsProg_runs (K + 1 + N)
  -- the calls, in their environments
  have c₂ := callVar_eval (env := [Data.ofNat N, d]) (i := 0) (addConstProg_wellScoped (K + 1))
    (v := .ofNat N) (by simp) h₂
  have c₃ := callVar_eval (env := [Data.ofNat (K + 1 + N), Data.ofNat N, d]) (i := 0)
    expBitsProg_wellScoped (v := .ofNat (K + 1 + N)) (by simp) h₃
  refine ⟨t₁ + (((Data.ofNat N).size + 1 + t₂ + 1) +
      ((Data.ofNat (K + 1 + N)).size + 1 + t₃ + 1) + 1) + 1, ?_, ?_⟩
  · simp only [Data.size_ofNat] at ht₁ ht₂ ht₃ ⊢
    nlinarith [ht₁, ht₂, ht₃, Nat.zero_le N, Nat.zero_le K]
  · exact Eval.let_ h₁ (Eval.let_ c₂ c₃)

end Prog

/-- `e ↦ 2 ^ (K + 1 + esize e)`, in polynomial time. -/
noncomputable def PolyTimeFun.threshold (K : ℕ) : PolyTimeFun Prog ℕ where
  toFun e := 2 ^ (K + 1 + esize e)
  code := Prog.thresholdProg K
  closed := Prog.thresholdProg_wellScoped K
  timeBound := C 40 * (X + C (K + 4)) ^ 2
  computes e := by
    obtain ⟨t, ht, h⟩ := Prog.thresholdProg_runs K (encode e)
    refine ⟨t, ?_, h⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    exact ht

@[simp] theorem PolyTimeFun.threshold_apply (K : ℕ) (e : Prog) :
    PolyTimeFun.threshold K e = 2 ^ (K + 1 + esize e) := rfl

end MIPRE.Cost
