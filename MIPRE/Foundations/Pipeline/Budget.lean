/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.VerifierValue

/-!
# Resource budgets of a verifier at one index

The four transformations of chapter 6 of the blueprint (introspection, oracularization,
answer reduction, parallel repetition) each take a normal form verifier and return one, and
each states its complexity as bounds on the output *in terms of bounds on the input*: the
paper's `TIME_𝒮(n)`, `TIME_𝒟(n)`, the dimension `s(n)` and the timeout bound `B_𝒟(n)` of a
decider in timeout-counter form. In the ambient cost model these are five numbers per index
(`MIPRE.Verifier` explains the degree): the running-time coefficients of the sampler and the
decider, their common degree in the size of the input, a bound on the dimension of the
questions, and a length of answers beyond which the decider rejects (`Verifier.RejectsLong`,
the ambient reading of "the decider first parses its answers against `B_𝒟(n)`"). `Budget`
collects them and `Verifier.Within V n R` says `V` respects `R` at index `n`.

Nothing here has content: it is the vocabulary in which the hypothesis structures of
`MIPRE.Foundations.Pipeline` state their complexity clauses, so that the composition
`MIPRE.GapCompression.ofPipeline` can chain them.
-/

namespace MIPRE

open Cost

/-- A resource budget at one index: a bound `S` on the sampler's running-time coefficient, `d`
on the dimension of its questions, `D` on the decider's running-time coefficient, `k` on the
degree of both running times in the size of the input, and `B` on the length of the answers
the decider can accept. -/
structure Budget where
  /-- Sampler running-time coefficient (`TIME_𝒮(n)`). -/
  S : ℕ
  /-- Dimension of the questions (`s(n)`). -/
  d : ℕ
  /-- Decider running-time coefficient (`TIME_𝒟(n)`). -/
  D : ℕ
  /-- Degree of both running times in the size of the input. -/
  k : ℕ
  /-- Length beyond which the decider rejects an answer (`B_𝒟(n)`). -/
  B : ℕ

namespace Budget

/-- The budget with the same bound `z` on every quantity, at degree `k`. -/
def uniform (z k : ℕ) : Budget := ⟨z, z, z, k, z⟩

@[simp] theorem uniform_S (z k : ℕ) : (uniform z k).S = z := rfl
@[simp] theorem uniform_d (z k : ℕ) : (uniform z k).d = z := rfl
@[simp] theorem uniform_D (z k : ℕ) : (uniform z k).D = z := rfl
@[simp] theorem uniform_k (z k : ℕ) : (uniform z k).k = k := rfl
@[simp] theorem uniform_B (z k : ℕ) : (uniform z k).B = z := rfl

/-- Pointwise comparison of budgets. -/
def Le (R R' : Budget) : Prop :=
  R.S ≤ R'.S ∧ R.d ≤ R'.d ∧ R.D ≤ R'.D ∧ R.k ≤ R'.k ∧ R.B ≤ R'.B

theorem Le.refl (R : Budget) : R.Le R := ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem uniform_le_uniform {z z' k k' : ℕ} (hz : z ≤ z') (hk : k ≤ k') :
    (uniform z k).Le (uniform z' k') := ⟨hz, hz, hz, hk, hz⟩

end Budget

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- `V` respects the budget `R` at index `n`: its sampler runs within `R.S` at degree `R.k`,
its questions have dimension at most `R.d`, its decider runs within `R.D` at degree `R.k`, and
its decider rejects every answer longer than `R.B`. -/
def Within (n : ℕ) (R : Budget) : Prop :=
  V.sampler.TimeBoundAt n R.S R.k ∧ V.sampler.dim n ≤ R.d ∧
    V.decider.TimeBoundAt n R.D R.k ∧ V.RejectsLong n R.B

variable {V}

theorem RejectsLong.mono {n T T' : ℕ} (hT : T ≤ T') (h : V.RejectsLong n T) :
    V.RejectsLong n T' := fun x y a b hab =>
  h x y a b (by omega)

theorem Within.mono {n : ℕ} {R R' : Budget} (h : V.Within n R) (hle : R.Le R') :
    V.Within n R' :=
  ⟨h.1.mono hle.1 hle.2.2.2.1, h.2.1.trans hle.2.1, h.2.2.1.mono hle.2.2.1 hle.2.2.2.1,
    RejectsLong.mono hle.2.2.2.2 h.2.2.2⟩

theorem Within.sampler_time {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.sampler.TimeBoundAt n R.S R.k := h.1

theorem Within.sampler_dim {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.sampler.dim n ≤ R.d := h.2.1

theorem Within.decider_time {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.decider.TimeBoundAt n R.D R.k := h.2.2.1

theorem Within.rejectsLong {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.RejectsLong n R.B := h.2.2.2

/-- A verifier respecting a budget has, at any larger answer bound, the same value as at the
budget's answer bound. -/
theorem Within.valStar_eq {n : ℕ} {R : Budget} (h : V.Within n R) {T : ℕ} (hT : R.B ≤ T) :
    V.valStar n T = V.valStar n R.B :=
  V.valStar_eq_of_rejects hT h.rejectsLong

end Verifier

end MIPRE
