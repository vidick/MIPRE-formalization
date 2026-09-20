/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Pipeline.Budget
import MIPRE.Foundations.GapCompression

/-!
# Introspection, as a hypothesis

Blueprint `thm:introspection` (paper `introspection.tex`, `thm:introspection`; ledger nodes
`1.2`, `1.2.3.8`), stated as the data the theorem provides: the structure `Introspection ℓ`.
Its inhabitation is the theorem — the rigidity argument of the paper's Section 8 through the
Pauli basis test `thm:qld` — and nothing here proves it. The composition
`MIPRE.GapCompression.ofPipeline` consumes an instance at `ℓ = 7`.

The reading of the paper's statement in the vocabulary of `MIPRE.Verifier`:

* `ComputeIntroVerifier` takes `(𝒱, λ, ℓ)`; with `ℓ` a parameter of the structure, the
  procedure is a polynomial-time function `compute` of `((S̄, D̄), λ)` returning the program of
  the introspective decider, and the introspective sampler `𝒮^intro_λ` depends only on `λ`
  (paper `lem:intro-sampler-complexity`), with its program computable from `λ`
  (`samplerProg`). On every input, well-formed or not, the output is a `5`-level normal form
  verifier (`output`).
* The complexity clauses hold for every input and every index: `TIME_𝒮(n) ≤ (λn)^C`,
  `TIME_𝒟(n) ≤ 2^{Cλn}` and `|𝒟^intro| ≤ Cλ^C` for a constant `C` (the paper's `C_intro`,
  eq. `c_intro` of `recursive.tex`), read with `λn + 1` in place of `λn` so that the bounds
  are meaningful at every index and level; the running times carry the degree `C` in the size
  of the input that `Decider.TimeBoundAt` needs, and the decider rejects every answer longer
  than its time bound (`Budget.B`). The introspective decider keeps `𝒟` within its own
  description only up to `λ` bits (paper `lem:intro-decider-complexity`), which is why the
  size bound does not depend on the input.
* For a `λ`-bounded `ℓ`-level input: a value-`1` PCC strategy for `𝒱_{2^n}` gives
  one for `𝒱^intro_n` (completeness), and `val*(𝒱^intro_n) > 1 - ε` gives
  `val*(𝒱_{2^n}) ≥ 1 - δ(ε, n)` with `δ(ε, n) = a((λn)^a ε^b + (λn)^{-b})` (soundness), the
  constants `a, b` depending on `ℓ` only. Soundness requires `1 ≤ n`, as in the construction's
  indexing convention: the original input is bounded only at `2 ≤ 2^n`. At zero the displayed
  error would vanish and assert an unintended exact conclusion. The paper has `a > 0`; `a ≥ 1` is assumed here,
  which only weakens the clause and is what the proof of `thm:compression` uses.

Answer alphabets follow `MIPRE.GapCompression`: `𝒱_{2^n}` is read with answers of length at
most `(2^n)^λ`, and `𝒱^intro_n` with answers of length at most its time bound, beyond which
its decider rejects.
-/

namespace MIPRE

open Cost

namespace Introspection

/-- The answer bound of the introspective verifier at level `λ` and index `n`: its decider's
running-time coefficient `2^{C(λn + 1)}`. -/
abbrev ansBound (C lam n : ℕ) : ℕ := 2 ^ (C * (lam * n + 1))

/-- The budget of the introspective verifier at level `λ` and index `n`: sampler within
`(λn + 1)^C`, questions of dimension at most `(λn + 1)^C`, decider within `2^{C(λn + 1)}`, both
at degree `C`, and no answer longer than `2^{C(λn + 1)}` accepted. -/
def budget (C lam n : ℕ) : Budget :=
  ⟨(lam * n + 1) ^ C, (lam * n + 1) ^ C, ansBound C lam n, C, ansBound C lam n⟩

/-- The soundness loss `δ(ε, n) = a((λn)^a ε^b + (λn)^{-b})`. -/
noncomputable def delta (a b : ℝ) (lam n : ℕ) (ε : ℝ) : ℝ :=
  a * (((lam : ℝ) * n) ^ a * ε ^ b + ((lam : ℝ) * n) ^ (-b))

/-- At index zero the displayed error vanishes, so soundness cannot use this index. -/
theorem delta_zero_index (a b : ℝ) (lam : ℕ) (ε : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    delta a b lam 0 ε = 0 := by
  simp [delta, Real.zero_rpow ha, Real.zero_rpow (neg_ne_zero.mpr hb)]

/-- Positive introspection indices are exactly the range where the original budget applies. -/
theorem two_le_exp_index_iff (n : ℕ) : 2 ≤ 2 ^ n ↔ 1 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have : n = 0 := by omega
    simp [this] at h
  · intro hn
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn : 2 ^ 1 ≤ 2 ^ n)

end Introspection

/-- **Introspection** (blueprint `thm:introspection`) for `ℓ`-level inputs: the data of the
procedure `ComputeIntroVerifier` together with the guarantees of the theorem. An instance of
this structure is the theorem. -/
structure Introspection (ℓ : ℕ) where
  /-- The constant `a` of the soundness loss, normalized to `a ≥ 1`. -/
  a : ℝ
  /-- The exponent `b` of the soundness loss, `0 < b ≤ 1`. -/
  b : ℝ
  one_le_a : 1 ≤ a
  b_pos : 0 < b
  b_le_one : b ≤ 1
  /-- The complexity constant `C_intro`. -/
  C : ℕ
  /-- The introspective sampler `𝒮^intro_λ`, depending only on `λ`. -/
  sampler : ℕ → CL.Sampler 5
  /-- Its program, computable from `λ` in polynomial time. -/
  samplerProg : PolyTimeFun ℕ Prog
  samplerProg_eq : ∀ lam : ℕ, samplerProg lam = (sampler lam).prog
  /-- `ComputeIntroVerifier`: from the programs of a verifier and `λ`, the program of the
  introspective decider, in polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog) × ℕ) Prog
  /-- The output on any input is a `5`-level normal form verifier, with the introspective
  sampler and the introspective decider. -/
  output : Prog × Prog → ℕ → Verifier 5
  output_sampler : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).sampler = sampler lam
  output_decider : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).decider.prog = compute (V, lam)
  /-- The complexity clauses, for every input and index. -/
  within : ∀ (V : Prog × Prog) (lam n : ℕ), (output V lam).Within n (Introspection.budget C lam n)
  /-- `|𝒟^intro| ≤ C λ^C`, for every input. -/
  decider_size : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).decider.size ≤ C * (lam + 1) ^ C
  /-- **Completeness.** For a `λ`-bounded input: a value-`1` PCC strategy for `𝒱_{2^n}` gives
  one for `𝒱^intro_n`. -/
  completeness : ∀ (V : Verifier ℓ) (lam n : ℕ), V.IsBounded lam →
    V.HasPerfectPCC (2 ^ n) ((2 ^ n) ^ lam) →
    (output (V.sampler.prog, V.decider.prog) lam).HasPerfectPCC n (Introspection.ansBound C lam n)
  /-- **Soundness.** For a `λ`-bounded input and `n ≥ 1`: `val*(𝒱^intro_n) > 1 - ε` gives
  `val*(𝒱_{2^n}) ≥ 1 - δ(ε, n)`. -/
  soundness : ∀ (V : Verifier ℓ) (lam n : ℕ) (ε : ℝ), V.IsBounded lam → 1 ≤ n → 0 < ε →
    1 - ε < (output (V.sampler.prog, V.decider.prog) lam).valStar n (Introspection.ansBound C lam n) →
    1 - Introspection.delta a b lam n ε ≤ V.valStar (2 ^ n) ((2 ^ n) ^ lam)

end MIPRE
