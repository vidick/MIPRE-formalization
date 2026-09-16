/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Pipeline.Budget
import MIPRE.Foundations.GapCompression

/-!
# Answer reduction, as a hypothesis

Blueprint `thm:answer-reduction` (paper `ld_compiler.tex`, `thm:ar`; ledger nodes `1.3`,
`1.3.4`), stated as the data the theorem provides: the structure `AnswerReduction ℓ`. Its
inhabitation is the theorem — oracularization (`MIPRE.Oracularization`) composed with the
bespoke PCP for deciders (`thm:pcp-decider`) — and nothing here proves it. The composition
`MIPRE.GapCompression.ofPipeline` consumes an instance at `ℓ = 5`, the level of the
introspective verifier, and reads its output at `max (5 + 2) 5 = 7` levels.

The reading of the paper's statement in the vocabulary of `MIPRE.Verifier`:

* `ComputeAnsVerifier` takes `(𝒱, λ, μ, σ)` (and `ℓ`, here a parameter of the structure). The
  answer-reduced sampler depends only on the input sampler and the parameters (`sampler`),
  with its program computable in polynomial time (`samplerProg`); the decider is computed
  from the input programs and the parameters (`compute`).
* The paper's hypotheses on the input, `|𝒟| ≤ σ`, `TIME_𝒮(n) ≤ (λn)^μ` and
  `TIME_𝒟(n) ≤ (2^{λn})^μ` for `n ≥ 2`, are the budget `inBudget λ μ n` at index `n` — with
  `λn + 1` in place of `λn`, so that it is meaningful at every index, the dimension bounded by
  the sampler's time as `Verifier.IsBounded` does, and the answers bounded by the decider's
  time — together with `𝒟.size ≤ σ`. The output at index `n` is then within a polynomial of
  `(λn + 1)^μ + σ` (the paper's `poly((λn)^μ, σ)`), at a universal degree `deg`, and rejects
  answers longer than that bound.
* For `n ≥ C_ar` (the paper's threshold): a value-`1` PCC strategy for `𝒱_n` gives one for
  `𝒱^ans_n` (completeness), and `val*(𝒱^ans_n) > 1 - ε` gives `val*(𝒱_n) ≥ 1 - δ(ε, n)` with
  `δ(ε, n) = σ^a((λn)^{μa} ε^b + (λn)^{-μb})` (soundness), for universal constants `a, b`, with
  `a ≥ 1` assumed as in `Introspection`. The blueprint's statement has no threshold; the
  paper's does, and it is kept.

Answer alphabets: `𝒱_n` is read with answers of length at most the decider's time bound
`2^{μ(λn + 1)}`, the length the PCP decodes to (`rem:ar-composition`, item 4), and `𝒱^ans_n`
with answers of length at most its own time bound, beyond which its decider rejects.
-/

namespace MIPRE

open Cost

namespace AnswerReduction

/-- The answer bound answer reduction reads its input at: the decider's time bound
`2^{μ(λn + 1)}`. -/
abbrev inAns (lam mu n : ℕ) : ℕ := 2 ^ (mu * (lam * n + 1))

/-- The budget answer reduction asks of its input at index `n`: sampler within `(λn + 1)^μ`,
questions of dimension at most `(λn + 1)^μ`, decider within `2^{μ(λn + 1)}`, at degree `μ`,
and no answer longer than `2^{μ(λn + 1)}` accepted. -/
def inBudget (lam mu n : ℕ) : Budget :=
  ⟨(lam * n + 1) ^ mu, (lam * n + 1) ^ mu, inAns lam mu n, mu, inAns lam mu n⟩

/-- The argument of the polynomial bounding the output at index `n`: `(λn + 1)^μ + σ`. -/
abbrev arg (lam mu sigma n : ℕ) : ℕ := (lam * n + 1) ^ mu + sigma

/-- The soundness loss `δ(ε, n) = σ^a((λn)^{μa} ε^b + (λn)^{-μb})`. -/
noncomputable def delta (a b : ℝ) (lam mu sigma n : ℕ) (ε : ℝ) : ℝ :=
  (sigma : ℝ) ^ a *
    (((lam : ℝ) * n) ^ ((mu : ℝ) * a) * ε ^ b + ((lam : ℝ) * n) ^ (-((mu : ℝ) * b)))

end AnswerReduction

/-- **Answer reduction** (blueprint `thm:answer-reduction`) for `ℓ`-level inputs: the data of
the procedure `ComputeAnsVerifier` together with the guarantees of the theorem. An instance of
this structure is the theorem. -/
structure AnswerReduction (ℓ : ℕ) where
  /-- The constant `a` of the soundness loss, normalized to `a ≥ 1`. -/
  a : ℝ
  /-- The exponent `b` of the soundness loss, `0 < b ≤ 1`. -/
  b : ℝ
  one_le_a : 1 ≤ a
  b_pos : 0 < b
  b_le_one : b ≤ 1
  /-- The threshold `C_ar` above which the completeness and soundness clauses hold. -/
  C : ℕ
  /-- The polynomial `poly((λn)^μ, σ)` bounding the output. -/
  bound : Polynomial ℕ
  /-- The degree of the output's running times in the size of the input. -/
  deg : ℕ
  /-- The answer-reduced sampler, a function of the input sampler and `(λ, μ, σ)`. -/
  sampler : CL.Sampler ℓ → ℕ → ℕ → ℕ → CL.Sampler (max (ℓ + 2) 5)
  /-- Its program, computable from the input sampler's program and the parameters in
  polynomial time. -/
  samplerProg : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog
  samplerProg_eq : ∀ (S : CL.Sampler ℓ) (lam mu sigma : ℕ),
    samplerProg (S.prog, lam, mu, sigma) = (sampler S lam mu sigma).prog
  /-- `ComputeAnsVerifier`: the answer-reduced decider, from the input programs and
  `(λ, μ, σ)`, in polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog) × ℕ × ℕ × ℕ) Prog
  /-- The output on a normal form input, at parameters `(λ, μ, σ)`: a `max (ℓ + 2) 5`-level
  normal form verifier. -/
  output : Verifier ℓ → ℕ → ℕ → ℕ → Verifier (max (ℓ + 2) 5)
  output_sampler : ∀ (V : Verifier ℓ) (lam mu sigma : ℕ),
    (output V lam mu sigma).sampler = sampler V.sampler lam mu sigma
  output_decider : ∀ (V : Verifier ℓ) (lam mu sigma : ℕ),
    (output V lam mu sigma).decider.prog =
      compute ((V.sampler.prog, V.decider.prog), lam, mu, sigma)
  /-- The complexity clause: an input within `inBudget λ μ n` with `|𝒟| ≤ σ` gives an output
  within `poly((λn + 1)^μ + σ)` at degree `deg`, rejecting longer answers. -/
  within : ∀ (V : Verifier ℓ) (lam mu sigma n : ℕ),
    V.Within n (AnswerReduction.inBudget lam mu n) → V.decider.size ≤ sigma →
    (output V lam mu sigma).Within n
      (Budget.uniform (bound.eval (AnswerReduction.arg lam mu sigma n)) deg)
  /-- **Completeness**, for `n ≥ C_ar`. -/
  completeness : ∀ (V : Verifier ℓ) (lam mu sigma n : ℕ), C ≤ n →
    V.Within n (AnswerReduction.inBudget lam mu n) → V.decider.size ≤ sigma →
    V.HasPerfectPCC n (AnswerReduction.inAns lam mu n) →
    (output V lam mu sigma).HasPerfectPCC n (bound.eval (AnswerReduction.arg lam mu sigma n))
  /-- **Soundness**, for `n ≥ max C_ar 2` and `λ ≥ 1`: `val*(𝒱^ans_n) > 1 - ε` gives
  `val*(𝒱_n) ≥ 1 - δ(ε, n)`. -/
  soundness : ∀ (V : Verifier ℓ) (lam mu sigma n : ℕ) (ε : ℝ), C ≤ n → 2 ≤ n → 1 ≤ lam →
    V.Within n (AnswerReduction.inBudget lam mu n) → V.decider.size ≤ sigma → 0 < ε →
    1 - ε < (output V lam mu sigma).valStar n (bound.eval (AnswerReduction.arg lam mu sigma n)) →
    1 - AnswerReduction.delta a b lam mu sigma n ε ≤ V.valStar n (AnswerReduction.inAns lam mu n)

end MIPRE
