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
* The ambient input budget `inBudget λ μ n` bounds the sampler and dimension by
  `(λn + 1)^μ`, and the decider and answer length by `2^{(λn + 1)^μ}`, together with
  `𝒟.size ≤ σ`; the complexity clause asks `𝒮.size ≤ σ` as well (below). This explicitly
  adapts the paper's absolute-time hypothesis `TIME_𝒟(n) ≤ (2^{λn})^μ` to the ambient
  input-size degree: the logarithm of the permitted absolute decider time on legal inputs is
  polynomial in the sampler's budget when `λ, n ≥ 1`.
  The ambient sampler also has input-size degree `μ`: on inputs of size `O(L)`, where
  `L = (λn + 1)^μ`, its cost can be `L * O(L)^μ`. A universal polynomial in `L + σ` alone
  does not bound that uniformly in `μ`. We therefore use the explicit ambient output bound
  `outBound bound λ μ σ n = (bound.eval (L + σ + λ + n))^(μ + 1)`, at degree
  `outDegree deg μ = deg * (μ + 1)`, and reject longer answers. This is a conservative
  adaptation of the paper's absolute-time contract, not a proof of that adaptation or of
  answer reduction. Compression fixes `μ`, so its final bound remains polynomial.
* The complexity clause bounds the input sampler's description by `σ` too. The output
  simulates the input sampler (the oracularized sampler and the answer-reduced decider both
  call it through the universal machine), and the simulation's overhead is polynomial in the
  size of the program simulated as well as in its running time; the paper's `thm:ar` bounds
  only `|𝒟|`, and its `poly((λn)^μ, σ)` running times hold for a sampler of bounded size, as
  the introspective sampler that compression feeds it is. Completeness and soundness do not
  need the bound and keep the paper's hypothesis.
* For `n ≥ C_ar` (the paper's threshold): a value-`1` PCC strategy for `𝒱_n` gives one for
  `𝒱^ans_n` (completeness), and `val*(𝒱^ans_n) > 1 - ε` gives `val*(𝒱_n) ≥ 1 - δ(ε, n)` with
  `δ(ε, n) = σ^a((λn)^{μa} ε^b + (λn)^{-μb})` (soundness), for universal constants `a, b`, with
  `a ≥ 1` assumed as in `Introspection`. The blueprint's statement has no threshold; the
  paper's does, and it is kept.

Answer alphabets: `𝒱_n` is read with answers of length at most the decider's time bound
`2^{(λn + 1)^μ}`, the length the PCP decodes to, and `𝒱^ans_n`
with answers of length at most its own time bound, beyond which its decider rejects.
-/

namespace MIPRE

open Cost

namespace AnswerReduction

/-- The answer bound answer reduction reads its input at: the decider's time bound
`2^{(λn + 1)^μ}`. -/
abbrev inAns (lam mu n : ℕ) : ℕ := 2 ^ ((lam * n + 1) ^ mu)

/-- The budget answer reduction asks of its input at index `n`: sampler within `(λn + 1)^μ`,
questions of dimension at most `(λn + 1)^μ`, decider within `2^{(λn + 1)^μ}`, at degree `μ`,
and no answer longer than `2^{(λn + 1)^μ}` accepted. -/
def inBudget (lam mu n : ℕ) : Budget :=
  ⟨(lam * n + 1) ^ mu, (lam * n + 1) ^ mu, inAns lam mu n, mu, inAns lam mu n⟩

/-- The argument of the polynomial bounding the output at index `n`: `(λn + 1)^μ + σ + λ + n`.
For `λ, μ ≥ 1` and `n ≥ 2`, the paper's regime, `λ + n ≤ 2 (λn)^μ` and the last two terms change
nothing; they are there for the indices where `(λn + 1)^μ` does not grow with `n` — `λ = 0`,
`μ = 0`, or `n = 0` — at which the output still computes the PCP's parameters from `n` and `λ`. -/
abbrev arg (lam mu sigma n : ℕ) : ℕ := (lam * n + 1) ^ mu + sigma + lam + n

/-- The ambient output bound, retaining the input sampler's degree `μ`. For fixed `μ`,
this is a polynomial in the base argument. -/
abbrev outBound (bound : Polynomial ℕ) (lam mu sigma n : ℕ) : ℕ :=
  (bound.eval (arg lam mu sigma n)) ^ (mu + 1)

/-- The output's input-size degree after simulating a degree-`μ` input sampler. -/
abbrev outDegree (deg mu : ℕ) : ℕ := deg * (mu + 1)

/-- A sampler with coefficient `L` and degree `μ`, called on an input of encoded size
at most `B - 1`, costs at most `B^(μ + 1)` when `L ≤ B`. This is the arithmetic reason
for the extra power in `outBound`; supplying the actual compiler calls remains part of
constructing an `AnswerReduction`. -/
theorem sampler_cost_le_power {L B s mu : ℕ} (hL : L ≤ B) (hs : s + 1 ≤ B) :
    L * (s + 1) ^ mu ≤ B ^ (mu + 1) := by
  calc L * (s + 1) ^ mu ≤ B * B ^ mu :=
      Nat.mul_le_mul hL (Nat.pow_le_pow_left hs mu)
    _ = B ^ (mu + 1) := by rw [pow_succ, Nat.mul_comm]

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
  /-- The universal base polynomial for the ambient output bound `outBound`. -/
  bound : Polynomial ℕ
  /-- The universal base degree; the output's input-size degree is `outDegree deg μ`. -/
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
  /-- The complexity clause: an input within `inBudget λ μ n` with `|𝒮|, |𝒟| ≤ σ` gives an
  output within `outBound bound λ μ σ n` at degree `outDegree deg μ`, rejecting longer
  answers. -/
  within : ∀ (V : Verifier ℓ) (lam mu sigma n : ℕ),
    V.Within n (AnswerReduction.inBudget lam mu n) → V.size ≤ sigma →
    (output V lam mu sigma).Within n
      (Budget.uniform (AnswerReduction.outBound bound lam mu sigma n)
        (AnswerReduction.outDegree deg mu))
  /-- **Completeness**, for `n ≥ C_ar`. -/
  completeness : ∀ (V : Verifier ℓ) (lam mu sigma n : ℕ), C ≤ n →
    V.Within n (AnswerReduction.inBudget lam mu n) → V.decider.size ≤ sigma →
    V.HasPerfectPCC n (AnswerReduction.inAns lam mu n) →
    (output V lam mu sigma).HasPerfectPCC n (AnswerReduction.outBound bound lam mu sigma n)
  /-- **Soundness**, for `n ≥ max C_ar 2` and `λ ≥ 1`: `val*(𝒱^ans_n) > 1 - ε` gives
  `val*(𝒱_n) ≥ 1 - δ(ε, n)`. -/
  soundness : ∀ (V : Verifier ℓ) (lam mu sigma n : ℕ) (ε : ℝ), C ≤ n → 2 ≤ n → 1 ≤ lam →
    V.Within n (AnswerReduction.inBudget lam mu n) → V.decider.size ≤ sigma → 0 < ε →
    1 - ε < (output V lam mu sigma).valStar n (AnswerReduction.outBound bound lam mu sigma n) →
    1 - AnswerReduction.delta a b lam mu sigma n ε ≤ V.valStar n (AnswerReduction.inAns lam mu n)

end MIPRE
