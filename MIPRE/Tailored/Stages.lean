/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Compression
public import MIPRE.Foundations.Pipeline.Introspection
public import MIPRE.Foundations.Pipeline.AnswerReduction
public import MIPRE.Foundations.Pipeline.Repetition

@[expose] public section

/-!
# The three stages of tailored compression, as hypotheses

Paper II of the Aldous–Lyons track (Bowen–Chapman–Vidick, arXiv:2501.00173): question reduction
(`thm:h_level_question_reduciton`, II:5712), answer reduction (`thm:main_ans_red`, II:6883) and
parallel repetition (`thm:repetition`, II:11103), each in value form; the plan is
`planning/aldous-lyons-track.md`, §4 and §5. Each structure is the data its theorem provides,
in the vocabulary of `MIPRE.Introspection`, `MIPRE.AnswerReduction` and `MIPRE.Repetition` —
the same parameters, budgets and soundness losses — with tailored verifiers in and out:

* the output's answer-length calculator is part of the data, as a function of the parameters
  (the paper's `A^λ_qr` and `A_ar` depend on `λ` only, II:5712 and II:6883) or, for repetition,
  of the input's sampler and answer-length calculator;
* the answer-length calculators halt on the sampler's questions (`len_total`), and the budgets
  bound the lengths (`TailoredVerifier.Within`);
* completeness is read in perfect Z-aligned permutation strategies commuting along edges;
* the answer bounds of the existing contracts disappear: a tailored game reads every answer at
  its own length. Repetition keeps one, the bound `B` on the input's lengths, which its
  soundness loss depends on; its parse parameter `β` disappears with it, as the repeated
  linear-constraints processor reads the coordinates' lengths from the input's calculator
  (II:11464–11516).

These are the Phase 0 contracts, written before any construction; the stages that inhabit
them (Phases 2–4) may revise them, as the existing contracts were revised when theirs were
built. `TailoredGapCompression.ofTailoredPipeline`, their composition, is Phase 5.
-/

namespace MIPRE.Tailored

open Cost

/-- **Question reduction** (II:5712) for `ℓ`-level tailored inputs, in value form. On the
plan's Route A its inhabitant is a tailored presentation of the repository's introspection
verifier (`MIPRE.Introspection.seven`), applied to the input padded to constant lengths
(II:6219): the same sampler, an answer-length calculator reading the question's type, and a
linear-constraints processor whose constraints accept exactly what the introspective decider
accepts. -/
structure TailoredIntrospection (ℓ : ℕ) where
  /-- The constant `a` of the soundness loss, normalized to `a ≥ 1`. -/
  a : ℝ
  /-- The exponent `b` of the soundness loss, `0 < b ≤ 1`. -/
  b : ℝ
  one_le_a : 1 ≤ a
  b_pos : 0 < b
  b_le_one : b ≤ 1
  /-- The complexity constant. -/
  C : ℕ
  /-- The introspective sampler, depending only on `λ`. -/
  sampler : ℕ → CL.Sampler 5
  samplerProg : PolyTimeFun ℕ Prog
  samplerProg_eq : ∀ lam : ℕ, samplerProg lam = (sampler lam).prog
  /-- The introspective answer-length calculator, depending only on `λ`. -/
  len : ℕ → Decider
  lenProg : PolyTimeFun ℕ Prog
  lenProg_eq : ∀ lam : ℕ, lenProg lam = (len lam).prog
  /-- The introspective linear-constraints processor, from the input programs and `λ`, in
  polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog × Prog) × ℕ) Prog
  output : Prog × Prog × Prog → ℕ → TailoredVerifier 5
  output_sampler : ∀ (V : Prog × Prog × Prog) (lam : ℕ), (output V lam).sampler = sampler lam
  output_len : ∀ (V : Prog × Prog × Prog) (lam : ℕ), (output V lam).len = len lam
  output_lp : ∀ (V : Prog × Prog × Prog) (lam : ℕ), (output V lam).lp.prog = compute (V, lam)
  /-- The complexity clauses, for every input and index. -/
  within : ∀ (V : Prog × Prog × Prog) (lam n : ℕ),
    (output V lam).Within n (Introspection.budget C lam n)
  /-- `|LP^intro| ≤ C λ^C`, for every input. -/
  lp_size : ∀ (V : Prog × Prog × Prog) (lam : ℕ), (output V lam).lp.size ≤ C * (lam + 1) ^ C
  len_total : ∀ lam n : ℕ, LenTotal (len lam) n ((sampler lam).dim n)
  /-- **Completeness.** For a `λ`-bounded input. -/
  completeness : ∀ (V : TailoredVerifier ℓ) (lam n : ℕ), V.IsBounded lam →
    V.HasPerfectZPC (2 ^ n) → (output V.progs lam).HasPerfectZPC n
  /-- **Soundness.** For a `λ`-bounded input and `n ≥ 1`: `val*(𝒱^intro_n) > 1 - ε` gives
  `val*(𝒱_{2^n}) ≥ 1 - δ(ε, n)`. -/
  soundness : ∀ (V : TailoredVerifier ℓ) (lam n : ℕ) (ε : ℝ), V.IsBounded lam → 1 ≤ n →
    0 < ε → 1 - ε < (output V.progs lam).valStar n →
    1 - Introspection.delta a b lam n ε ≤ V.valStar (2 ^ n)

/-- **Answer reduction** (II:6883) for `ℓ`-level tailored inputs, in value form: the paper's
tailored PCP (purification, oracularization, triangulation, decoupling, the output indicator
and its decoupled Cook–Levin description, the low-degree test), with the parameters
`(λ, μ, σ)` and the budgets of `MIPRE.AnswerReduction`. -/
structure TailoredAnswerReduction (ℓ : ℕ) where
  /-- The constant `a` of the soundness loss, normalized to `a ≥ 1`. -/
  a : ℝ
  /-- The exponent `b` of the soundness loss, `0 < b ≤ 1`. -/
  b : ℝ
  one_le_a : 1 ≤ a
  b_pos : 0 < b
  b_le_one : b ≤ 1
  /-- The threshold above which the completeness and soundness clauses hold. -/
  C : ℕ
  /-- The base polynomial of the output bound `AnswerReduction.outBound`. -/
  bound : Polynomial ℕ
  /-- The base degree; the output's degree is `AnswerReduction.outDegree deg μ`. -/
  deg : ℕ
  /-- The answer-reduced sampler, a function of the input sampler and `(λ, μ, σ)`. -/
  sampler : CL.Sampler ℓ → ℕ → ℕ → ℕ → CL.Sampler (max (ℓ + 2) 5)
  samplerProg : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog
  samplerProg_eq : ∀ (S : CL.Sampler ℓ) (lam mu sigma : ℕ),
    samplerProg (S.prog, lam, mu, sigma) = (sampler S lam mu sigma).prog
  /-- The answer-reduced answer-length calculator, depending only on `(λ, μ, σ)`. -/
  len : ℕ → ℕ → ℕ → Decider
  lenProg : PolyTimeFun (ℕ × ℕ × ℕ) Prog
  lenProg_eq : ∀ lam mu sigma : ℕ, lenProg (lam, mu, sigma) = (len lam mu sigma).prog
  /-- The answer-reduced linear-constraints processor, from the input programs and
  `(λ, μ, σ)`, in polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog × Prog) × ℕ × ℕ × ℕ) Prog
  output : TailoredVerifier ℓ → ℕ → ℕ → ℕ → TailoredVerifier (max (ℓ + 2) 5)
  output_sampler : ∀ (V : TailoredVerifier ℓ) (lam mu sigma : ℕ),
    (output V lam mu sigma).sampler = sampler V.sampler lam mu sigma
  output_len : ∀ (V : TailoredVerifier ℓ) (lam mu sigma : ℕ),
    (output V lam mu sigma).len = len lam mu sigma
  output_lp : ∀ (V : TailoredVerifier ℓ) (lam mu sigma : ℕ),
    (output V lam mu sigma).lp.prog = compute (V.progs, lam, mu, sigma)
  /-- The complexity clause, as `MIPRE.AnswerReduction.within`. -/
  within : ∀ (V : TailoredVerifier ℓ) (lam mu sigma n : ℕ),
    V.Within n (AnswerReduction.inBudget lam mu n) → V.size ≤ sigma →
    (output V lam mu sigma).Within n
      (Budget.uniform (AnswerReduction.outBound bound lam mu sigma n)
        (AnswerReduction.outDegree deg mu))
  len_total : ∀ (V : TailoredVerifier ℓ) (lam mu sigma n : ℕ),
    LenTotal (len lam mu sigma) n ((sampler V.sampler lam mu sigma).dim n)
  /-- **Completeness**, for `n ≥ C` and `λ, μ ≥ 1`. -/
  completeness : ∀ (V : TailoredVerifier ℓ) (lam mu sigma n : ℕ), C ≤ n → 1 ≤ lam → 1 ≤ mu →
    V.Within n (AnswerReduction.inBudget lam mu n) → V.size ≤ sigma →
    V.HasPerfectZPC n → (output V lam mu sigma).HasPerfectZPC n
  /-- **Soundness**, for `n ≥ max C 2` and `λ ≥ 1`: `val*(𝒱^ans_n) > 1 - ε` gives
  `val*(𝒱_n) ≥ 1 - δ(ε, n)`. -/
  soundness : ∀ (V : TailoredVerifier ℓ) (lam mu sigma n : ℕ) (ε : ℝ), C ≤ n → 2 ≤ n →
    1 ≤ lam → V.Within n (AnswerReduction.inBudget lam mu n) → V.size ≤ sigma → 0 < ε →
    1 - ε < (output V lam mu sigma).valStar n →
    1 - AnswerReduction.delta a b lam mu sigma n ε ≤ V.valStar n

namespace TailoredRepetition

/-- The argument of the polynomial bounding the repeated verifier at index `n`: the
repetition count, the input's budget and description length, the parameters, and `10^{R.k}`,
the input's cost on the dimension query (as in `MIPRE.Repetition.arg`, without the parse
length, which a tailored verifier does not need). -/
abbrev arg (lam tau n : ℕ) (R : Budget) (s : ℕ) : ℕ :=
  Repetition.reps lam tau n + R.S + R.d + R.D + R.B + s + lam + tau + n + 10 ^ R.k

end TailoredRepetition

/-- **Parallel repetition** (II:11103) of `ℓ`-level tailored verifiers, in value form and
direct rather than anchored: `k(n) = Repetition.reps λ τ n` independent copies, the lengths
added coordinate by coordinate, the constraints of each coordinate padded with zeros to the
whole answer (II:11464–11516), and the soundness of the vendored direct repetition theorem
(`MIPRE.Repetition.quantumValue_repeat_le`). The paper's anchored, entanglement-preserving
form is not needed on the plan's route (§4.1). -/
structure TailoredRepetition (ℓ : ℕ) where
  /-- The constant of the soundness exponent. -/
  c : ℝ
  c_pos : 0 < c
  /-- The polynomial bounding the running times and dimension of the output. -/
  bound : Polynomial ℕ
  /-- The degree multiplier of the output's running times. -/
  deg : ℕ
  /-- The repeated sampler, a function of the input sampler and `(λ, τ)`. -/
  sampler : CL.Sampler ℓ → ℕ → ℕ → CL.Sampler ℓ
  samplerProg : PolyTimeFun (Prog × ℕ × ℕ) Prog
  samplerProg_eq : ∀ (S : CL.Sampler ℓ) (lam tau : ℕ),
    samplerProg (S.prog, lam, tau) = (sampler S lam tau).prog
  /-- The repeated answer-length calculator, a function of the input sampler, the input
  answer-length calculator and `(λ, τ)`. -/
  len : CL.Sampler ℓ → Decider → ℕ → ℕ → Decider
  lenProg : PolyTimeFun (Prog × Prog × ℕ × ℕ) Prog
  lenProg_eq : ∀ (S : CL.Sampler ℓ) (L : Decider) (lam tau : ℕ),
    lenProg (S.prog, L.prog, lam, tau) = (len S L lam tau).prog
  /-- The repeated linear-constraints processor, from the input programs and `(λ, τ)`, in
  polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog × Prog) × ℕ × ℕ) Prog
  output : TailoredVerifier ℓ → ℕ → ℕ → TailoredVerifier ℓ
  output_sampler : ∀ (V : TailoredVerifier ℓ) (lam tau : ℕ),
    (output V lam tau).sampler = sampler V.sampler lam tau
  output_len : ∀ (V : TailoredVerifier ℓ) (lam tau : ℕ),
    (output V lam tau).len = len V.sampler V.len lam tau
  output_lp : ∀ (V : TailoredVerifier ℓ) (lam tau : ℕ),
    (output V lam tau).lp.prog = compute (V.progs, lam, tau)
  /-- The complexity clause: within a polynomial of `k(n)`, the input's budget and the input's
  description length, at degree `deg (k + 1)`, with lengths at most `k(n)` times the input's. -/
  within : ∀ (V : TailoredVerifier ℓ) (lam tau n : ℕ) (R : Budget), V.Within n R →
    (output V lam tau).Within n
      ⟨bound.eval (TailoredRepetition.arg lam tau n R V.size),
        bound.eval (TailoredRepetition.arg lam tau n R V.size),
        bound.eval (TailoredRepetition.arg lam tau n R V.size), deg * (R.k + 1),
        Repetition.reps lam tau n * R.B⟩
  /-- The repeated calculator halts where the input's does. -/
  len_total : ∀ (V : TailoredVerifier ℓ) (lam tau n : ℕ),
    LenTotal V.len n (V.sampler.dim n) →
      LenTotal (output V lam tau).len n ((output V lam tau).sampler.dim n)
  /-- **Completeness.** -/
  completeness : ∀ (V : TailoredVerifier ℓ) (lam tau n : ℕ),
    V.HasPerfectZPC n → (output V lam tau).HasPerfectZPC n
  /-- **Soundness.** For an input whose lengths are at most `B`, `val*(𝒱_n) ≤ 1 - ε` gives
  `val*(𝒱^rep_n) ≤ exp(-c ε^13 k(n) / (B + 1))`; the constant absorbs the factor between the
  bound on each kind of variable and the bound on the answers. -/
  soundness : ∀ (V : TailoredVerifier ℓ) (lam tau n B : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    LenBound V.len n B → V.valStar n ≤ 1 - ε →
    (output V lam tau).valStar n ≤ Repetition.soundBound c ε (Repetition.reps lam tau n) B

end MIPRE.Tailored

end
