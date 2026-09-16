/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Pipeline.Budget
import MIPRE.Foundations.GapCompression

/-!
# Oracularization, as a hypothesis

Blueprint `thm:oracularization` (paper `oracularization.tex`, `thm:oracle-completeness` and
`thm:oracle-soundness`; ledger node `1.3.5`), stated as the data the theorem provides: the
structure `Oracularization ℓ`. Its inhabitation is the theorem. It is **not** consumed by the
composition `MIPRE.GapCompression.ofPipeline`: in the paper, `Compress` has three steps, and
oracularization is the first step of the *proof* of answer reduction (`thm:ar`, whose
`ComputeAnsVerifier` begins by computing the oracularized verifier). So this structure is the
input to a future proof that `MIPRE.AnswerReduction` is inhabited, and is stated here so that
the four transformations of chapter 6 are all available in one vocabulary.

The reading of the paper's statement in the vocabulary of `MIPRE.Verifier`:

* The oracularized sampler depends only on the input sampler (`sampler`), with the same number
  of levels; the oracularized decider is computed from the input programs and the parameters
  `(λ, β)` (`compute`), where `(λn + 1)^β` is the length against which it parses each answer
  component — the paper's `B_𝒟(n)`, read from the timeout-counter form of the decider there,
  and a parameter here since the ambient model has no such form (`rem:oracularization-repairs`,
  item 4: the truncation is load-bearing and must be explicit).
* The complexity clause bounds the output at index `n` by a polynomial in the parse length, the
  input's budget at `n` and the input's description length, at a degree affine in the input's.
* Completeness: a value-`1` PCC strategy for `𝒱_n` gives one for `𝒱^ora_n`. In the synchronous
  framework the two players of a PCC strategy of the doubled game already measure with the same
  operators, so the paper's extra clause (identical measurement operators) is automatic.
* Soundness: `val*(𝒱^ora_n) > 1 - ε` gives `val*(𝒱_n) ≥ 1 - c √ε` — one square root, per
  `rem:oracularization-repairs`, item 1.
-/

namespace MIPRE

open Cost

namespace Oracularization

/-- The answer bound the oracularized decider parses each component against: `(λn + 1)^β`. -/
abbrev parseBound (lam beta n : ℕ) : ℕ := (lam * n + 1) ^ beta

/-- The argument of the polynomial bounding the output at index `n`. -/
abbrev arg (lam beta n : ℕ) (R : Budget) (s : ℕ) : ℕ :=
  parseBound lam beta n + R.S + R.d + R.D + R.B + s

end Oracularization

/-- **Oracularization** (blueprint `thm:oracularization`) for `ℓ`-level inputs: the data of
the procedure `ComputeOracleVerifier` together with the guarantees of the theorem. An instance
of this structure is the theorem. -/
structure Oracularization (ℓ : ℕ) where
  /-- The constant of the soundness loss `δ(ε) = c √ε`. -/
  c : ℝ
  c_pos : 0 < c
  /-- The polynomial bounding the running times and dimension of the output. -/
  bound : Polynomial ℕ
  /-- The polynomial bounding the length of the answers the output accepts, in the parse
  length. -/
  ansBound : Polynomial ℕ
  /-- The degree multiplier of the output's running times. -/
  deg : ℕ
  /-- The oracularized sampler, a function of the input sampler alone. -/
  sampler : CL.Sampler ℓ → CL.Sampler ℓ
  /-- Its program, computable from the input sampler's program in polynomial time. -/
  samplerProg : PolyTimeFun Prog Prog
  samplerProg_eq : ∀ S : CL.Sampler ℓ, samplerProg S.prog = (sampler S).prog
  /-- The oracularized decider, from the input programs and `(λ, β)`, in polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog) × ℕ × ℕ) Prog
  /-- The output on a normal form input, at parameters `(λ, β)`. -/
  output : Verifier ℓ → ℕ → ℕ → Verifier ℓ
  output_sampler : ∀ (V : Verifier ℓ) (lam beta : ℕ), (output V lam beta).sampler = sampler V.sampler
  output_decider : ∀ (V : Verifier ℓ) (lam beta : ℕ),
    (output V lam beta).decider.prog = compute ((V.sampler.prog, V.decider.prog), lam, beta)
  /-- The complexity clause: within a polynomial of the parse length, the input's budget and
  the input's description length, at degree `deg (k + 1)`. -/
  within : ∀ (V : Verifier ℓ) (lam beta n : ℕ) (R : Budget), V.Within n R →
    (output V lam beta).Within n
      ⟨bound.eval (Oracularization.arg lam beta n R V.size),
        bound.eval (Oracularization.arg lam beta n R V.size),
        bound.eval (Oracularization.arg lam beta n R V.size), deg * (R.k + 1),
        ansBound.eval (Oracularization.parseBound lam beta n)⟩
  /-- **Completeness.** -/
  completeness : ∀ (V : Verifier ℓ) (lam beta n : ℕ),
    V.HasPerfectPCC n (Oracularization.parseBound lam beta n) →
    (output V lam beta).HasPerfectPCC n (ansBound.eval (Oracularization.parseBound lam beta n))
  /-- **Soundness.** `val*(𝒱^ora_n) > 1 - ε` gives `val*(𝒱_n) ≥ 1 - c √ε`. -/
  soundness : ∀ (V : Verifier ℓ) (lam beta n : ℕ) (ε : ℝ), 0 < ε →
    1 - ε < (output V lam beta).valStar n (ansBound.eval (Oracularization.parseBound lam beta n)) →
    1 - c * Real.sqrt ε ≤ V.valStar n (Oracularization.parseBound lam beta n)

end MIPRE
