/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Verifier

@[expose] public section

/-!
# Gap-preserving compression of tailored verifiers, as a hypothesis

Paper II of the Aldous–Lyons track (Bowen–Chapman–Vidick, arXiv:2501.00173), Theorem
`thm:compression` (II:1852), proved as `thm:h_level_compression` (II:5643), in the value form
that the paper's Remark II:1876 calls the content of its proofs; the plan is
`planning/aldous-lyons-track.md`, §4.1 and §4.4. The structure `TailoredGapCompression ℓ` is
the data the theorem provides, as `MIPRE.GapCompression` is for the existing pipeline; its
inhabitation is the theorem (Phase 5 of the plan, from the three stage contracts of
`MIPRE.Tailored.Stages`), and the halting reduction is to consume it (Phase 1).

What differs from `MIPRE.GapCompression`:

* the verifiers are tailored, so the output has two components depending on `λ` only — the
  sampler `S^λ` and the answer-length calculator `L^λ` — and the compression procedure computes
  the linear-constraints processor;
* the answer-length calculator never fails on the sampler's questions (`len_total`, the paper's
  "never decodes to `error`", II:1863), which the halting protocol spends once (II:1965, item 3:
  when the machine has halted, the game accepts every well-formatted answer);
* the lengths it outputs are bounded (`len_bound`), in place of `output_rejects_long`: the
  canonical decider rejects every answer of another length;
* completeness is read in perfect Z-aligned permutation strategies commuting along edges
  (`TailoredVerifier.HasPerfectZPC`), not in PCC strategies;
* soundness is the value form, as there: `val*(𝒱_{2^n}) ≤ 1/2` gives `val*(𝒱'_n) ≤ 1/2`. The
  paper states it in entanglement form, `Ent(𝒱'_n, 1/2) ≥ max{Ent(𝒱_{2^n}, 1/2), 2^{2^{λn}-1}}`,
  which needs the anchored parallel repetition theorem and the almost-synchronous rounding; the
  plan's §4.1 records why the value form is taken, and how the halting argument then gets its
  base case from Lin's search branch instead.

The level `ℓ` is a parameter: the fixed point of the halting protocol has input and output at
the same level, that of `S^λ`.
-/

namespace MIPRE.Tailored

open Cost

/-- **Gap-preserving compression of tailored verifiers** (II:1852, value form): the data of a
compression procedure together with the guarantees of the theorem. An instance of this
structure is the theorem. -/
structure TailoredGapCompression (ℓ : ℕ) where
  /-- The universal constant above which the guarantees hold. -/
  C₀ : ℕ
  /-- The compressed sampler `S^λ`, depending only on `λ`. -/
  sampler : ℕ → CL.Sampler ℓ
  /-- Its program, computable from `λ` in time polynomial in the length of `λ`. -/
  samplerProg : PolyTimeFun ℕ Prog
  samplerProg_eq : ∀ lam : ℕ, samplerProg lam = (sampler lam).prog
  /-- The compressed answer-length calculator `L^λ`, depending only on `λ`. -/
  len : ℕ → Decider
  /-- Its program, computable from `λ` in time polynomial in the length of `λ`. -/
  lenProg : PolyTimeFun ℕ Prog
  lenProg_eq : ∀ lam : ℕ, lenProg lam = (len lam).prog
  /-- `Compress`: from the three programs of a tailored verifier and `λ`, the program of the
  compressed linear-constraints processor, in polynomial time. -/
  compress : PolyTimeFun ((Prog × Prog × Prog) × ℕ) Prog
  /-- The output on any input is a tailored verifier with the compressed sampler, the
  compressed answer-length calculator and the compressed linear-constraints processor. -/
  output : Prog × Prog × Prog → ℕ → TailoredVerifier ℓ
  output_sampler : ∀ (V : Prog × Prog × Prog) (lam : ℕ), (output V lam).sampler = sampler lam
  output_len : ∀ (V : Prog × Prog × Prog) (lam : ℕ), (output V lam).len = len lam
  output_lp : ∀ (V : Prog × Prog × Prog) (lam : ℕ), (output V lam).lp.prog = compress (V, lam)
  /-- The polynomial `poly(n, λ)` bounding the running times of the output at index `n`, the
  dimension of the compressed sampler, and the lengths. -/
  bound : Polynomial ℕ
  /-- The degree, in the size of the input, of the running times of the output. -/
  deg : ℕ
  sampler_time : ∀ lam n : ℕ, (sampler lam).TimeBoundAt n (bound.eval (n + lam)) deg
  sampler_dim : ∀ lam n : ℕ, (sampler lam).dim n ≤ bound.eval (n + lam)
  len_time : ∀ lam n : ℕ, (len lam).TimeBoundAt n (bound.eval (n + lam)) deg
  lp_time : ∀ (V : Prog × Prog × Prog) (lam n : ℕ),
    (output V lam).lp.TimeBoundAt n (bound.eval (n + lam)) deg
  /-- The lengths are at most `poly(n, λ)`. -/
  len_bound : ∀ lam n : ℕ, LenBound (len lam) n (bound.eval (n + lam))
  /-- The answer-length calculator halts on every question of the sampler. -/
  len_total : ∀ lam n : ℕ, LenTotal (len lam) n ((sampler lam).dim n)
  /-- **Completeness.** For a `λ`-bounded input and `n ≥ C₀`: a perfect Z-aligned permutation
  strategy commuting along edges for `𝒱_{2^n}` gives one for `𝒱'_n`. -/
  completeness : ∀ (V : TailoredVerifier ℓ) (lam n : ℕ), V.IsBounded lam → C₀ ≤ n →
    V.HasPerfectZPC (2 ^ n) → (output V.progs lam).HasPerfectZPC n
  /-- **Soundness**, value form. For a `λ`-bounded input and `n ≥ C₀`: `val*(𝒱_{2^n}) ≤ 1/2`
  implies `val*(𝒱'_n) ≤ 1/2`. -/
  soundness : ∀ (V : TailoredVerifier ℓ) (lam n : ℕ), V.IsBounded lam → C₀ ≤ n →
    V.valStar (2 ^ n) ≤ 1 / 2 → (output V.progs lam).valStar n ≤ 1 / 2

end MIPRE.Tailored

end
