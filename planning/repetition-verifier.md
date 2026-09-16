# Inhabiting `Repetition ℓ`: the plan

Status 2026-09-16, written when `MIPRE.Repetition ℓ` (`Foundations/Pipeline/Repetition.lean`)
was stated and consumed by `GapCompression.ofPipeline` (#85), before anything supplied it.
The supply is `thm:parallel-repetition`: the game-level direct repetition theorem
`thm:direct-repetition-q` (`MIPRE.Repetition.quantumValue_repeat_le`, vendored), packaged at
the level of normal form verifiers. This file is the decomposition, in the order the pieces
are worth doing, and what each has to prove. It is the analogue of `h4-assembly.md` §4 for
this item.

## What the structure asks for

`Repetition ℓ` (read it before this file) has, for an input `V : Verifier ℓ` and parameters
`(λ, τ, β)`, with `k = 2^{τ(|λ|+|n|)}` repetitions and parse length `B = 2^{β(|λ|+|n|)}`:

1. `sampler : CL.Sampler ℓ → ℕ → ℕ → CL.Sampler ℓ` with its program a `PolyTimeFun` of
   `(S.prog, λ, τ)`; `compute : PolyTimeFun ((Prog × Prog) × ℕ × ℕ × ℕ) Prog` for the
   decider; `output V λ τ β : Verifier ℓ` with `output_sampler`, `output_decider`.
2. `within`: from `V.Within n R`, the output is within `bound.eval (k + B + R.S + R.d + R.D +
   R.B + |V|)` at degree `deg (R.k + 1)`, with answers rejected beyond
   `ansBound.eval (k + B)`.
3. `completeness`: `V.HasPerfectPCC n B → output.HasPerfectPCC n (ansBound.eval (k + B))`.
4. `soundness`: `0 < ε ≤ 1`, `V.valStar n B ≤ 1 - ε` give
   `output.valStar n (ansBound.eval (k + B)) ≤ exp(-c ε^13 k / (B + 1))`.

The counts are powers of two because a program of the ambient model writes
`2^{τ(|λ|+|n|)}` by a bit walk (`lamProg` does `2^{2|n|}`); the paper's `(λn)^τ` would need
multiplication at run time. Nothing downstream can tell the difference
(`Pipeline.pow_le_reps`, `parseBound_le`).

## The pieces

**R1 — game level (pure mathematics).** `Foundations/TensorFamily.lean`: the `k`-fold
Kronecker product of a family of matrices as a matrix over `Fin k → ι`
(`fun v w => ∏ i, M i (v i) (w i)`): multiplicative, star-compatible, trace of a family is
the product of the traces, sums of families. `Background/Repetition/TensorPower.lean`:
`SyncStrategy.tensorPow S k : SyncStrategy (H.repeat k)` with `value = S.value ^ k` and PCC
from PCC (the tracial state on `ℂ^{d^k}` is the product of the ones on `ℂ^d`, after
`Fin k → Fin d ≃ Fin (d^k)`); its relabeling to `(G.repeat k).doubled` for a strategy of
`G.doubled` (the tags are read off the first coordinate; the support of the doubled repeated
distribution is inside the image), giving **game-level completeness**: a value-`1` PCC
strategy of `G.doubled` gives one of `(G.repeat k).doubled`. **Game-level soundness**: from
`quantumValue_repeat_le`, for `G` with answers `Verifier.Answers B` (card at most `3^{B+1}`,
by `Answers.getElem?_injective`), `quantumValue G ≤ 1 - ε` gives `quantumValue (G.repeat k) ≤
Repetition.soundBound c' ε k B` with `c' = c / (1 + 2 log 3)`; the exponent is monotone in
`ε`, so the hypothesis need not be tight.

**R2 — the repeated sampler's CL functions.** `Fin (k * s) ≃ Fin k × Fin s`; the `k`-fold
direct sum of `L : CLFun 𝔽₂ (Fin s) ℓ` as a `CLFun 𝔽₂ (Fin (k*s)) ℓ` (iterate
`CLFun.directSum` along the blocks, or define it directly on the presentation), exactly on
the whole space (`ExactlyOn.directSum`); `clDist` of the direct sum is the product of the
`clDist`s of the blocks, which is what makes the repeated game the direct repetition; and the
blockwise descriptions of `truncate j`, `mapOfPrefix`, `factorOfPrefix` of the direct sum,
which the sampler program's `runs_*` clauses need.

**R3 — the programs.** (a) Bit walks: `2^{e(|λ|+|n|)}` as a binary numeral (a
`lamProg`-style walk over the bits of `λ`, embedded in the program, and of `n`, the input),
and the same numeral with the bits of `s` prepended, which is `k · s` — the `dimension`
query. (b) Block splitting: a walk over a list with a binary counter (`decProg`) cutting it
into blocks of `s` bits; the sampler answers `marginal`, `linear`, `factor` queries by
splitting the vectors into blocks, running `S` on each block (`callVar`, the input sampler
embedded as a literal subprogram) and concatenating; the count of blocks is not checked
(`runs_*` only speak of well-formed inputs) but the program halts on everything. (c) The
decider: `s` from `S`'s dimension query, `|x| = |y| = k · s` checked against the numeral with
`eqBitsProg`, `x` and `y` split into blocks, `a` and `b` parsed as self-delimiting tuples
(`parseProg`, `Halting/Serial.lean`), each component's length checked against `B` (walk with
`decProg` on `B`), `D` run on every coordinate (`callVar`, embedded), accept iff all accept.
No universal machine: the input programs are embedded as literals, so the cost of a call is
the callee's own cost, and the degree in the input size is preserved. (d) `compute` and
`samplerProg` build the program text from the encodings, as `wrapBuildProg` does
(`Compressor.lean`, the `pK/pC/pL/pE` builders). (e) Cost: every walk is polynomial in its
input, the `k` calls to `D` cost `k · R.D · (|d| + 1)^{R.k}`, and the accounting is the
`wrapCoreCost` pattern of `Halting/WrapperCost.lean`.

**R4 — assembly.** `Background/Repetition/Verifier.lean`: the equivalence of games —
`(output V λ τ β).game n (ansBound.eval (k + B))` has `quantumValue` equal to
`(V.game n B).repeat k`'s: questions `Fin (k*s) → 𝔽₂ ≃ Fin k → (Fin s → 𝔽₂)` with the
distribution matching by R2, answers the strings of length at most the bound, of which the
encoded `k`-tuples of strings of length at most `B` are the accepted ones
(`quantumValue_extendAnswers` for the rest, `quantumValue_eq_of_equiv` for the relabeling);
then `completeness` and `soundness` from R1, `within` from R3(e), and the instance. Blueprint:
proof-level `\leanok` on `thm:parallel-repetition` with the guard.

## Order and size

R1 first (it is the mathematics the vendored theorem does not provide, and it stands on its
own: every lemma there is a blueprint statement). R2 next. R3 is the bulk, O4-sized; (a)–(c)
are independent programs and can be separate pull requests. R4 last. Each piece validated
against `Repetition ℓ` as the consumer before the next.
