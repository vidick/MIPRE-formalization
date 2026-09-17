# The decoupled 5SAT describer (`lem:decoupled-5sat`): the plan

Written 2026-09-17, immediately after `thm:succinct-sat` was proved (#88, PRs #89–#91). This
is A1 of the answer-reduction track: the first consumer of `SuccinctCookLevin`, and the form
in which answer reduction's PCP reads the decider. The paper's statement and proof are
`prop:explicit-succinct-deciders` in `answer_reduction.tex`, `sec:succinct-deciders`.

## Why this first

`thm:answer-reduction` declares seven inputs. Three of them — `thm:pcp-decider`, `thm:qld`
and `lem:self-dual-basis` — have no Lean at all, and `thm:qld` is a chapter-3 campaign of its
own. `lem:decoupled-5sat` is the one input whose own dependencies are now all discharged:
its `\uses` is `thm:succinct-sat`, `def:succinct-3sat`, `def:decider`, and nothing else. It
is also the consumer `thm:succinct-sat`'s statement was validated against in S0, so proving
it is the first real test of whether that validation held.

## The construction, from the paper

Run the 3SAT describer on `(𝒟, n, T, Q, σ, x, y)` to get `C₃` on `3r₀ + 3` inputs, where
`r₀ = m` is the index width of `thm:succinct-sat`. Put `ℓ₀ = ⌈log 2T⌉`, `L = 2^ℓ₀`,
`R = 2^r₀`. Since `R ≥ 4T` and `L < 4T`, we have `L ≤ R` and `ℓ₀ ≤ r₀`, so an `ℓ₀`-bit index
compared with an `r₀`-bit one is zero-padded and `i₂ + 2T < 4T ≤ R` does not overflow.

The output circuit `C` reads `i₁, i₂` of `ℓ₀` bits, `i₃, i₄, i₅` of `r₀` bits and five signs,
and accepts when any of nine conditions holds:

| # | condition | what it forces |
|---|---|---|
| 1 | `C₃(i₃, i₄, i₅, o₃, o₄, o₅) = 1` | the 3SAT formula on `(w₁, w₂, w₃)` |
| 2 | `i₁ < 2T ∧ i₁ = i₃ ∧ o₁ ≠ o₃` | `w₁` agrees with `a` below `2T` |
| 3 | `i₂ < 2T ∧ i₃ = i₂ + 2T ∧ o₂ ≠ o₃` | `w₁` agrees with `b` on `[2T, 4T)` |
| 4 | `i₁ ≥ 2T ∧ i₁` even `∧ o₁ = 1` | `a` is blank-padded above `2T` |
| 5 | `i₁ ≥ 2T ∧ i₁` odd `∧ o₁ = 0` | likewise |
| 6 | `i₂ ≥ 2T ∧ i₂` even `∧ o₂ = 1` | `b` is blank-padded above `2T` |
| 7 | `i₂ ≥ 2T ∧ i₂` odd `∧ o₂ = 0` | likewise |
| 8 | `i₃ = i₄ ∧ o₃ ≠ o₄` | `w₁ = w₂` |
| 9 | `i₄ = i₅ ∧ o₄ ≠ o₅` | `w₂ = w₃` |

**The parities in rows 4–7 are a repair the audit campaign made**, and they are the one place
where a careless transcription silently breaks completeness. Blocks are `0`-indexed and the
blank encodes as `10`, so the honest padding `enc(⊔)^{L/2 − T}` starts at the even index `2T`
and puts `1` at *even* indices and `0` at odd ones. The pre-repair text had it the other way
round, which forces `(01)^{L/2−T}` and is violated by the honest assignment. Our `tapeBits`
already agrees with the repaired parity: `tapeBits ap j` past the end of `ap` is the blank
cell `(true, false)`, so `true` at even `j` and `false` at odd `j`. Nothing to adapt, but
nothing to take on trust either.

Why rows 8 and 9 read as equalities of whole blocks rather than of single bits: for a fixed
`i₁, i₂, i₃` the signs `o₁, o₂, o₃` range over all of `{0,1}³`, so the first three literals of
the decoupled clause cover every pattern and the clause is satisfied exactly when the last two
literals are. That is the argument the paper makes once and uses for the whole circuit.

## The route in Lean, and why it avoids composing circuits

The obvious reading — take `C₃` as a black box and OR it with a circuit for rows 2–9 — needs
circuit-level composition: relabelling inputs, concatenating gate lists with index shifts, and
re-proving `WellFormed` (fan-out at most two, terminal output) through both. That is a few
hundred lines of index arithmetic for no mathematical content.

Instead, stay in the formula layer, which S3 already built. `descCirc` is by definition the
flattening of the formula `descFml`, so:

* **`Fml.remap f`** renames input variables, a `map` over the post-order list, with
  `eval (remap f φ) x = eval φ (x ∘ f)`. The 3SAT describer's inputs `0 .. 3r₀ + 2` sit in the
  five-block layout at `ρ k = k + 2ℓ₀` for `k < 3r₀` and `k + 2ℓ₀ + 2` above, because the two
  answer indices come first and the two answer signs are the first two of the five.
* **`linkFml`** is rows 2–9 in the existing bit-vector vocabulary: `ltConst` for `i < 2T`,
  `eqFields` on zero-padded indices for `i₁ = i₃`, `addConstRel` for `i₃ = i₂ + 2T`, the head
  bit for parity, and `xor` for `o ≠ o'`.
* The describer is `or (remap ρ descFml) linkFml`, flattened once with `toCircuitF`. Its
  well-formedness and input count come from the flattener, as they did in S3, and its gate
  bound comes from the program's time bound, as it did in S4.

## `ℓ₀` is the one new arithmetic

`ℓ₀ T = ⌈log 2T⌉` is pinned by `ℓ₀_spec` (`2T ≤ 2^ℓ₀ < 4T` for `T ≥ 1`), so it cannot be
replaced by the cheaper `Nat.size T + 1`, which is right except at powers of two, where it
gives `4T` and violates the strict bound. Written with `Nat.size`,

    ℓ₀ T = if T is a power of two then Nat.size T else Nat.size T + 1,

and as a program the test is `T.bits.dropLast` being all false, since `Nat.bits` carries no
trailing zeros. That is a `take` against a unary length minus one, and a `foldl`.

## The pieces

**A1a — `Fml.remap`.** The renaming, its `eval`, `InputsLt` and `size` lemmas, and its
program (a `map` over the post-order list, so the cost is immediate).

**A1b — `linkFml` and its exactness.** The eight rows as a formula over the five-block input
layout, and the lemma that its evaluation on `clauseInput5` of a clause is the disjunction of
the eight decoded conditions. This is where the parity repair is discharged against
`tapeBits`.

**A1c — the bridge.** `c ∈ C.formula5 ℓ₀ r₀` iff the 3-clause of `(l₃, l₄, l₅)` is in
`descCirc.formula3 r₀` or `c` satisfies one of the eight conditions.

**A1d — the description.** `(∃ w₁ w₂ w₃, Sat a b w₁ w₂ w₃) ↔ EncodesAccepted`, by the paper's
argument: rows 8 and 9 collapse the three auxiliary blocks to one `w`, rows 2 and 3 tie `w`'s
first `4T` bits to `a` and `b`, rows 4–7 pin the padding, and then item 1 of
`thm:succinct-sat` (`extendsAnswers_iff`) closes it.

**A1e — assembly.** The program, `ℓ₀`, `r₀`, `s₀` with their bounds, and the
`DecoupledDescriber` instance, with the blueprint's proof-level mark and the axiom guard.

## What this does not do

It does not touch `thm:pcp-decider`, which additionally needs the arithmetization and the
quantum low-degree test; and it does not inhabit `AnswerReduction 5`, which needs that PCP,
oracularization, and the four normalization obligations that `lem:answer-reduction-supply`
lists. Those are separate items.
