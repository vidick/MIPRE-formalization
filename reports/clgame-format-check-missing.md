# `clGame` was missing `fig:ld-decider`'s format check, and was therefore vacuous

**Status: found and repaired 2026-09-18**, while scoping the seeded-CL adapter (Chunk 3 of
`planning/next-chunks.md`, issue #105's successor). Found in Lean merged by #98, not in the
paper and not in the blueprint, both of which were correct.

## The defect

`MIPRE.LIDT.CL.accepts` (`MIPRE/Background/LIDT/CLGame.lean`) was a single `match` over the
question pair and the answer pair, with seven handled cases and a catch-all

```lean
  | _, _, _, _ => true
```

The catch-all was intended for `fig:ld-decider`'s closing line, "In all cases where no action
is indicated, accept", which covers the two cross type pairs `(ALine, DLine)` and
`(DLine, ALine)`. But it also caught every pair whose *answer format does not match its
question's type*, and the paper's decider **rejects** those. The figure's first step is

> Check that `(t_A, x_A)` and `(t_B, x_B)` are correctly formatted [...] and that `a_A` and
> `a_B` also have the correct length, as can be inferred from the table above

and the paragraph introducing the figure says so again, without qualification:

> If the answers returned by the players do not fit this format the decision procedure
> rejects.

Three `rfl`s, generic in `F`, `m`, `d`, `ldc`, confirmed the reading before anything was
changed: `accepts hm (.aline u₀ s) (.point x) (.values a) (.values b)`,
`accepts hm (.point u) (.point x) (.apolys f) (.apolys g)` and the cross pair all reduced to
`true`. Only the third should.

## Why it mattered

The test was vacuous, and the theorem stated about it was false.

Take the strategy, one-dimensional and deterministic, in which both players answer

* `point u ↦ values (fun _ => h u)` for an arbitrary `h : F^m → F`,
* `aline _ _ ↦ values 0` and `dline _ _ _ ↦ values 0` — the wrong format for both.

Every ordered type pair is then accepted: `(Point, Point)` because both players compute `h` at
the same `u`; every pair involving a line question because the line player's answer is in the
point format, so the four line-versus-point cases of the `match` do not apply and the catch-all
fires; the two cross pairs likewise. So the strategy has value exactly `1`, i.e. `ε = 0`.

Now read `thm:lidt-cl-soundness` at `ldc = 1` on it. The conclusion supplies a projective
measurement `G^B` with outcomes polynomials of individual degree at most `d`, whose evaluation
at a uniform `u` is `δ`-consistent with A's point measurement at `u`, with `δ = 0`. A's point
measurement is deterministic with outcome `h u`, and the strategy is a product state on a
one-dimensional space, so zero inconsistency forces `G^B` to be deterministic at a single
polynomial `p` with `p(u) = h u` for **every** `u ∈ F^m`. Choose `h` that is not such a
polynomial — the indicator of `u = 0` has individual degree `q - 1`, so any `d < q - 1` does —
and the conclusion fails. The theorem was false as a statement about `clGame`.

What is machine-checked here is the defect itself — the three `rfl`s above, now inverted into
the three regression theorems below. The vacuity argument in this section is a hand argument
about a strategy that is no longer expressible against the repaired predicate, and it is
recorded as reasoning, not as a checked Lean counterexample.

Nothing downstream consumed `clGame` yet, so no other result was affected; the adapter this was
found while scoping would have been the first consumer, and it would have been proving the
adapter's value transfer *into* a game that could not be lost.

## The repair

`fig:ld-decider`'s two steps are now two definitions, which is the shape that keeps them from
being conflated again:

* `Question.fmtOk : Question F m → Answer F m d ldc → Bool` — the table at the top of the
  figure: `Point` takes `values`, `ALine` takes `apolys`, `DLine` takes `dpolys`;
* `subtests` — the three numbered tests and the closing "accept", unchanged from the old
  `match`;
* `accepts hm x y a b := x.fmtOk a && y.fmtOk b && subtests hm x y a b`.

Three theorems pin the behaviour that was wrong and the behaviour that had to survive:
`accepts_aline_values_eq_false`, `accepts_point_apolys_eq_false` and `accepts_aline_dline`.
They are named in `def:lidt-cl`'s `\lean{}` list, so `scripts/lean-coverage.py` will not let a
reorganization drop them silently.

## Root cause, so it does not happen again

The two clauses read almost identically in English — one says "reject if the format is wrong",
the other "accept if no action is indicated" — and they sit three paragraphs apart in the
source, the first in the prose before the figure and the second in the figure's last line. A
single `match` with one catch-all is the natural Lean shape for the figure's numbered list, and
it silently absorbs the first clause into the second.

The general lesson is narrower than "read the paper more carefully", because the paper *was*
read: the module docstring written in #98 quotes the figure and works through one place where
the formalization is deliberately *stricter* than the paper (line membership), so attention was
on the subtests. It is that **a decision predicate with a catch-all that accepts should be
suspected of being vacuous, and the suspicion is cheap to discharge**: ask what the constant
strategy does. For a test whose whole content is that answers have structure, the constant
strategy is the first thing an adversarial reader tries, and here it takes three `rfl`s.
