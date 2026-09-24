# The explicit separation: findings for the companion paper

Written 2026-09-24, while formalizing `thm:separation` (#222). Read against the companion
repository `vidick/MIPRE-proof` at `a459dee`: `paper/intro.tex`, the separation section of
`paper/recursive.tex`, and the live ledger nodes `1.8.8`–`1.8.11`, replayed with
`scripts/ledger-sync.py`'s event handling. Nothing is copied here. The Lean is
`MIPRE.separation` (`MIPRE/Tsirelson.lean`), resting on
`MIPRE/Foundations/Tsirelson/Separation.lean`, with only `propext`, `Classical.choice` and
`Quot.sound`.

## 1. The introduction says more than the proof gives

- It promises an *explicit correlation* in `C_qc` but not in `C_qa`. The separation theorem and
  ledger node `1.8.11` give only the *existence* of such a correlation. That correlation comes
  from a value-`1` commuting-operator strategy that the proof does not construct; the
  introduction's own later remark about CEP says as much.
- It calls the separating game *synchronous*. Nothing in the separation section proves that,
  and the early-accept branch of the separating decider accepts every answer pair when it
  fires. That includes unequal answers to equal questions.

Suggested repair: "an explicit game … hence the existence of a correlation …", and drop
"synchronous", or prove it.

## 2. Details of the separating construction that are not checked

- `λ`-boundedness of the separating verifier is asserted only by analogy with the halting
  verifier.
- Its decider lacks the bounded input-length check that the halting construction has. So the
  claim that its timeout dominates the running time of the machine `N` fails on over-long
  inputs. Ledger node `1.8.8` repairs this.
- The identification of the separating verifier with the compressed verifier, with the
  answer-alphabet merge and padding, is used but not stated. Ledger node `1.8.9` repairs this.
- There is no remark that the choice of the timeout constant is non-circular.

## 3. A shorter proof of the theorem's conclusion

Kleene's recursion theorem proves the conclusion from two inputs:

- the halting reduction to `val*` (the main theorem);
- the upper semidecider for `ω_co` (the ledger's `1.8.4`).

Take the machine that halts exactly when `ω_co(g(itself)) < 1`, where `g` is the reduction.
If it halted, `val* = 1` would force `ω_co = 1`, and so it would not halt. So it does not halt:
`val* ≤ 1/2` and `ω_co = 1`. No Schmidt-rank clause, no anchored repetition and no early-accept
branch is needed.

The game is not the paper's `G^sep`. It is explicit in the same sense, because it comes from
self-reference. The paper's footnote showing that the gap holds for infinitely many
non-halting machines is the closest statement in the source. The paper may want this as a
remark, since the Schmidt-rank machinery is currently used only for this theorem.
