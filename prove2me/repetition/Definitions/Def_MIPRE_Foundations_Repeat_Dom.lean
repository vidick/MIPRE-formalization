/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Dom.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Tactic

/-!
# Domination by a monomial in the parameters and the input size

The time bounds of the repeated verifier (`thm:parallel-repetition`) have the shape
`c (W + 1)^m X^{e (K + 1)}`: `W` a number dominating all the parameters at index `n` (the
argument `MIPRE.Repetition.arg`), `X = |d| + 1` the size of the input and `K` the input's
degree. `Dom W X K c m e v` says `v` is below such a monomial. The costs of the programs are
sums and products of quantities each of which is below `W`, below `X`, or a constant, and the
combinators here — `add`, `mul`, `pow`, `ofLeW`, `ofLeX`, `const` — assemble the exponents,
so that the final `c, m, e` are produced by the chain rather than computed by hand. The
exponent of `X` is counted in units of `K + 1`, so that a bound `X^{e (K + 1)}` with `e`
independent of `K` is what comes out, as the degree clause of the theorem needs.
-/

namespace MIPRE.Repeat

/-- `v ≤ c (W + 1)^m X^{e (K + 1)}`. -/
def Dom (W X K c m e v : ℕ) : Prop := v ≤ c * (W + 1) ^ m * X ^ (e * (K + 1))

namespace Dom

variable {W X K : ℕ}

end Dom

end MIPRE.Repeat
