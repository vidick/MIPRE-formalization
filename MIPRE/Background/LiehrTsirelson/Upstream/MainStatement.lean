/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/MainStatement.lean, from a snapshot of the `main` branch supplied on 2026-09-25
(archive, no commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core
/-!
# The three terminal propositions

Shapes audited in `ReferenceOnly/TERMINAL_STATEMENT_SPEC.md`; mathematical
authority `Blueprint/Nodes/B28-Separation/Math.tex` (quantitative separation) and
`Blueprint/Nodes/B30-Tsirelson-Consequence/Math.tex`, `thm:tsirelson` (proper
inclusion and strict game-value separation).

This module contains **no proof** and **no duplicate core definition**: each
proposition is built only from imported canonical declarations.  Nothing is
proved here — B28 must supply `thm:separation` (the shape of
`QuantitativeSeparationStatement`).  As of 2026-07-30 the B30 deduction
itself IS proved, conditionally: `Tsirelson.Nodes.B30.tsirelson_of_separation`
(`Tsirelson/Nodes/B30/Conditional.lean`) derives
`NegativeTsirelsonStatement ∧ GameValueSeparationStatement` from
`QuantitativeSeparationStatement`, so the campaign's remaining obligation for
the headline results is exactly B28.
-/

namespace Tsirelson

/-- **B28 quantitative separation.**  Quantified over a generic `GameSig`, whose
bundled game already carries the nonemptiness of all four alphabets, so no
separate cardinality-positivity hypotheses are needed. -/
def QuantitativeSeparationStatement : Prop :=
  ∃ g : GameSig, valStar g.game ≤ (1 : ℝ) / 2 ∧ valCo g.game = 1

/-- **B30 negative answer to Tsirelson's problem**: a proper inclusion
`C_qa(n,k) ⊂ C_qc(n,k)` for some `n, k ≥ 1`. -/
def NegativeTsirelsonStatement : Prop :=
  ∃ n k : ℕ, 1 ≤ n ∧ 1 ≤ k ∧ Cqa n k ⊂ Cqc n k

/-- **B30 strict game-value separation**: a square game whose finite-dimensional
value is strictly below its commuting value, the latter being one. -/
def GameValueSeparationStatement : Prop :=
  ∃ (n k : ℕ) (G : Game n k), 1 ≤ n ∧ 1 ≤ k ∧ valStar G < valCo G ∧ valCo G = 1

end Tsirelson
