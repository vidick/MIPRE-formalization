/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core.lean, from a snapshot of the `main` branch supplied on 2026-09-25 (archive, no
commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
module
public import MIPRE.Background.LiehrTsirelson.Upstream.Core.FiniteProbability
public import MIPRE.Background.LiehrTsirelson.Upstream.Core.Correlation
public import MIPRE.Background.LiehrTsirelson.Upstream.Core.Game
public import MIPRE.Background.LiehrTsirelson.Upstream.Core.Measurement
public import MIPRE.Background.LiehrTsirelson.Upstream.Core.Strategy
public import MIPRE.Background.LiehrTsirelson.Upstream.Core.Value
public import MIPRE.Background.LiehrTsirelson.Upstream.Core.Entanglement

@[expose] public section

/-!
# Paper-facing core facade

A thin import surface for the canonical semantic core: finite probability,
correlations, games, measurements, strategies and the three correlation sets,
payoff and the two values, Schmidt rank and `Ent`, and the B23 strategy
predicates.

This file declares nothing of its own.
-/

end
