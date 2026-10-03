/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Statements
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures
public import MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries

@[expose] public section

/-!
# Section 6 — Induction parameter bound preliminaries

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

The vendored file is classical throughout: the point-line reduction of the base case
(`throughPoint_eq_zeroPoint_of_m_eq_one`, at `m = 1` every axis-parallel line in a direction is
the one through the zero point), the real-variable comparisons `min x 1 ≤ x^c` for `0 ≤ c ≤ 1`
and `x^c ≤ 1 → x ≤ 1` for `c > 0`, the ratio bound `d/q ≤ 1` (`dq_ratio_le_one`) and
`min ε 1 ≤ mainInductionError params k ε δ γ` at `m = 1`. None of them mentions a state, an
operator or a measurement, so none is ported: this file imports the vendored file, and the ported
files of `MainInductionStep/Theorems` name its declarations through explicit
`open MIPStarRE.LDT.MainInductionStep (…)` lists. Inside `MIPRE.LIDT.Co` the dotted name
`MainInductionStep.X` resolves to the Co namespace, so these names are reached through that list
or fully qualified, not as `MainInductionStep.dq_ratio_le_one`.

The file mirrors the vendored module so that the ported tree keeps the vendored import graph: it
imports `Co/MainInductionStep/Statements.lean` and `Co/Test/StrategyFailures.lean`, the
counterparts of the vendored file's imports, and the ported files that import the vendored
`Preliminaries` import it.

## Not ported

- `throughPoint_eq_zeroPoint_of_m_eq_one`: classical, imported.
- `min_le_rpow_of_nonneg_of_exponent_le_one`: classical, imported.
- `le_one_of_rpow_le_one`: classical, imported.
- `dq_ratio_le_one`: classical, imported.
- `min_eps_one_le_mainInductionError_of_m_eq_one`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

end
