/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/InductionParameterBounds/Averaging.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.DistributionPMF
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries
public import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Averaging

@[expose] public section

/-!
# Section 6 — Induction parameter averaging bounds

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Averaging.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

The vendored file is classical throughout: Jensen's inequality for `x ↦ x^{1/n}` against a
uniform distribution (`avgOver_uniform_rpow_one_div_le_rpow_avg`, the average of `(f a)^{1/n}` is
at most `(E f)^{1/n}`), and the two comparisons
`m · (sliceConditioningLoss · x)^c ≤ (m + 1) · x^c` and
`m² · (sliceConditioningLoss · x)^c ≤ (m + 1)² · x^c` for `0 ≤ c ≤ 1`, which replace the ambient
factor `m` by `m + 1` in the induction step. None of them mentions a state, an operator or a
measurement, so none is ported: this file imports the vendored file, and the ported files of
`MainInductionStep/Theorems` name its declarations through explicit
`open MIPStarRE.LDT.MainInductionStep (…)` lists (the Jensen lemma lives in that namespace, not
in `MIPStarRE.LDT`).

The file mirrors the vendored module so that the ported tree keeps the vendored import graph: it
imports `Co/Basic/DistributionPMF.lean` and
`Co/MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean`, the counterparts of
the vendored file's imports, and the ported files that import the vendored `Averaging` import it.

## Not ported

- `avgOver_uniform_rpow_one_div_le_rpow_avg`: classical, imported.
- `m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow`: classical, imported.
- `m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

end
