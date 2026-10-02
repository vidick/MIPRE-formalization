/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Core/
DDistinct.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Statements
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Core.DDistinct

@[expose] public section

/-!
# Section 12 pasting: distinct tuple distribution bound

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Core/DDistinct.lean` in the port
of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored file is classical throughout: its one theorem, `ldDnoteq` (`prop:ld-dnoteq`),
bounds the total variation distance between the uniform distribution on `k`-tuples of points
and the uniform distribution on distinct `k`-tuples by `k² / q`. It mentions no state, operator
or measurement, so it is not ported: this file imports the vendored file, and ported files name
`ldDnoteq` through an explicit `open MIPStarRE.LDT.Pasting (ldDnoteq)` list.

The file mirrors the vendored module so that the ported tree keeps the vendored import graph: it
imports `Co/Pasting/Statements.lean`, the counterpart of the vendored file's import of
`Pasting/Statements`, and the ported files that import the vendored `DDistinct` import it.

## Not ported

- `ldDnoteq`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

end
