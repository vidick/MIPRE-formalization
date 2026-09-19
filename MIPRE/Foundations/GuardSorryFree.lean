/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Lean

/-!
# The axiom guard

`#guard_sorry_free a, b, c` fails the build if any of the named constants depends on `sorryAx`.
It is what makes a proof-level `\leanok` in the blueprint a checked claim rather than an
assertion: `scripts/lean-coverage.py` requires the set of names guarded in the project's
axiom-guard files to be exactly the set the blueprint marks that way.

It lives in a module of its own, importing nothing but `Lean`, so that every guard file can use
it --- `MIPRE/Axioms.lean` for this project's own results and the four
`MIPRE/Background/*/Axioms.lean` for the vendored trees and for the developments whose imports
are cheapest there. Before this module the elaborator was defined inside `MIPRE/Axioms.lean`,
which the Background guard files do not import, so they had to fall back on
`#guard_msgs in #print axioms` --- sensitive to how the axiom list is line-wrapped and to which
of the standard axioms a proof happens to use, which is exactly wrong for guarding a long list
of declarations of mixed kinds.
-/

open Lean Elab Command in
/-- `#guard_sorry_free a, b, c` fails the build if any of the named constants depends on
`sorryAx`. Used rather than `#guard_msgs in #print axioms` because it is insensitive to how the
axiom list is line-wrapped and to which of the standard axioms a proof happens to use: some
guarded names use only `propext` and `Quot.sound`, some are axiom-free, and a definition's list
generally differs from that of a theorem about it. -/
elab "#guard_sorry_free " ids:ident,* : command => do
  for id in ids.getElems do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let ax ← liftCoreM <| collectAxioms n
    if ax.contains ``sorryAx then
      throwErrorAt id "{n} depends on sorryAx, but the blueprint marks its proof \\leanok"
