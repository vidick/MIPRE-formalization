/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Tactic/LdtSimpAttr.lean
-/
import Mathlib.Tactic.Attr.Register

-- Vendoring compile fix (Lean v4.33): the vendored tree is built with the pre-v4.33
-- transparency behaviour (`backward.isDefEq.respectTransparency false`), the option
-- Mathlib sets on declarations affected by Lean v4.33's check; see README.md.
set_option backward.isDefEq.respectTransparency false

/-!
# Registration for the LDT-local simplifier set

This tiny module declares the opt-in `ldt_simp` simp set.  Lemmas are registered
in downstream modules, rather than here, because Lean cannot reliably use a simp
attribute in the same file that registers it.
-/

/-- Opt-in simplification set for stable LDT proof boilerplate. -/
register_simp_attr ldt_simp
