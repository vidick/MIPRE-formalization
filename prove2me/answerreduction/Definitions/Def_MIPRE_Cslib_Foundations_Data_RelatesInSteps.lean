/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

/-
Vendored from CSLib (https://github.com/leanprover/cslib), upstream file
  Cslib/Foundations/Data/RelatesInSteps.lean
at commit 3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc (2026-08-03); fetched 2026-08-05.

CSLib cannot currently be a Lake dependency of this project: its MultiTape development
requires Lean >= v4.33.0-rc1, while this project pins v4.32.0. See
`planning/tm-infrastructure.md` (decision D1). Delete this copy and `require` CSLib once
the toolchains align.

Adaptations (the only differences from upstream):
* module-system markers removed: the `module` line, `public import` -> `import`, and the
  `@[expose] public section` line (replaced by the `set_option` lines below);
* `set_option autoImplicit true` / `set_option relaxedAutoImplicit true` added to restore
  the upstream Lean defaults (this project's lakefile disables both);
* `import Cslib.Init` dropped (only needed under the module system); in its stead,
  `import Mathlib.Data.Nat.Notation` added — upstream receives the `ℕ` notation through
  `Cslib.Init`, and `Mathlib.Logic.Relation` alone does not provide it.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Cslib/Foundations/Data/RelatesInSteps.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-! # Relations Across Steps

This file defines `Relation.RelatesInSteps` (and `Relation.RelatesWithinSteps`).
These are inductively defines propositions that communicate whether a relation forms a
chain of length `n` (or at most `n`) between two elements.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

variable {α : Type*} {r : α → α → Prop} {a b c : α}

namespace Relation

/--
A relation `r` relates two elements of `α` in `n` steps
if there is a chain of `n` pairs `(t_i, t_{i+1})` such that `r t_i t_{i+1}` for each `i`,
starting from the first element and ending at the second.
-/
inductive RelatesInSteps (r : α → α → Prop) : α → α → ℕ → Prop
  | refl (a : α) : RelatesInSteps r a a 0
  | tail (t t' t'' : α) (n : ℕ) (h₁ : RelatesInSteps r t t' n) (h₂ : r t' t'') :
      RelatesInSteps r t t'' (n + 1)

lemma RelatesInSteps.zero {a b : α} (h : RelatesInSteps r a b 0) : a = b := by
  cases h
  rfl

@[simp]
lemma RelatesInSteps.zero_iff {a b : α} : RelatesInSteps r a b 0 ↔ a = b := by
  constructor
  · exact RelatesInSteps.zero
  · intro rfl
    exact RelatesInSteps.refl a

end Relation
