/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Peel

/-!
# The tactic bundle

Mathlib is a library of Lean modules, and a module re-exports only what it imports with
`public import`; Mathlib imports the tactic modules it uses in proofs privately wherever it
can. A non-module file saw every tactic in its transitive closure; a module of this
repository sees a tactic only along a public path, and `norm_num` reached
`Foundations/Halting/Descriptions.lean` along none (2026-09-28, the module-system PR of
`planning/palomar.md`). So every module that imports part of Mathlib, rather than the
`Mathlib` umbrella, also imports this bundle, which re-exports the common tactics and the
heavy ones the library uses; `scripts/modularize.py` inserts the line and `--check` (CI)
reports a file without it.
-/
