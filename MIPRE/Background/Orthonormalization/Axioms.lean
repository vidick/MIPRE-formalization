/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Main
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Corollaries
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Fourier
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.FullAlgebra
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.II1Factor
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Main
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Corollaries

/-!
# Axiom audit for the orthonormalization theorem

What the vendored development proves outright, and what it does not, is the thing to know
before citing any of it, and the distinction is invisible in the source: every statement
reads like a theorem. This file makes it mechanical. It fails to build if one of the
unconditional results acquires an axiom, and equally if one of the four open targets is
closed upstream without this repository noticing — in which case the blueprint's
`thm:orthonormalization` and `rem:orthonormalization-scope` are what need updating.

Unconditional, in order of generality: every von Neumann algebra on a
finite-dimensional space; `B(H)` for arbitrary `H`; and II₁ factors whose trace and state
are of trace-class form. The general case is `povm_orthogonalization_of_structure`, which
is a theorem about the implication only: its hypothesis `MvNStructureTheory` bundles eight
facts of von Neumann algebra structure theory that Mathlib does not have, and no term of
that type is constructed anywhere.
-/

/-! ## Unconditional -/

/-- info: 'Orthogonalization.povm_orthogonalization_finDim_vn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.povm_orthogonalization_finDim_vn

/--
info: 'Orthogonalization.povm_orthogonalization_fullAlgebra_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Orthogonalization.povm_orthogonalization_fullAlgebra_general

/-- info: 'Orthogonalization.povm_orthogonalization_II₁Factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.povm_orthogonalization_II₁Factor

/-- info: 'Orthogonalization.povm_orthogonalization_hilbert_finDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.povm_orthogonalization_hilbert_finDim

/-- info: 'Orthogonalization.pvm_almost_commute_finDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.pvm_almost_commute_finDim

/-- info: 'Orthogonalization.almost_commuting_unitaries_finDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.almost_commuting_unitaries_finDim

/-! ## Conditional on the structure-theory interface

The implication is proved; its hypothesis is not. -/

/-- info: 'Orthogonalization.povm_orthogonalization_of_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.povm_orthogonalization_of_structure

/-! ## The open targets

Upstream's *signed statements*: the unconditional general forms, stated so that each tier
can be compared against them, and `sorry` until the interface above is discharged. Nothing
proved in the development depends on them. -/

/-- info: 'Orthogonalization.povm_orthogonalization' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.povm_orthogonalization

/-- info: 'Orthogonalization.povm_orthogonalization_hilbert' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.povm_orthogonalization_hilbert

/-- info: 'Orthogonalization.pvm_almost_commute' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.pvm_almost_commute

/-- info: 'Orthogonalization.almost_commuting_unitaries' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Orthogonalization.almost_commuting_unitaries
