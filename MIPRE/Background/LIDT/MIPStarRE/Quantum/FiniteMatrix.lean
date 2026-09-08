/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteMatrix.lean
-/
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.Basic
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.Order
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.TracePairing
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace

/-!
# Finite-dimensional matrix layer for the MIP*=RE project

This aggregate module preserves the historical `MIPStarRE.Quantum.FiniteMatrix`
import path while the underlying facts are organized into mathematical leaves:
basic operator and trace facts, positive-semidefinite order and cone facts,
real trace-pairing representation, block-diagonal order facts, and normalized
trace/projector material.

## References

The declarations re-exported here collect the finite-dimensional matrix and PSD
facts from Mathlib for the project's quantum layer and the LDT development
formalizing `references/ldt-paper/`.
-/
