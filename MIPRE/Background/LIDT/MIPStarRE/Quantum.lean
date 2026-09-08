/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum.lean
-/
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteHilbert
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.Basic
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.Order
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.TracePairing
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace
import MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteConicDuality
import MIPRE.Background.LIDT.MIPStarRE.Quantum.ProjectorONB
import MIPRE.Background.LIDT.MIPStarRE.Quantum.Measurement

-- Mathlib 4.31 header checks require this for this aggregate module.
set_option linter.style.header false

/-!
# Quantum infrastructure

This root module provides the finite-dimensional Hilbert-space, matrix, projector,
and measurement infrastructure used by the low individual degree test
formalization.
-/
