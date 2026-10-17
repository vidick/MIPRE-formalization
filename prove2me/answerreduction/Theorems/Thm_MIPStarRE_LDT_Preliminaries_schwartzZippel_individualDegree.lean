/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/Polynomials.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean (statement stub of MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials

open MIPStarRE
open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open Finset Fintype
open scoped BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (g h : polyFunc m K d) (hneq : g ≠ h) :
    polynomialAgreementProbability m K g.1 h.1 ≤ ((m * d : ℕ) : ℚ≥0) / Fintype.card K := by sorry
