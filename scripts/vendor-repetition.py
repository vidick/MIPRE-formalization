#!/usr/bin/env python3
"""Vendor the external formalizations of parallel repetition and orthonormalization.

Usage (from the repository root):

    python scripts/vendor-repetition.py \
        --cr-source <path to a commuting-repetition clone> --cr-commit <sha> \
        --tp-source <path to a ten-proofs clone> --tp-commit <sha> \
        --or-source <the same commuting-repetition clone> --or-commit <sha>

``--or`` vendors the ``orthogonalization/`` Lean package of the commuting-repetition
repository (de la Salle's POVM orthogonalization, blueprint ``thm:orthonormalization``)
into ``MIPRE/Background/Orthonormalization/``; it is a second package in the same clone
as ``--cr``, not a second repository.

The script

* checks that each clone is at the requested commit and has no local changes;
* deletes and recreates ``MIPRE/Background/Repetition/CommutingRepetition/`` and
  ``MIPRE/Background/Repetition/TenProofs/`` (both destinations are wholly generated;
  local hand edits there are lost on purpose -- see ``planning/repetition-port.md``);
* copies, from commuting-repetition, the import closure of the root modules
  (``CR_ROOTS`` below), rewriting ``import CommutingRepetition.X`` to
  ``import MIPRE.Background.Repetition.CommutingRepetition.X``, together with the
  upstream ``NOTICE`` file;
* copies, from ten-proofs, the single module ``QuantumParallelRepetition.lean`` and, as
  an audit aid, the Mathlib-only statement file
  ``ComparatorChallenges/G_QuantumParallelRepetition.lean`` (as ``.lean.expected``);
* prepends a provenance header to every copied Lean file and, unless
  ``--no-auto-implicit`` is given, inserts ``set_option autoImplicit true`` after the
  import block (both upstreams compile with Lean's default ``autoImplicit = true``,
  which this repository turns off in ``lakefile.toml``);
* splits ``QuantumParallelRepetition.lean`` (71k lines upstream) into a chain of parts
  of at most ``SPLIT_MAX_LINES`` lines each, ``QuantumParallelRepetition/Part01.lean``,
  ``Part02.lean``, ..., cut only between the top-level ``noncomputable section`` blocks
  of its one namespace, and leaves ``QuantumParallelRepetition.lean`` as the module that
  imports every part (so its module name, which the bridge imports, is unchanged). The
  Palomar registry caps every Lean file at 10,000 physical lines
  (``planning/palomar.md``). ``--resplit`` redoes the split on the vendored copy
  without a clone;
* refreshes the generated block of each destination's ``README.md``.

Afterwards run ``lake exe mk_all`` to refresh ``MIPRE.lean``, then ``lake build``.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

DEST_ROOT = Path("MIPRE/Background/Repetition")

BEGIN_MARK = "<!-- BEGIN GENERATED (scripts/vendor-repetition.py) -->"
END_MARK = "<!-- END GENERATED -->"

# The vendored commuting-repetition modules imported by the bridge in
# MIPRE/Background/Repetition/; everything they transitively import is vendored,
# nothing else (upstream's audit-node map Fidelity/Nodes.lean in particular is not).
CR_ROOTS = (
    "CommutingRepetition.MainTheorem.Main",
    "CommutingRepetition.StatementBridge",
)


@dataclass(frozen=True)
class Fix:
    """A recorded compile fix, applied after copying: ``old`` must occur exactly once in the
    vendored file ``path`` (relative to the destination directory) and is replaced by
    ``new``. Every fix is also described in the directory's README under "Local
    deviations from upstream"."""

    path: str
    old: str
    new: str
    reason: str


TP_FIX_SCHMIDT_OLD = """theorem exists_proofSchmidtDecomposition
"""

TP_FIX_SCHMIDT_NEW = """-- Vendoring compile fix (Lean v4.33): this proof needs the pre-v4.33 transparency
-- behaviour (its closing `simpa` no longer sees through `Matrix.toEuclideanLin`);
-- see README.md.
set_option backward.isDefEq.respectTransparency false in
theorem exists_proofSchmidtDecomposition
"""


CR_FIX_PROD_LE_ONE_OLD = """    Finset.prod_le_one
      (fun i _ => G.payoff_nonneg (xs i) (ys i) (as i) (bs i))
      (fun i _ => G.payoff_le_one (xs i) (ys i) (as i) (bs i))
"""

CR_FIX_PROD_LE_ONE_NEW = """    -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one` lost its nonnegativity
    -- hypothesis; the version with it is `Finset.prod_le_one₀`. See README.md.
    Finset.prod_le_one₀
      (fun i _ => G.payoff_nonneg (xs i) (ys i) (as i) (bs i))
      (fun i _ => G.payoff_le_one (xs i) (ys i) (as i) (bs i))
"""

CR_FIX_MONOTONE_OLD = """          mul_le_mul_of_nonneg_left
            (Finset.prod_le_one
              (fun j _ => G.payoff_nonneg _ _ _ _)
              (fun j _ => G.payoff_le_one _ _ _ _))
"""

CR_FIX_MONOTONE_NEW = """          -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one₀` is the version with
          -- the nonnegativity hypothesis. See README.md.
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_one₀
              (fun j _ => G.payoff_nonneg _ _ _ _)
              (fun j _ => G.payoff_le_one _ _ _ _))
"""

CR_FIX_SCALAR_OLD = """      exact Finset.prod_le_one hfmem hfmem1
"""

CR_FIX_SCALAR_NEW = """      -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one₀` is the version with
      -- the nonnegativity hypothesis. See README.md.
      exact Finset.prod_le_one₀ hfmem hfmem1
"""

CR_FIX_CSTAR_CONT1_OLD = """      · exact M.continuous_traceState.comp (continuous_mul_right _)
      · exact M.continuous_traceState.comp (continuous_mul_left _)
"""

CR_FIX_CSTAR_CONT1_NEW = """      -- Vendoring compile fix (Mathlib v4.35): `continuous_mul_right`/`_left` are now
      -- `continuous_mul_const`/`continuous_const_mul`. See README.md.
      · exact M.continuous_traceState.comp (continuous_mul_const _)
      · exact M.continuous_traceState.comp (continuous_const_mul _)
"""

CR_FIX_CSTAR_CONT2_OLD = """    · exact M.continuous_traceState.comp (continuous_mul_left _)
    · exact M.continuous_traceState.comp (continuous_mul_right _)
"""

CR_FIX_CSTAR_CONT2_NEW = """    -- Vendoring compile fix (Mathlib v4.35): `continuous_mul_left`/`_right` are now
    -- `continuous_const_mul`/`continuous_mul_const`. See README.md.
    · exact M.continuous_traceState.comp (continuous_const_mul _)
    · exact M.continuous_traceState.comp (continuous_mul_const _)
"""

CR_FIX_CSTAR_NORM_OLD = """    exact IsSelfAdjoint.le_algebraMap_norm_self hYsa
"""

CR_FIX_CSTAR_NORM_NEW = """    -- Vendoring compile fix (Mathlib v4.35): `IsSelfAdjoint.le_algebraMap_norm_self` takes
    -- the element explicitly. See README.md.
    exact IsSelfAdjoint.le_algebraMap_norm_self Y hYsa
"""

CR_FIX_CLOSED_OLD = """  have hp := (ContinuousLinearMap.nonneg_iff_isPositive T).mp h0
"""

CR_FIX_CLOSED_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `nonneg_iff_isPositive` takes its operator
  -- implicitly. See README.md.
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp h0
"""

OR_FIX_JOINT1_OLD = """  have hp := (ContinuousLinearMap.nonneg_iff_isPositive x).mp h
"""

OR_FIX_JOINT1_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `nonneg_iff_isPositive` takes its operator
  -- implicitly. See README.md.
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp h
"""

OR_FIX_JOINT2_OLD = """  have hp := (ContinuousLinearMap.le_def x 1).mp h
"""

OR_FIX_JOINT2_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `le_def` takes its operators implicitly.
  -- See README.md.
  have hp := ContinuousLinearMap.le_def.mp h
"""

OR_FIX_PERTURB_OLD = """  have h := conj_le_conj (IsSelfAdjoint.le_algebraMap_norm_self hb) r
"""

OR_FIX_PERTURB_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `IsSelfAdjoint.le_algebraMap_norm_self` takes
  -- the element explicitly. See README.md.
  have h := conj_le_conj (IsSelfAdjoint.le_algebraMap_norm_self b hb) r
"""

TP_FIX_NONNEG_OLD = """    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr h_positive
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ h_nonneg).mpr
  exact (ContinuousLinearMap.le_def _ _).mpr
"""

TP_FIX_NONNEG_NEW = """    -- Vendoring compile fix (Mathlib v4.35): `nonneg_iff_isPositive` and `le_def` take
    -- their operators implicitly. See README.md.
    ContinuousLinearMap.nonneg_iff_isPositive.mpr h_positive
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ h_nonneg).mpr
  exact ContinuousLinearMap.le_def.mpr
"""

TP_FIX_MULVEC_OLD = """  apply (hA.dotProduct_mulVec_zero_iff x).mp
"""

TP_FIX_MULVEC_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `dotProduct_mulVec_zero_iff` takes the vector
  -- implicitly. See README.md.
  apply hA.dotProduct_mulVec_zero_iff.mp
"""

TP_FIX_PROD_A_OLD = """  unfold fullHistoryHiddenAliceWeight
  rw [← Fintype.prod_sum]
  apply Finset.prod_le_one
"""

TP_FIX_PROD_A_NEW = """  unfold fullHistoryHiddenAliceWeight
  rw [← Fintype.prod_sum]
  -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one₀` is the version with the
  -- nonnegativity hypothesis. See README.md.
  apply Finset.prod_le_one₀
"""

TP_FIX_PROD_B_OLD = """  unfold fullHistoryHiddenBobWeight
  rw [← Fintype.prod_sum]
  apply Finset.prod_le_one
"""

TP_FIX_PROD_B_NEW = """  unfold fullHistoryHiddenBobWeight
  rw [← Fintype.prod_sum]
  -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one₀` is the version with the
  -- nonnegativity hypothesis. See README.md.
  apply Finset.prod_le_one₀
"""

OR_FIX_POSITIVE_OLD = """      ((nonneg_iff_isPositive s).mp hs0)
"""

OR_FIX_POSITIVE_NEW = """      -- Vendoring compile fix (Mathlib v4.35): `nonneg_iff_isPositive` takes its operator
      -- implicitly. See README.md.
      (nonneg_iff_isPositive.mp hs0)
"""


CR_FIX_SUBMODEL_OLD = """    exact IsSelfAdjoint.le_algebraMap_norm_self hYsa
"""

CR_FIX_SUBMODEL_NEW = """    -- Vendoring compile fix (Mathlib v4.35): `IsSelfAdjoint.le_algebraMap_norm_self` takes
    -- the element explicitly; dot notation supplies it. See README.md.
    exact hYsa.le_algebraMap_norm_self
"""

CR_FIX_CFC_OLD = """    ContinuousFunctionalCalculus ℝ (L2Q K →L[ℂ] L2Q K) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
"""

CR_FIX_CFC_NEW = """    ContinuousFunctionalCalculus ℝ (L2Q K →L[ℂ] L2Q K) IsSelfAdjoint :=
  -- Vendoring compile fix (Mathlib v4.35): the algebra must be named for the `IsSelfAdjoint`
  -- predicate's `Star` instance to unify. See README.md.
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := L2Q K →L[ℂ] L2Q K)
"""

CR_FIX_ARENA_A_OLD = """include hxA in
theorem Ame_isPos (i : I) (a : A) : IsPosElem (lft M (Ame M h kA xA hxA i a)) := by
"""

CR_FIX_ARENA_A_NEW = """include hxA in
-- Vendoring compile fix (Mathlib v4.35): the `map_sum` step of this proof exceeds the default
-- heartbeat budget (its instance search unfolds the arena's algebra); it elaborates within
-- a larger one. See README.md.
set_option maxHeartbeats 1600000 in
theorem Ame_isPos (i : I) (a : A) : IsPosElem (lft M (Ame M h kA xA hxA i a)) := by
"""

CR_FIX_ARENA_B_OLD = """include hyB in
theorem Bme_isPos (j : J) (b : B) : IsPosElem (lft M (Bme M h kB yB hyB j b)) := by
"""

CR_FIX_ARENA_B_NEW = """include hyB in
-- Vendoring compile fix (Mathlib v4.35): as for `Ame_isPos`. See README.md.
set_option maxHeartbeats 1600000 in
theorem Bme_isPos (j : J) (b : B) : IsPosElem (lft M (Bme M h kB yB hyB j b)) := by
"""

CR_FIX_AMP_OLD = """  rw [sub_eq_add_neg, amp_add, ← neg_one_smul ℂ z, amp_smul, neg_one_smul, sub_eq_add_neg]
"""

CR_FIX_AMP_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `neg_one_smul` needs its module element named to
  -- unify with the scalar action `amp_smul` produces. See README.md.
  rw [sub_eq_add_neg, amp_add, ← neg_one_smul ℂ z, amp_smul, neg_one_smul ℂ (amp z),
    sub_eq_add_neg]
"""

CR_FIX_PROB_OLD = """  Measure.isProbabilityMeasure_map (measurable_ψψ).aemeasurable
"""

CR_FIX_PROB_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `Measure.isProbabilityMeasure_map` became the
  -- equivalence `isProbabilityMeasure_map_iff`. See README.md.
  (Measure.isProbabilityMeasure_map_iff (measurable_ψψ).aemeasurable).mpr inferInstance
"""

# Mathlib v4.35: on `H →L[ℂ] H` the `Star` instance is `⟨adjoint⟩` (`instStarId`), and the
# `Star` of a `StarSubalgebra` of it is `StarMemClass.instStar`; the generic `star_sub`,
# `star_add` and `star_zero` are stated for the `StarAddMonoid`-derived instance, which
# `rw`/`simp` no longer identify with these (the unfolding times out). Applying the lemma to
# its explicit arguments (or going through `adjoint`) resolves the instance before matching.
CR_FIX_BUDGET_A_OLD = """  rw [star_sub, sub_mul, mul_sub, mul_sub, star_cA_mul_cA, star_cA_mul_cA, star_cA_mul_cA,
    star_cA_mul_cA]
"""

CR_FIX_BUDGET_A_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `star_sub` applied to its arguments, so that the
  -- `Star` instance of the corner algebra is resolved before the rewrite. See README.md.
  rw [star_sub (cA M h i) (cA M h i'), sub_mul, mul_sub, mul_sub, star_cA_mul_cA,
    star_cA_mul_cA, star_cA_mul_cA, star_cA_mul_cA]
"""

CR_FIX_BUDGET_B_OLD = """  rw [star_sub, sub_mul, mul_sub, mul_sub, dB_mul_star_dB, dB_mul_star_dB, dB_mul_star_dB,
    dB_mul_star_dB]
"""

CR_FIX_BUDGET_B_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `star_sub` applied to its arguments (as above).
  -- See README.md.
  rw [star_sub (dB M h j) (dB M h j'), sub_mul, mul_sub, mul_sub, dB_mul_star_dB,
    dB_mul_star_dB, dB_mul_star_dB, dB_mul_star_dB]
"""

CR_FIX_MODULAR_A_OLD = """    · rw [star_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [star_add]; exact add_mem hx hy
"""

CR_FIX_MODULAR_A_NEW = """    -- Vendoring compile fix (Mathlib v4.35): `star` on `B(ℓ²(ℚ, K))` is `adjoint`, and the
    -- generic `star_zero`/`star_add` no longer rewrite it unapplied. See README.md.
    · rw [ContinuousLinearMap.star_eq_adjoint, map_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [star_add x y]; exact add_mem hx hy
"""

CR_FIX_MODULAR_B_OLD = """  · simp only [_root_.zero_apply, map_zero, star_zero]
  · intro x y _ _ hx hy
    simp only [_root_.add_apply, map_add, star_add, hx, hy]
"""

CR_FIX_MODULAR_B_NEW = """  -- Vendoring compile fix (Mathlib v4.35): as in `spanAlg`, `star 0` through `adjoint` and
  -- `star_add` applied to its arguments. See README.md.
  · simp only [_root_.zero_apply, map_zero, ContinuousLinearMap.star_eq_adjoint]
  · intro x y _ _ hx hy
    rw [star_add x y]
    simp only [_root_.add_apply, map_add, hx, hy]
"""

CR_FIX_PHI_ZERO_OLD = """  have := Phi_smul M Ω n 0 (0 : L2Q K →L[ℂ] L2Q K)
  simpa using this
"""

CR_FIX_PHI_ZERO_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `simp` no longer sees `zero_smul`/`smul_zero`
  -- through the `SMul` instance of `B(ℓ²(ℚ, K))` (`ContinuousLinearMap.instSMul`), so
  -- `Phi 0 = 0` is read off additivity instead. See README.md.
  have := Phi_add M Ω n (0 : L2Q K →L[ℂ] L2Q K) 0
  rw [add_zero] at this
  exact add_left_cancel (this.symm.trans (add_zero _).symm)
"""

CR_FIX_SUCCESS_OLD = """  Finset.prod_le_one (fun j _ => G.payoff_nonneg _ _ _ _) (fun j _ => G.payoff_le_one _ _ _ _)
"""

CR_FIX_SUCCESS_NEW = """  -- Vendoring compile fix (Mathlib v4.35): `Finset.prod_le_one₀` is the version with the
  -- nonnegativity hypothesis. See README.md.
  Finset.prod_le_one₀ (fun j _ => G.payoff_nonneg _ _ _ _) (fun j _ => G.payoff_le_one _ _ _ _)
"""


@dataclass(frozen=True)
class PatternFix:
    """A recorded compile fix applied to every vendored Lean file of a source: each match of
    ``pattern`` (a regular expression, matched with ``re.DOTALL``) is replaced by ``repl``.
    Unlike ``Fix`` it may match any number of times, including zero, and no comment is
    inserted at the sites; the README lists the pattern and the count."""

    pattern: str
    repl: str
    reason: str


# Mathlib v4.35 made the operator of `ContinuousLinearMap.nonneg_iff_isPositive` implicit;
# upstream passes it explicitly (`_`, or a name) at many sites.
NONNEG_IMPLICIT = PatternFix(
    pattern=r"\(\s*ContinuousLinearMap\.nonneg_iff_isPositive\s+(?:_|[A-Za-z][\w.']*)\s*\)",
    repl="ContinuousLinearMap.nonneg_iff_isPositive",
    reason="Mathlib v4.35: the operator of `ContinuousLinearMap.nonneg_iff_isPositive` is "
           "implicit; the explicit argument is dropped",
)


@dataclass
class Source:
    key: str
    url: str
    copyright: str
    dest: Path                      # relative to the repository root
    module_prefix: str | None       # upstream module prefix to rewrite, if any
    local_prefix: str               # module prefix of the destination
    src_subdir: Path                # directory of the clone mirrored into `dest`
    module_root: Path               # directory of the clone that module names resolve in
    roots: tuple[str, ...] = ()     # import closure of these (module names)...
    files: tuple[str, ...] = ()     # ...or these files (relative to src_subdir)
    extra_prefixes: tuple[tuple[str, str], ...] = ()   # further (upstream, local) import
                                    # prefixes to rewrite, for a package that imports
                                    # another vendored one
    extra_files: tuple[tuple[str, str], ...] = ()   # (relative to clone, dest name)
    audit_aids: tuple[tuple[str, str], ...] = ()    # (relative to clone, dest name)
    readme: str = ""
    fixes: tuple[Fix, ...] = ()
    pattern_fixes: tuple[PatternFix, ...] = ()
    header: str = ""


HEADER = """/-
Copyright (c) 2026 {copyright}. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
{url} (commit {short}, {date}) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: {upstream_path}
-/
"""

AUTO_IMPLICIT = (
    "-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it\n"
    "-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.\n"
    "set_option autoImplicit true\n"
)

# The one upstream module that exceeds the 10,000-line cap, and the cap the parts are
# kept under (a margin for the part header and the repeated namespace-level lines).
SPLIT_FILE = "QuantumParallelRepetition.lean"
SPLIT_NAMESPACE = "QuantumParallelRepetition"
SPLIT_MAX_LINES = 9000

SPLIT_NOTE = (
    "-- Part {k} of {n} of upstream's single module `{file}`: its lines\n"
    "-- {first}-{last}, cut between top-level `noncomputable section` blocks by\n"
    "-- scripts/vendor-repetition.py (the Palomar registry caps a Lean file at 10,000 lines).\n"
)

SPLIT_ROOT_NOTE = (
    "-- Upstream's single module `{file}` ({lines} lines) is vendored as\n"
    "-- the chain of parts imported above, cut by scripts/vendor-repetition.py between its\n"
    "-- top-level `noncomputable section` blocks; this module re-exports it under its\n"
    "-- upstream name.\n"
)

CR_README = """# Vendored commuting-repetition sources

This directory is a **generated, read-only** copy of Lean sources of
[commuting-repetition](https://github.com/vidick/commuting-repetition), Thomas Vidick's
formalization of the uniform direct parallel repetition theorem for commuting-operator
strategies (manuscript *Uniform direct parallel repetition for two-player
commuting-operator strategies*, 2026), which also proves Lin's tracial density theorem
(arXiv:2304.01940, Theorem 3.2). The roots are
`CommutingRepetition.uniform_parallel_repetition` (`MainTheorem/Main.lean`) and its
Mathlib-only restatement `MainStatement.uniform_parallel_repetition`
(`StatementBridge.lean`, proving the proposition of `Statement.lean`); Lin's theorem is
`CommutingRepetition.Density.tracialDensity` (`Tracial/Density/Main.lean`). They are
used in this repository only through the bridge in `MIPRE/Background/Repetition/`; see
`planning/repetition-port.md`.

## License

Upstream is released under the Apache 2.0 license, the same license as this
repository. `NOTICE`, copied from upstream, records the material it ports from
`openai/ten-proofs`. Every file carries a header saying so.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-repetition.py` instead. The
  only differences from upstream are the header, the rewritten `import` prefix
  (`CommutingRepetition.` becomes `MIPRE.Background.Repetition.CommutingRepetition.`),
  the `set_option autoImplicit true` line inserted after the imports, and the compile
  fixes listed below. Lean *namespaces* are unchanged (`CommutingRepetition`,
  `MainStatement`).
- Nothing outside `MIPRE/Background/Repetition/` may refer to these namespaces.
- Only the import closure of the root modules is vendored (`CR_ROOTS` in the script);
  upstream's audit-node map (`Fidelity/Nodes.lean`) and the modules not needed for the
  roots are left out. Docstrings cite upstream documents (`FIDELITY.md`,
  `DIFFERENCES.md`, `PLAN-*.md`, manuscript section files); these resolve in the
  upstream repository at the commit below.

## Local deviations from upstream

None yet (beyond the mechanical ones above).

## Provenance

{generated}
"""

TP_README = """# Vendored ten-proofs sources

This directory is a **generated, read-only** copy of one Lean module of
[ten-proofs](https://github.com/openai/ten-proofs), the formalizations accompanying
OpenAI's *Ten Advances in Mathematics and Theoretical Computer Science* (2026):
`QuantumParallelRepetition.lean`, the proof of Chapter 6, *Exponential parallel
repetition for all two-player entangled games*. The root is
`QuantumParallelRepetition.distributionUniformExponential`. It is used in this
repository only through the bridge in `MIPRE/Background/Repetition/`; see
`planning/repetition-port.md`.

## License

Upstream is released under the Apache 2.0 license, the same license as this
repository. Every file carries a header saying so.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-repetition.py` instead. The
  only differences from upstream are the header, the `set_option autoImplicit true`
  line inserted after the imports, the compile fixes listed below, and the split. The
  Lean *namespace* is unchanged (`QuantumParallelRepetition`).
- Upstream's one module is 71k lines, and the Palomar registry caps a Lean file at
  10,000 (`planning/palomar.md`), so the script cuts it between its top-level
  `noncomputable section` blocks into `QuantumParallelRepetition/Part01.lean`,
  `Part02.lean`, ... (each importing the previous one, each under 9,000 lines, each
  repeating the two namespace-level `open` lines that upstream places mid-file) and
  leaves `QuantumParallelRepetition.lean` as the module importing all of them, so the
  module name the bridge imports is unchanged. Each part's header says which upstream
  lines it holds. `--resplit` redoes the split on an unsplit vendored copy.
- Nothing outside `MIPRE/Background/Repetition/` may refer to that namespace.
- `G_QuantumParallelRepetition.lean.expected` is upstream's Mathlib-only statement file
  (the definitions and the two root statements, with `sorry` proofs), kept as a reading
  aid; it is not built.

## Local deviations from upstream

None yet (beyond the mechanical ones above).

## Provenance

{generated}
"""

ORTHO_ROOTS = (
    # What tier T1b/T2/T4 prove outright, and what tier T3 proves from the interface.
    "Orthogonalization.Blocks.Main",         # Thm 1.2, any von Neumann algebra on a
                                             # finite-dimensional space
    "Orthogonalization.Blocks.Corollaries",  # Thms 1.1 and 1.4 in finite dimension
    "Orthogonalization.Blocks.Fourier",      # Cor 1.5 in finite dimension
    "Orthogonalization.FinDim.Main",         # Thm 1.2 for B(H), H finite-dimensional
    "Orthogonalization.MvN.FullAlgebra",     # Thm 1.2 for B(H), H arbitrary
    "Orthogonalization.MvN.II1Factor",       # Thm 1.2 for II_1 factors
    "Orthogonalization.MvN.Main",            # Thm 1.2, conditional on MvNStructureTheory
    "Orthogonalization.MvN.Corollaries",     # Thms 1.1, 1.4 and Cor 1.5, conditional
)


OR_README = """# Vendored orthonormalization sources

This directory is a generated copy of the `orthogonalization/` Lean package of
[commuting-repetition](https://github.com/vidick/commuting-repetition), the
formalization of de la Salle's POVM orthogonalization theorem
([arXiv:2103.14126](https://arxiv.org/abs/2103.14126)) --- blueprint
`thm:orthonormalization`. It is vendored by `scripts/vendor-repetition.py` (`--or-source`),
never edited by hand, and the import prefixes are rewritten twice: `Orthogonalization.` to
this directory's, and `CommutingRepetition.` to the sibling tree already vendored under
`MIPRE/Background/Repetition/CommutingRepetition/`, which the package depends on and which
is therefore not duplicated here.

What is proved unconditionally, and what is not, is the thing to know before citing any of
it; `MIPRE/Background/Orthonormalization/Axioms.lean` records the axioms of each root, and
the blueprint states the split. The four `sorry`s in `Orthogonalization/Basic.lean` are
upstream's *signed statements* --- the unconditional general forms of Theorems 1.1, 1.2,
1.4 and Corollary 1.5, stated so that the tiers can be compared against them. They have no
users anywhere in the package: nothing proved here depends on them, as the axiom guard
shows.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-repetition.py` instead. The only
  differences from upstream are the header, the two rewritten `import` prefixes and the
  `set_option autoImplicit true` line inserted after the imports. Lean *namespaces* are
  unchanged (`Orthogonalization`).
- Nothing outside `MIPRE/Background/Orthonormalization/` may refer to that namespace.
- Only the import closure of the root modules is vendored (`ORTHO_ROOTS` in the script).
  Docstrings cite upstream documents (`PLAN.md`, `FIDELITY.md`, `DIFFERENCES.md`, the
  manuscript); these resolve in the upstream repository at the commit below.

{generated}
"""


SOURCES = {
    "cr": Source(
        key="cr",
        url="https://github.com/vidick/commuting-repetition",
        copyright="the commuting-repetition contributors",
        dest=DEST_ROOT / "CommutingRepetition",
        module_prefix="CommutingRepetition",
        local_prefix="MIPRE.Background.Repetition.CommutingRepetition",
        src_subdir=Path("lean/CommutingRepetition"),
        module_root=Path("lean"),
        roots=CR_ROOTS,
        extra_files=(("lean/NOTICE", "NOTICE"),),
        readme=CR_README,
        fixes=(
            Fix(path="Game/Basic.lean", old=CR_FIX_PROD_LE_ONE_OLD, new=CR_FIX_PROD_LE_ONE_NEW,
                reason="Mathlib v4.35 `Finset.prod_le_one₀`: `Game.repeat`"),
            Fix(path="Statement.lean", old=CR_FIX_PROD_LE_ONE_OLD, new=CR_FIX_PROD_LE_ONE_NEW,
                reason="Mathlib v4.35 `Finset.prod_le_one₀`: `MainStatement.Game.repeat`"),
            Fix(path="Prelim/Scalar.lean", old=CR_FIX_SCALAR_OLD, new=CR_FIX_SCALAR_NEW,
                reason="Mathlib v4.35 `Finset.prod_le_one₀`: the product telescoping bound"),
            Fix(path="Game/Monotone.lean", old=CR_FIX_MONOTONE_OLD, new=CR_FIX_MONOTONE_NEW,
                reason="Mathlib v4.35 `Finset.prod_le_one₀`: the monotonicity bound"),
            Fix(path="Tracial/CStarLayer.lean", old=CR_FIX_CSTAR_CONT1_OLD,
                new=CR_FIX_CSTAR_CONT1_NEW,
                reason="Mathlib v4.35 `continuous_mul_const`/`continuous_const_mul` (1)"),
            Fix(path="Tracial/CStarLayer.lean", old=CR_FIX_CSTAR_CONT2_OLD,
                new=CR_FIX_CSTAR_CONT2_NEW,
                reason="Mathlib v4.35 `continuous_mul_const`/`continuous_const_mul` (2)"),
            Fix(path="Tracial/CStarLayer.lean", old=CR_FIX_CSTAR_NORM_OLD,
                new=CR_FIX_CSTAR_NORM_NEW,
                reason="Mathlib v4.35 `IsSelfAdjoint.le_algebraMap_norm_self` explicit element"),
            Fix(path="Tracial/Density/ClosedSubalg.lean", old=CR_FIX_CLOSED_OLD,
                new=CR_FIX_CLOSED_NEW,
                reason="Mathlib v4.35 `nonneg_iff_isPositive` implicit argument"),
            Fix(path="VN/SubModel.lean", old=CR_FIX_SUBMODEL_OLD, new=CR_FIX_SUBMODEL_NEW,
                reason="Mathlib v4.35 `IsSelfAdjoint.le_algebraMap_norm_self` explicit element"),
            Fix(path="Prerounding/Success.lean", old=CR_FIX_SUCCESS_OLD, new=CR_FIX_SUCCESS_NEW,
                reason="Mathlib v4.35 `Finset.prod_le_one₀`: the success probability bound"),
            Fix(path="VN/Crossed/Space.lean", old=CR_FIX_CFC_OLD, new=CR_FIX_CFC_NEW,
                reason="Mathlib v4.35: the shortcut CFC instance on `B(ℓ²(ℚ, K))` names its algebra"),
            Fix(path="Resolver/EntropicArena.lean", old=CR_FIX_ARENA_A_OLD, new=CR_FIX_ARENA_A_NEW,
                reason="Mathlib v4.35: heartbeat budget of `Ame_isPos`"),
            Fix(path="Resolver/EntropicArena.lean", old=CR_FIX_ARENA_B_OLD, new=CR_FIX_ARENA_B_NEW,
                reason="Mathlib v4.35: heartbeat budget of `Bme_isPos`"),
            Fix(path="VN/Crossed/AmpCalc.lean", old=CR_FIX_AMP_OLD, new=CR_FIX_AMP_NEW,
                reason="Mathlib v4.35: `neg_one_smul` with its element named (`amp_sub`)"),
            Fix(path="VN/JointModulus.lean", old=CR_FIX_PROB_OLD, new=CR_FIX_PROB_NEW,
                reason="Mathlib v4.35: `Measure.isProbabilityMeasure_map_iff`"),
            Fix(path="Resolver/EntropicArenaBudget.lean", old=CR_FIX_BUDGET_A_OLD,
                new=CR_FIX_BUDGET_A_NEW,
                reason="Mathlib v4.35: `star_sub` with its arguments (`star_diffA_mul_diffA`)"),
            Fix(path="Resolver/EntropicArenaBudget.lean", old=CR_FIX_BUDGET_B_OLD,
                new=CR_FIX_BUDGET_B_NEW,
                reason="Mathlib v4.35: `star_sub` with its arguments (`diffB_mul_star_diffB`)"),
            Fix(path="VN/Crossed/Modular.lean", old=CR_FIX_MODULAR_A_OLD,
                new=CR_FIX_MODULAR_A_NEW,
                reason="Mathlib v4.35: `star` of `B(ℓ²(ℚ, K))` in `spanAlg.star_mem'`"),
            Fix(path="VN/Crossed/Modular.lean", old=CR_FIX_MODULAR_B_OLD,
                new=CR_FIX_MODULAR_B_NEW,
                reason="Mathlib v4.35: `star` of `B(ℓ²(ℚ, K))` in `Th_Jh_spanAlg`"),
            Fix(path="Tracial/Density/CrossedTracial.lean", old=CR_FIX_PHI_ZERO_OLD,
                new=CR_FIX_PHI_ZERO_NEW,
                reason="Mathlib v4.35: `Phi_zero` from additivity (the `SMul` instance)"),
        ),
        pattern_fixes=(NONNEG_IMPLICIT,),
    ),
    "tp": Source(
        key="tp",
        url="https://github.com/openai/ten-proofs",
        copyright="the openai/ten-proofs contributors",
        dest=DEST_ROOT / "TenProofs",
        module_prefix=None,
        local_prefix="MIPRE.Background.Repetition.TenProofs",
        src_subdir=Path("."),
        module_root=Path("."),
        files=("QuantumParallelRepetition.lean",),
        audit_aids=(("ComparatorChallenges/G_QuantumParallelRepetition.lean",
                     "G_QuantumParallelRepetition.lean.expected"),),
        readme=TP_README,
        fixes=(
            Fix(
                path="QuantumParallelRepetition.lean",
                old=TP_FIX_SCHMIDT_OLD,
                new=TP_FIX_SCHMIDT_NEW,
                reason="Lean v4.33 transparency check: `exists_proofSchmidtDecomposition`",
            ),
            Fix(path="QuantumParallelRepetition.lean", old=TP_FIX_NONNEG_OLD,
                new=TP_FIX_NONNEG_NEW,
                reason="Mathlib v4.35 `nonneg_iff_isPositive`/`le_def` implicit arguments"),
            Fix(path="QuantumParallelRepetition.lean", old=TP_FIX_MULVEC_OLD,
                new=TP_FIX_MULVEC_NEW,
                reason="Mathlib v4.35 `dotProduct_mulVec_zero_iff` implicit vector"),
            Fix(path="QuantumParallelRepetition.lean", old=TP_FIX_PROD_A_OLD,
                new=TP_FIX_PROD_A_NEW,
                reason="Mathlib v4.35 `Finset.prod_le_one₀`: the hidden Alice weight"),
            Fix(path="QuantumParallelRepetition.lean", old=TP_FIX_PROD_B_OLD,
                new=TP_FIX_PROD_B_NEW,
                reason="Mathlib v4.35 `Finset.prod_le_one₀`: the hidden Bob weight"),
        ),
    ),
    "or": Source(
        key="or",
        url="https://github.com/vidick/commuting-repetition",
        copyright="the commuting-repetition contributors",
        dest=Path("MIPRE/Background/Orthonormalization/Orthogonalization"),
        module_prefix="Orthogonalization",
        local_prefix="MIPRE.Background.Orthonormalization.Orthogonalization",
        src_subdir=Path("orthogonalization/Orthogonalization"),
        module_root=Path("orthogonalization"),
        roots=ORTHO_ROOTS,
        extra_prefixes=(("CommutingRepetition",
                         "MIPRE.Background.Repetition.CommutingRepetition"),),
        readme=OR_README,
        fixes=(
            Fix(path="FinDim/Isometry.lean", old=OR_FIX_POSITIVE_OLD, new=OR_FIX_POSITIVE_NEW,
                reason="Mathlib v4.35 `nonneg_iff_isPositive` implicit argument"),
            Fix(path="FinDim/JointDiag.lean", old=OR_FIX_JOINT1_OLD, new=OR_FIX_JOINT1_NEW,
                reason="Mathlib v4.35 `nonneg_iff_isPositive` implicit argument (eigenvalues)"),
            Fix(path="FinDim/JointDiag.lean", old=OR_FIX_JOINT2_OLD, new=OR_FIX_JOINT2_NEW,
                reason="Mathlib v4.35 `le_def` implicit arguments (eigenvalues)"),
            Fix(path="MvN/Perturb.lean", old=OR_FIX_PERTURB_OLD, new=OR_FIX_PERTURB_NEW,
                reason="Mathlib v4.35 `IsSelfAdjoint.le_algebraMap_norm_self` explicit element"),
        ),
        pattern_fixes=(NONNEG_IMPLICIT,),
    ),
}


def apply_pattern_fixes(src: Source, dest: Path) -> list[tuple[PatternFix, int]]:
    """Apply the source's pattern fixes to every Lean file under ``dest``; returns the
    number of replacements per pattern."""
    counts = []
    for pf in src.pattern_fixes:
        rx = re.compile(pf.pattern, re.DOTALL)
        n = 0
        for path in sorted(dest.rglob("*.lean")):
            text = path.read_text(encoding="utf-8")
            new, k = rx.subn(pf.repl, text)
            if k:
                path.write_text(new, encoding="utf-8", newline="\n")
                n += k
        counts.append((pf, n))
    return counts


def apply_fixes(repo_root: Path) -> int:
    """Apply every recorded fix to the vendored trees as they are (no clone needed): a fix
    whose ``old`` text occurs exactly once is applied, one whose ``new`` text is already
    present is skipped, anything else is an error. Returns the number applied."""
    applied = 0
    for src in SOURCES.values():
        for fix in src.fixes:
            target = repo_root / src.dest / fix.path
            # After the split, a fix recorded against the single upstream module lives in
            # one of its parts.
            candidates = [target] + sorted((target.parent / target.stem).glob("Part*.lean"))
            target = next((c for c in candidates
                           if fix.old in c.read_text(encoding="utf-8")
                           or fix.new in c.read_text(encoding="utf-8")), target)
            text = target.read_text(encoding="utf-8")
            # `new` may contain `old` (a fix that prepends to a declaration), so the
            # already-applied check comes first.
            if text.count(fix.new) == 1:
                print(f"[{src.key}] already applied to {fix.path}: {fix.reason}")
            elif text.count(fix.old) == 1:
                target.write_text(text.replace(fix.old, fix.new), encoding="utf-8",
                                  newline="\n")
                applied += 1
                print(f"[{src.key}] applied to {fix.path}: {fix.reason}")
            else:
                sys.exit(f"error: fix for {src.key}/{fix.path} ({fix.reason}) matched "
                         f"{text.count(fix.old)} times, expected 1")
        for pf, n in apply_pattern_fixes(src, repo_root / src.dest):
            print(f"[{src.key}] pattern fix, {n} replacement(s): {pf.reason}")
            applied += n
    return applied


def git(source: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(source), *args], text=True).strip()


def import_line_re(prefix: str) -> re.Pattern[str]:
    return re.compile(rf"^import\s+({re.escape(prefix)}(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE)


def import_closure(src_root: Path, prefix: str, roots: tuple[str, ...]) -> list[Path]:
    """All upstream modules transitively imported by ``roots`` (including them)."""
    line_re = import_line_re(prefix)
    seen: dict[str, Path] = {}
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        path = src_root / (module.replace(".", "/") + ".lean")
        if not path.exists():
            sys.exit(f"error: module {module} not found at {path}")
        seen[module] = path
        stack.extend(line_re.findall(path.read_text(encoding="utf-8")))
    return sorted(seen.values())


def rewrite_imports(text: str, prefix: str, local_prefix: str) -> tuple[str, int]:
    pattern = re.compile(rf"^(\s*import\s+){re.escape(prefix)}(\.|\s*$)", re.MULTILINE)
    count = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal count
        count += 1
        return f"{match.group(1)}{local_prefix}{match.group(2)}"

    return pattern.sub(repl, text), count


def insert_auto_implicit(text: str) -> str:
    """Insert the ``set_option`` block right after the leading import block."""
    lines = text.split("\n")
    first = next((i for i, l in enumerate(lines) if l.startswith("import ")), None)
    if first is None:
        return AUTO_IMPLICIT + text
    end = first
    while end < len(lines) and (lines[end].startswith("import ") or lines[end].strip() == ""):
        end += 1
    # `end` is the first non-import, non-blank line after the block; keep one blank line.
    block = lines[first:end]
    while block and block[-1].strip() == "":
        block.pop()
    return "\n".join(lines[:first] + block + ["", AUTO_IMPLICIT.rstrip("\n")] + [""] + lines[end:])


_BLOCK_OPEN = re.compile(r"^(noncomputable\s+)?section\b|^namespace\b")
_BLOCK_END = re.compile(r"^end\b")


def split_module(text: str, max_lines: int, namespace: str) -> tuple[list[str], list[str],
                                                                      list[list[str]],
                                                                      list[tuple[int, int]]]:
    """Cut the body of ``text`` (one ``namespace .. end`` at the top level) between its
    top-level blocks into parts of at most ``max_lines`` lines.

    Returns ``(prologue, epilogue, parts, spans)``: the lines before ``namespace`` and
    after ``end namespace``, the parts (lists of body lines), and each part's line span in
    ``text`` (1-based, inclusive). Namespace-level lines that are not blocks (``open``,
    ``set_option`` and the like) are repeated at the start of every later part, since a
    part is its own file. Block comments and line comments are skipped when tracking the
    nesting, so an ``end`` inside a comment does not count."""
    lines = text.split("\n")
    ns_line = next(i for i, l in enumerate(lines) if l.strip() == f"namespace {namespace}")
    end_line = max(i for i, l in enumerate(lines) if l.strip() == f"end {namespace}")
    prologue, epilogue = lines[:ns_line], lines[end_line + 1:]
    body = lines[ns_line + 1:end_line]

    # Top-level units of the body: a block (a section/namespace and everything to its
    # matching end) or a single namespace-level line, each with its trailing blank lines.
    units: list[tuple[int, int, bool]] = []      # (start, stop, is_block) as body indices
    depth = 0
    in_comment = 0
    start: int | None = None
    for i, l in enumerate(body):
        s = l.strip()
        if in_comment:
            if "-/" in s:
                in_comment -= 1
            continue
        if s.startswith("/-"):
            if "-/" not in s:
                in_comment += 1
            if depth == 0 and s:
                units.append((i, i + 1, False))
            continue
        if s.startswith("--"):
            if depth == 0:
                units.append((i, i + 1, False))
            continue
        if _BLOCK_OPEN.match(s):
            if depth == 0:
                start = i
            depth += 1
        elif _BLOCK_END.match(s):
            depth -= 1
            if depth < 0:
                sys.exit(f"error: unbalanced `end` at body line {i + 1}")
            if depth == 0:
                assert start is not None
                units.append((start, i + 1, True))
                start = None
        elif depth == 0 and s:
            units.append((i, i + 1, False))
    if depth != 0 or in_comment:
        sys.exit("error: the body's sections do not balance; cannot split")

    parts: list[list[str]] = []
    spans: list[tuple[int, int]] = []
    carried: list[str] = []          # namespace-level lines seen so far, repeated per part
    current: list[str] = []
    current_start: int | None = None
    prev_stop = 0
    for u_start, u_stop, is_block in units:
        chunk = body[prev_stop:u_stop]          # the unit with the blank lines before it
        prev_stop = u_stop
        if current and len(current) + len(chunk) > max_lines:
            parts.append(current)
            spans.append((ns_line + 2 + current_start, ns_line + 1 + prev_stop - len(chunk)))
            current, current_start = [], None
        if current_start is None:
            current_start = u_stop - len(chunk)
            current = list(carried)
            if carried:
                current.append("")
        current.extend(chunk)
        if not is_block:
            carried.extend(l for l in body[u_start:u_stop] if l.strip())
    if current:
        parts.append(current)
        spans.append((ns_line + 2 + current_start, ns_line + 1 + prev_stop))
    return prologue, epilogue, parts, spans


def write_split(dest: Path, filename: str, local_prefix: str,
                max_lines: int = SPLIT_MAX_LINES, namespace: str = SPLIT_NAMESPACE) -> int:
    """Split ``dest/filename`` (a vendored file: provenance header, imports, the inserted
    ``set_option`` block, one namespace) into ``dest/<stem>/PartNN.lean`` and rewrite it as
    the module importing the parts. Returns the number of parts."""
    path = dest / filename
    stem = Path(filename).stem
    text = path.read_text(encoding="utf-8")
    prologue, epilogue, parts, spans = split_module(text, max_lines, namespace)
    if any(l.strip() for l in epilogue):
        sys.exit(f"error: {filename} has code after `end {namespace}`; cannot split")
    if not prologue or prologue[0] != "/-":
        sys.exit(f"error: {filename} does not start with the provenance header")
    close = next(i for i, l in enumerate(prologue) if l.strip() == "-/")
    header = "\n".join(prologue[:close + 1]) + "\n"
    imports = [l for l in prologue[close + 1:] if l.startswith("import ")]
    rest = [l for l in prologue[close + 1:] if not l.startswith("import ")]
    part_dir = dest / stem
    if part_dir.exists():
        shutil.rmtree(part_dir)
    part_dir.mkdir()
    n = len(parts)
    for k, (part, (first, last)) in enumerate(zip(parts, spans), 1):
        module = f"{local_prefix}.{stem}.Part{k:02d}"
        chain = imports + ([f"import {local_prefix}.{stem}.Part{k - 1:02d}"] if k > 1 else [])
        out = [header.rstrip("\n")] + chain + [""]
        out += [SPLIT_NOTE.format(k=k, n=n, file=filename, first=first, last=last).rstrip("\n")]
        out += [l for l in rest if l.strip()] + ["", f"namespace {namespace}", ""]
        out += part
        while out and out[-1].strip() == "":
            out.pop()
        out += ["", f"end {namespace}", ""]
        (part_dir / f"Part{k:02d}.lean").write_text("\n".join(out), encoding="utf-8",
                                                    newline="\n")
        if len(out) > 10000:
            sys.exit(f"error: {module} has {len(out)} lines")
    root = [header.rstrip("\n")]
    root += [f"import {local_prefix}.{stem}.Part{k:02d}" for k in range(1, n + 1)]
    root += ["", SPLIT_ROOT_NOTE.format(file=filename, lines=text.count("\n")).rstrip("\n"), ""]
    path.write_text("\n".join(root), encoding="utf-8", newline="\n")
    return n


def refresh_readme(path: Path, default: str, generated: str) -> None:
    text = path.read_text(encoding="utf-8") if path.exists() else None
    if text is None:
        text = default.format(generated=generated)
    elif BEGIN_MARK in text and END_MARK in text:
        pre, rest = text.split(BEGIN_MARK, 1)
        _, post = rest.split(END_MARK, 1)
        text = pre + generated + post
    else:
        text = text.rstrip() + "\n\n" + generated + "\n"
    path.write_text(text, encoding="utf-8", newline="\n")


def vendor(src: Source, clone: Path, commit: str, repo_root: Path, auto_implicit: bool) -> None:
    head = git(clone, "rev-parse", "HEAD")
    if not head.startswith(commit):
        sys.exit(f"error: clone at {clone} is at {head[:12]}, not {commit}")
    if git(clone, "status", "--porcelain"):
        sys.exit(f"error: clone at {clone} has uncommitted changes")
    date = git(clone, "show", "-s", "--format=%cs", "HEAD")
    short = head[:8]

    src_root = clone / src.src_subdir
    dest = repo_root / src.dest
    readme = dest / "README.md"
    readme_text = readme.read_text(encoding="utf-8") if readme.exists() else None
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    if readme_text is not None:
        readme.write_text(readme_text, encoding="utf-8", newline="\n")

    if src.roots:
        assert src.module_prefix is not None
        files = import_closure(clone / src.module_root, src.module_prefix, src.roots)
    else:
        files = [src_root / f for f in src.files]

    rewritten = 0
    lines = 0
    for path in files:
        rel = path.relative_to(src_root)
        text = path.read_text(encoding="utf-8")
        if src.module_prefix is not None:
            text, n = rewrite_imports(text, src.module_prefix, src.local_prefix)
            rewritten += n
        for upstream_prefix, local in src.extra_prefixes:
            text, n = rewrite_imports(text, upstream_prefix, local)
            rewritten += n
        if auto_implicit:
            text = insert_auto_implicit(text)
        lines += text.count("\n")
        upstream_path = (src.src_subdir / rel).as_posix().removeprefix("./")
        header = HEADER.format(copyright=src.copyright, url=src.url, short=short,
                               date=date, upstream_path=upstream_path)
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(header + text, encoding="utf-8", newline="\n")

    for rel, name in src.extra_files + src.audit_aids:
        shutil.copyfile(clone / rel, dest / name)

    for fix in src.fixes:
        target = dest / fix.path
        text = target.read_text(encoding="utf-8")
        if text.count(fix.old) != 1:
            sys.exit(f"error: fix for {fix.path} ({fix.reason}) matched "
                     f"{text.count(fix.old)} times, expected 1")
        target.write_text(text.replace(fix.old, fix.new), encoding="utf-8", newline="\n")

    pattern_counts = apply_pattern_fixes(src, dest)

    parts = 0
    if src.key == "tp":
        parts = write_split(dest, SPLIT_FILE, src.local_prefix)

    details = [
        BEGIN_MARK,
        f"- Upstream: {src.url}",
        f"- Commit: `{head}` ({date})",
        f"- Vendored files: {len(files)} Lean files, {lines} lines"
        + (f" (the import closure of {len(src.roots)} root modules); "
           f"{rewritten} import lines rewritten from `{src.module_prefix}.` to "
           f"`{src.local_prefix}.`" if src.roots else ""),
    ]
    details += [f"- Copied verbatim: `{name}` = upstream `{rel}`"
                for rel, name in src.extra_files + src.audit_aids]
    details += [f"- `set_option autoImplicit true` inserted after the imports: "
                f"{'yes' if auto_implicit else 'no'}"]
    details += [f"- Recorded compile fixes applied: {len(src.fixes)} "
                f"(listed under \"Local deviations from upstream\")"]
    details += [f"- Recorded pattern fix, {n} replacement(s): {pf.reason}"
                for pf, n in pattern_counts]
    if parts:
        details += [f"- `{SPLIT_FILE}` split into {parts} parts of at most {SPLIT_MAX_LINES} "
                    f"lines (`{Path(SPLIT_FILE).stem}/PartNN.lean`), cut between its "
                    f"top-level `noncomputable section` blocks; the root module imports them"]
    details += [END_MARK]
    refresh_readme(readme, src.readme, "\n".join(details))
    print(f"[{src.key}] vendored {len(files)} files ({lines} lines) from {src.url}@{short} "
          f"into {src.dest.as_posix()}; {rewritten} imports rewritten")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--cr-source", type=Path, help="path to a commuting-repetition clone")
    parser.add_argument("--cr-commit", help="expected commuting-repetition commit (prefix ok)")
    parser.add_argument("--tp-source", type=Path, help="path to a ten-proofs clone")
    parser.add_argument("--tp-commit", help="expected ten-proofs commit (prefix ok)")
    parser.add_argument("--or-source", type=Path,
                        help="path to a commuting-repetition clone (the orthogonalization "
                             "package; the same clone as --cr-source)")
    parser.add_argument("--or-commit", help="expected commuting-repetition commit (prefix ok)")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--no-auto-implicit", action="store_true",
                        help="do not insert `set_option autoImplicit true`")
    parser.add_argument("--resplit", action="store_true",
                        help=f"only redo the split of the vendored {SPLIT_FILE} (no clone "
                             "needed): the parts are regenerated from the root module's "
                             "current parts, joined back together first")
    parser.add_argument("--apply-fixes", action="store_true",
                        help="apply the recorded compile fixes to the vendored trees as they "
                             "are (no clone needed); fixes already applied are skipped")
    args = parser.parse_args()
    if args.apply_fixes:
        n = apply_fixes(args.repo_root.resolve())
        print(f"{n} fixes applied; next: lake build")
        return
    if args.resplit:
        dest = args.repo_root.resolve() / SOURCES["tp"].dest
        root = dest / SPLIT_FILE
        if f"namespace {SPLIT_NAMESPACE}" not in root.read_text(encoding="utf-8"):
            sys.exit(f"error: {root} is already the import-only root of a split; --resplit "
                     "needs the unsplit vendored module (re-vendor from a clone, or restore "
                     "the file from the commit before the split)")
        n = write_split(dest, SPLIT_FILE, SOURCES["tp"].local_prefix)
        print(f"[tp] split {SPLIT_FILE} into {n} parts; next: lake exe mk_all && lake build")
        return
    done = 0
    if args.cr_source:
        if not args.cr_commit:
            sys.exit("error: --cr-commit is required with --cr-source")
        vendor(SOURCES["cr"], args.cr_source.resolve(), args.cr_commit,
               args.repo_root.resolve(), not args.no_auto_implicit)
        done += 1
    if args.tp_source:
        if not args.tp_commit:
            sys.exit("error: --tp-commit is required with --tp-source")
        vendor(SOURCES["tp"], args.tp_source.resolve(), args.tp_commit,
               args.repo_root.resolve(), not args.no_auto_implicit)
        done += 1
    if args.or_source:
        if not args.or_commit:
            sys.exit("error: --or-commit is required with --or-source")
        vendor(SOURCES["or"], args.or_source.resolve(), args.or_commit,
               args.repo_root.resolve(), not args.no_auto_implicit)
        done += 1
    if not done:
        sys.exit("error: give --cr-source, --tp-source and/or --or-source")
    print("next: lake exe mk_all && lake build")


if __name__ == "__main__":
    main()
