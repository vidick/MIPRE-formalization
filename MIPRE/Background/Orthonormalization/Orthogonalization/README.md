# Vendored orthonormalization sources

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
  differences from upstream are the header, the module-system lines (`module`, `public import`, `@[expose] public section`, no `private` definitions; added by `scripts/modularize.py`, 2026-09-28), the two rewritten `import` prefixes and the
  `set_option autoImplicit true` line inserted after the imports. Lean *namespaces* are
  unchanged (`Orthogonalization`).
- Nothing outside `MIPRE/Background/Orthonormalization/` may refer to that namespace.
- Only the import closure of the root modules is vendored (`ORTHO_ROOTS` in the script).
  Docstrings cite upstream documents (`PLAN.md`, `FIDELITY.md`, `DIFFERENCES.md`, the
  manuscript); these resolve in the upstream repository at the commit below.

## Local deviations from upstream

Compile fixes for the Mathlib crossing (this repository moved to Lean v4.35.0-rc3 and
Mathlib `v4.35.0-rc3` on 2026-09-28, `planning/palomar.md`), applied by
`scripts/vendor-repetition.py` from its recorded `Fix` list (`--apply-fixes` re-applies them
to the tree as it is); each site carries a comment saying so:

- `FinDim/Isometry.lean` (the eigenvalue bound in the isometry lemma), `FinDim/JointDiag.lean`
  (the eigenvalue bounds, also `le_def`), and a recorded *pattern* fix over the whole tree
  (7 sites at the time of writing): Mathlib v4.35 makes the operator of
  `nonneg_iff_isPositive` and of `le_def` implicit, so the explicit argument is dropped.
- `MvN/Perturb.lean`: `IsSelfAdjoint.le_algebraMap_norm_self` takes its element explicitly.

<!-- BEGIN GENERATED (scripts/vendor-repetition.py) -->
- Upstream: https://github.com/vidick/commuting-repetition
- Commit: `8ff85e29d24282297c328a11db4eabf1515948c3` (2026-09-10)
- Vendored files: 43 Lean files, 12838 lines (the import closure of 8 root modules); 111 import lines rewritten from `Orthogonalization.` to `MIPRE.Background.Orthonormalization.Orthogonalization.`
- `set_option autoImplicit true` inserted after the imports: yes
- Recorded compile fixes applied: 0 (listed under "Local deviations from upstream")
- Module system: 43 files given the `module` header, `public import`s, an `@[expose] public section` and no `private` definitions by `scripts/modularize.py` (Palomar requires it; `planning/palomar.md`)
<!-- END GENERATED -->
