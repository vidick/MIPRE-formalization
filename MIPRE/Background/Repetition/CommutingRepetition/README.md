# Vendored commuting-repetition sources

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
  only differences from upstream are the header, the module-system lines (`module`, `public import`, `@[expose] public section`, no `private` definitions; added by `scripts/modularize.py`, 2026-09-28), the rewritten `import` prefix
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

Compile fixes for the Mathlib crossing (this repository moved to Lean v4.35.0-rc3 and
Mathlib `v4.35.0-rc3` on 2026-09-28, `planning/palomar.md`), applied by
`scripts/vendor-repetition.py` from its recorded `Fix` list (`--apply-fixes` re-applies them
to the tree as it is); each site carries a comment saying so:

- `Game/Basic.lean` and `Statement.lean` (`Game.repeat`'s `payoff_le_one`),
  `Game/Monotone.lean`, `Prerounding/Success.lean` and `Prelim/Scalar.lean` (product
  bounds): `Finset.prod_le_one` lost its nonnegativity hypothesis in Mathlib v4.35; the
  version with it is `Finset.prod_le_one₀`, which is what these call now.
- `Tracial/CStarLayer.lean`: `continuous_mul_right`/`continuous_mul_left` are now
  `continuous_mul_const`/`continuous_const_mul`; `IsSelfAdjoint.le_algebraMap_norm_self`
  takes its element explicitly (also `VN/SubModel.lean`, through dot notation).
- `Tracial/Density/ClosedSubalg.lean`, and a recorded *pattern* fix over the whole tree
  (16 sites at the time of writing): the operator of
  `ContinuousLinearMap.nonneg_iff_isPositive` is implicit, so the explicit argument
  upstream passes (`_` or a name) is dropped.
- `VN/Crossed/Space.lean`: the shortcut `ContinuousFunctionalCalculus` instance on
  `B(ℓ²(ℚ, K))` names its algebra, without which the `Star` instance of the
  `IsSelfAdjoint` predicate no longer unifies.
- `VN/Crossed/AmpCalc.lean` (`amp_sub`): `neg_one_smul` is applied with its module element
  named, since the scalar action produced by `amp_smul` no longer unifies with the bare
  rewrite. `VN/JointModulus.lean`: `Measure.isProbabilityMeasure_map` became the
  equivalence `isProbabilityMeasure_map_iff`.
- `Resolver/EntropicArena.lean`: `Ame_isPos` and `Bme_isPos` get
  `set_option maxHeartbeats 1600000 in`; their `map_sum` step exceeds the default budget
  under Mathlib v4.35 (the instance search unfolds the arena's algebra) and elaborates
  within the larger one.
- `Resolver/EntropicArenaBudget.lean` and `VN/Crossed/Modular.lean`: on `H →L[ℂ] H` the
  `Star` instance is `⟨adjoint⟩`, and on a `StarSubalgebra` of it `StarMemClass.instStar`;
  the generic `star_sub`, `star_add` and `star_zero` are stated for the instance derived
  from `StarAddMonoid`, which `rw` and `simp` no longer identify with these before
  matching (the unfolding exceeds the budget). The lemmas are applied to their explicit
  arguments, or `star 0` is rewritten through `ContinuousLinearMap.star_eq_adjoint`, so
  the instance is resolved first.
- `Tracial/Density/CrossedTracial.lean` (`Phi_zero`): the same kind of mismatch for the
  `SMul` instance of `B(ℓ²(ℚ, K))` (`ContinuousLinearMap.instSMul` against the one
  `zero_smul` and `smul_zero` are stated for), so `Phi 0 = 0` is derived from `Phi_add`
  instead of `Phi_smul`.

## Provenance

<!-- BEGIN GENERATED (scripts/vendor-repetition.py) -->
- Upstream: https://github.com/vidick/commuting-repetition
- Commit: `cfa2f1bf199139cea65827e708f7956c743f14e8` (2026-09-11)
- Vendored files: 130 Lean files, 54798 lines (the import closure of 2 root modules); 246 import lines rewritten from `CommutingRepetition.` to `MIPRE.Background.Repetition.CommutingRepetition.`
- Copied verbatim: `NOTICE` = upstream `lean/NOTICE`
- `set_option autoImplicit true` inserted after the imports: yes
- Recorded compile fixes applied: 0 (listed under "Local deviations from upstream")
- Module system: 130 files given the `module` header, `public import`s, an `@[expose] public section` and no `private` definitions by `scripts/modularize.py` (Palomar requires it; `planning/palomar.md`)
<!-- END GENERATED -->
