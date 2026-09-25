<!-- Area survey written by a Claude Code agent on 2026-09-25 for planning/simplification-2026-09-25.md; read-only, grep-and-read evidence plus the compiler probes it names. Consumer counts are snapshots. -->

# Simplification survey: `MIPRE/Background/AnswerReduction/` and `MIPRE/Background/Introspection/`

Read-only survey, 2026-09-25. Method: whole-corpus reference counts (`refcount.py` → `refcount_all.json`,
1549 area declarations, 213 blueprint-tagged, 174 guarded), an import-closure computation from
`MIPRE.MainTheorem` / `Introspection.Compiler` / `AnswerReduction.Instance`, a homonym-shadowing pass
(declarations whose only apparent consumers are same-named declarations in other files), a pass-through
scan, an Alice/Bob mirror-pair measurement, and four `lean_references` probes on the decisive claims.
Numbers are line counts from the declaration index (docstring through end of proof).

## Headline

The Introspection tree still carries the **pre-`qld_soundness` "extraction-callback" route** end to end:
theorems that take `extract : ∀ R η, … → Nonempty (Extraction …)` as a hypothesis, the explicit-selector
`RestrictionXxxEq` scaffolding, and "compatibility statements retaining the original … API". The planning
record says the final route "uses the proved `QLD.qld_soundness`, with no extraction callback"
(`planning/formalization-plan.md`, 2026-09-23). Everything on the old route is either in the dead lists
already, or is kept alive only by a same-named declaration elsewhere (the mechanical scan's homonym blind
spot), or is a file with zero importers. Removing it is one PR of pure deletion, about **520 lines and two
whole files**, with no blueprint tag, guard, or prose mention on any of it (checked: `rg` over
`blueprint/src` finds none of the file or declaration names).

## Candidates

| # | shape | declarations (path:line) | survivor / replacement | consumers (grepped, then read) | est. net lines | risk | conf. |
|---|---|---|---|---|---|---|---|
| 1 | **superseded route, whole file** | `MIPRE/Background/Introspection/CanonicalSoundness.lean` (65 lines): `RestrictedSoundness.canonical_quantumValue_ge_of_field_extraction` (:30), local instance `canonical_neZero` (:25) | `NumberedSoundness.canonical_quantumValue_ge` (`NumberedSoundness.lean:241`), which CompiledSoundness.lean:76 consumes | **0 importers** of the module (only `MIPRE.lean`); the theorem is in the dead list; it is outside the main theorem's import closure | −65 (and one `MIPRE.lean` line via `lake exe mk_all`) | low | high |
| 2 | **superseded route, whole file** | `MIPRE/Background/Introspection/ExplicitStrategy.lean` (196 lines). Dead per scan: `ExplicitGame.RestrictionStateEq/restrictionStateEq/RestrictionDimensionsEq/restrictionDimensionsEq/RestrictionPauliAEq/restrictionPauliAEq/RestrictionPauliBEq/restrictionPauliBEq` (:43–:76), `qldStrategy_state/_dimensions/_pauliAns_A/_pauliAns_B` (:101–:125), `selectorGame`, `selector_toLegacy_value`, `selector_qldStrategy_failure_le`, `selector_exists_perfectPCC` (:162–:194). Homonym-shadowed, not in the dead list: `ExplicitGame.restrictionOfRelabel` (:36), `ExplicitGame.qldStrategy` (:97), `ExplicitGame.qldStrategy_failure_le` (:112), `ExplicitGame.exists_perfectPCC` (:139) | `NumberedSoundness.qldStrategy` / `qldStrategy_failure_le` (`NumberedSoundness.lean:139,:203`, built through `legacyStrategy` and `RestrictedSoundness.restriction`) and `NumberedComplete.exists_perfectPCC_with_format` (tagged) | `lean_references`: `ExplicitGame.exists_perfectPCC` → only `ExplicitStrategy.lean:194` (dead `selector_exists_perfectPCC`); `ExplicitGame.qldStrategy` → only :113, :176 in the same file; `qldStrategy_failure_le` → only :179 (dead). `restrictionOfRelabel` → 8 hits, all in this file. Sole importer `BinaryQuotientComplete.lean` uses only `ExplicitGame.pccToExplicit*`, `pauliCheck`, `questionEquiv` (from `ExplicitGame.lean`) — it would import `ExplicitGame` + `BinaryGame` directly | −196 | low | high |
| 3 | **superseded route, tail of a file** | `MIPRE/Background/Introspection/RestrictedProfileSoundness.lean`: `RestrictedSoundness.quantumValue_ge_of_qld_errorProfile` (:50), `explicit_quantumValue_ge_of_qld_errorProfile` (:73), `padded_quantumValue_ge_of_qld_errorProfile` (:95) — all take an `extract` callback | `NumberedSoundness.quantumValue_ge_of_errorProfile` (:185), which takes a `FieldExtraction` witness for the *specific* restricted strategy | all three in the dead list (count=2 = self + docstring/inventory). What survives in the file is 20 lines: `edgeCount`, `edgeCount_one_le`, `profileCoefficient`, `profileCoefficient_one_le`, consumed by `NumberedSoundness.lean` (9 hits) and `CompiledSoundness.lean:22`. Those could move into `NumberedSoundness.lean` and the file go, dropping its imports of `ExplicitGame` and `SourcePaddingValue` | −85 (−100 if the four survivors are moved and the file removed) | low | high |
| 4 | **superseded route, tails** | `RestrictedSoundness.quantumValue_ge_of_qld_extraction` (`RestrictedSoundness.lean:125`, callback form of the live `quantumValue_ge_of_extraction`); `RestrictedSoundness.padded_quantumValue_ge_of_field_extraction` (`BinaryExtraction.lean:220`, its only non-dead caller was file #1); `RestrictedSoundness.exists_degreeOne_fieldExtraction` (`QLDExtractionAdapter.lean:218`, replaced by `degreeOne_fieldExtraction_exists` :255 which NumberedSoundness.lean:263 uses) | as named | all three in the dead list; the `Extraction` structure and `FieldExtraction.toBinary` stay (live through `NumberedSoundness.quantumValue_ge_of_extraction`) | −18 −27 −16 = −61 | low | high |
| 5 | **superseded transport, tail of a file** | `MIPRE/Background/Introspection/ExplicitGame.lean`: `ExplicitGame.toExplicit` (:154), `toExplicit_value` (:160), `toLegacy_state` (:185), `toLegacy_dimensions` (:194, a `def` of a Prop with `linter.defProp false`) | `toLegacy`, `toLegacy_value` (tagged), `toLegacy_pauli_A/B` (used by NumberedSoundness.lean:101,:123) | all four in the dead list; `toLegacy_dimensions` and `toLegacy_state` exist only to feed #2's `RestrictionDimensionsEq/StateEq`, which are dead | −25 | low | high |
| 6 | **compatibility shims (self-declared)** | `NumberedComplete.exists_perfectPCC` (`NumberedComplete.lean:143`, docstring "Compatibility statement retaining the original guarded witness API") and `NumberedComplete.coordinate_exists_perfectPCC` (:125, same, already dead) | `NumberedComplete.exists_perfectPCC_with_format` (:90, tagged, consumed by `CanonicalGame.lean:70`) | `lean_references` on :143 → the declaration only. `CanonicalComplete.lean:111` calls `CanonicalGame.exists_perfectPCC` (it opens `CanonicalGame`, not `NumberedComplete`) — the grep count of 32 was homonyms | −34 | low | high |
| 7 | **degenerate padding variant** | `BinaryComplete.exactPaddedGame` (`BinaryPadding.lean:81`), `exists_exactPadded_perfectPCC` (:88) | `depthPaddedGame` / `exists_depthPadded_perfectPCC` (:111/:118, tagged); the docstring at :16 already says the depth variant is the one used | both in the dead list; the whole module sits **outside the main theorem's import closure** (only importer `QLD/Axioms.lean`) but `exists_padded_perfectPCC` and `exists_depthPadded_perfectPCC` are tagged, so the file stays | −28 | low | high |
| 8 | **cross-file private duplicate** | `doubled_positive`: `Introspection/BinaryGame.lean:149`, `CompleteGame.lean:149`, `HonestPauliGame.lean:184`, **and a fourth** at `Foundations/Introspection/HonestMagicSquareGame.lean:169`. Identical proof, statement `0 < G.doubled.μ p q → (p.1 = false ∧ q.1 = true) ∧ 0 < G.μ p.2 q.2` | one owner in `MIPRE/Foundations/GameDouble.lean` beside `Game.doubled_μ` (:66), e.g. `Game.pos_of_doubled_μ_pos (G : Game X X A A) (p q : Bool × X)`, proof unchanged (5 lines) | each copy is used 2–3 times in its own file only | −4×9 + 8 = −28 | low | high |
| 9 | **cross-file private duplicate** | `pauli_adj`: `BinarySampled.lean:32`, `CompleteSampled.lean:31` — identical statement and proof (`TypeGraph.Adj … (.inl p) (.inl q) → QLD.adj p q = true`) | one non-private lemma next to `TypeGraph.adj_pauli` (its only ingredient; `MIPRE/Foundations/Introspection/…`), or in `HonestPauliGame.lean` which both files import | 1 use each (`pauli_pair_commute`, `pauli_pair_reject` in each file) | −6 | low | high |
| 10 | **twin development (field register vs binary register)** | `Introspection/Complete{Game,Sampled,Anchors,Measurements}.lean` (570 lines, namespace `MIPRE.Introspection.Complete`, seeds `Seed F m`) vs `Binary{Game,Sampled,Anchors,Measurements}.lean` (namespace `BinaryComplete`, seeds `Seed m t` through a self-dual basis). `diff CompleteGame BinaryGame` is 60 changed lines out of 198: the same file with `t`, `b`, `hb` threaded through; the same holds for the other three pairs (75/99/139 changed lines). Plus the field half of `PauliExtraction.lean` (:203–:222, :374–:495, ≈140 lines: `fieldGame_eq_fullGame`, `fieldToFull`, `fieldToFull_value`, `exists_field_extraction`, `exists_quantumValue_ge_of_field`) | the binary route, which is the only one the compiler (`Introspection.seven`) reaches. The Complete files are in the closure only because `BinaryMeasurements.lean:5` imports `CompleteGame` (it uses **no** `Complete.*` token; it needs `HonestPauliMeasurements`, `QLD.CLBinary`, `HonestCompleteGame`, `HonestPauliEdges`, which arrive transitively) | `Complete.*` is consumed outside its four files only by `PauliExtraction.lean` (field analogues) and the guards. All of it is production **by policy**: `lem:intro-full-typed-completeness` tags both `Complete.*` and `BinaryComplete.*` (`06_proof_structure.tex:3432`), `lem:intro-extracted-soundness` tags both `exists_quantumValue_ge_of_binary` and `…_of_field` (:3540); `QLD/Axioms.lean:1112–1118, :1573–1579` guard them. `PauliExtraction.lean` itself is outside the main theorem's closure (importer: `QLD/Axioms.lean` only) | up to −700 if the blueprint drops the field-register clause from those two nodes and retags them to the binary declarations; 0 otherwise | high (blueprint decision, two nodes' statements change) | high on the facts, low that it should be done |
| 11 | **pass-through re-exports** | `AnswerReduction.size_treeHead_le` / `size_treeTail_le` (`DeciderCost.lean:34,:37`) are `ProductSampler.size_treeHead_le d` / `…tail_le d` under a second name; `DecisionKernel.program_runs` (`DecisionKernel.lean:143`) is the field projection `(program U).computes z` | the originals | 1 own-file use each for the first two (own_hits=1); `program_runs`: `lean_references` → declaration only | −12 | low | high |
| 12 | **speculative generality** | the explicit-selector parameters `(χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)` threaded through 19 binders in `ExplicitGame`, `NumberedComplete`, `NumberedSoundness`, `BinaryQuotientComplete`, `CanonicalGame` | there is exactly **one live discharge**, `CanonicalGame.lean:39` with `chi_seedPermutation (field c lam n) (selectorBits c lam n)`; the other three discharges are in file #2 (dead) | 19 binders, 1 caller | a specialization would remove ~40 lines of parameter plumbing but is a design change against a recorded rationale (`planning/classical-pcp-introspection.md`, "CLExplicitSeed uses a proved seed/content permutation … no selector-correspondence premise remains in the instantiated theorem") | med | low priority; listed for the record |

Items 1–7 are the same PR: one route, ~520 lines, `lake exe mk_all` after the two file removals, and
`BinaryQuotientComplete.lean`'s import line changed from `ExplicitStrategy` to `ExplicitGame` + `BinaryGame`.
Nothing in the blueprint, `Axioms.lean` files, or the guards names any of it.

## Rejected with evidence

- **Alice/Bob mirror pairs in the AR soundness chain** — 14 pairs, 310 lines in the smaller member:
  `gcA_le`/`gcB_le` (80/75, `SoundDecoded.lean`), `sum_gcEvA_le`/`sum_gcEvB_le` (96/95, `SoundGameCheck.lean`),
  `disPolyA_le`/`disPolyB_le` (38/38) and `sum_disPolyA_le`/`sum_disPolyB_le` (26/26, `SoundPoly.lean`),
  the nine `condFail_{OO,Oa,Ob,aO,bO,aa,ab,bb,ba}_le` (29–37 lines each, `SoundDecoded.lean:119–467`).
  `SoundSetup.lean`'s docstring records the decision: "The paper symmetrizes it first
  (`lem:symmetric-strat`); the Lean does not, and derives every relation for each ordered pair of players
  from the ordered pair of types that carries it." There is no swap transport on `MIPRE.dis`/`condFail`
  in Foundations (`Foundations/Swap.lean` has `povmValue_swapVec_of_symm` only), so a symmetrization would
  be new mathematics, not a deletion. Rejected.
- **Copy-6 variants** (`cl_accepts_of_accepts6`, `valsOf_ans6`, `readAns6`, `tq_point6`, `cl_eval_append6`,
  `JA/JB` vs `GA1/GB1`, `err6` vs `err1`): the sixth copy runs the `m'`-variable test with `m'+6`
  codewords, a different parameter set from copies 1–5 (`Predicate.lean`, `PcpPresentation.lean`). Not a
  staged variant; rejected.
- **Zero-index apparatus** (`DecisionCompilerZero.lean`, `PauliSamplerZero.lean`, `ZeroIndexSampler.*`):
  the contract's sampler must be total at index 0 while soundness is only claimed at positive index
  (`formalization-plan.md`: "positive-index strict-value soundness domain"). Live, all consumed by the
  compiler. Rejected.
- **`NumberedSoundness.quantumValue_ge_of_qld`** (`NumberedSoundness.lean:215`) is a general-`d` version
  beside the degree-one `canonical_quantumValue_ge` the compiler uses; only consumer is `MIPRE/Axioms.lean:2550`
  (guard = a proof-level `\leanok`). Production by policy; rejected.
- **`hb : IsSelfDualBasis b`** (28 binders) — discharged by the Shoup/self-dual construction at the compiler;
  genuinely needed (`Complete` vs `BinaryComplete` differ exactly here). Rejected.
- **`getD_ofFn` (`AnswerFormat.lean:75`), `lam_mul_add_one_le` (`ParamsCost.lean:47`), `pow_le_tPcp`
  (`Complete.lean:78`), `sliceL`/`placeL` (`StageLists.lean`)** — searched for Mathlib shapes: `getD_ofFn`
  is one `simp [List.getD_eq_getElem?_getD]` away from Mathlib and nothing else has a Mathlib name. Too
  small to be worth a row; hygiene at most.
- **AR chain scaffolding** ("copy-6 per-seed strategy", "AR-5b6", "extraction per seed", "edge relations",
  "decoding" from the planning record): read every `Sound*.lean` docstring and the import graph. Each piece
  is imported by exactly the next one (`SoundSetup → SoundIsolate → SoundCopy → SoundExtract → SoundRelations
  → SoundPoly → SoundGameCheck → SoundDecoded → SoundPcp → SoundError → SoundFinal`) and the dead list for the
  directory is 17 small lemmas (no cluster). The staged names in the planning record are PR labels, not
  surviving variants. No finding.

## Hygiene batch (tiny, correct, batch under one PR if ever)

- `AnswerReduction.size_treeHead_le`/`size_treeTail_le` re-exports (`DeciderCost.lean:34,:37`), −6.
- `DecisionKernel.program_runs` (`DecisionKernel.lean:143`), unused field projection, −4.
- `BinaryComplete.quotientHonest_prefixGuard` / `quotientHonest_introspect` (`BinaryQuotientComplete.lean:84,:88`)
  are one-line renames of `explicitHonest_*`, one consumer each; `sum_disPolyA_le'` (`SoundDecoded.lean:702`)
  is `sum_disPolyA_le` restated (its B twin is a real `linarith` step, so keep the pair shape), −4 each if inlined.
- `CompiledSoundness.sourceCoefficient_one_le` / `coefficient_one_le` (:29,:32): one-line wrappers, 1 use each.
- `LIDT.LowIndDegPoly.eval_sub` full-name collision (`AnswerReduction/SoundPoly.lean:37` vs
  `QLD/Separate.lean:50`) — the only full-name collision in the corpus involving this area (checked over all
  17184 declarations); being handled.
- Namespace injections: 94 declarations of `Background/Introspection/HonestPauli*.lean` live in
  `MIPRE.QLD.Honest` (the QLD tree's namespace); `AnswerReduction/SoundRelations.lean:41` puts
  `ptOf_eq_comp` (dead) in `MIPRE.LIDT.CL.Regs`; `SoundGameCheck.lean:33,:42` and `SoundRelations.lean:94,:105`
  put four generic POVM lemmas (`sum_ite_bornProb_one_map`, `sum_ite_bornProb_one_map'`, `inconsistency_uniform`,
  `sum_dis_le_of_inconsistency`) in the root `MIPRE` namespace though nothing like them exists in Foundations.
  Not simplifications; placement notes for whoever next touches those files.
- `BinaryMeasurements.lean:5` imports `CompleteGame` for its transitive imports only (no `Complete.*` token in
  the Binary chain); import `HonestPauliMeasurements`, `QLD.CLBinary`, `Foundations/Introspection/HonestCompleteGame`,
  `HonestPauliEdges` directly. Matters only if #10 is ever done.

## Files surveyed and limits

- All 35 `AnswerReduction/*.lean` (docstrings read in full; `SoundDecoded`, `SoundRelations`, `SoundPoly`,
  `SoundGameCheck`, `DeciderCost`, `StageLists`, `AnswerFormat`, `Instance`, `Complete`, `ParamsCost`,
  `SoundError` read in the relevant spans).
- All 56 `Introspection/*.lean` docstrings; read in full: `CanonicalSoundness`, `RestrictedSoundness`,
  `RestrictedProfileSoundness`, `ExplicitStrategy`, `NumberedSoundness`, `BinaryPadding` (:45–), `NumberedComplete`
  (:85–), `ExplicitGame` (:140–), `BinaryQuotientComplete` (:50–), the `Binary*`/`Complete*` diffs, `DecisionKernel` (:120–).
- Compiler probes used: 4 of the ~8 allowed (`lean_references` on `ExplicitGame.exists_perfectPCC`,
  `ExplicitGame.qldStrategy`, `NumberedComplete.exists_perfectPCC`, `DecisionKernel.program_runs`).
- Not checked: no build was run, so "removing X leaves the tree compiling" is inferred from reference
  data, not demonstrated; the pass-through scan is regex-based and was used only to surface candidates that
  were then read. Consumer counts for the Complete/Binary twin lemmas (`op_isPVM`, `seedAnswer`, …) are
  same-named in both chains and were not separated further, since #10 is a blueprint decision, not a Lean one.
