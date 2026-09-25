<!-- Area survey written by a Claude Code agent on 2026-09-25 for planning/simplification-2026-09-25.md; read-only, grep-and-read evidence plus the compiler probes it names. Consumer counts are snapshots. -->

# Simplification survey — `MIPRE/Foundations/Introspection/` (files A–L)

Read-only survey, 2026-09-25. 165 files (A–L basenames, 21.9k lines). Method: importer counts,
module docstrings, mechanical scans (single-line pass-through proofs; per-declaration consumer
counts by final identifier component over all of `MIPRE/`, `blueprint/`, guard files — script in
scratchpad `fast_liveness.py`, output `liveness_fast.txt`), targeted reading, and one
`lean_run_code` probe (6 examples) for Mathlib shadows. All paths relative to the repo root; all
line numbers from the current tree.

Conventions respected: no vendored-tree proposals; blueprint-tagged and guard-listed names are
never deletion candidates; the 137-entry mechanical dead list is not re-reported item by item.

## Candidates

| # | shape | declarations (path:line) | survivor / replacement | consumers (grepped, then read) | est. net lines | risk | conf. |
|---|---|---|---|---|---|---|---|
| 1 | superseded route — whole file | `MIPRE.Introspection.AuxiliaryPrefix.scan` (def) + `scan_sound`, `stage_of_honest`, `scan_honest`, `scan_legal_query` — `MIPRE/Foundations/Introspection/AuxiliaryPrefixScan.lean:17-71` (73-line file) | delete the file; in `AuxiliaryScanCorrect.lean:6` replace `import …AuxiliaryPrefixScan` by `import …AuxiliaryPrefixSolve`; `lake exe mk_all` | only importer is `AuxiliaryScanCorrect.lean`, which references only `AuxiliaryPrefix.{outputPrefix_step, solveStage, replaceSeed, extend_claimed}` — all from `AuxiliaryPrefixSolve`. `AuxiliaryPrefix.scan` has zero references anywhere; the 4 theorems are on the dead list (their non-zero counts are in-file). `AuxiliaryScanCorrect.lean:56-106` re-proves the same scan on the executable `stage`/`program` (`program_sound`), i.e. this is the earlier, abstract version of the scan that the executable one replaced. | −73 | low | high |
| 2 | superseded route — whole file | `MIPRE.Introspection.DecisionPreparation.compiler_ambient_time` — `MIPRE/Foundations/Introspection/DecisionPreparationBound.lean:20` (55-line file, one declaration, on the dead list) | delete the file; in `MIPRE/Background/Introspection/DecisionCompiler.lean:8` import `…DecisionPreparationCost` instead; `mk_all` | sole importer `Background/Introspection/DecisionCompiler.lean` uses only `DecisionPreparation.{compiler, compiler_closed, compiler_runs, kernelInput}` (all from `DecisionPreparation.lean`). No blueprint tag, no guard. The ambient-time bound was replaced by `DecisionPreparationCost.compiler_runs_poly` / `compiledPoly` (consumed by `Background/Introspection/DecisionCompilerTime.lean`). | −55 | low | high |
| 3 | Mathlib shadow (×2, identical private copies) | `matrix_ite_entry` — `AdaptiveDualMarginal.lean:20-23` and `AdaptiveXSplit.lean:20-23` | `Matrix.ite_apply` (`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:318`, statement identical; probe compiled) | uses: `AdaptiveDualMarginal.lean:42,156`, `AdaptiveXSplit.lean:35` — all inside `simp only [...]` lists; substitute the name | −8 | low | high |
| 4 | Mathlib shadow | `sum_supported` (private) — `HonestParsed.lean:31-41` | `(Fintype.sum_of_injective f hf (g ∘ f) g hz fun _ => rfl).symm` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:1005`; probe compiled) | 3 in-file `rw [sum_supported …]` at `HonestParsed.lean:74,94,115`; a `have` of the one-liner, or rewrite with the Mathlib lemma directly | −9 | low | high |
| 5 | Mathlib shadow + duplicate fact | `self_le_sqrt_of_unit` (private) — `AdaptivePowerBudget.lean:52-57`; and `MIPRE.Introspection.state_transfer_loss_le_three_sqrt` — `ErrorBounds.lean:161-166` (tagged+guarded, no Lean consumer) states the same fact (`δ + 2√δ ≤ 3√δ` ⇔ `δ ≤ √δ`) | `Real.le_sqrt_self_iff : x ≤ √x ↔ x ≤ 1` (`Mathlib/Analysis/Real/Sqrt.lean:310`; `exact?` found it). Replace the private with the Mathlib lemma (its one consumer is `self_le_iteratedRoot`, `:64`); `state_transfer_loss_le_three_sqrt` keeps its name/tag with a one-line proof `by linarith [Real.le_sqrt_self_iff.mpr hδ1]` | private: one in-file consumer; the public one: guard + tag only | −9 | low | high |
| 6 | duplication (identical private lemma in two files) + Mathlib-free general owner | `auxCheck_swap` — `HonestCompleteAux.lean:64-71`; `aux_check_swap` — `HonestParsedHiding.lean:57-65` (statement and proof identical; `AuxQuestion ℓ := AuxType ℓ × Bool`, `HonestCompleteAux.lean:29`); sibling `check_pauli_aux_swap` — `HonestPauliEdges.lean:105-110` (the `.inl p, .inr t` case) | one public lemma in `TypedPredicate.lean` (after `check`, `:69`): `check_swap_of_not_pauli`/two lemmas `check_inr_swap`, `check_inl_inr_swap`. `check` is symmetric except for `DP p q x y` on two Pauli questions, so both shapes follow from one statement guarded by `¬ (t.isLeft ∧ u.isLeft)` | `auxCheck_swap`: `HonestCompleteAux.lean:169`; `aux_check_swap`: `HonestParsedHiding.lean:109,133`; `check_pauli_aux_swap`: `HonestPauliEdges.lean:140,149` | −14 | low | med |
| 7 | special case beside general (cross-area, LCS) | private `observable_kronecker` (`HonestMagicSquare.lean:29-36`), `tensor_commute` (`:52-57`), `tensor_anticommute` (`:59-66`) generalise `MIPRE.LCS.IsObservable.kronecker`, `MIPRE.LCS.commute_kronecker_of_commute`, `MIPRE.LCS.commute_kronecker_of_anticomm` (`MIPRE/LCS/Pauli.lean:163-197`), which are stated for `Matrix (Fin 2) (Fin 2) ℂ` only although their proofs never use `Fin 2` | generalise the three LCS lemmas to `{A B : Matrix I I ℂ} {C D : Matrix J J ℂ}` (proofs unchanged), delete the three privates | LCS lemmas: `MIPRE/LCS/MagicSquare/Strategy.lean`, `MIPRE/LCS/Pauli.lean`; privates: in-file (`grid_isObservable`, `grid_commute…`) | −22 | med (touches `MIPRE/LCS/`, another area; instance-argument order may need adjusting at the two LCS call sites) | med |
| 8 | duplication across namespaces | `MIPRE.Introspection.fibSum_aOp` — `ConditionalNormalizerStepAux.lean:26-28` and `MIPRE.QLD.fibSum_aOp` — `MIPRE/Background/QLD/Lines.lean:751-754` (same statement, QLD one is blueprint-tagged and guard-listed) | keep the Foundations one (2-line proof `(aOp_sum _ _).symm`), ideally moved next to `fibSum` in `MIPRE/Foundations/Pasting.lean:158`; the QLD copy becomes a tag-redirect (low priority by the rules) | Introspection copy: 9 files (`ReadRigidity`, `ProductStageZTests`, `HidingBaseRigidity`, …); QLD copy: `QLD/Lines.lean:899`, `QLD/Axioms.lean` | −4 (+ tag redirect) | low | high |
| 9 | superseded generality (report only) | `MIPRE.Introspection.exists_varying_conditional_projective_dilation` — `HidingInductionDilation.lean:243-297` (55 lines) has no Lean consumer (guard + tag only); its only Lean use of the base theorem `exists_conditional_projective_dilation` (`:182`) and the other consumer `StrategyReplacementDilation.lean:52` both instantiate `J := Unit`, so the `(D : J → ℝ)` weighting of the base theorem is exercised only trivially | not deletable (tagged). If the blueprint node can be satisfied by the `J := Unit` form, the weighted-family layer (`D`, `hD0`, `hD1`, `sum_weighted_sqrt_le`) could be dropped from both statements | as stated | 0 now; up to −60 if the tag is renegotiated | high if attempted (blueprint) | high (facts), low (actionability) |

Totals for the safe subset (#1–#6, #8): about −170 lines with no change to what is proved.

## Clusters in the dead list worth a single decision (not re-listed individually)

- **`*_runs` / `*_halts` / `*_haltsWithin` / `*_closed` template ladder.** 31 `_runs` theorems in A–L; 30
  are the pass-through `X.computes x`; 16 are referenced only inside their own file (all on the dead
  list: `axisDirectionProg_runs`, `decodeBlocksProg_runs`, `encodeBlocksProg_runs`,
  `splitBlocksProg_runs`, `fromSelfDual*Prog_runs`, `toSelfDual*Prog_runs`, `fullPauliParserProg_runs`,
  `gammaProg_runs`, `indicatorProg_runs`, `lineCheckProg_runs`, `shoupHornerProg_runs`,
  `tableProg_runs`, …). 24 of the 137 dead entries match `_(runs|halts|haltsWithin|closed|apply|valid)`.
  Decision: stop emitting the ladder per program file; the live ones (`prog_runs` 14 files,
  `uniformProg_runs`, `compiler_runs`, `bothUnary_runs`) are the only ones consumed.
- **Contrapositive twins in `HonestPrefixSupport.lean`** (`:47`, `:73`, `:105`, `:112`, `:131`, ~35
  lines): each `*_eq_zero_of_prefix_unattained` / `auxOp_eq_zero_of_prefixGuard` is `by_contra` of the
  neighbouring `*_attained` lemma. The file's only external consumer is `auxOp_nonzero_prefixGuard`
  (`Background/Introspection/BinaryQuotientComplete.lean`).
- **`AuxiliaryDualProgram.lean:59-75`**: `dualProg` + `dualProg_correct` (dead) — the executable dual
  was replaced by `rowSpaceCheck` (tagged). `perp_span_rows`/`span_rows_eq_perp_ker` stay (used by
  `rowSpaceCheck_matrix`).
- **`DecisionPreparation.lean:57-90`**: `samplerData`, `deciderData`, `decodeResources`,
  `decodeResources_encode`, `source_metadata` — a decode-side reader interface no kernel consumes
  (dead list). ~30 lines with the accompanying docstrings.
- **`AdaptivePowerBudget.lean`** — the chain `adaptiveFailureBudget_le_soundness_power` (`:182`) →
  `adaptiveSoundness_power_le_errorProfile` (`:239`) → `exists_adaptiveSoundness_errorProfile` (`:259`)
  is consumed only in-file, ending at a tagged theorem with no Lean consumer; the three dead
  neighbours (`:151`, `:216`, `:250`) are side branches of the same profile computation. The
  Lean-consumed export of this file is `adaptiveSoundness_power_cases` (`PrimitiveSoundness.lean`).
  Not actionable without the blueprint; recorded so the next person does not extend the profile
  chain further.

## Rejected with evidence

- `hidingNext_of_legacy`, `hidingPauli_of_legacy` (`AuxiliaryQuotientChecks.lean:42,74`): "legacy"
  names the `CLChecks` predicate, not a superseded route; both consumed by
  `TypedQuotientPredicate.lean:72-73`.
- `hiding_chain_uniform` (`HidingTests.lean:122`) is a one-line corollary of `hiding_chain_average`
  (`:99`), but is tagged and has 3 consumers (`TypedPrefixChainEstimate:93`, `TypedPrefixChainBob:95`,
  `ReadChainEstimate:90`) — keep.
- `.symm` re-exports `parsedHide_next_commute_reversed` (`HonestParsedHiding.lean:39`),
  `parsedRead_hide_commute` (`:52`), `parsedRead_core_commute` (`HonestParsed.lean:137`): tagged and
  guard-listed; production consumers by policy.
- The `ConditionalNormalizer*` (10 files) and `HidingRigidity*`/`HidingInduction*` (7 files) chains:
  every file's docstring records a current design step, every terminal theorem is consumed by the
  next file or tagged; one-declaration files (`ConditionalNormalizerStepGame`, `StepSeed`, `Tests`,
  `IsometricSoundness`, `AdaptiveMarginalTest`) are proof stages, not wrappers — merging would only
  save file headers.
- Structures with one instance: only `IntroPrefixInvariant` (`AdaptiveInductionInvariant.lean:26`)
  is a structure in the area; it is referenced from 8 files. No single-value parameter found besides
  #9.
- `(hk : 1 ≤ k) [NeZero k]` appears together 11 times in `BasisProg.lean`/`BinaryBlockProg.lean`
  (`1 ≤ k` is derivable from `NeZero k`), but the convention originates in `MIPRE/Foundations/SAT/`
  (41 more occurrences) — out of area; only worth doing library-wide.
- `decide_and_if` (private, `DynamicParser.lean:44` and `ParserAnswers.lean:106` [M–Z]): identical
  copies, but `exact?` finds no Mathlib lemma for the equation form; `DynamicParser` imports
  `DynamicParserSlice`, not `ParserAnswers`, so a shared owner needs a new home (hygiene, −4).
- `esize_bool_le`: the two copies are in `MIPRE/Foundations/SAT/{ArrayProg,PcpFormat}.lean`, not in this
  directory.

## Hygiene batch (tiny, correct, batch under one PR)

- `exists_entry_ne_zero` (`HonestHidingAcceptance.lean:26-30`) → `Function.ne_iff` twice (probe
  compiled): −4.
- `supported_zero` (`HonestHidingChecks.lean:26-29`) is `CL.proj_eq_self_iff.mp hy i hi`
  (`MIPRE/Foundations/CL/Register.lean:93`): −3 (5 in-file uses).
- `support_mono` (`HonestLabelSupport.lean:25-30`) is `hx ▸ CL.proj_proj_of_subset' h x`: −4 (7 uses).
- `observable_one`, `observable_mul`, `observable_commute_projector`, `projector_measurement`,
  `transpose_X`, `transpose_Z`, `ZX_anticomm`, `sign_injective` (`HonestMagicSquare.lean`): general
  observable facts that belong in `MIPRE/LCS/Observable.lean` / `MIPRE/LCS/Pauli.lean` next to
  `isObservable_X`, `X_anticomm_Z` (no `Xᵀ = X` lemma exists in LCS). Net ~0, but removes eight
  privates from a 393-line file.
- Ladder `introspectOp_output_attained` → `parsedIntrospectOp_output_attained` →
  `auxOp_introspect_output_attained` (`HonestIntrospectSupport.lean:41-52`): the middle rung is a
  pure pass-through consumed once; −4.
- `hidingAliceError_nonneg`/`hidingBobError_nonneg` (`HidingRigidityOrientation.lean:62,69`),
  `coarseJointLeftError_nonneg`/`RightError_nonneg` (`HidingInduction.lean:46,50`): one dead, three
  one-liners; keep or inline.
- 22 `@[simp]`/`rfl` lemmas with zero references (`grid_zero`, `grid_four`, `residual_zero`,
  `selectedPoint_zero`, `parsedCoreOp_pair`, `ambientProjectivePOVM_mats`, …; full list in
  `liveness_fast.txt`, filter `int=0 ext=-` without `D`): not on the dead list, presumably because
  they may fire inside `simp`; verify with the compiler before touching.

## Files surveyed / not checked

- Surveyed: all 165 A–L files mechanically (declaration liveness, pass-throughs, private duplicates);
  read in full or in relevant part: `AuxiliaryPrefixScan`, `AuxiliaryScanCorrect`,
  `DecisionPreparationBound`, `DecisionPreparation`, `AuxiliaryDualProgram`, `HonestPrefixSupport`,
  `HonestIntrospectSupport`, `HonestMagicSquare` (helpers), `HonestCompleteAux`/`HonestParsedHiding`/
  `HonestPauliEdges` (swap lemmas), `HidingInductionDilation`, `AdaptivePowerBudget`,
  `AdaptiveIterationBudget`, `ErrorBounds`, `AuxiliaryQuotientChecks`, `TypedPredicate` (def of
  `check`), the cluster docstrings of `ConditionalNormalizer*`, `HidingRigidity*`, `HidingInduction*`.
- Not checked: the paper (`vidick/MIPRE-proof` not attached) — so #9 is stated as a Lean-side
  observation only; whether `simp` uses the 22 unreferenced simp lemmas; whether generalising the
  LCS kronecker lemmas (#7) elaborates unchanged at its two LCS call sites (not probed, to keep
  within the probe budget).
- Probes used: 1 `lean_run_code` (6 examples: #3, #4, #5, `exists_entry_ne_zero` confirmed;
  `decide_and_if` and matrix-entry `exact?` found nothing).
