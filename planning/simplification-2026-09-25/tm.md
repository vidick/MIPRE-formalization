<!-- Area survey written by a Claude Code agent on 2026-09-25 for planning/simplification-2026-09-25.md; read-only, grep-and-read evidence plus the compiler probes it names. Consumer counts are snapshots. -->

# find-simplification survey: `MIPRE/TM/` (63 files, 24k lines)

Read-only survey, 2026-09-25. Grep proposes, elaboration decides: every consumer count below
was grepped on the final name component (`rg -F`, one name at a time, `MIPRE/` +
`blueprint/src/`, own file subtracted), then the hits were read. Compiler probes used: 3 of
the budget of ~8 (`lean_run_code` ×2, `lean_local_search` ×8, which is not a compiler probe).

## Structure that decides everything else

The import graph of `MIPRE/TM/` is two disconnected regimes hanging off one shared file:

* **Live route** (`thm:succinct-sat`, PCP, classical PCP): `MultiInput/Deterministic.lean` →
  `Interp/*` (14 files, 6.5k lines) → `CookLevin/*` (35 files, 12.5k lines) →
  `MIPRE/Axioms.lean`, `MIPRE/Background/AnswerReduction/Instance.lean`. Consumed heavily
  (55 axiom-guard entries, 45 blueprint tags).
* **Milestone A–D island** (`planning/tm-infrastructure.md`): `MultiInput/{TapeLemmas,
  Complexity, Congr, OneInputEquiv}.lean` + `Code/*` (9 files) + `Universal/Spec.lean` =
  **2,999 lines**. Nothing in `Interp/` or `CookLevin/` names `Turing.Code`, `RawCode`,
  `encodeCode`, `decodeCode`, `Code.Produces`, `evalWithin` (the `evalWithin`/`runFor` hits
  in `Foundations/` are `MIPRE.Cost.*`, a different namespace). Its only consumers are the
  blueprint subsection `sec:machine-model` (14 `\lean{}` tags) and `MIPRE/Axioms.lean:294-296`
  (3 guards). `planning/succinct-cook-levin.md` records why: the interpreter machine `U` was
  written directly as a `MultiInputTM` and "no compiler from `Prog` to `Code k`" was needed,
  so the island's stated role (a) "substrate for `thm:succinct-sat`" did not materialize; role
  (c) "paper-literal machine statements" ended with issues #17/#18 closed 2026-09-24.

So the durable candidates split into (1) island files nothing consumes and (2) small
hygiene inside the live route. The live route itself is tight: the pass-through scan found
103 one-line proofs, and on reading, all but the ones listed below are legitimate API
projections (`Holds.cons`, `TapeIs.holds`, `Desc.state`, ...) or the deliberate
`FieldsR`/`FieldsF` "programs match formulas by `rfl`" design (`FieldProg.lean` docstring).

## Candidates

| # | shape | declarations (path:line) | survivor / replacement | consumers (grepped, then read) | est. net lines | risk | conf. |
|---|---|---|---|---|---|---|---|
| 1 | file nothing consumes (superseded route: Milestone E glue, E abandoned 2026-09-09) | `MIPRE/TM/MultiInput/Congr.lean` whole file: `Turing.MultiInputTM.Cfg.congrState` (:48) … `computesInTimeAndSpace_congrSymbol` (:329); 32 declarations | delete file; `lake exe mk_all` | 0 importers (`rg -l "^import MIPRE.TM.MultiInput.Congr$"` = only `MIPRE.lean`); all 15 non-simp lemmas are on the dead list; no blueprint tag or `\lean{}` mention; `git log -S congrState` outside the file: nothing. Rationale recorded (tm-infrastructure "Adopted for Milestone A … Milestone E") is superseded by the route-β decision in the same file and the `succinct-cook-levin.md` note that `U` is built directly. | −344 | low | high |
| 2 | file nothing consumes (Milestone A acceptance test) | `MIPRE/TM/MultiInput/OneInputEquiv.lean` whole file: `Turing.MultiInputTM.toCSLib` (:33), `ofCSLib` (:41), `toCSLib_ofCSLib` (:50), `ofCSLib_toCSLib` (:54), `cfgEquiv` … `toCSLib_computesInTimeAndSpace` (:194) | delete file, or keep as the one witness of the blueprint sentence | 0 importers; all 11 theorems dead-listed; not tagged. The only textual consumer is the prose "At $i = 1$ this is exactly the CSLib multi-tape model" in `blueprint/src/content/04_computability.tex:31-32` (no `\lean{}`), and `Deterministic.lean:17-18` docstring. If deleted, that sentence should lose "exactly" or cite nothing. | −204 | med (blueprint prose) | high |
| 3 | scaffolding nothing consumes; two standing `sorry`s | `MIPRE/TM/Universal/Spec.lean`: `Turing.encodeBoundedResult` (:52), `Turing.exists_universalCode` (:66, sorry), `Turing.exists_boundedUniversalCode` (:87, sorry) | delete file + blueprint nodes `lem:universal-machine` (`04_computability.tex:82-97`) and `lem:bounded-universal-machine` (:99-115) + `CONTRIBUTING.md:65` paragraph; keep the "machine-level counterpart" sentence at `:217-220` as prose | 0 importers; `encodeBoundedResult` used only inside the file; tagged (2 tags) but both nodes' proofs read "Not planned: issue #17/#18 closed 2026-09-24"; issues #17/#18 closed as not planned; CONTRIBUTING calls them "the standing exception" to the sorry policy. Decision D13 froze them "so that later work can be planned against a fixed specification" — that later work (Milestones E–G) is recorded as no longer needed. Removing them also removes the only non-vendored `sorry`s in the library. | −101 Lean, −36 LaTeX, −1 CONTRIBUTING paragraph | med (blueprint edit; maintainer decision) | high |
| 4 | speculative generality: packaged bound predicate with no instance | `Turing.MultiInputTM.ComputesFunWithBounds` `MIPRE/TM/MultiInput/Complexity.lean:43-51` (+ docstring :16-23) | delete | dead-listed (count 3 = def + its docstring + module docstring); decision D4 records its *shape*, not a consumer; `ComputesInTimeAndSpace` (:31, tagged) stays | −18 | low | high |
| 5 | definition whose only purpose was dead lemmas | `MIPRE.TM.CookLevin.Desc.Fields.numEq` `Kinds.lean:27`, `Fields.numEq_refl` :31, `numEqF` :55, `eval_numEqF` :60-93, `numEqR` `FamilyProg.lean:164`, `numEqR_apply` :168 | delete the chain | `numEq`/`numEq_refl`/`eval_numEqF` dead-listed; `numEqF` is used only by `numEqR`/`numEqR_apply`; `numEqR` has no consumer anywhere (`rg numEqR` → only FamilyProg.lean:164-169). The family predicates never compare two records numerically (the window family compares fields one at a time). | −50 | low | high |
| 6 | superseded parallel development (five properties proved twice, once on each side of a rewrite) | `MIPRE.TM.CookLevin.Pad.pcpCircuitProg_wellFormed` `PcpPrepare.lean:70`, `_inputs` :74, `_size` :79, `_variables` :85, `_describes` :92 | the same five facts are `fixedCircuit_wellFormed/_inputs/_variables/_describes` in `PcpBridge.lean:23-40` on `fixedCircuit`, reached through `pcpCircuitProg_eq_fixed` (`PcpPrepare.lean:57`, live: `PcpBridge.lean:95,123`) | all five dead-listed (their counts 1–2 are the internal uses `_variables` → `_inputs`, `_size`); `pcpCircuitProg` itself and `_apply`/`_eq_fixed` are live (`PcpVerifier.lean:47,55`) | −30 | low | high |
| 7 | hypotheses no theorem uses, carried by a section `variable` and cancelled by 66 `omit` lines | `MIPRE/TM/CookLevin/Semantics.lean:28` `variable … [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State]` with 22 `omit … in` (of 25 declarations); `Correct.lean:39` with 22 `omit` (of 34); `Sound.lean:128,287,497,742` with 22 `omit` (of 44) | move the four instance binders out of the section `variable` and put them on the few declarations that need them (Semantics: 3; Correct: 12; Sound: 22), or open a sub-section per group | the `omit` lines are the evidence: each says the declaration does not use the instance. Purely structural, no statement changes. | −66 `omit` lines, +~10 `variable`/binder lines ≈ −55 | low | high |
| 8 | port section with no consumer, mirrored "section for section" from CSLib (D8) — **rejected by rationale, recorded for the un-vendoring day** | `MIPRE/TM/MultiInput/TapeLemmas.lean` (155 lines, all 12 lemmas: only the vendored `Cslib` twins match the names); `Deterministic.lean:285-413` `TransitionRelation`, `relatesInSteps_iff_configs_eq`, `haltsAtStep`, `halting_step_unique`, `not_halts_of_repeat_nonhalt`; `:262-273` `spaceUsed_zero_tapes_eq_zero`, `spaceUsedByTape_le_spaceUsed` | keep (D1/D7/D8: upstream-shaped for CSLib) | outside `Cslib/` and the island, none of these is named anywhere; `spaceUsed`/`visitedByTapeHead` live only through the island's `ComputesInTimeAndSpace` (tagged) and `Code.Examples`; `haltsAtStep` only in `Code/Examples.lean`. The dead scan missed them because the vendored CSLib copies carry the same names. | (−300 if the island goes and D8 is dropped) | high | high as a fact; not proposed |

### The island as a whole (information, not a deletion row)

`MIPRE/TM/Code/{Raw,Observation,WellFormed,Semantics,Examples,Evaluator}.lean` +
`Code/Encoding/{Nat,MachineCode,Total}.lean` (2,097 lines) are live only through
`sec:machine-model`'s tags (`Turing.Code`, `Code.toTM`, `encodeCode`, `decodeCode`,
`codeSize`, `Code.Produces`, `Code.evalWithin`, `decodeCodeExact_encodeCode`,
`encodeCode_injective`, `decodeCodeExact_sound`) and `Axioms.lean:294-296`. No pipeline
node `\uses` `def:machine-code` or `def:code-run` except the two "not planned" lemmas of row 3.
Within it, 20 of the 99 dead-listed declarations live (`Turing.codeSize_le`, `natToBits_*`,
`encodeNat_*`, `toTM_tr*`, `runFor_succ`, `outputFor_succ`, ...). `Turing.natToBits`
(`Nat.lean:47`) shadows Mathlib's `Nat.bits` (little-endian, canonical) but carries the
recorded rationale D10 (fuel-based so the kernel evaluates it; `Nat.bits` is `binaryRec`,
which `decide` does not unfold) — rejected. The island is a maintainer-level question
("does the blueprint want a machine-model subsection the proof never touches?"), and by the
rules it is at most a redirect candidate, so it is recorded here and not scored.

Cross-area note: the vendored `MIPRE/Cslib/` (3 files, ~900 lines) is reached from the live
route only for `Turing.moveInputPos` (`MultiInput/Deterministic.lean:88,159`) and, if row 8
ever moves, `Relation.RelatesInSteps` (:343). `OneInputEquiv.lean` is the only other user.

## Rejected with evidence

* **`(by decide)` discharge of `hpc : pc.val + 1 < maxPc` and `rfl` for `instrAt k pc = …`** —
  554 `(by decide)` sites (`Interp/Step.lean` 304, `GetEnv.lean` 40, `Run.lean` 23), the same
  hypothesis pair on every `D_*`/`exec_*`/`evDispatch_round` call. Removing it needs a total
  `next_` (saturating `Fin maxPc` successor or `pc : Fin (maxPc-1)`), which is a redesign of
  `Routines.lean:25-41` and every routine spec; no deletion it enables is clear. Not proposed.
* **30 tape-distinctness simp lemmas** `MIPRE.TM.Interp.C_ne_E … BUD_ne_CNT`
  (`Step.lean:32-61`). Probe (`lean_run_code` on `import MIPRE.TM.Interp.Instr`): plain `simp`
  closes `C ≠ E` (it is `0 ≠ 1`) but **not** `BUD ≠ CNT` (`5 ≠ 4` behind `abbrev`s), so the
  lemmas do work as simp rewrite rules. Keep.
* **`nbits w n := bitsOfNat w n`** (`Layout.lean:298`) with three forwarding lemmas
  (`length_nbits`, `bitsVal_nbits`, `bitsVal_nbits_of_lt`, :300-306): a pure alias, but with
  ~190 uses across 11 files (`FamilyFml` 61, `Layout` 36, `Kinds` 30); collapsing saves 5
  lines and touches 190 sites. Not worth it.
* **`PreTo` / `PreTo1` / `StepTo` / `RunTo`** (`Step.lean:98-116`): `PreTo1` is `PreTo` with
  `1 ≤ n`, which `sim_run` needs for progress; `RunTo` is used once (`:1865`, the main step
  theorem). A ladder, but each rung is consumed. Only `PreTo1.toPreTo` (:122) is dead (hygiene).
* **`InputsLt.and'/or'/not'/const'`** (`FamilyFml.lean:120-128`): no unprimed base versions
  exist in `Foundations/SAT/FmlLib.lean` (only `mux`, `constBits`, `eqConst`, `eqFields`), so
  they are not duplicates; `and'`/`or'`/`not'` have 8/10/35 uses. Only `const'` is dead.
* **`cfgAt` (`Tableau.lean:233`) wrapping `M.configs (M.initCfg input) t`** — a one-line
  alias with ~150 uses across Semantics/Correct/Sound; the alias is what keeps the tableau
  statements readable. Keep.
* **`Code/Examples.lean`** (242 lines, `#decide` acceptance tests): consumed by
  `Encoding/Total.lean:36` (`defaultRejectCode`, decision D6) and its own `example`s at
  `Total.lean:140-147`; part of the island question, not separately removable.
* **`MultiInput/TapeLemmas.lean` + `Deterministic.lean` space/RelatesInSteps sections**
  (row 8): recorded rationale D1/D8 (mirror CSLib exactly for later un-vendoring). Challenged
  only by the fact that nothing consumes them; that fact is recorded above, not acted on.

## Hygiene batch (tiny, correct, batch into one PR)

Live-route duplicates and one-liners (each ≤ 5 lines):

* `MIPRE.TM.Interp.overwrite_append_nil'` `Step.lean:182` is a verbatim restatement of
  `overwrite_append_nil` `Desc.lean:53` (identical statement, proof `:= overwrite_append_nil a w hp`);
  2 call sites in `Step.lean`. −3.
* `MIPRE.TM.CookLevin.Desc.length_bits` `Sat.lean:32` (`@[simp]`) duplicates
  `MIPRE.TM.Interp.length_bits` `Tape.lean:137` (`@[simp]`, same `bits`, `open Interp` in
  scope). −1.
* `MIPRE.TM.CookLevin.Desc.mem_bits'` `Sat.lean:149` is the curried form of
  `MIPRE.TM.Interp.mem_bits` `Run.lean:44` (in scope). −4.
* `MIPRE.TM.CookLevin.Desc.boolsOf` `Sat.lean:39` = `List.map MIPRE.TM.Interp.boolOf`
  (`InputRoutines.lean:228`); `bits_boolsOf` (`Sat.lean:44`) and `map_boolOf_bits`
  (`Run.lean:50`) are the two directions of one round trip. −6 if `boolsOf` is replaced by
  `·.map boolOf`.
* `MIPRE.TM.Interp.SignType.one_eq_pos` / `neg_one_eq_neg` `Routines.lean:950-951` are
  Mathlib's `SignType.pos_eq_one` / `neg_eq_neg_one` (`Mathlib/Data/Sign/Defs.lean`) reversed;
  `one_eq_pos` is dead. −2.
* `MIPRE.TM.CookLevin.Desc.getD_append_left` / `getD_append_right` `Decoupled.lean:39-46`
  are `List.getD_append` / `List.getD_append_right` (`Mathlib/Data/List/GetD.lean`, confirmed
  by `lean_local_search`; the exact-shape `exact?` probe failed only because that module is
  not in the file's import closure — `Tape.lean`'s `import Mathlib.Tactic` does not pull it).
  Replace with the import. −8.
* `MIPRE.TM.CookLevin.Desc.range'_drop_take` `FieldFml.lean:29-35` composes core's
  `List.drop_range'` and `List.take_range'_of_length_ge`. −5.
* `MIPRE.TM.Interp.getElem?_append_right'` `Step.lean:1037`, `kontRepr_cons'` `Step.lean:1033`
  (= `kontRepr_cons` `Repr.lean:146` + `frameRepr_eq` :95; 25 uses, so keep unless simp
  handles it), `Env.get_nil'` `GetEnv.lean:390` (`by simp`, 3 uses): convenience restatements.
* Dead one-liners not worth separate rows (all on the dead list): `Params.lean:52,64,66,68`
  (`Gc_eq`, `chk_size_le`, `Gc_le`, `Gc_pos`), `Desc.lean:403,406` (`D_halt`, `D_emit`, the
  only `D_*` with no `case_*` consumer), `Reach.lean:128` (`HaltsIn.configs_state`),
  `Step.lean:122` (`PreTo1.toPreTo`), `Desc.lean:218` (`cast_ds`), `FamilyFml.lean:128,136`
  (`InputsLt.const'`, `nbitsC`), `Tape.lean:111,117` (`BlankBeyond.update_of_lt`,
  `BlankBefore.update_of_le`), `Routines.lean:38` (`resolve_jmp`), `Decoupled.lean:48`
  (`clauseInput_eq'`).
* Not shadows (checked): `Assemble.lean:43 size_le_self` (no `Nat.size_le_self` in this
  Mathlib), `FamilyFml.lean:25 Bool.eq_decide_of_iff`, `Describer.lean:25 getD_drop_eq`,
  `LayoutProg.lean:87 getD_bits` (no `Nat.testBit_eq_getD`), `Correct.lean:57
  SignType.cast_bounds` (Mathlib's `neg_one_le`/`le_one` are on `SignType`, not its cast).

## Files surveyed and what was not checked

* Read in full or by outline: all 63 files' module docstrings; `Interp/{Tape,Instr(programs),
  Reach,Desc,Step(outline+key sections),Routines(outline),Run(head),InputRoutines(part)}`;
  `CookLevin/{Correct,Sound,Semantics,Tableau,Params,Kinds,FamilyFml(part),FamilyProg(part),
  Layout(part),Sat,Decoupled,Describer,Assemble,PcpPrepare,PcpBridge}`; all of `MultiInput/`,
  `Code/` heads, `Universal/Spec.lean`; blueprint `04_computability.tex:1-120,200-235`;
  `planning/tm-infrastructure.md`, `planning/succinct-cook-levin.md` (head), `CONTRIBUTING.md:65`.
* Scripts (in the scratchpad): `inv.py` → `tm_inventory.tsv` (2,287 declarations with
  cross-file reference counts), `pt.py` → `passthrough.txt` (103 one-line proofs, read),
  `dup.py` (identical-statement finder across `MIPRE/TM` + `MIPRE/Foundations`: 1 true
  duplicate, row "hygiene 1").
* Not checked: whether `simp` would close the 25 `kontRepr_cons'` sites without it (one
  more probe); the deep interior of `FamilyFml.lean` (81 `InputsLt.*` and 87 `eval_*` lemmas,
  one per formula — the pattern is uniform and each is consumed by `FamilyProg`/`Describer`,
  so no ladder was pursued); `Sound.lean:287-742` proof internals; whether any `\uses` edge
  in `sec:machine-model` would need `scripts/blueprint-edges.py --fix` after rows 2–3.
