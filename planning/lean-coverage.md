# What the blueprint accounts for, and what it does not

> **Superseded in part, 2026-09-15.** The `#print axioms` audit at the end of this file — the
> evidence behind every proof-level `\leanok` — is now performed by the build instead of by
> hand. `MIPRE/Axioms.lean` asserts each of this project's own claims sorry-free with
> `#guard_sorry_free`, the three `MIPRE/Background/*/Axioms.lean` do the same for the vendored
> results, and `scripts/lean-coverage.py` fails when the set of guarded names and the set of
> proof-level `\leanok` declarations differ in either direction. All 98 were verified clean at
> the time of the change, so the audit below was still *true*; it had simply stopped being
> *checked*, having been written against 80 modules and 1502 declarations when the tree had
> reached 122 and 2467. Read the rest of this file for what the blueprint names; do not read
> its axiom table as current.

Written for the chapter-by-chapter restructuring along the vibefeld ledger
(`planning/ledger-informed-plan.md`). The purpose is narrow: before any chapter is
rearranged, there should be a record of which Lean declarations the blueprint actually
names, so that a reorganization cannot quietly drop one.

Refresh with `scripts/lean-coverage.py`; `--check` is run by CI on every push and PR
against the committed snapshot `planning/lean-coverage.json`, and fails if a declaration
the blueprint used to name stops being named, or if a `\lean{}` name no longer resolves.
When a rename or a deliberate removal makes it fail, re-run `--refresh` and say so in the
commit message.

## The numbers

80 non-vendored modules hold 1502 public declarations. 48 `\lean{}` tags name 75 of
them, across 29 modules. Every one of the 75 resolves.

That ratio is not itself a problem: a blueprint names headline statements, and the great
majority of the 1502 are the lemmas that prove them. The question worth tracking is
whether each *group* of modules is accounted for by something, and by what.

| group | modules | with a tag | declarations | named | accounted for by |
| --- | --- | --- | --- | --- | --- |
| `Foundations/Cost/` | 22 | 5 | 589 | 9 | the six statements of `sec:rr-computability` |
| `TM/` | 15 | 8 | 288 | 14 | `def:multiinput-tm`, `def:machine-code`, `def:code-run`, `lem:code-canonical`, the two universal-machine lemmas |
| `LCS/` | 17 | 3 | 199 | 5 | **under-recorded — see below** |
| `Background/LIDT/Bridge/` | 8 | 0 | 135 | 0 | the proof of `thm:lidt-soundness` |
| core (`Foundations/*.lean`, `HaltingGameValue`) | 6 | 6 | 99 | 37 | chapters 2 and 7 |
| `Cslib/` | 3 | 0 | 81 | 0 | nothing, deliberately — destined for upstream Cslib |
| `Background/` (Gowers–Hatami, LIDT game/soundness) | 3 | 3 | 70 | 4 | chapter 3 |
| `Background/Repetition/` | 4 | 4 | 41 | 6 | chapter 5 |
| axiom guards | 2 | 0 | 0 | 0 | nothing to name: `#guard_msgs` files |

## Accounted for, even with no tag

- **`Foundations/Cost/` (403 unnamed declarations).** The ambient cost model is a
  documented departure (§`sec:departures`); the blueprint states what it delivers —
  `lem:universal-tm`, `lem:smn`, `lem:kleene`, `def:succinct`,
  `lem:recursive-compression`, `lem:compressible-criterion`, `lem:halting-form` — and
  not how. The largest single file, `Cost/Interpreter.lean` (73), is the interpreter
  those six statements are proved against. No blueprint work is owed here.
- **`Background/LIDT/Bridge/` (135).** These transport the vendored MIPStarRE soundness
  theorem into MIPRE vocabulary. Their entire output is
  `MIPRE.LIDT.lowIndividualDegree_soundness`, which is named by `thm:lidt-soundness`
  with a proof-level `\leanok` and guarded by `Background/LIDT/Axioms.lean`. The bridge
  is the proof of that theorem, so it is accounted for the way any proof is.
- **`Cslib/` (81).** Multi-tape deterministic machines and `RelatesInSteps`, written to
  be contributed upstream. Outside the blueprint on purpose.
- **`TM/` (215 unnamed).** Supporting lemmas for the five tagged TM statements. Two of
  those five (`lem:universal-machine`, `lem:bounded-universal-machine`) are still
  `sorry`, which is the honest reason the group looks thin.

## Under-recorded: the LCS and Magic Square development

`LCS/` holds 199 declarations in 17 modules and the blueprint names 5, in four
environments (`def:lcs-instance`, `def:lcs-game`, `def:solution-group`,
`thm:lcs-perfect`). The unnamed bulk is a real mathematical development, not scaffolding:

| module | declarations |
| --- | --- |
| `LCS/Pauli.lean` | 31 |
| `LCS/SolutionGroup/Representation.lean` | 23 |
| `LCS/EPR.lean` | 22 |
| `LCS/Strategy/Equivalence.lean` | 16 |
| `LCS/Strategy/ProjectorStrategy.lean` | 14 |
| `LCS/Strategy/ObservableStrategy.lean` | 11 |
| `LCS/Common.lean` | 10 |
| `LCS/MagicSquare/SolutionGroup.lean` | 8 |
| `LCS/Measurement.lean` | 8 |
| `LCS/Strategy/ObservableToProjector.lean` | 8 |
| `LCS/WinningCondition.lean` | 8 |
| `LCS/MagicSquare/Strategy.lean` | 6 |
| `LCS/Observable.lean` | 4 |
| `LCS/MatrixSOS.lean` | 1 |

This is where blueprint work is owed, and it lines up with the ledger: node `1.2.2.4.1`
(Magic Square rigidity) is one of the three *admitted* nodes of the campaign, and stage
1.2 carries 169 of the 291 challenges. So the missing blueprint text and the ledger's own
weakest point are the same place. Doing stage 1.2 should begin by giving these modules
statements to be named by — in particular the three observable/projector strategy
equivalences (`Strategy/Equivalence`, `Strategy/ObservableToProjector`,
`Strategy/ProjectorStrategy`), which are reusable well beyond Magic Square, and the
Pauli group development, which is the concrete witness behind `thm:lcs-perfect`.

## Sorry-freeness of what is named

`#print axioms` over all 75 names: 70 depend on nothing beyond
`[propext, Classical.choice, Quot.sound]`. Five carry `sorryAx`:

| Lean name | blueprint | note |
| --- | --- | --- |
| `MIPRE.syncValue_le_quantumValue` | `lem:sync-le-valstar` | the free comparison, used by `cor:main-quantum` |
| `MIPRE.LCS.exists_tensorStrategy_value_eq_one_of_localLoss_annihilates_epr` | `thm:lcs-perfect` | intended proof written out in the docstring |
| `Turing.exists_universalCode` | `lem:universal-machine` | issue #17 |
| `Turing.exists_boundedUniversalCode` | `lem:bounded-universal-machine` | issue #18 |
| `HaltingGameValue.halting_reduces_to_gameValue` | `thm:main` | the project's target |

Each of the five carries a statement-level `\leanok` and no proof-level one, and no
environment in the blueprint claims a proof-level `\leanok` for a declaration that
depends on `sorryAx`. The `\leanok` marking is therefore exact in both directions as of
this snapshot, and `scripts/lean-coverage.py --check` keeps the first direction that way.
