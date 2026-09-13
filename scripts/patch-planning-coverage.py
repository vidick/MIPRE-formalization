#!/usr/bin/env python3
"""Record the 2026-09-13 \\leanok / blueprint-coverage audit in the planning files.

Exact-string replacement only; --check asserts each anchor occurs exactly once and
that the edit has not already been applied. (planning/next-steps.md has been corrupted
once by a patch script that appended instead of replacing; hence the discipline.)
"""
import sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
EDITS = []

def edit(relpath, anchor, replacement, why, marker):
    EDITS.append((relpath, anchor, replacement, why, marker))

# -- next-steps.md, item 4: record the parts now delivered -------------------
edit("planning/next-steps.md",
"""- Deliverables: `MIPRE/Foundations/ValueApprox.lean` (enumeration, density, the `RePred`
  statement, its `Prog` form); the `FromPartrec.lean` lemma; `\\lean`/`\\leanok` on
  `lem:value-lower-approx` and `def:game-description`; the chapter-3 table row.
""",
"""- Deliverables: `MIPRE/Foundations/ValueApprox.lean` (enumeration, density, the `RePred`
  statement, its `Prog` form); the `FromPartrec.lean` lemma; `\\lean`/`\\leanok` on
  `lem:value-lower-approx` and `def:game-description`; the chapter-3 table row.
- Delivered 2026-09-13: `def:game-description` now carries
  `\\lean{HaltingGameValue.GameData, HaltingGameValue.GameData.toGame}` and `\\leanok`, and
  `rem:standalone-restatement` (chapter 7) records the split this item's "decision to take
  first" is about — that `HaltingGameValue` re-declares the game, the strategy and the
  value on Mathlib alone — with `gameValue` and `GameData.equivTuple` tagged. That makes
  the decision visible in the blueprint without pre-empting it: the recommended
  foundations `GameDescription` and the agreement lemma are still owed.
  `lem:norm-two-psd` and `lem:perturbation-split` (chapter 3) now name the four
  `ValueApprox` lemmas that exist. `lem:value-lower-approx` itself still has no Lean.
  On the route, read Finding 3 of `planning/ledger-informed-plan.md` before the Cayley
  paragraph above: the ledger settles this against Cayley.
""",
"record item 4's delivered parts",
"Delivered 2026-09-13: `def:game-description` now carries")

# -- next-steps.md: the audit itself, as its own section at the end ----------
edit("planning/next-steps.md",
"""- **R9 — offered contributions** (§14).""",
"""## The blueprint/Lean coverage audit of 2026-09-13

Prompted by the question of whether the ledger-driven restructuring could lose Lean code.
Full record in `planning/lean-coverage.md`; the mechanical part is
`scripts/lean-coverage.py`, now run by CI on every push and PR.

- **The `\\leanok` marking was already exact.** `#print axioms` over every name the
  blueprint cites: the only five that depend on `sorryAx` are
  `MIPRE.syncValue_le_quantumValue`, `MIPRE.LCS.exists_tensorStrategy_...epr`,
  `Turing.exists_universalCode`, `Turing.exists_boundedUniversalCode` and
  `HaltingGameValue.halting_reduces_to_gameValue`, and those five are exactly the ones
  with a statement-level `\\leanok` and no proof-level one. Nothing was overclaimed, so
  nothing needed retracting.
- **What was missing was tags, not marks.** Six environments gained `\\lean{}`:
  `def:game-description`, `thm:main` (the project's own target, previously named only in
  prose), `rem:standalone-restatement`, `lem:halting-form`, `lem:norm-two-psd` and
  `lem:perturbation-split`. Distinct names cited went 64 → 75.
- **`MIPRE.Cost.recursive_compression_halting` and
  `MIPRE.Cost.compressibility_criterion_halting`** were finished, sorry-free, and named
  nowhere in the blueprint. They are the Mathlib-halting form of the two reduction
  lemmas — the seam at which the cost model meets `Nat.Partrec.Code` — and are now
  `lem:halting-form` in chapter 4, with a proof-level `\\leanok`.
- **The one real gap is `LCS/`**: 199 declarations in 17 modules, of which the blueprint
  names 5. The Pauli development, the three observable/projector strategy equivalences and
  the Magic Square modules have no blueprint statements to be named by. This coincides
  with the ledger's own weakest point — node `1.2.2.4.1` (Magic Square rigidity) is one of
  three admitted nodes and stage 1.2 carries 169 of the 291 challenges — so stage 1.2
  should start by writing those statements. Everything else unnamed is accounted for:
  `Cost/` by the six statements of `sec:rr-computability`, `LIDT/Bridge/` as the proof of
  `thm:lidt-soundness`, `Cslib/` deliberately (upstream-bound), `TM/` by the five tagged
  TM statements.
- **Regression guard.** `planning/lean-coverage.json` is the committed snapshot;
  `scripts/lean-coverage.py --check` fails if a declaration the blueprint used to name
  stops being named, if a covered module loses all coverage, or if a `\\lean{}` name stops
  resolving. A deliberate rename means re-running `--refresh` and saying so in the commit
  message. The checker is multi-line-aware, which matters: the blueprint wraps several
  `\\lean{}` tags across lines and a per-line grep silently skips their continuations.

- **R9 — offered contributions** (§14).""",
"add the coverage-audit section",
"## The blueprint/Lean coverage audit of 2026-09-13")

# -- ledger-informed-plan.md: the progress table now has blueprint homes ----
edit("planning/ledger-informed-plan.md",
"""| `1.1.7.2.1` (norm constraint half) | — | `MIPRE.ValueApprox.posSemidef_realSmul_one_add_and_sub_iff` | proved 2026-09-13 |
| `1.1.7.2.1` (exact arithmetic, psd decidability) | — | — | open |
| `1.1.7.2.2` candidate set finiteness | — | — | open |
| `1.1.7.2.3` stability | — | — | open |
| `1.1.7.2.4` density | — | — | open |
""",
"""| `1.1.7.2.1` (norm constraint half) | `lem:norm-two-psd` | `MIPRE.ValueApprox.posSemidef_realSmul_one_add_and_sub_iff` | proved 2026-09-13 |
| `1.1.7.2.1` (exact arithmetic, psd decidability) | — | — | open |
| `1.1.7.2.2` candidate set finiteness | — | — | open |
| `1.1.7.2.3` stability (the split) | `lem:perturbation-split` | `MIPRE.ValueApprox.dotProduct_mulVec_perturb` | proved 2026-09-13 |
| `1.1.7.2.3` stability (the bound) | — | — | open |
| `1.1.7.2.4` density (the split) | `lem:perturbation-split` | `MIPRE.ValueApprox.kronecker_sub_kronecker`, `dotProduct_kronecker_perturb` | proved 2026-09-13 |
| `1.1.7.2.4` density (the bound) | — | — | open |
""",
"give the ValueApprox nodes their blueprint homes",
"`lem:perturbation-split` | `MIPRE.ValueApprox.dotProduct_mulVec_perturb`")


def main():
    check = "--check" in sys.argv
    seen, problems = {}, []
    for rel, anchor, repl, why, marker in EDITS:
        p = ROOT / rel
        text = seen.get(rel, p.read_text())
        n = text.count(anchor)
        if n != 1:
            problems.append(f"{rel}: anchor for '{why}' occurs {n} times, expected 1")
            continue
        if marker not in repl:
            problems.append(f"{rel}: marker for '{why}' is not in the replacement")
            continue
        if marker in text:
            problems.append(f"{rel}: '{why}' already applied")
            continue
        seen[rel] = text.replace(anchor, repl, 1)
        print(f"  ok  {rel}: {why}")
    if problems:
        for q in problems:
            print("  FAIL " + q, file=sys.stderr)
        return 1
    if check:
        print("check passed; nothing written")
        return 0
    for rel, text in seen.items():
        (ROOT / rel).write_text(text)
        print(f"wrote {rel}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
