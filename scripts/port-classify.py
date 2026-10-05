#!/usr/bin/env python3
"""Sort the declarations of vendored LDT files into quantum and classical, and measure the port.

The commuting-operator port (`planning/c6b-plan.md`, milestones M0-M14) ports the quantum
declarations of the `MIPStarRE` Lake dependency (`.lake/packages/MIPStarRE/MIPStarRE/LDT/`) to the symmetric model
and imports the classical ones (sampling, distributions, scalar error constants) unchanged. The
sizes of the remaining stages in section 3 of the plan are estimated as

    ported lines ~ r * (vendored quantum-declaration lines) + 58 * (files),

and this script produces both inputs: the quantum-declaration lines of a vendored directory, and
the ratio r measured on files that are already ported.

**The rule.** A line is counted by `wc -l`. A declaration starts at a line that begins (after
optional attributes and modifiers) with `theorem`, `lemma`, `def`, `abbrev`, `structure`,
`instance`, `class`, `inductive`, `example`, `opaque` or `irreducible_def`, and runs to the line
before the next declaration start (or the end of the file), so the docstring of the next
declaration, `namespace`/`end` lines and blank lines are charged to the declaration before them.
Everything before the first declaration start (copyright, module docstring, imports, `open`) is
the file's *header*. A declaration is *quantum* when its text, with `/- ... -/` comments removed,
matches `QUANTUM` below (it mentions the state, `ev`, a measurement, a placement, `ᴴ`, a strategy
or a matrix), and *classical* otherwise.

The rule is a heuristic, not a dependency analysis: a classical declaration whose proof calls a
quantum lemma by a name that matches none of the patterns counts as classical. On
`CommutativityPoints` it finds 452 classical lines, against about 500 counted by hand.

Usage:

    python3 scripts/port-classify.py [--per-file] [--exclude PATH ...] PATH ...
    python3 scripts/port-classify.py --ratio [--per-file] PATH ...

Without `--ratio`, each PATH is a vendored file or directory, relative to the vendored LDT root
(`CommutativityPoints`, `Pasting/Defs.lean`) or to the repository; `--exclude` removes files or
directories from the count (`--exclude SelfImprovement/MatrixRealization`). The output gives, per
PATH, the files, the total lines and their split into quantum declarations, classical
declarations and header, and the classical share of the declaration lines.

With `--ratio`, each PATH is a ported file or directory under `MIPRE/Background/LIDT/Co/`
(relative to `Co/` or to the repository). Each ported file is paired with the vendored file of the
same relative path, and the output gives its header and body (the lines from its first
declaration on), the vendored quantum-declaration lines q, and r = body / q; then the totals, with
the mean header per file on each side.

Examples (the figures of the plan's section 3):

    python3 scripts/port-classify.py CommutativityPoints Commutativity Pasting
    python3 scripts/port-classify.py SelfImprovement --exclude SelfImprovement/MatrixRealization \\
        --exclude SelfImprovement/Theorems/Results/SdpMatrixBridge.lean
    python3 scripts/port-classify.py --ratio --per-file CommutativityPoints
"""

from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIDT = os.path.join(ROOT, "MIPRE", "Background", "LIDT")
VENDORED = os.path.join(ROOT, ".lake", "packages", "MIPStarRE", "MIPStarRE", "LDT")
PORTED = os.path.join(LIDT, "Co")

QUANTUM = re.compile(
    r"QuantumState|\bev\b|SubMeas|leftTensor|rightTensor|opTensor|MIPStarRE\.Quantum|\bOp\b"
    r"|SymStrat|ProjStrat|IdxSubMeas|Measurement|sddError|ConsRel|SDDRel|SDDOpRel|qSDD"
    r"|swapDensity|PermInvState|quantum_nonneg|Matrix|OpFamily|ᴴ|strategy|psi\b|ψ|consError"
    r"|bndError|sscError|SSCRel|qCons|qBipartite|liftLeft|liftRight|PSD|PosSemidef"
    r"|normalizedTrace|density|Bipartite|Strat\b|Strategy"
)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec |scoped )*"
    r"(?:theorem|lemma|def|abbrev|structure|instance|class|inductive|example|opaque"
    r"|irreducible_def)\b"
)
COMMENT = re.compile(r"/-.*?-/", re.S)


def lines_of(path: str) -> list[str]:
    """The lines of a file, counted as `wc -l` counts them."""
    text = open(path, encoding="utf-8").read()
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines


def decl_starts(lines: list[str]) -> list[int]:
    return [i for i, line in enumerate(lines) if DECL.match(line)]


def classify(path: str) -> tuple[int, int, int]:
    """(quantum-declaration lines, classical-declaration lines, header lines) of a file."""
    lines = lines_of(path)
    starts = decl_starts(lines)
    quantum = classical = 0
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        block = COMMENT.sub("", "\n".join(lines[s:e]))
        if QUANTUM.search(block):
            quantum += e - s
        else:
            classical += e - s
    header = starts[0] if starts else len(lines)
    return quantum, classical, header


def resolve(path: str, base: str) -> str:
    for candidate in (os.path.join(base, path), os.path.join(ROOT, path), path):
        if os.path.exists(candidate):
            return os.path.abspath(candidate)
    sys.exit(f"port-classify: no such file or directory: {path}")


def lean_files(path: str) -> list[str]:
    if os.path.isfile(path):
        return [path]
    found = []
    for root, _, files in os.walk(path):
        found += [os.path.join(root, f) for f in files if f.endswith(".lean")]
    return sorted(found)


def excluded(path: str, exclusions: list[str]) -> bool:
    return any(path == x or path.startswith(x.rstrip(os.sep) + os.sep) for x in exclusions)


def classify_main(args: argparse.Namespace) -> None:
    exclusions = [resolve(x, VENDORED) for x in args.exclude]
    for target in args.paths:
        files = [f for f in lean_files(resolve(target, VENDORED)) if not excluded(f, exclusions)]
        tq = tc = th = 0
        for f in files:
            q, c, h = classify(f)
            tq, tc, th = tq + q, tc + c, th + h
            if args.per_file:
                rel = os.path.relpath(f, VENDORED)
                print(f"  {rel:64s} total {q + c + h:6d} quantum {q:6d} classical {c:6d} header {h:5d}")
        share = tc / (tq + tc) if tq + tc else 0.0
        print(f"{target:45s} files {len(files):3d} total {tq + tc + th:6d} quantum {tq:6d} "
              f"classical {tc:6d} header {th:5d} classical-share {share:.2f}")


def ratio_main(args: argparse.Namespace) -> None:
    for target in args.paths:
        files = lean_files(resolve(target, PORTED))
        rows = []
        for f in files:
            rel = os.path.relpath(f, PORTED)
            vendored = os.path.join(VENDORED, rel)
            if not os.path.exists(vendored):
                print(f"  {rel}: new file, no vendored counterpart")
                continue
            lines = lines_of(f)
            starts = decl_starts(lines)
            header = starts[0] if starts else len(lines)
            q, c, vh = classify(vendored)
            rows.append((rel, len(lines), header, len(lines) - header, q, c, vh))
        for rel, n, h, body, q, c, vh in rows:
            if args.per_file:
                r = f"{body / q:.2f}" if q else "-"
                print(f"  {rel:52s} ported {n:4d} (header {h:3d}, body {body:4d}) | "
                      f"vendored quantum {q:4d} classical {c:4d} header {vh:3d} | r {r}")
        if not rows:
            continue
        t = [sum(row[i] for row in rows) for i in range(1, 7)]
        print(f"{target:45s} files {len(rows):3d} ported {t[0]:5d} (header {t[1]:4d}, body {t[2]:5d}) "
              f"| vendored quantum {t[3]:5d} classical {t[4]:5d} header {t[5]:4d} | "
              f"r {t[2] / t[3]:.2f} | header per file ported {t[1] / len(rows):.0f} "
              f"vendored {t[5] / len(rows):.0f}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--ratio", action="store_true",
                        help="measure r on ported files under Co/ against their vendored files")
    parser.add_argument("--per-file", action="store_true", help="also print one line per file")
    parser.add_argument("--exclude", action="append", default=[],
                        help="vendored file or directory to leave out (repeatable)")
    args = parser.parse_args()
    if args.ratio:
        ratio_main(args)
    else:
        classify_main(args)


if __name__ == "__main__":
    main()
