#!/usr/bin/env python3
"""Vendor the MIPStarRE low individual degree test development into this repository.

Usage (from the repository root):

    python scripts/vendor-lidt.py --source <path to a MIPStarRE clone> --commit <sha>

The script

* checks that the clone is at the requested commit;
* deletes and recreates ``MIPRE/Background/LIDT/MIPStarRE/`` (the destination is
  wholly generated; local hand edits there are lost on purpose — see the plan in
  ``planning/lidt-port.md``, decisions D3 and D6);
* copies the import closure of the root modules used by this repository's bridge
  (``ROOTS`` below; pass ``--all`` to copy every module of ``MIPStarRE/Quantum/**`` and
  ``MIPStarRE/LDT/**`` instead);
* rewrites ``import MIPStarRE.X`` to ``import MIPRE.Background.LIDT.MIPStarRE.X``;
* prepends a provenance header to every copied Lean file;
* copies the upstream Mathlib-only statement closure
  ``scripts/comparator/expected/Challenge.lean.expected`` as an audit aid;
* refreshes the generated block of ``MIPRE/Background/LIDT/MIPStarRE/README.md``
  (the part between the ``BEGIN GENERATED`` / ``END GENERATED`` markers).

Afterwards run ``lake exe mk_all`` to refresh ``MIPRE.lean``, then ``lake build``.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

UPSTREAM_URL = "https://github.com/LionSR/MIPStarRE"
UPSTREAM_PREFIX = "MIPStarRE"
LOCAL_PREFIX = "MIPRE.Background.LIDT.MIPStarRE"
DEST_REL = Path("MIPRE/Background/LIDT/MIPStarRE")
COPIED_DIRS = ("Quantum", "LDT")
COPIED_FILES = ("Quantum.lean", "LDT.lean")
# The vendored modules imported by MIPRE/Background/LIDT/**; everything they transitively
# import is vendored, nothing else.
ROOTS = (
    "MIPStarRE.LDT.Basic.AxisParallelLine",
    "MIPStarRE.LDT.Basic.DiagonalLine",
    "MIPStarRE.LDT.Basic.Distribution",
    "MIPStarRE.LDT.Basic.LinePolynomials",
    "MIPStarRE.LDT.Basic.LowDegreePolynomial",
    "MIPStarRE.LDT.Basic.SubMeasurementFamilies",
    "MIPStarRE.LDT.Test.Defs",
    "MIPStarRE.LDT.Test.MainTheorem.MainFormal",
    "MIPStarRE.LDT.Test.StrategyBiProj.Measurements",
    "MIPStarRE.LDT.Test.StrategyCore",
)
IMPORT_LINE_RE = re.compile(rf"^import\s+({re.escape(UPSTREAM_PREFIX)}(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE)


def module_path(source: Path, module: str) -> Path:
    return source / (module.replace(".", "/") + ".lean")


def import_closure(source: Path, roots: tuple[str, ...]) -> list[Path]:
    """All upstream modules transitively imported by ``roots`` (including them)."""
    seen: dict[str, Path] = {}
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        path = module_path(source, module)
        if not path.exists():
            sys.exit(f"error: module {module} not found at {path}")
        seen[module] = path
        stack.extend(IMPORT_LINE_RE.findall(path.read_text(encoding="utf-8")))
    return sorted(seen.values())
CHALLENGE_REL = Path("scripts/comparator/expected/Challenge.lean.expected")

IMPORT_RE = re.compile(rf"^(\s*import\s+){re.escape(UPSTREAM_PREFIX)}(\.|\s*$)", re.MULTILINE)

BEGIN_MARK = "<!-- BEGIN GENERATED (scripts/vendor-lidt.py) -->"
END_MARK = "<!-- END GENERATED -->"

HEADER_TEMPLATE = """/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from {url}
(commit {short}, {date}) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: {upstream_path}
-/
"""


def git(source: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(source), *args], text=True).strip()


# Lean v4.33 introduced a transparency check (`backward.isDefEq.respectTransparency`) that
# rejects a number of `rw`/`simp` steps of the upstream proofs (upstream builds with Lean
# v4.32). Mathlib disables the check on affected declarations; the vendored tree is built
# with it disabled file by file, by the block below inserted after each file's imports.
TRANSPARENCY_BLOCK = """
-- Vendoring compile fix (Lean v4.33): the vendored tree is built with the pre-v4.33
-- transparency behaviour (`backward.isDefEq.respectTransparency false`), the option
-- Mathlib sets on declarations affected by Lean v4.33's check; see README.md.
set_option backward.isDefEq.respectTransparency false
"""

# Recorded compile fixes, applied after copying: `old` must occur exactly once in the
# vendored file `path` (relative to the destination directory) and is replaced by `new`.
# With the option above, six `rfl` steps follow a tactic that now closes the goal.
FIXES: list[tuple[str, str, str]] = [
    ('LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean',
     """            sum_fourierBasisProjector_eq_one]
          rfl
""",
     """            sum_fourierBasisProjector_eq_one]
          try rfl -- vendoring compile fix (Lean v4.33): `rw` now closes this step
"""),
    ('LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean',
     """            rw [fourierBasisState_inner_product_dual params v w]
            rfl
""",
     """            rw [fourierBasisState_inner_product_dual params v w]
            try rfl -- vendoring compile fix (Lean v4.33): `rw` now closes this step
"""),
    ('LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean',
     """            matrixAdjacencyOperator_spectral_decomp]
          rfl
""",
     """            matrixAdjacencyOperator_spectral_decomp]
          try rfl -- vendoring compile fix (Lean v4.33): `rw` now closes this step
"""),
    ('LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean',
     """            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, eigenvectors params α]
            rfl
""",
     """            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, eigenvectors params α]
            try rfl -- vendoring compile fix (Lean v4.33): `rw` now closes this step
"""),
    ('LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean',
     """            rw [fourierBasisState_inner_product params α β]
            rfl
""",
     """            rw [fourierBasisState_inner_product params α β]
            try rfl -- vendoring compile fix (Lean v4.33): `rw` now closes this step
"""),
    ('LDT/MainInductionStep/Defs.lean',
     """  simp [diagonalValueRepresentative, DiagonalLinePolynomial.toFun, evalLinePolynomialModel]
  rfl
""",
     """  simp [diagonalValueRepresentative, DiagonalLinePolynomial.toFun, evalLinePolynomialModel]
  try rfl -- vendoring compile fix (Lean v4.33): `simp` now closes this goal
""")
]


def insert_transparency_block(text: str) -> str:
    """Insert `TRANSPARENCY_BLOCK` right after the leading import block."""
    lines = text.split("\n")
    first = next((i for i, l in enumerate(lines) if l.startswith("import ")), None)
    if first is None:
        return TRANSPARENCY_BLOCK + text
    end = first
    while end < len(lines) and (lines[end].startswith("import ") or lines[end].strip() == ""):
        end += 1
    block = lines[first:end]
    while block and block[-1].strip() == "":
        block.pop()
    return "\n".join(lines[:first] + block + TRANSPARENCY_BLOCK.rstrip("\n").split("\n") + [""] + lines[end:])


def apply_fixes(dest: Path) -> int:
    for rel, old, new in FIXES:
        target = dest / rel
        text = target.read_text(encoding="utf-8")
        if text.count(old) != 1:
            sys.exit(f"error: recorded fix for {rel} matched {text.count(old)} times, expected 1")
        target.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    return len(FIXES)


def rewrite_imports(text: str) -> tuple[str, int]:
    count = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal count
        count += 1
        return f"{match.group(1)}{LOCAL_PREFIX}{match.group(2)}"

    return IMPORT_RE.sub(repl, text), count


def vendor(source: Path, commit: str, repo_root: Path, everything: bool) -> None:
    head = git(source, "rev-parse", "HEAD")
    if not head.startswith(commit):
        sys.exit(f"error: clone at {source} is at {head[:12]}, not {commit}")
    if git(source, "status", "--porcelain"):
        sys.exit(f"error: clone at {source} has uncommitted changes")
    date = git(source, "show", "-s", "--format=%cs", "HEAD")
    short = head[:8]

    src_root = source / UPSTREAM_PREFIX
    dest = repo_root / DEST_REL
    readme = dest / "README.md"
    readme_text = readme.read_text(encoding="utf-8") if readme.exists() else None

    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)

    files: list[Path] = []
    if everything:
        for d in COPIED_DIRS:
            files.extend(sorted((src_root / d).rglob("*.lean")))
        for f in COPIED_FILES:
            files.append(src_root / f)
    else:
        files = import_closure(source, ROOTS)

    rewritten = 0
    lines = 0
    for path in files:
        rel = path.relative_to(src_root)
        text = path.read_text(encoding="utf-8")
        text, n = rewrite_imports(text)
        rewritten += n
        text = insert_transparency_block(text)
        lines += text.count("\n")
        header = HEADER_TEMPLATE.format(
            url=UPSTREAM_URL, short=short, date=date,
            upstream_path=(Path(UPSTREAM_PREFIX) / rel).as_posix(),
        )
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(header + text, encoding="utf-8", newline="\n")

    fixed = apply_fixes(dest)

    challenge_src = source / CHALLENGE_REL
    if challenge_src.exists():
        shutil.copyfile(challenge_src, dest / CHALLENGE_REL.name)

    generated = "\n".join([
        BEGIN_MARK,
        f"- Upstream: {UPSTREAM_URL}",
        f"- Commit: `{head}` ({date})",
        f"- Vendored files: {len(files)} Lean files, {lines} lines"
        + ("" if everything else f" (the import closure of {len(ROOTS)} root modules)") + "; "
        f"{rewritten} import lines rewritten from `{UPSTREAM_PREFIX}.` to `{LOCAL_PREFIX}.`",
        f"- Audit aid: `{CHALLENGE_REL.name}` = upstream `{CHALLENGE_REL.as_posix()}`",
        "- `set_option backward.isDefEq.respectTransparency false` inserted after the imports of "
        "every file, and recorded compile fixes applied: "
        f"{fixed} (listed under \"Local deviations from upstream\")",
        END_MARK,
    ])
    if readme_text is None:
        readme_text = DEFAULT_README.format(generated=generated)
    elif BEGIN_MARK in readme_text and END_MARK in readme_text:
        pre, rest = readme_text.split(BEGIN_MARK, 1)
        _, post = rest.split(END_MARK, 1)
        readme_text = pre + generated + post
    else:
        readme_text = readme_text.rstrip() + "\n\n" + generated + "\n"
    readme.write_text(readme_text, encoding="utf-8", newline="\n")

    print(f"vendored {len(files)} files ({lines} lines) from {UPSTREAM_PREFIX}@{short} "
          f"into {DEST_REL.as_posix()}; {rewritten} imports rewritten")
    print("next: lake exe mk_all && lake build")


DEFAULT_README = """# Vendored MIPStarRE sources

This directory is a **generated, read-only** copy of the Lean sources of
[MIPStarRE](https://github.com/LionSR/MIPStarRE), Sirui Lu's formalization of the
soundness of the classical low individual degree test (Ji, Natarajan, Vidick, Wright,
Yuen, arXiv:2009.12982). The main theorem is `MIPStarRE.LDT.Test.mainFormal`
(`LDT/Test/MainTheorem/MainFormal.lean`). It is used in this repository only through
the bridge in `MIPRE/Background/LIDT/Bridge/`; see `planning/lidt-port.md`.

## Permission and license

The upstream repository carries no license file. Its authors agreed (September 2026,
by correspondence with Thomas Vidick) to the inclusion of their code in this
repository under its Apache 2.0 license. Copyright remains with Sirui Lu and the
MIPStarRE contributors; every file carries a header saying so.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-lidt.py` instead. The only
  differences from upstream are the header, the rewritten `import` prefix
  (`MIPStarRE.` becomes `MIPRE.Background.LIDT.MIPStarRE.`), and the compile fixes
  listed below. Lean *namespaces* are unchanged (`MIPStarRE.LDT`, `MIPStarRE.Quantum`).
- Nothing outside `MIPRE/Background/LIDT/` may refer to the `MIPStarRE` namespace.
- Docstrings cite upstream paths (`blueprint/src/chapter/...`, `references/ldt-paper/...`,
  `docs/paper-gaps/...`); these resolve in the upstream repository at the commit below.

## Local deviations from upstream

None yet.

## Provenance

{generated}
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--source", required=True, type=Path, help="path to a MIPStarRE clone")
    parser.add_argument("--commit", required=True, help="expected upstream commit (prefix ok)")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--all", action="store_true",
                        help="copy every module instead of the import closure of ROOTS")
    args = parser.parse_args()
    vendor(args.source.resolve(), args.commit, args.repo_root.resolve(), args.all)


if __name__ == "__main__":
    main()
