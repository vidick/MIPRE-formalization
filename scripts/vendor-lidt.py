#!/usr/bin/env python3
"""Vendor the MIPStarRE low individual degree test development into this repository.

Usage (from the repository root):

    python scripts/vendor-lidt.py --source <path to a MIPStarRE clone> --commit <sha>

The script

* checks that the clone is at the requested commit;
* deletes and recreates ``MIPRE/Background/LIDT/MIPStarRE/`` (the destination is
  wholly generated; local hand edits there are lost on purpose — see the plan in
  ``planning/lidt-port.md``, decisions D3 and D6);
* copies ``MIPStarRE/Quantum/**``, ``MIPStarRE/LDT/**`` and the two aggregators
  ``MIPStarRE/Quantum.lean``, ``MIPStarRE/LDT.lean``;
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


def rewrite_imports(text: str) -> tuple[str, int]:
    count = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal count
        count += 1
        return f"{match.group(1)}{LOCAL_PREFIX}{match.group(2)}"

    return IMPORT_RE.sub(repl, text), count


def vendor(source: Path, commit: str, repo_root: Path) -> None:
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
    for d in COPIED_DIRS:
        files.extend(sorted((src_root / d).rglob("*.lean")))
    for f in COPIED_FILES:
        files.append(src_root / f)

    rewritten = 0
    lines = 0
    for path in files:
        rel = path.relative_to(src_root)
        text = path.read_text(encoding="utf-8")
        text, n = rewrite_imports(text)
        rewritten += n
        lines += text.count("\n")
        header = HEADER_TEMPLATE.format(
            url=UPSTREAM_URL, short=short, date=date,
            upstream_path=(Path(UPSTREAM_PREFIX) / rel).as_posix(),
        )
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(header + text, encoding="utf-8", newline="\n")

    challenge_src = source / CHALLENGE_REL
    if challenge_src.exists():
        shutil.copyfile(challenge_src, dest / CHALLENGE_REL.name)

    generated = "\n".join([
        BEGIN_MARK,
        f"- Upstream: {UPSTREAM_URL}",
        f"- Commit: `{head}` ({date})",
        f"- Vendored files: {len(files)} Lean files, {lines} lines; "
        f"{rewritten} import lines rewritten from `{UPSTREAM_PREFIX}.` to `{LOCAL_PREFIX}.`",
        f"- Audit aid: `{CHALLENGE_REL.name}` = upstream `{CHALLENGE_REL.as_posix()}`",
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
    args = parser.parse_args()
    vendor(args.source.resolve(), args.commit, args.repo_root.resolve())


if __name__ == "__main__":
    main()
