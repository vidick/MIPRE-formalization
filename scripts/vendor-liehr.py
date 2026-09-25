#!/usr/bin/env python3
"""Vendor the core of `lukasliehr/MIPRE`, an independent Lean statement of Tsirelson's problem.

Usage (from the repository root):

    python scripts/vendor-liehr.py --source <path to an upstream checkout or unpacked
        archive> --date <YYYY-MM-DD> [--commit <sha>]

Upstream is a large Lean 4 project (about 900k lines) whose terminal file
``Tsirelson/MainStatement.lean`` states three propositions and proves none of them:
``QuantitativeSeparationStatement``, ``NegativeTsirelsonStatement`` and
``GameValueSeparationStatement``. This repository proves all three from ``MIPRE.separation``
(``MIPRE/Background/LiehrTsirelson/Main.lean``), so only the vocabulary they are written in
is vendored: the import closure of ``MainStatement.lean``, with one substitution.
``MainStatement.lean`` imports ``Tsirelson.Operational``, a facade that re-exports
``Tsirelson.Core`` together with ``Tsirelson.Bridge.StrategyCorrelation``; the statements use
nothing from the latter, so the import is redirected to ``Tsirelson.Core`` (``IMPORT_SUBST``)
and the bridge tree, which pulls in most of upstream, stays out.

The script

* deletes and recreates ``MIPRE/Background/LiehrTsirelson/Upstream/`` (wholly generated;
  hand edits there are lost on purpose);
* copies the import closure of ``ROOTS`` after the substitution, rewriting
  ``import Tsirelson.X`` to ``import MIPRE.Background.LiehrTsirelson.Upstream.X``;
* prepends a provenance header to every copied file;
* refreshes the generated block of the destination's ``README.md``.

Upstream needs no ``set_option autoImplicit true``: its modules vendored here elaborate
under this repository's ``autoImplicit = false``.

Afterwards run ``lake exe mk_all`` to refresh ``MIPRE.lean``, then ``lake build``.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
import textwrap
from pathlib import Path

URL = "https://github.com/lukasliehr/MIPRE"
DEST = Path("MIPRE/Background/LiehrTsirelson/Upstream")
UPSTREAM_PREFIX = "Tsirelson"
LOCAL_PREFIX = "MIPRE.Background.LiehrTsirelson.Upstream"
ROOTS = ("Tsirelson.MainStatement",)
# Import redirections, applied both when computing the closure and in the copied text.
IMPORT_SUBST = {"Tsirelson.Operational": "Tsirelson.Core"}

BEGIN_MARK = "<!-- BEGIN GENERATED (scripts/vendor-liehr.py) -->"
END_MARK = "<!-- END GENERATED -->"

HEADER = ("Vendored from `lukasliehr/MIPRE` ({url}), a Lean 4 formalization of Tsirelson's "
          "problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path: "
          "{upstream_path}, from {snapshot}. The import prefix `{up}.` is rewritten to "
          "`{local}.`; the Lean namespace `{up}` is unchanged, and nothing outside "
          "`MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file; "
          "see README.md.")


def header(**kw: str) -> str:
    return "/-\n" + textwrap.fill(HEADER.format(**kw), width=98) + "\n-/\n"

README = """# Vendored `lukasliehr/MIPRE` core

This directory is a **generated, read-only** copy of the statement vocabulary of
[lukasliehr/MIPRE](https://github.com/lukasliehr/MIPRE), an independent Lean 4 formalization
whose goal is the negative resolution of Tsirelson's problem along the route of MIP* = RE.
Its terminal file `Tsirelson/MainStatement.lean` states three propositions in its own terms
(games on `EuclideanSpace`, POVMs on both sides, `sSup` values) and proves none of them.
`MIPRE/Background/LiehrTsirelson/Main.lean` proves all three from `MIPRE.separation`, through
the identification of the two vocabularies in `MIPRE/Background/LiehrTsirelson/Bridge.lean`;
`MIPRE/Background/LiehrTsirelson/Axioms.lean` asserts that the three proofs use only the
standard axioms. `reports/liehr-tsirelson-bridge.md` records what the exercise showed about
the two sets of definitions.

## License

The upstream repository carries **no license file**, and the archive it was vendored from
carries none either. The files here are reproduced as the statements this repository
proves, with their provenance in every header; the maintainer is to settle the terms with
upstream before the tree is relied on for anything else.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-liehr.py` instead. The only
  differences from upstream are the header, the rewritten `import` prefix (`Tsirelson.`
  becomes `MIPRE.Background.LiehrTsirelson.Upstream.`) and one redirected import:
  `MainStatement.lean` imports upstream's facade `Tsirelson.Operational`, which re-exports
  the core together with a bridge tree the statements do not use, and the import is
  redirected to `Tsirelson.Core`. The Lean *namespace* is unchanged (`Tsirelson`).
- Nothing outside `MIPRE/Background/LiehrTsirelson/` may refer to that namespace.
- Only the import closure of `Tsirelson.MainStatement` (after the redirection) is vendored:
  the eight `Core` modules and the facade `Core.lean`. Docstrings cite upstream's own
  blueprint (`Blueprint/Nodes/...`); those resolve in the upstream repository.

## Local deviations from upstream

None beyond the mechanical ones above.

## Provenance

{generated}
"""


def import_line_re(prefix: str) -> re.Pattern[str]:
    return re.compile(rf"^import\s+({re.escape(prefix)}(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE)


def substitute_imports(text: str) -> tuple[str, int]:
    count = 0
    for old, new in IMPORT_SUBST.items():
        pattern = re.compile(rf"^(\s*import\s+){re.escape(old)}\s*$", re.MULTILINE)
        text, n = pattern.subn(lambda m: f"{m.group(1)}{new}", text)
        count += n
    return text, count


def import_closure(src_root: Path) -> list[tuple[str, Path]]:
    line_re = import_line_re(UPSTREAM_PREFIX)
    seen: dict[str, Path] = {}
    stack = list(ROOTS)
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        path = src_root / (module.replace(".", "/") + ".lean")
        if not path.exists():
            sys.exit(f"error: module {module} not found at {path}")
        seen[module] = path
        text, _ = substitute_imports(path.read_text(encoding="utf-8"))
        stack.extend(line_re.findall(text))
    return sorted(seen.items())


def rewrite_imports(text: str) -> tuple[str, int]:
    pattern = re.compile(rf"^(\s*import\s+){re.escape(UPSTREAM_PREFIX)}(\.|\s*$)", re.MULTILINE)
    return pattern.subn(lambda m: f"{m.group(1)}{LOCAL_PREFIX}{m.group(2)}", text)


def refresh_readme(path: Path, generated: str) -> None:
    text = path.read_text(encoding="utf-8") if path.exists() else None
    if text is None:
        text = README.format(generated=generated)
    elif BEGIN_MARK in text and END_MARK in text:
        pre, rest = text.split(BEGIN_MARK, 1)
        _, post = rest.split(END_MARK, 1)
        text = pre + generated + post
    else:
        text = text.rstrip() + "\n\n" + generated + "\n"
    path.write_text(text, encoding="utf-8", newline="\n")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--source", required=True, type=Path,
                    help="upstream checkout or unpacked archive (the directory holding "
                         "`Tsirelson/`)")
    ap.add_argument("--date", required=True, help="date of the snapshot, YYYY-MM-DD")
    ap.add_argument("--commit", default=None, help="upstream commit, if known")
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    src_root = args.source.resolve()
    if not (src_root / "Tsirelson").is_dir():
        sys.exit(f"error: {src_root} has no Tsirelson/ directory")
    snapshot = (f"commit {args.commit[:8]} of {args.date}" if args.commit
                else f"a snapshot of the `main` branch supplied on {args.date} "
                     f"(archive, no commit recorded)")

    dest = repo_root / DEST
    readme = dest / "README.md"
    readme_text = readme.read_text(encoding="utf-8") if readme.exists() else None
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    if readme_text is not None:
        readme.write_text(readme_text, encoding="utf-8", newline="\n")

    files = import_closure(src_root)
    rewritten = substituted = lines = 0
    for module, path in files:
        text = path.read_text(encoding="utf-8")
        text, n = substitute_imports(text)
        substituted += n
        text, n = rewrite_imports(text)
        rewritten += n
        lines += text.count("\n")
        rel = path.relative_to(src_root)
        head = header(url=URL, upstream_path=rel.as_posix(), snapshot=snapshot,
                      up=UPSTREAM_PREFIX, local=LOCAL_PREFIX)
        target = dest / rel.relative_to(UPSTREAM_PREFIX)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(head + text, encoding="utf-8", newline="\n")

    generated = "\n".join([
        BEGIN_MARK,
        f"- Upstream: {URL}",
        f"- Snapshot: {snapshot}",
        f"- Vendored files: {len(files)} Lean files, {lines} lines (the import closure of "
        f"`{ROOTS[0]}` after the redirection); {rewritten} import lines rewritten from "
        f"`{UPSTREAM_PREFIX}.` to `{LOCAL_PREFIX}.`, {substituted} redirected "
        + ", ".join(f"`{k}` to `{v}`" for k, v in IMPORT_SUBST.items()),
        "- `set_option autoImplicit true` inserted: no (not needed)",
        END_MARK,
    ])
    refresh_readme(readme, generated)
    print(f"vendored {len(files)} files ({lines} lines) into {DEST}")
    for module, _ in files:
        print(f"  {module}")


if __name__ == "__main__":
    main()
