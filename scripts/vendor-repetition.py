#!/usr/bin/env python3
"""Vendor the two direct parallel repetition formalizations into this repository.

Usage (from the repository root):

    python scripts/vendor-repetition.py \
        --cr-source <path to a commuting-repetition clone> --cr-commit <sha> \
        --tp-source <path to a ten-proofs clone> --tp-commit <sha>

The script

* checks that each clone is at the requested commit and has no local changes;
* deletes and recreates ``MIPRE/Background/Repetition/CommutingRepetition/`` and
  ``MIPRE/Background/Repetition/TenProofs/`` (both destinations are wholly generated;
  local hand edits there are lost on purpose -- see ``planning/repetition-port.md``);
* copies, from commuting-repetition, the import closure of the root modules
  (``CR_ROOTS`` below), rewriting ``import CommutingRepetition.X`` to
  ``import MIPRE.Background.Repetition.CommutingRepetition.X``, together with the
  upstream ``NOTICE`` file;
* copies, from ten-proofs, the single module ``QuantumParallelRepetition.lean`` and, as
  an audit aid, the Mathlib-only statement file
  ``ComparatorChallenges/G_QuantumParallelRepetition.lean`` (as ``.lean.expected``);
* prepends a provenance header to every copied Lean file and, unless
  ``--no-auto-implicit`` is given, inserts ``set_option autoImplicit true`` after the
  import block (both upstreams compile with Lean's default ``autoImplicit = true``,
  which this repository turns off in ``lakefile.toml``);
* refreshes the generated block of each destination's ``README.md``.

Afterwards run ``lake exe mk_all`` to refresh ``MIPRE.lean``, then ``lake build``.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

DEST_ROOT = Path("MIPRE/Background/Repetition")

BEGIN_MARK = "<!-- BEGIN GENERATED (scripts/vendor-repetition.py) -->"
END_MARK = "<!-- END GENERATED -->"

# The vendored commuting-repetition modules imported by the bridge in
# MIPRE/Background/Repetition/; everything they transitively import is vendored,
# nothing else (upstream's audit-node map Fidelity/Nodes.lean in particular is not).
CR_ROOTS = (
    "CommutingRepetition.MainTheorem.Main",
    "CommutingRepetition.StatementBridge",
)


@dataclass(frozen=True)
class Fix:
    """A recorded compile fix, applied after copying: ``old`` must occur exactly once in the
    vendored file ``path`` (relative to the destination directory) and is replaced by
    ``new``. Every fix is also described in the directory's README under "Local
    deviations from upstream"."""

    path: str
    old: str
    new: str
    reason: str


TP_FIX_SCHMIDT_OLD = """theorem exists_proofSchmidtDecomposition
"""

TP_FIX_SCHMIDT_NEW = """-- Vendoring compile fix (Lean v4.33): this proof needs the pre-v4.33 transparency
-- behaviour (its closing `simpa` no longer sees through `Matrix.toEuclideanLin`);
-- see README.md.
set_option backward.isDefEq.respectTransparency false in
theorem exists_proofSchmidtDecomposition
"""


@dataclass
class Source:
    key: str
    url: str
    copyright: str
    dest: Path                      # relative to the repository root
    module_prefix: str | None       # upstream module prefix to rewrite, if any
    local_prefix: str               # module prefix of the destination
    src_subdir: Path                # directory of the clone mirrored into `dest`
    module_root: Path               # directory of the clone that module names resolve in
    roots: tuple[str, ...] = ()     # import closure of these (module names)...
    files: tuple[str, ...] = ()     # ...or these files (relative to src_subdir)
    extra_files: tuple[tuple[str, str], ...] = ()   # (relative to clone, dest name)
    audit_aids: tuple[tuple[str, str], ...] = ()    # (relative to clone, dest name)
    readme: str = ""
    fixes: tuple[Fix, ...] = ()
    header: str = ""


HEADER = """/-
Copyright (c) 2026 {copyright}. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
{url} (commit {short}, {date}) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: {upstream_path}
-/
"""

AUTO_IMPLICIT = (
    "-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it\n"
    "-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.\n"
    "set_option autoImplicit true\n"
)

CR_README = """# Vendored commuting-repetition sources

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
  only differences from upstream are the header, the rewritten `import` prefix
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

None yet (beyond the mechanical ones above).

## Provenance

{generated}
"""

TP_README = """# Vendored ten-proofs sources

This directory is a **generated, read-only** copy of one Lean module of
[ten-proofs](https://github.com/openai/ten-proofs), the formalizations accompanying
OpenAI's *Ten Advances in Mathematics and Theoretical Computer Science* (2026):
`QuantumParallelRepetition.lean`, the proof of Chapter 6, *Exponential parallel
repetition for all two-player entangled games*. The root is
`QuantumParallelRepetition.distributionUniformExponential`. It is used in this
repository only through the bridge in `MIPRE/Background/Repetition/`; see
`planning/repetition-port.md`.

## License

Upstream is released under the Apache 2.0 license, the same license as this
repository. Every file carries a header saying so.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-repetition.py` instead. The
  only differences from upstream are the header, the `set_option autoImplicit true`
  line inserted after the imports, and the compile fixes listed below. The Lean
  *namespace* is unchanged (`QuantumParallelRepetition`).
- Nothing outside `MIPRE/Background/Repetition/` may refer to that namespace.
- `G_QuantumParallelRepetition.lean.expected` is upstream's Mathlib-only statement file
  (the definitions and the two root statements, with `sorry` proofs), kept as a reading
  aid; it is not built.

## Local deviations from upstream

None yet (beyond the mechanical ones above).

## Provenance

{generated}
"""

SOURCES = {
    "cr": Source(
        key="cr",
        url="https://github.com/vidick/commuting-repetition",
        copyright="the commuting-repetition contributors",
        dest=DEST_ROOT / "CommutingRepetition",
        module_prefix="CommutingRepetition",
        local_prefix="MIPRE.Background.Repetition.CommutingRepetition",
        src_subdir=Path("lean/CommutingRepetition"),
        module_root=Path("lean"),
        roots=CR_ROOTS,
        extra_files=(("lean/NOTICE", "NOTICE"),),
        readme=CR_README,
    ),
    "tp": Source(
        key="tp",
        url="https://github.com/openai/ten-proofs",
        copyright="the openai/ten-proofs contributors",
        dest=DEST_ROOT / "TenProofs",
        module_prefix=None,
        local_prefix="MIPRE.Background.Repetition.TenProofs",
        src_subdir=Path("."),
        module_root=Path("."),
        files=("QuantumParallelRepetition.lean",),
        audit_aids=(("ComparatorChallenges/G_QuantumParallelRepetition.lean",
                     "G_QuantumParallelRepetition.lean.expected"),),
        readme=TP_README,
        fixes=(
            Fix(
                path="QuantumParallelRepetition.lean",
                old=TP_FIX_SCHMIDT_OLD,
                new=TP_FIX_SCHMIDT_NEW,
                reason="Lean v4.33 transparency check: `exists_proofSchmidtDecomposition`",
            ),
        ),
    ),
}


def git(source: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(source), *args], text=True).strip()


def import_line_re(prefix: str) -> re.Pattern[str]:
    return re.compile(rf"^import\s+({re.escape(prefix)}(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE)


def import_closure(src_root: Path, prefix: str, roots: tuple[str, ...]) -> list[Path]:
    """All upstream modules transitively imported by ``roots`` (including them)."""
    line_re = import_line_re(prefix)
    seen: dict[str, Path] = {}
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        path = src_root / (module.replace(".", "/") + ".lean")
        if not path.exists():
            sys.exit(f"error: module {module} not found at {path}")
        seen[module] = path
        stack.extend(line_re.findall(path.read_text(encoding="utf-8")))
    return sorted(seen.values())


def rewrite_imports(text: str, prefix: str, local_prefix: str) -> tuple[str, int]:
    pattern = re.compile(rf"^(\s*import\s+){re.escape(prefix)}(\.|\s*$)", re.MULTILINE)
    count = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal count
        count += 1
        return f"{match.group(1)}{local_prefix}{match.group(2)}"

    return pattern.sub(repl, text), count


def insert_auto_implicit(text: str) -> str:
    """Insert the ``set_option`` block right after the leading import block."""
    lines = text.split("\n")
    first = next((i for i, l in enumerate(lines) if l.startswith("import ")), None)
    if first is None:
        return AUTO_IMPLICIT + text
    end = first
    while end < len(lines) and (lines[end].startswith("import ") or lines[end].strip() == ""):
        end += 1
    # `end` is the first non-import, non-blank line after the block; keep one blank line.
    block = lines[first:end]
    while block and block[-1].strip() == "":
        block.pop()
    return "\n".join(lines[:first] + block + ["", AUTO_IMPLICIT.rstrip("\n")] + [""] + lines[end:])


def refresh_readme(path: Path, default: str, generated: str) -> None:
    text = path.read_text(encoding="utf-8") if path.exists() else None
    if text is None:
        text = default.format(generated=generated)
    elif BEGIN_MARK in text and END_MARK in text:
        pre, rest = text.split(BEGIN_MARK, 1)
        _, post = rest.split(END_MARK, 1)
        text = pre + generated + post
    else:
        text = text.rstrip() + "\n\n" + generated + "\n"
    path.write_text(text, encoding="utf-8", newline="\n")


def vendor(src: Source, clone: Path, commit: str, repo_root: Path, auto_implicit: bool) -> None:
    head = git(clone, "rev-parse", "HEAD")
    if not head.startswith(commit):
        sys.exit(f"error: clone at {clone} is at {head[:12]}, not {commit}")
    if git(clone, "status", "--porcelain"):
        sys.exit(f"error: clone at {clone} has uncommitted changes")
    date = git(clone, "show", "-s", "--format=%cs", "HEAD")
    short = head[:8]

    src_root = clone / src.src_subdir
    dest = repo_root / src.dest
    readme = dest / "README.md"
    readme_text = readme.read_text(encoding="utf-8") if readme.exists() else None
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    if readme_text is not None:
        readme.write_text(readme_text, encoding="utf-8", newline="\n")

    if src.roots:
        assert src.module_prefix is not None
        files = import_closure(clone / src.module_root, src.module_prefix, src.roots)
    else:
        files = [src_root / f for f in src.files]

    rewritten = 0
    lines = 0
    for path in files:
        rel = path.relative_to(src_root)
        text = path.read_text(encoding="utf-8")
        if src.module_prefix is not None:
            text, n = rewrite_imports(text, src.module_prefix, src.local_prefix)
            rewritten += n
        if auto_implicit:
            text = insert_auto_implicit(text)
        lines += text.count("\n")
        upstream_path = (src.src_subdir / rel).as_posix().removeprefix("./")
        header = HEADER.format(copyright=src.copyright, url=src.url, short=short,
                               date=date, upstream_path=upstream_path)
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(header + text, encoding="utf-8", newline="\n")

    for rel, name in src.extra_files + src.audit_aids:
        shutil.copyfile(clone / rel, dest / name)

    for fix in src.fixes:
        target = dest / fix.path
        text = target.read_text(encoding="utf-8")
        if text.count(fix.old) != 1:
            sys.exit(f"error: fix for {fix.path} ({fix.reason}) matched "
                     f"{text.count(fix.old)} times, expected 1")
        target.write_text(text.replace(fix.old, fix.new), encoding="utf-8", newline="\n")

    details = [
        BEGIN_MARK,
        f"- Upstream: {src.url}",
        f"- Commit: `{head}` ({date})",
        f"- Vendored files: {len(files)} Lean files, {lines} lines"
        + (f" (the import closure of {len(src.roots)} root modules); "
           f"{rewritten} import lines rewritten from `{src.module_prefix}.` to "
           f"`{src.local_prefix}.`" if src.roots else ""),
    ]
    details += [f"- Copied verbatim: `{name}` = upstream `{rel}`"
                for rel, name in src.extra_files + src.audit_aids]
    details += [f"- `set_option autoImplicit true` inserted after the imports: "
                f"{'yes' if auto_implicit else 'no'}"]
    details += [f"- Recorded compile fixes applied: {len(src.fixes)} "
                f"(listed under \"Local deviations from upstream\")", END_MARK]
    refresh_readme(readme, src.readme, "\n".join(details))
    print(f"[{src.key}] vendored {len(files)} files ({lines} lines) from {src.url}@{short} "
          f"into {src.dest.as_posix()}; {rewritten} imports rewritten")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--cr-source", type=Path, help="path to a commuting-repetition clone")
    parser.add_argument("--cr-commit", help="expected commuting-repetition commit (prefix ok)")
    parser.add_argument("--tp-source", type=Path, help="path to a ten-proofs clone")
    parser.add_argument("--tp-commit", help="expected ten-proofs commit (prefix ok)")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--no-auto-implicit", action="store_true",
                        help="do not insert `set_option autoImplicit true`")
    args = parser.parse_args()
    done = 0
    if args.cr_source:
        if not args.cr_commit:
            sys.exit("error: --cr-commit is required with --cr-source")
        vendor(SOURCES["cr"], args.cr_source.resolve(), args.cr_commit,
               args.repo_root.resolve(), not args.no_auto_implicit)
        done += 1
    if args.tp_source:
        if not args.tp_commit:
            sys.exit("error: --tp-commit is required with --tp-source")
        vendor(SOURCES["tp"], args.tp_source.resolve(), args.tp_commit,
               args.repo_root.resolve(), not args.no_auto_implicit)
        done += 1
    if not done:
        sys.exit("error: give --cr-source and/or --tp-source")
    print("next: lake exe mk_all && lake build")


if __name__ == "__main__":
    main()
