#!/usr/bin/env python3
"""Put every Lean source file of this repository under Lean's module system.

The Palomar registry requires every regular ``.lean`` file to use the module system
(``planning/palomar.md``). This script rewrites a file that does not yet start with
``module`` so that it does, preserving the semantics the file had as a non-module file:

* ``module`` is inserted before the first ``import`` (comments may precede it);
* every ``import X`` becomes ``public import X``, so that what a file re-exported to its
  importers before is still re-exported (a plain ``import`` inside a module is private to
  that module);
* ``@[expose] public section`` is inserted after the import block (after the
  ``set_option autoImplicit true`` block the vendor scripts insert, when present), so that
  every declaration is exported and every definition body stays unfoldable by importers,
  as before; the section is closed by an ``end`` appended to the file.

Two things the module system forbids that a plain file allowed, and what is done about them:

* a ``private`` definition may not occur in the statement of a public theorem nor in the
  body of an exposed public definition (a private *theorem* may be used in proofs, so those
  are left alone). ``--unprivate-defs`` drops ``private`` from every non-theorem
  declaration (``def``, ``abbrev``, ``structure``, ``instance``, ``inductive``, ``class``,
  ``opaque``); the names must then be distinct across files, which
  ``scripts/modularize.py --clashes`` checks by full name before anything is rewritten;
* meta code (``syntax``, ``macro``, ``elab``, ...) needs ``public meta import`` of what it
  uses (``Lean`` for the elaborator API) and must sit outside the public section; the ten
  files defining such code are adjusted by hand after the script runs.

Usage: ``python3 scripts/modularize.py [--check] [--unprivate-defs] [--clashes] [paths...]``
(default: every ``.lean`` file under ``MIPRE/`` and ``MIPRE.lean``). ``--check`` only
lists the files that would change and exits 1 if there are any. The vendored trees are
rewritten too: the script is the recorded mechanism, and ``scripts/vendor-*.py`` call it
on what they produce.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^(public\s+|meta\s+|public\s+meta\s+|all\s+)?import\s+\S+")
EXPOSE = "@[expose] public section"


def is_module(lines: list[str]) -> bool:
    """A file is a module if its first non-comment, non-blank line is ``module``."""
    in_comment = 0
    for l in lines:
        s = l.strip()
        if in_comment:
            if "-/" in s:
                in_comment -= 1
            continue
        if s.startswith("/-"):
            if "-/" not in s:
                in_comment += 1
            continue
        if not s or s.startswith("--"):
            continue
        return s == "module"
    return False


def modularize(text: str) -> str | None:
    """Return the rewritten text, or None if the file is already a module."""
    lines = text.split("\n")
    if is_module(lines):
        return None
    first = next((i for i, l in enumerate(lines) if IMPORT_RE.match(l)), None)
    if first is None:
        # No imports at all (a file importing only the prelude): the module header goes
        # before the first non-comment line.
        in_comment = 0
        first = 0
        for i, l in enumerate(lines):
            s = l.strip()
            if in_comment:
                if "-/" in s:
                    in_comment -= 1
                continue
            if s.startswith("/-"):
                if "-/" not in s:
                    in_comment += 1
                continue
            if s and not s.startswith("--"):
                first = i
                break
        out = lines[:first] + ["module", "", EXPOSE, ""] + lines[first:]
    else:
        end = first
        while end < len(lines) and (IMPORT_RE.match(lines[end]) or not lines[end].strip()):
            end += 1
        block = [("public " + l if l.startswith("import ") else l) for l in lines[first:end]]
        while block and not block[-1].strip():
            block.pop()
        rest = lines[end:]
        # The vendor scripts insert a `set_option autoImplicit true` block right after the
        # imports; keep it there and open the public section after it.
        k = 0
        if rest and rest[0].startswith("-- Upstream builds with Lean's default `autoImplicit = true`"):
            while k < len(rest) and rest[k].strip() and not rest[k].startswith("set_option autoImplicit"):
                k += 1
            k += 1  # the set_option line
        out = lines[:first] + ["module"] + block + [""] + rest[:k] + ([""] if k else []) \
            + [EXPOSE, ""] + rest[k:]
    while out and not out[-1].strip():
        out.pop()
    out += ["", "end", ""]
    return "\n".join(out)


PRIVATE_DEF_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]]*\]\s*)?)(?P<nc>noncomputable\s+)?private\s+"
    r"(?P<nc2>noncomputable\s+)?(?P<kind>def|abbrev|structure|instance|inductive|class|opaque)\b")


def unprivate_defs(text: str) -> tuple[str, int]:
    """Drop ``private`` from every non-theorem declaration. Returns the text and the count."""
    out = []
    n = 0
    for l in text.split("\n"):
        m = PRIVATE_DEF_RE.match(l)
        if m:
            n += 1
            l = (m.group("attrs") + (m.group("nc") or m.group("nc2") or "") + m.group("kind")
                 + l[m.end():])
        out.append(l)
    return "\n".join(out), n


def private_def_names(paths: list[Path]) -> dict[str, list[Path]]:
    """Full names (namespace-qualified, approximately: `namespace`/`section`/`end` are
    tracked line by line) of every private non-theorem declaration, with their files."""
    name_re = re.compile(PRIVATE_DEF_RE.pattern + r"\s+(?P<name>[^\s(:{\[]+)")
    names: dict[str, list[Path]] = {}
    for p in paths:
        stack: list[str | None] = []
        for l in p.read_text(encoding="utf-8").split("\n"):
            s = l.strip()
            m = re.match(r"^namespace\s+(\S+)", s)
            if m:
                stack.append(m.group(1))
                continue
            if re.match(r"^(?:noncomputable\s+)?section\b", s):
                stack.append(None)
                continue
            if re.match(r"^end\b", s) and stack:
                stack.pop()
                continue
            m = name_re.match(s)
            if m:
                name = m.group("name")
                if m.group("kind") == "instance" and not name[0].isalpha():
                    continue
                ns = ".".join(x for x in stack if x)
                names.setdefault(f"{ns}.{name}" if ns else name, []).append(p)
    return names


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    check = "--check" in sys.argv
    if args:
        paths = [Path(a) for a in args]
    else:
        paths = sorted(ROOT.glob("MIPRE/**/*.lean")) + [ROOT / "MIPRE.lean"]
    if "--clashes" in sys.argv:
        clashes = {k: v for k, v in private_def_names(paths).items() if len(v) > 1}
        for k, v in sorted(clashes.items()):
            print(f"{k}: " + ", ".join(str(p.relative_to(ROOT)) for p in v))
        print(f"{len(clashes)} clashing full names among private definitions")
        return 1 if clashes else 0
    changed = []
    for p in paths:
        text = p.read_text(encoding="utf-8")
        new = modularize(text)
        if "--unprivate-defs" in sys.argv:
            new2, n = unprivate_defs(new if new is not None else text)
            if n:
                new = new2
        if new is None:
            continue
        changed.append(p)
        if not check:
            p.write_text(new, encoding="utf-8", newline="\n")
    for p in changed:
        rel = p.relative_to(ROOT) if p.resolve().is_relative_to(ROOT) else p
        print(("would rewrite " if check else "rewrote ") + str(rel))
    print(f"{len(changed)} files")
    return 1 if (check and changed) else 0


if __name__ == "__main__":
    sys.exit(main())
