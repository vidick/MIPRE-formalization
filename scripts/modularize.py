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

* a ``private`` declaration may not occur in the statement of a public theorem nor in the
  body of an exposed public definition, and the second case catches private *theorems* too
  (a ``PolyTimeFun`` is a program with its cost proof, so a private cost lemma in a
  definition's body is an "unknown identifier" in a module). ``--unprivate-defs`` therefore
  drops ``private`` from every declaration; the full names must then be distinct across
  files, which ``scripts/modularize.py --clashes`` checks before anything is rewritten
  (a clash with a *public* name elsewhere shows up as "already declared" in the build);
* Mathlib is itself a library of modules and imports its tactic modules privately where it
  can, so a module sees a tactic only along a public import path (a non-module file saw
  everything in its closure). Every module that imports part of Mathlib but not the
  ``Mathlib`` umbrella gets ``public import MIPRE.Tactics``, the bundle of
  ``MIPRE/Tactics.lean``, after its import block;
* meta code (``elab``, ``elab_rules``, ...) uses the elaborator API at elaboration time,
  which a module must import with ``meta``: every ``import Lean`` or ``import Lean.X`` line
  gets a ``public meta import`` twin, and in a file that runs compiled code at elaboration
  time (``#eval``, ``native_decide``) every import does, since a module gets the code of
  what it imports only through ``meta import``. Macros and elaborators may sit inside the exposed
  public section and are visible to module importers there (checked on Lean v4.35.0-rc3
  with `MIPRE/ModExp` experiments, 2026-09-28: a ``macro`` expanding to Mathlib tactics
  needs no ``meta`` import at all).

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
META_IMPORT_RE = re.compile(r"^import\s+Lean(?:\.\S+)?\s*$")
# A file that runs compiled code at elaboration time (`#eval`, `native_decide`) needs the
# code of every module it imports, which a module gets only through `meta import`.
EVAL_RE = re.compile(r"^\s*#eval\b|\bnative_decide\b", re.MULTILINE)


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
        # `lake exe mk_all` writes `module  -- shake: keep-all ...` on the root file.
        return s == "module" or s.startswith("module ") and s[7:].lstrip().startswith("--")
    return False


BUNDLE = "MIPRE.Tactics"
BUNDLE_LINE = f"public import {BUNDLE}"
MATHLIB_PART_RE = re.compile(r"^public import Mathlib\.\S+\s*$")
MATHLIB_ALL_RE = re.compile(r"^public import Mathlib\s*$")


def ensure_meta_twins(text: str) -> str | None:
    """In a module that runs compiled code (`#eval`, `native_decide`), give every
    ``public import X`` a ``public meta import X`` twin it lacks. Returns None if unchanged."""
    if not EVAL_RE.search(text):
        return None
    lines = text.split("\n")
    have = {l.strip() for l in lines}
    out = []
    changed = False
    for l in lines:
        out.append(l)
        if l.startswith("public import ") and not l.startswith("public import MIPRE.Tactics"):
            twin = "public meta import " + l[len("public import "):]
            if twin not in have:
                out.append(twin)
                changed = True
    return "\n".join(out) if changed else None


def ensure_bundle(text: str) -> str | None:
    """Insert ``public import MIPRE.Tactics`` after the import block of a module that
    imports part of Mathlib but not the `Mathlib` umbrella (Mathlib imports its tactic
    modules privately, so a module sees a tactic only along a public path; the bundle,
    `MIPRE/Tactics.lean`, re-exports the common ones). Returns None if nothing changes."""
    lines = text.split("\n")
    if any(l.strip() == BUNDLE_LINE for l in lines):
        return None
    if any(MATHLIB_ALL_RE.match(l) for l in lines):
        return None
    if not any(MATHLIB_PART_RE.match(l) for l in lines):
        return None
    last = max(i for i, l in enumerate(lines) if IMPORT_RE.match(l))
    lines.insert(last + 1, BUNDLE_LINE)
    return "\n".join(lines)


def modularize(text: str) -> str | None:
    """Return the rewritten text, or None if the file is already a module with the bundle."""
    lines = text.split("\n")
    if is_module(lines):
        t1 = ensure_meta_twins(text)
        t2 = ensure_bundle(t1 if t1 is not None else text)
        return t2 if t2 is not None else t1
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
        block = []
        runs_code = bool(EVAL_RE.search(text))
        for l in lines[first:end]:
            if l.startswith("import "):
                block.append("public " + l)
                # Meta code (`elab`, `elab_rules`, ...) uses the elaborator API of `Lean` at
                # elaboration time, which a module must import with `meta`; `#eval` and
                # `native_decide` run the compiled code of what they import.
                if META_IMPORT_RE.match(l) or runs_code:
                    block.append("public meta " + l)
            else:
                block.append(l)
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
    result = "\n".join(out)
    result = ensure_meta_twins(result) or result
    return ensure_bundle(result) or result


PRIVATE_DEF_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]]*\]\s*)?)(?P<nc>(?:noncomputable\s+|partial\s+)*)private\s+"
    r"(?P<nc2>(?:noncomputable\s+|partial\s+)*)"
    r"(?P<kind>def|abbrev|structure|instance|inductive|class|opaque|theorem|lemma)\b")


def unprivate_defs(text: str) -> tuple[str, int]:
    """Drop ``private`` from every declaration. Returns the text and the count."""
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
    tracked line by line) of every private declaration, with their files."""
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


KNOWN_FLAGS = {"--check", "--unprivate-defs", "--clashes"}


def modularize_tree(dest: Path, unprivate: bool = True) -> int:
    """``modularize_paths`` over every ``.lean`` file under ``dest`` (for the vendor scripts)."""
    return modularize_paths(sorted(dest.rglob("*.lean")), unprivate)


def modularize_paths(paths: list[Path], unprivate: bool = True) -> int:
    """Rewrite every file of ``paths`` that is not yet a module (the vendor scripts call this
    on the trees they produce). Returns the number of files rewritten."""
    n = 0
    for p in paths:
        text = p.read_text(encoding="utf-8")
        new = modularize(text)
        if unprivate:
            new2, k = unprivate_defs(new if new is not None else text)
            if k:
                new = new2
        if new is not None:
            p.write_text(new, encoding="utf-8", newline="\n")
            n += 1
    return n


def main() -> int:
    flags = [a for a in sys.argv[1:] if a.startswith("--")]
    if "--help" in flags or "-h" in sys.argv[1:] or set(flags) - KNOWN_FLAGS:
        print(__doc__)
        return 0 if ("--help" in flags or "-h" in sys.argv[1:]) else 2
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    check = "--check" in sys.argv
    if args:
        paths = [Path(a) for a in args]
    else:
        paths = sorted(ROOT.glob("MIPRE/**/*.lean")) + [ROOT / "MIPRE.lean"]
    paths = [p for p in paths if p.resolve() != (ROOT / "MIPRE" / "Tactics.lean").resolve()]
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
        rel = p.resolve().relative_to(ROOT) if p.resolve().is_relative_to(ROOT) else p
        print(("would rewrite " if check else "rewrote ") + str(rel))
    print(f"{len(changed)} files")
    return 1 if (check and changed) else 0


if __name__ == "__main__":
    sys.exit(main())
