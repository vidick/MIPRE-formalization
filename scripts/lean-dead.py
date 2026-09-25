#!/usr/bin/env python3
"""Dead declarations, from the compiler's own reference index.

Every elaborated identifier reference is recorded by Lean in the module's `.ilean`
file (format version 5): for each constant, its definition site and every usage,
`[line, col, endLine, endCol, enclosingDeclaration]`. Aggregating that index over
the built library says exactly which declaration uses which, with none of grep's
homonym noise. A declaration is reported dead when

* it is a `theorem`, `lemma`, `def` or `abbrev` at column 0 of a project-written
  module (the vendored trees are skipped; their duplicates are upstream's);
* it carries no attribute and is not an instance — a `@[simp]` lemma or an
  instance can fire without an identifier, which the index cannot see;
* no blueprint `\\lean{}` tag and no `#guard_sorry_free` guard names it;
* every recorded usage lies inside its own body or inside a declaration already
  found dead — iterated to a fixpoint, so a definition whose only users were dead
  lemmas is dead too.

The index reflects the last build, so run it on a built tree (`lake build`, seconds
when the modules are in place). Grep proposes; elaboration decides; this reads the
elaboration's own notes.

    python3 scripts/lean-dead.py                 # the dead list, one per line
    python3 scripts/lean-dead.py MIPRE/TM        # restricted to a directory
    python3 scripts/lean-dead.py --attributed    # the other batch: attribute-carrying
                                                 # declarations with no recorded usage
                                                 # at all (only a build can rule on them)
    python3 scripts/lean-dead.py --summary       # counts per directory

Each line is `path:line  kind  name` (`[private]` when private). The per-directory
summary and the control checks go to stderr.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB = os.path.join(ROOT, ".lake", "build", "lib", "lean")
SRC = "MIPRE"
VENDORED = (
    "MIPRE/Background/Repetition/TenProofs/",
    "MIPRE/Background/Repetition/CommutingRepetition/",
    "MIPRE/Background/LIDT/MIPStarRE/",
    "MIPRE/Background/Orthonormalization/Orthogonalization/",
    "MIPRE/Background/LiehrTsirelson/Upstream/",
)
GUARD_FILES = ["MIPRE/Axioms.lean"] + [
    f"MIPRE/Background/{d}/Axioms.lean"
    for d in ("LIDT", "Repetition", "QLD", "Orthonormalization")
]
KINDS = "theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom"
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*"
    r"(?P<kind>" + KINDS + r")\s+(?P<name>[^\s({\[:]+)"
)
NS_RE = re.compile(r"^namespace\s+(\S+)")
END_RE = re.compile(r"^end(?:\s+\S+)?\s*$")
SECTION_RE = re.compile(r"^section(?:\s+\S+)?\s*$")
LEAN_TAG_RE = re.compile(r"\\lean\{([^}]*)\}", re.S)
IDENT_RE = re.compile(r"[A-Za-z_][^\s(){}\[\],:;«»@#$%^&*+=<>≤≥≠/\\|~`\"]*")


def source_files(prefixes):
    for dp, _, fn in os.walk(os.path.join(ROOT, SRC)):
        for f in sorted(fn):
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dp, f), ROOT)
            if any(rel.startswith(v) for v in VENDORED):
                continue
            if prefixes and not any(rel.startswith(p) for p in prefixes):
                continue
            yield rel


def declarations(rel):
    """Column-0 declarations of one file: (full name, line, kind, attributed, private)."""
    out = []
    ns = []
    attrs = False
    in_doc = False
    with open(os.path.join(ROOT, rel), encoding="utf-8") as fh:
        for i, line in enumerate(fh, 1):
            if in_doc:
                if "-/" in line:
                    in_doc = False
                continue
            if line.startswith("/--") or line.startswith("/-!"):
                if "-/" not in line:
                    in_doc = True
                continue
            m = NS_RE.match(line)
            if m:
                ns.append(("ns", m.group(1))); attrs = False; continue
            if SECTION_RE.match(line):
                ns.append(("sec", None)); attrs = False; continue
            if END_RE.match(line):
                if ns:
                    ns.pop()
                attrs = False
                continue
            m = DECL_RE.match(line)
            if m:
                name = m.group("name")
                if name.startswith("«"):
                    attrs = False
                    continue
                prefix = ".".join(x for k, x in ns if k == "ns")
                if name.startswith("_root_."):
                    full = name[len("_root_."):]
                else:
                    full = f"{prefix}.{name}" if prefix else name
                head = line[: m.start("kind")]
                out.append((full, i, m.group("kind"), attrs or "@[" in head, "private " in head))
                attrs = False
                continue
            if line.startswith("@["):
                attrs = True
            elif line.strip() and not line[0].isspace() and not line.startswith("--"):
                attrs = False
    return out


def blueprint_tags():
    names = set()
    base = os.path.join(ROOT, "blueprint", "src")
    for dp, _, fn in os.walk(base):
        for f in fn:
            if f.endswith(".tex"):
                text = open(os.path.join(dp, f), encoding="utf-8").read()
                text = re.sub(r"%\s*\n\s*", "", text)
                for m in LEAN_TAG_RE.finditer(text):
                    for n in re.split(r"[,\s]+", m.group(1)):
                        if n:
                            names.add(n)
    return names


def guarded_names():
    names = set()
    for rel in GUARD_FILES:
        p = os.path.join(ROOT, rel)
        if os.path.exists(p):
            names.update(IDENT_RE.findall(open(p, encoding="utf-8").read()))
    return names


def index():
    """From every project `.ilean`: defining module of each constant, and its usages."""
    defined = {}
    usages = collections.defaultdict(list)   # name -> [(module, enclosing declaration)]
    n = 0
    for dp, _, fn in os.walk(LIB):
        for f in fn:
            if not f.endswith(".ilean"):
                continue
            p = os.path.join(dp, f)
            mod = os.path.relpath(p, LIB)[:-6].replace(os.sep, ".")
            if not (mod == SRC or mod.startswith(SRC + ".")):
                continue
            n += 1
            data = json.load(open(p, encoding="utf-8"))
            priv = f"_private.{mod}.0."
            for key, v in data["references"].items():
                if not key.startswith("{"):
                    continue
                name = json.loads(key)["c"]["n"]
                if name.startswith(priv):
                    name = name[len(priv):]
                elif name.startswith("_private."):
                    continue   # another module's private constant
                if v.get("definition") is not None:
                    defined[name] = mod
                for u in v.get("usages", []):
                    usages[name].append((mod, u[4] if len(u) > 4 else None))
    return n, defined, usages


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("prefixes", nargs="*", help="restrict to these path prefixes")
    ap.add_argument("--attributed", action="store_true",
                    help="list attribute-carrying declarations with no recorded usage instead")
    ap.add_argument("--summary", action="store_true", help="counts per directory only")
    ap.add_argument("--json", help="also write every dead declaration with its usages here")
    args = ap.parse_args()

    decls = []
    for rel in source_files(args.prefixes):
        decls.extend((rel,) + d for d in declarations(rel))
    tags = blueprint_tags()
    guards = guarded_names()
    n_files, defined, usages = index()
    if n_files == 0:
        sys.exit(f"no .ilean files under {LIB}: build the library first")

    by_name = collections.Counter(d[1] for d in decls)
    declared = set(by_name)
    parent_cache = {}

    def parent(enc):
        """The declared name an enclosing-declaration name belongs to (aux names stripped)."""
        if enc is None:
            return None
        if enc not in parent_cache:
            r = enc
            if enc not in declared:
                parts = enc.split(".")
                for i in range(len(parts) - 1, 0, -1):
                    cand = ".".join(parts[:i])
                    if cand in declared:
                        r = cand
                        break
            parent_cache[enc] = r
        return parent_cache[enc]

    unindexed = [d for d in decls if d[1] not in defined]
    print(f"declarations: {len(decls)}   ilean files: {n_files}   "
          f"declared but absent from the index: {len(unindexed)}", file=sys.stderr)
    for d in unindexed[:5]:
        print(f"  not indexed: {d[1]} ({d[0]}:{d[2]})", file=sys.stderr)

    if args.attributed:
        rows = [d for d in decls if d[4] and d[3] != "instance" and d[1] in defined
                and not any(parent(e) != d[1] for _, e in usages.get(d[1], []))
                and d[1] not in tags and d[1] not in guards]
        for rel, name, line, kind, _, priv in sorted(rows):
            print(f"{rel}:{line}  {kind}  {name}{'  [private]' if priv else ''}")
        print(f"attribute-carrying declarations with no recorded usage: {len(rows)}", file=sys.stderr)
        return

    protected = {d[1] for d in decls
                 if d[3] == "instance" or d[4] or d[1] in tags or d[1] in guards or by_name[d[1]] > 1}
    cands = [d[1] for d in decls if d[1] in defined and d[1] not in protected
             and d[3] in ("theorem", "lemma", "def", "abbrev")]
    dead = set()
    changed = True
    while changed:
        changed = False
        for name in cands:
            if name in dead:
                continue
            if all(parent(e) == name or parent(e) in dead for _, e in usages.get(name, [])):
                dead.add(name)
                changed = True

    rows = sorted(d for d in decls if d[1] in dead)
    if args.json:
        json.dump([{"file": d[0], "name": d[1], "line": d[2], "kind": d[3], "private": d[5],
                    "usages": usages.get(d[1], [])} for d in rows],
                  open(args.json, "w"), ensure_ascii=False, indent=0)
    by_dir = collections.Counter()
    for rel, name, line, kind, _, priv in rows:
        parts = rel.split("/")
        by_dir["/".join(parts[:3]) if parts[1] in ("Background", "Foundations") else "/".join(parts[:2])] += 1
        if not args.summary:
            print(f"{rel}:{line}  {kind}  {name}{'  [private]' if priv else ''}")
    for k, c in by_dir.most_common():
        print(f"{c:5d}  {k}", file=sys.stderr)
    print(f"dead: {len(rows)} of {len(cands)} candidates "
          f"({len(decls)} declarations, {len(protected)} protected)", file=sys.stderr)


if __name__ == "__main__":
    main()
