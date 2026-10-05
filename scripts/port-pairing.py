#!/usr/bin/env python3
"""Pair the declarations of a ported LIDT file with those of its vendored original.

The commuting-operator port of the low-individual-degree test (`planning/c6b-plan.md`,
milestones M0-M14, and its section "Port conventions") mirrors the vendored tree
`MIPStarRE/LDT/` of the `MIPStarRE` Lake dependency (`.lake/packages/MIPStarRE`, pinned in
`lake-manifest.json`) file by file under `MIPRE/Background/LIDT/Co/`, with the
same relative paths, and keeps the vendored declaration names. This script checks that a ported
file accounts for every declaration of its vendored counterpart: each one is either ported (a
declaration of the same name) or listed, with its reason, in the ported file's module docstring
under a heading `Not ported`, one name per bullet:

    ## Not ported

    - `QuantumState.tensor`: the model has one state and no tensor product of Hilbert spaces.
    - `normalizedTrace_opTensor`: the model has no trace.

Names are compared after removing the root namespaces (`MIPStarRE.LDT.` and `MIPStarRE.` on the
vendored side, `MIPRE.LIDT.Co.` on the ported side) and the namespaces of the state, which the
port renames (`QuantumState`, `PureState`, `SymModel` and `VecState` are dropped wherever they
occur): so the vendored `QuantumState.IsNormalized` is paired with the ported
`VecState.IsNormalized`, and `leftTensor_one` with `SymModel.leftTensor_one`. A vendored
declaration is then

* **ported** when a declaration of the ported file has the same normalized name;
* **ported elsewhere** when a declaration of another file under `Co/` has it (the port moves
  some declarations, e.g. every operator-positivity lemma into `Co/Basic/QuantumState.lean`);
* **listed** when a `Not ported` bullet names it: the bullet's first backticked name equals the
  vendored name, normalized or not, or is a dotted suffix of it (`` `basis` `` covers
  `PureState.basis`); a field of a structure that is listed is listed with it;
* **loose** when only the last name components agree with a declaration of the ported file that
  pairs with nothing else (a namespace changed); reported, so that a person can look;
* **missing** otherwise.

A declaration of the ported file that pairs with no vendored declaration of the counterpart is
**new**; when it has the name of a declaration of another vendored file, that file is shown
(the declaration was moved in). `Not ported` bullets that name no vendored declaration, or name
one that is ported after all, are reported as stale.

Declarations are read from the source, with comments and strings removed: `theorem`, `lemma`,
`def`, `abbrev`, `structure`, `class`, `inductive`, `opaque`, `axiom`, `alias` and named
`instance`s, at any indentation, with their names resolved against the enclosing `namespace`
blocks (`_root_.` honoured). Anonymous instances and `example`s cannot be paired and are skipped.
The fields of a `structure` or `class` (the lines at the first indentation after its `where`,
`name : type`, `name (binders) : type` or `[name : Class]`) are declarations too, `Struct.field`,
so that a field dropped or renamed by the port is reported like any other name; a ported
structure keeps the vendored field names, and a field that becomes a theorem (a vendored
`isNormalized` field, say) pairs with the theorem.

A `private` declaration of the ported file cannot be used by an importer, so it never counts as
the counterpart of a public vendored declaration: it pairs only with a private vendored one of the
same name, and is otherwise reported on a `private` line, not as new.

    python3 scripts/port-pairing.py MIPRE/Background/LIDT/Co/Basic/QuantumState.lean
    python3 scripts/port-pairing.py MIPRE/Background/LIDT/Co          # every ported file
    python3 scripts/port-pairing.py --check MIPRE/Background/LIDT/Co  # exit 1 on a missing name
    python3 scripts/port-pairing.py --verbose ...                     # also list every pair

Python 3 standard library only.
"""
from __future__ import annotations

import argparse
import os
import re
import signal
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PORT_DIR = "MIPRE/Background/LIDT/Co"
# The LIDT development is a Lake dependency (`lakefile.toml`), checked out by `lake build`
# under `.lake/packages/MIPStarRE`; the port is paired against that checkout.
VENDOR_DIR = ".lake/packages/MIPStarRE/MIPStarRE/LDT"
VENDOR_TREE = ".lake/packages/MIPStarRE/MIPStarRE"
VENDOR_PREFIXES = ("MIPStarRE.LDT.", "MIPStarRE.")
PORT_PREFIXES = ("MIPRE.LIDT.Co.",)
# Namespaces of the state, renamed by the port; dropped from names before comparing.
MODEL_NS = {"QuantumState", "PureState", "SymModel", "VecState"}

KINDS = (
    r"theorem|lemma|def|abbrev|structure|class\s+inductive|class|inductive|opaque|axiom|"
    r"instance|alias"
)
MODIFIERS = r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local|public|meta)\s+)*"
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?P<mods>" + MODIFIERS + r")(?P<kind>" + KINDS + r")\b(?P<rest>.*)$"
)
# A structure field: `name : T`, `a b : T`, `name (x : α) : T`, `[name : C]`; not `name :=`
# (a default for an inherited field) nor `mk ::` (the constructor).
FIELD_RE = re.compile(
    r"^\s*(?:\[\s*(?P<inst>[^\s:\[\](){}]+)\s*:"
    r"|(?P<names>[^\s:\[\](){}⦃,]+(?:\s+[^\s:\[\](){}⦃,]+)*)\s*(?P<sep>::|:=|:|\(|\{|\[|⦃))"
)
WHERE_RE = re.compile(r"(?:^|\s)where(?:\s|$)")
NAME_RE = re.compile(r"^\s*(?:\(priority\s*:=\s*[^)]*\)\s*)?(?P<name>[^\s(){}\[\]:⦃,]+)")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>\S+)")
SECTION_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b(?:\s+(?P<name>\S+))?"
)
END_RE = re.compile(r"^\s*end\b(?:\s+(?P<name>[^\s-]+))?\s*$")
HEADING_RE = re.compile(r"^\s*#+\s*(?P<title>.*?)\s*$")
BULLET_RE = re.compile(r"^\s*[-*+]\s+`(?P<name>[^`]+)`")


def strip_comments(src: str) -> str:
    """Remove block comments (nested), line comments and string literals, keeping newlines."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                if c == "\n":
                    out.append("\n")
                i += 1
        elif two == "/-":
            depth = 1
            i += 2
        elif two == "--":
            while i < n and src[i] != "\n":
                i += 1
        elif c == '"':
            out.append('""')
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\":
                    i += 1
                elif src[i] == "\n":
                    out.append("\n")
                i += 1
            i += 1
        elif c == "'" and i + 2 < n and src[i + 2] == "'" and src[i + 1] != "\\":
            out.append("'_'")  # a character literal such as '"'
            i += 3
        else:
            out.append(c)
            i += 1
    return "".join(out)


def declarations(path: str) -> list[tuple[str, str, int, bool, str]]:
    """The named declarations of a Lean file: (full name, kind, line, private, parent), where
    `parent` is the structure of a field (kind `field`) and empty otherwise."""
    with open(path, encoding="utf-8") as f:
        text = strip_comments(f.read())
    stack: list[tuple[str, list[str]]] = []  # ("ns" | "sec", namespace components)
    decls = []
    # The structure whose fields are being read: [full name, indent, seen `where`, field indent].
    struct: list | None = None
    for lineno, line in enumerate(text.split("\n"), start=1):
        if struct is not None and line.strip():
            indent = len(line) - len(line.lstrip())
            if indent <= struct[1]:
                struct = None
            elif not struct[2]:
                if WHERE_RE.search(line):
                    struct[2] = True
                continue
            else:
                if struct[3] is None:
                    struct[3] = indent
                if indent == struct[3]:
                    fm = FIELD_RE.match(line)
                    if fm and fm.group("inst"):
                        names = [fm.group("inst")]
                    elif fm and fm.group("sep") not in ("::", ":="):
                        names = fm.group("names").split()
                    else:
                        names = []
                    for nm_ in names:
                        if nm_ not in ("deriving", "extends", "where"):
                            decls.append((struct[0] + "." + nm_, "field", lineno, False,
                                          struct[0]))
                continue
        m = NAMESPACE_RE.match(line)
        if m:
            stack.append(("ns", m.group("name").split(".")))
            continue
        m = END_RE.match(line)
        if m:
            if stack:
                stack.pop()
            continue
        if SECTION_RE.match(line) and not DECL_RE.match(line):
            stack.append(("sec", []))
            continue
        m = DECL_RE.match(line)
        if not m:
            continue
        kind = re.sub(r"\s+", " ", m.group("kind"))
        private = "private" in m.group("mods").split()
        rest = m.group("rest")
        if kind == "instance" and re.match(r"^\s*(?:\(priority\s*:=\s*[^)]*\)\s*)?[:\[{(⦃]", rest):
            continue  # anonymous instance
        nm = NAME_RE.match(rest)
        if not nm:
            continue
        name = nm.group("name")
        if name in ("where", ":=", "|") or name.startswith("⟨"):
            continue
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        else:
            prefix = [c for kind_, comps in stack for c in comps]
            full = ".".join(prefix + [name])
        decls.append((full, kind, lineno, private, ""))
        if kind in ("structure", "class"):
            struct = [full, len(line) - len(line.lstrip()), bool(WHERE_RE.search(rest)), None]
    return decls


def relative(name: str, prefixes: tuple[str, ...]) -> str:
    for p in prefixes:
        if name.startswith(p):
            return name[len(p):]
    return name


def normalize(rel: str) -> str:
    return ".".join(c for c in rel.split(".") if c not in MODEL_NS) or rel


def last(rel: str) -> str:
    return rel.split(".")[-1]


def not_ported_bullets(path: str) -> list[str]:
    """The names listed under a `Not ported` heading of the module docstring."""
    with open(path, encoding="utf-8") as f:
        src = f.read()
    m = re.search(r"/-!(.*?)-/", src, re.S)
    if not m:
        return []
    names, inside = [], False
    for line in m.group(1).split("\n"):
        h = HEADING_RE.match(line)
        if h:
            inside = h.group("title").lower().rstrip(":") == "not ported"
            continue
        if inside:
            b = BULLET_RE.match(line)
            if b:
                names.append(b.group("name").strip())
    return names


def lean_files(path: str) -> list[str]:
    if os.path.isfile(path):
        return [path]
    out = []
    for d, _, fs in os.walk(path):
        out += [os.path.join(d, f) for f in fs if f.endswith(".lean")]
    return sorted(out)


def rel_to_root(path: str) -> str:
    return os.path.relpath(os.path.abspath(path), ROOT)


def bullet_covers(bullet: str, rel: str) -> bool:
    return (bullet == rel or normalize(bullet) == normalize(rel) or rel.endswith("." + bullet))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("paths", nargs="+", help="ported files or directories under " + PORT_DIR)
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if a vendored name is neither ported nor listed")
    ap.add_argument("--verbose", action="store_true", help="list every pair")
    args = ap.parse_args()

    # Every ported declaration, for 'ported elsewhere'.
    port_index: dict[str, str] = {}
    for f in lean_files(os.path.join(ROOT, PORT_DIR)) if os.path.isdir(os.path.join(ROOT, PORT_DIR)) else []:
        for full, _, _, private, _ in declarations(f):
            if not private:
                port_index.setdefault(normalize(relative(full, PORT_PREFIXES)), rel_to_root(f))
    # Every vendored declaration (the whole MIPStarRE tree), for 'moved in'.
    vendor_index: dict[str, str] = {}
    for f in lean_files(os.path.join(ROOT, VENDOR_TREE)):
        for full, _, _, _, _ in declarations(f):
            comps = normalize(relative(full, VENDOR_PREFIXES)).split(".")
            for i in range(len(comps)):  # every dotted suffix, the full name first
                vendor_index.setdefault(".".join(comps[i:]),
                                        os.path.relpath(f, os.path.join(ROOT, VENDOR_TREE)))

    files = []
    for p in args.paths:
        files += lean_files(p if os.path.isabs(p) else os.path.join(ROOT, p))
    if not files:
        print("no Lean files under " + " ".join(args.paths), file=sys.stderr)
        return 2

    total_missing = 0
    totals = dict(vendored=0, ported=0, elsewhere=0, listed=0, loose=0, missing=0, new=0,
                  private=0)
    for f in files:
        rf = rel_to_root(f)
        if not rf.startswith(PORT_DIR + "/"):
            print(f"{rf}: not under {PORT_DIR}/, skipped", file=sys.stderr)
            continue
        sub = rf[len(PORT_DIR) + 1:]
        vf = os.path.join(ROOT, VENDOR_DIR, sub)
        if not os.path.isfile(vf):
            print(f"{rf}: no vendored counterpart {VENDOR_DIR}/{sub} (a new file)\n")
            continue
        vfull = declarations(vf)
        vdecls = [(relative(n, VENDOR_PREFIXES), k, ln) for n, k, ln, _, _ in vfull]
        vprivate = {relative(n, VENDOR_PREFIXES) for n, _, _, p, _ in vfull if p}
        vparent = {relative(n, VENDOR_PREFIXES): relative(par, VENDOR_PREFIXES)
                   for n, _, _, _, par in vfull if par}
        pfull = declarations(f)
        pdecls = [(relative(n, PORT_PREFIXES), k, ln) for n, k, ln, p, _ in pfull if not p]
        pprivate = [(relative(n, PORT_PREFIXES), k, ln) for n, k, ln, p, _ in pfull if p]
        bullets = not_ported_bullets(f)
        pnorm = {normalize(r): r for r, _, _ in pdecls}
        pnorm_private = {normalize(r): r for r, _, _ in pprivate}
        vnorm = {normalize(r) for r, _, _ in vdecls}

        status: dict[str, tuple[str, str]] = {}
        used_ported: set[str] = set()
        for r, _, _ in vdecls:
            n = normalize(r)
            if n in pnorm:
                status[r] = ("ported", pnorm[n])
                used_ported.add(pnorm[n])
            elif r in vprivate and n in pnorm_private:
                status[r] = ("ported", pnorm_private[n])
                used_ported.add(pnorm_private[n])
            elif n in port_index and port_index[n] != rf:
                status[r] = ("elsewhere", port_index[n])
            elif any(bullet_covers(b, r) for b in bullets):
                status[r] = ("listed", "")
        # A field of a structure that is not ported is not ported either.
        for r, _, _ in vdecls:
            if r not in status and status.get(vparent.get(r, ""), ("",))[0] == "listed":
                status[r] = ("listed", "")
        # Loose pairing: same last component, ported declaration otherwise unpaired.
        free_by_last: dict[str, list[str]] = {}
        for r, _, _ in pdecls:
            if r not in used_ported and normalize(r) not in vnorm:
                free_by_last.setdefault(last(r), []).append(r)
        for r, _, _ in vdecls:
            if r in status:
                continue
            cands = free_by_last.get(last(r), [])
            if cands:
                status[r] = ("loose", cands[0])
                used_ported.add(cands[0])
            else:
                status[r] = ("missing", "")

        counts = {k: 0 for k in ("ported", "elsewhere", "listed", "loose", "missing")}
        for st, _ in status.values():
            counts[st] += 1
        new = [(r, ln) for r, _, ln in pdecls if r not in used_ported]
        private_unpaired = [(r, ln) for r, _, ln in pprivate if r not in used_ported]
        stale = [b for b in bullets if not any(bullet_covers(b, r) for r, _, _ in vdecls)]
        contradicted = [b for b in bullets
                        if any(bullet_covers(b, r) and status.get(r, ("",))[0] == "ported"
                               for r, _, _ in vdecls)]

        print(f"{rf}  <-  {VENDOR_DIR}/{sub}")
        print(f"  vendored {len(vdecls)}: ported {counts['ported']}, loose {counts['loose']}, "
              f"ported elsewhere {counts['elsewhere']}, listed as not ported {counts['listed']}, "
              f"missing {counts['missing']}")
        print(f"  ported file {len(pdecls) + len(pprivate)}: paired "
              f"{len(pdecls) + len(pprivate) - len(new) - len(private_unpaired)}, new {len(new)}, "
              f"private {len(private_unpaired)}")
        for r, _, ln in vdecls:
            st, other = status[r]
            if st == "missing":
                print(f"  missing    {r}  (vendored line {ln})")
        for r, _, _ in vdecls:
            st, other = status[r]
            if st == "loose":
                print(f"  loose      {r}  ~  {other}")
            elif st == "elsewhere":
                print(f"  elsewhere  {r}  ->  {other}")
            elif args.verbose and st == "ported":
                print(f"  ported     {r}  =  {other}")
            elif args.verbose and st == "listed":
                print(f"  listed     {r}")
        for r, ln in new:
            src = vendor_index.get(normalize(r))
            print(f"  new        {r}" + (f"  [from vendored {src}]" if src else ""))
        for r, ln in private_unpaired:
            print(f"  private    {r}  (line {ln})")
        for b in stale:
            print(f"  stale 'Not ported' bullet `{b}`: names no vendored declaration")
        for b in contradicted:
            print(f"  stale 'Not ported' bullet `{b}`: the declaration is ported")
        print()
        total_missing += counts["missing"]
        totals["vendored"] += len(vdecls)
        for k in counts:
            totals[k] += counts[k]
        totals["new"] += len(new)
        totals["private"] += len(private_unpaired)

    if len(files) > 1:
        print("total: " + ", ".join(f"{k} {v}" for k, v in totals.items()))
    if args.check and total_missing:
        print(f"port-pairing: {total_missing} vendored declaration(s) neither ported nor listed "
              "under 'Not ported'", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)  # `| head` is not an error
    sys.exit(main())
