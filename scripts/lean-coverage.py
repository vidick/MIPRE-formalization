#!/usr/bin/env python3
r"""Which Lean code does the blueprint account for, and has any of it been dropped?

Two jobs, both mechanical and both runnable in a session (no plastex, no pdflatex,
no `lake build`):

1. Resolution. Every name in a blueprint `\\lean{}` tag must be a declaration that
   exists in this repository. Unlike a line-by-line grep, the scanner here handles
   `\\lean{}` tags that wrap across lines, which the blueprint uses.

2. Cross-references. Every `\ref`/`\eqref`/`\cref`/`\uses` target must be a `\label`
   defined somewhere in the blueprint, every `\cite` key must be in the bibliography, no
   label may be defined twice, and environments must balance. This is the check
   `CLAUDE.md` asks for before merging LaTeX, since a session has no plastex.

3. Coverage. The blueprint names only the headline statements, so most declarations
   are legitimately unnamed; what must not happen is for a module that the blueprint
   *did* account for to stop being accounted for --- silently losing Lean code in a
   reorganization. `planning/lean-coverage.json` is the committed snapshot of what is
   named, and `--check` fails if any named declaration or covered module has lost its
   coverage.

Usage:
  scripts/lean-coverage.py              report
  scripts/lean-coverage.py --check      compare against the snapshot, exit 1 on a loss
  scripts/lean-coverage.py --refresh    rewrite the snapshot (do this deliberately)
"""
import collections
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CONTENT = ROOT / "blueprint" / "src" / "content"
SNAPSHOT = ROOT / "planning" / "lean-coverage.json"

# Read-only vendored trees: they are accounted for wholesale by the statements that
# the bridge modules re-export, never declaration by declaration.
VENDORED = (
    "MIPRE/Background/Repetition/TenProofs/",
    "MIPRE/Background/Repetition/CommutingRepetition/",
    "MIPRE/Background/LIDT/MIPStarRE/",
    "MIPRE/Background/Orthonormalization/Orthogonalization/",
)

DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive", "class")
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(" + "|".join(DECL_KINDS) + r")\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?\u2080-\u2089]*)"
)
NS_OPEN = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")
NS_END = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")
# `\lean{...}` possibly wrapped across lines; also used for `\label`.
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.S)
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
# These may wrap across lines too, so all of them are matched with re.S on whole files.
REF_RE = re.compile(r"\\(?:ref|eqref|autoref|cref|Cref)\{([^}]*)\}", re.S)
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.S)
CITE_RE = re.compile(r"\\cite[tp]?\{([^}]*)\}", re.S)
BIBITEM_RE = re.compile(r"\\bibitem(?:\[[^\]]*\])?\{([^}]*)\}")
ENV_BEGIN_RE = re.compile(r"\\begin\{([a-zA-Z*]+)\}")
ENV_END_RE = re.compile(r"\\end\{([a-zA-Z*]+)\}")


def strip_comments(text: str) -> str:
    return re.sub(r"(?<!\\)%.*", "", text)


def blueprint_names():
    """name -> list of labels citing it, and the count of tags seen."""
    out = collections.defaultdict(list)
    tags = 0
    for f in sorted(CONTENT.glob("*.tex")):
        text = strip_comments(f.read_text())
        for m in LEAN_RE.finditer(text):
            tags += 1
            # the nearest preceding \label is the environment this tag belongs to
            before = text[: m.start()]
            labs = LABEL_RE.findall(before)
            label = labs[-1] if labs else f"{f.name}:?"
            for n in m.group(1).split(","):
                n = n.strip()
                if n:
                    out[n].append(label)
    return out, tags


def cross_references():
    """Returns (problems, counts) for labels, refs, uses, cites and environment nesting."""
    labels, dup, refs, cites = {}, [], [], []
    problems, env_events = [], []
    for f in sorted(CONTENT.glob("*.tex")):
        text = strip_comments(f.read_text())
        for m in LABEL_RE.finditer(text):
            lab = m.group(1).strip()
            line = text.count("\n", 0, m.start()) + 1
            if lab in labels:
                dup.append(f"{f.name}:{line}: label {lab!r} also at {labels[lab]}")
            else:
                labels[lab] = f"{f.name}:{line}"
        for rx, bucket in ((REF_RE, refs), (USES_RE, refs), (CITE_RE, cites)):
            for m in rx.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                for t_ in m.group(1).split(","):
                    if t_.strip():
                        bucket.append((t_.strip(), f"{f.name}:{line}"))
        # environment nesting, per file
        marks = [(m.start(), True, m.group(1)) for m in ENV_BEGIN_RE.finditer(text)]
        marks += [(m.start(), False, m.group(1)) for m in ENV_END_RE.finditer(text)]
        stack = []
        for pos, opening, name in sorted(marks):
            line = text.count("\n", 0, pos) + 1
            if opening:
                stack.append((name, line))
            elif not stack:
                problems.append(f"{f.name}:{line}: \\end{{{name}}} with nothing open")
            else:
                top, ln = stack.pop()
                if top != name:
                    problems.append(f"{f.name}:{line}: \\end{{{name}}} closes "
                                    f"\\begin{{{top}}} opened at line {ln}")
        for name, ln in stack:
            problems.append(f"{f.name}:{ln}: \\begin{{{name}}} never closed")
        env_events.append(len(marks))
    bib = set()
    for f in sorted(CONTENT.glob("*.tex")):
        bib |= set(BIBITEM_RE.findall(f.read_text()))
    problems += dup
    for target, where in refs:
        if target not in labels:
            problems.append(f"{where}: reference to undefined label {target!r}")
    for key, where in cites:
        if key not in bib:
            problems.append(f"{where}: \\cite of unknown key {key!r}")
    return problems, dict(labels=len(labels), refs=len(refs), cites=len(cites),
                          bibitems=len(bib))


def lean_declarations():
    """fully-qualified name -> module, over every Lean file including vendored ones."""
    index = {}
    per_module = {}
    for p in sorted(ROOT.glob("MIPRE/**/*.lean")):
        rel = str(p.relative_to(ROOT))
        stack, decls = [], []
        for line in p.read_text().splitlines():
            mo = NS_OPEN.match(line)
            if mo:
                stack.append(mo.group(1))
                continue
            me = NS_END.match(line)
            if me:
                if stack and stack[-1] == me.group(1):
                    stack.pop()
                continue
            md = DECL_RE.match(line)
            if md:
                full = ".".join(stack + [md.group(2)]) if stack else md.group(2)
                index.setdefault(full, rel)
                if not line.startswith("private"):
                    decls.append(full)
        if not any(rel.startswith(v) for v in VENDORED):
            per_module[rel] = decls
    return index, per_module


def build():
    cited, tags = blueprint_names()
    index, per_module = lean_declarations()
    unresolved = sorted(n for n in cited if n not in index)
    xref_problems, xref_counts = cross_references()
    covered_modules = {}
    for rel, decls in per_module.items():
        hits = sorted(n for n in decls if n in cited)
        if hits:
            covered_modules[rel] = hits
    return dict(
        lean_tags=tags,
        xref_problems=xref_problems,
        xref_counts=xref_counts,
        cited_names=sorted(cited),
        unresolved=unresolved,
        covered_modules=covered_modules,
        module_sizes={rel: len(d) for rel, d in per_module.items()},
        cited_labels={n: sorted(set(v)) for n, v in sorted(cited.items())},
    )


def report(state):
    sizes = state["module_sizes"]
    cov = state["covered_modules"]
    total = sum(sizes.values())
    named = len(state["cited_names"])
    xc = state["xref_counts"]
    print(f"labels {xc['labels']}   refs+uses {xc['refs']}   cites {xc['cites']}   "
          f"bibitems {xc['bibitems']}")
    if state["xref_problems"]:
        print("\nCROSS-REFERENCE PROBLEMS:")
        for q in state["xref_problems"]:
            print("  " + q)
    print(f"blueprint \\lean{{}} tags: {state['lean_tags']}   distinct names: {named}")
    print(f"non-vendored modules: {len(sizes)}   public declarations: {total}")
    print(f"modules the blueprint accounts for: {len(cov)} of {len(sizes)}")
    if state["unresolved"]:
        print("\nUNRESOLVED \\lean{} NAMES (no such declaration in this repository):")
        for n in state["unresolved"]:
            print(f"  {n}   cited by {', '.join(state['cited_labels'][n])}")
    print("\nACCOUNTED FOR")
    for rel in sorted(cov):
        print(f"  {rel:<62} {len(cov[rel]):>3}/{sizes[rel]:<4}")
    print("\nNOT NAMED BY ANY \\lean{} TAG")
    rest = sorted((rel for rel in sizes if rel not in cov), key=lambda r: -sizes[r])
    for rel in rest:
        print(f"  {rel:<62} {sizes[rel]:>5}")
    print(f"  --- {len(rest)} modules, {sum(sizes[r] for r in rest)} declarations ---")


def check(state):
    if not SNAPSHOT.exists():
        print(f"no snapshot at {SNAPSHOT.relative_to(ROOT)}; run --refresh", file=sys.stderr)
        return 1
    old = json.loads(SNAPSHOT.read_text())
    problems = list(state["xref_problems"])
    for n in state["unresolved"]:
        problems.append(f"\\lean{{{n}}} does not resolve "
                        f"(cited by {', '.join(state['cited_labels'][n])})")
    lost = sorted(set(old["cited_names"]) - set(state["cited_names"]))
    for n in lost:
        where = ", ".join(old["cited_labels"].get(n, ["?"]))
        problems.append(f"declaration no longer named by the blueprint: {n} (was cited by {where})")
    lost_mod = sorted(set(old["covered_modules"]) - set(state["covered_modules"]))
    for rel in lost_mod:
        problems.append(f"module lost all blueprint coverage: {rel}")
    for rel, hits in old["covered_modules"].items():
        now = set(state["covered_modules"].get(rel, []))
        gone = sorted(set(hits) - now)
        if gone and rel not in lost_mod:
            problems.append(f"{rel}: no longer named: {', '.join(gone)}")
    added = sorted(set(state["cited_names"]) - set(old["cited_names"]))
    if added:
        print(f"newly named ({len(added)}): {', '.join(added)}")
    for q in problems:
        print("  FAIL " + q, file=sys.stderr)
    print("PROBLEMS:", len(problems))
    return 1 if problems else 0


def main():
    state = build()
    if "--refresh" in sys.argv:
        SNAPSHOT.parent.mkdir(parents=True, exist_ok=True)
        snap = {k: v for k, v in state.items() if k != "xref_problems"}
        SNAPSHOT.write_text(json.dumps(snap, indent=1, sort_keys=True) + "\n")
        print(f"wrote {SNAPSHOT.relative_to(ROOT)}")
        return 0
    if "--check" in sys.argv:
        return check(state)
    report(state)
    return 1 if (state["unresolved"] or state["xref_problems"]) else 0


if __name__ == "__main__":
    sys.exit(main())
