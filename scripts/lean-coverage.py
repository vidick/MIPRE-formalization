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
    "MIPRE/Background/LiehrTsirelson/Upstream/",
)

DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive", "class",
               "instance")
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
        text = strip_comments(f.read_text(encoding="utf-8"))
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
        text = strip_comments(f.read_text(encoding="utf-8"))
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
        bib |= set(BIBITEM_RE.findall(f.read_text(encoding="utf-8")))
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
        rel = p.relative_to(ROOT).as_posix()
        stack, decls = [], []
        for line in p.read_text(encoding="utf-8").splitlines():
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


MACRO_DIR = ROOT / "blueprint" / "src" / "macros"
ALLOWED_COMMANDS = ROOT / "scripts" / "latex-allowed-commands.txt"

CMD_USE_RE = re.compile(r"\\([A-Za-z]+)")
MACRO_DEF_RE = re.compile(
    r"\\(?:newcommand|renewcommand|providecommand)\*?\s*\{?\\([A-Za-z]+)\}?"
    r"|\\def\s*\\([A-Za-z]+)"
    r"|\\DeclareMathOperator\*?\s*\{\\([A-Za-z]+)\}"
    r"|\\DeclarePairedDelimiter\s*\{\\([A-Za-z]+)\}")


def undefined_macros():
    """Commands used in the content and defined neither in macros/ nor in the allowlist.

    An undefined control sequence does not stop pdflatex under nonstopmode: it writes
    the PDF anyway and only returns 1 at the end, so latexmk aborts with no error line
    near the tail of the CI log. That is how \\downsize kept the blueprint red on main
    for about thirty hours. There is no pdflatex in a session, so this is the check.
    """
    used = set()
    for f in sorted(CONTENT.glob("*.tex")):
        used |= set(CMD_USE_RE.findall(strip_comments(f.read_text(encoding="utf-8"))))
    defined = set()
    for f in sorted(MACRO_DIR.glob("*.tex")):
        for m in MACRO_DEF_RE.finditer(f.read_text(encoding="utf-8")):
            defined.add(next(g for g in m.groups() if g))
    allowed = set()
    if ALLOWED_COMMANDS.exists():
        for line in ALLOWED_COMMANDS.read_text(encoding="utf-8").splitlines():
            if not line.startswith("#"):
                allowed.update(line.split())
    return sorted(used - defined - allowed), len(used), len(defined)


MATH_ENVS = {"equation", "equation*", "align", "align*", "gather", "gather*", "multline",
             "multline*", "displaymath", "eqnarray", "eqnarray*", "alignat", "alignat*"}

# Commands whose braced argument is not typeset, so an underscore inside it is harmless.
NAME_ARG_CMDS = {"label", "ref", "eqref", "cref", "Cref", "uses", "lean", "proves", "cite",
                 "ledgernode", "input", "discussion", "href", "url", "verb"}


def text_mode_specials():
    """`_` and `^` outside math mode, which stop pdflatex.

    They stop it the *invisible* way: under nonstopmode pdflatex prints `! Missing $
    inserted.`, carries on, writes the PDF and returns 1 only at the end, after which
    latexmk refuses to rerun and reports every reference in the document as unresolved.
    The tail of the CI log is then hundreds of undefined-reference warnings with no `!`
    line near it. That kept the blueprint red on `main` from #118 until the error was
    finally surfaced by adding `-halt-on-error` to `blueprint/src/latexmkrc`; the cause
    was two Lean identifiers quoted with backticks instead of `\texttt{}`, in
    `02_foundations.tex`. This check is what makes that class of failure cheap to find,
    since there is no pdflatex in a session.

    A single backtick before a letter is flagged too: it is never what this blueprint
    means (code is `\texttt{}`, quotation marks are doubled), and it is how the
    underscores got in.
    """
    problems = []
    for f in sorted(CONTENT.glob("*.tex")):
        src = f.read_text(encoding="utf-8")
        i, n, line = 0, len(src), 1
        math = 0          # `$` nesting, 0 or 1
        envs = []         # open math environments
        while i < n:
            c = src[i]
            if c == "\n":
                line += 1
                i += 1
                continue
            if c == "%":
                while i < n and src[i] != "\n":
                    i += 1
                continue
            if c == "\\":
                j = i + 1
                while j < n and src[j].isalpha():
                    j += 1
                name = src[i + 1:j]
                if name == "":                      # \_, \$, \&, \% ... and \[ \] \( \)
                    if i + 1 < n and src[i + 1] in "[(":
                        math = 1
                    elif i + 1 < n and src[i + 1] in "])":
                        math = 0
                    i += 2
                    continue
                if name == "begin" or name == "end":
                    k = src.find("{", j)
                    if k != -1 and k < n:
                        e = src.find("}", k)
                        env = src[k + 1:e]
                        if env in MATH_ENVS:
                            if name == "begin":
                                envs.append(env)
                            elif envs:
                                envs.pop()
                        i = e + 1
                        continue
                if name in NAME_ARG_CMDS:
                    k = j
                    while k < n and src[k] in " \n":
                        if src[k] == "\n":
                            line += 1
                        k += 1
                    if k < n and src[k] == "{":
                        depth, k = 1, k + 1
                        while k < n and depth:
                            if src[k] == "{":
                                depth += 1
                            elif src[k] == "}":
                                depth -= 1
                            elif src[k] == "\n":
                                line += 1
                            k += 1
                        i = k
                        continue
                i = j
                continue
            if c == "$":
                math = 1 - math
                i += 1
                continue
            if c in "_^" and not math and not envs:
                problems.append(f"{f.name}:{line}: {c!r} in text mode "
                                f"(escape it, or put it in math or \\texttt{{}})")
            if c == "`" and i + 1 < n and src[i + 1] == "`":
                i += 2                              # ``opening quotation marks''
                continue
            if c == "`" and i + 1 < n and src[i + 1].isalpha():
                problems.append(f"{f.name}:{line}: single backtick before a letter "
                                f"(code is \\texttt{{}} here, quotation marks are doubled)")
            i += 1
        if math or envs:
            problems.append(f"{f.name}: unbalanced math mode at end of file")
    return problems


AXIOM_GUARDS = [ROOT / "MIPRE" / "Axioms.lean",
                ROOT / "MIPRE" / "Background" / "LIDT" / "Axioms.lean",
                ROOT / "MIPRE" / "Background" / "QLD" / "Axioms.lean",
                ROOT / "MIPRE" / "Background" / "Repetition" / "Axioms.lean"]

AXIOM_DECL_RE = re.compile(r"^(?:public\s+)?axiom\s+([A-Za-z_][A-Za-z0-9_.']*)", re.M)
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)", re.M)

PROOF_ENV_RE = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.S)
PRINT_AX_RE = re.compile(r"^#print axioms\s+([A-Za-z0-9_.']+)", re.M)
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def axiom_problems():
    """Every `axiom` this project declares must be recorded in `MIPRE/Axioms.lean`.

    `#guard_sorry_free` catches `sorryAx` and nothing else, so an `axiom` would otherwise
    enter the dependency graph with nothing to notice it -- and an axiom is a stronger claim
    than a `sorry`, because everything resting on it builds. The blueprint says the project
    assumes exactly one thing beyond Mathlib (Shoup's construction, `lem:self-dual-basis`);
    this check is what keeps that sentence true. The vendored trees are excluded: they are
    read-only and carry their own guard files.
    """
    recorded = AXIOM_GUARDS[0].read_text(encoding="utf-8") if AXIOM_GUARDS[0].exists() else ""
    problems, found = [], []
    for f in sorted((ROOT / "MIPRE").rglob("*.lean")):
        rel = f.relative_to(ROOT).as_posix()
        if rel.startswith("MIPRE/Background/"):
            continue
        text = f.read_text(encoding="utf-8")
        names = AXIOM_DECL_RE.findall(text)
        if not names:
            continue
        ns = NAMESPACE_RE.findall(text)
        prefix = (ns[-1] + ".") if ns else ""
        for n in names:
            full = n if "." in n else prefix + n
            found.append(full)
            if full not in recorded:
                problems.append(f"{rel} declares `axiom {n}` but MIPRE/Axioms.lean does not "
                                f"name {full}; record it there with its contract")
    return problems, found


def proof_level_leanok():
    """Declarations whose *proof* the blueprint marks \\leanok, by blueprint label."""
    out = {}
    for f in sorted(CONTENT.glob("*.tex")):
        text = strip_comments(f.read_text(encoding="utf-8"))
        for m in PROOF_ENV_RE.finditer(text):
            if "\\leanok" not in m.group(1):
                continue
            before = text[: m.start()]
            tags = LEAN_RE.findall(before)
            if not tags:
                continue
            labs = LABEL_RE.findall(before)
            label = labs[-1] if labs else f"{f.name}:?"
            names = {n.strip() for n in tags[-1].split(",") if n.strip()}
            out.setdefault(label, set()).update(names)
    return out


def guarded_names():
    """Declarations asserted sorry-free by an axiom-guard file."""
    out = set()
    for f in AXIOM_GUARDS:
        if not f.exists():
            continue
        lines = f.read_text(encoding="utf-8").splitlines()
        i = 0
        while i < len(lines):
            # Only a real invocation starts the line; the elaborator's own definition and its
            # doc-comment mention `#guard_sorry_free` indented or inside backticks.
            if lines[i].startswith("#guard_sorry_free"):
                chunk = [lines[i][len("#guard_sorry_free"):]]
                i += 1
                while i < len(lines) and lines[i][:1].isspace() and lines[i].strip():
                    chunk.append(lines[i])
                    i += 1
                out.update(NAME_RE.findall(" ".join(chunk)))
            else:
                i += 1
        out.update(PRINT_AX_RE.findall("\n".join(lines)))
    return out


def leanok_guard_problems():
    """The blueprint's proof-level claims and the axiom guards must name the same set.

    `\\leanok` inside a proof asserts the proof closes. Nothing checked that until now; the
    one audit behind it (`planning/lean-coverage.md`) was run by hand against a tree of 80
    modules and the tree has grown well past it. A claim without a guard is an unchecked
    assertion about the project's own mathematics, and a guard without a claim is a leftover
    that will one day be read as one.
    """
    claimed = proof_level_leanok()
    flat = {n for v in claimed.values() for n in v}
    guarded = guarded_names()
    problems = []
    for label in sorted(claimed):
        for n in sorted(claimed[label] - guarded):
            problems.append(f"{label}: proof marked \\leanok but {n} is not asserted "
                            f"sorry-free in any axiom-guard file")
    for n in sorted(guarded - flat):
        problems.append(f"{n} is axiom-guarded but no blueprint proof claims it; "
                        f"drop the guard or restore the \\leanok")
    return problems, len(flat), len(guarded)


def build():
    cited, tags = blueprint_names()
    index, per_module = lean_declarations()
    unresolved = sorted(n for n in cited if n not in index)
    xref_problems, xref_counts = cross_references()
    guard_problems, n_claimed, n_guarded = leanok_guard_problems()
    xref_problems.extend(guard_problems)
    ax_problems, ax_found = axiom_problems()
    xref_problems.extend(ax_problems)
    xref_counts["axioms_declared"] = len(ax_found)
    xref_counts["leanok_claimed"] = n_claimed
    xref_counts["leanok_guarded"] = n_guarded
    xref_problems.extend(text_mode_specials())
    undef, used_cmds, defined_cmds = undefined_macros()
    xref_counts["commands_used"] = used_cmds
    xref_counts["commands_defined"] = defined_cmds
    for name in undef:
        xref_problems.append(
            f"\\{name} is used in the blueprint but defined nowhere in "
            f"blueprint/src/macros/ (and is not in scripts/latex-allowed-commands.txt)")
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
    print(f"commands used {xc['commands_used']}   defined in macros/ {xc['commands_defined']}")
    print(f"proof-level \\leanok declarations {xc['leanok_claimed']}   "
          f"axiom-guarded {xc['leanok_guarded']}")
    print(f"axioms declared outside the vendored trees {xc['axioms_declared']}   "
          f"(each must be recorded in MIPRE/Axioms.lean)")
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
    old = json.loads(SNAPSHOT.read_text(encoding="utf-8"))
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
        SNAPSHOT.write_text(json.dumps(snap, indent=1, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote {SNAPSHOT.relative_to(ROOT)}")
        return 0
    if "--check" in sys.argv:
        return check(state)
    report(state)
    return 1 if (state["unresolved"] or state["xref_problems"]) else 0


if __name__ == "__main__":
    sys.exit(main())
