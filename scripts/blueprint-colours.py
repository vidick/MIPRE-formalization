#!/usr/bin/env python3
r"""Is every proved result dark green in the blueprint's graph, as leanblueprint colours it?

`scripts/blueprint-edges.py` checks the `\uses` edges against the Lean from the LaTeX source;
this script asks leanblueprint itself. It parses the blueprint exactly as `leanblueprint web`
does --- plasTeX with the leanblueprint and plastexdepgraph plugins, stopping before anything
is rendered, about ten seconds --- and reads the colouring data that leanblueprint computes.
Its rule has corners that a reading of the source misses; after the edges were fixed, these
still kept 102 proved results pale, the main theorem among them:

* a result is *proved* only through a `\leanok` inside the proof environment attached to it:
  a statement-level `\leanok` with no proof environment does not count;
* a proof environment attaches to the nearest theorem-like environment before it in the
  same sectioning unit (a `\paragraph` opens one), and the last proof attached wins: a
  second, unmarked proof after a marked one unproves the result, and a proof nested inside
  its statement, or separated from it by a `\paragraph`, attaches to nothing;
* every label in `\uses` is an ancestor, drawn or not: a remark cited there is an ancestor
  that is never proved.

A proved result is dark green when every ancestor is proved or a definition. The checks:

* **detached** --- a proof environment carrying `\leanok` is not the one leanblueprint
  attaches to its statement;
* **pale** --- a proved result that is not a definition has an ancestor that is neither
  proved nor a definition. Reported by ancestor, with the number of results it holds back.

It also fails when plasTeX cannot read part of the blueprint, or finds no graph node at
all: plasTeX skips an `\input` it cannot resolve with a warning, and the checks above would
then pass on what is left.

Usage (needs `pip install leanblueprint`, which is what the blueprint deploy installs):
  scripts/blueprint-colours.py            report
  scripts/blueprint-colours.py --check    exit 1 on any finding
  scripts/blueprint-colours.py --verbose  also show plasTeX's own log
"""
import collections
import contextlib
import os
import pathlib
import shutil
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "blueprint" / "src"


def parse_blueprint(src, verbose=False):
    """The plasTeX document of the blueprint at `src`, after leanblueprint's post-parse
    callbacks (which compute the colouring data), and the number of warnings plasTeX logged."""
    from plasTeX.Compile import parse
    from plasTeX.Config import defaultConfig
    from plasTeX.TeX import TeX
    from plasTeX.client import collect_renderer_config

    def kpsewhich(self, name):
        # plasTeX resolves \input through TeX's kpsewhich, which a CI runner or a cloud
        # session does not have; the blueprint only inputs its own files
        here = os.path.dirname(getattr(self, "filename", "") or "")
        for d in (here, os.getcwd()):
            for f in (name, name + ".tex"):
                if os.path.isfile(os.path.join(d, f)):
                    return os.path.join(d, f)
        raise FileNotFoundError(f"Could not find any file named: {name}")

    TeX.kpsewhich = kpsewhich
    config = defaultConfig()
    collect_renderer_config(config)
    config.read([str(src / "plastex.cfg")])
    cwd = os.getcwd()
    # leanblueprint writes `lean_decls` next to the source directory: parse a copy
    with tempfile.TemporaryDirectory() as tmp:
        work = pathlib.Path(tmp) / "blueprint" / "src"
        shutil.copytree(src, work)
        log = pathlib.Path(tmp) / "plastex.log"
        try:
            with open(log, "wb") as sink, redirect_fds(sink.fileno()):
                os.chdir(work)
                try:
                    tex = parse("web.tex", config)
                finally:
                    os.chdir(cwd)
        except RecursionError:
            raise
        except Exception:
            print(log.read_text(encoding="utf-8", errors="replace")[-4000:])
            raise
        text = log.read_text(encoding="utf-8", errors="replace")
    if verbose:
        print(text)
    # plasTeX skips an \input it cannot read with a warning: the parse would then pass
    # on part of the blueprint
    unread = [line.strip() for line in text.splitlines()
              if "WARNING:" in line and ("File not found" in line or "Errno" in line)]
    return tex.ownerDocument, text.count("WARNING:"), unread


@contextlib.contextmanager
def redirect_fds(fd):
    """Send file descriptors 1 and 2 to `fd`: plasTeX's loggers hold the original streams, so
    redirecting `sys.stdout` does not silence them."""
    sys.stdout.flush()
    sys.stderr.flush()
    saved = os.dup(1), os.dup(2)
    os.dup2(fd, 1)
    os.dup2(fd, 2)
    try:
        yield
    finally:
        sys.stdout.flush()
        sys.stderr.flush()
        os.dup2(saved[0], 1)
        os.dup2(saved[1], 2)
        os.close(saved[0])
        os.close(saved[1])


def label(node):
    return getattr(node, "id", None) or "?"


def audit(doc):
    from plastexdepgraph.Packages.depgraph import item_kind

    graphs = doc.userdata["dep_graph"]["graphs"]
    nodes = set().union(*(g.nodes for g in graphs.values()))
    findings = collections.defaultdict(list)
    for proof in doc.getElementsByTagName("proof"):
        if not proof.userdata.get("leanok"):
            continue
        stmt = proof.userdata.get("proves")
        # (a proof attached to a remark is fine: remarks are not drawn)
        if stmt is None:
            words = " ".join(proof.textContent.split())[:60]
            findings["detached"].append(f"a marked proof attached to nothing: \"{words}...\"")
        elif stmt in nodes and stmt.userdata.get("proved_by") is not proof:
            findings["detached"].append(
                f"{label(stmt)}: a later proof environment replaces its marked proof")

    def why(a):
        if a not in nodes:
            return f"{item_kind(a) or 'a label'} the graph does not draw"
        if not a.userdata.get("leanok"):
            return "not stated in Lean"
        if a.userdata.get("proved_by") is None:
            return "statement marked, no proof environment attached"
        return "its proof environment carries no \\leanok"

    held = collections.defaultdict(list)
    for g in graphs.values():
        for n in g.nodes:
            if item_kind(n) == "definition" or not n.userdata.get("proved"):
                continue
            for a in g.ancestors(n):
                if not (a.userdata.get("proved", False) or item_kind(a) == "definition"):
                    held[a].append(label(n))
    for a, ns in sorted(held.items(), key=lambda kv: (-len(kv[1]), label(kv[0]))):
        findings["pale"].append(f"{label(a)} ({why(a)}) holds back {len(ns)} proved results, "
                                f"e.g. {', '.join(sorted(ns)[:3])}")
    return nodes, findings


def colours(doc, nodes):
    dg = doc.userdata["dep_graph"]
    names = {v[0]: v[1].lower() for v in dg["colors"].values()}
    names[dg["colors"]["defined"][0]] = "light green (formalized definitions)"
    names[dg["colors"]["proved"][0]] = "green (proved, not dark green)"
    names[dg["colors"]["fully_proved"][0]] = "dark green"
    names[dg["colors"]["can_prove"][0]] = "blue (ready to prove)"
    count = collections.Counter(names.get(dg["fillcolorizer"](n), "white") for n in nodes)
    return ", ".join(f"{c} {k}" for k, c in count.most_common())


def main(argv):
    try:
        import leanblueprint  # noqa: F401
    except ImportError:
        sys.exit("blueprint-colours: needs leanblueprint (pip install leanblueprint)")
    sys.setrecursionlimit(10000)
    try:
        doc, warnings, unread = parse_blueprint(SRC, verbose="--verbose" in argv)
    except RecursionError:
        print("blueprint-colours: the \\uses graph has a cycle, on which leanblueprint recurses "
              "forever (as the deploy would); scripts/blueprint-edges.py names it")
        return 1
    if unread:
        print("blueprint-colours: plasTeX could not read part of the blueprint:")
        for line in unread:
            print("  " + line)
        return 1
    nodes, findings = audit(doc)
    if not nodes:
        print("blueprint-colours: the parse found no graph nodes; --verbose shows plasTeX's log")
        return 1
    summary = f"{len(nodes)} graph nodes: {colours(doc, nodes)}"
    print(summary)
    if os.environ.get("GITHUB_ACTIONS") == "true":
        # an annotation on the check run: the colours show without opening the log
        print(f"::notice title=Blueprint graph colours::{summary}")
    print(f"(plasTeX: {warnings} warnings; --verbose shows its log)")
    for kind in ("detached", "pale"):
        items = findings.get(kind, [])
        print(f"\n{kind}: {len(items)}")
        for it in items:
            print("  " + it)
    if "--check" in argv and any(findings.values()):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
