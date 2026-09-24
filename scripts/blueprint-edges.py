#!/usr/bin/env python3
r"""Does the blueprint's dependency graph say what the Lean proofs use?

leanblueprint draws its graph from hand-written `\uses{}` lists and colours it from
hand-placed `\leanok` marks: a node is dark green when it and every ancestor is
formalized, light green when it is formalized but some ancestor is not. Nothing checked
that the edges are right, and after the main theorem was proved, 78 nodes --- the main
theorem among them --- were light green only because twelve edges still pointed at
paper-route lemmas that the Lean proof never used.

This script compares the edges with the Lean. `scripts/blueprint-deps.lean` dumps, from
the compiled modules, which constants each constant of this repository uses. A node's
declarations are the names in its `\lean{}`. Then, for the theorem-like nodes the graph
shows (definition, lemma, proposition, theorem, corollary):

* **Lean edges.** Node A *uses* node B in Lean when a declaration of A reaches a
  declaration of B through constants that belong to no third node. The transitive
  closure of these edges is exactly Lean reachability between nodes. A definition node is
  its definitions and the statements of its lemmas: the proofs of those lemmas may use
  later nodes without the definition depending on them.
* **shared** --- a declaration is listed by two graph nodes. Each declaration has one home;
  a node that relies on it cites the home. Otherwise the Lean cannot say which way the two
  nodes depend on each other. (Remarks are not drawn, and may list anything.)
* **unformalized** --- a formalized node cites (`\uses`) a node that is not: either the
  cited node's content is formalized and it lacks its marks, or the edge is stale.
* **stale** --- A cites B, both carry `\lean{}`, and no declaration of B is reachable
  from A's.
* **missing** --- A uses B in Lean, but B is not reachable from A through `\uses`.
* **cycle** --- the `\uses` graph has a cycle.
* **lean-cycle** --- information, not a failure: nodes whose declarations use one
  another's, so that the Lean does not order them. Edges between two such nodes are not
  required in either direction; the `\uses` graph must still not have a cycle.

A node is *formalized* when its proof carries `\leanok` (its statement, if it has no
proof). Edges are compared up to reachability, so a `\uses` list may cite an ancestor
instead of a direct dependency; it may not cite what the Lean does not use, nor leave out
what it does. `--fix` adds few edges: nodes are fixed dependencies first, and an edge is
added only when the target is not already reachable.

Usage:
  scripts/blueprint-edges.py                report (runs the Lean dump first)
  scripts/blueprint-edges.py --deps FILE    use an existing dump
  scripts/blueprint-edges.py --check        exit 1 on any finding
  scripts/blueprint-edges.py --fix          rewrite `\uses`: drop stale and unformalized
                                            edges, add missing ones, then re-check
  scripts/blueprint-edges.py --fix --only a,b    rewrite only the nodes labelled a and b
A `shared` finding needs a person to choose the declaration's home; `--fix` does not.
The dump needs the modules compiled (`lake build`); `LAKE` overrides the `lake` binary.
"""
import collections
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
CONTENT = ROOT / "blueprint" / "src" / "content"
NODE_ENVS = ("definition", "lemma", "proposition", "theorem", "corollary")
ALL_ENVS = NODE_ENVS + ("remark", "conjecture")
ENV_RE = re.compile(r"\\begin\{(" + "|".join(ALL_ENVS) + r")\}(\[[^\]]*\])?(.*?)\\end\{\1\}",
                    re.S)
PROOF_AFTER_RE = re.compile(r"\s*(?:%[^\n]*\n\s*)*\\begin\{proof\}")
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.S)
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.S)
LINE_WIDTH = 100


def comment_mask(text):
    """Positions inside a `%` comment (unescaped), so that commented-out tags are ignored."""
    mask = bytearray(len(text))
    for m in re.finditer(r"(?<!\\)%[^\n]*", text):
        mask[m.start():m.end()] = b"\x01" * (m.end() - m.start())
    return mask


def live(rx, text, mask, lo, hi):
    return [m for m in rx.finditer(text, lo, hi) if not mask[m.start()]]


def split_names(s):
    """The comma-separated names of a tag's argument. A `%` comments out the rest of its line,
    and the blueprint uses `,%` at a line break inside `\\uses{...}`."""
    s = re.sub(r"(?<!\\)%[^\n]*(\n|$)", "", s)
    return [x.strip() for x in s.replace("\n", " ").split(",") if x.strip()]


class Node:
    def __init__(self, **kw):
        self.__dict__.update(kw)

    @property
    def uses(self):
        return self.uses_stmt + [u for u in self.uses_proof if u not in self.uses_stmt]


def parse_blueprint():
    nodes = collections.OrderedDict()
    for f in sorted(CONTENT.glob("*.tex")):
        text = f.read_text(encoding="utf-8")
        mask = comment_mask(text)
        for m in ENV_RE.finditer(text):
            if mask[m.start()]:
                continue
            lo, hi = m.start(3), m.end(3)
            labs = live(LABEL_RE, text, mask, lo, hi)
            if not labs:
                continue
            label = labs[0].group(1).strip()
            proof = None
            pm = PROOF_AFTER_RE.match(text, m.end())
            if pm:
                plo = pm.end()
                phi = text.find("\\end{proof}", plo)
                proof = (plo, phi)
            stmt_uses = live(USES_RE, text, mask, lo, hi)
            proof_uses = live(USES_RE, text, mask, *proof) if proof else []
            nodes[label] = Node(
                label=label, kind=m.group(1), file=f, line=text.count("\n", 0, m.start()) + 1,
                title=(m.group(2) or "").strip("[]"), stmt=(lo, hi), proof=proof,
                label_end=labs[0].end(),
                lean=[n for t in live(LEAN_RE, text, mask, lo, hi) for n in split_names(t.group(1))],
                proof_ok=bool(proof) and bool(re.search(r"\\leanok\b", strip(text, mask, *proof))),
                uses_stmt=[u for x in stmt_uses for u in split_names(x.group(1))],
                uses_proof=[u for x in proof_uses for u in split_names(x.group(1))],
                stmt_uses_spans=[(x.start(), x.end()) for x in stmt_uses],
                proof_uses_spans=[(x.start(), x.end()) for x in proof_uses])
            n = nodes[label]
            n.stated = bool(re.search(r"\\(?:leanok|mathlibok)\b", strip(text, mask, lo, hi)))
            n.formalized = n.proof_ok if n.proof else n.stated
    return {l: n for l, n in nodes.items() if n.kind in NODE_ENVS}, nodes


def strip(text, mask, lo, hi):
    return "".join(c for c, k in zip(text[lo:hi], mask[lo:hi]) if not k)


def run_dump(keep_names, out_path):
    lake = os.environ.get("LAKE", "lake")
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as k:
        k.write("\n".join(sorted(keep_names)) + "\n")
        keep_path = k.name
    try:
        subprocess.run([lake, "env", "lean", "--run", "scripts/blueprint-deps.lean",
                        str(out_path), keep_path], cwd=ROOT, check=True)
    finally:
        os.unlink(keep_path)


def load_dump(path):
    consts, alias = {}, {}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            d = json.loads(line)
            if "a" in d:
                alias[d["n"]] = d["a"]
            else:
                consts[d["n"]] = d
    return consts, alias


def owners(graph):
    owner = collections.defaultdict(set)
    for l, n in graph.items():
        for d in n.lean:
            owner[d].add(l)
    return owner


def lean_edges(graph, consts, alias):
    """For each node with declarations, the groups of nodes it uses in Lean: one group per
    declaration of another node that it reaches, holding every node that lists that
    declaration (usually one). Returns (groups, groups reached from the statement)."""
    owner = owners(graph)

    def canon(c):
        return alias.get(c, c)

    def reach(label, starts, statement_only):
        found, seen, stack = set(), set(), list(starts)
        while stack:
            c = canon(stack.pop())
            if c in seen:
                continue
            seen.add(c)
            own = owner.get(c, set())
            if own and label not in own:
                found.add(frozenset(own))
                continue
            d = consts.get(c)
            if d is None:
                continue
            stack.extend(d["t"])
            if not statement_only or d["k"] != "thm":
                stack.extend(d["v"])
        return found

    groups, from_types = {}, {}
    for l, n in graph.items():
        decls = [canon(d) for d in n.lean if canon(d) in consts or canon(d) in owner]
        if not decls:
            continue
        type_starts = [x for d in decls for x in consts.get(d, {}).get("t", [])]
        # a definition node is its definitions and the statements of its lemmas: the proofs
        # of those lemmas may use later nodes without the definition depending on them
        val_starts = [x for d in decls
                      if n.kind != "definition" or consts.get(d, {}).get("k") != "thm"
                      for x in consts.get(d, {}).get("v", [])]
        # a node's own definitions are part of its statement
        stmt_starts = type_starts + [x for d in decls if consts.get(d, {}).get("k") != "thm"
                                     for x in consts[d]["v"]]
        from_types[l] = reach(l, stmt_starts, True)
        groups[l] = from_types[l] | reach(l, val_starts, False)
    return groups, from_types


def flatten(groups):
    """Lean edges to every member of every group: generous, for reachability."""
    return {l: set().union(*gs) if gs else set() for l, gs in groups.items()}


def closure(edges, start):
    seen, stack = set(), list(edges.get(start, ()))
    while stack:
        x = stack.pop()
        if x not in seen:
            seen.add(x)
            stack.extend(edges.get(x, ()))
    return seen


def find_cycles(edges):
    """Strongly connected components with more than one node, or a self-loop."""
    index, low, on, stack, out = {}, {}, set(), [], []
    counter = [0]
    sys.setrecursionlimit(10000)

    def visit(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in edges.get(v, ()):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1 or v in edges.get(v, ()):
                out.append(sorted(comp))

    for v in list(edges):
        if v not in index:
            visit(v)
    return out


def clusters(direct):
    """node -> the strongly connected component of the Lean graph containing it."""
    comp = {}
    for c in find_cycles(direct):
        for x in c:
            comp[x] = frozenset(c)
    return comp


def audit(graph, groups):
    direct = flatten(groups)
    comp = clusters(direct)
    uses = {l: [u for u in n.uses if u in graph and u != l] for l, n in graph.items()}
    lean_reach = {l: closure(direct, l) for l in direct}
    findings = collections.defaultdict(list)
    for l, n in graph.items():
        for u in uses[l]:
            b = graph[u]
            if n.formalized and not b.formalized:
                findings["unformalized"].append((l, u))
            elif (l in direct and u in direct and u not in lean_reach[l]
                  and not set(n.lean) & set(b.lean)):
                if n.formalized or u in n.uses_stmt:
                    findings["stale"].append((l, u))
    stale = set(findings["stale"]) | set(findings["unformalized"])
    kept = {l: [u for u in us if (l, u) not in stale] for l, us in uses.items()}
    for l in groups:
        reach = closure(kept, l)
        for g in sorted(groups[l], key=sorted):
            # within a cluster the Lean cannot say which way the blueprint should go
            if not g & reach and not g & comp.get(l, frozenset()):
                findings["missing"].append((l, g))
    findings["cycle"] = find_cycles(uses)
    # the Lean graph between nodes is acyclic unless a node's declarations are split badly
    findings["lean-cycle"] = find_cycles(direct)
    listed = collections.defaultdict(list)
    for l, n in graph.items():
        for d in n.lean:
            listed[d].append(l)
    findings["shared"] = [(d, ls) for d, ls in sorted(listed.items()) if len(ls) > 1]
    return findings


def describe(graph, direct, findings):
    lines = []
    total = sum(len(v) for v in findings.values())
    lines.append(f"{len(graph)} graph nodes, {len(direct)} with Lean declarations; "
                 f"{total} findings")
    lines.append("(lean-cycle is information, not a failure: nodes whose declarations use each "
                 "other's, so that the Lean cannot order them)")
    for kind in ("shared", "lean-cycle", "unformalized", "stale", "missing", "cycle"):
        items = findings.get(kind, [])
        lines.append(f"\n{kind}: {len(items)}")
        for it in items:
            if kind in ("cycle", "lean-cycle"):
                lines.append("  " + " <-> ".join(it))
            elif kind == "shared":
                lines.append(f"  {it[0]} is listed by {', '.join(it[1])}")
            else:
                a, b = it
                na = graph[a]
                if isinstance(b, frozenset):
                    b = next(iter(b)) if len(b) == 1 else "one of " + ", ".join(sorted(b))
                lines.append(f"  {a} -> {b}   ({na.file.name}:{na.line})")
    return "\n".join(lines)


# ---------------------------------------------------------------- rewriting \uses

def format_uses(names, indent=""):
    """`\\uses{a,b,...}`, wrapped at LINE_WIDTH with continuation lines indented by 2."""
    out, cur = [], indent + "\\uses{"
    for i, n in enumerate(names):
        piece = n + ("," if i < len(names) - 1 else "}")
        if len(cur) + len(piece) > LINE_WIDTH and not cur.endswith("{"):
            out.append(cur)
            cur = indent + "  " + piece
        else:
            cur += piece
    out.append(cur)
    return "\n".join(out)


def preferred(graph, group):
    """The member of a group of nodes sharing a declaration to cite: the most specific."""
    return min(group, key=lambda b: (len(graph[b].lean), b))


def minimal_additions(graph, groups, drop):
    """The missing edges to add, few: nodes are processed dependencies first, and an edge
    A -> B is added only when B is not already reachable from A. Once B has been processed,
    everything B uses in Lean is reachable from B, so one edge to B covers all of it; the
    targets of A are tried highest first, so that an edge to a node covers its ancestors."""
    direct = flatten(groups)
    comp = clusters(direct)
    uses = {l: [u for u in n.uses if u in graph and u != l and u not in drop.get(l, ())]
            for l, n in graph.items()}
    lean_reach = {l: closure(direct, l) for l in direct}
    # dependencies first: a node after everything it reaches in Lean (ties: by label)
    order = sorted(groups, key=lambda l: (len(lean_reach[l]), l))
    final = {l: list(us) for l, us in uses.items()}
    added = collections.defaultdict(list)
    for a in order:
        reach = closure(final, a)
        height = lambda g: (-max(len(lean_reach.get(b, ())) for b in g), sorted(g))
        for g in sorted(groups[a], key=height):
            if g & reach or g & comp.get(a, frozenset()):
                continue
            b = preferred(graph, g)
            final[a].append(b)
            added[a].append(b)
            reach |= {b} | closure(final, b)
    return added


def fix(graph, groups, from_types, findings, only=None):
    """Rewrite each touched node's `\\uses` lists (only those in `only`, if given).
    Returns the number of nodes changed."""
    drop = collections.defaultdict(set)
    for a, b in findings.get("stale", []) + findings.get("unformalized", []):
        if only is None or a in only:
            drop[a].add(b)
    add_stmt, add_proof = collections.defaultdict(list), collections.defaultdict(list)
    for a, bs in minimal_additions(graph, groups, drop).items():
        if only is not None and a not in only:
            continue
        n = graph[a]
        for b in bs:
            if any(b in g for g in from_types.get(a, ())) or not n.proof:
                add_stmt[a].append(b)
            else:
                add_proof[a].append(b)
    touched = set(drop) | set(add_stmt) | set(add_proof)
    edits = collections.defaultdict(list)  # file -> [(start, end, replacement)]
    for a in touched:
        n = graph[a]
        text = n.file.read_text(encoding="utf-8")
        for spans, extra, region in ((n.stmt_uses_spans, add_stmt[a], "stmt"),
                                     (n.proof_uses_spans, add_proof[a], "proof")):
            old = n.uses_stmt if region == "stmt" else n.uses_proof
            new = [u for u in old if u not in drop[a]]
            new += [u for u in extra if u not in new]
            if new == old:
                continue
            if spans:
                # replace the first \uses in the region, delete the others
                s, e = spans[0]
                line_start = text.rfind("\n", 0, s) + 1
                indent = text[line_start:s] if not text[line_start:s].strip() else ""
                edits[n.file].append((s, e, format_uses(new, indent)[len(indent):] if new else ""))
                for s2, e2 in spans[1:]:
                    edits[n.file].append((s2, e2, ""))
            elif new:
                if region == "stmt":
                    pos = text.find("\n", n.label_end)
                else:
                    pos = text.find("\n", n.proof[0] - 1) if text[n.proof[0] - 1] != "\n" \
                        else n.proof[0] - 1
                edits[n.file].append((pos, pos, "\n" + format_uses(new)))
    for f, es in edits.items():
        text = f.read_text(encoding="utf-8")
        for s, e, rep in sorted(es, reverse=True):
            text = text[:s] + rep + text[e:]
        # a \uses deleted to nothing leaves an empty line behind
        text = re.sub(r"\n[ \t]*\n(?=[ \t]*\\(?:leanok|lean\{|uses\{|ledgernode))", "\n", text)
        f.write_text(text, encoding="utf-8")
    return len(touched)


def main(argv):
    check = "--check" in argv
    do_fix = "--fix" in argv
    deps = None
    only = set(argv[argv.index("--only") + 1].split(",")) if "--only" in argv else None
    if "--deps" in argv:
        deps = pathlib.Path(argv[argv.index("--deps") + 1])
    graph, allnodes = parse_blueprint()
    keep = {d for n in allnodes.values() for d in n.lean}
    tmp = None
    if deps is None:
        tmp = tempfile.NamedTemporaryFile(suffix=".jsonl", delete=False)
        tmp.close()
        deps = pathlib.Path(tmp.name)
        run_dump(keep, deps)
    try:
        consts, alias = load_dump(deps)
        groups, from_types = lean_edges(graph, consts, alias)
        findings = audit(graph, groups)
        if do_fix and any(v for k, v in findings.items() if k != "lean-cycle"):
            changed = fix(graph, groups, from_types, findings, only)
            print(f"rewrote the \\uses lists of {changed} nodes")
            graph, allnodes = parse_blueprint()
            groups, from_types = lean_edges(graph, consts, alias)
            findings = audit(graph, groups)
        print(describe(graph, groups, findings))
    finally:
        if tmp is not None:
            os.unlink(tmp.name)
    failing = {k: v for k, v in findings.items() if k != "lean-cycle"}
    if (check or do_fix) and any(failing.values()):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
