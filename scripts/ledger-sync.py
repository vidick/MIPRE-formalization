#!/usr/bin/env python3
"""Keep the blueprint's ledger provenance honest.

The blueprint accounts for the adversarially verified decomposition of the proof recorded
in the companion repository ``vidick/mipre-proof`` (a vibefeld/``af`` campaign: an
event-sourced ledger of nodes, challenges and validations). A statement here declares
which node or nodes it accounts for with ``\\ledgernode{1.5.3}`` in its environment; that
macro expands to nothing, so it is source-only provenance.

The ledger is a live artifact in another repository, so the correspondence rots silently
unless something checks it. This script is that something. It has two modes.

**Check** (no arguments, what CI and a session should run)::

    python3 scripts/ledger-sync.py

reads the ``\\ledgernode{}`` annotations out of ``blueprint/src/content/*.tex`` and
compares them with the committed snapshot ``planning/ledger-index.json``. It reports
annotations naming a node the snapshot does not have, nodes the blueprint claims which the
ledger records as *admitted* rather than validated, and per-stage coverage: how many nodes
of each stage any blueprint statement accounts for.

**Refresh** (needs a clone of the companion repository)::

    python3 scripts/ledger-sync.py --ledger /path/to/mipre-proof

replays that clone's ledger, rewrites the snapshot, and --- the part that matters --- says
which nodes changed since the committed snapshot, flagging separately those the blueprint
references. A node whose statement changed under a blueprint statement that cites it is
exactly the case a human has to look at.

Neither mode needs Lean, LaTeX or the network. Exit status is 0 when the check passes and
1 when it does not, so it is usable as a CI step.
"""

import argparse
import glob
import hashlib
import io
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SNAPSHOT = os.path.join(HERE, "planning", "ledger-index.json")
CONTENT = os.path.join(HERE, "blueprint", "src", "content", "*.tex")

NODE_RE = re.compile(r"\\ledgernode\{([^}]*)\}")

# A site naming this many nodes or more is reported as an umbrella rather than a
# statement written for them. Five is where "a lemma and its parts" stops being a
# fair description of the grouping.
UMBRELLA_MIN = 5
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")


def stage_of(node_id):
    """The top-level stage a node belongs to: 1.2.3.6 -> 1.2, and 1 -> 1."""
    parts = node_id.split(".")
    return ".".join(parts[:2]) if len(parts) > 1 else parts[0]


def read_ledger(path):
    """Replay the event log of a mipre-proof clone into {node_id: record}."""
    files = sorted(glob.glob(os.path.join(path, "proofs", "*", "ledger", "*.json")))
    if not files:
        sys.exit("no ledger events under %s (expected proofs/*/ledger/*.json)" % path)
    events = []
    for f in files:
        try:
            events.append(json.load(io.open(f, encoding="utf-8")))
        except ValueError as exc:
            sys.exit("unparsable ledger event %s: %s" % (f, exc))

    nodes = {}
    for e in events:
        if e.get("type") == "node_created":
            n = e["node"]
            nodes[n["id"]] = {
                "state": "created",
                "challenges": 0,
                "amended": 0,
                "archived": False,
                "taint": None,
                "deps": sorted(n.get("dependencies") or []),
                "statement_sha256": hashlib.sha256(
                    n.get("statement", "").encode("utf-8")).hexdigest(),
            }
    transitions = {"node_validated": "validated", "node_admitted": "admitted",
                   "node_unvalidated": "created", "node_unadmitted": "created"}
    for e in events:
        nid, t = e.get("node_id"), e.get("type")
        if nid not in nodes:
            continue
        if t in transitions:
            nodes[nid]["state"] = transitions[t]
        elif t == "challenge_raised":
            nodes[nid]["challenges"] += 1
        elif t == "node_archived":
            # A superseded node. It keeps its history but is no longer an obligation,
            # so it must leave the coverage denominator -- otherwise a re-grain upstream
            # silently pushes a stage below 100%.
            nodes[nid]["archived"] = True
        elif t == "taint_recomputed":
            nodes[nid]["taint"] = e.get("new_taint")
        elif t == "node_deps_amended":
            # 0.1.7+mipre.deps1 appends edge corrections rather than rewriting the node.
            nodes[nid]["deps"] = sorted(e.get("new_dependencies") or [])
        elif t == "node_amended":
            nodes[nid]["amended"] += 1
            st = e.get("new_statement")
            if st is not None:
                nodes[nid]["statement_sha256"] = hashlib.sha256(
                    st.encode("utf-8")).hexdigest()

    head = ""
    try:
        head = subprocess.check_output(
            ["git", "-C", path, "rev-parse", "--short", "HEAD"],
            stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        pass
    return {"source": "vidick/mipre-proof", "head": head,
            "events": len(events), "nodes": nodes}


def read_blueprint():
    """{node_id: [blueprint labels citing it]} from the \\ledgernode annotations."""
    cited = {}
    for f in sorted(glob.glob(CONTENT)):
        s = io.open(f, encoding="utf-8").read()
        # Attribute each annotation to the nearest preceding \label in the same file.
        for m in NODE_RE.finditer(s):
            labels = LABEL_RE.findall(s[:m.start()])
            owner = labels[-1] if labels else "(no label)"
            for nid in (x.strip() for x in m.group(1).split(",")):
                if nid:
                    cited.setdefault(nid, []).append(owner)
    return cited


def import_reach(nodes):
    """{node_id: [admitted nodes its correctness rests on]}, over live nodes.

    The ledger's own ``taint`` field is computed from tree ancestry alone --- see
    ``reports/vibefeld-issue-dependency-edges.md`` in the companion repository, which
    records that 0.1.7 does not propagate along reference edges. So a node that consumes
    an admitted import through a declared dependency displays as ``clean``. This walks
    both relations, children *and* declared dependencies, which is what "my correctness
    rests on an admission" actually means, and is therefore the figure to quote when the
    blueprint says what it assumes beyond Mathlib.
    """
    live = {k: v for k, v in nodes.items() if not v.get("archived")}
    edges = {}
    for k, v in live.items():
        e = set(d for d in v.get("deps", []) if d in live)
        if "." in k:
            parent = k.rsplit(".", 1)[0]
            if parent in live:
                edges.setdefault(parent, set()).add(k)   # a parent rests on its children
        edges.setdefault(k, set()).update(e)
    memo = {}

    def walk(k, stack):
        if k in memo:
            return memo[k]
        if k in stack:
            return set()
        if live[k]["state"] == "admitted":
            memo[k] = {k}
            return memo[k]
        out = set()
        for c in edges.get(k, ()):
            out |= walk(c, stack | {k})
        memo[k] = out
        return out

    return dict((k, sorted(walk(k, set()))) for k in live)


def load_snapshot():
    if not os.path.exists(SNAPSHOT):
        sys.exit("no snapshot at %s; run with --ledger PATH to create one" % SNAPSHOT)
    return json.load(io.open(SNAPSHOT, encoding="utf-8"))


def check(snap, cited):
    all_nodes = snap["nodes"]
    nodes = dict((k, v) for k, v in all_nodes.items() if not v.get("archived"))
    problems = 0

    unknown = sorted(n for n in cited if n not in all_nodes)
    if unknown:
        problems += len(unknown)
        print("PROBLEM: %d annotation(s) name a node the snapshot does not have:" % len(unknown))
        for n in unknown:
            print("   %-12s cited by %s" % (n, ", ".join(cited[n])))

    archived = sorted(n for n in cited if n in all_nodes and all_nodes[n].get("archived"))
    if archived:
        problems += len(archived)
        print("PROBLEM: %d annotation(s) name a node the ledger has ARCHIVED (superseded "
              "upstream; re-home the annotation on its replacement):" % len(archived))
        for n in archived:
            print("   %-12s cited by %s" % (n, ", ".join(cited[n])))

    admitted = sorted(n for n in cited if n in nodes and nodes[n]["state"] == "admitted")
    if admitted:
        print("\nNote: %d cited node(s) are ADMITTED in the ledger (assumed, not proved) --"
              " the blueprint should present them as imports:" % len(admitted))
        for n in admitted:
            print("   %-12s cited by %s" % (n, ", ".join(cited[n])))

    print("\ncoverage by stage, counting only nodes an annotation names, archived nodes excluded.")
    print("These counts measure explicit annotations, not theorem equivalence or Lean proofs.")
    print("A stage below 100% can reflect finer-grained source decomposition or a different")
    print("proof route; a falling count needs review. See planning/paper-correspondence.md")
    print("for current adapters and planning/ledger-informed-plan.md for historical accounting.")
    by_stage = {}
    for nid in nodes:
        by_stage.setdefault(stage_of(nid), [0, 0])[0] += 1
    for nid in cited:
        if nid in nodes:
            by_stage.setdefault(stage_of(nid), [0, 0])[1] += 1
    for st in sorted(by_stage, key=lambda s: [int(x) for x in s.split(".")]):
        total, done = by_stage[st]
        bar = "#" * int(round(20.0 * done / total)) if total else ""
        print("   %-5s %3d/%-3d %s" % (st, done, total, bar))

    # How thinly is each annotation spread? A site naming one node is a statement
    # written for that node; a site naming twenty is an umbrella, and the nodes under
    # it are "accounted for" only in the sense that something upstream of them exists.
    # Counting nodes is therefore not the same as describing them, and this report is
    # here so the coverage figure above cannot be read as the stronger claim.
    sites = {}
    for nid, owners in cited.items():
        if nid in nodes:
            for o in owners:
                sites.setdefault(o, []).append(nid)
    umbrella = sorted(((o, ns) for o, ns in sites.items() if len(ns) >= UMBRELLA_MIN),
                      key=lambda kv: -len(kv[1]))
    if umbrella:
        carried = sum(len(ns) for _, ns in umbrella)
        print("\nannotation spread. %d node(s) are carried by %d umbrella site(s) naming"
              % (carried, len(umbrella)))
        print("%d or more nodes each. Those nodes are cited, not described: the blueprint"
              % UMBRELLA_MIN)
        print("says nothing about their substructure, and a reader cannot tell from it what")
        print("the sub-nodes contain. Defensible when the umbrella's proof is finished in")
        print("Lean; a gap when it is not.")
        for o, ns in umbrella:
            print("   %-30s %3d nodes  (%s ...)" % (o, len(ns), ", ".join(sorted(ns)[:3])))
        solo = sum(1 for o, ns in sites.items() if len(ns) == 1)
        print("   for contrast, %d site(s) name exactly one node." % solo)

    # What does the blueprint actually rest on? The admitted nodes it reaches, following
    # declared dependencies as well as decomposition. See import_reach's docstring for why
    # this is not the ledger's own taint figure.
    reach = import_reach(all_nodes)
    resting = {}
    for n in cited:
        for adm in reach.get(n, ()):
            resting.setdefault(adm, set()).update(cited[n])
    if resting:
        print("\nimport reach. Statements of this blueprint reach %d admitted node(s). Reach"
              % len(resting))
        print("follows the decomposition tree, and a node's children include its *corollaries*")
        print("as well as its premises -- stage 1.8 hangs under the root that way -- so read a")
        print("reach through a corollary subtree as 'the chapter needs it', not 'the theorem")
        print("assumes it'.")
        for adm in sorted(resting):
            who = sorted(resting[adm])
            print("   %-12s from %d statement(s): %s%s"
                  % (adm, len(who), ", ".join(who[:4]), " ..." if len(who) > 4 else ""))
        clean = sum(1 for n in cited if n in reach and not reach[n])
        print("   %d of %d cited nodes reach no admission at all." % (clean, len(cited)))

    total = len(nodes)
    accounted = sum(1 for n in cited if n in nodes)
    print("\nsnapshot: %s at %s, %d events, %d nodes (%d archived, excluded)"
          % (snap.get("source", "?"), snap.get("head") or "(unknown)",
             snap.get("events", 0), total, len(all_nodes) - total))
    print("explicitly annotated: %d of %d nodes" % (accounted, total))
    print("PROBLEMS: %d" % problems)
    return problems


def refresh(path, cited):
    fresh = read_ledger(path)
    old = json.load(io.open(SNAPSHOT, encoding="utf-8")) if os.path.exists(SNAPSHOT) else {"nodes": {}}
    on, nn = old.get("nodes", {}), fresh["nodes"]

    added = sorted(set(nn) - set(on))
    removed = sorted(set(on) - set(nn))
    changed = sorted(k for k in set(on) & set(nn) if on[k] != nn[k])

    print("ledger %s: %d events, %d nodes" % (fresh["head"] or "?", fresh["events"], len(nn)))
    print("added %d, removed %d, changed %d" % (len(added), len(removed), len(changed)))
    flagged = [k for k in added + removed + changed if k in cited]
    if flagged:
        print("\nOf those, %d are cited by the blueprint and need a human look:" % len(flagged))
        for k in sorted(flagged, key=lambda s: [int(x) for x in s.split(".")]):
            what = "added" if k in added else "removed" if k in removed else "changed"
            was, now = on.get(k, {}), nn.get(k, {})
            detail = ""
            if what == "changed":
                diffs = [f for f in ("state", "challenges", "amended", "archived", "taint", "deps",
                                  "statement_sha256")
                         if was.get(f) != now.get(f)]
                detail = " (" + ", ".join(diffs) + ")"
            print("   %-12s %-8s%s  cited by %s" % (k, what, detail, ", ".join(cited[k])))
    else:
        print("\nNothing the blueprint cites has changed.")

    io.open(SNAPSHOT, "w", encoding="utf-8").write(
        json.dumps(fresh, indent=1, sort_keys=True) + "\n")
    print("\nwrote %s" % os.path.relpath(SNAPSHOT, HERE))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ledger", metavar="PATH",
                    help="clone of vidick/mipre-proof; refresh the snapshot from it")
    args = ap.parse_args()
    cited = read_blueprint()
    if args.ledger:
        sys.exit(refresh(args.ledger, cited))
    sys.exit(1 if check(load_snapshot(), cited) else 0)


if __name__ == "__main__":
    main()
