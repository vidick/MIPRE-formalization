#!/usr/bin/env python3
"""Leaf closures: the solution of a `Nonempty (…)` leaf whose statement is already on the platform.

    P2M_CONFIG=prove2me/<tree>/config.json python3 prove2me/tools/glue_leaves.py

The config's ``glue_leaves`` lists ``{"theorem_name", "statement", "proof", "constants"}``: the
published leaf, its statement (as the stub states it), the one-line proof, and the constants the
proof names, whose bundles (this tree's or a published one) the solution imports.  Writes
``Solutions/Sol_<slug>.lean`` and ``<tree dir>/glue.json`` (items of kind ``leaf-closure`` with
``stub_published`` set, which the uploader resolves by name).
"""
import json, os, re, sys

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
CFG = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8"))
A = os.path.dirname(CFG["tree_out"])
tree = json.load(open(CFG["tree_out"], encoding="utf-8"))
plan = json.load(open(CFG["out"], encoding="utf-8"))
HEADER = "/-\nCopyright (c) 2026 Thomas Vidick. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Thomas Vidick\n-/\n"

def slug(name):
    return re.sub(r"[^A-Za-z0-9_]", "_", name)

# constant -> module (this tree's plan), module -> bundle (this tree, then the published trees)
const_module = {u["name"]: u["module"] for u in plan["units"].values() if u.get("name")}
module_bundle = {b["module"]: b["definition_name"] for b in tree["bundles"]}
for path in ([CFG["published_tree"]] if CFG.get("published_tree") else []) + list(CFG.get("published_trees", [])):
    pt = json.load(open(path, encoding="utf-8"))
    for b in pt["bundles"]:
        module_bundle.setdefault(b["module"], b["definition_name"])
    pp = os.path.join(os.path.dirname(path), "plan.json")
    if os.path.exists(pp):
        for u in json.load(open(pp, encoding="utf-8"))["units"].values():
            if u.get("name"):
                const_module.setdefault(u["name"], u["module"])

items, generated = [], []
for leaf in CFG.get("glue_leaves", []):
    name = leaf["theorem_name"]
    imports = []
    for c in leaf["constants"]:
        m = const_module.get(c)
        if not m:
            sys.exit(f"glue_leaves: constant {c} is not in this tree's plan nor in a published one")
        b = module_bundle.get(m)
        if not b:
            sys.exit(f"glue_leaves: module {m} of {c} has no bundle")
        imports.append(f"import Definitions.Def_{b}")
    # the delta bundles of those modules too (a declaration may live in the `_B` addition)
    for b in tree["bundles"]:
        if b.get("published_bundle") and f"import Definitions.Def_{b['published_bundle']}" in imports:
            imports.append(f"import Definitions.Def_{b['definition_name']}")
    imports = sorted(set(imports))
    sol = (HEADER + f"-- Prove2Me leaf closure: the witness of {name}, a `Nonempty` leaf whose statement is on the platform.\n"
           + "\n".join(imports) + "\n\n" + f"theorem solution : {leaf['statement']} :=\n  {leaf['proof']}\n")
    rel = f"Solutions/Sol_{slug(name)}.lean"
    os.makedirs(os.path.dirname(os.path.join(WS, rel)), exist_ok=True)
    if not (os.path.exists(os.path.join(WS, rel)) and open(os.path.join(WS, rel), encoding="utf-8").read() == sol):
        open(os.path.join(WS, rel), "w", encoding="utf-8").write(sol)
    generated.append(rel)
    items.append({"theorem_name": name, "slug": slug(name), "kind": "leaf-closure",
                  "formal_statement": f"theorem {name} : {leaf['statement']} := by sorry", "preamble": "\n".join(imports),
                  "stub_file": None, "stub_published": True, "solution_file": rel, "imported_nodes": [],
                  "source": leaf.get("source", {}), "witness": leaf["proof"]})
gp = os.path.join(A, "glue.json")
prev = json.load(open(gp, encoding="utf-8")) if os.path.exists(gp) else {"items": [], "generated": []}
keep = [it for it in prev["items"] if it["kind"] != "leaf-closure"]
json.dump({"items": keep + items, "generated": sorted(set([g for g in prev["generated"] if "leaf" not in g] + generated))},
          open(gp, "w", encoding="utf-8"), indent=1)
print(f"glue_leaves: {len(items)} leaf closure(s) -> {gp}; files {generated}")
