#!/usr/bin/env python3
"""Writer packets for the metadata of a tree: everything a writer needs to draft a title, a
natural-language statement, a source line, tags and (for theorems) an explanation, for each node,
glue item and bundle, in batches.

    P2M_CONFIG=prove2me/assembly/config.json python3 prove2me/tools/meta_packets.py [--batch-size 20]

Writes ``<tree dir>/meta_packets/batch_<k>.json`` (nodes and glue items) and
``bundles_<k>.json`` (bundles).  Each packet item carries the Lean statement or the bundle's kept
declarations, the docstring and module docstring, the source path and lines at the source commit,
the blueprint labels whose ``\\lean{}`` lists the declaration, and what the proof imports.
"""
import argparse, glob, json, os, re

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CFG = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8"))
A = os.path.dirname(CFG["tree_out"])
WS = f"{S}/ws"
COMMIT = "70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed"

ap = argparse.ArgumentParser()
ap.add_argument("--batch-size", type=int, default=20)
ap.add_argument("--out", default=None, help="directory for the packets (default: <tree dir>/meta_packets)")
args = ap.parse_args()
OUT = args.out or os.path.join(REPO, "prove2me", os.path.basename(A), "meta_packets")
os.makedirs(OUT, exist_ok=True)

tree = json.load(open(CFG["tree_out"], encoding="utf-8"))
plan = json.load(open(CFG["out"], encoding="utf-8"))
glue = json.load(open(os.path.join(A, "glue.json"), encoding="utf-8"))["items"] if os.path.exists(os.path.join(A, "glue.json")) else []
units_by_name = {u["name"]: u for u in plan["units"].values() if u["name"]}

# blueprint labels per declaration
labels = {}
for f in sorted(glob.glob(f"{REPO}/blueprint/src/content/*.tex")):
    t = open(f, encoding="utf-8").read()
    for m in re.finditer(r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}", t, re.S):
        body = m.group(3)
        lab = re.search(r"\\label\{([^}]*)\}", body)
        lean = re.search(r"\\lean\{([^}]*)\}", body, re.S)
        if not lab or not lean:
            continue
        title = (m.group(2) or "").strip()
        for n in re.sub(r"\s+", "", lean.group(1)).split(","):
            if n:
                labels.setdefault(n, []).append({"label": lab.group(1), "env": m.group(1), "title": title, "file": os.path.basename(f)})

def module_doc(module):
    for b in tree["bundles"]:
        if b["module"] == module and b.get("moduleDoc"):
            return b["moduleDoc"][:3000]
    src = f"{WS}/{module.replace('.', '/')}.lean"
    if os.path.exists(src):
        t = open(src, encoding="utf-8").read()
        m = re.search(r"/-!(.*?)-/", t, re.S)
        return ("/-!" + m.group(1) + "-/")[:3000] if m else ""
    return ""

def blob(path, lines=None):
    url = f"https://github.com/vidick/MIPRE-formalization/blob/{COMMIT}/{path}"
    return url + (f"#L{lines[0]}-L{lines[1]}" if lines else "")

items = []
for n in tree["nodes"]:
    items.append({
        "kind": "theorem", "theorem_name": n["theorem_name"], "source_name": n.get("source_name", n["theorem_name"]),
        "formal_statement": n["formal_statement"], "preamble_opens": [l for l in n["preamble"].split("\n") if l.startswith(("open ", "variable "))],
        "docstring": n["docstring"], "module": n["module"], "module_doc": module_doc(n["module"]),
        "source": blob(n["source_path"], n["lines"]), "source_path": n["source_path"], "lines": n["lines"],
        "blueprint": labels.get(n.get("source_name", n["theorem_name"]), []),
        "imported_nodes": n["imported_nodes"], "pasted_helpers": len(n["pasted"]), "prooflines": n["prooflines"],
        "is_target": n["is_target"],
    })
for g in glue:
    items.append({
        "kind": "glue-" + g["kind"], "theorem_name": g["theorem_name"], "formal_statement": g["formal_statement"],
        "preamble_opens": [l for l in g["preamble"].split("\n") if l.startswith("open ")],
        "docstring": "", "module": None, "module_doc": "",
        "source": blob(g["source"]["file"], g["source"].get("lines")), "source_path": g["source"]["file"], "lines": g["source"].get("lines"),
        "witness": g.get("witness"), "blueprint": labels.get(g["theorem_name"], []),
        "imported_nodes": g["imported_nodes"], "stub_published": g.get("stub_published", False),
        "solution_file": g.get("solution_file"),
    })
bundles = []
for b in tree["bundles"]:
    kept = []
    for name in b["kept"]:
        u = units_by_name.get(name)
        kept.append({"name": name, "kind": u["kind"] if u else "?", "has_doc": bool(u and u["has_doc"]),
                     "lines": [u["decl"]["declStart"]["line"], u["decl"]["declEnd"]["line"]] if u else None})
    bundles.append({
        "kind": "bundle-" + b["kind"], "definition_name": b["definition_name"], "module": b["module"],
        "module_doc": b["moduleDoc"][:4000], "source": blob(b["source_path"]), "source_path": b["source_path"],
        "defmat": b["defmat"], "embedded": b["embedded"], "kept": kept, "lines": b["lines"],
        "published_bundle": b.get("published_bundle"), "imports": b["imports"],
        "blueprint": sorted({l["label"] for name in b["kept"] for l in labels.get(name, [])}),
        "defmat_docstrings": {name: (open(f"{WS}/{b['source_path']}", encoding="utf-8").read().split("\n")[units_by_name[name]["decl"]["docstring"]["start"]["line"] - 1: units_by_name[name]["decl"]["docstring"]["end"]["line"]]
                              if units_by_name.get(name) and units_by_name[name]["decl"]["docstring"] else None) for name in b["defmat"]},
    })

k = 0
for i in range(0, len(items), args.batch_size):
    json.dump(items[i:i + args.batch_size], open(f"{OUT}/batch_{k}.json", "w", encoding="utf-8"), indent=1, ensure_ascii=False); k += 1
j = 0
for i in range(0, len(bundles), args.batch_size):
    json.dump(bundles[i:i + args.batch_size], open(f"{OUT}/bundles_{j}.json", "w", encoding="utf-8"), indent=1, ensure_ascii=False); j += 1
print(f"{len(items)} theorem items in {k} packets, {len(bundles)} bundles in {j} packets -> {OUT}")
