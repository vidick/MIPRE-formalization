#!/usr/bin/env python3
"""Merge and check the writers' metadata batches into prove2me/metadata.json."""
import argparse, json, re, sys, os, glob

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
ap = argparse.ArgumentParser(description="merge meta_out_*.json writer packets into metadata.json")
ap.add_argument("out", nargs="?", default=None, help="output path (default: <tree dir>/metadata.json)")
ap.add_argument("--tree", default=None, help="tree directory holding tree.json, glue.json and the meta_out_* files "
                "(default: the P2M_CONFIG tree directory, else the p2m scratch directory)")
args = ap.parse_args()
# with P2M_CONFIG: the tree directory's tree.json (+ glue.json items) and meta_out_* packets
CFG = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8")) if os.environ.get("P2M_CONFIG") else None
A = args.tree if args.tree else (os.path.dirname(CFG["tree_out"]) if CFG else S)
OUT = args.out if args.out else f"{A}/metadata.json"
tree = json.load(open(f"{A}/tree.json", encoding="utf-8"))
if os.path.exists(f"{A}/glue.json"):
    for g in json.load(open(f"{A}/glue.json", encoding="utf-8"))["items"]:
        tree["nodes"].append({"theorem_name": g["theorem_name"]})
TAGS = {"computability", "complexity-theory", "turing-machines", "polynomial-time", "undecidability",
        "recursive-compression", "universal-machine", "kleene-recursion", "smn-theorem", "cost-model",
        "self-interpreter", "succinct-descriptions", "mip-re",
        # the assembly layer
        "nonlocal-games", "quantum-information", "interactive-proofs", "halting-problem", "verifiers",
        "gap-compression", "game-value", "synchronous-games", "entangled-strategies", "bit-strings",
        "list-programs", "binary-arithmetic", "semidecidability", "tabulation", "pcc-strategies"}

def check_text(label, t, minlen=120, maxlen=2500):
    probs = []
    if not isinstance(t, str) or len(t) < minlen:
        probs.append(f"{label}: too short ({len(t) if isinstance(t, str) else t})")
        return probs
    if len(t) > maxlen:
        probs.append(f"{label}: too long ({len(t)} > {maxlen})")
    if t.count("$") % 2:
        probs.append(f"{label}: odd number of $")
    if re.search(r"\\\\[a-zA-Z]", t):
        probs.append(f"{label}: double backslash before a command (over-escaped?)")
    if "sorry" in t:
        probs.append(f"{label}: contains 'sorry'")
    if re.search(r"\b(elegant|clever|trick)\b", t, re.I):
        probs.append(f"{label}: forbidden adjective")
    return probs

nodes_out, problems = [], []
by_name = {}
for f in sorted(glob.glob(f"{A}/meta_out_[0-9]*.json")):
    for o in json.load(open(f, encoding="utf-8")):
        by_name[o["theorem_name"]] = o
for n in tree["nodes"]:
    name = n["theorem_name"]
    o = by_name.get(name)
    if not o:
        problems.append(f"missing node metadata: {name}")
        continue
    for k in ("theorem_title", "natural_language_statement", "source", "tags", "explanation"):
        if k not in o:
            problems.append(f"{name}: missing {k}")
    if len(o.get("theorem_title", "")) > 200 or len(o.get("theorem_title", "")) < 10:
        problems.append(f"{name}: title length {len(o.get('theorem_title',''))}")
    problems += check_text(f"{name}.statement", o.get("natural_language_statement", ""))
    problems += check_text(f"{name}.explanation", o.get("explanation", ""), 80, 50000)
    if "**Formalization Note**" not in o.get("natural_language_statement", ""):
        problems.append(f"{name}: no Formalization Note")
    if "$$" not in o.get("natural_language_statement", ""):
        problems.append(f"{name}: no display-math block")
    bad = [t for t in o.get("tags", []) if t not in TAGS]
    if bad or not o.get("tags"):
        problems.append(f"{name}: tags {o.get('tags')}")
    if "github.com/vidick/MIPRE-formalization/blob/70cbf1c" not in o.get("source", ""):
        problems.append(f"{name}: source lacks the blob link")
    if len(o.get("explanation", "")) > 50000:
        problems.append(f"{name}: explanation over 50k")
    for k in ("natural_language_statement", "explanation"):
        o[k] = o[k].replace("**Formalization Note.**", "**Formalization Note**")
    nodes_out.append({"theorem_name": name, "theorem_title": o["theorem_title"],
                      "natural_language_statement": o["natural_language_statement"],
                      "source": o["source"], "tags": sorted(set(o["tags"])), "explanation": o["explanation"]})

bundles_out = []
bb = {}
for f in sorted(glob.glob(f"{A}/meta_out_bundles*.json")):
    for o in json.load(open(f, encoding="utf-8")):
        bb[o["definition_name"]] = o
for b in tree["bundles"]:
    name = b["definition_name"]
    o = bb.get(name)
    if not o:
        problems.append(f"missing bundle metadata: {name}")
        continue
    for k in ("definition_title", "natural_language_statement", "source", "tags"):
        if k not in o:
            problems.append(f"{name}: missing {k}")
    problems += check_text(f"{name}.statement", o.get("natural_language_statement", ""))
    if len(o.get("definition_title", "")) > 200 or len(o.get("definition_title", "")) < 10:
        problems.append(f"{name}: title length {len(o.get('definition_title',''))}")
    if "**Formalization Note**" not in o.get("natural_language_statement", "").replace("**Formalization Note.**", "**Formalization Note**"):
        problems.append(f"{name}: no Formalization Note")
    bad = [t for t in o.get("tags", []) if t not in TAGS]
    if bad or not o.get("tags"):
        problems.append(f"{name}: tags {o.get('tags')}")
    o["natural_language_statement"] = o["natural_language_statement"].replace("**Formalization Note.**", "**Formalization Note**")
    bundles_out.append({"definition_name": name, "definition_title": o["definition_title"],
                        "natural_language_statement": o["natural_language_statement"],
                        "source": o["source"], "tags": sorted(set(o["tags"]))})

print(f"nodes {len(nodes_out)}/{len(tree['nodes'])}, bundles {len(bundles_out)}/{len(tree['bundles'])}, problems {len(problems)}")
for p in problems:
    print("  -", p)
json.dump({"nodes": nodes_out, "bundles": bundles_out}, open(OUT, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
print("wrote", OUT)
