#!/usr/bin/env python3
"""Phase 5: pretty-print the elaborated type of every uploaded statement in the original tree, in
the stub tree and in its solution, and diff.  Also records the axioms of every solution.

    P2M_CONFIG=prove2me/assembly/config.json python3 prove2me/tools/validate.py [--jobs 4]

The original type is read from the node's source module (the workspace holds the source closure),
under the declaration's source name (one node is renamed for the platform: `classV_game_μ`).  Glue
items (``<tree dir>/glue.json``) are checked too: a conditional or unconditional glue theorem keeps
its source statement, so all three types must agree; a leaf (`Nonempty (MIPRE.Introspection 7)`)
has no source declaration and no solution, so only its stub is recorded.  Every solution may
depend on `sorryAx` locally, since the stubs it imports are `sorry`; any axiom outside
`propext`, `Classical.choice`, `Quot.sound` and `sorryAx` is reported.
"""
import argparse, os, json, subprocess, re
from concurrent.futures import ThreadPoolExecutor

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
TOOLCHAIN = f"{S}/toolchain/bin"
CFG = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8")) if os.environ.get("P2M_CONFIG") else {}
TREE = CFG.get("tree_out", f"{S}/tree.json")
A = os.path.dirname(TREE)
VOUT = os.path.join(A, "validation.json")
ap = argparse.ArgumentParser()
ap.add_argument("--jobs", type=int, default=4)
args = ap.parse_args()

tree = json.load(open(TREE, encoding="utf-8"))
glue = json.load(open(os.path.join(A, "glue.json"), encoding="utf-8"))["items"] if os.path.exists(os.path.join(A, "glue.json")) else []
os.makedirs(f"{WS}/Check", exist_ok=True)
env = dict(os.environ, PATH=TOOLCHAIN + ":" + os.environ["PATH"])
OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound", "sorryAx"}

def module_of_path(p):
    return p[:-5].replace("/", ".")

# the items: (platform name, source name or None, source module or None, slug, has solution)
items = []
for n in tree["nodes"]:
    items.append({"name": n["theorem_name"], "source_name": n.get("source_name", n["theorem_name"]),
                  "module": n["module"], "slug": n["slug"], "solution": n["solution_file"] is not None, "kind": "node"})
for g in glue:
    # a leaf (`Nonempty (MIPRE.Introspection 7)`) and a leaf closure (its later solution) have no source
    # declaration: the statement is synthetic, so only stub and solution are compared
    synthetic = g["kind"] in ("leaf", "leaf-closure")
    items.append({"name": g["theorem_name"], "source_name": None if synthetic else g["theorem_name"],
                  "module": None if synthetic else module_of_path(g["source"]["file"]),
                  "slug": g["slug"], "solution": g.get("solution_file") is not None, "kind": "glue-" + g["kind"]})

PP = '''
open Lean Meta in
def ppType (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let f ← ppExpr ci.type
  return f.pretty 100000
'''

def run_lean(path):
    r = subprocess.run(["lake", "env", "lean", path], cwd=WS, env=env, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr

def write_check(name, imports, pairs):
    # one `run_meta` block per 40 names: a single block of 500 statements exceeds the elaborator's
    # recursion depth (the repetition tree has 515 nodes)
    body = "\n".join(f"import {i}" for i in imports) + "\n" + PP
    for k in range(0, len(pairs), 40):
        body += "\nrun_meta do\n"
        for (n, lab) in pairs[k:k + 40]:
            body += f'  IO.println s!"{lab} :: {{← ppType `{n}}}"\n'
    open(f"{WS}/Check/{name}.lean", "w", encoding="utf-8").write(body)
    return f"Check/{name}.lean"

def parse(out):
    """`label :: type` lines; a type the pretty-printer breaks over several lines is joined back."""
    d, cur = {}, None
    for l in out.splitlines():
        if " :: " in l and not l.startswith(" "):
            cur, t = l.split(" :: ", 1)
            d[cur] = t
        elif cur is not None and l.startswith(" "):
            d[cur] += "\n" + l
    return d

# original tree: the source modules of the items that have a source declaration.  A source module
# outside the workspace (the glue theorems live in `MIPRE/Background/Pipeline.lean` and
# `MIPRE/MainTheorem.lean`, which depend on the vendored trees) cannot be elaborated here; those
# statements are verbatim textual cuts of the source (glue.py), and are checked as text below.
def in_workspace(module):
    return os.path.exists(f"{WS}/.lake/build/lib/lean/{module.replace('.', '/')}.olean")
with_src = [it for it in items if it["source_name"] and in_workspace(it["module"])]
textual = [it for it in items if it["source_name"] and not in_workspace(it["module"])]
p = write_check("Orig", sorted({it["module"] for it in with_src}), [(it["source_name"], it["name"]) for it in with_src])
rc, out = run_lean(p)
orig = parse(out)
# a field another project published under a different name is renamed in the generated copies
# (config `token_renames`); the source's types are read with the same renaming
for o, n in CFG.get("token_renames", {}).items():
    orig = {k: re.sub(r"(?<![\w'])" + re.escape(o) + r"(?![\w'])", n, v) for k, v in orig.items()}
print("original tree:", rc, len(orig), "types of", len(with_src))
if rc != 0:
    print(out[:3000])
# textual check of the glue statements against the source at the pinned commit
COMMIT = "70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed"
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
def source_head(path, short):
    src = subprocess.run(["git", "show", f"{COMMIT}:{path}"], cwd=REPO, capture_output=True, text=True).stdout
    m = re.search(r"^theorem " + re.escape(short) + r"\b(.*?):=", src, re.S | re.M)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else None
glue_by_name = {g["theorem_name"]: g for g in glue}
text_bad = 0
for it in textual:
    g = glue_by_name[it["name"]]
    head = source_head(g["source"]["file"], it["name"].split(".")[-1])
    stub_head = re.sub(r"\s+", " ", g["formal_statement"].split(":= by sorry")[0]).strip()
    ok = head is not None and head in stub_head
    text_bad += 0 if ok else 1
    print(("textual OK  " if ok else "TEXTUAL DIFFERS") + f" {it['name']} (source {g['source']['file']}, not in the workspace)")
    if not ok:
        print("  source:", head)
        print("  stub  :", stub_head)
# stub tree
p = write_check("Stubs", [f"Theorems.Thm_{it['slug']}" for it in items], [(it["name"], it["name"]) for it in items])
rc, out = run_lean(p)
stubs = parse(out)
print("stub tree:", rc, len(stubs), "types of", len(items))
if rc != 0:
    print(out[:3000])
bad = 0
for it in with_src:
    if orig.get(it["name"]) != stubs.get(it["name"]):
        bad += 1
        print("STUB TYPE DIFFERS:", it["name"])
        print("  orig:", orig.get(it["name"]))
        print("  stub:", stubs.get(it["name"]))
print("stub types identical to the original:", len(with_src) - bad, "of", len(with_src))
for it in items:
    if not it["source_name"]:
        print("leaf (no source declaration):", it["name"], "::", stubs.get(it["name"]))

# solutions: one run each (every solution declares `solution`)
def check_solution(it):
    body = (f"import Solutions.Sol_{it['slug']}\n" + PP +
            '\nrun_meta do\n  IO.println s!"T :: {← ppType `solution}"\n'
            '#print axioms solution\n')
    path = f"Check/Sol_{it['slug']}.lean"
    open(f"{WS}/{path}", "w", encoding="utf-8").write(body)
    rc, out = run_lean(path)
    t = list(parse("\n".join(l for l in out.splitlines() if l.startswith("T :: ") or l.startswith(" "))).values())
    ax = re.search(r"'solution' depends on axioms: \[([^\]]*)\]", out)
    if ax:
        axs = ax.group(1)
    elif "'solution' does not depend on any axioms" in out:
        axs = ""
    else:
        axs = out.strip()[-300:]   # the check itself failed: reported as an unexpected "axiom"
    return it, rc, t[0] if t else None, axs, out

sol_items = [it for it in items if it["solution"]]
sol_bad, axioms, extra = 0, {}, []
with ThreadPoolExecutor(max_workers=args.jobs) as ex:
    for it, rc, t, ax, out in ex.map(check_solution, sol_items):
        axioms[it["name"]] = ax
        if rc != 0 or t is None or t != stubs.get(it["name"]):
            sol_bad += 1
            print("SOLUTION TYPE DIFFERS / FAILED:", it["name"], rc)
            print("  stub:", stubs.get(it["name"]))
            print("  sol :", t if t else out[:500])
        used = {a.strip() for a in ax.split(",") if a.strip()}
        if not used <= OK_AXIOMS:
            extra.append((it["name"], sorted(used - OK_AXIOMS)))
print("solution types identical to the stub:", len(sol_items) - sol_bad, "of", len(sol_items))
print("axioms outside {propext, Classical.choice, Quot.sound, sorryAx}:", extra or "none")
json.dump({"orig": orig, "stubs": stubs, "axioms": axioms, "stub_mismatch": bad, "solution_mismatch": sol_bad,
           "textual_mismatch": text_bad, "textual_checked": [it["name"] for it in textual],
           "extra_axioms": extra}, open(VOUT, "w", encoding="utf-8"), indent=1)
