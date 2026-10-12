#!/usr/bin/env python3
"""Phase 5: pretty-print the elaborated type of every node in the original tree, in the
stub tree and in each solution, and diff.  Also records the axioms of every solution."""
import os, json, subprocess, sys, re

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
TOOLCHAIN = f"{S}/toolchain/bin"
tree = json.load(open(f"{S}/tree.json"))
nodes = tree["nodes"]
os.makedirs(f"{WS}/Check", exist_ok=True)
env = dict(os.environ, PATH=TOOLCHAIN + ":" + os.environ["PATH"])

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

def write_check(name, imports, names, label):
    body = "\n".join(f"import {i}" for i in imports) + "\n" + PP + "\nrun_meta do\n"
    for (n, lab) in zip(names, label):
        body += f'  IO.println s!"{lab} :: {{← ppType `{n}}}"\n'
    open(f"{WS}/Check/{name}.lean", "w").write(body)
    return f"Check/{name}.lean"

names = [n["theorem_name"] for n in nodes]
# original tree
p = write_check("Orig", ["MIPRE"], names, names)
rc, out = run_lean(p)
orig = dict(l.split(" :: ", 1) for l in out.splitlines() if " :: " in l)
print("original tree:", rc, len(orig), "types")
if rc != 0:
    print(out[:3000])
# stub tree
p = write_check("Stubs", [f"Theorems.Thm_{n['slug']}" for n in nodes], names, names)
rc, out = run_lean(p)
stubs = dict(l.split(" :: ", 1) for l in out.splitlines() if " :: " in l)
print("stub tree:", rc, len(stubs), "types")
if rc != 0:
    print(out[:3000])
bad = 0
for n in names:
    if orig.get(n) != stubs.get(n):
        bad += 1
        print("STUB TYPE DIFFERS:", n)
        print("  orig:", orig.get(n))
        print("  stub:", stubs.get(n))
print("stub types identical to the original:", len(names) - bad, "of", len(names))
# solutions: one run each (every solution declares `solution`)
sol_bad, axioms = 0, {}
for n in nodes:
    body = (f"import Solutions.Sol_{n['slug']}\n" + PP +
            '\nrun_meta do\n  IO.println s!"T :: {← ppType `solution}"\n'
            '#print axioms solution\n')
    path = f"Check/Sol_{n['slug']}.lean"
    open(f"{WS}/{path}", "w").write(body)
    rc, out = run_lean(path)
    t = [l.split(" :: ", 1)[1] for l in out.splitlines() if l.startswith("T :: ")]
    ax = re.search(r"'solution' depends on axioms: \[([^\]]*)\]", out)
    axioms[n["theorem_name"]] = ax.group(1) if ax else out.strip()[-300:]
    if rc != 0 or not t or t[0] != stubs.get(n["theorem_name"]):
        sol_bad += 1
        print("SOLUTION TYPE DIFFERS / FAILED:", n["theorem_name"], rc)
        print("  stub:", stubs.get(n["theorem_name"]))
        print("  sol :", t[0] if t else out[:500])
print("solution types identical to the stub:", len(nodes) - sol_bad, "of", len(nodes))
print("axioms:")
for k, v in axioms.items():
    print(f"  {k}: {v}")
json.dump({"orig": orig, "stubs": stubs, "axioms": axioms}, open(f"{S}/validation.json", "w"), indent=1)
