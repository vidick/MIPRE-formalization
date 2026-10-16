#!/usr/bin/env python3
"""Add the import closure of the given root modules, at the pinned commit, to the p2m workspace.

Usage: P2M_DIR=<dir> python3 prove2me/tools/ws_extend.py [--rev 70cbf1c] <root module> ...

Writes or updates <P2M_DIR>/ws/MIPRE/**.lean from `git cat-file` at the commit (a file already
identical is left alone, so oleans stay valid), appends the roots to ws/MIPRE.lean, which lists
every root ever added, and writes <P2M_DIR>/closure_<Root>.json with the closure and the Mathlib
imports lacking an olean.  Vendored modules importing Mathlib wholesale are rewritten afterwards by
ws_rewrite_imports.py."""
import subprocess, re, os, sys, json, argparse

ap = argparse.ArgumentParser()
ap.add_argument("--rev", default="70cbf1c")
ap.add_argument("roots", nargs="+")
args = ap.parse_args()
S = os.environ.get("P2M_DIR") or sys.exit("set P2M_DIR to the p2m scratch directory")
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
rev, roots = args.rev, args.roots
files = subprocess.check_output(["git", "-C", REPO, "ls-tree", "-r", "--name-only", rev, "MIPRE"], text=True).split()
mods = {f[:-5].replace("/", "."): f for f in files if f.endswith(".lean")}
out = subprocess.run(["git", "-C", REPO, "cat-file", "--batch"], input="\n".join(f"{rev}:{p}" for p in mods.values()).encode(),
                     capture_output=True).stdout
raw, pos = {}, 0
for m in mods:
    e = out.index(b"\n", pos); size = int(out[pos:e].split()[2]); raw[m] = out[e + 1:e + 1 + size]; pos = e + 1 + size + 1
imp_re = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", re.M)
imports = {m: imp_re.findall(raw[m].decode("utf-8", "replace")) for m in mods}
seen, stack = set(), list(roots)
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m); stack.extend(i for i in imports[m] if i in mods)
closure = sorted(seen)
new = 0
for m in closure:
    dst = os.path.join(S, "ws", mods[m]); os.makedirs(os.path.dirname(dst), exist_ok=True)
    if not (os.path.exists(dst) and open(dst, "rb").read() == raw[m]):
        open(dst, "wb").write(raw[m]); new += 1
rootfile = os.path.join(S, "ws/MIPRE.lean")
old_roots = [l.split()[1] for l in open(rootfile).read().splitlines() if l.startswith("import ")] if os.path.exists(rootfile) else []
all_roots = old_roots + [r for r in roots if r not in old_roots]
open(rootfile, "w").write("".join(f"import {r}\n" for r in all_roots))
mathlib = sorted({i for m in closure for i in imports[m] if i.startswith("Mathlib")})
lib = os.path.join(S, "ws/.lake/packages/mathlib/.lake/build/lib/lean")
missing = [i for i in mathlib if not os.path.exists(os.path.join(lib, i.replace(".", "/") + ".olean"))]
json.dump({"roots": roots, "closure": closure, "missing_mathlib": missing},
          open(os.path.join(S, f"closure_{roots[0].split('.')[-1]}.json"), "w"), indent=1)
nl = sum(raw[m].count(b"\n") for m in closure)
print(f"closure {len(closure)} modules, {nl:,} lines; files written/updated {new}; roots in MIPRE.lean {len(all_roots)}; "
      f"Mathlib imports {len(mathlib)}, without oleans {len(missing)}: {missing[:5]}")
