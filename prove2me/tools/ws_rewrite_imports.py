#!/usr/bin/env python3
"""Replace a wholesale `import Mathlib` in the workspace copy of a vendored module by the explicit
Mathlib modules its declarations use, plus `Mathlib.Tactic`.

Usage:
  P2M_DIR=<dir> python3 prove2me/tools/ws_rewrite_imports.py --from-lean min_imports.out
      turn the `MODULE <module> <mathlib module>` lines of tools/min_imports.lean (run in the main
      repository) into <P2M_DIR>/minimports.json
  P2M_DIR=<dir> python3 prove2me/tools/ws_rewrite_imports.py
      rewrite every workspace module listed in minimports.json that still imports Mathlib wholesale

The lists come from the proof terms (min_imports.lean reads the `.olean.private` parts with
`value? (allowOpaque := true)`; statement-level lists left the vendored parts short of the lemmas
their proofs name).  Module names are the repository Mathlib's (`c55e6e7`) and are mapped to the
platform pin (`0df444a`) by RENAME; DROP holds modules the platform pin lacks whose constants the
sources never name.  Idempotent; records the rewrites in <P2M_DIR>/import_rewrites.json."""
import json, os, re, sys, argparse, collections

ap = argparse.ArgumentParser()
ap.add_argument("--from-lean", default=None, help="output of tools/min_imports.lean to turn into minimports.json")
args = ap.parse_args()
S = os.environ.get("P2M_DIR") or sys.exit("set P2M_DIR to the p2m scratch directory")
WS = f"{S}/ws"
MINI = f"{S}/minimports.json"

RENAME = {"Mathlib.Basic.ENNReal.Basic": "Mathlib.Data.ENNReal.Basic", "Mathlib.Basic.Logic.Basic": "Mathlib.Logic.Basic",
          "Mathlib.Algebra.Group.DivInvMonoid": "Mathlib.Algebra.Group.Defs", "Mathlib.Basic.Complex.Basic": "Mathlib.Data.Complex.Basic",
          "Mathlib.Basic.Nonempty": "Mathlib.Logic.Nonempty", "Mathlib.Basic.Real.Basic": "Mathlib.Data.Real.Basic",
          "Mathlib.Basic.Finite.Defs": "Mathlib.Data.Finite.Defs", "Mathlib.Basic.Real.Star": "Mathlib.Data.Real.Star",
          "Mathlib.Algebra.Group.Monoid": "Mathlib.Algebra.Group.Defs", "Mathlib.Algebra.Group.Semigroup": "Mathlib.Algebra.Group.Defs",
          # the repository's Mathlib (c55e6e7) has a Mathlib.Basic.* hierarchy the platform's (0df444a) lacks
          "Mathlib.Basic.Complex.BigOperators": "Mathlib.Data.Complex.BigOperators", "Mathlib.Basic.Countable.Defs": "Mathlib.Data.Countable.Defs",
          "Mathlib.Basic.ENNReal.BigOperators": "Mathlib.Data.ENNReal.BigOperators", "Mathlib.Basic.ENNReal.Holder": "Mathlib.Data.ENNReal.Holder",
          "Mathlib.Basic.ENNReal.Inv": "Mathlib.Data.ENNReal.Inv", "Mathlib.Basic.Finite.Prod": "Mathlib.Data.Finite.Prod",
          "Mathlib.Basic.Finite.Sigma": "Mathlib.Data.Finite.Sigma", "Mathlib.Basic.Finite.Sum": "Mathlib.Data.Finite.Sum",
          "Mathlib.Basic.IsEmpty.Defs": "Mathlib.Logic.IsEmpty.Defs", "Mathlib.Basic.NNReal.Defs": "Mathlib.Data.NNReal.Defs",
          "Mathlib.Basic.NNReal.Star": "Mathlib.Data.NNReal.Star", "Mathlib.Basic.Nontrivial.Defs": "Mathlib.Logic.Nontrivial.Defs",
          "Mathlib.Basic.Unique": "Mathlib.Logic.Unique", "Mathlib.Topology.Algebra.Group.ContinuousDiv": "Mathlib.Topology.Algebra.Group.Basic"}
DROP = {"Mathlib.RingTheory.Coalgebra.IsFrobenius"}   # an instance the newer typeclass search found; never named in the sources

root = f"{WS}/.lake/packages/mathlib"
if args.from_lean:
    per = collections.defaultdict(set)
    for line in open(args.from_lean, encoding="utf-8"):
        if line.startswith("MODULE "):
            _, mod, ml = line.split()
            per[mod].add(ml)
    allm = {m for v in per.values() for m in v}
    unknown = sorted(m for m in allm if m not in DROP and not os.path.exists(f"{root}/{RENAME.get(m, m).replace('.', '/')}.lean"))
    json.dump({"per_module": {k: sorted(v) for k, v in sorted(per.items())}, "unknown": unknown,
               "note": "proof-level lists from tools/min_imports.lean; repository Mathlib module names"},
              open(MINI, "w", encoding="utf-8"), indent=1)
    print(f"{len(per)} modules, {len(allm)} Mathlib modules named; unknown at the platform pin (extend RENAME or DROP): {unknown}")
    sys.exit(1 if unknown else 0)

d = json.load(open(MINI, encoding="utf-8"))
rec_path = f"{S}/import_rewrites.json"
record = json.load(open(rec_path)) if os.path.exists(rec_path) else {}
done, skipped = 0, 0
for mod, mods in d["per_module"].items():
    path = f"{WS}/{mod.replace('.', '/')}.lean"
    if not os.path.exists(path):
        skipped += 1; continue
    t = open(path, encoding="utf-8").read()
    if not re.search(r"^(public\s+)?import Mathlib\s*$", t, re.M):
        continue   # already rewritten
    new = sorted({RENAME.get(m, m) for m in mods if m not in DROP} | {"Mathlib.Tactic"})
    bad = [m for m in new if not os.path.exists(f"{root}/{m.replace('.', '/')}.lean")]
    assert not bad, (mod, bad)
    lines = "\n".join(f"import {m}" for m in new)
    t2, n = re.subn(r"^(public\s+)?import Mathlib\s*$", lambda mm: lines.replace("import ", (mm.group(1) or "") + "import "), t, count=1, flags=re.M)
    assert n == 1, mod
    open(path, "w", encoding="utf-8").write(t2)
    record[mod] = new; done += 1
json.dump(record, open(rec_path, "w"), indent=1)
print(f"rewrote {done} modules, skipped {skipped} not in the workspace, {len(record)} recorded")
