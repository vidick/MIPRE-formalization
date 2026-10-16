#!/usr/bin/env python3
"""Replace a wholesale `import Mathlib` in the workspace copy of a vendored module by the explicit
Mathlib modules its declarations use, plus `Mathlib.Tactic`.

Usage:
  P2M_DIR=<dir> python3 prove2me/tools/ws_rewrite_imports.py --from-lean min_imports.out
      turn the `MODULE <module> <mathlib module>` lines of tools/min_imports.lean (run in the main
      repository) into <P2M_DIR>/minimports.json
  P2M_DIR=<dir> python3 prove2me/tools/ws_rewrite_imports.py
      rewrite every workspace module listed in minimports.json that still imports Mathlib wholesale;
      give every other listed module that has not compiled yet its constants' Mathlib modules as
      explicit imports (a module downstream of a wholesale importer relied on it transitively); add
      the modules of the namespaces an uncompiled rewritten module opens (NAMESPACE_MODULES)

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
          "Mathlib.Basic.Unique": "Mathlib.Logic.Unique", "Mathlib.Topology.Algebra.Group.ContinuousDiv": "Mathlib.Topology.Algebra.Group.Basic",
          # found by the low-degree-test lists (2026-10-16): the constants named sit in these modules at the platform pin
          "Mathlib.Basic.ENNReal.Operations": "Mathlib.Data.ENNReal.Operations", "Mathlib.Basic.ENNReal.Real": "Mathlib.Data.ENNReal.Real",
          "Mathlib.Basic.IsEmpty.Basic": "Mathlib.Logic.IsEmpty.Basic", "Mathlib.MeasureTheory.Measure.Dirac.Def": "Mathlib.MeasureTheory.Measure.Dirac",
          "Mathlib.MeasureTheory.Measure.Module": "Mathlib.MeasureTheory.Measure.MeasureSpace"}
DROP = {"Mathlib.RingTheory.Coalgebra.IsFrobenius"}   # an instance the newer typeclass search found; never named in the sources
# A namespace a module opens (`open scoped MatrixOrder`, `open WithLp`) is not a constant reference, so the
# proof-level lists miss the Mathlib module that declares it when no constant of that module is used:
# the two vendored low-degree-test modules that open these failed with "unknown namespace" (2026-10-16).
# Namespace -> the platform-pin module declaring it (its `scoped[...]` instances or its `namespace`).
NAMESPACE_MODULES = {"MatrixOrder": "Mathlib.Analysis.Matrix.Order", "Matrix.Norms.L2Operator": "Mathlib.Analysis.Matrix.Order",
                     "Matrix.Norms.Elementwise": "Mathlib.Analysis.Matrix.Normed", "WithLp": "Mathlib.Analysis.Normed.Lp.WithLp"}
OPEN_RE = re.compile(r"^open(?:\s+scoped)?\s+([^\n]+)$", re.M)

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
# a module downstream of a wholesale importer relied on that import transitively (the vendored
# low-degree test's `FiniteMatrix.Order` names `ProperCone`, which only `import Mathlib` brought in),
# so every module listed in minimports.json that has not compiled yet gets its own constants' Mathlib
# modules as explicit imports, added after its last import line; a module that compiled is left alone
explicit = 0
for mod, mods in d["per_module"].items():
    path = f"{WS}/{mod.replace('.', '/')}.lean"
    olean = f"{WS}/.lake/build/lib/lean/{mod.replace('.', '/')}.olean"
    if not os.path.exists(path) or (os.path.exists(olean) and os.path.getmtime(olean) > os.path.getmtime(path)):
        continue
    t = open(path, encoding="utf-8").read()
    if re.search(r"^(public\s+)?import Mathlib\s*$", t, re.M):
        continue   # a wholesale importer is handled above
    have = set(re.findall(r"^(?:public\s+)?import\s+(\S+)", t, re.M))
    need = sorted({RENAME.get(m, m) for m in mods if m not in DROP} - have)
    if not need:
        continue
    assert all(os.path.exists(f"{root}/{m.replace('.', '/')}.lean") for m in need), (mod, [m for m in need if not os.path.exists(f"{root}/{m.replace('.', '/')}.lean")])
    last = list(re.finditer(r"^(?:public\s+)?import\s+\S+\s*$", t, re.M))[-1]
    t = t[:last.end()] + "".join(f"\nimport {m}" for m in need) + t[last.end():]
    open(path, "w", encoding="utf-8").write(t)
    record[mod] = sorted(set(record.get(mod, [])) | set(need)); explicit += 1

# second pass, over every rewritten module: the modules of the namespaces it opens
added = 0
for mod in list(record):
    path = f"{WS}/{mod.replace('.', '/')}.lean"
    olean = f"{WS}/.lake/build/lib/lean/{mod.replace('.', '/')}.olean"
    if not os.path.exists(path) or (os.path.exists(olean) and os.path.getmtime(olean) > os.path.getmtime(path)):
        continue   # a module that compiled has every namespace it opens
    t = open(path, encoding="utf-8").read()
    opened = {ns for m in OPEN_RE.finditer(t) for ns in m.group(1).split()}
    have = set(re.findall(r"^(?:public\s+)?import\s+(\S+)", t, re.M))
    need = sorted({NAMESPACE_MODULES[ns] for ns in opened if ns in NAMESPACE_MODULES} - have)
    if not need:
        continue
    assert all(os.path.exists(f"{root}/{m.replace('.', '/')}.lean") for m in need), (mod, need)
    last = list(re.finditer(r"^(?:public\s+)?import\s+Mathlib\.\S+\s*$", t, re.M))[-1]
    t = t[:last.end()] + "".join(f"\nimport {m}" for m in need) + t[last.end():]
    open(path, "w", encoding="utf-8").write(t)
    record[mod] = sorted(set(record[mod]) | set(need)); added += len(need)
json.dump(record, open(rec_path, "w"), indent=1)
print(f"rewrote {done} wholesale importers, {explicit} downstream modules given explicit imports, skipped {skipped} not in the workspace, {len(record)} recorded; {added} namespace import(s) added")
