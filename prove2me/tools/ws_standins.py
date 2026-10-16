#!/usr/bin/env python3
"""Write the workspace stand-ins of platform items another project published, which this tree imports
but never uploads: a definition bundle's Lean text and a theorem's preamble plus formal statement, as
the platform serves them.  They let build_tree.py and validate.py compile the generated files locally.

    P2M_DIR=<dir> python3 prove2me/tools/ws_standins.py <tree dir>/platform-imports.json <records.json>

`records.json` maps each item (definition name or theorem name) to the platform record
(`definition` for a bundle; `preamble` and `formal_statement` for a theorem).  Prints the module
names to compile with tools/compile_modules.py."""
import json, os, re, sys
S = os.environ.get("P2M_DIR") or sys.exit("set P2M_DIR")
imports, records = json.load(open(sys.argv[1], encoding="utf-8")), json.load(open(sys.argv[2], encoding="utf-8"))
ws = f"{S}/ws"
mods = []
b = imports["bundle"]
txt = records[b]["definition"]
open(f"{ws}/Definitions/Def_{b}.lean", "w", encoding="utf-8").write(txt if txt.endswith("\n") else txt + "\n")
mods.append(f"Definitions.Def_{b}")
for name, slug in imports["theorems"].items():
    rec = records[name]
    stmt = rec["formal_statement"].rstrip()
    if not re.search(r":=\s*by\s+sorry\s*$", stmt):
        stmt = re.sub(r":=\s*$", "", stmt).rstrip() + " := by sorry"
    open(f"{ws}/Theorems/Thm_{slug}.lean", "w", encoding="utf-8").write(rec["preamble"].rstrip() + "\n\n" + stmt + "\n")
    mods.append(f"Theorems.Thm_{slug}")
print(" ".join(mods))
