#!/usr/bin/env python3
"""Phase 3-4 of the Prove2Me full-project upload: generate the platform tree.

Definitions bundles by skeleton subtraction, Thm_ stubs and Sol_ files by context
reconstruction.  All positions are byte offsets from the Stage 2 facts; the only text
this script parses itself is the import header and the one-line `namespace`/`open`/
`variable` commands whose spans Stage 2 reports.
"""
import os, json, re, sys, collections, shutil

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
E, WS = f"{S}/extract", f"{S}/ws"
REPO = "vidick/MIPRE-formalization"
COMMIT = "70cbf1c"
COMMIT_FULL = None  # filled from git

plan = json.load(open(f"{S}/plan.json"))
U = plan["units"]
modules = plan["modules"]
bundles = set(plan["bundles"])
nodes = plan["nodes"]
comp = plan["composition"]
slugs = plan["slugs"]

def module_path(m):
    return m.replace(".", "/") + ".lean"

def mslug(m):
    return m.replace(".", "_")

# ---------- facts ----------
F = {}
for m in modules:
    base = m.split(".")[-1]
    d = collections.defaultdict(list)
    for l in open(f"{E}/sketch_info.{base}.jsonl", encoding="utf-8"):
        if l.strip():
            o = json.loads(l)
            d[o["kind"]].append(o)
    for k in d:
        d[k].sort(key=lambda o: (o["start"] if "start" in o else o["declStart"])["offset"])
    B = open(f"{WS}/{module_path(m)}", "rb").read()
    F[m] = {"cmds": d["cmd"], "decls": d["decl"], "refs": d["ref"], "B": B}

def txt(m, a, b):
    return F[m]["B"][a:b].decode("utf-8")

# all namespaces of the project (prefixes of declaration names)
rows = [json.loads(l) for l in open(f"{E}/decl_graph.jsonl", encoding="utf-8") if l.strip()]
NS = set()
for r in rows:
    parts = r["userName"].split(".")
    for i in range(1, len(parts)):
        NS.add(".".join(parts[:i]))

# ---------- scope map: context of every declaration command ----------
CTX = {}  # (module, declStart.offset) -> {"ns": [...], "opens": [...], "vars": [...]}
for m in modules:
    stack = []  # frames: {"name", "opens", "vars"}
    root = {"name": None, "opens": [], "vars": []}
    for c in F[m]["cmds"]:
        k = c["syntaxKind"].split(".")[-1]
        t = txt(m, c["start"]["offset"], c["end"]["offset"]).strip()
        if k == "namespace":
            stack.append({"name": t.split()[1], "opens": [], "vars": []})
        elif k == "end":
            if stack:
                stack.pop()
        elif k == "open":
            (stack[-1] if stack else root)["opens"].append(t)
        elif k == "variable":
            (stack[-1] if stack else root)["vars"].append(t)
        elif k in ("declaration", "in"):
            frames = [root] + stack
            CTX[(m, c["start"]["offset"])] = {
                "ns": [f["name"] for f in stack],
                "opens": [o for f in frames for o in f["opens"]],
                "vars": [v for f in frames for v in f["vars"]],
            }
        # moduleDoc, macro, export, eoi: no scope effect
    assert not stack, (m, stack)

def unit_ctx(uid):
    u = U[uid]
    return CTX[(u["module"], u["decl"]["declStart"]["offset"])]

def ns_of_chain(chain):
    return ".".join(chain)

def resolve_ns(name, chain):
    """Resolve a namespace name as written inside `chain` to its full name (project namespaces only)."""
    full = ns_of_chain(chain)
    prefixes = []
    parts = full.split(".") if full else []
    for i in range(len(parts), 0, -1):
        prefixes.append(".".join(parts[:i]))
    for p in prefixes:
        cand = f"{p}.{name}"
        if cand in NS:
            return cand
    if name in NS:
        return name
    return name  # a Mathlib/core namespace: keep as written

def resolve_open(open_text, chain):
    """Rewrite `open A B (x y)` for the top level."""
    body = open_text[len("open"):].strip()
    toks = re.findall(r"\([^)]*\)|\S+", body)
    out = []
    for tk in toks:
        out.append(tk if tk.startswith("(") else resolve_ns(tk, chain))
    return "open " + " ".join(out)

# ---------- imports ----------
imports = plan["imports"]
mod_closure = {m: set(v) for m, v in plan["mod_closure"].items()}

def topo_modules():
    order, seen = [], set()
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in imports[m]["proj"]:
            visit(d)
        order.append(m)
    for m in modules:
        visit(m)
    return order
TOPO = topo_modules()
TOPO_IDX = {m: i for i, m in enumerate(TOPO)}

def ext_imports(m):
    s = set(imports[m]["ext"])
    for d in mod_closure[m]:
        s |= set(imports[d]["ext"])
    return sorted(s)

def bundle_imports(m, include_self):
    mods = set(mod_closure[m]) | ({m} if include_self else set())
    return [f"import Definitions.Def_{mslug(d)}" for d in TOPO if d in mods and d in bundles]

HEADER = txt(modules[0], 0, F[modules[0]]["B"].find(b"\nimport ")).strip() + "\n"

def gen_note(m, what):
    return (f"/- Generated for Prove2Me from {REPO}@{COMMIT}, {module_path(m)} ({what});\n"
            f"   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/\n")

# ---------- Definitions bundles ----------
os.makedirs(f"{WS}/Definitions", exist_ok=True)
os.makedirs(f"{WS}/Theorems", exist_ok=True)
os.makedirs(f"{WS}/Solutions", exist_ok=True)
for d in ("Definitions", "Theorems", "Solutions"):
    for f in os.listdir(f"{WS}/{d}"):
        os.remove(f"{WS}/{d}/{f}")

def collapse(s):
    s = re.sub(r"\n[ \t]*\n[ \t]*\n+", "\n\n", s)
    return s.strip("\n") + "\n"

bundle_meta = {}
for m in TOPO:
    if m not in bundles:
        continue
    B = F[m]["B"]
    cmds = F[m]["cmds"]
    body_start = cmds[0]["start"]["offset"]  # first command after the import header
    body_end = len(B)
    # spans to delete: declaration commands of units not kept in the bundle
    dele = []
    kept_units = []
    for uid, u in U.items():
        if u["module"] != m:
            continue
        a, b = u["decl"]["declStart"]["offset"], u["decl"]["declEnd"]["offset"]
        if u["cls"] in ("defmat", "embedded"):
            kept_units.append(uid)
        else:
            # extend to end of line
            while b < len(B) and B[b:b+1] in (b" ", b"\t"):
                b += 1
            if B[b:b+1] == b"\n":
                b += 1
            dele.append((a, b))
    dele.sort()
    pieces, pos = [], body_start
    for a, b in dele:
        if a < pos:
            raise RuntimeError(f"overlapping spans in {m}")
        pieces.append(B[pos:a])
        pos = b
    pieces.append(B[pos:body_end])
    body = b"".join(pieces).decode("utf-8")
    header = HEADER + gen_note(m, "definition bundle: declarations the uploaded statements rest on")
    imps = ext_imports(m) and "\n".join(f"import {x}" for x in ext_imports(m))
    imps = "\n".join([f"import {x}" for x in ext_imports(m)] + bundle_imports(m, include_self=False))
    out = header + imps + "\n\n" + collapse(body)
    fn = f"{WS}/Definitions/Def_{mslug(m)}.lean"
    open(fn, "w", encoding="utf-8").write(out)
    # module docstring for metadata
    mdoc = ""
    for c in cmds:
        if c["syntaxKind"].endswith("moduleDoc"):
            mdoc = txt(m, c["start"]["offset"], c["end"]["offset"])
            break
    bundle_meta[m] = {
        "definition_name": mslug(m), "file": f"Definitions/Def_{mslug(m)}.lean", "module": m,
        "lines": out.count("\n"), "kept": sorted(U[u]["name"] for u in kept_units),
        "defmat": sorted(U[u]["name"] for u in kept_units if U[u]["cls"] == "defmat"),
        "embedded": sorted(U[u]["name"] for u in kept_units if U[u]["cls"] == "embedded"),
        "imports": bundle_imports(m, include_self=False), "moduleDoc": mdoc,
        "source_path": module_path(m),
    }

# ---------- helpers for hoisted context ----------
def unit_text(uid):
    u = U[uid]
    return txt(u["module"], u["decl"]["declStart"]["offset"], u["decl"]["declEnd"]["offset"])

def head_rest(uid, upto):
    """Text from after the binding name up to `upto` ('val' = valStart, 'end' = declEnd)."""
    u = U[uid]
    assert u["bind"], u["name"]
    a = u["bind"]["end"]["offset"]
    b = u["decl"]["valStart"]["offset"] if upto == "val" else u["decl"]["declEnd"]["offset"]
    return txt(u["module"], a, b)

def hoisted_context(uid):
    """Top-level `open`/`variable` lines reproducing the resolution scope of a declaration."""
    u = U[uid]
    ctx = unit_ctx(uid)
    chain = ctx["ns"]
    full_ns = ".".join(u["name"].split(".")[:-1])
    lines = []
    parts = full_ns.split(".") if full_ns else []
    for i in range(1, len(parts) + 1):
        p = ".".join(parts[:i])
        if p in NS:
            lines.append(f"open {p}")
    for o in ctx["opens"]:
        r = resolve_open(o, chain)
        if r not in lines:
            lines.append(r)
    lines += ctx["vars"]
    return lines

def pasted_block(uid):
    ctx = unit_ctx(uid)
    ns = ns_of_chain(ctx["ns"])
    body = []
    if ns:
        body.append(f"namespace {ns}")
    body += ctx["opens"]
    body += ctx["vars"]
    body.append(unit_text(uid).rstrip())
    if ns:
        body.append(f"end {ns}")
    return "\n".join(body) + "\n"

def docstring_text(uid):
    u = U[uid]
    ds = u["decl"]["docstring"]
    if not ds:
        return ""
    s = txt(u["module"], ds["start"]["offset"], ds["end"]["offset"]).strip()
    s = re.sub(r"^/--\s*", "", s)
    s = re.sub(r"\s*-/$", "", s)
    return s.strip()

# ---------- Thm_ stubs and Sol_ files ----------
node_meta = {}
for uid in nodes:
    u = U[uid]
    m = u["module"]
    slug = slugs[uid]
    rest = head_rest(uid, "val").rstrip()
    if u["decl"]["valKind"] != "simple":
        print("note: non-simple value kind for node", u["name"], u["decl"]["valKind"])
    formal = f"theorem {u['name']}{rest} := by sorry"
    pre_lines = ([f"import {x}" for x in ext_imports(m)] + bundle_imports(m, include_self=True)
                 + [""] + hoisted_context(uid))
    preamble = "\n".join(pre_lines)
    stub = HEADER + gen_note(m, f"statement stub of {u['name']}") + preamble + "\n\n" + formal + "\n"
    open(f"{WS}/Theorems/Thm_{slug}.lean", "w", encoding="utf-8").write(stub)

    # solution
    c = comp[uid]
    pasted = sorted(c["pasted"], key=lambda v: (TOPO_IDX[U[v]["module"]], U[v]["decl"]["declStart"]["offset"]))
    imp_lines = ([f"import {x}" for x in ext_imports(m)] + bundle_imports(m, include_self=True)
                 + [f"import Theorems.Thm_{slugs[v]}" for v in sorted(c["imported_nodes"], key=lambda v: slugs[v])])
    sol_parts = [HEADER + gen_note(m, f"solution of {u['name']}"), "\n".join(imp_lines), ""]
    if pasted:
        sol_parts.append("/-! Helper declarations, pasted verbatim from the source modules with their\n"
                         "namespace and `open` context; each is used only by proofs. -/")
        for v in pasted:
            sol_parts.append(pasted_block(v))
    sol_parts.append("/-! The uploaded declaration, hoisted to the top level as `solution`. -/")
    sol_parts.append("\n".join(hoisted_context(uid)))
    body = head_rest(uid, 'end').rstrip()
    # a structurally recursive theorem refers to itself inside its own body; those occurrences
    # elaborate as local variables (no ref facts), so the hoisted copy renames them textually
    # and the compile check validates the result
    short = u["name"].split(".")[-1]
    stmt_len = u["decl"]["valStart"]["offset"] - u["bind"]["end"]["offset"]
    stmt_part, val_part = body[:stmt_len], body[stmt_len:]
    if re.search(r"(?<![A-Za-z0-9_.'])" + re.escape(short) + r"(?![A-Za-z0-9_'])", val_part):
        val_part = re.sub(r"(?<![A-Za-z0-9_.'])" + re.escape(short) + r"(?![A-Za-z0-9_'])", "solution", val_part)
        print("note: renamed self-references in recursive node", u["name"])
    sol_parts.append(f"theorem solution{stmt_part}{val_part}\n")
    sol = "\n".join(sol_parts)
    open(f"{WS}/Solutions/Sol_{slug}.lean", "w", encoding="utf-8").write(sol)
    node_meta[uid] = {
        "theorem_name": u["name"], "slug": slug, "module": m, "source_path": module_path(m),
        "lines": [u["decl"]["declStart"]["line"], u["decl"]["declEnd"]["line"]],
        "prooflines": u["prooflines"], "docstring": docstring_text(uid),
        "formal_statement": formal, "preamble": preamble,
        "imported_nodes": [U[v]["name"] for v in c["imported_nodes"]],
        "pasted": [U[v]["name"] for v in pasted],
        "stub_file": f"Theorems/Thm_{slug}.lean", "solution_file": f"Solutions/Sol_{slug}.lean",
        "is_target": u["name"] in plan["targets"],
    }

json.dump({"bundles": [bundle_meta[m] for m in TOPO if m in bundle_meta],
           "nodes": [node_meta[uid] for uid in nodes], "topo_modules": TOPO},
          open(f"{S}/tree.json", "w"), indent=1)
print(f"wrote {len(bundle_meta)} bundles, {len(nodes)} stubs and solutions; tree.json")
