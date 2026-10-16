#!/usr/bin/env python3
"""Phase 3-4 of the Prove2Me full-project upload: generate the platform tree.

Definitions bundles by skeleton subtraction, Thm_ stubs and Sol_ files by context
reconstruction.  All positions are byte offsets from the Stage 2 facts; the only text
this script parses itself is the import header and the one-line `namespace`/`open`/
`variable` commands whose spans Stage 2 reports.

Configuration: ``P2M_CONFIG`` names the same JSON file plan.py used (``plan`` = its output,
``tree_out`` = where to write tree.json, ``manifest`` = the list of files this run generated,
``wipe`` = whether to empty the three output directories first).  Without it the script
regenerates the recursive-compression tree of 2026-10-12.  With published content in the plan,
nothing already on the platform is regenerated: published nodes are imported as
``Theorems.Thm_<slug>``, published bundles as ``Definitions.Def_<name>``, and a module whose
published bundle lacks a needed declaration gets a delta bundle ``Def_<name>_B`` holding just
the missing declarations.
"""
import os, json, re, sys, collections, shutil

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
REPO = "vidick/MIPRE-formalization"
COMMIT = "70cbf1c"

CFG = {"extract_dir": f"{S}/extract", "plan": f"{S}/plan.json", "tree_out": f"{S}/tree.json",
       "manifest": None, "wipe": True, "token_renames": {}}
if os.environ.get("P2M_CONFIG"):
    c = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8"))
    CFG.update({k: v for k, v in c.items() if k in CFG})
    CFG["plan"] = c.get("out", CFG["plan"])
E = CFG["extract_dir"]

META_CMDS = {"macro", "macro_rules", "syntax", "elab", "elab_rules", "notation", "notation3", "declare_syntax_cat"}
# `size_omega` (Cost/Interpreter.lean) is the closure's one macro; every generated file spells
# out its expansion, with the names the macro pre-resolved at its definition site
MACRO_EXPANSIONS = {
    "size_omega": "((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, "
                  "MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, "
                  "MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, "
                  "MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, "
                  "List.map_cons, List.map_nil] at *); all_goals omega)",
    # the three cost macros of Halting/{Lists,Arith,Serial}.lean (namespace MIPRE.Cost.Prog, open Data)
    "cost_omega": "((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)",
    "cost_omega'": "((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)",
    "cost_omega\u2082": "((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)",
}

def expand_macros(text):
    for name in sorted(MACRO_EXPANSIONS, key=len, reverse=True):   # longest first: cost_omega₂ before cost_omega
        text = re.sub(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])", MACRO_EXPANSIONS[name], text)
    for old, new in RENAMES.items():
        # every written form of the name: in full, and qualified by any suffix of its namespace
        # (`POVM.ext'` inside `namespace MIPRE`), as well as bare; a rename changes the last component
        op, np_ = old.split("."), new.split(".")
        assert op[:-1] == np_[:-1], (old, new)
        for k in range(len(op)):
            o, n = ".".join(op[k:]), ".".join(np_[k:])
            text = re.sub(r"(?<![\w.'])" + re.escape(o) + r"(?![\w'])", lambda _m, n=n: n, text)
    # a field or method of a structure another project published under a different name (the ten-proofs
    # statement file's `POVM.operator` is the proof file's `POVM.effect`): every occurrence of the
    # token, in field notation (`P.effect a`) and in structure instances (`{ effect := … }`); the
    # config lists such a rename only after checking the token has no other use in the tree's modules
    for o, n in TOKEN_RENAMES.items():
        text = re.sub(r"(?<![\w'])" + re.escape(o) + r"(?![\w'])", n, text)
    # `private` is per file: a private declaration copied into a bundle or pasted into a solution
    # would be invisible to the other generated files that use it, so the copies drop the modifier
    text = re.sub(r"^(\s*(?:@\[[^\]]*\]\s*)?)private\s+", r"\1", text, flags=re.M)
    return text

plan = json.load(open(CFG["plan"], encoding="utf-8"))
RENAMES = plan.get("renames", {})
TOKEN_RENAMES = CFG.get("token_renames", {})
U = plan["units"]
modules = plan["modules"]
bundles = set(plan["bundles"])
new_bundles = set(plan.get("new_bundles", plan["bundles"]))
delta_bundles = plan.get("delta_bundles", {})          # module -> definition_name (…_B)
published_bundles = plan.get("published_bundles", {})  # module -> definition_name
bundle_node_imports = plan.get("bundle_imported_nodes", {})  # module -> [slugs of published nodes]
bundle_node_deps = plan.get("bundle_node_deps", {})          # module -> [uids of this tree's nodes its bundle imports]
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
    fn = f"{E}/sketch_info.{m}.jsonl"
    if not os.path.exists(fn):
        fn = f"{E}/sketch_info.{m.split('.')[-1]}.jsonl"
    d = collections.defaultdict(list)
    for l in open(fn, encoding="utf-8"):
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

def effective_opts(lines):
    """The `set_option`/`universe` lines in effect: the last assignment of each option wins, universe
    declarations are kept once, source order otherwise."""
    last = {}
    for i, l in enumerate(lines):
        mm = re.match(r"set_option\s+(\S+)", l)
        last[("opt", mm.group(1)) if mm else ("univ", l)] = i
    keep = set(last.values())
    return [l for i, l in enumerate(lines) if i in keep]

# ---------- scope map: context of every declaration command ----------
CTX = {}  # (module, declStart.offset) -> {"ns": [...], "opens": [...], "vars": [...]}
OPEN_NAMES = {}  # (module, open command text) -> {name as written: unit or None}

def filter_open(m, text, avail):
    """`open X (a b)` keeping only the named declarations the file can see at that point (`avail` on
    their units; a name that is no unit of the closure stays): a theorem the source opens by name may
    have become a helper or a node this file does not import (`open MultiTapeTM (…
    moveInputPos_neg_of_ne_left …)` in a bundle).  A group left empty goes with its namespace (`open
    X` alone would open all of X); None when nothing remains."""
    names = OPEN_NAMES.get((m, text.strip()))
    if not names or "(" not in text:
        return text
    head, body = text.strip()[:len("open")], text.strip()[len("open"):]
    toks = re.findall(r"\([^)]*\)|\S+", body)
    out = []
    for tk in toks:
        if tk.startswith("(") and out and not out[-1].startswith("("):
            kept = [n for n in tk[1:-1].split() if names.get(n) is None or avail(names[n])]
            if kept:
                out.append("(" + " ".join(kept) + ")")
            else:
                out.pop()   # the namespace this group belonged to
        else:
            out.append(tk)
    rest = [x for x in out if x not in ("scoped",)]
    return (head + " " + " ".join(out)) if rest else None
ATTRS = {}  # module -> [attribute commands: {"start", "end", "attr", "names": [(token, uid|None)]}]
const_unit = {}
for uid, u in U.items():
    for r in u["rows"]:
        const_unit[r] = uid
for m in modules:
    stack = []  # frames: {"name" (None for a section), "opens", "vars", "opts", "attrs"}
    root = {"name": None, "opens": [], "vars": [], "opts": [], "attrs": []}
    ATTRS[m] = []
    for c in F[m]["cmds"]:
        k = c["syntaxKind"].split(".")[-1]
        t = txt(m, c["start"]["offset"], c["end"]["offset"]).strip()
        if k == "namespace":
            stack.append({"name": t.split()[1], "opens": [], "vars": [], "opts": [], "attrs": []})
        elif k in ("section", "noncomputableSection"):
            # Lean 4.33 parses `noncomputable section` as a `section` command with the modifier
            nc = k == "noncomputableSection" or re.match(r"(?:@\[[^\]]*\]\s*)?(?:public\s+)?noncomputable\b", t) is not None
            stack.append({"name": None, "opens": [], "vars": [], "opts": [], "attrs": [], "nc": nc})
        elif k == "end":
            if stack:
                stack.pop()
        elif k == "attribute":
            raw = txt(m, c["start"]["offset"], c["end"]["offset"])
            lead = len(raw) - len(raw.lstrip())
            mm = re.match(r"attribute\s*(\[.*?\])\s*(.*)$", t, re.S)
            if mm:
                names = []
                names_at = t.index(mm.group(2), mm.end(1))
                base = c["start"]["offset"] + len(raw[:lead].encode("utf-8"))
                for tok in re.finditer(r"\S+", mm.group(2)):
                    ta = base + len(t[:names_at + tok.start()].encode("utf-8"))
                    tb = ta + len(tok.group(0).encode("utf-8"))
                    uid, const = None, None
                    best = None
                    for rf in F[m]["refs"]:
                        if ta <= rf["start"]["offset"] and rf["end"]["offset"] <= tb:
                            if best is None or rf["end"]["offset"] - rf["start"]["offset"] > best["end"]["offset"] - best["start"]["offset"]:
                                best = rf
                    if best is not None:
                        const = best["const"]
                        uid = const_unit.get(const)
                        if uid is None:
                            pm = re.match(r"_private\.(?:[^.]+\.)*?\d+\.(.*)$", const)
                            if pm:
                                const = pm.group(1)
                                uid = next((x for x, uu in U.items() if uu["name"] and uu["name"].endswith(pm.group(1))), None)
                    names.append((tok.group(0), uid, const))
                ATTRS[m].append({"start": c["start"]["offset"], "end": c["end"]["offset"], "attr": mm.group(1), "names": names})
                # a `local`/`scoped` attribute is in effect to the end of its section (the vendored parts open
                # every section with `attribute [local instance] Classical.propDecidable`, which their
                # statements need); a global one from its position on
                is_local = re.match(r"\[\s*(local|scoped)\b", mm.group(1)) is not None
                (stack[-1] if (stack and is_local) else root)["attrs"].append({"attr": mm.group(1), "names": names})
        elif k == "open":
            (stack[-1] if stack else root)["opens"].append(t)
            if "(" in t:
                # the declarations an `open X (a b)` names, resolved by the reference facts inside it
                a0, b0 = c["start"]["offset"], c["end"]["offset"]
                found = {}
                for rf in F[m]["refs"]:
                    if a0 <= rf["start"]["offset"] and rf["end"]["offset"] <= b0:
                        tok = txt(m, rf["start"]["offset"], rf["end"]["offset"])
                        found[tok] = const_unit.get(rf["const"])
                OPEN_NAMES[(m, t)] = found
        elif k in ("variable", "include", "omit"):
            (stack[-1] if stack else root)["vars"].append(t)
        elif k in ("set_option", "universe"):
            # a top-level `set_option` (the vendored parts set `autoImplicit`, `maxHeartbeats`,
            # `maxRecDepth` and `backward.isDefEq.respectTransparency` this way, hundreds of times)
            # and a `universe` declaration are in effect for the rest of their section
            (stack[-1] if stack else root)["opts"].append(t)
        elif k in ("declaration", "in", "lemma", "deriving") or k.startswith("command_Irreducible_def"):
            # Mathlib's `lemma`, `deriving instance … for …` and `irreducible_def` declare constants too
            frames = [root] + stack
            CTX[(m, c["start"]["offset"])] = {
                "ns": [f["name"] for f in stack if f["name"]],
                "opens": [o for f in frames for o in f["opens"]],
                "vars": [v for f in frames for v in f["vars"]],
                "opts": effective_opts([o for f in frames for o in f["opts"]]),
                "nc": any(f.get("nc") for f in stack),   # inside a `noncomputable section`
                "attrs": [a for f in frames for a in f["attrs"]],
            }
        # moduleDoc, macro, export, eoi: no scope effect
    # a file may end inside a section or namespace (a file-level `noncomputable section` is often left
    # open), which Lean closes at the end of the file; only an `end` without a scope would be wrong

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

def ns_registrations(ctx, own_ns=None):
    """`namespace N end N` lines, at the top level, for the declaration's own namespace and each project
    namespace its `open` lines name.  `open N` fails when no declaration of the file's environment lives
    in N, which happens once all of N's declarations have become nodes or helpers the file does not
    import (`open MIPRE.CL.CLFun.ExactlyOn` for `theorem ExactlyOn.concat`); an empty `namespace N end N`
    registers N and adds nothing to it."""
    chain = ctx["ns"]
    names = [own_ns] if own_ns else []
    for o in ctx["opens"]:
        for tk in re.findall(r"\([^)]*\)|\S+", o[len("open"):].strip()):
            if tk in ("hiding", "renaming"):
                break          # what follows names declarations, not namespaces
            if tk.startswith("(") or tk in ("scoped", "in"):
                continue
            r = resolve_ns(tk, chain)
            if r in NS:
                names.append(r)
    return [f"namespace {n} end {n}" for n in dict.fromkeys(names)]

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

def bundle_names(d, exclude_delta_of=None):
    """Platform bundle modules that carry module d's declarations, in import order."""
    out = []
    if d in published_bundles:
        out.append(f"Definitions.Def_{published_bundles[d]}")
    if d in delta_bundles and d != exclude_delta_of:
        out.append(f"Definitions.Def_{delta_bundles[d]}")
    if d in new_bundles:
        out.append(f"Definitions.Def_{mslug(d)}")
    return out

def bundle_imports(m, include_self, exclude_delta_of=None):
    mods = set(mod_closure[m]) | ({m} if include_self else set())
    return [f"import {b}" for d in TOPO if d in mods for b in bundle_names(d, exclude_delta_of)]

HEADER = txt(modules[0], 0, F[modules[0]]["B"].find(b"\nimport ")).strip() + "\n"

def gen_note(m, what):
    return (f"/- Generated for Prove2Me from {REPO}@{COMMIT}, {module_path(m)} ({what});\n"
            f"   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/\n")

# ---------- output directories ----------
for d in ("Definitions", "Theorems", "Solutions"):
    os.makedirs(f"{WS}/{d}", exist_ok=True)
if CFG["wipe"]:
    for d in ("Definitions", "Theorems", "Solutions"):
        for f in os.listdir(f"{WS}/{d}"):
            os.remove(f"{WS}/{d}/{f}")
previous = set()
PARTIAL = f"{CFG['manifest']}.partial" if CFG["manifest"] else None   # files a run writes before it finishes
if not CFG["wipe"] and CFG["manifest"]:
    for mf in (CFG["manifest"], PARTIAL):
        if os.path.exists(mf):
            previous |= set(json.load(open(mf, encoding="utf-8")))
generated = []

def emit(rel, text):
    fn = f"{WS}/{rel}"
    if not CFG["wipe"] and os.path.exists(fn) and rel not in previous:
        raise RuntimeError(f"refusing to overwrite an existing file not generated by this plan: {rel}")
    generated.append(rel)
    if PARTIAL:   # an aborted run must not leave files the next run refuses to touch
        json.dump(generated, open(PARTIAL, "w"), indent=0)
    if os.path.exists(fn) and open(fn, encoding="utf-8").read() == text:
        return
    open(fn, "w", encoding="utf-8").write(text)

def collapse(s):
    s = re.sub(r"\n[ \t]*\n[ \t]*\n+", "\n\n", s)
    return s.strip("\n") + "\n"

# ---------- Definitions bundles ----------
bundle_meta = {}
for m in TOPO:
    if m not in bundles:
        continue
    is_delta = m in delta_bundles
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
    # the platform rejects metaprogramming ("custom syntax/elaborator registration ... not
    # supported in submissions"): drop such commands from the bundle; their uses are expanded below
    for c in cmds:
        if c["syntaxKind"].split(".")[-1] in META_CMDS:
            a, b = c["start"]["offset"], c["end"]["offset"]
            while b < len(B) and B[b:b+1] in (b" ", b"\t"):
                b += 1
            if B[b:b+1] == b"\n":
                b += 1
            dele.append((a, b))
    # attribute commands: keep the names this bundle's environment has (kept here, kept in an
    # imported bundle, or not a project declaration); drop the command when none remains
    repl = {}
    visible = set(kept_units) | {uid for uid, u in U.items() if u["cls"] in ("avail",)
                                  or (u["cls"] in ("defmat", "embedded") and u["module"] in mod_closure[m])}
    visible |= set(bundle_node_deps.get(m, []))   # this tree's nodes the bundle imports
    pub_imp = set(bundle_node_imports.get(m, []))   # and the published nodes it imports
    visible |= {uid for uid, u in U.items() if u["cls"] == "pubnode" and slugs.get(uid) in pub_imp}
    for c in cmds:
        if c["syntaxKind"].endswith(".open"):
            a, b = c["start"]["offset"], c["end"]["offset"]
            ot = txt(m, a, b).strip()
            if (m, ot) in OPEN_NAMES:
                nt = filter_open(m, ot, lambda v: v in visible)
                if nt != ot:
                    while b < len(B) and B[b:b+1] in (b" ", b"\t"):
                        b += 1
                    if B[b:b+1] == b"\n":
                        b += 1
                    dele.append((a, b))
                    repl[a] = (nt + "\n").encode("utf-8") if nt else b""
    for at in ATTRS[m]:
        keep = [tok if uid is None else const for tok, uid, const in at["names"] if uid is None or uid in visible]
        a, b = at["start"], at["end"]
        while b < len(B) and B[b:b+1] in (b" ", b"\t"):
            b += 1
        if B[b:b+1] == b"\n":
            b += 1
        dele.append((a, b))
        repl[a] = (f"attribute {at['attr']} " + " ".join(keep) + "\n").encode("utf-8") if keep else b""
    dele.sort()
    pieces, pos = [], body_start
    for a, b in dele:
        if a < pos:
            raise RuntimeError(f"overlapping spans in {m}")
        pieces.append(B[pos:a])
        pieces.append(repl.get(a, b""))
        pos = b
    pieces.append(B[pos:body_end])
    body = b"".join(pieces).decode("utf-8")
    what = ("delta bundle: declarations the new statements need that the published bundle "
            f"Def_{published_bundles[m]} does not carry" if is_delta
            else "definition bundle: declarations the uploaded statements rest on")
    header = HEADER + gen_note(m, what)
    imps = "\n".join([f"import {x}" for x in ext_imports(m)] + bundle_imports(m, include_self=is_delta, exclude_delta_of=m)
                     + [f"import Theorems.Thm_{sl}" for sl in bundle_node_imports.get(m, [])]
                     + [f"import Theorems.Thm_{slugs[v]}" for v in sorted(bundle_node_deps.get(m, []), key=lambda v: slugs[v])])
    out = expand_macros(header + imps + "\n\n" + collapse(body))
    name = delta_bundles[m] if is_delta else mslug(m)
    rel = f"Definitions/Def_{name}.lean"
    emit(rel, out)
    # module docstring for metadata
    mdoc = ""
    for c in cmds:
        if c["syntaxKind"].endswith("moduleDoc"):
            mdoc = txt(m, c["start"]["offset"], c["end"]["offset"])
            break
    bundle_meta[m] = {
        "definition_name": name, "kind": "delta" if is_delta else "new", "file": rel, "module": m,
        "lines": out.count("\n"), "kept": sorted(U[u]["name"] for u in kept_units),
        "defmat": sorted(U[u]["name"] for u in kept_units if U[u]["cls"] == "defmat"),
        "embedded": sorted(U[u]["name"] for u in kept_units if U[u]["cls"] == "embedded"),
        "imports": bundle_imports(m, include_self=is_delta, exclude_delta_of=m),
        "imported_published_nodes": bundle_node_imports.get(m, []), "moduleDoc": mdoc,
        "imported_nodes": sorted(U[v]["name"] for v in bundle_node_deps.get(m, [])),
        "source_path": module_path(m),
        "published_bundle": published_bundles.get(m),
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
    lines = ns_registrations(ctx, full_ns)
    parts = full_ns.split(".") if full_ns else []
    for i in range(1, len(parts) + 1):
        p = ".".join(parts[:i])
        if p in NS:
            lines.append(f"open {p}")
    for o in ctx["opens"]:
        o = filter_open(u["module"], o, lambda v: U[v]["cls"] in ("defmat", "embedded", "avail"))
        if o is None:
            continue
        r = resolve_open(o, chain)
        if r not in lines:
            lines.append(r)
    lines += ctx["opts"]
    lines += ctx["vars"]
    return lines

REDUCIBILITY = {"reducible", "semireducible", "irreducible", "instance_reducible", "implicit_reducible"}

def replayable(attr):
    """The attribute list of a replayed command without its global reducibility attributes: Lean sets
    those only in the file that declares the constant (`attribute [instance_reducible, instance]
    FieldModel.instField` of the vendored test), and the bundle declaring it carries them to every
    importer already.  A `local` reducibility attribute is allowed anywhere and stays."""
    inner, parts, depth, cur = attr.strip()[1:-1], [], 0, ""
    for ch in inner:
        if ch in "([{": depth += 1
        elif ch in ")]}": depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur.strip()); cur = ""
        else:
            cur += ch
    parts.append(cur.strip())
    keep = [q for q in parts if q and q.split()[0] not in REDUCIBILITY]
    return "[" + ", ".join(keep) + "]" if keep else None

def attr_lines(uid, available):
    """The attribute commands in effect at a declaration, restricted to targets the file can see."""
    out = []
    for at in unit_ctx(uid)["attrs"]:
        names = [tok if tu is None else const for tok, tu, const in at["names"] if tu is None or available(tu)]
        attr = replayable(at["attr"])
        if names and attr:
            out.append(f"attribute {attr} " + " ".join(dict.fromkeys(names)))
    return out

def pasted_block(uid, available):
    """A helper declaration with its scope: namespace, then a section (noncomputable when the source
    declares it inside one, so that a pasted definition compiles as in the source) holding the `open`,
    `set_option`/`universe` and `variable` lines and the attribute commands in effect (a `local instance`
    of the source's section must not reach a helper from a section without it: the instance found for
    a statement would differ from the source's), so that none of them leaks into the next block."""
    ctx = unit_ctx(uid)
    ns = ns_of_chain(ctx["ns"])
    body = ns_registrations(ctx)
    if ns:
        body.append(f"namespace {ns}")
    body.append("noncomputable section" if ctx.get("nc") else "section")
    body += [o for o in (filter_open(U[uid]["module"], o, available) for o in ctx["opens"]) if o is not None]
    body += ctx["opts"]
    body += ctx["vars"]
    body += attr_lines(uid, available)
    body.append(unit_text(uid).rstrip())
    body.append("end")
    if ns:
        body.append(f"end {ns}")
    return "\n".join(body) + "\n"

DECL_KW = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                     r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b", re.M)

def in_prefix(uid):
    """The `<cmd> in` prefixes of a declaration (`include G U in`, `omit [h] in`, `open X in`), as the
    verbatim prefix text and as the list of bare commands."""
    u = U[uid]
    d = u["decl"]
    a = d["declStart"]["offset"]
    b = d["docstring"]["start"]["offset"] if d["docstring"] else u["bind"]["start"]["offset"]
    head = txt(u["module"], a, b)
    if not d["docstring"]:
        km = DECL_KW.search(head)
        head = head[:km.start()] if km else ""
    cmds = [c.strip() for c in re.findall(r"(\S.*?)\s+in(?=\s)", head, re.S)]
    return head.strip(), cmds

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
    formal = expand_macros(f"theorem {u['name']}{rest} := by sorry")
    prefix_text, prefix_cmds = in_prefix(uid)
    pre_lines = ([f"import {x}" for x in ext_imports(m)] + bundle_imports(m, include_self=True)
                 + [""] + hoisted_context(uid)
                 + attr_lines(uid, lambda tu: U[tu]["cls"] in ("defmat", "embedded", "avail", "pubnode"))
                 + prefix_cmds)   # `include G U in` becomes a bare `include G U`
    preamble = "\n".join(pre_lines)
    stub = HEADER + gen_note(m, f"statement stub of {u['name']}") + preamble + "\n\n" + formal + "\n"
    stub = expand_macros(stub)
    emit(f"Theorems/Thm_{slug}.lean", stub)

    # solution
    c = comp[uid]
    pasted = sorted(c["pasted"], key=lambda v: (TOPO_IDX[U[v]["module"]], U[v]["decl"]["declStart"]["offset"]))
    imp_lines = ([f"import {x}" for x in ext_imports(m)] + bundle_imports(m, include_self=True)
                 + [f"import Theorems.Thm_{slugs[v]}" for v in sorted(c["imported_nodes"], key=lambda v: slugs[v])])
    sol_parts = [HEADER + gen_note(m, f"solution of {u['name']}"), "\n".join(imp_lines), ""]
    # The global attribute commands of the source modules are replayed at their source position, in
    # the same (module, offset) order as the pasted helpers, so that each is in effect only from its
    # position on; commands after the uploaded declaration are dropped.  A `local`/`scoped` attribute
    # (`[local irreducible] tab` in Reduction.lean after the lemmas whose proofs unfold `tab`;
    # `[local instance] Classical.propDecidable` opening every section of the vendored parts) is in
    # effect only inside its section, and is reproduced inside the blocks of the helpers declared
    # under it instead (replayed globally it made a helper's statement pick `Classical.propDecidable`
    # where the source had `FinEnum.decEq`).
    main_off = u["decl"]["declStart"]["offset"]
    events = [("unit", TOPO_IDX[U[v]["module"]], U[v]["decl"]["declStart"]["offset"], v) for v in pasted]
    for am in sorted({m} | {U[v]["module"] for v in pasted}, key=lambda x: TOPO_IDX[x]):
        for at in ATTRS[am]:
            if am == m and at["start"] >= main_off:
                continue
            if re.match(r"\[\s*(local|scoped)\b", at["attr"]) is not None:
                continue   # scoped to its section: emitted inside the blocks it applies to
            events.append(("attr", TOPO_IDX[am], at["start"], at))
    events.sort(key=lambda e: (e[1], e[2]))
    if events:
        sol_parts.append("/-! Helper declarations, pasted verbatim from the source modules with their\n"
                         "namespace and `open` context, each used only by proofs, interleaved with the\n"
                         "attribute commands of those modules at their source positions. -/")
    emitted = set()
    def available(tu):
        return (U[tu]["cls"] in ("defmat", "embedded", "avail", "pubnode") or tu in emitted
                or tu in c["imported_nodes"])
    for e in events:
        if e[0] == "unit":
            sol_parts.append(pasted_block(e[3], available))
            emitted.add(e[3])
        else:
            at = e[3]
            # a target pasted into this file takes the command as written; an imported one only what
            # Lean allows outside the declaring file (no global reducibility attribute, see replayable)
            here = [const for tok, tu, const in at["names"] if tu is not None and tu in emitted]
            there = [tok if tu is None else const for tok, tu, const in at["names"]
                     if (tu is None or U[tu]["cls"] in ("defmat", "embedded", "avail", "pubnode")
                         or tu in c["imported_nodes"]) and not (tu is not None and tu in emitted)]
            if here:
                sol_parts.append(f"attribute {at['attr']} " + " ".join(dict.fromkeys(here)) + "\n")
            attr = replayable(at["attr"])
            if there and attr:
                sol_parts.append(f"attribute {attr} " + " ".join(dict.fromkeys(there)) + "\n")
    sol_parts.append("/-! The uploaded declaration as `solution` (a root name declared inside the source's\n"
                     "namespace, so that names resolve as they do in the source). -/")
    sctx = unit_ctx(uid)
    name_ns = ".".join(u["name"].split(".")[:-1])
    chain_ns = ns_of_chain(sctx["ns"])
    # names resolve as in the source inside the source's namespace chain; a declaration whose name
    # extends the chain (`theorem C.foo` in `namespace A.B`) has its own namespace current as well, and
    # a `_root_` declaration (`theorem _root_.Nat.bits_two_pow_mul` in `namespace MIPRE.Cost.Prog`) has
    # its prefix opened instead, since `open Data` of the source would not resolve under `namespace Nat`
    if not chain_ns or name_ns == chain_ns or name_ns.startswith(chain_ns + "."):
        sol_ns, extra_open = name_ns, None
    else:
        sol_ns, extra_open = chain_ns, name_ns
    sol_parts += ns_registrations(sctx, name_ns)
    if sol_ns:
        sol_parts.append(f"namespace {sol_ns}")
    sol_parts += [o for o in (filter_open(u["module"], o, available) for o in sctx["opens"]) if o is not None]
    sol_parts += sctx["opts"] + sctx["vars"]
    sol_parts += attr_lines(uid, available)
    if extra_open:
        sol_parts.append(f"open {extra_open}")
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
    if prefix_text:
        sol_parts.append(prefix_text)
    sol_parts.append(f"theorem _root_.solution{stmt_part}{val_part}" if sol_ns else f"theorem solution{stmt_part}{val_part}")
    if sol_ns:
        sol_parts.append(f"end {sol_ns}\n")
    sol = expand_macros("\n".join(sol_parts))
    emit(f"Solutions/Sol_{slug}.lean", sol)
    node_meta[uid] = {
        "theorem_name": RENAMES.get(u["name"], u["name"]), "source_name": u["name"], "slug": slug, "module": m, "source_path": module_path(m),
        "lines": [u["decl"]["declStart"]["line"], u["decl"]["declEnd"]["line"]],
        "prooflines": u["prooflines"], "docstring": docstring_text(uid),
        "formal_statement": formal, "preamble": preamble, "in_prefix": prefix_cmds,
        "imported_nodes": [U[v]["name"] for v in c["imported_nodes"]],
        "imported_published_nodes": [U[v]["name"] for v in c["imported_nodes"] if U[v]["cls"] == "pubnode"],
        "pasted": [U[v]["name"] for v in pasted],
        "stub_file": f"Theorems/Thm_{slug}.lean", "solution_file": f"Solutions/Sol_{slug}.lean",
        "is_target": u["name"] in plan["targets"],
    }

tree = {"bundles": [bundle_meta[m] for m in TOPO if m in bundle_meta],
        "nodes": [node_meta[uid] for uid in nodes], "topo_modules": TOPO,
        "published_bundles": published_bundles,
        "published_nodes": sorted({slugs[uid] for uid, u in U.items() if u["cls"] == "pubnode"})}
json.dump(tree, open(CFG["tree_out"], "w"), indent=1)
for rel in sorted(previous - set(generated)):   # generated by the previous run, not by this one
    if os.path.exists(f"{WS}/{rel}"):
        os.remove(f"{WS}/{rel}")
if CFG["manifest"]:
    json.dump(generated, open(CFG["manifest"], "w"), indent=1)
    if PARTIAL and os.path.exists(PARTIAL):
        os.remove(PARTIAL)
print(f"wrote {len(bundle_meta)} bundles ({sum(1 for b in bundle_meta.values() if b['kind'] == 'delta')} delta), "
      f"{len(nodes)} stubs and solutions; {CFG['tree_out']}")
