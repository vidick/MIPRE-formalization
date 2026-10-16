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
OPEN_CHAIN = {}  # (module, open command offset) -> the namespace chain the command sits in

def open_ns_tokens(text):
    """The namespaces an `open` line names (not its declaration groups, keywords or hidden names)."""
    out = []
    for tk in re.findall(r"\([^)]*\)|\S+", text.strip()[len("open"):].strip()):
        if tk in ("hiding", "renaming"):
            break
        if tk.startswith("(") or tk in ("scoped", "in"):
            continue
        out.append(tk)
    return out
VAR_GROUPS = {}  # (module, variable command text) -> [(binder group text, {units it references}, [names it binds])]
BRACKETS = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}

def binder_groups(m, c):
    """The binder groups of a `variable` command, each with the project units its text references
    (by the reference facts inside it) and the names it binds."""
    a0, b0 = c["start"]["offset"], c["end"]["offset"]
    raw = F[m]["B"][a0:b0].decode("utf-8")
    lead = len(raw) - len(raw.lstrip())
    s = raw.strip()
    i = s.index("variable") + len("variable")
    groups = []
    while i < len(s):
        ch = s[i]
        if ch in BRACKETS:
            close, depth, j = BRACKETS[ch], 0, i
            while j < len(s):
                if s[j] == ch: depth += 1
                elif s[j] == close:
                    depth -= 1
                    if depth == 0: break
                j += 1
            gtext = s[i:j + 1]
            ga = a0 + len(raw[:lead].encode("utf-8")) + len(s[:i].encode("utf-8"))
            gb = ga + len(gtext.encode("utf-8"))
            units = {const_unit[rf["const"]] for rf in F[m]["refs"]
                     if ga <= rf["start"]["offset"] and rf["end"]["offset"] <= gb and rf["const"] in const_unit}
            inner = gtext[1:-1]
            names = inner.split(":", 1)[0].split() if ":" in inner else []
            groups.append((gtext, units, names))
            i = j + 1
        else:
            i += 1
    return groups

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

# attributes that cannot be set outside the declaring file, or that generate declarations
NO_REPLAY = REDUCIBILITY | {"deprecated", "inherit_doc", "to_additive", "simps", "nolint", "irreducible_def"}

def node_attr_lines(uids):
    """`attribute [a] X` for each imported node X the source declares with attributes (`@[simp]
    theorem AxisParallelLine.appendAtHeight_rebaseAt`, `@[ext] theorem ProjMeas.ext`): a node's stub
    declares it without them, so a file importing it lost the simp or ext lemma the source's proofs
    rely on (`simp` made no progress in the MainInductionStep bundle)."""
    out = []
    for v in sorted(uids, key=lambda v: U[v]["name"]):
        u = U[v]
        if not u.get("has_attr"):
            continue
        attrs = []
        for a in u.get("attr_text") or []:
            inner = a.strip()
            if inner.startswith("@[") and inner.endswith("]"):
                inner = inner[2:-1]
            got = replayable("[" + inner + "]")
            for q in (got[1:-1].split(",") if got else []):
                q = q.strip()
                if q and q.split()[0] not in NO_REPLAY:
                    attrs.append(q)
        if attrs:
            out.append(f"attribute [{', '.join(attrs)}] {u['name']}")
    return out

# ---------- private declarations whose names collide once the copies drop `private` ----------
# Lean keeps a private name apart per file; the generated copies are public (other generated files
# use them), so two modules' `private def isEmptyProg` in one namespace (BinaryGCD, BinaryExactDivision,
# BinaryNonresidueLoop) would declare the same constant in bundles that import each other.  Each such
# declaration is renamed after its module, in the text that module contributes (its references to
# the private name are all bare, and resolve to its own copy).
def _user_of(name):
    mm = re.match(r"_private\.(?:[^.]+\.)*?\d+\.(.*)$", name)
    return mm.group(1) if mm else name
_AUX = re.compile(r"\.(match_\d+|eq_\d+|splitter|_sparseCasesOn_\d+|proof_\d+|eq_def|induct)(\.|$)|\._")
_by_user = collections.defaultdict(set)
for _uid, _u in U.items():
    if _u.get("is_private") and _u.get("name") and not _AUX.search(_user_of(_u["name"])):
        _by_user[_user_of(_u["name"])].add(_u["module"])
_public = {_u["name"] for _u in U.values() if _u.get("name") and not _u.get("is_private")}
PRIVATE_RENAMES = collections.defaultdict(dict)   # module -> {short name: short name after the module}
for _un, _ms in _by_user.items():
    if len(_ms) > 1 or _un in _public:
        _short = _un.split(".")[-1]
        for _mod in _ms:
            PRIVATE_RENAMES[_mod][_short] = f"{_short}_{_mod.split('.')[-1]}"

def mod_rename(m, text):
    for o, n in PRIVATE_RENAMES.get(m, {}).items():
        text = re.sub(r"(?<![\w.'])" + re.escape(o) + r"(?![\w'])", lambda _m, n=n: n, text)
    return text

def filter_vars(m, var_texts, avail):
    """The `variable`/`include`/`omit` lines of a scope without the binders over declarations the file
    cannot see: a declaration left out of every bundle (no kept declaration needs it, so none uses such
    a binder) is still named by its section's `variable (I : Index)`.  An `include`/`omit` loses the
    names of dropped binders; a line left empty goes."""
    out, dropped = [], set()
    for v in var_texts:
        groups = VAR_GROUPS.get((m, v.strip()))
        if groups is not None:
            kept = [g for g in groups if all(avail(x) for x in g[1])]
            for g in groups:
                if g not in kept:
                    dropped.update(g[2])
            if len(kept) == len(groups):
                out.append(v)
            elif kept:
                out.append("variable " + " ".join(g[0] for g in kept))
            continue
        mm = re.match(r"\s*(include|omit)\b(.*)$", v, re.S)
        if mm and dropped:
            toks = re.findall(r"\[[^\]]*\]|\S+", mm.group(2))
            kept = [x for x in toks if x.strip("[]") not in dropped and x not in dropped]
            if kept:
                out.append(mm.group(1) + " " + " ".join(kept))
            continue
        out.append(v)
    return out

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
            OPEN_CHAIN[(m, c["start"]["offset"])] = [f["name"] for f in stack if f["name"]]
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
            if k == "variable":
                VAR_GROUPS[(m, t)] = binder_groups(m, c)
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

# ---------- imports ----------
imports = plan["imports"]
mod_closure = {m: set(v) for m, v in plan["mod_closure"].items()}

# ---------- `open` lines: namespaces as the source resolved them, pruned to the file's environment ----------
# An `open N` of a project namespace no declaration of a generated file's environment lives in fails
# ("unknown namespace"), and would open nothing: that happens once all of N's declarations became
# nodes or helpers the file does not import (`open MIPRE.CL.CLFun.ExactlyOn` for `theorem
# ExactlyOn.concat`, `open GCommStability.Scalar` in a vendored bundle).  Such a namespace is dropped
# from the line.  The namespace a name denotes is the one Lean found in the source: the first match
# from the innermost enclosing namespace out, among the namespaces of the module's own environment
# (its import closure), not of the whole closure: `open Cost` inside `namespace MIPRE.CL` is
# `MIPRE.Cost`, and registering an empty `MIPRE.CL.Cost` instead shadowed it (2026-10-16).
def _prefixes(name):
    parts = name.split(".")
    return [".".join(parts[:i]) for i in range(1, len(parts))]

_MOD_NS = collections.defaultdict(set)    # module -> namespaces its declarations live in
for _uid, _u in U.items():
    if _u.get("name"):
        _MOD_NS[_u["module"]].update(_prefixes(_user_of(_u["name"])))
_SRC_NS = {}
def src_ns(m):
    """The project namespaces of module m's environment in the source: its own and its imports'."""
    if m not in _SRC_NS:
        s = set(_MOD_NS.get(m, ()))
        for x in mod_closure.get(m, ()):
            s |= _MOD_NS.get(x, set())
        _SRC_NS[m] = s
    return _SRC_NS[m]

def resolve_src(m, tk, chain):
    """The project namespace `open tk` denoted in module m inside `chain`; None for any other (Mathlib, core)."""
    nsset = src_ns(m)
    full = ns_of_chain(chain)
    parts = full.split(".") if full else []
    for i in range(len(parts), 0, -1):
        cand = ".".join(parts[:i]) + "." + tk
        if cand in nsset:
            return cand
    return tk if tk in nsset else None

def env_ns_of(units):
    """The namespaces the declarations of these units live in."""
    s = set()
    for v in units:
        n = U[v].get("name")
        if n:
            s.update(_prefixes(_user_of(n)))
    return s

_STUB_ENV = {}
def stub_env_ns(m):
    """Namespaces of a stub's or solution's bundles: the definition material and embedded theorems of
    the module's closure, and the published bundles' declarations."""
    if m not in _STUB_ENV:
        mods = set(mod_closure.get(m, ())) | {m}
        _STUB_ENV[m] = env_ns_of(v for v, uu in U.items()
                                 if uu["module"] in mods and uu["cls"] in ("defmat", "embedded", "avail"))
    return _STUB_ENV[m]

def prune_open(m, text, chain, env_ns, absolute=False):
    """The `open` line without the project namespaces absent from the file's environment (None if
    nothing is left); with absolute, each kept project namespace is written in full, as the source
    resolved it, for a line moved to the top level."""
    toks = re.findall(r"\([^)]*\)|\S+", text.strip()[len("open"):].strip())
    if any(tk in ("hiding", "renaming") for tk in toks):
        k = 1 if toks and toks[0] == "scoped" else 0
        if k < len(toks):
            r = resolve_src(m, toks[k], chain)
            if r is not None and r not in env_ns:
                return None
            if absolute and r is not None:
                toks[k] = r
        return "open " + " ".join(toks)
    out, drop_group = [], False
    for tk in toks:
        if tk.startswith("("):
            if not drop_group:
                out.append(tk)
            continue
        if tk == "scoped":
            out.append(tk); drop_group = False; continue
        r = resolve_src(m, tk, chain)
        if r is not None and r not in env_ns:
            drop_group = True
            continue
        drop_group = False
        out.append(r if (absolute and r is not None) else tk)
    if not [x for x in out if x != "scoped" and not x.startswith("(")]:
        return None
    return "open " + " ".join(out)

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
    bundle_env = env_ns_of(visible)
    for c in cmds:
        if c["syntaxKind"].endswith(".open"):
            a, b = c["start"]["offset"], c["end"]["offset"]
            ot = txt(m, a, b).strip()
            nt = filter_open(m, ot, lambda v: v in visible) if (m, ot) in OPEN_NAMES else ot
            # a project namespace no declaration of the bundle's environment lives in makes `open`
            # fail (`open GCommStability.Scalar` inside `namespace MIPStarRE.LDT.Commutativity`, all of
            # whose declarations became nodes); opening it would make nothing visible, so it is dropped
            # (registering it instead created namespaces that shadowed the ones the source opened)
            nt = prune_open(m, nt, OPEN_CHAIN.get((m, a), []), bundle_env) if nt is not None else None
            if nt != ot:
                while b < len(B) and B[b:b+1] in (b" ", b"\t"):
                    b += 1
                if B[b:b+1] == b"\n":
                    b += 1
                dele.append((a, b))
                repl[a] = (nt + "\n").encode("utf-8") if nt else b""
    bundle_dropped = set()
    for c in cmds:
        k = c["syntaxKind"].split(".")[-1]
        if k not in ("variable", "include", "omit"):
            continue
        a, b = c["start"]["offset"], c["end"]["offset"]
        vt = txt(m, a, b).strip()
        if k == "variable":
            groups = VAR_GROUPS.get((m, vt), [])
            kept = [g for g in groups if all(x in visible for x in g[1])]
            if len(kept) == len(groups):
                continue
            for g in groups:
                if g not in kept:
                    bundle_dropped.update(g[2])
            nt = ("variable " + " ".join(g[0] for g in kept)) if kept else None
        else:
            if not bundle_dropped:
                continue
            toks = re.findall(r"\[[^\]]*\]|\S+", vt[len(k):])
            kept_t = [x for x in toks if x.strip("[]") not in bundle_dropped and x not in bundle_dropped]
            if len(kept_t) == len(toks):
                continue
            nt = (k + " " + " ".join(kept_t)) if kept_t else None
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
    body = mod_rename(m, b"".join(pieces).decode("utf-8"))
    what = ("delta bundle: declarations the new statements need that the published bundle "
            f"Def_{published_bundles[m]} does not carry" if is_delta
            else "definition bundle: declarations the uploaded statements rest on")
    header = HEADER + gen_note(m, what)
    imps = "\n".join([f"import {x}" for x in ext_imports(m)] + bundle_imports(m, include_self=is_delta, exclude_delta_of=m)
                     + [f"import Theorems.Thm_{sl}" for sl in bundle_node_imports.get(m, [])]
                     + [f"import Theorems.Thm_{slugs[v]}" for v in sorted(bundle_node_deps.get(m, []), key=lambda v: slugs[v])])
    nattr = node_attr_lines(set(bundle_node_deps.get(m, [])) | {uid for uid, uu in U.items() if uu["cls"] == "pubnode" and slugs.get(uid) in pub_imp})
    if nattr:
        imps += "\n\n" + "\n".join(nattr)
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
    return mod_rename(u["module"], txt(u["module"], u["decl"]["declStart"]["offset"], u["decl"]["declEnd"]["offset"]))

def head_rest(uid, upto):
    """Text from after the binding name up to `upto` ('val' = valStart, 'end' = declEnd)."""
    u = U[uid]
    assert u["bind"], u["name"]
    a = u["bind"]["end"]["offset"]
    b = u["decl"]["valStart"]["offset"] if upto == "val" else u["decl"]["declEnd"]["offset"]
    return mod_rename(u["module"], txt(u["module"], a, b))

def hoisted_context(uid):
    """Top-level `open`/`variable` lines reproducing the resolution scope of a declaration."""
    u = U[uid]
    ctx = unit_ctx(uid)
    chain = ctx["ns"]
    full_ns = ".".join(u["name"].split(".")[:-1])
    env = stub_env_ns(u["module"])
    lines = []
    parts = full_ns.split(".") if full_ns else []
    for i in range(1, len(parts) + 1):
        p = ".".join(parts[:i])
        if p in env:
            lines.append(f"open {p}")
    for o in ctx["opens"]:
        o = filter_open(u["module"], o, lambda v: U[v]["cls"] in ("defmat", "embedded", "avail"))
        r = prune_open(u["module"], o, chain, env, absolute=True) if o is not None else None
        if r is not None and r not in lines:
            lines.append(r)
    lines += ctx["opts"]
    lines += filter_vars(u["module"], ctx["vars"], lambda v: U[v]["cls"] in ("defmat", "embedded", "avail"))
    return lines

def attr_lines(uid, available):
    """The attribute commands in effect at a declaration, restricted to targets the file can see."""
    out = []
    for at in unit_ctx(uid)["attrs"]:
        names = [tok if tu is None else const for tok, tu, const in at["names"] if tu is None or available(tu)]
        attr = replayable(at["attr"])
        if names and attr:
            out.append(f"attribute {attr} " + " ".join(dict.fromkeys(names)))
    return out

def pasted_block(uid, available, env_ns):
    """A helper declaration with its scope: namespace, then a section (noncomputable when the source
    declares it inside one, so that a pasted definition compiles as in the source) holding the `open`,
    `set_option`/`universe` and `variable` lines and the attribute commands in effect (a `local instance`
    of the source's section must not reach a helper from a section without it: the instance found for
    a statement would differ from the source's), so that none of them leaks into the next block."""
    ctx = unit_ctx(uid)
    ns = ns_of_chain(ctx["ns"])
    body = []
    if ns:
        body.append(f"namespace {ns}")
    body.append("noncomputable section" if ctx.get("nc") else "section")
    env = env_ns
    for o in ctx["opens"]:
        o = filter_open(U[uid]["module"], o, available)
        o = prune_open(U[uid]["module"], o, ctx["ns"], env) if o is not None else None
        if o is not None:
            body.append(o)
    body += ctx["opts"]
    body += filter_vars(U[uid]["module"], ctx["vars"], available)
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
    # the namespaces of the solution's imports: the stub's bundles and the imported nodes' theorems
    sol_env = stub_env_ns(m) | env_ns_of(c["imported_nodes"])
    nattr = node_attr_lines(c["imported_nodes"])
    if nattr:
        sol_parts += nattr + [""]
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
            sol_parts.append(pasted_block(e[3], available, sol_env | env_ns_of(emitted)))
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
    env = sol_env | env_ns_of(emitted)
    if sol_ns:
        sol_parts.append(f"namespace {sol_ns}")
    for o in sctx["opens"]:
        o = filter_open(u["module"], o, available)
        o = prune_open(u["module"], o, sctx["ns"], env) if o is not None else None
        if o is not None:
            sol_parts.append(o)
    sol_parts += sctx["opts"] + filter_vars(u["module"], sctx["vars"], available)
    sol_parts += attr_lines(uid, available)
    if extra_open and extra_open in env:
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
