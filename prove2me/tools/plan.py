#!/usr/bin/env python3
"""Phase 2 of the Prove2Me full-project upload: plan the node set.

Reads Stage 1 (decl_graph.jsonl) and Stage 2 (sketch_info.<Base>.jsonl) facts of a closure and
writes plan.json.  Every position fact comes from the two Lean extractors; this script never
parses Lean code beyond the import header lines.

Configuration: ``P2M_CONFIG`` names a JSON file (see ``prove2me/assembly/config.json``); without
it the script plans the recursive-compression closure exactly as on 2026-10-12.  A configuration
may also name content that is *already published* (an earlier tree.json and extra bundles): its
theorems are forced to be nodes that the new solutions import, and its bundles' declarations are
available by import, so a module whose published bundle lacks a declaration the new statements
need gets a *delta bundle* with just the missing declarations.
"""
import os, json, re, sys, collections

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"

DEFAULT_CFG = {
    "extract_dir": f"{S}/extract",
    "out": f"{S}/plan.json",
    "targets": [
        "MIPRE.Cost.recursive_compression",
        "MIPRE.Cost.recursive_compression_halting",
        "MIPRE.Cost.compressibility_criterion",
        "MIPRE.Cost.compressibility_criterion_levels",
        "MIPRE.Cost.compressibility_criterion_nested",
        "MIPRE.Cost.compressibility_criterion_halting",
        "MIPRE.Cost.exists_efficient_universal",
        "MIPRE.Cost.exists_clocked_universal",
        "MIPRE.Cost.efficient_fixed_point",
        "MIPRE.Cost.PolyTimeFun.smn",
        "MIPRE.Cost.IsSuccinctDesc",
    ],
    # declarations the blueprint names with \lean{} (promotion signal: "named in the source")
    "blueprint_names": [
        "MIPRE.Cost.IsSuccinctDesc", "MIPRE.Cost.bitQueryAnswer", "MIPRE.Cost.compressibility_criterion",
        "MIPRE.Cost.compressibility_criterion_levels", "MIPRE.Cost.compressibility_criterion_nested",
        "MIPRE.Cost.compressibility_criterion_halting", "MIPRE.Cost.recursive_compression_halting",
        "MIPRE.Cost.efficient_fixed_point", "MIPRE.Cost.exists_clocked_universal",
        "MIPRE.Cost.exists_efficient_universal", "MIPRE.Cost.hardcode_size", "MIPRE.Cost.hardcode_time",
        "MIPRE.Cost.hardcode_time_rev", "MIPRE.Cost.kleeneFix", "MIPRE.Cost.kleeneFix_runs_of",
        "MIPRE.Cost.recursive_compression", "MIPRE.Cost.smn_polyTime", "MIPRE.Cost.PolyTimeFun.smn",
    ],
    # definitions that must be definition material (data the glue sketches apply), even when no
    # uploaded statement mentions them
    "defmat_targets": [],
    # already published content: an earlier tree.json (its nodes and bundles) and extra bundles
    "published_tree": None,
    "published_bundles": [],   # [{"module": ..., "definition_name": ..., "kept": "all" | [names]}]
    # the 2026-10-12 run seeded reachability with the blueprint names and forced them to be nodes;
    # a layer with hundreds of blueprint names uses them as a promotion signal only
    "blueprint_seeds": True,
    "force_blueprint_nodes": True,
    # platform names must be ASCII identifiers: {"old.full.name": "new.full.name"}
    "renames": {},
}
CFG = dict(DEFAULT_CFG)
if os.environ.get("P2M_CONFIG"):
    CFG.update(json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8")))
E = CFG["extract_dir"]
OUT = CFG["out"]
TARGETS = list(CFG["targets"])
BLUEPRINT_NAMES = set(CFG["blueprint_names"])
DEFMAT_TARGETS = list(CFG["defmat_targets"])
NODE_MIN = 40      # proof lines strictly above this -> node
INLINE_MAX = 10    # proof lines at most this -> inline (unless the statement needs it)


def module_path(m):
    return m.replace(".", "/") + ".lean"

def load_rows():
    rows = [json.loads(l) for l in open(f"{E}/decl_graph.jsonl", encoding="utf-8") if l.strip()]
    return rows

def load_facts(modules):
    facts = {}
    for m in modules:
        # Stage 2 fact files are named by the full module name; the 2026-10-12 run used base names
        fn = f"{E}/sketch_info.{m}.jsonl"
        if not os.path.exists(fn):
            fn = f"{E}/sketch_info.{m.split('.')[-1]}.jsonl"
        decls, cmds, refs = [], [], []
        for l in open(fn, encoding="utf-8"):
            if not l.strip():
                continue
            o = json.loads(l)
            {"decl": decls, "cmd": cmds, "ref": refs}[o["kind"]].append(o)
        decls.sort(key=lambda d: d["declStart"]["offset"])
        cmds.sort(key=lambda c: c["start"]["offset"])
        refs.sort(key=lambda r: r["start"]["offset"])
        text = open(f"{WS}/{module_path(m)}", encoding="utf-8").read()
        B = open(f"{WS}/{module_path(m)}", "rb").read()
        facts[m] = {"decls": decls, "cmds": cmds, "refs": refs, "text": text, "bytes": B}
    return facts

def header_imports(text):
    """Project and non-project imports of a module (header lines only)."""
    proj, ext = [], []
    for mm in re.finditer(r"^import\s+(\S+)\s*$", text, re.M):
        (proj if mm.group(1).startswith("MIPRE.") else ext).append(mm.group(1))
    return proj, ext

def load_published():
    """Published nodes {name: slug} and bundles {module: {"definition_name", "kept": set|None}}
    (kept None = every declaration of the module)."""
    nodes, bundles = {}, {}
    trees = ([CFG["published_tree"]] if CFG.get("published_tree") else []) + list(CFG.get("published_trees", []))
    for path in trees:   # every tree uploaded before this one, in upload order
        t = json.load(open(path, encoding="utf-8"))
        for n in t["nodes"]:
            nodes[n["theorem_name"]] = n["slug"]
        gp = os.path.join(os.path.dirname(path), "glue.json")
        if os.path.exists(gp):   # glue items (leaves, sketches, leaf closures) are published theorems too
            for g in json.load(open(gp, encoding="utf-8"))["items"]:
                nodes[g["theorem_name"]] = g["slug"]
        for b in t["bundles"]:
            prev = bundles.get(b["module"])
            kept = set(b["kept"]) | (prev["kept"] if prev and prev["kept"] is not None else set())
            # a later delta bundle (`…_B`) adds declarations to the module's published material; the
            # planner only needs to know which declarations are available by import
            bundles[b["module"]] = {"definition_name": b["definition_name"], "kept": kept,
                                    "delta_of": prev["definition_name"] if prev else b.get("published_bundle")}
    for b in CFG.get("published_bundles", []):
        bundles[b["module"]] = {"definition_name": b["definition_name"],
                               "kept": None if b.get("kept", "all") == "all" else set(b["kept"])}
    return nodes, bundles

def main():
    rows = load_rows()
    modules = sorted({r["module"] for r in rows})
    facts = load_facts(modules)
    by_name = {r["name"]: r for r in rows}
    pub_nodes, pub_bundles = load_published()

    # ---- units: one per Stage 2 decl fact; rows joined by line containment ----
    units = {}
    unit_of_row = {}
    for m in modules:
        for d in facts[m]["decls"]:
            uid = f"{m}:{d['declStart']['offset']}"
            units[uid] = {"id": uid, "module": m, "decl": d, "rows": []}
    orphans = []
    for r in rows:
        if r["startLine"] == 0:
            continue
        m = r["module"]
        hit = None
        for d in facts[m]["decls"]:
            if d["declStart"]["line"] <= r["startLine"] <= d["declEnd"]["line"]:
                hit = f"{m}:{d['declStart']['offset']}"
                break
        if hit is None:
            orphans.append(r["name"])
            continue
        units[hit]["rows"].append(r)
        unit_of_row[r["name"]] = hit
    # primary row of each unit
    for u in units.values():
        d = u["decl"]
        nt = d["nameText"]
        prim = None
        if nt:
            nt2 = nt[len("_root_."):] if nt.startswith("_root_.") else nt
            cands = [r for r in u["rows"] if r["userName"] == nt2 or r["userName"].endswith("." + nt2)]
            # prefer the non-companion (shortest userName)
            cands.sort(key=lambda r: len(r["userName"]))
            prim = cands[0] if cands else None
        if prim is None:
            inst = [r for r in u["rows"] if r["isInstance"]]
            prim = inst[0] if inst else (u["rows"][0] if u["rows"] else None)
        u["primary"] = prim
        u["name"] = prim["name"] if prim else None
        u["kind"] = prim["kind"] if prim else "unknown"
        u["is_thm"] = u["kind"] == "theorem"
        u["is_instance"] = any(r["isInstance"] for r in u["rows"])
        u["is_private"] = bool(prim and prim["isPrivate"])
        vs = d["valStart"]
        u["prooflines"] = (d["declEnd"]["line"] - vs["line"]) if vs else 0
        u["span_lines"] = d["declEnd"]["line"] - d["declStart"]["line"] + 1
        u["has_doc"] = d["docstring"] is not None
        B = facts[u["module"]]["bytes"]
        # binding occurrence of the primary name (Stage 2 ref fact inside the head), if any
        bind = None
        if prim:
            for rf in facts[u["module"]]["refs"]:
                if rf["const"] == prim["name"] and d["declStart"]["offset"] <= rf["start"]["offset"] < (vs["offset"] if vs else d["declEnd"]["offset"]):
                    bind = rf
                    break
        u["bind"] = bind
        head_from = d["docstring"]["end"]["offset"] if d["docstring"] else d["declStart"]["offset"]
        head_to = bind["start"]["offset"] if bind else (vs["offset"] if vs else d["declEnd"]["offset"])
        head = B[head_from:head_to].decode("utf-8", errors="replace")
        u["attr_text"] = re.findall(r"@\[[^\]]*\]", head)
        u["has_attr"] = bool(u["attr_text"])
    unitless_decls = [u["id"] for u in units.values() if not u["rows"]]

    # ---- published content, per unit ----
    pubnode_units, avail_units = set(), set()
    for uid, u in units.items():
        if u["name"] in pub_nodes:
            pubnode_units.add(uid)
        pb = pub_bundles.get(u["module"])
        if pb and (pb["kept"] is None or any(r["name"] in pb["kept"] for r in u["rows"]) or (u["name"] in pb["kept"] if pb["kept"] else False)):
            avail_units.add(uid)

    # ---- reachability ----
    def rows_of_unit(uid):
        return [r["name"] for r in units[uid]["rows"]]
    extra = sorted(n for n in BLUEPRINT_NAMES if n in by_name and n not in TARGETS)
    if CFG["blueprint_seeds"]:
        print("blueprint-named declarations added as targets:", len(extra))
        TARGETS.extend(extra)
    else:
        print("blueprint-named declarations in the closure (promotion signal only):", len(extra))
    seeds = list(TARGETS) + list(DEFMAT_TARGETS) + [r["name"] for r in rows if r["isInstance"]]
    missing_targets = [t for t in TARGETS + DEFMAT_TARGETS if t not in by_name]
    reach = set()
    work = list(seeds)
    while work:
        n = work.pop()
        if n in reach:
            continue
        r = by_name.get(n)
        if r is None:
            continue
        reach.add(n)
        work.extend(r["typeDeps"])
        work.extend(r["valueDeps"])
        uid = unit_of_row.get(n)
        if uid:
            work.extend(rows_of_unit(uid))
    reach_units = {unit_of_row[n] for n in reach if n in unit_of_row}
    # (ref-based deps are added below; close reach_units under them afterwards)

    def unit_deps(uid, which):
        """Units referenced by the given dependency lists of all rows of a unit (excluding itself)."""
        out = set()
        for r in units[uid]["rows"]:
            for d in r[which]:
                v = unit_of_row.get(d)
                if v and v != uid:
                    out.add(v)
                elif v is None and d in by_name and by_name[d]["startLine"] == 0:
                    # spanless companion: traverse through it
                    for dd in by_name[d]["typeDeps"] + by_name[d]["valueDeps"]:
                        vv = unit_of_row.get(dd)
                        if vv and vv != uid:
                            out.add(vv)
        return out
    unit_of_user = {}
    for uid, u in units.items():
        for r in u["rows"]:
            unit_of_user[r["userName"]] = uid
    def ref_unit(const):
        if const in unit_of_row:
            return unit_of_row[const]
        # Stage 2 prints private names with a different prefix: join by the user name
        m = re.match(r"_private\.(?:[^.]+\.)*?\d+\.(.*)$", const)
        if m and m.group(1) in unit_of_user:
            return unit_of_user[m.group(1)]
        return None
    for m in modules:
        refs = facts[m]["refs"]
        for d in facts[m]["decls"]:
            uid = f"{m}:{d['declStart']['offset']}"
            a, b = d["declStart"]["offset"], d["declEnd"]["offset"]
            vs = d["valStart"]["offset"] if d["valStart"] else b
            sr, br = set(), set()
            for rf in refs:
                o = rf["start"]["offset"]
                if o < a or o >= b:
                    continue
                v = ref_unit(rf["const"])
                if v is None or v == uid:
                    continue
                (sr if o < vs else br).add(v)
            units[uid]["stmt_refs"] = sr
            units[uid]["body_refs"] = br
    for uid in units:
        units[uid]["stmt_deps"] = unit_deps(uid, "typeDeps") | units[uid].get("stmt_refs", set())
        units[uid]["body_deps"] = unit_deps(uid, "valueDeps") | units[uid].get("body_refs", set())

    # close reachability under the ref-based dependencies (dsimp lemmas named in proofs); published
    # content is a boundary: what lies behind a published node or bundle declaration is theirs
    def frontier(uid):
        if uid in pubnode_units or uid in avail_units:
            return set()
        return units[uid]["stmt_deps"] | units[uid]["body_deps"]
    changed = True
    while changed:
        changed = False
        for uid in list(reach_units):
            for v in frontier(uid):
                if v not in reach_units:
                    reach_units.add(v); changed = True
    # ---- classification ----
    defmat, embedded = set(), set()
    for uid in reach_units:
        u = units[uid]
        if uid in avail_units or uid in pubnode_units:
            continue
        if not u["is_thm"] and (u["kind"] in ("inductive",) or u["is_instance"]):
            defmat.add(uid)
    for t in DEFMAT_TARGETS:
        uid = unit_of_row.get(t)
        if uid and uid not in avail_units:
            defmat.add(uid)
    # anything referenced by a statement must be importable
    for uid in reach_units:
        if uid in avail_units or uid in pubnode_units:
            continue
        for v in units[uid]["stmt_deps"]:
            if v in avail_units or v in pubnode_units:
                continue
            (embedded if units[v]["is_thm"] else defmat).add(v)
    # simp lemmas with short proofs stay with the definitions (dsimp leaves no trace in proof terms)
    for uid in units:
        u = units[uid]
        if uid in avail_units or uid in pubnode_units:
            continue
        if u["is_thm"] and u["has_attr"] and u["prooflines"] <= INLINE_MAX and not u["is_private"]:
            embedded.add(uid)
    reach_units |= embedded
    # closure: bundles may not import sorry stubs, so bodies of bundle content stay in bundles
    bundle_node_imports = collections.defaultdict(set)  # module -> published nodes its bundle imports
    changed = True
    while changed:
        changed = False
        for uid in list(defmat | embedded):
            for v in units[uid]["body_deps"] | units[uid]["stmt_deps"]:
                if v in avail_units:
                    continue
                if v in pubnode_units:
                    # a published node is Proved on the platform, so a bundle may import its theorem
                    # (the platform rejects only imports of theorems that are not yet Proved)
                    bundle_node_imports[units[uid]["module"]].add(v)
                    continue
                if units[v]["is_thm"]:
                    if v not in embedded:
                        embedded.add(v); changed = True
                else:
                    if v not in defmat:
                        defmat.add(v); changed = True
    reach_units |= defmat | embedded
    bundle_units = defmat | embedded
    # theorems: node / inline
    thm_units = [uid for uid in reach_units if units[uid]["is_thm"] and uid not in embedded
                 and uid not in avail_units and uid not in pubnode_units]
    forced = set(TARGETS) | (BLUEPRINT_NAMES if CFG["force_blueprint_nodes"] else set())
    nodes = set(uid for uid in thm_units if units[uid]["name"] in forced)
    for uid in thm_units:
        u = units[uid]
        if u["is_private"]:
            continue
        if u["prooflines"] > NODE_MIN:
            nodes.add(uid)
    # promotion signals for the 11..40 band, iterated to a fixpoint on "used by >= 2 nodes"
    def consumers(uid, pool):
        return {c for c in pool if uid in units[c]["body_deps"] | units[c]["stmt_deps"]}
    changed = True
    while changed:
        changed = False
        for uid in thm_units:
            u = units[uid]
            if uid in nodes or u["is_private"] or not (INLINE_MAX < u["prooflines"] <= NODE_MIN):
                continue
            cons_all = consumers(uid, reach_units)
            signal = (
                len(consumers(uid, nodes)) >= 2
                or any(units[c]["module"] != u["module"] for c in cons_all)
                or u["has_doc"]
                or u["name"] in BLUEPRINT_NAMES
            )
            if signal:
                nodes.add(uid); changed = True
    inline = set(uid for uid in thm_units if uid not in nodes)
    proofdefs = set(uid for uid in reach_units if not units[uid]["is_thm"] and uid not in defmat
                    and uid not in avail_units)
    dead = set(units) - reach_units
    reach_pub_nodes = reach_units & pubnode_units
    reach_avail = reach_units & avail_units

    # ---- solution composition (what each node's solution pastes and imports) ----
    comp = {}
    for n in nodes:
        pasted, imported_nodes, seen = [], set(), {n}
        def deps(uid):
            return units[uid]["body_deps"] | units[uid]["stmt_deps"]
        frontier_ = list(deps(n))
        while frontier_:
            v = frontier_.pop()
            if v in seen:
                continue
            seen.add(v)
            if v in avail_units:
                pass  # available through the published bundle's import
            elif v in pubnode_units or v in nodes:
                imported_nodes.add(v)
            elif v in bundle_units:
                pass
            elif v in inline or v in proofdefs:
                pasted.append(v)
                frontier_.extend(deps(v))
            else:
                raise RuntimeError(f"{units[v]['name']} reached from node {units[n]['name']} but unclassified")
        comp[n] = {"pasted": pasted, "imported_nodes": sorted(imported_nodes)}

    # ---- module import closure ----
    imports = {}
    for m in modules:
        proj, ext = header_imports(facts[m]["text"])
        imports[m] = {"proj": proj, "ext": ext}
    def closure(m):
        out, work = set(), [m]
        while work:
            x = work.pop()
            for y in imports[x]["proj"]:
                if y not in out:
                    out.add(y); work.append(y)
        return out
    mod_closure = {m: sorted(closure(m)) for m in modules}
    bundle_modules = sorted({units[uid]["module"] for uid in bundle_units})
    delta_bundles = {m: pub_bundles[m]["definition_name"] + "_B" for m in bundle_modules if m in pub_bundles}
    new_bundles = [m for m in bundle_modules if m not in pub_bundles]
    # every published bundle whose module is in the closure is importable content
    published_bundles = {m: pub_bundles[m]["definition_name"] for m in modules if m in pub_bundles}

    RENAMES = CFG.get("renames", {})
    def slug(name):
        return RENAMES.get(name, name).replace(".", "_")
    bad_names = sorted(units[uid]["name"] for uid in nodes if not re.fullmatch(r"[A-Za-z0-9_.]+", RENAMES.get(units[uid]["name"], units[uid]["name"])))

    # ---- report ----
    def nm(uid):
        return units[uid]["name"]
    print(f"rows {len(rows)}, units {len(units)} (unitless decl facts {len(unitless_decls)}), orphan rows {len(orphans)}")
    if orphans:
        print("  orphans:", orphans[:10])
    if missing_targets:
        print("  MISSING TARGETS:", missing_targets)
    print(f"reachable units {len(reach_units)} of {len(units)}; dead {len(dead)}")
    print(f"published nodes reached {len(reach_pub_nodes)}, published bundle declarations reached {len(reach_avail)}")
    print(f"def-material {len(defmat)}, embedded theorems {len(embedded)}, nodes {len(nodes)}, inline {len(inline)}, proof-side defs {len(proofdefs)}")
    print(f"bundles: new {len(new_bundles)}, delta {len(delta_bundles)} (modules with a published bundle that lacks something needed)")
    for m, vs in sorted(bundle_node_imports.items()):
        print(f"  bundle of {m.split('.')[-1]} imports published theorems: {sorted(nm(v).split('.')[-1] for v in vs)}")
    for m in bundle_modules:
        us = [uid for uid in bundle_units if units[uid]["module"] == m]
        lines = sum(units[uid]["span_lines"] for uid in us)
        emb = [nm(uid) for uid in us if uid in embedded and units[uid]["prooflines"] > INLINE_MAX]
        tag = "DELTA" if m in delta_bundles else "new"
        print(f"  {tag:5} {m.split('.')[-1]:22s} units {len(us):3d} lines {lines:5d}  long embedded theorems: {emb[:6]}{'…' if len(emb) > 6 else ''}")
    print("nodes by module:")
    for m in modules:
        ns = sorted((uid for uid in nodes if units[uid]["module"] == m), key=lambda uid: units[uid]["decl"]["declStart"]["offset"])
        if ns:
            print(f"  {m.split('.')[-1]}: " + ", ".join(f"{nm(uid).split('.')[-1]}({units[uid]['prooflines']})" for uid in ns))
    print("solution sizes (node prooflines + pasted span lines), largest first:")
    sizes = []
    for n in nodes:
        pl = sum(units[v]["span_lines"] for v in comp[n]["pasted"])
        sizes.append((units[n]["prooflines"] + pl, units[n]["prooflines"], pl, len(comp[n]["pasted"]), len(comp[n]["imported_nodes"]), nm(n)))
    for s in sorted(sizes, reverse=True)[:15]:
        print(f"  {s[0]:5d} = proof {s[1]:4d} + pasted {s[2]:4d} ({s[3]} units); imports {s[4]} nodes  {s[5]}")
    print("proof-side defs (pasted into solutions):", [nm(u) for u in proofdefs][:20])
    print("private units reachable:", [nm(u) for u in reach_units if units[u]["is_private"]])
    print("node names needing renames:", bad_names)
    print("nodes with attributes:", [(nm(u), units[u]["attr_text"]) for u in nodes if units[u]["has_attr"]])

    def cls(uid):
        if uid in avail_units and uid in reach_units: return "avail"
        if uid in pubnode_units and uid in reach_units: return "pubnode"
        if uid in nodes: return "node"
        if uid in inline: return "inline"
        if uid in defmat: return "defmat"
        if uid in embedded: return "embedded"
        if uid in proofdefs: return "proofdef"
        return "dead"
    plan = {
        "targets": TARGETS,
        "defmat_targets": DEFMAT_TARGETS,
        "modules": modules,
        "mod_closure": mod_closure,
        "imports": imports,
        "bundles": bundle_modules,
        "new_bundles": new_bundles,
        "delta_bundles": delta_bundles,
        "published_bundles": published_bundles,
        "published_nodes": {uid: pub_nodes[units[uid]["name"]] for uid in reach_pub_nodes},
        "bundle_imported_nodes": {m: sorted(pub_nodes[units[v]["name"]] for v in vs) for m, vs in bundle_node_imports.items()},
        "units": {uid: {
            "id": uid, "module": u["module"], "name": u["name"], "kind": u["kind"], "is_thm": u["is_thm"],
            "is_instance": u["is_instance"], "is_private": u["is_private"], "prooflines": u["prooflines"],
            "span_lines": u["span_lines"], "has_doc": u["has_doc"], "has_attr": u["has_attr"], "attr_text": u["attr_text"],
            "decl": u["decl"], "bind": u["bind"], "rows": [r["name"] for r in u["rows"]],
            "stmt_deps": sorted(u["stmt_deps"]), "body_deps": sorted(u["body_deps"]),
            "cls": cls(uid),
        } for uid, u in units.items()},
        "nodes": sorted(nodes, key=lambda uid: (units[uid]["module"], units[uid]["decl"]["declStart"]["offset"])),
        "composition": comp,
        "slugs": {**{uid: slug(units[uid