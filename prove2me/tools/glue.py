#!/usr/bin/env python3
"""The top of the dependency graph of MIP* = RE as platform items: three Open leaves and the glue
sketches that assemble the main theorem and its consequences from the own-code assembly layer.

Read with the same ``P2M_CONFIG`` as plan.py / gen.py, after both have run (it needs plan.json
for the bundle map and tree.json for the generated stubs).  Writes into the workspace:

* ``Theorems/Thm_<leaf>.lean`` for the three leaves ``Nonempty (Introspection 7)``,
  ``Nonempty (AnswerReduction 5)``, ``Nonempty (Repetition 7)`` (no solution: their witnesses are
  the stage instances whose bodies the platform cannot host yet);
* for every conditional theorem of ``MIPRE/Background/Pipeline.lean`` at the source commit (the
  consequences of answer reduction alone), a stub with the explicit binder ``(A : AnswerReduction 5)``
  and a solution that is the source's own one-line body with ``GapCompression.ofAnswerReduction A``
  spelled out as ``GapCompression.ofPipeline`` applied to the chosen witnesses of the two leaves;
* for every unconditional theorem of ``MIPRE/MainTheorem.lean``, a solution that is the source's
  body with the answer-reduction instance replaced by the chosen witness of its leaf (the stub of
  the goal is already published; the other stubs are generated here).

The statement texts are copied from the two source files, which cannot be elaborated in the
workspace (their proofs import the vendored trees), so the one textual step is cutting each
declaration at its first ``:=``; the compiler checks every generated file against the stubs and
bundles.  Output manifest: ``glue.json`` next to tree.json.
"""
import json, os, re, subprocess, sys

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
REPO_DIR = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REPO, COMMIT = "vidick/MIPRE-formalization", "70cbf1c"
CFG = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8"))
plan = json.load(open(CFG["out"], encoding="utf-8"))
tree = json.load(open(CFG["tree_out"], encoding="utf-8"))
A = os.path.dirname(CFG["tree_out"])
rows = [json.loads(l) for l in open(f"{CFG['extract_dir']}/decl_graph.jsonl", encoding="utf-8") if l.strip()]
module_of = {r["name"]: r["module"] for r in rows}

def git_show(path):
    return subprocess.check_output(["git", "-C", REPO_DIR, "show", f"{COMMIT}:{path}"], text=True)

# ---------- bundle map (as in gen.py) ----------
imports, mod_closure = plan["imports"], {m: set(v) for m, v in plan["mod_closure"].items()}
def topo():
    order, seen = [], set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in imports[m]["proj"]: visit(d)
        order.append(m)
    for m in plan["modules"]: visit(m)
    return order
TOPO = topo()
def bundle_names(d):
    out = []
    if d in plan["published_bundles"]: out.append(f"Definitions.Def_{plan['published_bundles'][d]}")
    if d in plan["delta_bundles"]: out.append(f"Definitions.Def_{plan['delta_bundles'][d]}")
    if d in plan["new_bundles"]: out.append(f"Definitions.Def_{d.replace('.', '_')}")
    return out
def import_lines(consts, stubs):
    """Imports giving the modules of `consts` (with their closures) and the stubs named."""
    mods = set()
    for c in consts:
        m = module_of.get(c)
        if m is None:
            sys.exit(f"glue: constant {c} is not in the extracted closure")
        mods |= mod_closure[m] | {m}
    ext = sorted({x for m in mods for x in imports[m]["ext"]})
    lines = [f"import {x}" for x in ext] + [f"import {b}" for d in TOPO if d in mods for b in bundle_names(d)]
    lines += [f"import Theorems.Thm_{s}" for s in stubs]
    return lines

HEADER = ("/-\nCopyright (c) 2026 Thomas Vidick. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Thomas Vidick\n-/\n")
def note(what, src):
    return (f"/- Generated for Prove2Me from {REPO}@{COMMIT}, {src} ({what});\n"
            f"   produced by prove2me/tools/glue.py: the statement is the source's, the proof term is the\n"
            f"   source's with the stage instances replaced by the witnesses of the Nonempty leaves. -/\n")
slug = lambda n: n.replace(".", "_")
generated, items = [], []
def emit(rel, text):
    fn = f"{WS}/{rel}"
    if not (os.path.exists(fn) and open(fn, encoding="utf-8").read() == text):
        open(fn, "w", encoding="utf-8").write(text)
    generated.append(rel)

# ---------- the three leaves ----------
LEAVES = [
    ("MIPRE.Introspection.nonempty_seven", "Nonempty (MIPRE.Introspection 7)", "MIPRE.Introspection",
     "MIPRE.Introspection.seven", "MIPRE/Background/Introspection/Compiler.lean"),
    ("MIPRE.AnswerReduction.nonempty_five", "Nonempty (MIPRE.AnswerReduction 5)", "MIPRE.AnswerReduction",
     "MIPRE.AnswerReduction.answerReduction", "MIPRE/Background/AnswerReduction/Instance.lean"),
    ("MIPRE.Repetition.nonempty_seven", "Nonempty (MIPRE.Repetition 7)", "MIPRE.Repetition",
     "MIPRE.repetition", "MIPRE/Background/Repetition/Verifier.lean"),
]
for name, stmt, struct, witness, wfile in LEAVES:
    pre = import_lines([struct], [])
    formal = f"theorem {name} : {stmt} := by sorry"
    emit(f"Theorems/Thm_{slug(name)}.lean", HEADER + note(f"Open leaf: the stage instance {witness} as an existence statement", wfile)
         + "\n".join(pre) + "\n\n" + formal + "\n")
    items.append({"theorem_name": name, "slug": slug(name), "kind": "leaf", "formal_statement": formal,
                  "preamble": "\n".join(pre), "stub_file": f"Theorems/Thm_{slug(name)}.lean", "solution_file": None,
                  "imported_nodes": [], "witness": witness, "source": {"file": wfile, "commit": COMMIT}})

# ---------- textual cut of the two glue files ----------
def declarations(text):
    """[(name, head, body, start_line, end_line, namespace)] for every top-level `theorem` of a file whose
    declarations are separated by blank lines; the cut is at the first `:=` of the declaration."""
    lines = text.split("\n")
    ns, out, i = [], [], 0
    while i < len(lines):
        l = lines[i]
        if l.startswith("namespace "):
            ns.append(l.split()[1])
        elif re.match(r"^end( |$)", l):
            if ns: ns.pop()
        elif l.startswith("theorem "):
            j = i
            while j + 1 < len(lines) and lines[j + 1].strip() != "":
                j += 1
            decl = "\n".join(lines[i:j + 1])
            name = decl.split()[1]
            cut = decl.index(":=")
            head = decl[len("theorem ") + len(name):cut].rstrip()
            body = decl[cut + 2:].strip()
            out.append((name, head, body, i + 1, j + 1, ".".join(ns)))
            i = j
        i += 1
    return out

pipeline = git_show("MIPRE/Background/Pipeline.lean")
main = git_show("MIPRE/MainTheorem.lean")
OF_PIPELINE = ("(MIPRE.GapCompression.ofPipeline MIPRE.Introspection.nonempty_seven.some A "
               "MIPRE.Repetition.nonempty_seven.some)")
STMT_CONSTS = ["MIPRE.AnswerReduction", "MIPRE.quantumValue", "MIPRE.IsRE", "MIPRE.MIPStarComputable",
               "MIPRE.MIPStar", "MIPRE.Cost.BitStr", "HaltingGameValue.GameData", "HaltingGameValue.gameValue",
               "HaltingGameValue.HaltsOnEmptyInput", "HaltingGameValue.HaltingReducesToGameValue"]
BODY_CONSTS = ["MIPRE.GapCompression.ofPipeline", "MIPRE.Cost.selfUniversal", "MIPRE.Cost.selfClockedUniversal"]
OPENS = "open MIPRE MIPRE.Halting MIPRE.Cost\n"

cond = declarations(pipeline)
assert cond and all(ns == "MIPRE.Halting" for *_, ns in cond), [c[0] for c in cond]
cond_names = []
for name, head, body, a, b, ns in cond:
    full = f"MIPRE.Halting.{name}"
    assert name.endswith("_of_answerReduction"), name
    target = f"MIPRE.Halting.{name[:-len('_answerReduction')]}"  # the own-code theorem it applies
    if target not in module_of:
        sys.exit(f"glue: {target} not in the extracted closure")
    tslug = slug(target)
    if tslug not in {n["slug"] for n in tree["nodes"]}:
        sys.exit(f"glue: {target} is not a generated node (check the plan's targets)")
    formal = f"theorem {full} (A : MIPRE.AnswerReduction 5){head} := by sorry"
    pre = import_lines(STMT_CONSTS, []) + ["", "open MIPRE MIPRE.Cost"]   # MIPRE.Halting exists only with the proof's imports
    emit(f"Theorems/Thm_{slug(full)}.lean", HEADER + note(f"statement stub of {full}, binder A made explicit", "MIPRE/Background/Pipeline.lean")
         + "\n".join(pre) + "\n\n" + formal + "\n")
    body2 = body.replace("(GapCompression.ofAnswerReduction A)", OF_PIPELINE).replace("GapCompression.ofAnswerReduction A", OF_PIPELINE)
    assert body2 != body, name
    sol_imports = import_lines(STMT_CONSTS + BODY_CONSTS,
                               [tslug, slug("MIPRE.Introspection.nonempty_seven"), slug("MIPRE.Repetition.nonempty_seven")])
    sol = (HEADER + note(f"sketch of {full}", "MIPRE/Background/Pipeline.lean") + "\n".join(sol_imports) + "\n\n" + OPENS
           + f"\ntheorem solution (A : MIPRE.AnswerReduction 5){head} :=\n  {body2}\n")
    emit(f"Solutions/Sol_{slug(full)}.lean", sol)
    items.append({"theorem_name": full, "slug": slug(full), "kind": "conditional", "formal_statement": formal,
                  "preamble": "\n".join(pre), "stub_file": f"Theorems/Thm_{slug(full)}.lean",
                  "solution_file": f"Solutions/Sol_{slug(full)}.lean",
                  "imported_nodes": [target, "MIPRE.Introspection.nonempty_seven", "MIPRE.Repetition.nonempty_seven"],
                  "source": {"file": "MIPRE/Background/Pipeline.lean", "lines": [a, b], "commit": COMMIT}})
    cond_names.append(full)

uncond = declarations(main)
for name, head, body, a, b, ns in uncond:
    full = f"{ns}.{name}" if ns else name
    body2 = re.sub(r"(?<![A-Za-z0-9_.])(?:MIPRE\.)?AnswerReduction\.answerReduction(?![A-Za-z0-9_'])",
                   "MIPRE.AnswerReduction.nonempty_five.some", body)
    body2 = re.sub(r"(?<![A-Za-z0-9_.])(?:MIPRE\.)?gapCompression(?![A-Za-z0-9_'])",
                   "(MIPRE.GapCompression.ofPipeline MIPRE.Introspection.nonempty_seven.some "
                   "MIPRE.AnswerReduction.nonempty_five.some MIPRE.Repetition.nonempty_seven.some)", body2)
    assert body2 != body, name
    used = [c for c in cond_names if c.split(".")[-1] in body2]
    published_stub = full == "HaltingGameValue.halting_reduces_to_gameValue"
    opens = OPENS if ns.startswith("MIPRE") else "open MIPRE\n"
    pre = import_lines(STMT_CONSTS, []) + ["", "open MIPRE MIPRE.Cost" if ns.startswith("MIPRE") else "open MIPRE"]
    formal = f"theorem {full}{head} := by sorry"
    if not published_stub:
        emit(f"Theorems/Thm_{slug(full)}.lean", HEADER + note(f"statement stub of {full}", "MIPRE/MainTheorem.lean")
             + "\n".join(pre) + "\n\n" + formal + "\n")
    sol_imports = import_lines(STMT_CONSTS + BODY_CONSTS, [slug(c) for c in used] + [slug("MIPRE.AnswerReduction.nonempty_five")])
    sol = (HEADER + note(f"sketch of {full}", "MIPRE/MainTheorem.lean") + "\n".join(sol_imports) + "\n\n" + opens
           + f"\ntheorem solution{head} :=\n  {body2}\n")
    emit(f"Solutions/Sol_{slug(full)}.lean", sol)
    items.append({"theorem_name": full, "slug": slug(full), "kind": "unconditional", "formal_statement": formal,
                  "preamble": "\n".join(pre), "stub_file": None if published_stub else f"Theorems/Thm_{slug(full)}.lean",
                  "stub_published": published_stub, "solution_file": f"Solutions/Sol_{slug(full)}.lean",
                  "imported_nodes": used + ["MIPRE.AnswerReduction.nonempty_five"],
                  "source": {"file": "MIPRE/MainTheorem.lean", "lines": [a, b], "commit": COMMIT}})

json.dump({"items": items, "generated": generated}, open(f"{A}/glue.json", "w", encoding="utf-8"), indent=1)
print(f"glue: {len(LEAVES)} leaves, {len(cond)} conditional, {len(uncond)} unconditional items; {len(generated)} files; {A}/glue.json")
