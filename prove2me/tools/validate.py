#!/usr/bin/env python3
"""Phase 5: pretty-print the elaborated type of every uploaded statement in the original tree, in
the stub tree and in its solution, and diff.  Also records the axioms of every solution.

    P2M_CONFIG=prove2me/assembly/config.json python3 prove2me/tools/validate.py [--jobs 4]
    P2M_CONFIG=… python3 prove2me/tools/validate.py --phase orig        # needs the source oleans
    P2M_CONFIG=… python3 prove2me/tools/validate.py --phase stubs       # needs the stub oleans
    P2M_CONFIG=… python3 prove2me/tools/validate.py --phase solutions --compile [--jobs 3]

The original type is read from the node's source module (the workspace holds the source closure),
under the declaration's source name (one node is renamed for the platform: `classV_game_μ`).  Glue
items (``<tree dir>/glue.json``) are checked too: a conditional or unconditional glue theorem keeps
its source statement, so all three types must agree; a leaf (`Nonempty (MIPRE.Introspection 7)`)
has no source declaration and no solution, so only its stub is recorded.  Every solution may
depend on `sorryAx` locally, since the stubs it imports are `sorry`; any axiom outside
`propext`, `Classical.choice`, `Quot.sound` and `sorryAx` is reported.

The phases cache their results in <tree dir>/validation-orig.json, validation-stubs.json and
validation-solutions.jsonl, so that a large tree is checked in steps that fit the session's disk:
the source types are read while the source closure's oleans exist (they can be archived afterwards),
and with --compile each solution is compiled from a copy with the check appended, which is deleted
afterwards, so no solution olean is ever written (nothing imports a solution).  A rerun of the solutions
phase skips the solutions already recorded as identical (--redo checks them again).  validation.json,
the summary every tree has, is written once the three are complete.  `--phase all` (the default)
runs the three in order from scratch, as before.
"""
import argparse, os, json, subprocess, re, sys, time
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_setup   # module-setup files for the --compile path

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
TOOLCHAIN = f"{S}/toolchain/bin"
CFG = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8")) if os.environ.get("P2M_CONFIG") else {}
TREE = CFG.get("tree_out", f"{S}/tree.json")
A = os.path.dirname(TREE)
VOUT = os.path.join(A, "validation.json")
ORIG_OUT = os.path.join(A, "validation-orig.json")
STUB_OUT = os.path.join(A, "validation-stubs.json")
SOL_OUT = os.path.join(A, "validation-solutions.jsonl")
ap = argparse.ArgumentParser()
ap.add_argument("--jobs", type=int, default=4)
ap.add_argument("--phase", choices=["all", "orig", "stubs", "solutions"], default="all")
ap.add_argument("--compile", action="store_true",
                help="solutions: compile a copy of each solution with the check appended (no olean is written)")
ap.add_argument("--redo", action="store_true", help="solutions: check again the solutions already recorded")
ap.add_argument("--wave-order", default=None,
                help="solutions: check them in the upload's wave order, read from this staged tree directory "
                     "(relative to the repository), so that an upload gated on the check can run alongside it")
ap.add_argument("--orig-from", default=None,
                help="orig: read the source types from this dump (tools/orig_types.lean) instead of elaborating "
                     "the source modules, so the phase needs no source olean")
args = ap.parse_args()

tree = json.load(open(TREE, encoding="utf-8"))
glue = json.load(open(os.path.join(A, "glue.json"), encoding="utf-8"))["items"] if os.path.exists(os.path.join(A, "glue.json")) else []
os.makedirs(f"{WS}/Check", exist_ok=True)
env = dict(os.environ, PATH=TOOLCHAIN + ":" + os.environ["PATH"])
OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound", "sorryAx"}

def module_of_path(p):
    return p[:-5].replace("/", ".")

# the items: (platform name, source name or None, source module or None, slug, has solution)
items = []
for n in tree["nodes"]:
    items.append({"name": n["theorem_name"], "source_name": n.get("source_name", n["theorem_name"]),
                  "module": n["module"], "slug": n["slug"], "solution": n["solution_file"] is not None, "kind": "node"})
for g in glue:
    # a leaf (`Nonempty (MIPRE.Introspection 7)`) and a leaf closure (its later solution) have no source
    # declaration: the statement is synthetic, so only stub and solution are compared
    synthetic = g["kind"] in ("leaf", "leaf-closure")
    items.append({"name": g["theorem_name"], "source_name": None if synthetic else g["theorem_name"],
                  "module": None if synthetic else module_of_path(g["source"]["file"]),
                  "slug": g["slug"], "solution": g.get("solution_file") is not None, "kind": "glue-" + g["kind"]})

PP = '''
open Lean Meta in
def ppType (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let f ← ppExpr ci.type
  return f.pretty 100000

open Lean Meta in
def ppTypeAll (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let o := (((← getOptions).setBool `pp.all true).set `pp.maxSteps (100000000 : Nat)).setBool `pp.deepTerms true
  let f ← withTheReader Core.Context (fun c => { c with options := o }) (ppExpr ci.type)
  return f.pretty 1000000000
'''

def run_lean(path):
    r = subprocess.run(["lake", "env", "lean", path], cwd=WS, env=env, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr

def write_check(name, imports, pairs, explicit=False):
    # one `run_meta` block per 40 names: a single block of 500 statements exceeds the elaborator's
    # recursion depth (the repetition tree has 515 nodes)
    body = "\n".join(f"import {i}" for i in imports) + "\n" + PP
    for k in range(0, len(pairs), 40):
        body += "\nrun_meta do\n"
        for (n, lab) in pairs[k:k + 40]:
            body += f'  IO.println s!"{lab} :: {{← ppType `{n}}}"\n'
            if explicit:
                body += f'  IO.println s!"{lab}#ALL :: {{← ppTypeAll `{n}}}"\n'
    open(f"{WS}/Check/{name}.lean", "w", encoding="utf-8").write(body)
    return f"Check/{name}.lean"

def parse(out):
    """`label :: type` lines; a type the pretty-printer breaks over several lines is joined back."""
    d, cur = {}, None
    for l in out.splitlines():
        if " :: " in l and not l.startswith(" "):
            cur, t = l.split(" :: ", 1)
            d[cur] = t
        elif cur is not None and l.startswith(" "):
            d[cur] += "\n" + l
    return d

# original tree: the source modules of the items that have a source declaration.  A source module
# outside the workspace (the glue theorems live in `MIPRE/Background/Pipeline.lean` and
# `MIPRE/MainTheorem.lean`, which depend on the vendored trees) cannot be elaborated here; those
# statements are verbatim textual cuts of the source (glue.py), and are checked as text below.
def in_workspace(module):
    return os.path.exists(f"{WS}/.lake/build/lib/lean/{module.replace('.', '/')}.olean")

def phase_orig():
  if args.orig_from:
    # the dump keys the types by source name, in the same `name :: type` form as the check output
    dump = parse(open(args.orig_from, encoding="utf-8").read())
    with_src = [it for it in items if it["source_name"] and it["source_name"] in dump]
    textual = [it for it in items if it["source_name"] and it["source_name"] not in dump]
    orig, rc = {it["name"]: dump[it["source_name"]] for it in with_src}, 0
    print(f"original types read from {args.orig_from}")
  else:
    with_src = [it for it in items if it["source_name"] and in_workspace(it["module"])]
    textual = [it for it in items if it["source_name"] and not in_workspace(it["module"])]
    p = write_check("Orig", sorted({it["module"] for it in with_src}), [(it["source_name"], it["name"]) for it in with_src])
    rc, out = run_lean(p)
    orig = parse(out)
  # a field another project published under a different name is renamed in the generated copies
  # (config `token_renames`); the source's types are read with the same renaming
  for o, n in CFG.get("token_renames", {}).items():
      orig = {k: re.sub(r"(?<![\w'])" + re.escape(o) + r"(?![\w'])", n, v) for k, v in orig.items()}
  print("original tree:", rc, len(orig), "types of", len(with_src))
  if rc != 0:
      print(out[:3000])
  return phase_orig_rest(orig, with_src, textual, rc)
# textual check of the glue statements against the source at the pinned commit
COMMIT = "70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed"
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
def source_head(path, short):
    src = subprocess.run(["git", "show", f"{COMMIT}:{path}"], cwd=REPO, capture_output=True, text=True).stdout
    m = re.search(r"^theorem " + re.escape(short) + r"\b(.*?):=", src, re.S | re.M)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else None
glue_by_name = {g["theorem_name"]: g for g in glue}

def textual_checks(textual):
  text_bad = 0
  for it in textual:
    g = glue_by_name[it["name"]]
    head = source_head(g["source"]["file"], it["name"].split(".")[-1])
    stub_head = re.sub(r"\s+", " ", g["formal_statement"].split(":= by sorry")[0]).strip()
    ok = head is not None and head in stub_head
    text_bad += 0 if ok else 1
    print(("textual OK  " if ok else "TEXTUAL DIFFERS") + f" {it['name']} (source {g['source']['file']}, not in the workspace)")
    if not ok:
        print("  source:", head)
        print("  stub  :", stub_head)
  return text_bad

def phase_orig_rest(orig, with_src, textual, rc):
  res = {"orig": orig, "with_src": [it["name"] for it in with_src], "textual_checked": [it["name"] for it in textual],
         "textual_mismatch": textual_checks(textual), "rc": rc}
  json.dump(res, open(ORIG_OUT, "w", encoding="utf-8"), indent=1)
  return res

def load(path, phase):
  if not os.path.exists(path):
    sys.exit(f"{path} is missing: run --phase {phase} first")
  return json.load(open(path, encoding="utf-8"))

def phase_stubs(o):
  # stub tree
  p = write_check("Stubs", [f"Theorems.Thm_{it['slug']}" for it in items], [(it["name"], it["name"]) for it in items],
                  explicit=True)
  rc, out = run_lean(p)
  both = parse(out)
  # the default print is compared with the source's (the dump is printed so); the explicit one
  # (pp.all), which no notation of the environment affects, with each solution's
  stubs = {k: v for k, v in both.items() if not k.endswith("#ALL")}
  stubs_all = {k[:-4]: v for k, v in both.items() if k.endswith("#ALL")}
  print("stub tree:", rc, len(stubs), "types of", len(items))
  if rc != 0:
      print(out[:3000])
  bad, priv = 0, []
  for name in o["with_src"]:
      a, b = o["orig"].get(name), stubs.get(name)
      if a != b:
          # a statement naming a private declaration prints it `name✝` in the source; the generated
          # copy of that declaration is public, so the stub prints it bare: the same statement
          if a is not None and b is not None and a.replace("✝", "") == b.replace("✝", ""):
              priv.append(name)
              continue
          bad += 1
          print("STUB TYPE DIFFERS:", name)
          print("  orig:", a)
          print("  stub:", b)
  print("stub types identical to the original:", len(o["with_src"]) - bad, "of", len(o["with_src"]),
        f"({len(priv)} of them up to the `✝` of a private declaration the copies make public)")
  for it in items:
      if not it["source_name"]:
          print("leaf (no source declaration):", it["name"], "::", stubs.get(it["name"]))
  res = {"stubs": stubs, "stubs_all": stubs_all, "stub_mismatch": bad, "stub_private_marker_only": priv, "rc": rc}
  json.dump(res, open(STUB_OUT, "w", encoding="utf-8"), indent=1)
  return res

# solutions: one run each (every solution declares `solution`)
def check_body(it):
    return (f"import Solutions.Sol_{it['slug']}\n" + PP +
            '\nrun_meta do\n  IO.println s!"T :: {← ppType `solution}"\n'
            '#print axioms solution\n')

def parse_check(out):
    """(default print, explicit print or None, axioms)."""
    ta = [l[len("TALL :: "):] for l in out.splitlines() if l.startswith("TALL :: ")]
    t = list(parse("\n".join(l for l in out.splitlines() if l.startswith("T :: ") or l.startswith(" "))).values())
    ax = re.search(r"'solution' depends on axioms: \[([^\]]*)\]", out)
    if ax:
        axs = ax.group(1)
    elif "'solution' does not depend on any axioms" in out:
        axs = ""
    else:
        axs = out.strip()[-300:]   # the check itself failed: reported as an unexpected "axiom"
    return (t[0] if t else None), (ta[0] if ta else None), axs

def check_solution(it):
    path = f"Check/Sol_{it['slug']}.lean"
    open(f"{WS}/{path}", "w", encoding="utf-8").write(check_body(it))
    rc, out = run_lean(path)
    t, TALL[it["name"]], axs = parse_check(out)
    return it, rc, t, axs, out

def remove(p):
    try:
        os.remove(p)
    except OSError:
        pass

SECS = {}   # solution -> seconds its checked copy took to compile
TALL = {}   # solution -> its type printed with pp.all
CHECK_TAIL = PP + ('\nrun_meta do\n  IO.println s!"T :: {← ppType `solution}"\n'
                   '  IO.println s!"TALL :: {← ppTypeAll `solution}"\n#print axioms solution\n')

def compile_and_check(it):
    """Compile a copy of the solution with the check appended, with the platform's options, and
    delete the copy: one Lean process per solution and no olean written.  Every solution declares
    `_root_.solution` inside a namespace block it closes before the end of the file, so the appended
    check runs in the root scope with no `open` in effect and prints the type exactly as a separate
    check file importing the solution does (that was the first version: a compile to the RAM disk,
    then a check run, at the cost of loading the imports twice)."""
    rel = f"Solutions/Sol_{it['slug']}.lean"
    path = f"Check/Sol_{it['slug']}.lean"
    os.makedirs(f"{A}/diag", exist_ok=True)
    text = open(f"{WS}/{rel}", encoding="utf-8").read()
    open(f"{WS}/{path}", "w", encoding="utf-8").write(text.rstrip("\n") + "\n" + CHECK_TAIL)
    try:
        try:
            setup = lean_setup.setup_for(f"{WS}/{path}")
        except FileNotFoundError as e:
            return it, 1, None, f"compile failed: {e}", str(e)
        t0 = time.time()
        r = subprocess.run(["lake", "env", "lean", f"--setup={setup}", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                            path], cwd=WS, env=env, capture_output=True, text=True)
        SECS[it["name"]] = round(time.time() - t0, 1)   # the platform's compile limit is 300 s
        remove(setup)
    finally:
        remove(f"{WS}/{path}")
    out = r.stdout + r.stderr
    open(f"{A}/diag/Solutions.Sol_{it['slug']}.txt", "w", encoding="utf-8").write(out)
    if r.returncode != 0:
        errs = [l for l in out.splitlines() if ": error" in l]
        return it, r.returncode, None, "compile failed: " + (errs[0][:300] if errs else out.strip()[-300:]), out
    t, TALL[it["name"]], axs = parse_check(out)
    return it, r.returncode, t, axs, out

def phase_solutions(s):
    stubs = s["stubs"]
    stubs_all = s.get("stubs_all", {})
    sol_items = [it for it in items if it["solution"]]
    rec = {}
    if args.phase == "all" or args.redo:
        open(SOL_OUT, "w").close()
    elif os.path.exists(SOL_OUT):
        for l in open(SOL_OUT, encoding="utf-8"):
            if l.strip():
                r = json.loads(l); rec[r["name"]] = r
    todo = [it for it in sol_items if not rec.get(it["name"], {}).get("ok")]
    if args.wave_order:
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "scripts"))
        import p2m_upload
        p2m_upload.set_tree_dir(args.wave_order)
        _, wn = p2m_upload.compute_waves(p2m_upload.load_tree())
        todo.sort(key=lambda it: wn.get(it["name"], 1 << 30))   # stable: within a wave, the tree's order
    print(f"solutions: {len(sol_items)}, {len(sol_items) - len(todo)} already checked, {len(todo)} to check"
          + (" (compiled with the check appended)" if args.compile else ""), flush=True)
    fn = compile_and_check if args.compile else check_solution
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=args.jobs) as ex, open(SOL_OUT, "a", encoding="utf-8") as fo:
        for k, (it, rc, t, ax, out) in enumerate(ex.map(fn, todo), 1):
            # the types printed with pp.all are compared when the stub check recorded them: the default
            # print depends on the notation the environment has (`∀ i < n, …` where Mathlib's binder
            # predicates are imported, `∀ (i : ℕ), i < n → …` where they are not)
            ta = TALL.get(it["name"])
            if it["name"] in stubs_all and ta is not None:
                same = ta == stubs_all[it["name"]]
            else:
                same = t is not None and t == stubs.get(it["name"])
            ok = rc == 0 and t is not None and same
            r = {"name": it["name"], "rc": rc, "type": t, "axioms": ax, "ok": ok,
                 "compared": "pp.all" if it["name"] in stubs_all and ta is not None else "default"}
            if it["name"] in SECS:
                r["secs"] = SECS[it["name"]]
            rec[it["name"]] = r
            fo.write(json.dumps(r, ensure_ascii=False) + "\n"); fo.flush()
            if not ok:
                print("SOLUTION TYPE DIFFERS / FAILED:", it["name"], rc)
                print("  stub:", stubs.get(it["name"]))
                print("  sol :", t if t else (ax if ax.startswith("compile failed") else out[:500]))
            if args.compile and k % 25 == 0:
                print(f"  {k}/{len(todo)} checked, {time.time() - t0:.0f}s", flush=True)
    sol_bad = sum(1 for it in sol_items if not rec.get(it["name"], {}).get("ok"))
    axioms = {it["name"]: rec[it["name"]]["axioms"] for it in sol_items if it["name"] in rec}
    extra = []
    for name, ax in axioms.items():
        used = {a.strip() for a in ax.split(",") if a.strip()}
        if not used <= OK_AXIOMS:
            extra.append((name, sorted(used - OK_AXIOMS)))
    print("solution types identical to the stub:", len(sol_items) - sol_bad, "of", len(sol_items))
    print("axioms outside {propext, Classical.choice, Quot.sound, sorryAx}:", extra or "none")
    return axioms, sol_bad, extra, all(it["name"] in rec for it in sol_items)

o = phase_orig() if args.phase in ("all", "orig") else load(ORIG_OUT, "orig")
if args.phase in ("all", "stubs"):
    s = phase_stubs(o)
elif args.phase == "solutions":
    s = load(STUB_OUT, "stubs")
if args.phase in ("all", "solutions"):
    axioms, sol_bad, extra, complete = phase_solutions(s)
    if complete:
        json.dump({"orig": o["orig"], "stubs": s["stubs"], "axioms": axioms, "stub_mismatch": s["stub_mismatch"],
                   "stub_private_marker_only": s.get("stub_private_marker_only", []),
                   "solution_mismatch": sol_bad, "textual_mismatch": o["textual_mismatch"],
                   "textual_checked": o["textual_checked"], "extra_axioms": extra},
                  open(VOUT, "w", encoding="utf-8"), indent=1)
        print("validation.json written")
