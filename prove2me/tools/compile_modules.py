#!/usr/bin/env python3
"""Compile source modules of the p2m workspace directly, in dependency order, without Lake's build
(which would also rebuild Mathlib whenever its intermediate files are missing).

    python3 prove2me/tools/compile_modules.py [--jobs 3] [--all] <module> ...

Each module's import closure within the workspace is compiled first; modules whose olean is newer
than their source are skipped unless --all.  Per-module wall time is appended to
<P2M_DIR>/compile-times.jsonl, diagnostics go to <P2M_DIR>/compile-diag/<module>.txt.
"""
import argparse, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_setup   # module-setup files: Lean then loads only the olean parts the cache ships

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
ENV = dict(os.environ, PATH=f"{S}/toolchain/bin:" + os.environ["PATH"])
ap = argparse.ArgumentParser()
ap.add_argument("modules", nargs="+")
ap.add_argument("--jobs", type=int, default=3)
ap.add_argument("--all", action="store_true")
ap.add_argument("--parts", action="store_true",
                help="also recompile module-system modules whose .olean.private part is missing (Mathlib's cache ships none)")
args = ap.parse_args()

imp_re = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", re.M)
MATHLIB = f"{WS}/.lake/packages/mathlib"
def src(m):
    # a Mathlib module (one the cache did not have) is compiled from the package's own sources
    base = MATHLIB if m == "Mathlib" or m.startswith("Mathlib.") else WS
    return f"{base}/{m.replace('.', '/')}.lean"
def olean(m):
    base = f"{MATHLIB}/.lake/build/lib/lean" if m == "Mathlib" or m.startswith("Mathlib.") else f"{WS}/.lake/build/lib/lean"
    return f"{base}/{m.replace('.', '/')}.olean"
deps, order = {}, []
def visit(m):
    if m in deps or not os.path.exists(src(m)): return
    imps = lean_setup.header_imports(open(src(m), encoding="utf-8", errors="replace").read())
    # every import with a source orders the compile (an importer never runs while an import is being
    # rewritten); what is actually recompiled is decided by stale() below
    deps[m] = [i for i in imps if os.path.exists(src(i))]
    for d in deps[m]: visit(d)
    order.append(m)
for m in args.modules: visit(m)
def is_module_system(m):
    return lean_setup.is_module_file(src(m))
def stale(m):
    if args.all or not os.path.exists(olean(m)) or os.path.getmtime(olean(m)) < os.path.getmtime(src(m)):
        return True
    return args.parts and is_module_system(m) and not os.path.exists(olean(m) + ".private")
todo = {m for m in order if stale(m)}
if not args.parts:   # a changed source rebuilds its dependents; a parts-only pass leaves them alone
    changed = True
    while changed:
        changed = False
        for m in order:
            if m not in todo and any(d in todo for d in deps[m]): todo.add(m); changed = True
print(f"{len(order)} modules in closure, {len(todo)} to compile ({args.jobs} jobs)", flush=True)
os.makedirs(f"{S}/compile-diag", exist_ok=True)
times = open(f"{S}/compile-times.jsonl", "a")
done = set(m for m in order if m not in todo); failed = {}

def compile_one(m):
    os.makedirs(os.path.dirname(olean(m)), exist_ok=True)
    t0 = time.time()
    try:
        setup = lean_setup.setup_for(src(m))
    except FileNotFoundError as e:
        return m, 1, [f"{src(m)}: error: {e}"], 0.0
    # each package's own lakefile options: Mathlib elaborates with maxSynthPendingDepth 3 (a module
    # compiled without it can fail where Mathlib's CI did not), the workspace with autoImplicit off
    opts = (["-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DautoImplicit=false"]
            if m == "Mathlib" or m.startswith("Mathlib.") else ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false"])
    r = subprocess.run(["lake", "env", "lean", f"--setup={setup}", *opts, "-o", olean(m), src(m)],
                       cwd=WS, env=ENV, capture_output=True, text=True)
    try:
        os.remove(setup)
    except OSError:
        pass
    out = r.stdout + r.stderr
    open(f"{S}/compile-diag/{m}.txt", "w", encoding="utf-8").write(out)
    errs = [l for l in out.splitlines() if ": error:" in l]
    return m, r.returncode, errs, time.time() - t0

with ThreadPoolExecutor(max_workers=args.jobs) as ex:
    futures = {}
    while todo or futures:
        ready = [m for m in order if m in todo and all(d in done for d in deps[m]) and m not in futures]
        for m in ready[: max(0, args.jobs - len(futures))]:
            futures[m] = ex.submit(compile_one, m); todo.discard(m)
        if not futures:
            for m in todo: failed[m] = ["dependency failed"]
            break
        fin = None
        while fin is None:
            for m, fu in list(futures.items()):
                if fu.done(): fin = m; break
            if fin is None: time.sleep(0.5)
        m, rc, errs, dt = futures.pop(fin).result()
        print(f"{'ok ' if rc == 0 else 'ERR'} {dt:7.1f}s {m}" + (f"  {errs[0][:160]}" if errs else ""), flush=True)
        times.write(json.dumps({"module": m, "seconds": round(dt, 1), "ok": rc == 0, "when": time.strftime('%Y-%m-%d %H:%M:%S')}) + "\n"); times.flush()
        if rc == 0: done.add(m)
        else:
            failed[m] = errs
            for k in list(todo):
                if m in deps[k]: todo.discard(k); failed[k] = ["dependency failed: " + m]
print(f"failed: {len(failed)}", flush=True)
for m, e in failed.items(): print(" ", m, e[0][:200] if e else "")
sys.exit(1 if failed else 0)
