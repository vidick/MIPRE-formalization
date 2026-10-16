#!/usr/bin/env python3
"""Compile the generated platform files directly with `lake env lean -o/-i`, in dependency order.

Lake's own build of the three libraries writes, per module, a multi-megabyte setup file and the
C output of the module, which exhausted the session's disk allowance; the platform compiles each
file itself, so the local check only needs the olean (for later imports) and the diagnostics.
This driver compiles the files named in the manifests, four at a time, placing the oleans where
`lake env` looks for them (`.lake/build/lib/lean/<Module>.olean`), and records every error.

    P2M_CONFIG=prove2me/assembly/config.json python3 prove2me/tools/build_tree.py [--jobs 4] [--all]

Files whose olean is newer than the source are skipped unless --all is given.  Exit status 1 if
any file failed; the log is <tree dir>/build-tree.log and the per-file diagnostics are kept in
<tree dir>/diag/.
"""
import argparse, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_setup   # module-setup files: Lean then loads only the olean parts the cache ships

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
CFG = json.load(open(os.environ["P2M_CONFIG"], encoding="utf-8"))
A = os.path.dirname(CFG["tree_out"])
ENV = dict(os.environ, PATH=f"{S}/toolchain/bin:" + os.environ["PATH"])

ap = argparse.ArgumentParser()
ap.add_argument("--jobs", type=int, default=4)
ap.add_argument("--all", action="store_true", help="recompile every file, not only the stale ones")
ap.add_argument("--files", nargs="*", help="only these files (relative to the workspace)")
args = ap.parse_args()

files = json.load(open(CFG["manifest"], encoding="utf-8"))
gp = os.path.join(A, "glue.json")
if os.path.exists(gp):
    files += json.load(open(gp, encoding="utf-8"))["generated"]
if args.files:
    files = args.files
files = sorted(set(files))

def module_of(rel):
    return rel[:-5].replace("/", ".")
def olean_of(rel):
    return f"{WS}/.lake/build/lib/lean/{rel[:-5]}.olean"
imp_re = re.compile(r"^import\s+(\S+)", re.M)
mods = {module_of(f): f for f in files}
deps = {}
for f in files:
    text = open(f"{WS}/{f}", encoding="utf-8").read()
    deps[module_of(f)] = [i for i in imp_re.findall(text) if i in mods]

def stale(rel):
    o = olean_of(rel)
    return args.all or not os.path.exists(o) or os.path.getmtime(o) < os.path.getmtime(f"{WS}/{rel}")

todo = {m for m, f in mods.items() if stale(f)}
# a stale module makes its dependents stale
changed = True
while changed:
    changed = False
    for m, ds in deps.items():
        if m not in todo and any(d in todo for d in ds):
            todo.add(m); changed = True
print(f"{len(files)} files, {len(todo)} to compile ({args.jobs} jobs)", flush=True)
os.makedirs(f"{A}/diag", exist_ok=True)
log = open(f"{A}/build-tree.log", "a", encoding="utf-8")
log.write(f"\n=== {time.strftime('%Y-%m-%d %H:%M:%S')} {len(todo)} files\n")

done, failed, running = set(m for m in mods if m not in todo), {}, {}
def compile_one(m):
    rel = mods[m]
    o = olean_of(rel)
    os.makedirs(os.path.dirname(o), exist_ok=True)
    t0 = time.time()
    # `lake env lean` does not apply the lakefile's leanOptions; the platform compiles with
    # autoImplicit off, so pass the same options explicitly
    try:
        setup = lean_setup.setup_for(f"{WS}/{rel}")
    except FileNotFoundError as e:
        out = f"{rel}: error: {e}"
        open(f"{A}/diag/{m}.txt", "w", encoding="utf-8").write(out)
        return m, 1, [out], 0, time.time() - t0
    r = subprocess.run(["lake", "env", "lean", f"--setup={setup}", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                        "-o", o, rel],
                       cwd=WS, env=ENV, capture_output=True, text=True)
    try:
        os.remove(setup)
    except OSError:
        pass
    out = r.stdout + r.stderr
    diag = f"{A}/diag/{m}.txt"
    open(diag, "w", encoding="utf-8").write(out)
    errors = [l for l in out.splitlines() if ": error:" in l]
    sorries = sum(1 for l in out.splitlines() if "declaration uses `sorry`" in l)
    return m, r.returncode, errors, sorries, time.time() - t0

with ThreadPoolExecutor(max_workers=args.jobs) as ex:
    futures = {}
    while todo or futures:
        ready = [m for m in todo if all(d in done for d in deps[m]) and m not in futures]
        for m in ready[: max(0, args.jobs - len(futures))]:
            futures[m] = ex.submit(compile_one, m)
            todo.discard(m)
        if not futures:
            if todo:
                blocked = sorted(todo)[:5]
                print("blocked (a dependency failed):", blocked, flush=True)
                for m in todo:
                    failed[m] = ["dependency failed"]
                todo.clear()
            break
        # wait for any one to finish
        finished = None
        while finished is None:
            for m, fu in list(futures.items()):
                if fu.done():
                    finished = m
                    break
            if finished is None:
                time.sleep(0.2)
        m, rc, errors, sorries, dt = futures.pop(finished).result()
        line = f"{'ok ' if rc == 0 else 'ERR'} {dt:5.1f}s sorry={sorries} {mods[m]}" + (f"  {errors[0][:200]}" if errors else "")
        print(line, flush=True); log.write(line + "\n"); log.flush()
        if rc == 0:
            done.add(m)
        else:
            failed[m] = errors
            # dependents of a failed module cannot be compiled
            for k, ds in deps.items():
                if m in ds and k in todo:
                    todo.discard(k); failed[k] = ["dependency failed: " + m]
print(f"compiled {len(todo) - len(failed)} ok, {len(failed)} failed", flush=True)   # todo was fixed before compiling; stale() is false afterwards
for m, errs in sorted(failed.items())[:40]:
    print(" ", mods[m], errs[0][:200] if errs else "")
json.dump({"failed": {mods[m]: errs for m, errs in failed.items()}}, open(f"{A}/build-tree.json", "w"), indent=1)
sys.exit(1 if failed else 0)
