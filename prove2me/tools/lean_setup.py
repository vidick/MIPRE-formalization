#!/usr/bin/env python3
"""Module-setup files for direct `lean` runs in the p2m workspace.

Plain `lean` opens the `.olean.server` and `.olean.private` parts of every module-system import
(`readModuleDataPartsOfMod`), and Mathlib's cache ships neither for its module-system modules;
Lake avoids this by handing Lean a setup file naming the artefacts of each transitive import
(`--setup=<json>`, `Lean.ModuleSetup`), from which Lean loads only the parts listed.  This module
builds such a file from the import graph: core (the toolchain), the Lake packages, the workspace's
MIPRE modules and the generated trees.

    from lean_setup import setup_for
    path = setup_for("/…/ws/MIPRE/Foundations/Games.lean")   # -> /…/setup/MIPRE.Foundations.Games.json

As a script: `python3 lean_setup.py <file.lean>` prints the setup path.  The import graph is cached
in <P2M_DIR>/import_graph.json and refreshed for files whose mtime changed.
"""
import glob, json, os, re, sys, threading, time

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
WS = f"{S}/ws"
TOOLCHAIN = f"{S}/toolchain"
CACHE = f"{S}/import_graph.json"
# `import X`, `public import X`, `meta import X`, `public meta import X`, `import all X`
IMP_RE = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)", re.M)

def header_imports(text):
    """The imports of a file's header: `prelude`/`module`/`import` lines and comments only, so an
    `import` mentioned in a docstring or a later comment is not taken for one."""
    out, i, n = [], 0, len(text)
    while i < n:
        # skip whitespace and comments
        if text[i].isspace():
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i); i = n if j < 0 else j + 1; continue
        if text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i): depth += 1; i += 2
                elif text.startswith("-/", i): depth -= 1; i += 2
                else: i += 1
            continue
        m = re.match(r"(prelude|module|(?:public\s+|private\s+)?(?:meta\s+)?import)\b", text[i:])
        if not m:
            break
        if m.group(1) in ("prelude", "module"):
            i += m.end(); continue
        j = text.find("\n", i); line = text[i:(n if j < 0 else j)]
        mm = IMP_RE.match(line)
        if mm:
            out.append(mm.group(1))
        i = n if j < 0 else j + 1
    return out

# (source root, olean root) pairs; a module `A.B.C` is `<src>/A/B/C.lean` and `<olean>/A/B/C.olean`
def roots():
    rs = [(f"{TOOLCHAIN}/src/lean", f"{TOOLCHAIN}/lib/lean"),   # Init, Std, Lean, Lake
          (f"{TOOLCHAIN}/src/lean/lake", f"{TOOLCHAIN}/lib/lean")]
    for pkg in sorted(glob.glob(f"{WS}/.lake/packages/*")):
        for lib in (f"{pkg}/.lake/build/lib/lean", f"{pkg}/.lake/build/lib"):
            if os.path.isdir(lib):
                rs.append((pkg, lib))
                break
        else:
            rs.append((pkg, f"{pkg}/.lake/build/lib/lean"))
    rs.append((WS, f"{WS}/.lake/build/lib/lean"))
    return rs

ROOTS = roots()

def source_of(mod):
    rel = mod.replace(".", "/") + ".lean"
    for src, _ in ROOTS:
        p = os.path.join(src, rel)
        if os.path.exists(p):
            return p
    return None

def olean_of(mod):
    rel = mod.replace(".", "/") + ".olean"
    for _, ol in ROOTS:
        p = os.path.join(ol, rel)
        if os.path.exists(p):
            return p
    return None

_graph = None
_lock = threading.RLock()   # the drivers call setup_for from several threads
def graph():
    global _graph
    with _lock:
        if _graph is None:
            try:
                _graph = json.load(open(CACHE, encoding="utf-8")) if os.path.exists(CACHE) else {}
            except (OSError, ValueError):
                _graph = {}
        return _graph

def imports_of(mod):
    """Direct imports of a module, from its source (cached by mtime)."""
    g = graph()
    src = source_of(mod)
    if src is None:
        return g.get(mod, {}).get("imports", [])   # a module without source (e.g. the toolchain's Init.Prelude): its olean is a leaf
    mt = os.path.getmtime(src)
    e = g.get(mod)
    if e and e.get("mtime") == mt and e.get("src") == src:
        return e["imports"]
    text = open(src, encoding="utf-8", errors="replace").read()
    imps = header_imports(text)
    g[mod] = {"mtime": mt, "src": src, "imports": imps}
    return imps

def save_graph():
    with _lock:
        if _graph is not None:
            tmp = f"{CACHE}.{os.getpid()}.{threading.get_ident()}.tmp"
            json.dump(dict(_graph), open(tmp, "w", encoding="utf-8"))
            os.replace(tmp, CACHE)

def closure(mods):
    seen, stack = set(), list(mods)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(imports_of(m))
    return seen

def is_module_file(path):
    """Does the file use the module system? The header keyword may carry a trailing line comment
    (Mathlib writes `module  -- shake: keep-all`), so the test is for the keyword, not the bare line."""
    text = open(path, encoding="utf-8", errors="replace").read(4000)
    return re.search(r"^module\b(?:\s*--.*)?$", text, re.M) is not None

def module_name_of(path):
    for src, _ in ROOTS:
        if path.startswith(src + "/"):
            return path[len(src) + 1:-5].replace("/", ".")
    return os.path.splitext(os.path.basename(path))[0]

def setup_for(path, out_dir=None):
    """Write the setup JSON for compiling `path`; return its path."""
    with _lock:
        return _setup_for(path, out_dir)

def _setup_for(path, out_dir=None):
    path = os.path.abspath(path)
    text = open(path, encoding="utf-8", errors="replace").read()
    direct = header_imports(text)
    mods = closure(direct)
    arts, missing = {}, []
    for m in sorted(mods):
        ol = olean_of(m)
        if ol is None:
            missing.append(m)
            continue
        # ImportArtifacts: [[olean, oleanServer?, oleanPrivate?], [irSig, ir?]].  Like Lake, list the
        # parts that exist (the private part only after a server part, as Lean nests them): the
        # toolchain ships all three, Mathlib's cache ships no server part, so Mathlib modules are
        # imported through their exported part alone, exactly as under `lake build`.
        parts = [ol]
        if os.path.exists(ol + ".server"):
            parts.append(ol + ".server")
            if os.path.exists(ol + ".private"):
                parts.append(ol + ".private")
        ir = []
        if os.path.exists(ol[:-6] + ".ir.sig"):
            ir.append(ol[:-6] + ".ir.sig")
            if os.path.exists(ol[:-6] + ".ir"):
                ir.append(ol[:-6] + ".ir")
        arts[m] = [parts, ir]
    save_graph()
    if missing:
        raise FileNotFoundError(f"{len(missing)} imported module(s) have no olean, e.g. {missing[:5]}")
    name = module_name_of(path)
    setup = {"name": name, "isModule": is_module_file(path), "importArts": arts,
             "dynlibs": [], "plugins": [], "options": {}}
    # setup files are large (every transitive artefact path) and short-lived: keep them in RAM when
    # the machine offers /dev/shm, and let the drivers remove them after the compile
    out_dir = out_dir or (f"/dev/shm/p2m_setup" if os.path.isdir("/dev/shm") else f"{S}/setup")
    os.makedirs(out_dir, exist_ok=True)
    out = os.path.join(out_dir, name + ".json")
    json.dump(setup, open(out, "w", encoding="utf-8"))
    return out

if __name__ == "__main__":
    print(setup_for(sys.argv[1]))
