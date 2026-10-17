#!/usr/bin/env python3
"""Idempotent uploader for the Prove2Me submission of the recursive-compression closure.

Reads the staged platform tree under ``prove2me/`` (``tree.json``, ``metadata.json`` and the
``Definitions/``, ``Theorems/``, ``Solutions/`` files that ``prove2me/tools/gen.py`` wrote and
``lake build`` checked) and uploads it in the order the platform requires: definition bundles
in import order, then every theorem statement, then every solution leaves-first, so that each
node resolves straight to ``Proved``.  Everything is created **private** unless ``--public``
is passed; a private tree is released later with ``POST /theorems/:id/make-public``.

State lives in ``prove2me/upload-state.json``: every action is recorded before and after its
API call, so an interrupted run resumes without duplicates.  The API key is read from the
environment variable ``PROVE2ME_API_KEY`` and is never printed; it is exchanged for one-hour
access tokens, refreshed before they expire.  Nothing is ever sent to a host other than
``prove2.me``.

Usage (from the repository root):
    python3 scripts/p2m_upload.py [--public] [--only definitions|theorems|solutions]
                                  [--dry-run] [--max-inflight N]
    python3 scripts/p2m_upload.py --status       # re-read every node's status and summarize
    python3 scripts/p2m_upload.py --tree prove2me/assembly   # another tree directory (tree.json, optional
                                                 # glue.json, metadata.json, upload-config.json, the files)
    python3 scripts/p2m_upload.py --tree prove2me/introspection --pipeline --after prove2me/answerreduction \\
        --gate <validation-solutions.jsonl> --max-inflight 20
                                                 # each item as soon as what it imports is ready, instead of
                                                 # wave by wave and phase by phase (upload_pipelined)
"""
import argparse, collections, io, json, os, re, sys, time, urllib.error, urllib.parse, urllib.request, uuid

API = "https://prove2.me/api/v1"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
P2M = os.path.join(ROOT, "prove2me")            # the tree directory; --tree changes it
STATE_PATH = os.path.join(P2M, "upload-state.json")
PROJECT_TAG = "mipre-formalization"
PUBLISHED = set()   # theorem names already on the platform (Proved), imported but not uploaded by this tree
DRY_DONE = {"definitions": set(), "solutions": set()}   # what a dry run has walked, across the waves
# platform-side failures that are not about the file: a dropped database connection while an
# import is looked up or a reduction edge recorded, an explicit "please resubmit"
TRANSIENT = ("ConnectionTerminated", "DB error", "please resubmit", "could not be recorded",
             "ConnectionReset", "timed out", "Connection refused", "temporarily unavailable")


def is_transient(msg):
    return any(pat in (msg or "") for pat in TRANSIENT)


def set_tree_dir(rel):
    global P2M, STATE_PATH
    P2M = os.path.join(ROOT, rel)
    STATE_PATH = os.path.join(P2M, "upload-state.json")


def load_tree():
    """tree.json, with the glue items of glue.json (if any) merged in as nodes."""
    tree = json.load(open(os.path.join(P2M, "tree.json"), encoding="utf-8"))
    gp = os.path.join(P2M, "glue.json")
    if os.path.exists(gp):
        for g in json.load(open(gp, encoding="utf-8"))["items"]:
            tree["nodes"].append({
                "theorem_name": g["theorem_name"], "slug": g["slug"], "formal_statement": g["formal_statement"],
                "preamble": g["preamble"], "imported_nodes": g["imported_nodes"],
                "stub_file": g.get("stub_file"), "solution_file": g.get("solution_file"),
                "stub_published": bool(g.get("stub_published")), "glue_kind": g["kind"],
            })
    names = {n["theorem_name"] for n in tree["nodes"]}
    # published nodes: named by slug in tree.json; recover the names from the imports
    pub_slugs = set(tree.get("published_nodes", []))
    for n in tree["nodes"]:
        for c in n["imported_nodes"]:
            if c not in names:
                PUBLISHED.add(c)
    return tree


# ----------------------------------------------------------------------------- auth
class Auth:
    def __init__(self):
        key = os.environ.get("PROVE2ME_API_KEY", "").strip()
        if not key:
            sys.exit("PROVE2ME_API_KEY is not set in the environment")
        self._key = key
        self._token, self._exp = None, 0

    def token(self):
        if self._token is None or time.time() > self._exp - 300:
            body = json.dumps({"api_key": self._key}).encode()
            for attempt in range(8):   # the host's security checkpoint and outages: wait them out
                req = urllib.request.Request(f"{API}/agent/refresh", data=body,
                                             headers={"Content-Type": "application/json"}, method="POST")
                try:
                    with urllib.request.urlopen(req, timeout=60) as r:
                        d = json.loads(r.read().decode())
                    break
                except urllib.error.HTTPError as e:
                    if e.code in (403, 429, 502, 503, 504) and attempt < 7:
                        wait = min(30 * 2 ** attempt, 600)
                        log(f"token refresh: HTTP {e.code} (security checkpoint or outage); retrying in {wait}s")
                        time.sleep(wait)
                        continue
                    raise
                except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
                    if attempt < 7:
                        wait = min(5 * 2 ** attempt, 300)
                        log(f"token refresh: network error ({e.__class__.__name__}); retrying in {wait}s")
                        time.sleep(wait)
                        continue
                    raise
            self._token = d["access_token"]
            self._exp = d.get("expires_at", time.time() + 3600)
            log(f"token refreshed (platform version {d.get('version')})")
        return self._token


AUTH = None


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def request(method, path, body=None, params=None, multipart=None, retries=8):
    url = f"{API}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    for attempt in range(retries):
        headers = {"Authorization": f"Bearer {AUTH.token()}"}
        data = None
        if multipart is not None:
            boundary = uuid.uuid4().hex
            buf = io.BytesIO()
            for k, v in multipart.items():
                buf.write(f"--{boundary}\r\n".encode())
                if isinstance(v, tuple):  # (filename, bytes)
                    buf.write(f'Content-Disposition: form-data; name="{k}"; filename="{v[0]}"\r\n'
                              f"Content-Type: text/plain; charset=utf-8\r\n\r\n".encode())
                    buf.write(v[1])
                    buf.write(b"\r\n")
                else:
                    buf.write(f'Content-Disposition: form-data; name="{k}"\r\n\r\n'.encode())
                    buf.write(str(v).encode("utf-8"))
                    buf.write(b"\r\n")
            buf.write(f"--{boundary}--\r\n".encode())
            data = buf.getvalue()
            headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
        elif body is not None:
            data = json.dumps(body, ensure_ascii=False).encode("utf-8")
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                txt = r.read().decode("utf-8")
                return r.status, (json.loads(txt) if txt.strip() else {})
        except urllib.error.HTTPError as e:
            txt = e.read().decode("utf-8", errors="replace")
            try:
                d = json.loads(txt)
            except Exception:
                d = {"raw": txt[:2000]}
            if e.code == 429:
                log(f"429 rate limited on {path}; sleeping 60s")
                time.sleep(60)
                continue
            # the host's security checkpoint answers 403 with an HTML page in place of the API
            # (seen 2026-10-15, "Vercel Security Checkpoint"); it clears on its own, so wait it out
            if e.code in (403, 502, 503, 504) and "raw" in d and attempt < retries - 1:
                wait = min(30 * 2 ** attempt, 600)
                kind = "security checkpoint" if "Security Checkpoint" in txt else "non-API response"
                log(f"{e.code} {kind} on {path}; retrying in {wait}s")
                time.sleep(wait)
                continue
            if e.code >= 500 and attempt < retries - 1:
                log(f"{e.code} on {path}; retrying in {5 * (attempt + 1)}s")
                time.sleep(5 * (attempt + 1))
                continue
            return e.code, d
        except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
            if attempt < retries - 1:
                wait = min(5 * 2 ** attempt, 300)
                log(f"network error on {path}: {e}; retrying in {wait}s")
                time.sleep(wait)
                continue
            raise
    return 599, {"error": "retries exhausted"}


# ----------------------------------------------------------------------------- state
def load_state():
    if os.path.exists(STATE_PATH):
        return json.load(open(STATE_PATH, encoding="utf-8"))
    return {"definitions": {}, "theorems": {}, "solutions": {}, "log": []}


DRY = False   # --dry-run: nothing is sent and nothing is written


def save_state(st):
    if DRY:
        return
    tmp = STATE_PATH + ".tmp"
    json.dump(st, open(tmp, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    os.replace(tmp, STATE_PATH)


def poll_job(job_id, what, every=4.0, limit=1800):
    """Poll a publish job until it is terminal; return the job object."""
    t0 = time.time()
    while True:
        code, d = request("GET", f"/publish-jobs/{job_id}")
        if code != 200:
            log(f"  poll {what}: HTTP {code} {d}")
            time.sleep(every)
            if time.time() - t0 > limit:
                return {"status": "POLL_TIMEOUT", "error_message": str(d)}
            continue
        if d.get("status") in ("PUBLISHED", "FAILED", "ERROR"):
            return d
        if time.time() - t0 > limit:
            return {"status": "POLL_TIMEOUT", "error_message": "no terminal status"}
        time.sleep(every)


def poll_submission(sub_id, what, every=5.0, limit=3600):
    t0 = time.time()
    while True:
        code, d = request("GET", "/verify", params={"submission_id": sub_id})
        if code == 200 and d.get("status") not in (None, "PENDING"):
            return d
        if code != 200:
            log(f"  poll {what}: HTTP {code} {d}")
        if time.time() - t0 > limit:
            return {"status": "POLL_TIMEOUT", "error_message": str(d)}
        time.sleep(every)


def find_theorem_id(name, env=None):
    """Exact-match lookup of a theorem (or definition) by its fully-dotted name."""
    params = {"theorem_name": name, "limit": 50}
    if env:
        params["env"] = env
    code, d = request("GET", "/theorems", params=params)
    if code != 200:
        return None
    items = d.get("theorems") or []
    for it in items:
        if it.get("theorem_name") == name or it.get("definition_name") == name:
            return it.get("theorem_id") or it.get("id")
    return None


# ----------------------------------------------------------------------------- phases
def read(path):
    return open(os.path.join(P2M, path), encoding="utf-8").read()


def bundle_deps(b, names):
    """Same-tree bundles a bundle imports (its `import Definitions.Def_<name>` lines)."""
    out = []
    for line in b.get("imports", []):
        m = re.match(r"\s*import\s+Definitions\.Def_(\S+)", line)
        if m and m.group(1) in names:
            out.append(m.group(1))
    return out


def upload_definitions(tree, meta, st, args):
    """Publish the bundles in import order, up to --max-inflight jobs at once: a bundle is
    submitted once every same-tree bundle it imports is PUBLISHED; a job that fails on a transient
    platform error is resubmitted (three times at most, 60 s apart)."""
    mb = {b["definition_name"]: b for b in meta["bundles"]}
    by = {b["definition_name"]: b for b in tree["bundles"]}
    names = set(by)
    pending = [b["definition_name"] for b in tree["bundles"] if st["definitions"].get(b["definition_name"], {}).get("status") != "PUBLISHED"]
    inflight, attempts, retry_at, dry_done = {}, collections.defaultdict(int), {}, DRY_DONE["definitions"]

    def published(n):
        return n not in names or n in dry_done or st["definitions"].get(n, {}).get("status") == "PUBLISHED"

    while pending or inflight:
        progressed = False
        for name in list(pending):
            if len(inflight) >= args.max_inflight:
                break
            b = by[name]
            if not all(published(d) for d in bundle_deps(b, names)) or retry_at.get(name, 0) > time.time():
                continue
            rec = st["definitions"].setdefault(name, {})
            if rec.get("job_id") and rec.get("status") not in ("FAILED", "ERROR", "REJECTED", "POLL_TIMEOUT"):
                inflight[name] = rec["job_id"]        # a job from an earlier run: poll it
                pending.remove(name); progressed = True
                continue
            if args.dry_run:
                log(f"[dry-run] submit-definition {name} ({len(read(b['file']))} bytes, after {bundle_deps(b, names)})")
                dry_done.add(name); pending.remove(name); progressed = True
                continue
            m = mb[name]
            body = {
                "definition_name": name,
                "definition_title": m["definition_title"][:200],
                "definition": read(b["file"]),
                "natural_language_statement": m["natural_language_statement"],
                "source": m["source"],
                "tags": sorted(set(m["tags"] + [PROJECT_TAG])),
                "private": not args.public,
            }
            code, d = request("POST", "/submit-definition", body=body)
            rec.update({"submitted_at": time.time(), "http": code, "status": d.get("status", "SUBMITTED")})
            if code != 202 or not d.get("job_id"):
                rec["error"] = d
                save_state(st)
                log(f"submit-definition {name}: HTTP {code} {json.dumps(d)[:500]}")
                if "already" in json.dumps(d).lower() or "exists" in json.dumps(d).lower() or "duplicate" in json.dumps(d).lower():
                    tid = find_theorem_id(name)
                    if tid:
                        rec.update({"status": "PUBLISHED", "theorem_id": tid, "note": "pre-existing"})
                        save_state(st)
                        pending.remove(name); progressed = True
                        continue
                sys.exit(f"definition {name} was rejected before queueing; fix and rerun")
            rec["job_id"] = d["job_id"]
            rec["status"] = "PENDING"
            save_state(st)
            log(f"submit-definition {name}: queued job {d['job_id']} ({len(inflight) + 1} in flight)")
            inflight[name] = d["job_id"]
            pending.remove(name); progressed = True
        if not inflight:
            if pending and not progressed:
                blocked = [n for n in pending if not all(published(d) for d in bundle_deps(by[n], names))]
                if blocked and all(retry_at.get(n, 0) <= time.time() for n in pending):
                    sys.exit(f"{len(blocked)} definition(s) blocked by an unpublished import, e.g. {blocked[0]}: "
                             f"{[d for d in bundle_deps(by[blocked[0]], names) if not published(d)]}")
            if not pending:
                break
            time.sleep(2)
            continue
        time.sleep(4)
        for name, job_id in list(inflight.items()):
            code, job = request("GET", f"/publish-jobs/{job_id}")
            if code != 200:
                log(f"  poll {name}: HTTP {code} {str(job)[:120]}")
                continue
            status = job.get("status")
            if status not in ("PUBLISHED", "FAILED", "ERROR"):
                continue
            del inflight[name]
            rec = st["definitions"][name]
            rec["status"] = status
            rec["theorem_id"] = job.get("theorem_id")
            rec["error_message"] = job.get("error_message", "")
            save_state(st)
            log(f"definition {name}: {status} {rec.get('theorem_id') or ''} {rec['error_message'][:300]}")
            if status != "PUBLISHED":
                if is_transient(rec["error_message"]) and attempts[name] < 3:
                    attempts[name] += 1
                    retry_at[name] = time.time() + 60
                    pending.insert(0, name)
                    log(f"definition {name}: transient platform error; resubmitting in 60 s (attempt {attempts[name] + 1} of 4)")
                else:
                    sys.exit(f"definition {name} did not publish ({status}); later content imports it, stopping")


def upload_theorems(tree, meta, st, args, rounds=0):
    mn = {n["theorem_name"]: n for n in meta["nodes"]}
    pending = []
    for n in tree["nodes"]:
        name = n["theorem_name"]
        rec = st["theorems"].setdefault(name, {})
        if rec.get("status") == "PUBLISHED" and rec.get("theorem_id"):
            continue
        if n.get("stub_published"):
            tid = find_theorem_id(name)
            if not tid:
                sys.exit(f"{name} is recorded as already published but the platform has no theorem of that name")
            rec.update({"status": "PUBLISHED", "theorem_id": tid, "note": "published before this tree"})
            save_state(st)
            log(f"theorem {name}: already on the platform, {tid}")
            continue
        if rec.get("job_id") and rec.get("status") not in ("FAILED", "ERROR"):
            pending.append((name, rec["job_id"]))
            continue
        m = mn[name]
        problem = {
            "theorem_name": name,
            "theorem_title": m["theorem_title"][:200],
            "formal_statement": n["formal_statement"],
            "natural_language_statement": m["natural_language_statement"],
            "preamble": n["preamble"],
            "source": m["source"],
            "tags": sorted(set(m["tags"] + [PROJECT_TAG])),
        }
        body = {"problems": [problem], "private": not args.public}
        if args.dry_run:
            log(f"[dry-run] submit-problem {name}")
            continue
        code, d = request("POST", "/submit-problem", body=body)
        rec.update({"submitted_at": time.time(), "http": code})
        jobs = d.get("jobs") or []
        if code != 202 or not jobs:
            rec["error"] = d
            rec["status"] = "REJECTED"
            save_state(st)
            log(f"submit-problem {name}: HTTP {code} {json.dumps(d)[:600]}")
            tid = find_theorem_id(name)
            if tid:
                rec.update({"status": "PUBLISHED", "theorem_id": tid, "note": "pre-existing"})
                save_state(st)
                continue
            sys.exit(f"theorem {name} was rejected before queueing; fix and rerun")
        rec["job_id"] = jobs[0]["job_id"]
        rec["status"] = "QUEUED"
        save_state(st)
        log(f"submit-problem {name}: queued job {rec['job_id']}")
        pending.append((name, rec["job_id"]))
        # keep the number of in-flight jobs bounded
        while len(pending) >= args.max_inflight:
            pending = drain(pending, st, "theorems", 1)
    while pending:
        pending = drain(pending, st, "theorems", len(pending))
    mine = {n["theorem_name"] for n in tree["nodes"]}   # the state may hold records of an earlier tree or wave
    failed = [k for k, v in st["theorems"].items() if k in mine and v.get("status") != "PUBLISHED"]
    transient = [k for k in failed if is_transient(st["theorems"][k].get("error_message"))]
    if transient and rounds < 3 and not args.dry_run:
        log(f"{len(transient)} statement(s) failed on a transient platform error "
            f"({', '.join(transient)[:300]}); resubmitting in 60 s (round {rounds + 1} of 3)")
        time.sleep(60)
        return upload_theorems(tree, meta, st, args, rounds + 1)
    if failed and not args.dry_run:
        sys.exit(f"{len(failed)} theorem(s) did not publish: {failed[:10]}")


def drain(pending, st, kind, n):
    """Poll the oldest n pending publish jobs to a terminal state."""
    done = 0
    rest = []
    for name, job_id in pending:
        if done >= n:
            rest.append((name, job_id))
            continue
        job = poll_job(job_id, name)
        rec = st[kind][name]
        rec["status"] = job.get("status")
        rec["theorem_id"] = job.get("theorem_id")
        rec["error_message"] = job.get("error_message", "")
        save_state(st)
        log(f"{kind[:-1]} {name}: {rec['status']} {rec.get('theorem_id') or ''} {rec['error_message'][:300]}")
        done += 1
    return rest


def node_bundle_deps(n, names):
    """Same-tree bundles a node's stub and solution import (their `import Definitions.Def_<name>` lines)."""
    out = set()
    texts = [n.get("preamble") or ""]
    if n.get("solution_file") and os.path.exists(os.path.join(P2M, n["solution_file"])):
        texts.append(read(n["solution_file"]))
    for t in texts:
        for m in re.finditer(r"^\s*import\s+Definitions\.Def_(\S+)", t, re.M):
            if m.group(1) in names:
                out.add(m.group(1))
    return sorted(out)


def compute_waves(tree):
    """Upload waves.  A bundle may import a same-tree theorem only once that theorem is Proved on the
    platform, so a bundle goes one wave after the nodes it imports; a node goes with the latest bundle
    its stub or solution imports, and no earlier than the nodes its solution imports.  Returns the
    wave of every bundle (by definition name) and node (by theorem name)."""
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 50000))
    by_b = {b["definition_name"]: b for b in tree["bundles"]}
    by_n = {n["theorem_name"]: n for n in tree["nodes"]}
    names_b = set(by_b)
    wb, wn = {}, {}

    def bundle_wave(name):
        if name not in wb:
            wb[name] = -1   # cycle guard
            w = 0
            for d in bundle_deps(by_b[name], names_b):
                w = max(w, bundle_wave(d))
            for t in by_b[name].get("imported_nodes", []):
                if t in by_n:
                    w = max(w, node_wave(t) + 1)
            wb[name] = w
        if wb[name] < 0:
            sys.exit(f"import cycle through bundle {name}")
        return wb[name]

    def node_wave(name):
        if name not in wn:
            wn[name] = -1
            w = 0
            for d in node_bundle_deps(by_n[name], names_b):
                w = max(w, bundle_wave(d))
            for t in by_n[name]["imported_nodes"]:
                if t in by_n:
                    w = max(w, node_wave(t))
            wn[name] = w
        if wn[name] < 0:
            sys.exit(f"import cycle through node {name}")
        return wn[name]

    for b in tree["bundles"]:
        bundle_wave(b["definition_name"])
    for n in tree["nodes"]:
        node_wave(n["theorem_name"])
    return wb, wn


def ensure_proved(names, st, limit=3600):
    """Wait until the platform marks each theorem Proved (the solutions are accepted; the status
    follows once the platform has recorded the reduction)."""
    t0 = time.time()
    for name in names:
        tid = st["theorems"].get(name, {}).get("theorem_id")
        if not tid:
            sys.exit(f"{name} has no theorem id in the state; it must be published before the bundles that import it")
        while True:
            code, t = request("GET", f"/theorems/{tid}")
            if code == 200 and t.get("status") == "Proved":
                break
            if time.time() - t0 > limit:
                sys.exit(f"{name} is {t.get('status') if code == 200 else code} after {limit} s; the next wave's bundles import it as Proved")
            log(f"  waiting for {name} to be Proved (now {t.get('status') if code == 200 else code})")
            time.sleep(15)


def leaves_first(tree):
    """Nodes ordered so that every imported node comes first."""
    by = {n["theorem_name"]: n for n in tree["nodes"]}
    order, seen = [], set()

    def visit(name):
        if name in seen or name not in by:   # imported published nodes are not this tree's
            return
        seen.add(name)
        for c in by[name]["imported_nodes"]:
            visit(c)
        order.append(name)
    for n in tree["nodes"]:
        visit(n["theorem_name"])
    return [by[x] for x in order]


class Gate:
    """The local check's verdicts (validate.py's validation-solutions.jsonl, one JSON record per
    solution, the last one counting): with --gate a solution is submitted only once it compiled and
    matched its stub locally, so the upload can run while the check is still working through the
    later waves.  The file is re-read at most every 30 seconds; a failed check is reported once."""
    def __init__(self, path):
        self.path, self.read_at, self.ok, self.reported = path, 0.0, {}, set()

    def passed(self, name):
        if time.time() - self.read_at > 30:
            self.read_at = time.time()
            if os.path.exists(self.path):
                for line in open(self.path, encoding="utf-8"):
                    if line.strip():
                        r = json.loads(line)
                        self.ok[r["name"]] = bool(r.get("ok"))
        if self.ok.get(name) is False and name not in self.reported:
            self.reported.add(name)
            log(f"solution {name}: the local check failed; it is held until a new check passes")
        return self.ok.get(name) is True


def upload_solutions(tree, meta, st, args):
    """Verify the solutions leaves-first, up to --max-inflight at once: a solution is submitted once
    every node it imports is Proved (here or before this tree), an accepted sketch, or an Open leaf
    by design; a verdict lost to a transient platform error is resubmitted (three times at most)."""
    mn = {n["theorem_name"]: n for n in meta["nodes"]}
    order = leaves_first(tree)
    by = {n["theorem_name"]: n for n in order}
    inflight, attempts, retry_at, dry_done = {}, collections.defaultdict(int), {}, DRY_DONE["solutions"]

    def handled(c):
        return (c in PUBLISHED or c in dry_done
                or st["solutions"].get(c, {}).get("status") in ("ACCEPTED", "SKETCH_ACCEPTED", "LEAF_OPEN"))

    pending = [n["theorem_name"] for n in order if not handled(n["theorem_name"])]
    gate = Gate(args.gate) if getattr(args, "gate", None) and not args.dry_run else None
    while pending or inflight:
        progressed = False
        waiting_gate = False
        for name in list(pending):
            if len(inflight) >= args.max_inflight:
                break
            n = by[name]
            rec = st["solutions"].setdefault(name, {})
            if not n.get("solution_file"):
                rec["status"] = "LEAF_OPEN"   # an Open leaf: statement only, by design
                save_state(st)
                pending.remove(name); progressed = True
                continue
            if not all(handled(c) for c in n["imported_nodes"]) or retry_at.get(name, 0) > time.time():
                continue
            if gate is not None and not gate.passed(name):
                waiting_gate = True   # not yet checked locally (or failed there): submitted once it passes
                continue
            tid = st["theorems"].get(name, {}).get("theorem_id")
            if args.dry_run:
                log(f"[dry-run] verify {name} -> theorem {tid or '(id unknown until the theorems phase has run)'}"
                    f" ({len(open(os.path.join(P2M, n['solution_file']), 'rb').read())} bytes, "
                    f"{len(n['imported_nodes'])} imported)")
                dry_done.add(name); pending.remove(name); progressed = True
                continue
            if not tid:
                sys.exit(f"no theorem_id recorded for {name}; run the theorems phase first")
            if rec.get("submission_id") and rec.get("status") in (None, "PENDING", "SUBMITTED"):
                inflight[name] = rec["submission_id"]   # a submission from an earlier run: poll it
                pending.remove(name); progressed = True
                continue
            sol = open(os.path.join(P2M, n["solution_file"]), "rb").read()
            fields = {"theorem_id": tid, "proof_type": "prove",
                      "file": (f"Sol_{n['slug']}.lean", sol),
                      "explanation": mn[name].get("explanation", "")}
            code, d = request("POST", "/verify", multipart=fields)
            rec.update({"submitted_at": time.time(), "http": code})
            if code not in (200, 201, 202) or not d.get("submission_id"):
                rec["error"] = d
                rec["status"] = "REJECTED"
                save_state(st)
                sys.exit(f"verify {name}: HTTP {code} {json.dumps(d)[:800]}")
            rec["submission_id"] = d["submission_id"]
            rec["status"] = "PENDING"
            save_state(st)
            log(f"verify {name}: submission {d['submission_id']} ({len(inflight) + 1} in flight)")
            inflight[name] = d["submission_id"]
            pending.remove(name); progressed = True
        if not inflight:
            if waiting_gate and not progressed:
                time.sleep(30)   # the local check of the next solutions is still running
                continue
            if pending and not progressed and all(retry_at.get(n, 0) <= time.time() for n in pending):
                blocked = pending[0]
                sys.exit(f"{len(pending)} solution(s) blocked: {blocked} waits for "
                         f"{[c for c in by[blocked]['imported_nodes'] if not handled(c)]}")
            if not pending:
                break
            time.sleep(2)
            continue
        time.sleep(5)
        for name, sid in list(inflight.items()):
            code, res = request("GET", "/verify", params={"submission_id": sid})
            if code != 200:
                log(f"  poll {name}: HTTP {code} {str(res)[:120]}")
                continue
            status = res.get("status")
            if status in (None, "PENDING"):
                continue
            del inflight[name]
            rec = st["solutions"][name]
            rec["status"] = status
            rec["error_message"] = res.get("error_message", "")
            save_state(st)
            log(f"solution {name}: {status} {rec['error_message'][:400]}")
            if status in ("ACCEPTED", "SKETCH_ACCEPTED"):
                continue
            if is_transient(rec["error_message"]) and attempts[name] < 3:
                attempts[name] += 1
                retry_at[name] = time.time() + 60
                pending.insert(0, name)
                log(f"solution {name}: transient platform error; resubmitting in 60 s (attempt {attempts[name] + 1} of 4)")
            else:
                sys.exit(f"solution of {name} ended {status}: {rec['error_message'][:1500]}")


ACCEPTED = ("ACCEPTED", "SKETCH_ACCEPTED", "LEAF_OPEN")
DEF_IMPORT = re.compile(r"^\s*import\s+Definitions\.Def_(\S+)", re.M)


class Sibling:
    """A tree uploaded alongside this one (--after): what this tree imports from it is ready once its
    state file records it, a bundle as PUBLISHED, a node as a published statement with an accepted
    solution.  The file is re-read at most every 30 seconds (the other uploader replaces it
    atomically); content the sibling does not hold was on the platform before either tree."""
    def __init__(self, rel):
        d = os.path.join(ROOT, rel)
        self.rel, self.path = rel, os.path.join(d, "upload-state.json")
        t = json.load(open(os.path.join(d, "tree.json"), encoding="utf-8"))
        self.bundles = {b["definition_name"] for b in t["bundles"]}
        self.nodes = {n["theorem_name"] for n in t["nodes"]}
        gp = os.path.join(d, "glue.json")
        if os.path.exists(gp):
            self.nodes |= {g["theorem_name"] for g in json.load(open(gp, encoding="utf-8"))["items"]}
        self.read_at, self.st = 0.0, {"definitions": {}, "theorems": {}, "solutions": {}}

    def state(self):
        if time.time() - self.read_at > 30:
            self.read_at = time.time()
            try:
                self.st = json.load(open(self.path, encoding="utf-8"))
            except (OSError, ValueError):
                pass   # not written yet: keep the last reading
        return self.st

    def bundle_ready(self, name):
        return name not in self.bundles or self.state()["definitions"].get(name, {}).get("status") == "PUBLISHED"

    def node_ready(self, name):
        if name not in self.nodes:
            return True
        s = self.state()
        return (s["theorems"].get(name, {}).get("status") == "PUBLISHED"
                and s["solutions"].get(name, {}).get("status") in ACCEPTED)

    def theorem_id(self, name):
        return self.state()["theorems"].get(name, {}).get("theorem_id")


def upload_pipelined(tree, meta, st, args, siblings):
    """One scheduler for bundles, statements and solutions in place of the waves' three barriers: a
    bundle is submitted once the bundles it imports are published and the nodes it imports are
    Proved; a statement once the bundles its preamble imports are published; a solution once its
    statement is published, the bundles it imports are, the nodes it imports are accepted (leaves
    first) and, with --gate, the local check has passed it.  At most --max-inflight jobs of all three
    kinds are in flight, the earliest wave first.  A transient failure is resubmitted (three times at
    most, 60 s apart); any other failure stops only what depends on it, and is reported at the end."""
    mb = {b["definition_name"]: b for b in meta["bundles"]}
    mn = {n["theorem_name"]: n for n in meta["nodes"]}
    by_b = {b["definition_name"]: b for b in tree["bundles"]}
    by_n = {n["theorem_name"]: n for n in tree["nodes"]}
    names_b, names_n = set(by_b), set(by_n)
    wb, wn = compute_waves(tree)
    b_defs = {b: sorted(set(DEF_IMPORT.findall("\n".join(by_b[b].get("imports", []))))) for b in by_b}
    # (a bundle's imported_published_nodes are slugs; the generator records their names apart)
    b_nodes = {b: sorted(set(by_b[b].get("imported_nodes", [])) | set(by_b[b].get("imported_published_node_names", [])))
               for b in by_b}
    t_defs = {n: sorted(set(DEF_IMPORT.findall(by_n[n].get("preamble") or ""))) for n in by_n}
    s_defs = {n: sorted(set(DEF_IMPORT.findall(read(by_n[n]["solution_file"]))))
              if by_n[n].get("solution_file") else [] for n in by_n}
    dry = {"B": set(), "T": set(), "S": set()}

    def def_ok(d):
        if d in names_b:
            return d in dry["B"] or st["definitions"].get(d, {}).get("status") == "PUBLISHED"
        return args.dry_run or all(s.bundle_ready(d) for s in siblings)

    def stmt_ok(n):
        rec = st["theorems"].get(n, {})
        return n in dry["T"] or bool(rec.get("status") == "PUBLISHED" and rec.get("theorem_id"))

    def sol_ok(n):   # an imported node: accepted here, ready in a sibling, or on the platform before
        if n in names_n:
            return n in dry["S"] or st["solutions"].get(n, {}).get("status") in ACCEPTED
        return args.dry_run or all(s.node_ready(n) for s in siblings)

    proved, proved_at = set(), {}

    def proved_ok(n):   # a node a bundle imports: the platform must show it Proved
        if n in proved:
            return True
        if not sol_ok(n):
            return False
        if args.dry_run:
            return True
        if n in names_n:
            tid = st["theorems"].get(n, {}).get("theorem_id")
        else:
            tid = next((s.theorem_id(n) for s in siblings if n in s.nodes), None)
            if tid is None:
                proved.add(n)   # published (Proved) before this tree and its siblings
                return True
        if time.time() - proved_at.get(n, 0) < 30:
            return False
        proved_at[n] = time.time()
        code, t = request("GET", f"/theorems/{tid}")
        if code == 200 and t.get("status") == "Proved":
            proved.add(n)
            return True
        return False

    gate = Gate(args.gate) if getattr(args, "gate", None) and not args.dry_run else None

    def ready(kind, x):
        if kind == "B":
            return all(def_ok(d) for d in b_defs[x]) and all(proved_ok(c) for c in b_nodes[x])
        if kind == "T":
            return all(def_ok(d) for d in t_defs[x])
        return (stmt_ok(x) and all(def_ok(d) for d in s_defs[x]) and all(sol_ok(c) for c in by_n[x]["imported_nodes"])
                and (gate is None or not by_n[x].get("solution_file") or gate.passed(x)))

    def deps_in_tree(kind, x):   # the same-tree items whose failure blocks this one
        if kind == "B":
            return [("B", d) for d in b_defs[x] if d in names_b] + [("S", c) for c in b_nodes[x] if c in names_n]
        if kind == "T":
            return [("B", d) for d in t_defs[x] if d in names_b]
        return ([("T", x)] + [("B", d) for d in s_defs[x] if d in names_b]
                + [("S", c) for c in by_n[x]["imported_nodes"] if c in names_n])

    # ---- submitting: each returns a job/submission id, "done" (nothing to wait for) or "failed"
    def submit_B(name):
        b, m, rec = by_b[name], mb[name], st["definitions"].setdefault(name, {})
        if args.dry_run:
            log(f"[dry-run] submit-definition {name} (wave {wb[name]})")
            dry["B"].add(name)
            return "done"
        body = {"definition_name": name, "definition_title": m["definition_title"][:200],
                "definition": read(b["file"]), "natural_language_statement": m["natural_language_statement"],
                "source": m["source"], "tags": sorted(set(m["tags"] + [PROJECT_TAG])), "private": not args.public}
        code, d = request("POST", "/submit-definition", body=body)
        rec.update({"submitted_at": time.time(), "http": code, "status": d.get("status", "SUBMITTED")})
        if code != 202 or not d.get("job_id"):
            rec["error"] = d
            save_state(st)
            log(f"submit-definition {name}: HTTP {code} {json.dumps(d)[:500]}")
            txt = json.dumps(d).lower()
            if "already" in txt or "exists" in txt or "duplicate" in txt:
                tid = find_theorem_id(name)
                if tid:
                    rec.update({"status": "PUBLISHED", "theorem_id": tid, "note": "pre-existing"})
                    save_state(st)
                    return "done"
            rec["status"] = "REJECTED"
            save_state(st)
            return "failed"
        rec.update({"job_id": d["job_id"], "status": "PENDING"})
        save_state(st)
        log(f"submit-definition {name}: queued job {d['job_id']}")
        return d["job_id"]

    def submit_T(name):
        n, rec = by_n[name], st["theorems"].setdefault(name, {})
        if n.get("stub_published"):
            tid = find_theorem_id(name)
            if not tid:
                log(f"{name} is recorded as already published but the platform has no theorem of that name")
                return "failed"
            rec.update({"status": "PUBLISHED", "theorem_id": tid, "note": "published before this tree"})
            save_state(st)
            log(f"theorem {name}: already on the platform, {tid}")
            return "done"
        if args.dry_run:
            log(f"[dry-run] submit-problem {name} (wave {wn[name]})")
            dry["T"].add(name)
            return "done"
        m = mn[name]
        problem = {"theorem_name": name, "theorem_title": m["theorem_title"][:200],
                   "formal_statement": n["formal_statement"], "natural_language_statement": m["natural_language_statement"],
                   "preamble": n["preamble"], "source": m["source"], "tags": sorted(set(m["tags"] + [PROJECT_TAG]))}
        code, d = request("POST", "/submit-problem", body={"problems": [problem], "private": not args.public})
        rec.update({"submitted_at": time.time(), "http": code})
        jobs = d.get("jobs") or []
        if code != 202 or not jobs:
            rec.update({"error": d, "status": "REJECTED"})
            save_state(st)
            log(f"submit-problem {name}: HTTP {code} {json.dumps(d)[:600]}")
            tid = find_theorem_id(name)
            if tid:
                rec.update({"status": "PUBLISHED", "theorem_id": tid, "note": "pre-existing"})
                save_state(st)
                return "done"
            return "failed"
        rec.update({"job_id": jobs[0]["job_id"], "status": "QUEUED"})
        save_state(st)
        log(f"submit-problem {name}: queued job {rec['job_id']}")
        return rec["job_id"]

    def submit_S(name):
        n, rec = by_n[name], st["solutions"].setdefault(name, {})
        if not n.get("solution_file"):
            rec["status"] = "LEAF_OPEN"   # an Open leaf: statement only, by design
            save_state(st)
            return "done"
        tid = st["theorems"].get(name, {}).get("theorem_id")
        if args.dry_run:
            log(f"[dry-run] verify {name} (wave {wn[name]})")
            dry["S"].add(name)
            return "done"
        fields = {"theorem_id": tid, "proof_type": "prove",
                  "file": (f"Sol_{n['slug']}.lean", open(os.path.join(P2M, n["solution_file"]), "rb").read()),
                  "explanation": mn[name].get("explanation", "")}
        code, d = request("POST", "/verify", multipart=fields)
        rec.update({"submitted_at": time.time(), "http": code})
        if code not in (200, 201, 202) or not d.get("submission_id"):
            rec.update({"error": d, "status": "REJECTED"})
            save_state(st)
            log(f"verify {name}: HTTP {code} {json.dumps(d)[:800]}")
            return "failed"
        rec.update({"submission_id": d["submission_id"], "status": "PENDING"})
        save_state(st)
        log(f"verify {name}: submission {d['submission_id']}")
        return d["submission_id"]

    SUBMIT = {"B": submit_B, "T": submit_T, "S": submit_S}
    KIND = {"B": "definitions", "T": "theorems", "S": "solutions"}

    def poll(kind, name, jid):
        """None while the job runs; else (ok, error message)."""
        rec = st[KIND[kind]][name]
        if kind == "S":
            code, res = request("GET", "/verify", params={"submission_id": jid})
            if code != 200:
                log(f"  poll {name}: HTTP {code} {str(res)[:120]}")
                return None
            if res.get("status") in (None, "PENDING"):
                return None
            rec.update({"status": res.get("status"), "error_message": res.get("error_message", "")})
            save_state(st)
            log(f"solution {name}: {rec['status']} {rec['error_message'][:400]}")
            return rec["status"] in ("ACCEPTED", "SKETCH_ACCEPTED"), rec["error_message"]
        code, job = request("GET", f"/publish-jobs/{jid}")
        if code != 200:
            log(f"  poll {name}: HTTP {code} {str(job)[:120]}")
            return None
        if job.get("status") not in ("PUBLISHED", "FAILED", "ERROR"):
            return None
        rec.update({"status": job.get("status"), "theorem_id": job.get("theorem_id"),
                    "error_message": job.get("error_message", "")})
        save_state(st)
        log(f"{KIND[kind][:-1]} {name}: {rec['status']} {rec.get('theorem_id') or ''} {rec['error_message'][:300]}")
        return rec["status"] == "PUBLISHED" and bool(rec.get("theorem_id")), rec["error_message"]

    # ---- the work list, earliest wave first; jobs an earlier run left in flight are polled, not resent
    # a ready bundle first, whatever its wave: it unlocks every statement and solution beneath it, and
    # waiting for the rest of the previous wave's solutions (by wave alone) left the slots to them
    order = {"B": 0, "T": 1, "S": 2}
    items = sorted([("B", b) for b in by_b] + [("T", n) for n in by_n] + [("S", n) for n in by_n],
                   key=lambda kx: (kx[0] != "B", (wb if kx[0] == "B" else wn)[kx[1]], order[kx[0]]))
    done_now = {"B": lambda x: def_ok(x), "T": lambda x: stmt_ok(x),
                "S": lambda x: st["solutions"].get(x, {}).get("status") in ACCEPTED}
    pending = [kx for kx in items if not done_now[kx[0]](kx[1])]
    inflight = {}   # (kind, name) -> [job id, time of the last poll]
    for kind, name in list(pending):
        rec = st[KIND[kind]].get(name, {})
        jid = rec.get("submission_id") if kind == "S" else rec.get("job_id")
        live = (rec.get("status") in (None, "PENDING", "SUBMITTED") if kind == "S"
                else rec.get("status") not in ("FAILED", "ERROR", "REJECTED", "POLL_TIMEOUT", "PUBLISHED"))
        if jid and live and not args.dry_run:
            inflight[(kind, name)] = [jid, 0.0]
            pending.remove((kind, name))
    log(f"pipeline: {len(pending)} item(s) to submit, {len(inflight)} in flight from an earlier run, "
        f"at most {args.max_inflight} in flight")
    attempts, retry_at, failed = collections.defaultdict(int), {}, {}
    last_report = time.time()

    def dead(kx, memo):
        """Blocked for this run by a failure upstream in this tree."""
        if kx in failed:
            return True
        if kx not in memo:
            memo[kx] = False
            memo[kx] = any(dead(d, memo) for d in deps_in_tree(*kx) if d in failed or d in pending_set)
        return memo[kx]

    while pending or inflight:
        submitted = False
        for kx in list(pending):
            if len(inflight) >= args.max_inflight:
                break
            if retry_at.get(kx, 0) > time.time() or kx in failed or not ready(*kx):
                continue
            r = SUBMIT[kx[0]](kx[1])
            pending.remove(kx)
            submitted = True
            if r == "failed":
                failed[kx] = st[KIND[kx[0]]].get(kx[1], {}).get("error") or "rejected before queueing"
            elif r != "done":
                inflight[kx] = [r, time.time()]
        now = time.time()
        for kx, (jid, at) in list(inflight.items()):
            if now - at < 10:
                continue
            inflight[kx][1] = now
            res = poll(kx[0], kx[1], jid)
            if res is None:
                continue
            del inflight[kx]
            ok, msg = res
            if ok:
                continue
            if is_transient(msg) and attempts[kx] < 3:
                attempts[kx] += 1
                retry_at[kx] = time.time() + 60
                pending.insert(0, kx)
                log(f"{KIND[kx[0]][:-1]} {kx[1]}: transient platform error; resubmitting in 60 s (attempt {attempts[kx] + 1} of 4)")
            else:
                failed[kx] = msg
        if time.time() - last_report > 300:
            last_report = time.time()
            nb = sum(1 for b in by_b if def_ok(b))
            nt = sum(1 for n in by_n if stmt_ok(n))
            ns = sum(1 for n in by_n if st["solutions"].get(n, {}).get("status") in ACCEPTED)
            log(f"progress: definitions {nb}/{len(by_b)}, statements {nt}/{len(by_n)}, solutions {ns}/{len(by_n)}, "
                f"{len(inflight)} in flight, {len(failed)} failed")
        if not inflight and not submitted and pending:
            pending_set, memo = set(pending), {}
            if all(dead(kx, memo) for kx in pending):
                break   # everything left waits on a failure of this run
            if args.dry_run:
                break   # nothing changes outside a dry run's own walk
        if not submitted and not args.dry_run:
            time.sleep(4)
    if failed:
        log(f"{len(failed)} item(s) failed and {len(pending)} wait on them:")
        for (kind, name), msg in list(failed.items())[:40]:
            log(f"  {KIND[kind][:-1]} {name}: {str(msg)[:400]}")
        sys.exit(1)
    if pending:
        log(f"[dry-run] {len(pending)} item(s) never became ready, e.g. {pending[:3]}")
        sys.exit(1)
    log("pipeline: everything " + ("walked" if args.dry_run else "submitted and accepted"))


def status(tree, st):
    rows = []
    for n in tree["nodes"]:
        name = n["theorem_name"]
        tid = st["theorems"].get(name, {}).get("theorem_id")
        s = "?"
        if tid:
            code, d = request("GET", f"/theorems/{tid}")
            s = d.get("status", f"HTTP {code}") if code == 200 else f"HTTP {code}"
        rows.append((name, tid, s, st["solutions"].get(name, {}).get("status")))
    for r in rows:
        print(f"{r[2]:10s} {r[3] or '-':16s} {r[0]}  {r[1] or ''}")
    counts = {}
    for r in rows:
        counts[r[2]] = counts.get(r[2], 0) + 1
    print("theorem statuses:", counts)
    return rows


def release(tree, st, yes):
    """Make every private node public, by calling make-public on the roots of the node DAG
    (each call publishes the theorem and everything it depends on, permanently)."""
    imported = {c for n in tree["nodes"] for c in n["imported_nodes"]}
    roots = [n["theorem_name"] for n in tree["nodes"] if n["theorem_name"] not in imported]
    print("DAG roots to release (each with its dependency tree):")
    for r in roots:
        print("  ", r, st["theorems"].get(r, {}).get("theorem_id"))
    if not yes:
        print("re-run with --yes to publish; this cannot be undone")
        return
    for r in roots:
        tid = st["theorems"].get(r, {}).get("theorem_id")
        if not tid:
            print("no theorem_id for", r)
            continue
        code, d = request("POST", f"/theorems/{tid}/make-public")
        log(f"make-public {r}: HTTP {code} {json.dumps(d)[:400]}")
        st.setdefault("released", {})[r] = {"http": code, "response": d, "at": time.time()}
        save_state(st)


def main():
    global DRY
    global AUTH
    ap = argparse.ArgumentParser()
    ap.add_argument("--release", action="store_true", help="make the uploaded private tree public (asks for --yes)")
    ap.add_argument("--yes", action="store_true")
    ap.add_argument("--public", action="store_true", help="create public content (default: private)")
    ap.add_argument("--only", choices=["definitions", "theorems", "solutions"])
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--status", action="store_true")
    ap.add_argument("--max-inflight", type=int, default=10)
    ap.add_argument("--tree", default="prove2me", help="tree directory relative to the repository root")
    ap.add_argument("--gate", default=None,
                    help="submit a solution only once this file (validate.py's validation-solutions.jsonl) records it as passed")
    ap.add_argument("--pipeline", action="store_true",
                    help="one scheduler for the three kinds of item instead of the waves (see upload_pipelined)")
    ap.add_argument("--after", action="append", default=[],
                    help="with --pipeline: a tree directory being uploaded alongside, whose content this tree "
                         "imports once that tree's state file records it (repeatable)")
    args = ap.parse_args()
    DRY = args.dry_run
    set_tree_dir(args.tree)
    ucfg = os.path.join(P2M, "upload-config.json")
    if os.path.exists(ucfg):
        c = json.load(open(ucfg, encoding="utf-8"))
        if c.get("public"):
            args.public = True   # a tree that imports public content must itself be public
    AUTH = Auth()
    tree = load_tree()
    meta = json.load(open(os.path.join(P2M, "metadata.json"), encoding="utf-8"))
    st = load_state()
    log(f"tree {args.tree}: {len(tree['bundles'])} bundles, {len(tree['nodes'])} nodes "
        f"({sum(1 for n in tree['nodes'] if not n.get('solution_file'))} Open leaves, "
        f"{len(PUBLISHED)} imported published theorems); visibility {'public' if args.public else 'private'}")
    code, me = request("GET", "/me")
    if code == 200:
        lic = (me.get("licensing") or {}).get("status")
        log(f"account {me.get('username')}; licensing status of earlier contributions: {lic}")
    if args.status:
        status(tree, st)
        return
    if args.release:
        release(tree, st, args.yes)
        return
    if args.only:
        {"definitions": upload_definitions, "theorems": upload_theorems, "solutions": upload_solutions}[args.only](tree, meta, st, args)
    elif args.pipeline:
        upload_pipelined(tree, meta, st, args, [Sibling(rel) for rel in args.after])
    else:
        wb, wn = compute_waves(tree)
        last = max([0] + list(wb.values()) + list(wn.values()))
        log(f"{last + 1} wave(s): " + "; ".join(
            f"wave {k}: {sum(1 for v in wb.values() if v == k)} bundles, {sum(1 for v in wn.values() if v == k)} nodes" for k in range(last + 1)))
        for k in range(last + 1):
            sub = dict(tree, bundles=[b for b in tree["bundles"] if wb[b["definition_name"]] == k],
                       nodes=[n for n in tree["nodes"] if wn[n["theorem_name"]] == k])
            log(f"=== wave {k}: {len(sub['bundles'])} bundles, {len(sub['nodes'])} nodes")
            upload_definitions(sub, meta, st, args)
            upload_theorems(sub, meta, st, args)
            upload_solutions(sub, meta, st, args)
            needed = sorted({t for b in tree["bundles"] if wb[b["definition_name"]] == k + 1
                             for t in b.get("imported_nodes", []) if t in wn})
            if needed and not args.dry_run:
                log(f"wave {k + 1} bundles import {len(needed)} node(s) of earlier waves; checking they are Proved")
                ensure_proved(needed, st)
    if not args.dry_run:
        status(tree, st)


if __name__ == "__main__":
    main()
