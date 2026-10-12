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
"""
import argparse, json, os, sys, time, urllib.request, urllib.parse, urllib.error, uuid, io

API = "https://prove2.me/api/v1"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
P2M = os.path.join(ROOT, "prove2me")
STATE_PATH = os.path.join(P2M, "upload-state.json")
PROJECT_TAG = "mipre-formalization"


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
            req = urllib.request.Request(f"{API}/agent/refresh", data=body,
                                         headers={"Content-Type": "application/json"}, method="POST")
            with urllib.request.urlopen(req, timeout=60) as r:
                d = json.loads(r.read().decode())
            self._token = d["access_token"]
            self._exp = d.get("expires_at", time.time() + 3600)
            log(f"token refreshed (platform version {d.get('version')})")
        return self._token


AUTH = None


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def request(method, path, body=None, params=None, multipart=None, retries=5):
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
            if e.code >= 500 and attempt < retries - 1:
                log(f"{e.code} on {path}; retrying in {5 * (attempt + 1)}s")
                time.sleep(5 * (attempt + 1))
                continue
            return e.code, d
        except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
            if attempt < retries - 1:
                log(f"network error on {path}: {e}; retrying in {5 * (attempt + 1)}s")
                time.sleep(5 * (attempt + 1))
                continue
            raise
    return 599, {"error": "retries exhausted"}


# ----------------------------------------------------------------------------- state
def load_state():
    if os.path.exists(STATE_PATH):
        return json.load(open(STATE_PATH, encoding="utf-8"))
    return {"definitions": {}, "theorems": {}, "solutions": {}, "log": []}


def save_state(st):
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


def upload_definitions(tree, meta, st, args):
    mb = {b["definition_name"]: b for b in meta["bundles"]}
    for b in tree["bundles"]:
        name = b["definition_name"]
        rec = st["definitions"].setdefault(name, {})
        if rec.get("status") == "PUBLISHED":
            continue
        if rec.get("job_id") and rec.get("status") not in ("FAILED", "ERROR"):
            job = poll_job(rec["job_id"], name)
        else:
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
            if args.dry_run:
                log(f"[dry-run] submit-definition {name} ({len(body['definition'])} bytes)")
                continue
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
                        continue
                sys.exit(f"definition {name} was rejected before queueing; fix and rerun")
            rec["job_id"] = d["job_id"]
            save_state(st)
            log(f"submit-definition {name}: queued job {d['job_id']}")
            job = poll_job(d["job_id"], name)
        rec["status"] = job.get("status")
        rec["theorem_id"] = job.get("theorem_id")
        rec["error_message"] = job.get("error_message", "")
        save_state(st)
        log(f"definition {name}: {rec['status']} {rec.get('theorem_id') or ''} {rec['error_message'][:300]}")
        if rec["status"] != "PUBLISHED":
            sys.exit(f"definition {name} did not publish ({rec['status']}); later content imports it, stopping")


def upload_theorems(tree, meta, st, args):
    mn = {n["theorem_name"]: n for n in meta["nodes"]}
    pending = []
    for n in tree["nodes"]:
        name = n["theorem_name"]
        rec = st["theorems"].setdefault(name, {})
        if rec.get("status") == "PUBLISHED" and rec.get("theorem_id"):
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
    failed = [k for k, v in st["theorems"].items() if v.get("status") != "PUBLISHED"]
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


def leaves_first(tree):
    """Nodes ordered so that every imported node comes first."""
    by = {n["theorem_name"]: n for n in tree["nodes"]}
    order, seen = [], set()

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        for c in by[name]["imported_nodes"]:
            visit(c)
        order.append(name)
    for n in tree["nodes"]:
        visit(n["theorem_name"])
    return [by[x] for x in order]


def upload_solutions(tree, meta, st, args):
    mn = {n["theorem_name"]: n for n in meta["nodes"]}
    for n in leaves_first(tree):
        name = n["theorem_name"]
        rec = st["solutions"].setdefault(name, {})
        if rec.get("status") in ("ACCEPTED",):
            continue
        tid = st["theorems"].get(name, {}).get("theorem_id")
        if not tid:
            if args.dry_run:
                log(f"[dry-run] verify {name} (theorem id unknown until the theorems phase has run)")
                continue
            sys.exit(f"no theorem_id recorded for {name}; run the theorems phase first")
        # every child must already be Proved for the parent to resolve straight to Proved
        for c in n["imported_nodes"]:
            if st["solutions"].get(c, {}).get("status") != "ACCEPTED":
                sys.exit(f"child {c} of {name} is not ACCEPTED yet; aborting to keep the leaves-first order")
        if rec.get("submission_id") and rec.get("status") in (None, "PENDING", "SUBMITTED"):
            res = poll_submission(rec["submission_id"], name)
        else:
            if args.dry_run:
                log(f"[dry-run] verify {name} -> theorem {tid}")
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
            log(f"verify {name}: submission {d['submission_id']}")
            res = poll_submission(d["submission_id"], name)
        rec["status"] = res.get("status")
        rec["error_message"] = res.get("error_message", "")
        save_state(st)
        log(f"solution {name}: {rec['status']} {rec['error_message'][:400]}")
        if rec["status"] not in ("ACCEPTED",):
            sys.exit(f"solution of {name} ended {rec['status']}: {rec['error_message'][:1500]}")


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
    global AUTH
    ap = argparse.ArgumentParser()
    ap.add_argument("--release", action="store_true", help="make the uploaded private tree public (asks for --yes)")
    ap.add_argument("--yes", action="store_true")
    ap.add_argument("--public", action="store_true", help="create public content (default: private)")
    ap.add_argument("--only", choices=["definitions", "theorems", "solutions"])
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--status", action="store_true")
    ap.add_argument("--max-inflight", type=int, default=10)
    args = ap.parse_args()
    AUTH = Auth()
    tree = json.load(open(os.path.join(P2M, "tree.json"), encoding="utf-8"))
    meta = json.load(open(os.path.join(P2M, "metadata.json"), encoding="utf-8"))
    st = load_state()
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
    if args.only in (None, "definitions"):
        upload_definitions(tree, meta, st, args)
    if args.only in (None, "theorems"):
        upload_theorems(tree, meta, st, args)
    if args.only in (None, "solutions"):
        upload_solutions(tree, meta, st, args)
    if not args.dry_run:
        status(tree, st)


if __name__ == "__main__":
    main()
